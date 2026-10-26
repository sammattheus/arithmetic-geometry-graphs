module

public import CayleyProof.EvenMonomialGauss
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

open scoped BigOperators Classical

namespace CayleyProof

variable {F : Type*} [Field F] [Fintype F]

noncomputable instance complexMulCharFintype : Fintype (MulChar F ℂ) := Fintype.ofFinite _

instance complexMulCharCyclic : IsCyclic (MulChar F ℂ) :=
  (MulChar.mulEquiv_units F ℂ).some.isCyclic.mpr inferInstance

noncomputable def nontrivialTorsionCharacters (F : Type*) [Field F] [Fintype F]
    (d : ℕ) : Finset (MulChar F ℂ) := {χ | χ ^ d = 1 ∧ χ ≠ 1}

theorem mem_nontrivialTorsionCharacters (d : ℕ) (χ : MulChar F ℂ) :
    χ ∈ nontrivialTorsionCharacters F d ↔ χ ^ d = 1 ∧ χ ≠ 1 := by
  simp [nontrivialTorsionCharacters]

theorem card_nontrivialTorsionCharacters {d : ℕ} (hd : d ∣ Fintype.card F - 1) :
    (nontrivialTorsionCharacters F d).card = d - 1 := by
  have hker : Fintype.card {χ : MulChar F ℂ // χ ^ d = 1} = d := by
    change Fintype.card (powMonoidHom d : MulChar F ℂ →* MulChar F ℂ).ker = d
    rw [← Nat.card_eq_fintype_card, IsCyclic.card_powMonoidHom_ker,
      MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity,
      Nat.card_eq_fintype_card, Fintype.card_units, Nat.gcd_eq_right hd]
  have hset : nontrivialTorsionCharacters F d =
      ({χ : MulChar F ℂ | χ ^ d = 1} : Finset _).erase 1 := by
    ext χ
    simp [nontrivialTorsionCharacters, and_comm]
  rw [hset, Finset.card_erase_of_mem (by simp)]
  congr 1
  simpa [Fintype.card_subtype] using hker

theorem exists_quadratic_character_of_even_card_sub_one
    (h : 2 ∣ Fintype.card F - 1) : ∃ κ : MulChar F ℂ, κ ^ 2 = 1 ∧ κ ≠ 1 := by
  obtain ⟨κ, hκ⟩ := MulChar.exists_mulChar_orderOf F h (Complex.isPrimitiveRoot_exp 2 (by decide))
  refine ⟨κ, ?_, ?_⟩
  · rw [← hκ]; exact pow_orderOf_eq_one κ
  · intro heq
    simp [heq] at hκ

/-- An odd square field cardinality supplies the required square root of -1. -/
theorem neg_one_isSquare_of_square_card {v : ℕ}
    (hcard : Fintype.card F = v ^ 2) : IsSquare (-1 : F) := by
  rw [FiniteField.isSquare_neg_one_iff, hcard]
  have hv : v % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [Nat.pow_mod]
  interval_cases h : v % 4 <;> norm_num

/-- This closes the choice of monomial for every d dividing q-1, provided
q is a square.  No quadratic character or root of -1 remains as an input. -/
theorem exists_monomialGauss_product_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {c : ℂ} (hc : c ^ 2 * Fintype.card F = 1)
    {d v : ℕ} (hd : d ∣ Fintype.card F - 1) (hcard : Fintype.card F = v ^ 2) :
    ∃ u : F, u ≠ 0 ∧
      ∏ χ ∈ nontrivialTorsionCharacters F d, monomialGaussFactor ψ c u χ = 1 := by
  rcases Nat.even_or_odd d with he | ho
  · obtain ⟨κ, hκ, hκ₁⟩ := exists_quadratic_character_of_even_card_sub_one
      ((even_iff_two_dvd.mp he).trans hd)
    exact even_monomialGauss_product_one hψ hc he hκ hκ₁
      (neg_one_isSquare_of_square_card hcard) _ (mem_nontrivialTorsionCharacters d)
  · exact ⟨1, one_ne_zero, odd_monomialGauss_product hψ hc one_ne_zero ho _
      (mem_nontrivialTorsionCharacters d)⟩

end CayleyProof
