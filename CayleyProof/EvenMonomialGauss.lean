module

public import CayleyProof.MonomialGauss
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! The even-degree determinant calculation.  The product of the paired
factors is not discarded: it is included in the constant `A`, whose square
is one.  A nontrivial quadratic character then supplies either sign.
-/

@[expose] public section

open scoped BigOperators

namespace CayleyProof

variable {F : Type*} [Field F] [Fintype F]

theorem quadratic_character_unique {χ κ : MulChar F ℂ}
    (hχ : χ ^ 2 = 1) (hκ : κ ^ 2 = 1) (hχ₁ : χ ≠ 1) (hκ₁ : κ ≠ 1) : χ = κ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  apply (MulChar.eq_iff hg χ κ).mpr
  have hval (η : MulChar F ℂ) (hη : η ^ 2 = 1) (hne : η ≠ 1) : η g = -1 := by
    have hs : η g ^ 2 = 1 := by
      rw [← MulChar.pow_apply_coe, hη, MulChar.one_apply_coe]
    refine (sq_eq_one_iff.mp hs).resolve_left ?_
    intro heq
    apply hne
    exact (MulChar.eq_iff hg η 1).mpr (by simpa using heq)
  rw [hval χ hχ hχ₁, hval κ hκ hκ₁]

omit [Fintype F] in
theorem quadratic_character_exists_negative {κ : MulChar F ℂ}
    (hκ : κ ^ 2 = 1) (hne : κ ≠ 1) : ∃ u : F, u ≠ 0 ∧ κ u = -1 := by
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hne
  refine ⟨u, Units.ne_zero u, ?_⟩
  apply (sq_eq_one_iff.mp ?_).resolve_left hu
  rw [← MulChar.pow_apply_coe, hκ, MulChar.one_apply_coe]

omit [Fintype F] in
theorem quadratic_character_at_square {κ : MulChar F ℂ}
    (hκ : κ ^ 2 = 1) {x : F} (hx : x ≠ 0) : κ (x * x) = 1 := by
  rw [map_mul, ← pow_two, ← MulChar.pow_apply' _ two_ne_zero, hκ,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]

/-- Pairing the characters themselves, rather than their Gauss factors,
shows that their product is the unique nontrivial quadratic character. -/
theorem even_torsion_character_product {d : ℕ} (hd : Even d)
    {κ : MulChar F ℂ} (hκ : κ ^ 2 = 1) (hκ₁ : κ ≠ 1)
    (T : Finset (MulChar F ℂ))
    (hT : ∀ χ, χ ∈ T ↔ χ ^ d = 1 ∧ χ ≠ 1) : ∏ χ ∈ T, χ = κ := by
  classical
  have hκT : κ ∈ T := by
    apply (hT κ).mpr
    refine ⟨?_, hκ₁⟩
    obtain ⟨e, rfl⟩ := hd
    rw [show e + e = 2 * e by omega, pow_mul, hκ, one_pow]
  have hinvκ : κ⁻¹ = κ := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hκ)
  have he : ∏ χ ∈ T.erase κ, χ = 1 := by
    apply Finset.prod_involution (fun χ _ => χ⁻¹)
    · intro χ _; exact mul_inv_cancel χ
    · intro χ hχ _ heq
      have hs : χ ^ 2 = 1 := by
        calc χ ^ 2 = χ⁻¹ * χ := by rw [pow_two]; exact congrArg (· * χ) heq.symm
             _ = 1 := inv_mul_cancel χ
      exact (Finset.mem_erase.mp hχ).1
        (quadratic_character_unique hs hκ ((hT χ).mp (Finset.mem_erase.mp hχ).2).2 hκ₁)
    · intro χ _; exact inv_inv χ
    · intro χ hχ
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hχ
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        apply hne
        simpa [hinvκ] using congrArg Inv.inv heq
      · exact (hT χ⁻¹).mpr ⟨by rw [inv_pow, ((hT χ).mp hmem).1, inv_one],
          inv_ne_one.mpr ((hT χ).mp hmem).2⟩
  rw [← Finset.prod_erase_mul _ _ hκT, he, one_mul]

theorem monomialGauss_product_parameter {ψ : AddChar F ℂ} {c : ℂ}
    {u : F} (hu : u ≠ 0) (T : Finset (MulChar F ℂ)) :
    (∏ χ ∈ T, monomialGaussFactor ψ c u χ) =
      (∏ χ ∈ T, monomialGaussFactor ψ c 1 χ) * ((∏ χ ∈ T, χ) u)⁻¹ := by
  classical
  have heval : (∏ χ ∈ T, χ) u = ∏ χ ∈ T, χ u := by
    induction T using Finset.induction_on with
    | empty => simp [MulChar.one_apply (isUnit_iff_ne_zero.mpr hu)]
    | @insert χ T h ih => simp [h, ih]
  rw [heval, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro χ _
  simp [monomialGaussFactor]
  ring

theorem monomialGauss_product_square {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {c : ℂ} (hc : c ^ 2 * Fintype.card F = 1) {u : F} (hu : u ≠ 0)
    {d : ℕ} (T : Finset (MulChar F ℂ))
    (hT : ∀ χ, χ ∈ T ↔ χ ^ d = 1 ∧ χ ≠ 1) :
    (∏ χ ∈ T, monomialGaussFactor ψ c u χ) ^ 2 = (∏ χ ∈ T, χ) (-1) := by
  classical
  have hi : (∏ χ ∈ T, monomialGaussFactor ψ c u χ⁻¹) =
      ∏ χ ∈ T, monomialGaussFactor ψ c u χ := by
    apply Finset.prod_nbij' Inv.inv Inv.inv
    · intro χ hχ
      exact (hT χ⁻¹).mpr ⟨by rw [inv_pow, ((hT χ).mp hχ).1, inv_one],
        inv_ne_one.mpr ((hT χ).mp hχ).2⟩
    · intro χ hχ
      exact (hT χ⁻¹).mpr ⟨by rw [inv_pow, ((hT χ).mp hχ).1, inv_one],
        inv_ne_one.mpr ((hT χ).mp hχ).2⟩
    · intro χ _; exact inv_inv χ
    · intro χ _; exact inv_inv χ
    · intro χ _; rfl
  have heval : (∏ χ ∈ T, χ) (-1) = ∏ χ ∈ T, χ (-1) := by
    clear hi hT
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)))
    | @insert χ T h ih => simp [h, ih]
  rw [pow_two]
  nth_rw 2 [← hi]
  rw [← Finset.prod_mul_distrib, heval]
  exact Finset.prod_congr rfl (fun χ hχ =>
    monomialGaussFactor_pairing hψ hc hu ((hT χ).mp hχ).2)

/-- Over a field where -1 is a square, some monomial has determinant one.
All inverse-pair signs are retained in the constant product at u=1. -/
theorem even_monomialGauss_product_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {c : ℂ} (hc : c ^ 2 * Fintype.card F = 1)
    {d : ℕ} (hd : Even d) {κ : MulChar F ℂ} (hκ : κ ^ 2 = 1) (hκ₁ : κ ≠ 1)
    (hminus : IsSquare (-1 : F)) (T : Finset (MulChar F ℂ))
    (hT : ∀ χ, χ ∈ T ↔ χ ^ d = 1 ∧ χ ≠ 1) :
    ∃ u : F, u ≠ 0 ∧ ∏ χ ∈ T, monomialGaussFactor ψ c u χ = 1 := by
  classical
  have hprod := even_torsion_character_product hd hκ hκ₁ T hT
  have hneg : κ (-1) = 1 := by
    obtain ⟨x, hx⟩ := hminus
    have hx0 : x ≠ 0 := by intro h; simp [h] at hx
    rw [hx]
    exact quadratic_character_at_square hκ hx0
  let A := ∏ χ ∈ T, monomialGaussFactor ψ c 1 χ
  have hAsq : A ^ 2 = 1 := by
    change (∏ χ ∈ T, monomialGaussFactor ψ c 1 χ) ^ 2 = 1
    rw [monomialGauss_product_square hψ hc one_ne_zero T hT, hprod, hneg]
  rcases sq_eq_one_iff.mp hAsq with hp | hm
  · exact ⟨1, one_ne_zero, hp⟩
  · obtain ⟨u, hu, hval⟩ := quadratic_character_exists_negative hκ hκ₁
    refine ⟨u, hu, ?_⟩
    rw [monomialGauss_product_parameter hu T, hprod, hval]
    change A * (-1 : ℂ)⁻¹ = 1
    simp [hm]

end CayleyProof
