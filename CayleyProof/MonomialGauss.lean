module

public import CayleyProof.GaussPairing
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic

/-! Algebraic deductions for the monomial Frobenius calculation. The Gauss
factors here are the proposed eigenvalues; identification with the Frobenius
characteristic polynomial is a separate obligation, not an assumption hidden
inside the determinant theorem.
-/

@[expose] public section

open scoped BigOperators

namespace CayleyProof

variable {F : Type*} [Field F] [Fintype F]

noncomputable def monomialGaussFactor (ψ : AddChar F ℂ) (c : ℂ)
    (u : F) (χ : MulChar F ℂ) : ℂ :=
  -c * (χ u)⁻¹ * gaussSum χ ψ

/-- The normalizing scalar is the reciprocal of the positive square root of q. -/
theorem sqrt_card_normalization :
    (((Real.sqrt (Fintype.card F : ℝ) : ℝ) : ℂ)⁻¹) ^ 2 * Fintype.card F = 1 := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card F : ℝ)) ^ 2 = (Fintype.card F : ℝ) := Real.sq_sqrt hq.le
  have hs' : ((Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast hs
  rw [inv_pow, hs']
  exact inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt hq))

theorem monomialGaussFactor_pairing {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {c : ℂ} (hc : c ^ 2 * Fintype.card F = 1) {u : F} (hu : u ≠ 0)
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    monomialGaussFactor ψ c u χ * monomialGaussFactor ψ c u χ⁻¹ = χ (-1) := by
  have hχu : χ u ≠ 0 := MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hu)
  unfold monomialGaussFactor
  rw [MulChar.inv_apply_eq_inv', inv_inv]
  calc
    -c * (χ u)⁻¹ * gaussSum χ ψ * (-c * χ u * gaussSum χ⁻¹ ψ)
      = c ^ 2 * ((χ u)⁻¹ * χ u) * (gaussSum χ ψ * gaussSum χ⁻¹ ψ) := by ring
    _ = χ (-1) := by
      rw [inv_mul_cancel₀ hχu, mul_one, gauss_pairing hχ hψ]
      calc
        c ^ 2 * (χ (-1) * Fintype.card F) = (c ^ 2 * Fintype.card F) * χ (-1) := by ring
        _ = _ := by rw [hc, one_mul]

theorem odd_power_inv_ne_self {G : Type*} [Group G] {g : G} {d : ℕ}
    (hd : Odd d) (hpow : g ^ d = 1) (hg : g ≠ 1) : g⁻¹ ≠ g := by
  intro hinv
  have hsq : g ^ 2 = 1 := by
    calc
      g ^ 2 = g * g := pow_two g
      _ = g⁻¹ * g := by rw [hinv]
      _ = 1 := inv_mul_cancel g
  obtain ⟨r, hr⟩ := exists_pow_eq_pow_two_mul hpow hd 1
  rw [pow_one, pow_mul, hsq, one_pow] at hr
  exact hg hr

/-- In odd degree the product of all nontrivial d-torsion Gauss factors is one.
The finite set is explicit; no finiteness or enumeration of characters is postulated. -/
theorem odd_monomialGauss_product {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {c : ℂ} (hc : c ^ 2 * Fintype.card F = 1) {u : F} (hu : u ≠ 0)
    {d : ℕ} (hd : Odd d) (T : Finset (MulChar F ℂ))
    (hT : ∀ χ, χ ∈ T ↔ χ ^ d = 1 ∧ χ ≠ 1) :
    ∏ χ ∈ T, monomialGaussFactor ψ c u χ = 1 := by
  classical
  apply Finset.prod_involution (fun χ _ => χ⁻¹)
  · intro χ hχ
    rw [monomialGaussFactor_pairing hψ hc hu (hT χ |>.mp hχ).2]
    exact odd_order_character_at_neg_one hd (hT χ |>.mp hχ).1
  · intro χ hχ _
    exact odd_power_inv_ne_self hd (hT χ |>.mp hχ).1 (hT χ |>.mp hχ).2
  · intro χ hχ
    exact inv_inv χ
  · intro χ hχ
    apply (hT χ⁻¹).mpr
    exact ⟨by rw [inv_pow, (hT χ |>.mp hχ).1, inv_one],
      inv_ne_one.mpr (hT χ |>.mp hχ).2⟩

end CayleyProof
