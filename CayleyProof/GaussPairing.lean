module

public import Mathlib.NumberTheory.GaussSum

/-! Elementary Gauss-sum deductions in the appendix, reusing mathlib's characters
and Gauss sums. These are proofs, not external theorem declarations. -/

@[expose] public section

namespace CayleyProof

variable {F : Type*} [Field F] [Fintype F]

/-- Pair inverse multiplicative characters while keeping the same additive character. -/
theorem gauss_pairing {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * Fintype.card F := by
  rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹ ψ, mul_left_comm,
    gaussSum_mul_gaussSum_eq_card hχ hψ, MulChar.inv_apply', inv_neg_one]

omit [Fintype F] in
/-- Odd-order characters take the value one at minus one. -/
theorem odd_order_character_at_neg_one {χ : MulChar F ℂ} {d : ℕ}
    (hd : Odd d) (hχ : χ ^ d = 1) : χ (-1) = 1 :=
  MulChar.val_neg_one_eq_one_of_odd_order hd hχ

/-- The paired Gauss product for an odd-order nontrivial character. -/
theorem odd_order_gauss_pairing {χ : MulChar F ℂ} {d : ℕ}
    (hd : Odd d) (horder : χ ^ d = 1) (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = Fintype.card F := by
  rw [gauss_pairing hχ hψ, odd_order_character_at_neg_one hd horder, one_mul]

end CayleyProof
