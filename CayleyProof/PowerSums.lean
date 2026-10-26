module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.Tactic

/-! Recovering the determinant from all positive power traces.  This is
proved using mathlib's Newton identities, rather than admitted as a
Frobenius-eigenvalue identification.
-/

@[expose] public section

open scoped BigOperators

namespace CayleyProof

open MvPolynomial Finset

theorem eval_esymm_card {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    eval a (esymm ι ℂ (Fintype.card ι)) = ∏ i, a i := by
  classical
  simp [esymm, ← Finset.card_univ, Finset.powersetCard_self]

theorem esymm_eq_of_powerSums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (b : κ → ℂ)
    (h : ∀ n : ℕ, 0 < n → ∑ i, a i ^ n = ∑ j, b j ^ n) (n : ℕ) :
    eval a (esymm ι ℂ n) = eval b (esymm κ ℂ n) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    apply mul_left_cancel₀ (show (n : ℂ) ≠ 0 by exact_mod_cast hn.ne')
    have ha := congrArg (eval a) (mul_esymm_eq_sum ι ℂ n)
    have hb := congrArg (eval b) (mul_esymm_eq_sum κ ℂ n)
    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at ha hb
    rw [ha, hb]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hxsum, hxlt⟩ := Finset.mem_filter.mp hx
    have hpos : 0 < x.2 := by have := Finset.mem_antidiagonal.mp hxsum; omega
    rw [ih x.1 hxlt]
    have hp : eval a (psum ι ℂ x.2) = eval b (psum κ ℂ x.2) := by
      simpa [psum] using h x.2 hpos
    rw [hp]

/-- Only the positive power sums and equality of the ranks are needed. -/
theorem prod_eq_of_powerSums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (b : κ → ℂ) (hcard : Fintype.card ι = Fintype.card κ)
    (h : ∀ n : ℕ, 0 < n → ∑ i, a i ^ n = ∑ j, b j ^ n) :
    ∏ i, a i = ∏ j, b j := by
  classical
  have H := esymm_eq_of_powerSums a b h (Fintype.card ι)
  rw [eval_esymm_card a, hcard, eval_esymm_card b] at H
  exact H

end CayleyProof
