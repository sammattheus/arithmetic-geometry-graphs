module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-! The pointwise growth estimate used to control the exceptional eigenvalue.
The compactness argument producing a uniform bound on the coefficient sum
is a separate obligation; it is not assumed in this lemma.
-/

@[expose] public section

open scoped BigOperators

namespace CayleyProof

theorem abs_pow_le_one_add {i k : ℕ} (hik : i ≤ k) (x : ℝ) :
    |x| ^ i ≤ 1 + |x| ^ k := by
  by_cases hx : |x| ≤ 1
  · have hi : |x| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
    have hk : 0 ≤ |x| ^ k := pow_nonneg (abs_nonneg x) _
    linarith
  · have hi : |x| ^ i ≤ |x| ^ k := pow_le_pow_right₀ (by linarith) hik
    linarith

theorem polynomial_growth (p : Polynomial ℝ) (k : ℕ) (hdeg : p.natDegree ≤ k)
    (x : ℝ) :
    |p.eval x| ≤ (∑ i ∈ Finset.range (k + 1), |p.coeff i|) * (1 + |x| ^ k) := by
  rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < k + 1) x]
  calc
    |∑ i ∈ Finset.range (k + 1), p.coeff i * x ^ i|
        ≤ ∑ i ∈ Finset.range (k + 1), |p.coeff i * x ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), |p.coeff i| * (1 + |x| ^ k) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      apply mul_le_mul_of_nonneg_left (abs_pow_le_one_add (by simpa using hi) x)
      exact abs_nonneg _
    _ = _ := Finset.sum_mul .. |>.symm

end CayleyProof
