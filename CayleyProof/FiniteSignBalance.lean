module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-! A finite-measure version of the sign-count step in the inertia argument.
It includes the tail correction explicitly, so no uniform pointwise bound
is imposed on the exceptional spectral values outside `S`.
-/

@[expose] public section

open scoped BigOperators Classical

namespace CayleyProof

variable {ι : Type*} [Fintype ι]

theorem sum_posPart_of_sum_zero (f : ι → ℝ) (hmean : ∑ i, f i = 0) :
    2 * ∑ i, max (f i) 0 = ∑ i, |f i| := by
  have hid (x : ℝ) : 2 * max x 0 = |x| + x := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
    · rw [max_eq_right (by linarith), abs_of_nonpos (by linarith)]; ring
  simp_rw [Finset.mul_sum, hid, Finset.sum_add_distrib, hmean, add_zero]

theorem nonnegative_count_lower_bound (f : ι → ℝ) (S : Finset ι) (C : ℝ)
    (hmean : ∑ i, f i = 0)
    (hbulk : ∀ i ∈ S, |f i| ≤ 1)
    (hmass : C ≤ ∑ i, |f i|)
    (htail : ∑ i, (if i ∈ S then 0 else |f i|) ≤ C / 4) :
    C / 4 ≤ ((Finset.univ.filter (fun i => 0 ≤ f i)).card : ℝ) := by
  have hpoint (i : ι) : max (f i) 0 ≤
      (if 0 ≤ f i then (1 : ℝ) else 0) + (if i ∈ S then 0 else |f i|) := by
    by_cases hi : i ∈ S <;> by_cases hf : 0 ≤ f i
    · simp only [hi, hf, ↓reduceIte, add_zero, max_eq_left hf]
      exact (le_abs_self _).trans (hbulk i hi)
    · simp [hi, hf, max_eq_right (by linarith : f i ≤ 0)]
    · simp [hi, hf, abs_of_nonneg hf]
    · simp [hi, hf, max_eq_right (by linarith : f i ≤ 0), abs_nonneg]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [Finset.sum_add_distrib] at hsum
  have hcount : (∑ i, if 0 ≤ f i then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i => 0 ≤ f i)).card : ℝ) := by
    simp
  rw [hcount] at hsum
  have hbalance := sum_posPart_of_sum_zero f hmean
  linarith

theorem nonpositive_count_lower_bound (f : ι → ℝ) (S : Finset ι) (C : ℝ)
    (hmean : ∑ i, f i = 0)
    (hbulk : ∀ i ∈ S, |f i| ≤ 1)
    (hmass : C ≤ ∑ i, |f i|)
    (htail : ∑ i, (if i ∈ S then 0 else |f i|) ≤ C / 4) :
    C / 4 ≤ ((Finset.univ.filter (fun i => f i ≤ 0)).card : ℝ) := by
  have h := nonnegative_count_lower_bound (fun i => -f i) S C
    (by simpa using congrArg Neg.neg hmean)
    (by simpa using hbulk) (by simpa using hmass) (by simpa using htail)
  simpa using h

end CayleyProof
