module

public import CayleyProof.EmpiricalMeasure

/-! Removing a small proportion of a finite sample changes every bounded
test average by at most twice its bound times that proportion.
-/

@[expose] public section

open scoped BigOperators Classical

namespace CayleyProof

noncomputable def finiteAverage {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i

theorem abs_finiteAverage_le {ι : Type*} [Fintype ι]
    {f : ι → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ i, |f i| ≤ M) :
    |finiteAverage f| ≤ M := by
  by_cases hn : Fintype.card ι = 0
  · simp [finiteAverage, hn, hM]
  have hnpos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold finiteAverage
  rw [abs_mul, abs_of_pos (inv_pos.mpr hnpos)]
  calc
    (Fintype.card ι : ℝ)⁻¹ * |∑ i, f i|
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _ : ι, M := by gcongr with i; exact hf i
    _ = M := by simp [hnpos.ne']

theorem card_mul_finiteAverage {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (Fintype.card ι : ℝ) * finiteAverage f = ∑ i, f i := by
  by_cases hz : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hz
    simp [finiteAverage]
  · simp [finiteAverage, hz]

theorem finiteAverage_partition {ι : Type*} [Fintype ι]
    (P : ι → Prop) (f : ι → ℝ) :
    finiteAverage f =
      ((Fintype.card {i // P i} : ℝ) / Fintype.card ι) *
        finiteAverage (fun i : {i // P i} => f i.val) +
      ((Fintype.card {i // ¬ P i} : ℝ) / Fintype.card ι) *
        finiteAverage (fun i : {i // ¬ P i} => f i.val) := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype P f
  calc
    finiteAverage f = (Fintype.card ι : ℝ)⁻¹ *
        ((∑ i : {i // P i}, f i.val) + ∑ i : {i // ¬ P i}, f i.val) := by
      rw [hsplit]; rfl
    _ = _ := by
      rw [← card_mul_finiteAverage (fun i : {i // P i} => f i.val),
        ← card_mul_finiteAverage (fun i : {i // ¬ P i} => f i.val)]
      ring

theorem finiteAverage_subsample_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Prop) {f : ι → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ i, |f i| ≤ M) :
    |finiteAverage f - finiteAverage (fun i : {i // P i} => f i.val)| ≤
      2 * M * ((Fintype.card {i // ¬ P i} : ℝ) / Fintype.card ι) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcount : (Fintype.card {i // P i} : ℝ) + Fintype.card {i // ¬ P i} = Fintype.card ι := by
    simpa using Fintype.sum_subtype_add_sum_subtype P (fun _ : ι => (1 : ℝ))
  have hratio : (Fintype.card {i // P i} : ℝ) / Fintype.card ι +
      (Fintype.card {i // ¬ P i} : ℝ) / Fintype.card ι = 1 := by
    rw [← add_div, hcount, div_self hn]
  rw [finiteAverage_partition P f]
  have heq :
      ((Fintype.card {i // P i} : ℝ) / Fintype.card ι) *
        finiteAverage (fun i : {i // P i} => f i.val) +
      ((Fintype.card {i // ¬ P i} : ℝ) / Fintype.card ι) *
        finiteAverage (fun i : {i // ¬ P i} => f i.val) -
      finiteAverage (fun i : {i // P i} => f i.val) =
      ((Fintype.card {i // ¬ P i} : ℝ) / Fintype.card ι) *
        (finiteAverage (fun i : {i // ¬ P i} => f i.val) -
          finiteAverage (fun i : {i // P i} => f i.val)) := by
    linear_combination hratio * finiteAverage (fun i : {i // P i} => f i.val)
  rw [heq, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((Fintype.card {i // ¬ P i} : ℝ) / Fintype.card ι) * (M + M) := by
      gcongr
      exact (abs_sub _ _).trans (add_le_add
        (abs_finiteAverage_le hM (fun i => hf i.val))
        (abs_finiteAverage_le hM (fun i => hf i.val)))
    _ = _ := by ring

end CayleyProof
