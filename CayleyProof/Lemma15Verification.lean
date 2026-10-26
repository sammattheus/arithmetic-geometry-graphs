module

public import CayleyProof.PolynomialFamily
public import CayleyProof.CompactUniform
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Uniform integral and tail estimates for a compact bulk plus one exceptional
atom. This is the analytic step in Theorem 18. The bulk weak limit and the
exceptional moment estimate are separate explicit inputs.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal

namespace CayleyProof

variable {I : Set ℝ} [CompactSpace I]

noncomputable def bulkWithAtom (ν : ProbabilityMeasure I) (w : ℝ≥0) (e : ℝ) : Measure ℝ :=
  (1 - w) • Measure.map (Subtype.val : I → ℝ) (ν : Measure I) + w • Measure.dirac e

omit [CompactSpace I] in
theorem bulkWithAtom_probability (ν : ProbabilityMeasure I) {w : ℝ≥0}
    (hw : w ≤ 1) (e : ℝ) : IsProbabilityMeasure (bulkWithAtom ν w e) := by
  constructor
  simp only [bulkWithAtom, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ,
    measure_univ, Measure.dirac_apply_of_mem (Set.mem_univ e)]
  change ((1 - w : ℝ≥0) : ℝ≥0∞) * 1 + (w : ℝ≥0∞) * 1 = 1
  rw [mul_one, mul_one]
  exact_mod_cast tsub_add_cancel_of_le hw

omit [CompactSpace I] in
theorem integral_bulkWithAtom (ν : ProbabilityMeasure I) {w : ℝ≥0}
    (hw : w ≤ 1) (e : ℝ) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂bulkWithAtom ν w e) =
      (1 - (w : ℝ)) * (∫ x : I, f (x : ℝ) ∂(ν : Measure I)) + w * f e := by
  rw [bulkWithAtom, integral_add_measure (f.integrable _).smul_measure_nnreal
    (f.integrable _).smul_measure_nnreal]
  simp only [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul]
  rw [NNReal.coe_sub hw, NNReal.coe_one,
    integral_map_of_stronglyMeasurable measurable_subtype_coe f.continuous.stronglyMeasurable]

theorem polynomial_integrable_bulk (ν : ProbabilityMeasure I) {k : ℕ}
    (a : Fin (k + 1) → ℝ) :
    Integrable (fun x => |(polynomialOfCoefficients a).eval (x : ℝ)|)
      (Measure.map (Subtype.val : I → ℝ) (ν : Measure I)) := by
  apply (integrable_map_measure
    (by fun_prop : AEStronglyMeasurable (fun x => |(polynomialOfCoefficients a).eval (x : ℝ)|)
      (Measure.map (Subtype.val : I → ℝ) (ν : Measure I)))
    measurable_subtype_coe.aemeasurable).mpr
  simpa [Function.comp_def, Real.norm_eq_abs] using
    ((polynomialRestriction I k a).normComp.integrable (ν : Measure I))

theorem integral_polynomial_bulkWithAtom (ν : ProbabilityMeasure I)
    {w : ℝ≥0} (hw : w ≤ 1) (e : ℝ) {k : ℕ} (a : Fin (k + 1) → ℝ) :
    (∫ x, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂bulkWithAtom ν w e) =
      (1 - (w : ℝ)) * (∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(ν : Measure I)) +
      w * |(polynomialOfCoefficients a).eval e| := by
  rw [bulkWithAtom, integral_add_measure
    (polynomial_integrable_bulk ν a).smul_measure_nnreal
    ((integrable_dirac (by finiteness)).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul]
  rw [NNReal.coe_sub hw, NNReal.coe_one,
    integral_map_of_stronglyMeasurable measurable_subtype_coe
      (polynomialOfCoefficients a).continuous.abs.stronglyMeasurable]

omit [CompactSpace I] in
theorem polynomial_bulkWithAtom_tail_bound (ν : ProbabilityMeasure I)
    (hI : MeasurableSet I) (w : ℝ≥0) (e : ℝ) {k : ℕ} (a : Fin (k + 1) → ℝ) :
    (∫ x in Iᶜ, |(polynomialOfCoefficients a).eval x| ∂bulkWithAtom ν w e) ≤
      w * |(polynomialOfCoefficients a).eval e| := by
  classical
  have hzero : (Measure.map (Subtype.val : I → ℝ) (ν : Measure I)).restrict Iᶜ = 0 := by
    apply Measure.restrict_eq_zero.mpr
    rw [Measure.map_apply measurable_subtype_coe hI.compl]
    have : (Subtype.val : I → ℝ) ⁻¹' Iᶜ = ∅ := by ext x; simp
    rw [this, measure_empty]
  simp only [bulkWithAtom, Measure.restrict_add, Measure.restrict_smul, hzero,
    smul_zero, zero_add, restrict_dirac]
  split_ifs
  · simp [NNReal.smul_def, smul_eq_mul]
  · simp only [smul_zero, integral_zero_measure]
    positivity

theorem integral_bulk_abs_le_one (ν : ProbabilityMeasure I) {k : ℕ}
    {a : Fin (k + 1) → ℝ} (ha : a ∈ normalizedPolynomialFamily I k) :
    |∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(ν : Measure I)| ≤ 1 := by
  have h := (polynomialRestriction I k a).normComp.norm_integral_le_norm (ν : Measure I)
  change ‖polynomialRestriction I k a‖ = 1 at ha
  simpa [Real.norm_eq_abs, ha] using h

theorem polynomial_bulk_uniform_convergence {νn : ℕ → ProbabilityMeasure I}
    {ν : ProbabilityMeasure I} (hν : Tendsto νn atTop (𝓝 ν))
    (hI : I.Infinite) (k : ℕ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ a ∈ normalizedPolynomialFamily I k,
      |(∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(νn n : Measure I)) -
        ∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(ν : Measure I)| < ε := by
  intro ε hε
  have h := weak_convergence_uniform_on_compact hν
    (absolutePolynomialFamily_isCompact I k hI) ε hε
  filter_upwards [h] with n hn a ha
  simpa [Real.norm_eq_abs] using hn _ ⟨a, ha, rfl⟩

/-- The first hypothesis of Lemma 15, in its equivalent uniform epsilon form. -/
theorem lemma15_uniform_integrals {νn : ℕ → ProbabilityMeasure I}
    {ν : ProbabilityMeasure I} (hν : Tendsto νn atTop (𝓝 ν))
    (hI : I.Infinite) (k : ℕ) {w : ℕ → ℝ≥0} (hw : ∀ n, w n ≤ 1)
    {e : ℕ → ℝ}
    (htail : Tendsto (fun n => (w n : ℝ) * (1 + |e n| ^ k)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ a ∈ normalizedPolynomialFamily I k,
      |(∫ x, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂bulkWithAtom (νn n) (w n) (e n)) -
        ∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(ν : Measure I)| < ε := by
  obtain ⟨C, hC, hgrowth⟩ := normalized_polynomial_growth I k hI
  intro ε hε
  have hsmall := (Metric.tendsto_nhds.mp htail) (ε / (2 * (C + 1))) (by positivity)
  have hbulk := polynomial_bulk_uniform_convergence hν hI k (ε / 2) (by positivity)
  filter_upwards [hsmall, hbulk] with n hn hn' a ha
  have hnonneg : 0 ≤ (w n : ℝ) * (1 + |e n| ^ k) := by positivity
  have hs : (w n : ℝ) * (1 + |e n| ^ k) < ε / (2 * (C + 1)) := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hn
  have hwb : (w n : ℝ) ≤ (w n : ℝ) * (1 + |e n| ^ k) := by
    nlinarith [pow_nonneg (abs_nonneg (e n)) k, (w n).coe_nonneg]
  have herror :
      |(∫ x, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂bulkWithAtom (νn n) (w n) (e n)) -
        ∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(νn n : Measure I)|
      ≤ (C + 1) * ((w n : ℝ) * (1 + |e n| ^ k)) := by
    rw [integral_polynomial_bulkWithAtom _ (hw n)]
    let b := ∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(νn n : Measure I)
    have hb : |b| ≤ 1 := integral_bulk_abs_le_one (νn n) ha
    calc
      |(1 - (w n : ℝ)) * b + w n * |(polynomialOfCoefficients a).eval (e n)| - b|
        = |(w n : ℝ) * (|(polynomialOfCoefficients a).eval (e n)| - b)| := by congr 1; ring
      _ ≤ (w n : ℝ) * (|(polynomialOfCoefficients a).eval (e n)| + |b|) := by
        rw [abs_mul, abs_of_nonneg (w n).coe_nonneg]
        gcongr
        exact (abs_sub _ _).trans_eq (by rw [abs_abs])
      _ ≤ (w n : ℝ) * (C * (1 + |e n| ^ k) + 1) := by gcongr; exact hgrowth a ha (e n)
      _ ≤ (C + 1) * ((w n : ℝ) * (1 + |e n| ^ k)) := by nlinarith
  have he : (C + 1) * ((w n : ℝ) * (1 + |e n| ^ k)) < ε / 2 := by
    apply (mul_lt_mul_of_pos_left hs (by positivity)).trans_eq
    field_simp
  have htri := abs_sub_le
    (∫ x, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂bulkWithAtom (νn n) (w n) (e n))
    (∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(νn n : Measure I))
    (∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(ν : Measure I))
  linarith [hn' a ha]

/-- The second hypothesis of Lemma 15. All bulk mass lies in I, so only the
exceptional atom contributes to the integral over the complement. -/
theorem lemma15_uniform_tails (hI : I.Infinite) (hImeas : MeasurableSet I)
    (k : ℕ) (νn : ℕ → ProbabilityMeasure I) {w : ℕ → ℝ≥0} {e : ℕ → ℝ}
    (htail : Tendsto (fun n => (w n : ℝ) * (1 + |e n| ^ k)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ a ∈ normalizedPolynomialFamily I k,
      (∫ x in Iᶜ, |(polynomialOfCoefficients a).eval x|
        ∂bulkWithAtom (νn n) (w n) (e n)) < ε := by
  obtain ⟨C, hC, hgrowth⟩ := normalized_polynomial_growth I k hI
  intro ε hε
  have ht := (Metric.tendsto_nhds.mp htail) (ε / C) (div_pos hε hC)
  filter_upwards [ht] with n hn a ha
  have hnonneg : 0 ≤ (w n : ℝ) * (1 + |e n| ^ k) := by positivity
  have hs : (w n : ℝ) * (1 + |e n| ^ k) < ε / C := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hn
  calc
    (∫ x in Iᶜ, |(polynomialOfCoefficients a).eval x|
        ∂bulkWithAtom (νn n) (w n) (e n))
        ≤ (w n : ℝ) * |(polynomialOfCoefficients a).eval (e n)| :=
      polynomial_bulkWithAtom_tail_bound _ hImeas _ _ _
    _ ≤ (w n : ℝ) * (C * (1 + |e n| ^ k)) := by gcongr; exact hgrowth a ha (e n)
    _ = C * ((w n : ℝ) * (1 + |e n| ^ k)) := by ring
    _ < ε := (mul_lt_mul_of_pos_left hs hC).trans_eq (mul_div_cancel₀ ε hC.ne')

end CayleyProof
