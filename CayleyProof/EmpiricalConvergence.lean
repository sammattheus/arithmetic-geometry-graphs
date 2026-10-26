module

public import CayleyProof.EmpiricalComparison
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Two elementary weak-limit transfers: deleting a negligible fraction,
and uniformly perturbing samples in a compact metric space.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction Classical

namespace CayleyProof

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem empirical_subsample_tendsto
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (P : ∀ n, ι n → Prop) [∀ n, Nonempty {i : ι n // P n i}]
    (x : ∀ n, ι n → X) (μ : ProbabilityMeasure X)
    (hbad : Tendsto (fun n => (Fintype.card {i : ι n // ¬ P n i} : ℝ) /
      Fintype.card (ι n)) atTop (𝓝 0))
    (hgood : Tendsto (fun n => empiricalLaw (fun i : {i : ι n // P n i} => x n i.val))
      atTop (𝓝 μ)) :
    Tendsto (fun n => empiricalLaw (x n)) atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hgood f
  have hbound (n) := finiteAverage_subsample_bound (P n) (norm_nonneg f)
    (fun i => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (x n i))
  have hdiff : Tendsto (fun n =>
      (∫ z, f z ∂(empiricalLaw (x n) : Measure X)) -
      ∫ z, f z ∂(empiricalLaw (fun i : {i : ι n // P n i} => x n i.val) : Measure X))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa using hbad.const_mul (2 * ‖f‖))
    rw [integral_empiricalLaw _ _ f.continuous.stronglyMeasurable,
      integral_empiricalLaw _ _ f.continuous.stronglyMeasurable, Real.norm_eq_abs]
    simpa [finiteAverage] using hbound n
  simpa using hdiff.add hlim

theorem empirical_uniform_perturbation_tendsto [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (x y : ∀ n, ι n → X) (μ : ProbabilityMeasure X)
    (hclose : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, dist (x n i) (y n i) < ε)
    (hy : Tendsto (fun n => empiricalLaw (y n)) atTop (𝓝 μ)) :
    Tendsto (fun n => empiricalLaw (x n)) atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hy f
  have hdiff : Tendsto (fun n =>
      (∫ z, f z ∂(empiricalLaw (x n) : Measure X)) -
      ∫ z, f z ∂(empiricalLaw (y n) : Measure X)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hfc⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 2) (by positivity)
    filter_upwards [hclose δ hδ] with n hn
    rw [integral_empiricalLaw _ _ f.continuous.stronglyMeasurable,
      integral_empiricalLaw _ _ f.continuous.stronglyMeasurable, Real.dist_eq,
      sub_zero, ← mul_sub, ← Finset.sum_sub_distrib]
    have H := abs_finiteAverage_le (show 0 ≤ ε / 2 by positivity)
      (fun i => (show |f (x n i) - f (y n i)| < ε / 2 from
        (by simpa only [Real.dist_eq] using hfc (hn i))).le)
    exact H.trans_lt (by linarith)
  simpa using hdiff.add hlim

end CayleyProof
