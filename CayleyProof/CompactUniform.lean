module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Tactic

/-! Pointwise convergence with a common Lipschitz bound is uniform on compact
sets. Applied to integration, this supplies the finite-net argument in the
verification of Lemma 15. No equidistribution assumption is hidden here:
weak convergence is an explicit input to the general analytic lemma.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace CayleyProof

theorem uniform_on_compact_of_lipschitz
    {E : Type*} [PseudoMetricSpace E] {S : Set E} (hS : IsCompact S)
    {f : ℕ → E → ℝ} {g : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ n x y, |f n x - f n y| ≤ L * dist x y)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y)
    (hlim : ∀ x ∈ S, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ S, |f n x - g x| < ε := by
  intro ε hε
  let δ := ε / (4 * (L + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t, hts, htfin, ht⟩ := hS.finite_cover_balls hδ
  have hev : ∀ x ∈ t, ∀ᶠ n in atTop, |f n x - g x| < ε / 2 := by
    intro x hx
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp (hlim x (hts hx))) (ε / 2) (by positivity)
  have hev' : ∀ᶠ n in atTop, ∀ x ∈ t, |f n x - g x| < ε / 2 :=
    htfin.eventually_all.mpr hev
  filter_upwards [hev'] with n hn
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (ht hx)
  obtain ⟨hyt, hxy⟩ := Set.mem_iUnion.mp hy
  have hdist : dist x y < δ := hxy
  have hsmall : 2 * L * dist x y < ε / 2 := by
    have hmul := mul_lt_mul_of_pos_left hdist (show 0 < 2 * (L + 1) by positivity)
    have heq : 2 * (L + 1) * δ = ε / 2 := by
      dsimp [δ]
      field_simp
      norm_num
    rw [heq] at hmul
    have : 0 ≤ dist x y := dist_nonneg
    nlinarith
  calc
    |f n x - g x| ≤ |f n x - f n y| + |f n y - g y| + |g y - g x| := by
      have h := abs_add_three (f n x - f n y) (f n y - g y) (g y - g x)
      convert h using 1; ring_nf
    _ ≤ L * dist x y + |f n y - g y| + L * dist x y := by
      gcongr
      · exact hf n x y
      · simpa only [dist_comm] using hg y x
    _ < ε := by linarith [hn y hyt]

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem integral_probability_lipschitz (μ : ProbabilityMeasure X)
    (f g : X →ᵇ ℝ) :
    |(∫ x, f x ∂(μ : Measure X)) - ∫ x, g x ∂(μ : Measure X)| ≤ dist f g := by
  rw [← integral_sub (f.integrable _) (g.integrable _), dist_eq_norm]
  exact (f - g).norm_integral_le_norm _

/-- Weak convergence is uniform on each compact family of bounded continuous
test functions. This is stronger than convergence for each fixed polynomial. -/
theorem weak_convergence_uniform_on_compact
    {μn : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μn atTop (𝓝 μ))
    {S : Set (X →ᵇ ℝ)} (hS : IsCompact S) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ f ∈ S,
      |(∫ x, f x ∂(μn n : Measure X)) - ∫ x, f x ∂(μ : Measure X)| < ε := by
  apply uniform_on_compact_of_lipschitz hS (L := 1) (by positivity)
  · intro n f g
    simpa using integral_probability_lipschitz (μn n) f g
  · intro f g
    simpa using integral_probability_lipschitz μ f g
  · intro f _
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f

end CayleyProof
