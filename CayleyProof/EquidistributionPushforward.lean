module

public import CayleyProof.EmpiricalMeasure
public import CayleyProof.PushforwardSupport

/-! Deduce weak convergence of real-valued samples from equidistribution
against continuous class functions. This is the precise measure-theoretic
step used after Katz--Sarnak, Theorem 9.2.6(1).
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction

namespace CayleyProof

variable {K : Type*} [Group K] [TopologicalSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- Deligne's conclusion is used only for continuous conjugacy-invariant
functions. The limiting real measure is an actual probability pushforward. -/
theorem equidistribution_pushforward
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (θ : ∀ n, ι n → K) (μ : ProbabilityMeasure K)
    (φ : C(K, ℝ)) (hφ : ∀ x y, φ (y * x * y⁻¹) = φ x)
    (hEq : ∀ f : C(K, ℝ), (∀ x y, f (y * x * y⁻¹) = f x) →
      Tendsto (fun n => (Fintype.card (ι n) : ℝ)⁻¹ * ∑ i, f (θ n i))
        atTop (𝓝 (∫ x, f x ∂(μ : Measure K)))) :
    Tendsto (fun n => empiricalLaw (fun i => φ (θ n i)))
      atTop (𝓝 (μ.map φ)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have H := hEq (f.toContinuousMap.comp φ) (by intro x y; simp [hφ])
  have hmap : (∫ x, f x ∂(μ.map φ : Measure ℝ)) =
      ∫ x, f (φ x) ∂(μ : Measure K) := by
    exact integral_map_of_stronglyMeasurable φ.continuous.measurable
      f.continuous.stronglyMeasurable
  rw [hmap]
  convert H using 1
  · ext n
    exact integral_empiricalLaw _ _ f.continuous.stronglyMeasurable
  · rfl

end CayleyProof
