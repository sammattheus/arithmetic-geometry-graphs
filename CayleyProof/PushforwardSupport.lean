module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Order.Interval.Set.Infinite

/-! The support argument after Deligne equidistribution. It is a statement
about genuine mathlib measures, not a formal placeholder for infinite support.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace CayleyProof

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem image_support_subset_support_map
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Continuous f) :
    f '' μ.support ⊆ (Measure.map f μ).support := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Measure.support_eq_forall_isOpen]
  intro U hxU hU
  rw [Measure.map_apply hf.measurable hU.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx _
    (hf.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU))

/-- Every attained value of a continuous real function lies in the support of
its pushforward, when every nonempty open set has positive source measure. -/
theorem range_subset_support_map (μ : Measure X) [μ.IsOpenPosMeasure]
    {f : X → ℝ} (hf : Continuous f) : range f ⊆ (Measure.map f μ).support := by
  rintro _ ⟨x, rfl⟩
  rw [Measure.support_eq_forall_isOpen]
  intro U hxU hU
  rw [Measure.map_apply hf.measurable hU.measurableSet]
  exact μ.measure_pos_of_mem_nhds (hf.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU))

/-- For compact source, the support is exactly the image. -/
theorem support_map_eq_range [CompactSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {f : X → ℝ} (hf : Continuous f) : (Measure.map f μ).support = range f := by
  apply subset_antisymm _ (range_subset_support_map μ hf)
  have hc : IsClosed (range f) := isCompact_range hf |>.isClosed
  apply Measure.support_subset_of_isClosed hc
  rw [mem_ae_iff]
  rw [Measure.map_apply hf.measurable hc.measurableSet.compl]
  have : f ⁻¹' (range f)ᶜ = ∅ := by ext x; simp
  rw [this, measure_empty]

/-- A nonconstant continuous image of a preconnected space contains a real
interval. Thus its full-support pushforward cannot have finite support. -/
theorem infinite_support_map_of_two_values [PreconnectedSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] {f : X → ℝ} (hf : Continuous f)
    {x y : X} (hxy : f x < f y) : (Measure.map f μ).support.Infinite := by
  have hconn : IsPreconnected (range f) := isPreconnected_range hf
  have hint : Icc (f x) (f y) ⊆ range f :=
    hconn.ordConnected.out (mem_range_self x) (mem_range_self y)
  exact (Set.Icc_infinite hxy).mono (hint.trans (range_subset_support_map μ hf))

/-- Infinite support implies the nonconcentration condition of Lemma 15 for
every finite set, in particular every set of at most k points. -/
theorem infinite_support_not_concentrated_on_finite
    [T2Space X] (μ : ProbabilityMeasure X) (hμ : (μ : Measure X).support.Infinite)
    {S : Set X} (hS : S.Finite) : (μ : Measure X) S ≠ 1 := by
  intro hmass
  have hae : S ∈ ae (μ : Measure X) := by
    rw [mem_ae_iff, measure_compl hS.measurableSet (measure_ne_top _ _), hmass, measure_univ]
    simp
  have hsub := Measure.support_subset_of_isClosed hS.isClosed hae
  exact hμ (hS.subset hsub)

end CayleyProof
