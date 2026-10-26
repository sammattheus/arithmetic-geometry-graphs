module

public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Tactic

/-! Finite empirical laws, using mathlib's uniform counting probability.
The cardinality calculation gives the normalization in Theorem 22.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal NNReal

namespace CayleyProof

noncomputable def empiricalLaw {ι X : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace X] (x : ι → X) : ProbabilityMeasure X := by
  letI : MeasurableSpace ι := ⊤
  have hx : Measurable x := measurable_of_countable x
  exact ⟨Measure.map x (uniformOn (Set.univ : Set ι)), inferInstance⟩

theorem empiricalLaw_map {ι X Y : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace X] [MeasurableSpace Y] (x : ι → X)
    (f : X → Y) (hf : Measurable f) :
    (empiricalLaw x).map f = empiricalLaw (fun i => f (x i)) := by
  let : MeasurableSpace ι := ⊤
  apply Subtype.ext
  change Measure.map f (Measure.map x (uniformOn (Set.univ : Set ι))) = _
  exact Measure.map_map hf (measurable_of_countable x)

theorem integral_empiricalLaw {ι X : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace X] (x : ι → X) (f : X → ℝ) (hf : StronglyMeasurable f) :
    (∫ z, f z ∂(empiricalLaw x : Measure X)) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, f (x i) := by
  let : MeasurableSpace ι := ⊤
  have hx : Measurable x := measurable_of_countable x
  change (∫ z, f z ∂Measure.map x (uniformOn (Set.univ : Set ι))) = _
  rw [integral_map_of_stronglyMeasurable hx hf]
  simp [uniformOn, ProbabilityTheory.cond, ENNReal.toReal_inv, integral_smul_measure,
    ENNReal.toReal_natCast, smul_eq_mul]

theorem empiricalLaw_reindex {ι κ X : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] (e : ι ≃ κ) (x : κ → X) :
    empiricalLaw (fun i => x (e i)) = empiricalLaw x := by
  apply Subtype.ext
  change (empiricalLaw (fun i => x (e i)) : Measure X) = (empiricalLaw x : Measure X)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_empiricalLaw _ _ f.continuous.stronglyMeasurable,
    integral_empiricalLaw _ _ f.continuous.stronglyMeasurable,
    Fintype.card_congr e, e.sum_comp (fun i => f (x i))]

variable {F : Type*} [Field F] [Fintype F]

instance exactDegreeCoefficients_nonempty (s : ℕ) :
    Nonempty {b : Fin (s + 1) → F // b (Fin.last s) ≠ 0} :=
  ⟨⟨fun _ => 1, one_ne_zero⟩⟩

def exactDegreeCoefficientsEquiv (s : ℕ) :
    {b : Fin (s + 1) → F // b (Fin.last s) ≠ 0} ≃
      (Fin s → F) × {t : F // t ≠ 0} where
  toFun b := (Fin.init b.val, ⟨b.val (Fin.last s), b.property⟩)
  invFun a := ⟨Fin.snoc a.1 a.2.val, by simpa using a.2.property⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv a := by ext <;> simp

open scoped Classical in
theorem card_exactDegreeCoefficients (s : ℕ) :
    Fintype.card {b : Fin (s + 1) → F // b (Fin.last s) ≠ 0} =
      (Fintype.card F - 1) * Fintype.card F ^ s := by
  rw [Fintype.card_congr (exactDegreeCoefficientsEquiv (F := F) s), Fintype.card_prod]
  simp [Fintype.card_subtype_compl, mul_comm]

end CayleyProof
