module

public import CayleyProof.EmpiricalMeasure
public import CayleyProof.Lemma15Verification

/-! An exact decomposition of a finite empirical measure into its
nonprincipal law and its one distinguished atom. Multiplicities are retained.
-/

@[expose] public section

open MeasureTheory
open scoped Classical Topology NNReal BoundedContinuousFunction

namespace CayleyProof

variable {ι : Type*} [Fintype ι] [Nontrivial ι]

instance nonempty_ne_index (i : ι) : Nonempty {j : ι // j ≠ i} :=
  let ⟨j, hj⟩ := exists_ne i
  ⟨⟨j, hj⟩⟩

noncomputable def empiricalBulk {I : Set ℝ} (x : ι → ℝ) (i₀ : ι)
    (hx : ∀ i, i ≠ i₀ → x i ∈ I) : ProbabilityMeasure I :=
  empiricalLaw (fun i : {i : ι // i ≠ i₀} => (⟨x i.val, hx i.val i.property⟩ : I))

theorem empiricalLaw_split {I : Set ℝ} [CompactSpace I]
    (x : ι → ℝ) (i₀ : ι) (hx : ∀ i, i ≠ i₀ → x i ∈ I) :
    (empiricalLaw x : Measure ℝ) =
      bulkWithAtom (empiricalBulk x i₀ hx) (Fintype.card ι : ℝ≥0)⁻¹ (x i₀) := by
  have hN : 1 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.one_lt_card (α := ι)
  have hw : (Fintype.card ι : ℝ≥0)⁻¹ ≤ 1 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_inv, NNReal.coe_one, NNReal.coe_natCast]
    exact inv_le_one_of_one_le₀ hN.le
  let : IsProbabilityMeasure
      (bulkWithAtom (empiricalBulk x i₀ hx) (Fintype.card ι : ℝ≥0)⁻¹ (x i₀)) :=
    bulkWithAtom_probability _ hw _
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_empiricalLaw _ _ f.continuous.stronglyMeasurable, integral_bulkWithAtom _ hw]
  unfold empiricalBulk
  rw [integral_empiricalLaw _ (fun y : I => f (y : ℝ))
    (f.continuous.comp continuous_subtype_val).stronglyMeasurable]
  simp only [NNReal.coe_inv, NNReal.coe_natCast, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Nat.cast_sub (by exact_mod_cast hN.le), Nat.cast_one]
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun i => f (x i)) i₀]
  have hcoeff :
      (1 - (Fintype.card ι : ℝ)⁻¹) * ((Fintype.card ι : ℝ) - 1)⁻¹ =
        (Fintype.card ι : ℝ)⁻¹ := by
    have hN0 : (Fintype.card ι : ℝ) ≠ 0 := by linarith
    have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hN0, hN1]
  rw [← mul_assoc, hcoeff]
  ring

end CayleyProof
