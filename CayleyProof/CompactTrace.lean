module

public import CayleyProof.PushforwardSupport
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Tactic

/-! The compact-group support argument in Theorem 22. The matrices, special
unitary group, trace, and measure support are mathlib objects. The hypothesis
that the compact monodromy group contains SU is explicit here.
-/

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators Topology ComplexConjugate

namespace CayleyProof

noncomputable def negativeRealTrace {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : ℝ := -(Matrix.trace A).re

theorem continuous_negativeRealTrace {n : Type*} [Fintype n] :
    Continuous (negativeRealTrace (n := n)) := by
  unfold negativeRealTrace Matrix.trace
  fun_prop

theorem negativeRealTrace_mem_interval {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A ∈ Matrix.unitaryGroup n ℂ) :
    negativeRealTrace A ∈ Set.Icc (-(Fintype.card n : ℝ)) (Fintype.card n : ℝ) := by
  have h : |negativeRealTrace A| ≤ (Fintype.card n : ℝ) := by
    unfold negativeRealTrace
    rw [abs_neg]
    apply (Complex.abs_re_le_norm _).trans
    unfold Matrix.trace
    calc
      ‖∑ i : n, A i i‖ ≤ ∑ i : n, ‖A i i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => entry_norm_bound_of_unitary hA i i)
      _ = _ := by simp
  exact abs_le.mp h

noncomputable def specialDiagonal (m : ℕ) (θ : ℝ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  Matrix.diagonal (Fin.cons (Complex.exp (θ * Complex.I))
    (Fin.cons (Complex.exp (-(θ * Complex.I))) (fun _ : Fin m => 1)))

theorem specialDiagonal_mem_specialUnitary (m : ℕ) (θ : ℝ) :
    specialDiagonal m θ ∈ Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [specialDiagonal, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => (unitary ℂ).one_mem) j) i
    · simp [Unitary.mem_iff, ← Complex.exp_conj, ← Complex.exp_add]
    · simp [Unitary.mem_iff, ← Complex.exp_conj, ← Complex.exp_add]
  · simp [specialDiagonal, Matrix.det_diagonal, Fin.prod_univ_succ,
      ← Complex.exp_add]

theorem negativeRealTrace_specialDiagonal (m : ℕ) (θ : ℝ) :
    negativeRealTrace (specialDiagonal m θ) = -((m : ℝ) + 2 * Real.cos θ) := by
  simp [negativeRealTrace, specialDiagonal, Matrix.trace_diagonal, Fin.sum_univ_succ,
    Complex.exp_re]
  ring

/-- The two-dimensional diagonal rotation gives a genuine interval in the
trace image, even when the ambient compact group is disconnected. -/
theorem interval_subset_negativeRealTrace_range (m : ℕ)
    (K : Set (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ))
    (hSU : (Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ : Set _) ⊆ K) :
    Set.Icc (-(m : ℝ) - 2) (2 - (m : ℝ)) ⊆
      Set.range (fun A : K => negativeRealTrace (A.val)) := by
  have hcont : Continuous (fun θ : ℝ => -((m : ℝ) + 2 * Real.cos θ)) := by fun_prop
  have hconn := isPreconnected_range hcont
  have h0 : -(m : ℝ) - 2 ∈ Set.range (fun θ : ℝ => -((m : ℝ) + 2 * Real.cos θ)) := by
    refine ⟨0, ?_⟩
    simp
    ring
  have hpi : 2 - (m : ℝ) ∈ Set.range (fun θ : ℝ => -((m : ℝ) + 2 * Real.cos θ)) := by
    refine ⟨Real.pi, ?_⟩
    simp
    ring
  intro y hy
  obtain ⟨θ, rfl⟩ := hconn.ordConnected.out h0 hpi hy
  exact ⟨⟨specialDiagonal m θ, hSU (specialDiagonal_mem_specialUnitary m θ)⟩,
    negativeRealTrace_specialDiagonal m θ⟩

/-- Apply to Haar probability on a compact matrix group containing SU.
The interval is [1-d,5-d] when d=m+3. -/
theorem compact_trace_support_contains_interval (m : ℕ)
    (K : Set (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ))
    (hSU : (Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ : Set _) ⊆ K)
    (μ : Measure K) [μ.IsOpenPosMeasure] :
    Set.Icc (-(m : ℝ) - 2) (2 - (m : ℝ)) ⊆
      (Measure.map (fun A : K => negativeRealTrace A.val) μ).support :=
  (interval_subset_negativeRealTrace_range m K hSU).trans
    (range_subset_support_map μ (continuous_negativeRealTrace.comp continuous_subtype_val))

theorem compact_trace_support_infinite (m : ℕ)
    (K : Set (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ))
    (hSU : (Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ : Set _) ⊆ K)
    (μ : Measure K) [μ.IsOpenPosMeasure] :
    (Measure.map (fun A : K => negativeRealTrace A.val) μ).support.Infinite :=
  (Set.Icc_infinite (by linarith : -(m : ℝ) - 2 < 2 - (m : ℝ))).mono
    (compact_trace_support_contains_interval m K hSU μ)

end CayleyProof
