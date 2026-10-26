module

public import CayleyProof.PolynomialGrowth
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-! The compact polynomial family in Lemma 15. We use mathlib's existing
linear equivalence between polynomials of degree < k+1 and their coefficients.
The coefficient model carries its existing finite-dimensional normed topology.
The normalization itself is the uniform norm on the compact set I.
-/

@[expose] public section

open scoped BigOperators Topology BoundedContinuousFunction

namespace CayleyProof

noncomputable def polynomialOfCoefficients {k : ℕ} (a : Fin (k + 1) → ℝ) : Polynomial ℝ :=
  ((Polynomial.degreeLTEquiv ℝ (k + 1)).symm a).val

theorem polynomialOfCoefficients_eval {k : ℕ} (a : Fin (k + 1) → ℝ) (x : ℝ) :
    (polynomialOfCoefficients a).eval x = ∑ i, a i * x ^ (i : ℕ) := by
  have hp := ((Polynomial.degreeLTEquiv ℝ (k + 1)).symm a).property
  unfold polynomialOfCoefficients
  rw [Polynomial.eval_eq_sum_degreeLTEquiv hp]
  simp

theorem polynomialOfCoefficients_injective {k : ℕ} :
    Function.Injective (@polynomialOfCoefficients k) := by
  intro a b h
  exact (Polynomial.degreeLTEquiv ℝ (k + 1)).symm.injective (Subtype.ext h)

/-- Every polynomial of degree at most k is represented by its first k+1
coefficients. Thus the coefficient model does not omit any test polynomial. -/
theorem polynomialOfCoefficients_coefficients (p : Polynomial ℝ) {k : ℕ}
    (hdeg : p.natDegree ≤ k) :
    polynomialOfCoefficients (fun i : Fin (k + 1) => p.coeff i) = p := by
  have hp : p ∈ Polynomial.degreeLT ℝ (k + 1) :=
    Polynomial.mem_degreeLT.mpr
      (p.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hdeg))
  change (((Polynomial.degreeLTEquiv ℝ (k + 1)).symm
    ((Polynomial.degreeLTEquiv ℝ (k + 1)) ⟨p, hp⟩)).val) = p
  rw [LinearEquiv.symm_apply_apply]

variable (I : Set ℝ) [CompactSpace I] (k : ℕ)

/-- Evaluation on I, as a linear map into bounded continuous functions. -/
noncomputable def polynomialRestriction : (Fin (k + 1) → ℝ) →ₗ[ℝ] (I →ᵇ ℝ) where
  toFun a := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ∑ i, a i * (x : ℝ) ^ (i : ℕ), by fun_prop⟩
  map_add' a b := by ext x; simp [Finset.sum_add_distrib, add_mul]
  map_smul' c a := by ext x; simp [Finset.mul_sum, mul_assoc]

@[simp] theorem polynomialRestriction_apply (a : Fin (k + 1) → ℝ) (x : I) :
    polynomialRestriction I k a x = (polynomialOfCoefficients a).eval (x : ℝ) :=
  (polynomialOfCoefficients_eval a x).symm

theorem polynomialRestriction_injective (hI : I.Infinite) :
    Function.Injective (polynomialRestriction I k) := by
  intro a b h
  apply polynomialOfCoefficients_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply hI.mono
  intro x hx
  have := congrArg (fun f : I →ᵇ ℝ => f ⟨x, hx⟩) h
  simpa using this

/-- The coefficient representatives of S_k. -/
def normalizedPolynomialFamily : Set (Fin (k + 1) → ℝ) :=
  {a | ‖polynomialRestriction I k a‖ = 1}

theorem uniform_coefficient_bound (hI : I.Infinite) :
    ∃ C > (0 : ℝ), ∀ a ∈ normalizedPolynomialFamily I k, ‖a‖ ≤ C := by
  obtain ⟨K, hK, hanti⟩ :=
    (polynomialRestriction I k).injective_iff_antilipschitz.mp
      (polynomialRestriction_injective I k hI)
  refine ⟨K, by exact_mod_cast hK, fun a ha => ?_⟩
  have h := hanti.le_mul_norm (map_zero (polynomialRestriction I k)) a
  change ‖polynomialRestriction I k a‖ = 1 at ha
  simpa only [ha, mul_one] using h

theorem normalizedPolynomialFamily_isCompact (hI : I.Infinite) :
    IsCompact (normalizedPolynomialFamily I k) := by
  obtain ⟨C, _, hC⟩ := uniform_coefficient_bound I k hI
  apply (isCompact_closedBall (0 : Fin (k + 1) → ℝ) C).of_isClosed_subset
  · exact isClosed_eq ((polynomialRestriction I k).continuous_of_finiteDimensional.norm)
      continuous_const
  · intro a ha
    simpa only [Metric.mem_closedBall, dist_zero_right] using hC a ha

/-- A uniform polynomial growth bound for every member of the normalized family. -/
theorem normalized_polynomial_growth (hI : I.Infinite) :
    ∃ C > (0 : ℝ), ∀ a ∈ normalizedPolynomialFamily I k, ∀ x : ℝ,
      |(polynomialOfCoefficients a).eval x| ≤ C * (1 + |x| ^ k) := by
  obtain ⟨K, hK, hcoeff⟩ := uniform_coefficient_bound I k hI
  refine ⟨(k + 1) * K, by positivity, fun a ha x => ?_⟩
  rw [polynomialOfCoefficients_eval]
  calc
    |∑ i : Fin (k + 1), a i * x ^ (i : ℕ)|
        ≤ ∑ i : Fin (k + 1), |a i * x ^ (i : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (k + 1), K * (1 + |x| ^ k) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow]
      exact mul_le_mul
        ((show |a i| ≤ ‖a‖ from norm_le_pi_norm a i).trans (hcoeff a ha))
        (abs_pow_le_one_add (by omega) x) (by positivity) hK.le
    _ = _ := by simp; ring

/-- Pointwise absolute value is a continuous operation in the uniform norm. -/
theorem continuous_normComp {X : Type*} [TopologicalSpace X] :
    Continuous (fun f : X →ᵇ ℝ => f.normComp) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
  intro x
  exact (dist_norm_norm_le (f x) (g x)).trans
    (by simpa only [dist_eq_norm] using
      (BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) x))

/-- The actual family |p| on I is compact in the uniform norm. -/
theorem absolutePolynomialFamily_isCompact (hI : I.Infinite) :
    IsCompact ((fun a => (polynomialRestriction I k a).normComp) ''
      normalizedPolynomialFamily I k) :=
  (normalizedPolynomialFamily_isCompact I k hI).image
    (continuous_normComp.comp (polynomialRestriction I k).continuous_of_finiteDimensional)

end CayleyProof
