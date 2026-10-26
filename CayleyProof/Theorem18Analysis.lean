module

public import CayleyProof.Lemma15Verification
public import CayleyProof.NormalizedSpectrum

/-! Assembly of the analytic verification for the dimensions in Theorem 18.
The remaining spectral-distribution input is stated explicitly as weak
convergence of the nonprincipal law on the fixed compact interval.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal

namespace CayleyProof

noncomputable def principalMass (q : ℝ) (hq : 1 ≤ q) (s : ℕ) : ℝ≥0 :=
  ⟨(q ^ s)⁻¹, inv_nonneg.mpr (pow_nonneg (by linarith) _)⟩

@[simp] theorem principalMass_coe (q : ℝ) (hq : 1 ≤ q) (s : ℕ) :
    (principalMass q hq s : ℝ) = (q ^ s)⁻¹ := rfl

theorem principalMass_le_one (q : ℝ) (hq : 1 ≤ q) (s : ℕ) :
    principalMass q hq s ≤ 1 := by
  change (q ^ s)⁻¹ ≤ (1 : ℝ)
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hq)

/-- Both uniform hypotheses, with the actual exponent and exceptional
eigenvalue used for the curve graph. This theorem has no arithmetic black boxes;
its sole distribution input is the displayed bulk weak convergence. -/
theorem theorem18_analytic_verification
    {k : ℕ} (hk : 5 ≤ k)
    {q : ℕ → ℝ} (hq : Tendsto q atTop atTop) (hqone : ∀ n, 1 ≤ q n)
    {I : Set ℝ} [CompactSpace I] (hI : I.Infinite) (hImeas : MeasurableSet I)
    {νn : ℕ → ProbabilityMeasure I} {ν : ProbabilityMeasure I}
    (hν : Tendsto νn atTop (𝓝 ν)) :
    let w := fun n => principalMass (q n) (hqone n) (k / 2 + 1)
    let e := fun n => Real.sqrt (2 * (q n - 1))
    let μn := fun n => bulkWithAtom (νn n) (w n) (e n)
    (∀ n, IsProbabilityMeasure (μn n)) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ a ∈ normalizedPolynomialFamily I k,
      |(∫ x, |(polynomialOfCoefficients a).eval x| ∂μn n) -
        ∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(ν : Measure I)| < ε) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ a ∈ normalizedPolynomialFamily I k,
      (∫ x in Iᶜ, |(polynomialOfCoefficients a).eval x| ∂μn n) < ε) := by
  dsimp only
  have hw (n) := principalMass_le_one (q n) (hqone n) (k / 2 + 1)
  have ht := graph_principal_moment_tendsto_zero hq hqone hk
  refine ⟨fun n => bulkWithAtom_probability _ (hw n) _, ?_, ?_⟩
  · exact lemma15_uniform_integrals hν hI k hw ht
  · exact lemma15_uniform_tails hI hImeas k νn ht

end CayleyProof
