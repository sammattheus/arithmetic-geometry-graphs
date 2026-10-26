module

public import CayleyProof.SpectralBulkTransfer
public import CayleyProof.PushforwardSupport

/-! The requested part of Theorem 18, conditional on exactly the scalar
equidistribution conclusion of Theorem 22 and the explicit Weil estimate.
The transfer to the full spectrum and both uniform assumptions of Lemma 15
are derived here, rather than supplied as hypotheses.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace CayleyProof

theorem scaledSpectralClip_val_of_mem (s : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-(s : ℝ)) (s : ℝ)) :
    (scaledSpectralClip (s + 1) x : ℝ) = Real.sqrt 2 * x := by
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have := Real.sqrt_nonneg 2
    nlinarith
  have hxabs : |x| ≤ (s : ℝ) := abs_le.mpr hx
  have hmul : |Real.sqrt 2 * x| ≤ 2 * (s : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul hsqrt hxabs (abs_nonneg _) (by norm_num)
  have hmem : Real.sqrt 2 * x ∈ spectralInterval (s + 1) := by
    have H := abs_le.mp hmul
    dsimp [spectralInterval]
    push_cast
    constructor <;> linarith [H.1, H.2]
  unfold scaledSpectralClip spectralClip
  rw [Set.projIcc_of_mem _ hmem]

theorem scaledSpectralClip_injOn (s : ℕ) :
    Set.InjOn (scaledSpectralClip (s + 1)) (Set.Icc (-(s : ℝ)) (s : ℝ)) := by
  intro x hx y hy hxy
  have H := congrArg Subtype.val hxy
  rw [scaledSpectralClip_val_of_mem s hx, scaledSpectralClip_val_of_mem s hy] at H
  exact mul_left_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne' H

theorem scaledKatzLimit_support_infinite (s : ℕ) (μ : ProbabilityMeasure ℝ)
    (hinf : (μ : Measure ℝ).support.Infinite)
    (hsupp : (μ : Measure ℝ).support ⊆ Set.Icc (-(s : ℝ)) (s : ℝ)) :
    (μ.map (scaledSpectralClip (s + 1)) : Measure (spectralInterval (s + 1))).support.Infinite := by
  have hi := hinf.image ((scaledSpectralClip_injOn s).mono hsupp)
  exact hi.mono (image_support_subset_support_map (μ : Measure ℝ)
    (continuous_scaledSpectralClip (s + 1)))

/-- Both uniform convergence assumptions for the actual graph eigenvalues,
and nonconcentration of the limiting probability on every finite set.

The input `hKatz` is deliberately explicit: Theorem 22 is NOT black-boxed or
claimed to be proved by this theorem. Once its proof is finished, applying
this theorem completes the specified analytic step of Theorem 18.
-/
theorem theorem18_lemma15_assumptions_from_katz
    {k : ℕ} (hk : 5 ≤ k)
    (E : ℕ → Type*) [∀ n, Field (E n)] [∀ n, Fintype (E n)]
    (ψ : ∀ n, AddChar (E n) ℂ)
    (hW : ∀ n, HasWeilBound (ψ n) (k / 2 + 1))
    (hq : Tendsto (fun n => (Fintype.card (E n) : ℝ)) atTop atTop)
    (μ : ProbabilityMeasure ℝ)
    (hKatz : Tendsto (fun n => katzSampleLaw (ψ n) (k / 2)) atTop (𝓝 μ))
    (hinf : (μ : Measure ℝ).support.Infinite)
    (hsupp : (μ : Measure ℝ).support ⊆ Set.Icc (-(k / 2 : ℕ) : ℝ) (k / 2 : ℕ)) :
    let I := spectralInterval (k / 2 + 1)
    let ν := μ.map (scaledSpectralClip (k / 2 + 1))
    (∀ S : Set I, S.Finite → (ν : Measure I) S < 1) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ a ∈ normalizedPolynomialFamily I k,
      |(∫ x, |(polynomialOfCoefficients a).eval x|
          ∂(empiricalLaw (normalizedEigenvalue (s := k / 2 + 1) (ψ n)) : Measure ℝ)) -
        ∫ x : I, |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(ν : Measure I)| < ε) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ a ∈ normalizedPolynomialFamily I k,
      (∫ x in Iᶜ, |(polynomialOfCoefficients a).eval x|
        ∂(empiricalLaw (normalizedEigenvalue (s := k / 2 + 1) (ψ n)) : Measure ℝ)) < ε) := by
  dsimp only
  refine ⟨?_, curve_spectrum_lemma15_hypotheses hk E ψ hW hq _
    (curveNonprincipalLaw_tendsto_of_katz (k / 2) E ψ hW hq μ hKatz)⟩
  intro S hS
  exact lt_of_le_of_ne (prob_le_one)
    (infinite_support_not_concentrated_on_finite _
      (scaledKatzLimit_support_infinite (k / 2) μ hinf hsupp) hS)

end CayleyProof
