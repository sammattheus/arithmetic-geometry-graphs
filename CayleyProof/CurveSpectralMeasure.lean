module

public import CayleyProof.Theorem18Analysis
public import CayleyProof.EmpiricalSplit

/-! Connect the analytic verification to the actual coefficient-indexed
eigenvalues of the Cayley graph. The only distributional hypothesis in the
final theorem is weak convergence of the nonprincipal law. Deriving that law
from Theorem 22 remains a separate obligation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace CayleyProof

def spectralInterval (s : ℕ) : Set ℝ :=
  Set.Icc (-2 * ((s : ℝ) + 1)) (2 * ((s : ℝ) + 1))

instance spectralInterval_compact (s : ℕ) : CompactSpace (spectralInterval s) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

variable {F : Type*} [Field F] [Fintype F]

/-- Weil's estimate, as an explicit character-sum hypothesis. -/
def HasWeilBound (ψ : AddChar F ℂ) (s : ℕ) : Prop :=
  ∀ b : Fin s → F, b ≠ 0 →
    ‖∑ t : F, ψ (∑ i, b i * t ^ (i.val + 1))‖ ≤
      ((s : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ)

noncomputable def curveNonprincipalLaw (ψ : AddChar F ℂ) (s : ℕ)
    (hs : 0 < s) (hW : HasWeilBound ψ s) : ProbabilityMeasure (spectralInterval s) := by
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  exact empiricalBulk (normalizedEigenvalue ψ) 0
    (fun b hb => normalizedEigenvalue_mem_interval ψ b (by omega) (hW b hb))

theorem curve_empirical_decomposition (ψ : AddChar F ℂ) (s : ℕ)
    (hs : 0 < s) (hW : HasWeilBound ψ s) :
    (empiricalLaw (normalizedEigenvalue (s := s) ψ) : Measure ℝ) =
      bulkWithAtom (curveNonprincipalLaw ψ s hs hW)
        (principalMass (Fintype.card F : ℝ) (by have := field_card_real_ge_two (F := F); linarith) s)
        (Real.sqrt (2 * ((Fintype.card F : ℝ) - 1))) := by
  let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  rw [empiricalLaw_split (normalizedEigenvalue ψ) 0
    (fun b hb => normalizedEigenvalue_mem_interval ψ b (by omega) (hW b hb))]
  congr 1
  · apply Subtype.ext
    simp [principalMass]
  · exact normalizedEigenvalue_zero ψ

/-- Lemma 15's two uniform analytic assumptions for the actual spectrum,
conditional only on the bulk weak limit and the explicit Weil bound. The
one-atom decomposition and vanishing weighted moment are proved internally. -/
theorem curve_spectrum_lemma15_hypotheses
    {k : ℕ} (hk : 5 ≤ k)
    (E : ℕ → Type*) [∀ n, Field (E n)] [∀ n, Fintype (E n)]
    (ψ : ∀ n, AddChar (E n) ℂ)
    (hW : ∀ n, HasWeilBound (ψ n) (k / 2 + 1))
    (hq : Tendsto (fun n => (Fintype.card (E n) : ℝ)) atTop atTop)
    (ν : ProbabilityMeasure (spectralInterval (k / 2 + 1)))
    (hν : Tendsto (fun n => curveNonprincipalLaw (ψ n) (k / 2 + 1) (by omega) (hW n))
      atTop (𝓝 ν)) :
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ a ∈ normalizedPolynomialFamily (spectralInterval (k / 2 + 1)) k,
      |(∫ x, |(polynomialOfCoefficients a).eval x|
          ∂(empiricalLaw (normalizedEigenvalue (s := k / 2 + 1) (ψ n)) : Measure ℝ)) -
        ∫ x : spectralInterval (k / 2 + 1),
          |(polynomialOfCoefficients a).eval (x : ℝ)| ∂(ν : Measure _)| < ε) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ a ∈ normalizedPolynomialFamily (spectralInterval (k / 2 + 1)) k,
      (∫ x in (spectralInterval (k / 2 + 1))ᶜ, |(polynomialOfCoefficients a).eval x|
        ∂(empiricalLaw (normalizedEigenvalue (s := k / 2 + 1) (ψ n)) : Measure ℝ)) < ε) := by
  have hqone (n) : 1 ≤ (Fintype.card (E n) : ℝ) := by
    have := field_card_real_ge_two (F := E n)
    linarith
  have H := theorem18_analytic_verification hk hq hqone
    (spectral_interval_infinite (k / 2 + 1)) measurableSet_Icc hν
  dsimp only at H
  have hdecomp (n) := curve_empirical_decomposition (ψ n) (k / 2 + 1) (by omega) (hW n)
  constructor
  · intro ε hε
    filter_upwards [H.2.1 ε hε] with n hn a ha
    rw [hdecomp n]
    exact hn a ha
  · intro ε hε
    filter_upwards [H.2.2 ε hε] with n hn a ha
    rw [hdecomp n]
    exact hn a ha

end CayleyProof
