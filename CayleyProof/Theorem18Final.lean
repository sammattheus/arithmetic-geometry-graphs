module

public import CayleyProof.Theorem22Final
public import CayleyProof.Theorem18FromKatz
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Both assumptions of Lemma 15 for the actual normalized Cayley spectrum.
There is no equidistribution or tail-moment hypothesis in this theorem.
Theorem 22 and the approved Weil input supply the necessary inputs to the
already checked analytic argument.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace CayleyProof

theorem extension_cardinality_tendsto
    (F : Type) [Field F] [Fintype F]
    (E : ℕ → Type) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    (hrank : ∀ n, Module.finrank F (E n) = n + 1) :
    Tendsto (fun n => (Fintype.card (E n) : ℝ)) atTop atTop := by
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := F)
  have H := (tendsto_pow_atTop_atTop_of_one_lt hq).comp (tendsto_add_atTop_nat 1)
  have heq : (fun n => (Fintype.card (E n) : ℝ)) =
      (fun n => (Fintype.card F : ℝ) ^ (n + 1)) := by
    funext n
    have hc : Fintype.card (E n) = Fintype.card F ^ (n + 1) := by
      rw [Module.card_eq_pow_finrank (K := F), hrank]
    exact_mod_cast hc
  rw [heq]
  exact H

theorem theorem18_lemma15_assumptions
    (k p a : ℕ) (hk : 5 ≤ k) [Fact p.Prime] (hp : 5 < p)
    (hkp : k / 2 + 1 < p) (ha : 1 ≤ a)
    (hdiv : k / 2 + 1 ∣ p ^ (2 * a) - 1)
    (F : Type) [Field F] [Fintype F] [CharP F p]
    (hF : Fintype.card F = p ^ (2 * a))
    (E : ℕ → Type) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    (hrank : ∀ n, Module.finrank F (E n) = n + 1)
    (ψ : ∀ n, AddChar (E n) ℂ) (hψ : ∀ n, ψ n ≠ 1) :
    let I := spectralInterval (k / 2 + 1)
    ∃ ν : ProbabilityMeasure I,
      (∀ S : Set I, S.Finite → (ν : Measure I) S < 1) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, ∀ b ∈ normalizedPolynomialFamily I k,
        |(∫ x, |(polynomialOfCoefficients b).eval x|
            ∂(empiricalLaw (normalizedEigenvalue (s := k / 2 + 1) (ψ n)) : Measure ℝ)) -
          ∫ x : I, |(polynomialOfCoefficients b).eval (x : ℝ)| ∂(ν : Measure I)| < ε) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, ∀ b ∈ normalizedPolynomialFamily I k,
        (∫ x in Iᶜ, |(polynomialOfCoefficients b).eval x|
          ∂(empiricalLaw (normalizedEigenvalue (s := k / 2 + 1) (ψ n)) : Measure ℝ)) < ε) := by
  have hd : 3 ≤ k / 2 + 1 := by omega
  have hpd : ¬ p ∣ k / 2 + 1 := Nat.not_dvd_of_pos_of_lt (by omega) hkp
  obtain ⟨μ, hconv, hsupp, hinf⟩ := theorem22 (k / 2 + 1) p a hd hp hpd ha hdiv
    F hF E hrank ψ hψ
  have hW : ∀ n, HasWeilBound (ψ n) (k / 2 + 1) := by
    intro n
    let : CharP (E n) p := charP_of_injective_algebraMap (algebraMap F (E n)).injective p
    exact External.weilCharacterSumBound (E n) p (k / 2 + 1) hkp (ψ n) (hψ n)
  have hsupp' : (μ : Measure ℝ).support ⊆
      Set.Icc (-(k / 2 : ℕ) : ℝ) (k / 2 : ℕ) := by
    convert hsupp using 1; simp
  refine ⟨μ.map (scaledSpectralClip (k / 2 + 1)), ?_⟩
  exact theorem18_lemma15_assumptions_from_katz hk E ψ hW
    (extension_cardinality_tendsto F E hrank) μ
    (by simpa using hconv) hinf hsupp'

end CayleyProof
