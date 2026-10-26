module

public import CayleyProof.CompactTrace
public import CayleyProof.KatzSamples
public import CayleyProof.EquidistributionPushforward

@[expose] public section

open MeasureTheory Filter Matrix
open scoped BigOperators Topology Classical

namespace CayleyProof

variable {K : Type*} [Group K] [TopologicalSpace K]
  [MeasurableSpace K] [BorelSpace K] [CompactSpace K]

noncomputable def representedNegativeTrace {m : ℕ}
    (M : K →* (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)ˣ)
    (hM : Continuous (fun x => (M x).val)) : C(K, ℝ) :=
  ⟨fun x => negativeRealTrace (M x).val, continuous_negativeRealTrace.comp hM⟩

omit [MeasurableSpace K] [BorelSpace K] [CompactSpace K] in
theorem representedNegativeTrace_central {m : ℕ}
    (M : K →* (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)ˣ)
    (hM : Continuous (fun x => (M x).val)) (x y : K) :
    representedNegativeTrace M hM (y * x * y⁻¹) = representedNegativeTrace M hM x := by
  change -(Matrix.trace (M (y * x * y⁻¹)).val).re = -(Matrix.trace (M x).val).re
  simp only [map_mul, map_inv, Units.val_mul]
  rw [Matrix.trace_units_conj]

/-- Full-support Haar measure and SU containment imply the complete scalar
conclusion, after Deligne's class-function equidistribution.  The characters
used to define the actual laws may vary arbitrarily with the field. -/
theorem katz_law_of_compact_frobenius
    (m : ℕ) (E : ℕ → Type*) [∀ n, Field (E n)] [∀ n, Fintype (E n)]
    (ψ χ : ∀ n, AddChar (E n) ℂ) (hψ : ∀ n, (ψ n).IsPrimitive)
    (hχ : ∀ n, χ n ≠ 1)
    (M : K →* (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)ˣ)
    (hM : Continuous (fun x => (M x).val))
    (hunitary : ∀ x, (M x).val ∈ Matrix.unitaryGroup (Fin (m + 2)) ℂ)
    (hSU : ∀ A ∈ Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ, ∃ x, (M x).val = A)
    (haar : ProbabilityMeasure K) [(haar : Measure K).IsOpenPosMeasure]
    (θ : ∀ n, {b : Fin (m + 3) → E n // b (Fin.last (m + 2)) ≠ 0} → K)
    (htrace : ∀ n b, representedNegativeTrace M hM (θ n b) =
      normalizedCharacterSum (ψ n) b.val)
    (hEq : ∀ f : C(K, ℝ), (∀ x y, f (y * x * y⁻¹) = f x) →
      Tendsto (fun n =>
        (Fintype.card {b : Fin (m + 3) → E n // b (Fin.last (m + 2)) ≠ 0} : ℝ)⁻¹ *
          ∑ b, f (θ n b)) atTop (𝓝 (∫ x, f x ∂(haar : Measure K)))) :
    ∃ μ : ProbabilityMeasure ℝ,
      Tendsto (fun n => katzSampleLaw (χ n) (m + 2)) atTop (𝓝 μ) ∧
      (μ : Measure ℝ).support ⊆ Set.Icc (-(m + 2 : ℝ)) (m + 2 : ℝ) ∧
      (μ : Measure ℝ).support.Infinite := by
  let φ := representedNegativeTrace M hM
  refine ⟨haar.map φ, ?_, ?_, ?_⟩
  · have ht := equidistribution_pushforward
      (fun n => {b : Fin (m + 3) → E n // b (Fin.last (m + 2)) ≠ 0})
      θ haar φ (representedNegativeTrace_central M hM) hEq
    have hlaw : ∀ n, katzSampleLaw (χ n) (m + 2) =
        empiricalLaw (fun b => φ (θ n b)) := by
      intro n
      rw [katzSampleLaw_character_independent (hψ n) (hχ n), katzSampleLaw]
      congr 1
      funext b
      exact (htrace n b).symm
    simpa only [hlaw] using ht
  · change (Measure.map φ (haar : Measure K)).support ⊆ _
    rw [support_map_eq_range (haar : Measure K) φ.continuous]
    rintro _ ⟨x, rfl⟩
    change negativeRealTrace (M x).val ∈ Set.Icc (-(m + 2 : ℝ)) (m + 2 : ℝ)
    have hx := negativeRealTrace_mem_interval (hunitary x)
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using hx
  · change (Measure.map φ (haar : Measure K)).support.Infinite
    have hint : Set.Icc (-(m : ℝ) - 2) (2 - (m : ℝ)) ⊆ Set.range φ := by
      have hh := interval_subset_negativeRealTrace_range m
        (Set.range (fun x => (M x).val)) hSU
      intro y hy
      obtain ⟨⟨A, x, hx⟩, hA⟩ := hh hy
      exact ⟨x, by simpa [φ, representedNegativeTrace, hx] using hA⟩
    exact (Set.Icc_infinite (by linarith : -(m : ℝ) - 2 < 2 - (m : ℝ))).mono
      (hint.trans (range_subset_support_map (haar : Measure K) φ.continuous))

end CayleyProof
