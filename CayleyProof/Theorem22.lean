module

public import CayleyProof.ArithmeticMonodromy
public import CayleyProof.CompactFrobeniusLaw

/-! The complete deduction of the scalar distribution from explicitly listed
cohomological data.  In particular, arithmetic containment, zero-slice SL
containment, determinant one, and scalar-law convergence are NOT inputs.

This theorem does not itself construct the l-adic cohomological data from
the coefficient scheme.  The remaining instantiation obligation is recorded
in FOUNDATIONS.md; it must not be confused with a proof of their existence.
-/

@[expose] public section

open MeasureTheory Filter Matrix
open scoped BigOperators Topology Classical

namespace CayleyProof

theorem theorem22_from_cohomological_data
    (m : ℕ) {F : Type*} [Field F] [Fintype F]
    (E : ℕ → Type*) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    (hrank : ∀ n, Module.finrank F (E n) = n + 1)
    {v : ℕ} (hdiv : m + 3 ∣ Fintype.card F - 1) (hcard : Fintype.card F = v ^ 2)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (χ : ∀ n, AddChar (E n) ℂ) (hχ : ∀ n, χ n ≠ 1)
    (hHD : ∀ n, HasseDavenportIdentity (E := E n) ψ)
    (c : ℂ) (hc : c ^ 2 * Fintype.card F = 1)
    {P Q G Γ : Type*}
    [Group P] [TopologicalSpace P] [CompactSpace P]
    [Group Q] [TopologicalSpace Q] [T2Space Q]
    [Group G] [tEll : TopologicalSpace G] [IsTopologicalGroup G]
    (π : P →* Q) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (ρ : P →* G) (hρ : Continuous ρ) (det : G →* ℂˣ)
    (zariski : TopologicalSpace G) (hsep : @SeparatelyContinuousMul G zariski _)
    (H₀ : Subgroup G) (hH₀ : @IsClosed G tEll (H₀ : Set G))
    (hH₀Z : @IsClosed G zariski (H₀ : Set G))
    (hclosure : (H₀ : Set G) = @closure G zariski
      (Set.range (fun x : π.ker => ρ x.val)))
    (hSL : @IsPreconnected G zariski (det.ker : Set G))
    (ρfull : Γ → G) (r : Γ → π.ker) (α : Γ → G)
    (hfactor : ∀ γ, ρfull γ = α γ * ρ (r γ).val)
    (T : Set G) (hT : T.Finite) (hα : ∀ γ, α γ ∈ T)
    (hKatz : (det.ker : Set G) ⊆ @closure G zariski (Set.range ρfull))
    (frob : Fˣ → P) (hgen : ∀ u, DenseRange (fun n : ℤ => π (frob u) ^ n))
    (eigenvalues : Fˣ → Fin (m + 2) → ℂ)
    (hdet : ∀ u, (det (ρ (frob u))).val = ∏ i, eigenvalues u i)
    (hpowerTrace : ∀ (u : Fˣ) (n : ℕ),
      (∑ i, eigenvalues u i ^ (n + 1)) =
        -(c ^ (n + 1)) * ∑ t : E n,
          traceLift (E := E n) ψ (algebraMap F (E n) (u : F) * t ^ (m + 3)))
    {K : Type*} [Group K] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
    [CompactSpace K]
    (M : K →* (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)ˣ)
    (hM : Continuous (fun x => (M x).val))
    (hunitary : ∀ x, (M x).val ∈ Matrix.unitaryGroup (Fin (m + 2)) ℂ)
    (hcompact : det.ker ≤ H₀ →
      ∀ A ∈ Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ, ∃ x, (M x).val = A)
    (haar : ProbabilityMeasure K) [(haar : Measure K).IsOpenPosMeasure]
    (θ : ∀ n, {b : Fin (m + 3) → E n // b (Fin.last (m + 2)) ≠ 0} → K)
    (htrace : ∀ n b, representedNegativeTrace M hM (θ n b) =
      normalizedCharacterSum (traceLift (E := E n) ψ) b.val)
    (hDeligne : ρ.range ≤ H₀ → ∀ f : C(K, ℝ),
      (∀ x y, f (y * x * y⁻¹) = f x) →
      Tendsto (fun n =>
        (Fintype.card {b : Fin (m + 3) → E n // b (Fin.last (m + 2)) ≠ 0} : ℝ)⁻¹ *
          ∑ b, f (θ n b)) atTop (𝓝 (∫ x, f x ∂(haar : Measure K)))) :
    ∃ μ : ProbabilityMeasure ℝ,
      Tendsto (fun n => katzSampleLaw (χ n) (m + 2)) atTop (𝓝 μ) ∧
      (μ : Measure ℝ).support ⊆ Set.Icc (-(m + 2 : ℝ)) (m + 2 : ℝ) ∧
      (μ : Measure ℝ).support.Infinite := by
  let : TopologicalSpace G := tEll
  have hSL₀ : det.ker ≤ H₀ := by
    let : TopologicalSpace G := zariski
    let : SeparatelyContinuousMul G := hsep
    apply scalar_twist_transfers_connected_monodromy ρfull (fun x : π.ker => ρ x.val)
      r α hfactor H₀ hH₀Z ?_ T hT hα hSL det.ker.one_mem hKatz
    intro x
    change ρ x.val ∈ (H₀ : Set G)
    rw [hclosure]
    exact subset_closure ⟨x, rfl⟩
  have hArith : ρ.range ≤ H₀ := arithmetic_image_le_from_full_family E hrank
    (by omega : 0 < m + 3) hdiv hcard ψ hψ hHD c hc
    π hπ hsurj ρ hρ det zariski hsep H₀ hH₀ hH₀Z hclosure hSL
    ρfull r α hfactor T hT hα hKatz frob hgen eigenvalues hdet hpowerTrace
  have hψ₁ : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ one_ne_zero
  exact katz_law_of_compact_frobenius m E (fun n => traceLift (E := E n) ψ) χ
    (fun _ => AddChar.IsPrimitive.of_ne_one (traceLift_nontrivial hψ₁)) hχ
    M hM hunitary (hcompact hSL₀) haar θ htrace (hDeligne hArith)

end CayleyProof
