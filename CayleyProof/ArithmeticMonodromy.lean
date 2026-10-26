module

public import CayleyProof.MonomialFrobenius
public import CayleyProof.ScalarTwistMonodromy
public import CayleyProof.ArithmeticGeneration

/-! Assembly of the monodromy argument, with both topologies explicit.
The ordinary topology on G is the l-adic topology of the representation.
`zariski` is used only for the geometric closures and connected SL subgroup.
-/

@[expose] public section

open scoped BigOperators

namespace CayleyProof

theorem arithmetic_image_le_from_full_family
    {F : Type*} [Field F] [Fintype F]
    (E : ℕ → Type*) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    (hrank : ∀ n, Module.finrank F (E n) = n + 1)
    {d v : ℕ} (hd : 0 < d) (hdiv : d ∣ Fintype.card F - 1)
    (hcard : Fintype.card F = v ^ 2)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (hHD : ∀ n, HasseDavenportIdentity (E := E n) ψ)
    (c : ℂ) (hc : c ^ 2 * Fintype.card F = 1)
    {P Q G Γ : Type*}
    [Group P] [TopologicalSpace P] [CompactSpace P]
    [Group Q] [TopologicalSpace Q] [T2Space Q]
    [Group G] [tEll : TopologicalSpace G] [IsTopologicalGroup G]
    (π : P →* Q) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (ρ : P →* G) (hρ : Continuous ρ)
    (det : G →* ℂˣ)
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
    (eigenvalues : Fˣ → Fin (d - 1) → ℂ)
    (hdet : ∀ u, (det (ρ (frob u))).val = ∏ i, eigenvalues u i)
    (htrace : ∀ (u : Fˣ) (n : ℕ),
      (∑ i, eigenvalues u i ^ (n + 1)) =
        -(c ^ (n + 1)) * ∑ t : E n,
          traceLift (E := E n) ψ (algebraMap F (E n) (u : F) * t ^ d)) :
    ρ.range ≤ H₀ := by
  let : TopologicalSpace G := tEll
  have hker : ∀ x ∈ π.ker, ρ x ∈ H₀ := by
    intro x hx
    rw [show (ρ x ∈ H₀) = (ρ x ∈ (H₀ : Set G)) from rfl, hclosure]
    exact @subset_closure G zariski _ _ ⟨⟨x, hx⟩, rfl⟩
  have hSL₀ : det.ker ≤ H₀ := by
    let : TopologicalSpace G := zariski
    let : SeparatelyContinuousMul G := hsep
    exact scalar_twist_transfers_connected_monodromy ρfull (fun x : π.ker => ρ x.val)
      r α hfactor H₀ hH₀Z (fun x => hker x.val x.property)
      T hT hα hSL det.ker.one_mem hKatz
  obtain ⟨u, hu⟩ := exists_determinant_one_from_monomial_traces E hrank hd hdiv hcard
    ψ hψ hHD c hc eigenvalues (fun u => (det (ρ (frob u))).val) hdet htrace
  apply representation_range_le_of_kernel_and_generator π hπ hsurj (frob u) (hgen u)
    ρ hρ H₀ hH₀ hker
  apply hSL₀
  change det (ρ (frob u)) = 1
  exact Units.ext hu

end CayleyProof
