module

public import CayleyProof.FiniteIndex
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Tactic

/-! Passing the connected subgroup supplied by Katz from the full family to
the zero-constant family.  This file works with the Zariski topology on the
matrix group: only separate continuity is used.  No l-adic connectedness
assumption is made.
-/

@[expose] public section

namespace CayleyProof

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- A connected set through 1 covered by finitely many cosets of a closed
subgroup is contained in that subgroup.  Representatives need not lie in
the connected set or in any prescribed ambient monodromy subgroup. -/
theorem connected_subset_of_finite_cosets (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (T : Set G) (hT : T.Finite)
    {S : Set G} (hS : IsPreconnected S) (h1 : (1 : G) ∈ S)
    (hcover : ∀ g ∈ S, ∃ t ∈ T, t⁻¹ * g ∈ H) : S ⊆ H := by
  let B : Set G := ⋃ t ∈ T \ (H : Set G), {g | t⁻¹ * g ∈ H}
  have hB : IsClosed B :=
    hT.sdiff.isClosed_biUnion (fun t _ => hH.preimage (continuous_const_mul t⁻¹))
  have hBmem (g : G) : g ∈ B ↔ ∃ t ∈ T, t ∉ H ∧ t⁻¹ * g ∈ H := by
    simp [B, and_assoc]
  have hdis : ∀ g ∈ H, g ∉ B := by
    intro g hg hgb
    obtain ⟨t, _, ht, htg⟩ := (hBmem g).mp hgb
    apply ht
    have hm := H.mul_mem hg (H.inv_mem htg)
    simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hm
  have hSB : S ⊆ (H : Set G) ∪ B := by
    intro g hg
    obtain ⟨t, ht, htg⟩ := hcover g hg
    by_cases htH : t ∈ H
    · apply Or.inl
      change g ∈ H
      simpa only [mul_inv_cancel_left] using H.mul_mem htH htg
    · exact Or.inr ((hBmem g).mpr ⟨t, ht, htH, htg⟩)
  intro x hx
  by_contra hxH
  have hxB : x ∈ B := (hSB hx).resolve_left hxH
  obtain ⟨y, _, hyH, hyB⟩ := (isPreconnected_closed_iff.mp hS)
    (H : Set G) B hH hB hSB ⟨1, h1, H.one_mem⟩ ⟨x, hx, hxB⟩
  exact hdis y hyH hyB

/-- Taking Zariski closures does not lose the finite scalar-coset cover. -/
theorem closure_subset_finite_cosets {ι : Type*} (ρ : ι → G)
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (T : Set G) (hT : T.Finite)
    (hcover : ∀ γ, ∃ t ∈ T, t⁻¹ * ρ γ ∈ H) :
    ∀ g ∈ closure (Set.range ρ), ∃ t ∈ T, t⁻¹ * g ∈ H := by
  let C : Set G := ⋃ t ∈ T, {g | t⁻¹ * g ∈ H}
  have hC : IsClosed C :=
    hT.isClosed_biUnion (fun t _ => hH.preimage (continuous_const_mul t⁻¹))
  have hr : Set.range ρ ⊆ C := by
    rintro _ ⟨γ, rfl⟩
    simpa only [C, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hcover γ
  intro g hg
  have := closure_minimal hr hC hg
  simpa only [C, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using this

/-- Apply with S = SL, H = zero-family geometric monodromy, and the
factorization of the full sheaf into a pullback and an Artin-Schreier twist.
Katz is used only for S ⊆ closure(range ρ_full). -/
theorem scalar_twist_transfers_connected_monodromy {Γ Δ : Type*}
    (ρ : Γ → G) (ρ₀ : Δ → G) (r : Γ → Δ) (α : Γ → G)
    (hfactor : ∀ γ, ρ γ = α γ * ρ₀ (r γ))
    (H₀ : Subgroup G) (hH₀ : IsClosed (H₀ : Set G))
    (hrange : ∀ δ, ρ₀ δ ∈ H₀)
    (T : Set G) (hT : T.Finite) (hα : ∀ γ, α γ ∈ T)
    {S : Set G} (hS : IsPreconnected S) (h1 : (1 : G) ∈ S)
    (hKatz : S ⊆ closure (Set.range ρ)) : S ⊆ H₀ := by
  apply connected_subset_of_finite_cosets H₀ hH₀ T hT hS h1
  have hcover : ∀ γ, ∃ t ∈ T, t⁻¹ * ρ γ ∈ H₀ := by
    intro γ
    refine ⟨α γ, hα γ, ?_⟩
    simpa only [hfactor, inv_mul_cancel_left] using hrange (r γ)
  exact fun g hg => closure_subset_finite_cosets ρ H₀ hH₀ T hT hcover g (hKatz hg)

end CayleyProof
