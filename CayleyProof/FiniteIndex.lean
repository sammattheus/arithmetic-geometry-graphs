module

public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.GroupTheory.Coset.Basic

/-! The topological step behind the finite scalar-twist argument.

This proves the general closed finite-index subgroup lemma. Applying it to
the particular geometric monodromy groups still requires constructing those
groups and proving the finite-index hypothesis; no such application is assumed.
-/

@[expose] public section

namespace CayleyProof

/-- Finitely many translates covering a group give finite index. In the
constant-term twist argument these translates are indexed by p-th roots of unity. -/
theorem finiteIndex_of_finite_left_cover {G : Type*} [Group G]
    (H : Subgroup G) (T : Set G) (hT : T.Finite)
    (hcover : ∀ g : G, ∃ t ∈ T, t⁻¹ * g ∈ H) : H.FiniteIndex := by
  let : Finite T := hT.to_subtype
  let f : T → G ⧸ H := fun t => QuotientGroup.mk t.val
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨t, ht, htg⟩ := hcover g
      exact ⟨⟨t, ht⟩, QuotientGroup.eq.mpr htg⟩
  let : Finite (G ⧸ H) := Finite.of_surjective f hsurj
  exact H.finiteIndex_of_finite_quotient

-- Separate continuity is sufficient. This matters for Zariski topologies:
-- the product topology on G(k) × G(k) need not be the variety's product topology.
variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- A closed finite-index subgroup contains the identity component. -/
theorem connectedComponent_one_subset (H : Subgroup G) [H.FiniteIndex]
    (hH : IsClosed (H : Set G)) : connectedComponent (1 : G) ⊆ H := by
  exact (show IsClopen (H : Set G) from
    ⟨hH, H.isOpen_of_isClosed_of_finiteIndex hH⟩).connectedComponent_subset H.one_mem

/-- Every connected subset through the identity lies in that subgroup. -/
theorem connected_subset_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : IsClosed (H : Set G)) {S : Set G} (hS : IsPreconnected S)
    (h1 : (1 : G) ∈ S) : S ⊆ H := by
  exact (hS.subset_connectedComponent h1).trans (connectedComponent_one_subset H hH)

/-- A connected subset through the identity cannot move between the finitely
many closed cosets arising from a finite scalar twist. -/
theorem connected_subset_of_finite_left_cover (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (T : Set G) (hT : T.Finite)
    (hcover : ∀ g : G, ∃ t ∈ T, t⁻¹ * g ∈ H)
    {S : Set G} (hS : IsPreconnected S) (h1 : (1 : G) ∈ S) : S ⊆ H := by
  let := finiteIndex_of_finite_left_cover H T hT hcover
  exact connected_subset_finiteIndex H hH hS h1

end CayleyProof
