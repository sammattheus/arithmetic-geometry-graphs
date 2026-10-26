module

public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Tactic

/-! The topological deduction used after finding a determinant-one rational
Frobenius. The arithmetic fundamental-group exact sequence supplies the
surjective map in an application. This group-theoretic step is proved here,
rather than included in an algebraic-geometry black box.
-/

@[expose] public section

open scoped Topology

namespace CayleyProof

variable {G Q : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [Group Q] [TopologicalSpace Q] [T2Space Q]

/-- In a compact group mapping onto a procyclic quotient, a closed subgroup
containing the kernel and a lift of a dense cyclic generator is the whole group. -/
theorem subgroup_eq_top_of_kernel_and_generator
    (π : G →* Q) (hπ : Continuous π) (_hsurj : Function.Surjective π)
    (φ : G) (hφ : DenseRange (fun n : ℤ => π φ ^ n))
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (hker : π.ker ≤ H) (hmem : φ ∈ H) : H = ⊤ := by
  have hclosed : IsClosed ((H.map π : Subgroup Q) : Set Q) := by
    change IsClosed (π '' (H : Set G))
    exact (hH.isCompact.image hπ).isClosed
  have hmap : H.map π = ⊤ := by
    apply top_unique
    intro x _
    have hrange : Set.range (fun n : ℤ => π φ ^ n) ⊆ (H.map π : Set Q) := by
      rintro _ ⟨n, rfl⟩
      exact Subgroup.zpow_mem _ (Subgroup.mem_map.mpr ⟨φ, hmem, rfl⟩) n
    exact (closure_minimal hrange hclosed) (hφ x)
  apply top_unique
  intro x _
  have : π x ∈ H.map π := by rw [hmap]; trivial
  obtain ⟨y, hy, heq⟩ := Subgroup.mem_map.mp this
  have hk : y⁻¹ * x ∈ π.ker := by simp [MonoidHom.mem_ker, heq]
  have := H.mul_mem hy (hker hk)
  simpa only [mul_inv_cancel_left] using this

/-- A representation lands in a closed target subgroup once its kernel image
and one Frobenius lift do. This is the arithmetic = geometric step. -/
theorem representation_range_le_of_kernel_and_generator
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (π : G →* Q) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (φ : G) (hφ : DenseRange (fun n : ℤ => π φ ^ n))
    (ρ : G →* L) (hρ : Continuous ρ)
    (H : Subgroup L) (hH : IsClosed (H : Set L))
    (hker : ∀ x ∈ π.ker, ρ x ∈ H) (hmem : ρ φ ∈ H) : ρ.range ≤ H := by
  have htop : H.comap ρ = ⊤ :=
    subgroup_eq_top_of_kernel_and_generator π hπ hsurj φ hφ
      (H.comap ρ) (hH.preimage hρ) hker hmem
  rintro _ ⟨x, rfl⟩
  change x ∈ H.comap ρ
  rw [htop]
  trivial

end CayleyProof
