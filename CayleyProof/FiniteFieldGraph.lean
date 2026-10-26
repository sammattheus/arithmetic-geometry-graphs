module

public import CayleyProof.CharacterEigenvectors
public import CayleyProof.Diameter

/-! Verified finite-field graph properties. This is not the manuscript's
asymptotic inertia theorem; that theorem still requires the appendix,
the convergence argument, and the uniform polynomial argument.
-/

@[expose] public section

open scoped Matrix Classical

namespace CayleyProof

variable (F : Type*) [Field F] [Fintype F]

theorem exists_primitive_character : ∃ ψ : AddChar F ℂ, ψ.IsPrimitive := by
  obtain ⟨ψ, hψ⟩ := AddChar.exists_apply_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)
  refine ⟨ψ, AddChar.IsPrimitive.of_ne_one ?_⟩
  intro h
  exact hψ (by simp [h])

/-- Unconditional order, degree, vertex transitivity, and a complete
coefficient-indexed eigenbasis for the specified moment-curve Cayley graph. -/
theorem finite_field_graph_properties (s : ℕ) (hs : 2 ≤ s) (hchar : (2 : F) ≠ 0) :
    Fintype.card (Fin s → F) = Fintype.card F ^ s ∧
    (∀ v, (curveGraph F s).degree v = 2 * (Fintype.card F - 1)) ∧
    (∀ v w, ∃ e : curveGraph F s ≃g curveGraph F s, e v = w) ∧
    ∃ ψ : AddChar F ℂ, ψ.IsPrimitive ∧
      ∃ b : Module.Basis (Fin s → F) ℂ ((Fin s → F) → ℂ),
        ∀ a, (curveGraph F s).adjMatrix ℂ *ᵥ b a =
          (realEigenvalue ψ a : ℂ) • b a := by
  obtain ⟨ψ, hψ⟩ := exists_primitive_character F
  exact ⟨card_vertices, degree_curveGraph hs hchar, vertex_transitive,
    ψ, hψ, coefficient_eigenbasis hs hchar hψ⟩

end CayleyProof
