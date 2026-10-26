module

public import CayleyProof.EmpiricalMeasure
public import CayleyProof.CharacterEigenvectors

/-! The exact finite probability measures in Theorem 22, including their
normalization and independence of the chosen nontrivial additive character.
Here the polynomial degree is s+1; its constant coefficient is zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators Topology Classical

namespace CayleyProof

variable {F : Type*} [Field F] [Fintype F]

noncomputable def normalizedCharacterSum (ψ : AddChar F ℂ) {d : ℕ}
    (b : Fin d → F) : ℝ :=
  (∑ t : F, ψ (∑ i, b i * t ^ (i.val + 1))).re / Real.sqrt (Fintype.card F : ℝ)

noncomputable def katzSampleLaw (ψ : AddChar F ℂ) (s : ℕ) : ProbabilityMeasure ℝ :=
  empiricalLaw (fun b : {b : Fin (s + 1) → F // b (Fin.last s) ≠ 0} =>
    normalizedCharacterSum ψ b.val)

/-- The normalization is the reciprocal of (q-1)q^s, for exact degree s+1. -/
theorem integral_katzSampleLaw (ψ : AddChar F ℂ) (s : ℕ) (f : ℝ → ℝ)
    (hf : StronglyMeasurable f) :
    (∫ x, f x ∂(katzSampleLaw ψ s : Measure ℝ)) =
      (((Fintype.card F - 1) * Fintype.card F ^ s : ℕ) : ℝ)⁻¹ *
        ∑ b : {b : Fin (s + 1) → F // b (Fin.last s) ≠ 0},
          f (normalizedCharacterSum ψ b.val) := by
  rw [katzSampleLaw, integral_empiricalLaw _ _ hf, card_exactDegreeCoefficients]

def scaleExactDegreeCoefficients (s : ℕ) (u : F) (hu : u ≠ 0) :
    {b : Fin (s + 1) → F // b (Fin.last s) ≠ 0} ≃
      {b : Fin (s + 1) → F // b (Fin.last s) ≠ 0} where
  toFun b := ⟨fun i => u * b.val i, mul_ne_zero hu b.property⟩
  invFun b := ⟨fun i => u⁻¹ * b.val i, mul_ne_zero (inv_ne_zero hu) b.property⟩
  left_inv b := by apply Subtype.ext; ext i; simp [hu]
  right_inv b := by apply Subtype.ext; ext i; simp [hu]

theorem normalizedCharacterSum_mulShift (ψ : AddChar F ℂ) (u : F)
    {d : ℕ} (b : Fin d → F) :
    normalizedCharacterSum (ψ.mulShift u) b =
      normalizedCharacterSum ψ (fun i => u * b i) := by
  simp only [normalizedCharacterSum, AddChar.mulShift_apply, Finset.mul_sum, mul_assoc]

theorem katzSampleLaw_mulShift (ψ : AddChar F ℂ) (s : ℕ) (u : F) (hu : u ≠ 0) :
    katzSampleLaw (ψ.mulShift u) s = katzSampleLaw ψ s := by
  unfold katzSampleLaw
  simp only [normalizedCharacterSum_mulShift]
  exact empiricalLaw_reindex (scaleExactDegreeCoefficients s u hu)
    (fun b => normalizedCharacterSum ψ b.val)

theorem exists_nonzero_mulShift {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {χ : AddChar F ℂ} (hχ : χ ≠ 1) : ∃ u : F, u ≠ 0 ∧ ψ.mulShift u = χ := by
  have hbij : Function.Bijective ψ.mulShift := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨AddChar.to_mulShift_inj_of_isPrimitive hψ, (AddChar.card_eq (α := F)).symm⟩
  obtain ⟨u, hu⟩ := hbij.surjective χ
  refine ⟨u, ?_, hu⟩
  intro hz
  subst u
  exact hχ (by simpa using hu.symm)

/-- Exact equality at each finite field, so arbitrary choices of nontrivial
additive character across extension degrees cause no convergence problem. -/
theorem katzSampleLaw_character_independent {ψ χ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (hχ : χ ≠ 1) (s : ℕ) :
    katzSampleLaw χ s = katzSampleLaw ψ s := by
  obtain ⟨u, hu, rfl⟩ := exists_nonzero_mulShift hψ hχ
  exact katzSampleLaw_mulShift ψ s u hu

end CayleyProof
