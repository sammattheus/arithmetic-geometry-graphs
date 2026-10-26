module

public import CayleyProof.TorsionCharacters
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Trace.Basic

/-! Multiplicative characters lift by norm; additive characters lift by
trace.  The Hasse-Davenport statement is a theorem argument here, and its
application (including both minus signs) is proved in Lean.
-/

@[expose] public section

open scoped BigOperators

namespace CayleyProof

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

noncomputable def normLift (χ : MulChar F ℂ) : MulChar E ℂ where
  toMonoidHom := χ.toMonoidHom.comp (Algebra.norm F)
  map_nonunit' x hx := by
    have hx0 : x = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using hx
    change χ (Algebra.norm F x) = 0
    rw [hx0, Algebra.norm_zero, MulChar.map_zero]

noncomputable def traceLift (ψ : AddChar F ℂ) : AddChar E ℂ :=
  ψ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom

theorem normLift_algebraMap (χ : MulChar F ℂ) (u : F) :
    normLift (E := E) χ (algebraMap F E u) = χ u ^ Module.finrank F E := by
  change χ (Algebra.norm F (algebraMap F E u)) = _
  rw [Algebra.norm_algebraMap, map_pow]

theorem normLift_injective : Function.Injective (normLift (F := F) (E := E)) := by
  intro χ η h
  apply MulChar.ext'
  intro x
  obtain ⟨y, rfl⟩ := FiniteField.norm_surjective F E x
  exact congrArg (fun θ : MulChar E ℂ => θ y) h

@[simp] theorem normLift_one : normLift (F := F) (E := E) 1 = 1 := by
  apply MulChar.ext
  intro x
  change (1 : MulChar F ℂ) (Algebra.norm F (x : E)) = (1 : MulChar E ℂ) x
  rw [MulChar.one_apply_coe, MulChar.one_apply
    (isUnit_iff_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr (Units.ne_zero x)))]

@[simp] theorem normLift_mul (χ η : MulChar F ℂ) :
    normLift (E := E) (χ * η) = normLift χ * normLift η := by
  apply MulChar.ext'
  intro x
  rfl

noncomputable def normLiftHom : MulChar F ℂ →* MulChar E ℂ where
  toFun := normLift
  map_one' := normLift_one
  map_mul' := normLift_mul

theorem normLift_pow (χ : MulChar F ℂ) (d : ℕ) :
    normLift (E := E) (χ ^ d) = normLift χ ^ d :=
  map_pow (normLiftHom (F := F) (E := E)) χ d

theorem traceLift_nontrivial {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    traceLift (E := E) ψ ≠ 1 := by
  intro h
  apply hψ
  apply AddChar.compAddMonoidHom_injective_left (Algebra.trace F E).toAddMonoidHom
    (Algebra.trace_surjective F E)
  have h1 : (1 : AddChar F ℂ).compAddMonoidHom (Algebra.trace F E).toAddMonoidHom = 1 := by
    ext x
    rfl
  change ψ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom =
    (1 : AddChar F ℂ).compAddMonoidHom (Algebra.trace F E).toAddMonoidHom
  rw [h1]
  exact h

theorem degree_dvd_extension_card_sub_one {d : ℕ} (hd : d ∣ Fintype.card F - 1) :
    d ∣ Fintype.card E - 1 := by
  rw [Module.card_eq_pow_finrank (K := F)]
  exact hd.trans (Nat.sub_one_dvd_pow_sub_one _ _)

noncomputable def normLiftTorsion {d : ℕ} (χ : nontrivialTorsionCharacters F d) :
    nontrivialTorsionCharacters E d := by
  refine ⟨normLift χ.val, (mem_nontrivialTorsionCharacters d _).mpr ⟨?_, ?_⟩⟩
  · rw [← normLift_pow, ((mem_nontrivialTorsionCharacters d _).mp χ.property).1, normLift_one]
  · intro h
    apply ((mem_nontrivialTorsionCharacters d _).mp χ.property).2
    apply normLift_injective (E := E)
    simpa using h

theorem normLiftTorsion_bijective {d : ℕ} (hd : d ∣ Fintype.card F - 1) :
    Function.Bijective (normLiftTorsion (F := F) (E := E) (d := d)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro χ η h
    apply Subtype.ext
    exact normLift_injective (E := E) (congrArg Subtype.val h)
  · rw [Fintype.card_coe, Fintype.card_coe, card_nontrivialTorsionCharacters hd,
      card_nontrivialTorsionCharacters (degree_dvd_extension_card_sub_one (E := E) hd)]

/-- The exact approved Hasse-Davenport input for a finite extension. -/
def HasseDavenportIdentity (ψ : AddChar F ℂ) : Prop :=
  ∀ χ : MulChar F ℂ, χ ≠ 1 →
    -gaussSum (normLift (E := E) χ) (traceLift (E := E) ψ) =
      (-gaussSum χ ψ) ^ Module.finrank F E

/-- Normalizing by c^r and lifting u through the algebra map gives the
r-th power of the proposed base-field eigenvalue. -/
theorem lifted_normalized_gauss_factor (ψ : AddChar F ℂ)
    (hHD : HasseDavenportIdentity (E := E) ψ) (c : ℂ) (u : F)
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    -(c ^ Module.finrank F E) *
      (normLift (E := E) χ (algebraMap F E u))⁻¹ *
        gaussSum (normLift (E := E) χ) (traceLift (E := E) ψ) =
      monomialGaussFactor ψ c u χ ^ Module.finrank F E := by
  rw [normLift_algebraMap, ← inv_pow]
  calc
    -(c ^ Module.finrank F E) * ((χ u)⁻¹ ^ Module.finrank F E) *
        gaussSum (normLift (E := E) χ) (traceLift (E := E) ψ)
      = c ^ Module.finrank F E * ((χ u)⁻¹ ^ Module.finrank F E) *
        (-gaussSum (normLift (E := E) χ) (traceLift (E := E) ψ)) := by ring
    _ = _ := by
      rw [hHD χ hχ]
      simp only [monomialGaussFactor, mul_pow]
      ring

end CayleyProof
