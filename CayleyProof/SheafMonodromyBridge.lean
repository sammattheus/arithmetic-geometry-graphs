module

public import CayleyProof.SheafFactorization
public import CayleyProof.ScalarTwistMonodromy

/-! Moving from the categorical constant-coordinate isomorphism to the
representation input.  An isomorphism of sheaves gives conjugate matrices,
not equal matrices.  The conjugation is handled explicitly below.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CayleyProof

theorem determinant_kernel_containment_conjugate
    {G A Γ : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    [CommGroup A] (det : G →* A) (ρ : Γ → G) (C : G)
    (hKatz : (det.ker : Set G) ⊆ closure (Set.range ρ)) :
    (det.ker : Set G) ⊆ closure (Set.range (fun γ => C⁻¹ * ρ γ * C)) := by
  intro x hx
  have hy : C * x * C⁻¹ ∈ det.ker := by
    change det (C * x * C⁻¹) = 1
    have hx' : det x = 1 := hx
    simp [map_mul, map_inv, hx']
  have hcont : Continuous (fun y : G => C⁻¹ * y * C) :=
    (continuous_const_mul C⁻¹).mul_const C
  have hmap : Set.MapsTo (fun y : G => C⁻¹ * y * C) (Set.range ρ)
      (Set.range (fun γ => C⁻¹ * ρ γ * C)) := by
    rintro _ ⟨γ, rfl⟩
    exact ⟨γ, rfl⟩
  have hm := map_mem_closure hcont (hKatz hy) hmap
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hm

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {CX : Type u₁} [Category.{v₁} CX]
  {CD : Type u₂} [Category.{v₂} CD] [MonoidalCategory CD]
  {CXT : Type u₃} [Category.{v₃} CXT]
  {CDT : Type u₄} [Category.{v₄} CDT] [MonoidalCategory CDT]

/-- Base change, projection, AS additivity, and the fibre-functor rules
produce a representative of the full monodromy representation to which the
finite-scalar-twist lemma applies.  Katz is transported through the change
of basis, using the normality of the determinant kernel. -/
theorem sheaf_factorization_supplies_monodromy_input
    {R : Type*} [Add R] (AS : R → CDT)
    (additivity : ∀ f g, AS (f + g) ≅ AS f ⊗ AS g)
    (r : CX ⥤ CD) (rT : CXT ⥤ CDT)
    (pushX : CXT ⥤ CX) (pushD : CDT ⥤ CD) (πpull : CD ⥤ CDT)
    (baseChange : ∀ L, pushD.obj (rT.obj L) ≅ r.obj (pushX.obj L))
    (projection : ∀ L T, pushD.obj (L ⊗ πpull.obj T) ≅ pushD.obj L ⊗ T)
    (f c : R) (L : CXT) (T : CD)
    (hf : AS f ≅ rT.obj L) (hc : AS c ≅ πpull.obj T)
    {G A Γ Δ : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    [CommGroup A] (det : G →* A) (rep : CD → Γ → G)
    (isoConjugacy : ∀ U V, (U ≅ V) → ∃ C : G, ∀ γ, rep U γ = C * rep V γ * C⁻¹)
    (ρ₀ : Δ → G) (rπ : Γ → Δ) (α : Γ → G)
    (tensorPullback : ∀ γ, rep (r.obj (pushX.obj L) ⊗ T) γ = α γ * ρ₀ (rπ γ))
    (hKatz : (det.ker : Set G) ⊆ closure (Set.range (rep (pushD.obj (AS (f + c)))))) :
    ∃ ρfull : Γ → G,
      (∀ γ, ρfull γ = α γ * ρ₀ (rπ γ)) ∧
      (det.ker : Set G) ⊆ closure (Set.range ρfull) := by
  let i := artinSchreierConstantFactorization AS additivity r rT pushX pushD πpull
    baseChange projection f c L T hf hc
  obtain ⟨C, hC⟩ := isoConjugacy _ _ i
  refine ⟨fun γ => C⁻¹ * rep (pushD.obj (AS (f + c))) γ * C, ?_,
    determinant_kernel_containment_conjugate det _ C hKatz⟩
  intro γ
  change C⁻¹ * rep (pushD.obj (AS (f + c))) γ * C = α γ * ρ₀ (rπ γ)
  rw [hC, tensorPullback]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

end CayleyProof
