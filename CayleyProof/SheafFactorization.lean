module

public import Mathlib.CategoryTheory.Monoidal.Category

/-! The categorical derivation of the constant-coordinate factorization.

This is a generic theorem about functors and isomorphisms. Its input
isomorphisms are the shapes of compact-support base change (SGA 4 XVII,
5.2.6), the projection formula (XVII, 5.2.9), and Artin--Schreier additivity.
They are not asserted as new axioms, nor are the abstract categories claimed
to instantiate the absent l-adic derived-category infrastructure in mathlib.
That instantiation and passage to monodromy representations remain open.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CayleyProof

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {CX : Type u₁} [Category.{v₁} CX]
  {CD : Type u₂} [Category.{v₂} CD] [MonoidalCategory CD]
  {CXT : Type u₃} [Category.{v₃} CXT]
  {CDT : Type u₄} [Category.{v₄} CDT] [MonoidalCategory CDT]

/-- Pullback in the coefficient direction commutes with integration in t;
then projection removes the factor depending only on the constant term. -/
def constantCoordinateFactorization
    (r : CX ⥤ CD) (rT : CXT ⥤ CDT)
    (pushX : CXT ⥤ CX) (pushD : CDT ⥤ CD) (πpull : CD ⥤ CDT)
    (baseChange : ∀ L, pushD.obj (rT.obj L) ≅ r.obj (pushX.obj L))
    (projection : ∀ L T, pushD.obj (L ⊗ πpull.obj T) ≅ pushD.obj L ⊗ T)
    {L : CXT} {T : CD} {full : CDT}
    (integrand : full ≅ rT.obj L ⊗ πpull.obj T) :
    pushD.obj full ≅ r.obj (pushX.obj L) ⊗ T :=
  pushD.mapIso integrand ≪≫ projection (rT.obj L) T ≪≫
    tensorIso (baseChange L) (Iso.refl T)

/-- Additivity is applied before integration; this avoids trying to deduce
a sheaf isomorphism merely from equality of traces at rational points. -/
def artinSchreierConstantFactorization
    {R : Type*} [Add R] (AS : R → CDT)
    (additivity : ∀ f g, AS (f + g) ≅ AS f ⊗ AS g)
    (r : CX ⥤ CD) (rT : CXT ⥤ CDT)
    (pushX : CXT ⥤ CX) (pushD : CDT ⥤ CD) (πpull : CD ⥤ CDT)
    (baseChange : ∀ L, pushD.obj (rT.obj L) ≅ r.obj (pushX.obj L))
    (projection : ∀ L T, pushD.obj (L ⊗ πpull.obj T) ≅ pushD.obj L ⊗ T)
    (f c : R) (L : CXT) (T : CD)
    (hf : AS f ≅ rT.obj L) (hc : AS c ≅ πpull.obj T) :
    pushD.obj (AS (f + c)) ≅ r.obj (pushX.obj L) ⊗ T :=
  constantCoordinateFactorization r rT pushX pushD πpull baseChange projection
    (additivity f c ≪≫ tensorIso hf hc)

end CayleyProof
