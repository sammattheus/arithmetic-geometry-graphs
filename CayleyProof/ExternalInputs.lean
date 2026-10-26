module

public import CayleyProof.CohomologicalInputs
public import CayleyProof.CurveSpectralMeasure

/-! TRUSTED EXTERNAL INPUTS.

These are the three nonlogical axioms in the project.  The second is an
explicit realization interface bundling the permitted standard l-adic
formalism, original FULL-FAMILY Katz theorem, and Deligne theorem.  It is
not a mathlib construction of the scheme and its l-adic cohomology.
EXTERNAL_INPUTS.md records the exact trust boundary and sources by field.

The scalar-twist factorization and every subsequent appendix deduction are
proved in the project.  In particular the data structure has no field for
zero-family SL containment, determinant one, arithmetic containment, or
convergence of the scalar empirical laws.
-/

@[expose] public section

namespace CayleyProof

noncomputable def positiveNormalization (F : Type) [Field F] [Fintype F] : ℂ :=
  ((Real.sqrt (Fintype.card F : ℝ) : ℂ))⁻¹

namespace External

/-- Hasse-Davenport, with norm lift for multiplicative characters and trace
lift for additive characters.  Conrad, Theorem 3.1; both lifts are defined
using mathlib's actual algebraic norm and trace in CharacterLifts.lean. -/
axiom hasseDavenport
    (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) : HasseDavenportIdentity (E := E) ψ

/-- Realization of the explicitly displayed standard cohomological data
for X = A^(d-1) x G_m, d=m+3, and D = X x A^1, with universal polynomial
f(t)+c.  This packages standard geometric realization and the two approved
original deep theorems; consult the field-by-field source map before treating
this as a trust boundary.  No manuscript-specific monodromy or determinant
conclusion is included.

The normalization is FIXED to the positive inverse square root.  Arbitrary
square-root choices would change arithmetic Frobenius traces. -/
axiom katzDeligneCohomologicalRealization
    (m p : ℕ) [Fact p.Prime] (hp : 5 < p) (hpd : ¬ p ∣ m + 3)
    (F : Type) [Field F] [Fintype F] [CharP F p]
    (E : ℕ → Type) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    (hrank : ∀ n, Module.finrank F (E n) = n + 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    Nonempty (CoefficientCohomologyData m F E ψ (positiveNormalization F))

/-- The approved Weil estimate, in its weaker uniform degree-at-most-s form.
The restriction s<p makes every positive degree prime to p.  The degree-one
case has sum zero; higher degrees follow from Katz 3.5.10 and 3.5.12. -/
axiom weilCharacterSumBound
    (F : Type) [Field F] [Fintype F] (p s : ℕ) [Fact p.Prime] [CharP F p]
    (hsp : s < p) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) : HasWeilBound ψ s

end External

end CayleyProof
