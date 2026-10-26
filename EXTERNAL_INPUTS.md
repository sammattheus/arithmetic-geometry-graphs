# External inputs: exact source map

There are three project axioms, in `CayleyProof/ExternalInputs.lean`.
The second is a **bundled realization assertion**, not a single quoted
theorem or a construction in mathlib's scheme category. Its fields are
in `CayleyProof/CohomologicalInputs.lean`. Full references are in
`REFERENCES.md`.

## 1. Hasse-Davenport

`External.hasseDavenport` supplies -G_lift=(-G_base)^r for actual finite
fields, algebraic norm/trace, and mathlib characters. Source: Conrad,
*L-functions for Gauss and Jacobi sums*, Theorem 3.1.

Character lifting, its behavior on base-field elements, bijection on
d-torsion characters, and the power-sum application are proved here.

## 2. Cohomological realization

`External.katzDeligneCohomologicalRealization` asserts existence of
`CoefficientCohomologyData` for d=m+3, characteristic p>5, p not dividing d,
and a primitive additive character. The intended coefficient schemes are
X=A^(d-1) x G_m and D=X x A^1, adding the constant coordinate.
Normalization is the **positive** inverse square root of the base cardinality.

### FullFamilySheafData

| Fields | Interpretation and source |
| --- | --- |
| `CX, CD, CXT, CDT`, category/monoidal structures, `R, AS` | Coefficient categories and Artin-Schreier construction: Katz-Laumon Section 2.0. |
| `r, rT, pushX, pushD, πpull` | Pullback and relevant compact-support cohomology functors: Katz Section 3.5.5 and standard coefficient formalism. |
| `additivity` | Artin-Schreier tensor identity: Katz-Laumon Section 2.0; Katz Lemma 3.9.5. |
| `baseChange` | SGA 4 III, Expose XVII, Theorem 5.2.6, standard l-adic version. |
| `projection` | Same expose, Proposition 5.2.9, standard l-adic version. |
| `f, c, L, T, hf, hc` | Universal polynomial and constant coordinate with their pullback identifications. |
| `rep, isoConjugacy, tensorPullback` | Stalk representation compatibility: Milne, *Etale Cohomology*, Section 19. Only the relevant rank is represented; `rep` is not a fibre functor on all ranks. |
| `katzFullFamily` | Original Katz Theorem 3.9.2 for the **full** polynomial family. |

The standard input isomorphisms are supplied. Their composite constant-coordinate
factorization and the change of basis are proved.

### CoefficientCohomologyData

| Fields | Interpretation and source |
| --- | --- |
| `P, Q`, group/topology instances, `π, continuousπ, surjectiveπ` | Arithmetic fundamental group and finite-field Galois quotient: Stacks Tag 0BTX; profiniteness. |
| `G, ellTopology, ellGroup, ρ, continuousρ, det` | Normalized lisse representation and determinant: Milne Section 19; Katz Section 3.5. |
| `zariski, zariskiMul, H₀, ellClosed, zariskiClosed, closure_eq` | Geometric monodromy as Zariski closure; algebraic subgroups are also l-adically closed. |
| `connectedSL` | Connectedness of SL: Milne, *Algebraic Groups* v2.00, Example 5.56. |
| `Γ, rπ, α, scalarSet, finiteScalars, scalar_mem, fullSheaves` | Geometric group of D, map to X, finite Artin-Schreier rank-one monodromy, and full-family data. |
| `frob, frob_generator` | Monomial rational points u t^d; their Frobenius maps to a generator of the procyclic quotient. |
| `eigenvalues, determinant, powerTrace` | Rank d-1 eigenvalues, determinant product, extension-degree trace formula: Katz Theorem 3.5.10 and Corollaries 3.5.11-12; standard linear algebra and Frobenius base change. |
| `K`, its instances, `M, continuousM, unitary` | Unitarized maximal compact realization: Katz-Sarnak Section 9.2.3; Fresnel Theorem 1.1(ii). |
| `complexComparison, complexDet` | Complex coefficient comparison compatible with determinant and the chosen conjugate realization. |
| `compactIntersection` | H(C) intersect U is contained in the maximal compact group: the intersection is compact and contains that group, so maximality applies. |
| `haar, haarOpenPositive` | Haar probability positive on nonempty open sets. |
| `θ, trace` | Compact Frobenius representatives and trace interpretation: Katz-Sarnak Section 9.2.4; cohomological trace formula. |
| `deligne` | Continuous central-function equidistribution **assuming** arithmetic containment: Katz-Sarnak Theorem 9.2.6(1). |

These rows give the mathematical interpretation of the realization assertion,
not Lean proofs that these objects exist. Smoothness and geometric
connectedness of X, lissity, purity, and coefficient comparison are checked
externally in this interface. The cited SGA 4 statements originally use
torsion coefficients; their standard constructible l-adic extensions are
part of the supplied formalism.

### What the interface does not assume

Factorization, zero-family SL containment, a determinant-one point, arithmetic
containment, SU containment, and scalar-law convergence/support are deductions.
The conditional Deligne field is used only after proving its hypothesis.
No field asserts the manuscript's Theorem 22.

Katz Theorem 6.8.34 is **not** a black box for the determinant calculation.
Fourier expansion, lifting, Newton identities, and both parity arguments
are implemented here.

## 3. Weil bound

`External.weilCharacterSumBound` supplies the uniform estimate
`HasWeilBound` for degree at most s<p. This is the permitted Weil input:
the cited rank/purity and trace statements give (e-1)sqrt(q) for degree
e>1; the nontrivial linear sum is zero. The weaker uniform bound suffices.

The final Theorem 18 result applies this and Theorem 22, deriving both
uniform polynomial conditions without further axioms.
