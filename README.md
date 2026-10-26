# Moment-curve Cayley graph: Lean formalization 0.3.0

**Theorem 22 and the requested verification of Lemma 15 in Theorem 18 are
proved relative to explicitly declared external mathematical inputs.** There
are no `sorry` or `admit` proofs. There are three theorem axioms, one bundling
the standard cohomological realization with original full-family Katz and
Deligne equidistribution. This is a formal reduction to that displayed
interface, not a construction of l-adic cohomology inside mathlib. Read
`EXTERNAL_INPUTS.md` for the exact boundary.

## Entry points

| Result | File and declaration |
| --- | --- |
| Theorem 22 | `CayleyProof/Theorem22Final.lean`: `CayleyProof.theorem22` |
| Both uniform assumptions of Lemma 15 for the normalized spectral list | `CayleyProof/Theorem18Final.lean`: `CayleyProof.theorem18_lemma15_assumptions` |
| Reduction from explicit geometric data, without project-axiom dependencies | `CayleyProof/CohomologicalInputs.lean`: `CayleyProof.theorem22_from_standard_data` |
| Identification of the list as graph eigenvalues, with multiplicities | `CayleyProof/FiniteFieldGraph.lean`: `CayleyProof.normalized_coefficient_eigenbasis` |

For Theorem 22, `E n` has extension degree n+1 over a base field of size
Q=p^(2a), covering all positive extension degrees. Arbitrary nontrivial
additive characters may be chosen independently for each field. The conclusion
gives weak convergence to a probability measure with infinite support contained
in [1-d,d-1]. The sample probability uses the exact count (q-1)q^(d-1).

## Deductions checked in Lean

1. Artin-Schreier additivity, base change and the projection formula imply
   constant-coordinate factorization. Passing to representations includes
   conjugation for a change of basis.
2. Finite scalar twisting and connectedness of SL transfer full-family
   monodromy containment to the zero-constant family.
3. The monomial Fourier expansion uses actual mathlib characters. Multiplicative
   characters lift by norm and additive characters by trace. Hasse-Davenport
   then supplies all power traces.
4. Newton identities recover the determinant from those traces. Gauss pairing
   handles odd degree; the even case retains the constant sign and chooses
   a suitable quadratic-character value.
5. A determinant-one Frobenius and the geometric kernel give arithmetic
   containment.
6. The compact realization and SL containment give SU containment. The
   negative real trace of Haar probability has bounded, infinite support;
   class-function convergence gives weak scalar convergence.
7. Character independence covers every nontrivial additive-character sequence.

The Zariski topology for connectedness is distinct from the l-adic topology
for arithmetic continuity. The Zariski argument requires only separate
continuity of multiplication.

## Theorem 18: spectral and analytic transfer

For k>=5, put s=floor(k/2)+1. The final theorem invokes Theorem 22 and the Weil
input itself. It does not assume scalar equidistribution, spectral convergence,
field-size growth, or a polynomial tail estimate.

The transfer includes lower-degree coefficients, the varying affine spectral
normalization, and the principal atom of mass q^(-s) at sqrt(2(q-1)).
Its weighted contribution tends to zero since k<2s. Compactness of the normalized
degree-at-most-k polynomial family gives both uniform integral convergence and
uniformly vanishing tails outside I=[-2(s+1),2(s+1)]. The limit does not
concentrate on any finite set. The conditions use epsilon/eventually statements,
equivalent to uniform convergence. All real polynomials of degree at most k
are covered.

The probability on the subtype I uses a continuous clipping map, proved to
equal x |-> sqrt(2)x on the limiting support.

The graph is mathlib's `SimpleGraph.addCayley` on `Fin s -> F`, with generators
{+/- (t,t^2,...,t^s) : t != 0}. Existing results prove q^s vertices, degree
2(q-1), vertex transitivity, and a complete character eigenbasis in odd
characteristic. The analytic list is identified with the normalized adjacency
spectrum, including multiplicities.

The full diameter deduction from Cohen's theorem and the final optimized
inertia inequality are outside the two requested targets.

## Reproduce the checks

- Lean: `v4.36.0-rc1`.
- mathlib: `3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6`.
- Transitive revisions: `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

All proof modules are imported through `CayleyProof.lean`.
`verification/build.txt` and `verification/axioms.txt` record verification.
The audit checks every public project declaration's transitive dependencies,
allowing only Lean's standard logical axioms and these exact external names:

- `CayleyProof.External.hasseDavenport`
- `CayleyProof.External.katzDeligneCohomologicalRealization`
- `CayleyProof.External.weilCharacterSumBound`

Theorem 22 uses the first two; the final Theorem 18 result uses all three.
The data-consuming reduction uses no project axioms. The audit verifies
dependencies, not the truth or adequacy of the external input statements.

The archive excludes downloaded dependencies, toolchains and build products.
This environment needed an executable-discovery shim because process IDs
disagree with the mounted /proc. Its source is in `verification/`; ordinary
installations do not need it. The stock Lean kernel was not modified.
