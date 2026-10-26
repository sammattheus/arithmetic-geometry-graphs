# Scope and trust boundary

The user authorized original full-family Katz, the previously named external
results, and standard algebraic geometry. This project contains Lean derivations
of both requested conclusions relative to `EXTERNAL_INPUTS.md`.

## Proved deductions and supplied realization

`theorem22_from_standard_data` has explicit geometric-data and Hasse-Davenport
hypotheses. Its axiom dependencies are only Lean's standard logical axioms.
The assembled `theorem22` obtains those hypotheses from the declared inputs.
Its signature contains finite-field and degree conditions, not a hypothesis
asserting the manuscript's equidistribution conclusion.

The standard data package is **assumed to exist**. Its categories, functors,
groups and representations are abstract mathlib objects. The coefficient
scheme and its l-adic compactly supported cohomology are not constructed in
mathlib's scheme framework. Calling this an unconditional mathlib proof, or
a proof using only a bare Katz axiom, would misdescribe it. The package bundles
several permitted standard results and their compatible realization; its full
fields appear in `CayleyProof/CohomologicalInputs.lean`.

The following are not fields in that package:

- Constant-coordinate factorization.
- SL containment for zero-constant geometric monodromy.
- A determinant-one monomial Frobenius.
- Arithmetic image containment in geometric monodromy.
- SU containment of the compact realization.
- Weak convergence or support conclusions for the scalar laws.
- Either uniform polynomial condition in Lemma 15.

Each is derived in Lean. The Katz field concerns the **full** polynomial
family. The Deligne field is conditional on arithmetic containment; the proof
supplies that condition.

## Reuse of mathlib

The project uses mathlib's finite fields, norm and trace, characters, Gauss
sums, Newton identities, polynomials, category theory, topological groups,
special unitary matrices, probability measures, weak convergence and Cayley
graphs. The application-specific lisse/Rf_! realization is an explicit
external record. General schemes and sheaves in mathlib do not by themselves
supply that package.

## Scope

Theorem 18's final declaration proves exactly the requested uniform conditions
and finite-set nonconcentration for the spectral list identified by the graph
eigenbasis theorem. It does not state the entire graph theorem. The conditional
diameter argument is retained; deriving its representation hypothesis from
Cohen and formalizing the optimized inertia invariant are separate tasks.

## Verification

`Audit.lean` rejects every dependency except `propext`, `Classical.choice`,
`Quot.sound`, and the three exact external names. In particular, `sorryAx`
is rejected. It prints dependencies of both final results and the main
intermediate deductions.
