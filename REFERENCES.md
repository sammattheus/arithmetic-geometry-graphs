# Verified mathematical references

These are references for the declared external inputs. The field-by-field
interpretation of the cohomological realization axiom is in EXTERNAL_INPUTS.md.
The actual l-adic realization is supplied by that axiom, not constructed in Lean.

## Katz full-family theorem and exponential-sum bound

Nicholas M. Katz, *Moments, Monodromy, and Perversity: A Diophantine Perspective*,
Annals of Mathematics Studies **159**, Princeton University Press, 2005.
DOI: https://doi.org/10.1515/9781400826957

Author's text:
https://web.math.princeton.edu/~nmk/mmp/wholebookfeb2205.pdf

- Section 3.5.5: construction from compact-supported direct image.
- Theorem 3.5.10 and Corollaries 3.5.11-3.5.12: cohomological concentration,
  rank, purity, and the normalized Frobenius trace formula.
- Theorem 3.9.2, n=1, p>=7, degree d>=3 prime to p: geometric monodromy of the
  FULL polynomial family contains SL(d-1).
- Proof of Lemma 3.9.5: explicitly uses the Artin-Schreier tensor identity.

For a degree-e one-variable polynomial, e prime to p, the rank e-1 and weight-one
purity give the bound (e-1)sqrt(q). The e=1 sum is zero for a nontrivial additive
character. In the graph application p>s, all relevant degrees satisfy this
condition. This explains the explicit `HasWeilBound` input.

Theorem 3.9.2 is not itself a theorem about the zero-constant-term slice.
The restriction argument must be supplied. Neither Entin's summarized statement
nor the manuscript's Theorem 22 is used as a substitute black box.

## Compact-support base change and projection formula

Pierre Deligne, Expose XVII, "Cohomologie a supports propres," in
*Theorie des topos et cohomologie etale des schemas (SGA 4), Tome 3*,
Lecture Notes in Mathematics **305**, Springer, 1973.

- Theorem 5.2.6: Rf_! commutes with base change.
- Proposition 5.2.9: the derived projection formula.

https://www.normalesup.org/~forgogozo/SGA4/tomes/tome3.pdf
Publisher: https://doi.org/10.1007/BFb0070714

These original statements are formulated with torsion coefficients. The
application needs their standard constructible l-adic versions, obtained in
the l-adic formalism. They should not be described as literally stated in SGA 4
for algebraic-closure-valued l-adic sheaves.

## Artin-Schreier sheaf construction

Nicholas M. Katz and Gerard Laumon,
"Transformation de Fourier et majoration de sommes exponentielles,"
*Publications mathematiques de l'IHES* **62** (1985), 145-202, Section 2.0.

https://web.math.princeton.edu/~nmk/old/TFandmajSE.pdf

Section 2.0 constructs the rank-one lisse sheaf from the Artin-Schreier torsor
and an additive character. The tensor identity L_psi(f+g) = L_psi(f) tensor
L_psi(g) is also used explicitly in Katz's proof of Lemma 3.9.5 above.
Its p-th tensor power is trivial in characteristic p.

## Lisse sheaves and fundamental-group representations

James S. Milne, *Lectures on Etale Cohomology*, version 2.21, 22 March 2013,
Section 19, pp. 125-126.

https://www.jmilne.org/math/CourseNotes/LEC.pdf

Page 125 describes the correspondence between locally constant Z_l-sheaves
and continuous fundamental-group actions; page 126 discusses Q_l coefficients.
The finite-extension and algebraic-closure coefficient forms used here belong
to the corresponding l-adic coefficient formalism.

## Arithmetic/geometric fundamental-group exact sequence

The Stacks Project, Lemma **58.14.3**, Tag **0BTX**.

https://stacks.math.columbia.edu/tag/0BTX

For a quasi-compact, quasi-separated geometrically connected scheme X over k,
the sequence

    1 -> pi_1(X over kbar) -> pi_1(X) -> Gal(kbar/k) -> 1

is exact. Geometric connectedness is essential. Over a finite field the last
group is procyclic. A rational-point Frobenius maps to a topological generator.
The compact-group deduction from the kernel and one lift is proved in
`ArithmeticGeneration.lean`, not assumed as part of the graph result.

## Deligne equidistribution in the precise form needed

Nicholas M. Katz and Peter Sarnak,
*Random Matrices, Frobenius Eigenvalues, and Monodromy*,
American Mathematical Society Colloquium Publications **45**, AMS, 1999.
DOI: https://doi.org/10.1090/coll/045

https://web.math.princeton.edu/~nmk/RMFEM.pdf

Section 9.2.4 defines the compact Frobenius conjugacy classes.
Theorem **9.2.6(1)**, pp. 276-277, gives convergence against CONTINUOUS
central functions under smoothness, geometric connectedness, positive
dimension, purity of weight zero, positive rank, and the containment
of the arithmetic image in geometric monodromy. The denominator is the number
of parameter points, not the field cardinality.

The real pushforward step is proved in `EquidistributionPushforward.lean`.
The monodromy hypotheses for the zero-constant-term family are discharged by
the checked deductions in ArithmeticMonodromy.lean and Theorem22.lean.

## Hasse-Davenport lifting, including conventions

Keith Conrad, *L-functions for Gauss and Jacobi sums*, Theorem **3.1**, p. 3.

https://kconrad.math.uconn.edu/blurbs/gradnumthy/LfunctionGaussJacobi.pdf

For multiplicative chi_r = chi composed with the norm and additive
psi_r = psi composed with the trace, with at least one character nontrivial,

    -G(chi_r,psi_r) = (-G(chi,psi))^r.

This source provides a proof and fixes both the lifting maps and sign.
It is the precise external lifting identity declared in ExternalInputs.lean.
Its application to recovering the Frobenius determinant from power traces is
proved in CharacterLifts.lean, MonomialFourier.lean and MonomialFrobenius.lean,
using the Newton identities in PowerSums.lean.

The elementary Gauss pairing itself is proved from mathlib in
`GaussPairing.lean`; both parity cases are proved in `MonomialGauss.lean`,
`EvenMonomialGauss.lean` and `TorsionCharacters.lean`.

## Connected special linear group and compact realization

James S. Milne, *Algebraic Groups*, version 2.00, 20 December 2015,
Example 5.56, p. 95: connectedness of SL_n.

https://www.jmilne.org/math/CourseNotes/iAG200.pdf

Katz-Sarnak, Section 9.2.3, supplies the maximal compact group. For the
unitarization used in choosing its matrix realization, see Jean Fresnel,
"Compact Subgroups of GL_n(C)," *Rendiconti del Seminario Matematico della
Universita di Padova* **116** (2006), 187-192, Theorem 1.1(ii).

https://www.numdam.org/item/RSMUP_2006__116__187_0.pdf

After conjugation into U(n), maximality identifies the compact subgroup with
H(C) intersect U(n). The inference from SL containment to SU containment
is proved in CoefficientCohomologyData.compactSL.

