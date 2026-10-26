module

import CayleyProof
import Lean.Util.CollectAxioms

/-! Fail if any project declaration depends on anything except Lean's standard
logical axioms and the THREE explicitly named external inputs. In particular
`sorryAx` and any other theorem axiom fail. The realization axiom is a bundle
whose complete interface and sources are recorded in EXTERNAL_INPUTS.md.
-/

open Lean in
run_cmd do
  let names ← (← getEnv).constants.foldM (init := #[]) fun acc name _ => do
    pure (if (`CayleyProof).isPrefixOf name then acc.push name else acc)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``CayleyProof.External.hasseDavenport,
    ``CayleyProof.External.katzDeligneCohomologicalRealization,
    ``CayleyProof.External.weilCharacterSumBound]
  for name in names do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo m!"Axiom audit passed for {names.size} project declarations."

#print axioms CayleyProof.finite_field_graph_properties
#print axioms CayleyProof.kIndepNum_eq_one_of_curve_representations
#print axioms CayleyProof.gauss_pairing
#print axioms CayleyProof.connected_subset_finiteIndex
#print axioms CayleyProof.polynomial_growth
#print axioms CayleyProof.nonnegative_count_lower_bound
#print axioms CayleyProof.nonpositive_count_lower_bound
#print axioms CayleyProof.artinSchreierConstantFactorization
#print axioms CayleyProof.representation_range_le_of_kernel_and_generator
#print axioms CayleyProof.odd_monomialGauss_product
#print axioms CayleyProof.compact_trace_support_infinite
#print axioms CayleyProof.equidistribution_pushforward
#print axioms CayleyProof.katzSampleLaw_character_independent
#print axioms CayleyProof.theorem18_lemma15_assumptions_from_katz
#print axioms CayleyProof.normalized_coefficient_eigenbasis
#print axioms CayleyProof.monomial_sum_eq_gauss
#print axioms CayleyProof.exists_monomialGauss_product_one
#print axioms CayleyProof.prod_eq_of_powerSums
#print axioms CayleyProof.exists_determinant_one_from_monomial_traces
#print axioms CayleyProof.sheaf_factorization_supplies_monodromy_input
#print axioms CayleyProof.scalar_twist_transfers_connected_monodromy
#print axioms CayleyProof.arithmetic_image_le_from_full_family
#print axioms CayleyProof.CoefficientCohomologyData.compactSL
#print axioms CayleyProof.theorem22_from_standard_data
#print axioms CayleyProof.theorem22
#print axioms CayleyProof.theorem18_lemma15_assumptions
