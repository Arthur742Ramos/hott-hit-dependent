theory DHIT_Audit
  imports DHIT_Type_Formers DHIT_Sections DHIT_Displayed_Substitution
    DHIT_Affine_Model DHIT_Interchange_Examples DHIT_Path_Sensitive_Example
begin

section \<open>Proof-dependency audit\<close>

text \<open>The following check rejects oracle dependencies in the selected
headline results. It is an audit of existing proofs, not a proof-producing
extension. The principal equivalence is
@{thm [source] local_global_signature_coherence}; its constructed-fold consequence
is @{thm [source] locally_natural_signature_family.constructed_coherent_elimination}.
The list also explicitly includes all-fiber descent, representative-independent
quotient transport, and both successful and separating model results.

The Isabelle library operation traverses the selected theorems' transitive
proof dependencies and collects their recorded oracles. This is not an audit
of every theorem or of every logical axiom. In particular, ordinary HOL
foundations and choice remain in use, and locale assumptions remain explicit
hypotheses. The ML block only inspects existing theorem values and raises an
error on an unexpected oracle; it creates no theorem, axiom, or oracle.\<close>

ML \<open>
  val dependent_headlines =
    [@{thm cancel_subject_reduction},
     @{thm cancellation_terminates},
     @{thm path_equal_inverse_right},
     @{thm graph_family.transport_bijective},
     @{thm graph_family.transport_equal},
     @{thm graph_family.boundary_coherence_iff},
     @{thm based_graph_family.section_bijection},
     @{thm based_graph_family.invariant_iff_all_loops},
     @{thm based_graph_family.extension_route_independent},
     @{thm dependent_graph_family.pi_beta},
     @{thm dependent_graph_family.pi_eta},
     @{thm dependent_graph_family.pi_path_evaluation},
     @{thm dependent_graph_family.dependent_cancellation_subject_reduction},
     @{thm family_reindexing.transport_substitution},
     @{thm family_reindexing.dependent_section_substitution},
     @{thm instE_term_substitution},
     @{thm typed_hit_graph_substitution},
     @{thm typed_hit_graph.hit_substitution_reindexing},
     @{thm typed_hit_graph.typed_section_coherence},
     @{thm displayed_point_algebra.constructed_section_type},
     @{thm displayed_point_algebra.constructed_section_unique},
     @{thm point_fold_endpoint},
     @{thm displayed_hit_algebra.constructed_dependent_eliminator},
     @{thm displayed_hit_algebra.original_typed_graph},
     @{thm recursive_hit_path_computation},
     @{thm displayed_point_algebra.displayed_endpoint_type_general},
     @{thm parameter_displayed_algebra.constructed_section_type},
     @{thm parameter_displayed_algebra.constructed_section_unique},
     @{thm parameter_hit_algebra.constructed_dependent_eliminator},
     @{thm parameter_list_original_graph},
     @{thm parameterized_hit_path_computation},
     @{thm parameter_tree_substitution},
     @{thm parameter_fold_substitution},
     @{thm parameter_endpoint_substitution},
     @{thm displayed_algebra_substitution},
     @{thm opaque_parameter_substitution_example},
     @{thm substituted_parameter_list_typed},
     @{thm graph_family_on.transport_equal},
     @{thm graph_family_on.boundary_coherence_iff},
     @{thm empty_graph_family},
     @{thm contextual_point_algebra.contextual_dependent_eliminator},
     @{thm contextual_point_algebra.contextual_equality_descent},
     @{thm contextual_point_algebra.constructor_equality_lifting},
     @{thm displayed_hit_algebra.original_contextual_algebra},
     @{thm recursive_context_path_computation},
     @{thm contextual_parameter_algebra.contextual_dependent_eliminator},
     @{thm contextual_parameter_algebra.constructor_equality_lifting},
     @{thm parameter_hit_algebra.original_contextual_algebra},
     @{thm parameterized_context_path_computation},
     @{thm graph_family_on_UNIV},
     @{thm equality_on_UNIV},
     @{thm twisted_loop_has_no_section},
     @{thm shifted_interval_section},
     @{thm parameter_hit_algebra_substitution},
     @{thm contextual_parameter_algebra_substitution},
     @{thm path_presentation.qcompose_associative},
     @{thm path_presentation.qinverse_right},
     @{thm quotient_family.presented_transport},
     @{thm quotient_family.quotient_transport_class},
     @{thm quotient_family.quotient_transport_member},
     @{thm quotient_family.quotient_transport_bijective},
     @{thm quotient_family.quotient_transport_composition},
     @{thm quotient_family.quotient_transport_inverse},
     @{thm presented_path_map.map_hom_composition},
     @{thm presented_path_map.map_hom_inverse},
     @{thm contextual_parameter_algebra.constructed_section_quotient_descent},
     @{thm mixed_context_graph.constructor_preserves_composition},
     @{thm mixed_context_graph.constructor_preserves_inverse},
     @{thm mixed_context_graph.two_path_interchange},
     @{thm interchange_family.all_fiber_interchange_descent},
     @{thm interchange_family.arbitrary_path_transport_interchange},
     @{thm path_natural_family.path_naturality},
     @{thm parameter_path_structure.endpoint_motion_typed},
     @{thm signature_path_structure.original_endpoint_paths(1)},
     @{thm signature_path_structure.original_endpoint_paths(2)},
     @{thm parameter_path_structure.argument_motion_serialization},
     @{thm parameter_path_structure.elementary_endpoint_interpretation},
     @{thm serialize_coordinates_recover},
     @{thm endpoint_functor.constructor_motion_compose},
     @{thm endpoint_functor.constructor_motion_cong},
     @{thm endpoint_functor.endpoint_motion_identity},
     @{thm endpoint_functor.endpoint_motion_compose},
     @{thm endpoint_functor.endpoint_motion_cong},
     @{thm endpoint_functor.endpoint_motion_inverse},
     @{thm endpoint_functor.endpoint_image_projected},
     @{thm endpoint_functor.endpoint_motion_serialization},
     @{thm signature_path_structure.presented_coherence_lifting},
     @{thm coherent_signature_family.all_fiber_coherent_descent},
     @{thm locally_natural_signature_family.argument_graph_naturality},
     @{thm locally_natural_signature_family.serialized_argument_naturality},
     @{thm local_global_signature_coherence},
     @{thm locally_natural_signature_family.constructed_coherent_elimination},
     @{thm affine_graph.transport_formula},
     @{thm affine_graph.arbitrary_presentation},
     @{thm recursive_generator_naturality_presented},
     @{thm recursive_naturality_all_residuals},
     @{thm vector_binary_square_all_values},
     @{thm vector_constructed_section_and_square},
     @{thm binary_square_not_cancellation_equal},
     @{thm bad_context_not_relation_compatible},
     @{thm twist_coherent_model},
     @{thm twist_loop_typed},
     @{thm twist_loop_action},
     @{thm twist_loop_not_trivial},
     @{thm twist_recursive_naturality_cell},
     @{thm twist_recursive_naturality_action(1)},
     @{thm twist_recursive_naturality_action(2)},
     @{thm twist_binary_interchange_cell},
     @{thm twist_binary_interchange_action(1)},
     @{thm twist_binary_interchange_action(2)},
     @{thm twist_binary_distinct_nonidentity}];
  val _ = if null (Thm_Deps.all_oracles dependent_headlines) then ()
    else error "Unexpected proof oracle in dependent-family headline results";
\<close>

end
