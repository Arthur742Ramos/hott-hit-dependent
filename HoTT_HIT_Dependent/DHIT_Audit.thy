theory DHIT_Audit
  imports DHIT_Syntax_Bridge DHIT_Dependent_Transport DHIT_Sections DHIT_Displayed_Algebra
    DHIT_Parameter_Algebra DHIT_Parameter_Substitution DHIT_Constructor_Congruence DHIT_Parameter_Congruence
begin

section \<open>Proof-dependency audit\<close>

text \<open>The following check rejects oracle dependencies in the selected
headline results. It is an audit of existing proofs, not a proof-producing
extension. Locale assumptions remain explicit hypotheses of their theorems.\<close>

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
     @{thm shifted_interval_section}];
  val _ = if null (Thm_Deps.all_oracles dependent_headlines) then ()
    else error "Unexpected proof oracle in dependent-family headline results";
\<close>

end
