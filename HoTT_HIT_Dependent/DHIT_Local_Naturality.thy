theory DHIT_Local_Naturality
  imports DHIT_Argument_Graph DHIT_Coherent_Signature
begin

section \<open>Local recursive-slot squares imply signed argument-path naturality\<close>

context signature_path_structure
begin

definition elementary_left where
  "elementary_left k C a = lift_path C
    (endpoint_motion h (argument_source h src a) (argument_source h dst a)
      (paths.elementary_motion a) (fst (lends (S h) ! k)))"

definition elementary_right where
  "elementary_right k C a = lift_path C
    (endpoint_motion h (argument_source h src a) (argument_source h dst a)
      (paths.elementary_motion a) (snd (lends (S h) ! k)))"

definition generator_component where
  "generator_component k C xs = lift_path C [Pos (Generator (k,xs))]"

lemma elementary_left_interpretation:
  assumes K: "k < length (lcons (S h))" and C: "valid_shell S h P C"
  shows "path_interpretation (paths.argument_edges (lcons (S h) ! k))
    (argument_source h src) (argument_source h dst) paths.admitted paths.cs paths.ct
    (\<lambda>xs. plug_term h C (lhsOf S h k xs)) (elementary_left k C)"
proof
  fix a assume A: "a \<in> paths.argument_edges (lcons (S h) ! k)"
  note M = paths.elementary_motion_typed[OF A]
  note W = original_endpoint_paths(1)[OF K M]
  show "walk_on paths.admitted paths.cs paths.ct
    (plug_term h C (lhsOf S h k (argument_source h src a)))
    (elementary_left k C a) (plug_term h C (lhsOf S h k (argument_source h dst a)))"
    using contexts.shell_path_lifting[OF W C] by (simp add: elementary_left_def)
qed

lemma elementary_right_interpretation:
  assumes K: "k < length (lcons (S h))" and C: "valid_shell S h P C"
  shows "path_interpretation (paths.argument_edges (lcons (S h) ! k))
    (argument_source h src) (argument_source h dst) paths.admitted paths.cs paths.ct
    (\<lambda>xs. plug_term h C (rhsOf S h k xs)) (elementary_right k C)"
proof
  fix a assume A: "a \<in> paths.argument_edges (lcons (S h) ! k)"
  note M = paths.elementary_motion_typed[OF A]
  note W = original_endpoint_paths(2)[OF K M]
  show "walk_on paths.admitted paths.cs paths.ct
    (plug_term h C (rhsOf S h k (argument_source h src a)))
    (elementary_right k C a) (plug_term h C (rhsOf S h k (argument_source h dst a)))"
    using contexts.shell_path_lifting[OF W C] by (simp add: elementary_right_def)
qed

lemma generator_component_typed:
  assumes K: "k < length (lcons (S h))" and C: "valid_shell S h P C"
    and X: "parameter_arguments S h P (lcons (S h) ! k) xs"
  shows "walk_on paths.admitted paths.cs paths.ct (plug_term h C (lhsOf S h k xs))
    (generator_component k C xs) (plug_term h C (rhsOf S h k xs))"
  using contexts.shell_path_lifting[OF canonical_generator_typed[OF K X] C]
  by (simp add: generator_component_def)

end

text \<open>The additional naturality premise concerns one positive contextual
edge in one recursive argument, uniformly in an outer shell and every fiber
value. It is not a premise about arbitrary tuple paths. Interchange is retained
as an independent hypothesis for subsequent comparison with endpoint motions.\<close>

locale locally_natural_signature_family = signature_path_structure S h P +
  fibers: interchange_family S h P "signature_edges S h P"
    "\<lambda>e. lhsOf S h (fst e) (snd e)" "\<lambda>e. rhsOf S h (fst e) (snd e)" F up down
  for S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set"
    and F :: "tm \<Rightarrow> 'a set"
    and up down :: "(nat \<times> tm list) constructor_edge \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes elementary_naturality:
    "k < length (lcons (S h)) \<Longrightarrow> valid_shell S h P C \<Longrightarrow>
     e \<in> paths.argument_edges (lcons (S h) ! k) \<Longrightarrow>
     a \<in> F (plug_term h C (lhsOf S h k (argument_source h src e))) \<Longrightarrow>
     fibers.transport (generator_component k C (argument_source h dst e))
       (fibers.transport (elementary_left k C e) a) =
     fibers.transport (elementary_right k C e)
       (fibers.transport (generator_component k C (argument_source h src e)) a)"
begin

lemma elementary_natural_interpretation:
  assumes K: "k < length (lcons (S h))" and C: "valid_shell S h P C"
  shows "path_natural_family
    (paths.argument_edges (lcons (S h) ! k)) (argument_source h src) (argument_source h dst)
    paths.admitted paths.cs paths.ct
    (\<lambda>xs. plug_term h C (lhsOf S h k xs))
    (\<lambda>xs. plug_term h C (rhsOf S h k xs)) (elementary_left k C) (elementary_right k C)
    F up down {xs. parameter_arguments S h P (lcons (S h) ! k) xs}
    (generator_component k C)"
proof -
  interpret L: path_interpretation
    "paths.argument_edges (lcons (S h) ! k)" "argument_source h src" "argument_source h dst"
    paths.admitted paths.cs paths.ct "\<lambda>xs. plug_term h C (lhsOf S h k xs)" "elementary_left k C"
    by (rule elementary_left_interpretation[OF K C])
  interpret R: path_interpretation
    "paths.argument_edges (lcons (S h) ! k)" "argument_source h src" "argument_source h dst"
    paths.admitted paths.cs paths.ct "\<lambda>xs. plug_term h C (rhsOf S h k xs)" "elementary_right k C"
    by (rule elementary_right_interpretation[OF K C])
  show ?thesis
    by unfold_locales
      (auto intro: L.edge_image R.edge_image fibers.up_type fibers.down_type fibers.down_up fibers.up_down
        paths.argument_edge_carriers generator_component_typed[OF K C] elementary_naturality[OF K C])
qed

lemma argument_graph_naturality:
  assumes K: "k < length (lcons (S h))" and C: "valid_shell S h P C"
    and W: "walk_on (paths.argument_edges (lcons (S h) ! k))
      (argument_source h src) (argument_source h dst) xs p ys"
    and A: "a \<in> F (plug_term h C (lhsOf S h k xs))"
  shows "fibers.transport (generator_component k C ys)
      (fibers.transport (path_image (elementary_left k C) p) a) =
    fibers.transport (path_image (elementary_right k C) p)
      (fibers.transport (generator_component k C xs) a)"
  using path_natural_family.path_naturality[OF elementary_natural_interpretation[OF K C] W A] .

lemma serialized_argument_naturality:
  assumes K: "k < length (lcons (S h))" and C: "valid_shell S h P C"
    and M: "paths.argument_motion (lcons (S h) ! k) xs ps ys"
    and A: "a \<in> F (plug_term h C (lhsOf S h k xs))"
  shows "fibers.transport (generator_component k C ys)
      (fibers.transport (path_image (elementary_left k C) (serialize_arguments [] xs ys ps)) a) =
    fibers.transport (path_image (elementary_right k C) (serialize_arguments [] xs ys ps))
      (fibers.transport (generator_component k C xs) a)"
  by (rule argument_graph_naturality[OF K C paths.argument_motion_serialization[OF M] A])

end
end
