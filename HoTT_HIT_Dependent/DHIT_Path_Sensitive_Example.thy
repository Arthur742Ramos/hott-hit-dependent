theory DHIT_Path_Sensitive_Example
  imports DHIT_Coherence_From_Local
begin

section \<open>Recursive naturality and interchange with nontrivial loop transport\<close>

text \<open>The point constructors are a constant, a unary constructor and a
binary constructor. A recursive path collapses the unary constructor; a
nullary path loops at the constant. Fibers are the constant integer set, not
a varying motive. The loop acts by negation and the collapse by identity,
uniformly under constructor shells. This example checks the combined coherence
interface; it does not supply a displayed point-method interpretation.\<close>

definition twist_signature :: sigenv where
  "twist_signature = (\<lambda>_. \<lparr>pcons = [[], [Rec], [Rec, Rec]],
    lcons = [[Rec], []],
    lends = [(ECon 1 [EArg 0], EArg 0), (ECon 0 [], ECon 0 [])]\<rparr>)"

abbreviation twist_zero :: tm where "twist_zero \<equiv> PCon 0 0 []"
abbreviation twist_unary where "twist_unary x \<equiv> PCon 0 1 [x]"
abbreviation twist_binary where "twist_binary x y \<equiv> PCon 0 2 [x,y]"

lemma twist_signature_wf: "wf_hsig twist_signature 0"
  by (auto simp: wf_hsig_def twist_signature_def less_Suc_eq numeral_2_eq_2
    intro!: wf_endpt.wfECon recursive_argument_endpoint)

interpretation twist: signature_path_structure twist_signature 0 "\<lambda>_. {}"
  by unfold_locales
    (rule twist_signature_wf, auto simp: twist_signature_def external_arity_def less_Suc_eq numeral_2_eq_2)

fun loop_flag :: "(nat \<times> tm list) constructor_edge \<Rightarrow> bool" where
  "loop_flag (Generator e) = (fst e = 1)"
| "loop_flag (Under k before c after) = loop_flag c"

definition twist_action :: "(nat \<times> tm list) constructor_edge \<Rightarrow> int \<Rightarrow> int" where
  "twist_action c a = (if loop_flag c then -a else a)"

lemma loop_flag_shell [simp]: "loop_flag (plug_edge C c) = loop_flag c"
  by (induct C) simp_all

lemma twist_action_inverse [simp]: "twist_action c (twist_action c a) = a"
  by (simp add: twist_action_def)

lemma twist_action_commute:
  "twist_action c (twist_action d a) = twist_action d (twist_action c a)"
  by (simp add: twist_action_def)

interpretation twist_interchange: interchange_family twist_signature 0 "\<lambda>_. {}"
  twist.edges twist.src twist.dst "\<lambda>_. UNIV" twist_action twist_action
  by unfold_locales
    (auto intro: twist.source_tree twist.target_tree
      simp: twist_action_def fun_eq_iff)

lemma twist_argument_shape:
  assumes K: "k < length (lcons (twist_signature 0))"
    and A: "a \<in> twist.paths.argument_edges (lcons (twist_signature 0) ! k)"
  obtains c where "k = 0" "a = ArgumentEdge [] c []"
proof -
  obtain bs zs before c after where
    X: "a = ArgumentEdge before c after" "lcons (twist_signature 0) ! k = bs @ [Rec] @ zs"
    "parameter_arguments twist_signature 0 (\<lambda>_. {}) bs before"
    "parameter_arguments twist_signature 0 (\<lambda>_. {}) zs after"
    using A by (auto simp: twist.paths.argument_edges_def)
  have Cases: "k = 0 \<or> k = 1"
    using K by (simp add: twist_signature_def less_Suc_eq numeral_2_eq_2)
  have K0: "k = 0"
    using X(2) Cases by (auto simp: twist_signature_def)
  have BZ: "bs = [] \<and> zs = []"
    using arg_cong[OF X(2), of length] K0 by (simp add: twist_signature_def)
  have "before = []" "after = []"
    using X(3,4) BZ by (auto simp: parameter_arguments_def)
  with X K0 show thesis by (auto intro: that)
qed

lemma twist_elementary_naturality:
  assumes K: "k < length (lcons (twist_signature 0))"
    and A: "e \<in> twist.paths.argument_edges (lcons (twist_signature 0) ! k)"
  shows "twist_interchange.transport (twist.generator_component k C (argument_source 0 twist.dst e))
      (twist_interchange.transport (twist.elementary_left k C e) a) =
    twist_interchange.transport (twist.elementary_right k C e)
      (twist_interchange.transport (twist.generator_component k C (argument_source 0 twist.src e)) a)"
proof -
  obtain c where K0: "k = 0" and E: "e = ArgumentEdge [] c []"
    by (rule twist_argument_shape[OF K A])
  show ?thesis
    unfolding twist.generator_component_def twist.elementary_left_def twist.elementary_right_def
    by (simp add: K0 E twist_signature_def twist_action_def lift_path_def)
qed

interpretation twist_local: locally_natural_signature_family twist_signature 0 "\<lambda>_. {}"
  "\<lambda>_. UNIV" twist_action twist_action
  by unfold_locales
    (auto intro: twist.signature twist.external_points twist.source_tree twist.target_tree
      twist_elementary_naturality simp: twist_action_def fun_eq_iff)

lemma twist_coherent_model:
  "coherent_signature_family twist_signature 0 (\<lambda>_. {})
    (\<lambda>_. UNIV) twist_action twist_action"
  by (rule twist_local.coherent.coherent_signature_family_axioms)

section \<open>A loop survives the combined quotient\<close>

abbreviation twist_loop where
  "twist_loop \<equiv> Generator (1, [] :: tm list)"

lemma twist_zero_tree:
  "parameter_tree twist_signature 0 (\<lambda>_. {}) twist_zero"
  by (rule parameter_tree.node) (simp_all add: twist_signature_def external_arity_def)

lemma twist_loop_edge: "twist_loop \<in> twist.paths.admitted"
  by (auto simp: signature_edges_def twist_signature_def parameter_arguments_def
      external_arity_def intro: valid_parameter_context.generator)

lemma twist_loop_typed:
  "walk_on twist.paths.admitted twist.paths.cs twist.paths.ct twist_zero [Pos twist_loop] twist_zero"
  using twist_loop_edge
  by (auto simp: lhsOf_def rhsOf_def twist_signature_def)

lemma twist_loop_action:
  "twist_interchange.transport [Pos twist_loop] a = -a"
  by (simp add: twist_action_def)

lemma twist_loop_not_trivial:
  "\<not> presented_eq twist.paths.admitted twist.paths.cs twist.paths.ct
    twist.coherence_relation twist_zero [Pos twist_loop] [] twist_zero"
proof
  assume H: "presented_eq twist.paths.admitted twist.paths.cs twist.paths.ct
    twist.coherence_relation twist_zero [Pos twist_loop] [] twist_zero"
  have "twist_interchange.transport [Pos twist_loop] (1::int) =
      twist_interchange.transport [] 1"
    by (rule twist_local.coherent.all_fiber_coherent_descent[OF H]) simp
  then show False by (simp add: twist_action_def)
qed

section \<open>One recursive naturality cell and one binary interchange cell\<close>

lemma twist_loop_argument:
  "ArgumentEdge [] twist_loop [] \<in> twist.paths.argument_edges [Rec]"
  using twist_loop_edge
  by (auto simp: twist.paths.argument_edges_def parameter_arguments_def external_arity_def)

lemma twist_recursive_naturality_cell:
  "twist.naturality_relation (twist_unary twist_zero)
    [Pos (Under 1 [] twist_loop []), Pos (Generator (0,[twist_zero]))]
    [Pos (Generator (0,[twist_zero])), Pos twist_loop] twist_zero"
proof -
  have K: "0 < length (lcons (twist_signature 0))" by (simp add: twist_signature_def)
  have A: "twist.paths.argument_motion (lcons (twist_signature 0) ! 0)
    [twist_zero] [[Pos twist_loop]] [twist_zero]"
    using twist.paths.elementary_motion_typed[OF twist_loop_argument]
    by (simp add: twist_signature_def lhsOf_def rhsOf_def)
  show ?thesis using twist.naturality_relation.square[OF K A valid_shell.hole]
    by (simp add: twist_signature_def lhsOf_def rhsOf_def)
qed

lemma twist_recursive_naturality_action:
  "twist_interchange.transport
    [Pos (Under 1 [] twist_loop []), Pos (Generator (0,[twist_zero]))] a = -a"
  "twist_interchange.transport
    [Pos (Generator (0,[twist_zero])), Pos twist_loop] a = -a"
  by (simp_all add: twist_action_def)

lemma twist_binary_slots: "two_slot twist_signature 0 (\<lambda>_. {}) 2 [] [] []"
  by (auto simp: two_slot_def twist_signature_def parameter_arguments_def external_arity_def)

lemma twist_binary_interchange_cell:
  "twist.contexts.interchange_relation (twist_binary twist_zero twist_zero)
    [Pos (Under 2 [] twist_loop [twist_zero]), Pos (Under 2 [twist_zero] twist_loop [])]
    [Pos (Under 2 [twist_zero] twist_loop []), Pos (Under 2 [] twist_loop [twist_zero])]
    (twist_binary twist_zero twist_zero)"
  using twist.contexts.interchange_relation.square[OF valid_shell.hole
    twist_binary_slots twist_loop_edge twist_loop_edge]
  by (simp add: square_start_def square_lr_def square_rl_def lhsOf_def rhsOf_def twist_signature_def)

lemma twist_binary_interchange_action:
  "twist_interchange.transport
    [Pos (Under 2 [] twist_loop [twist_zero]), Pos (Under 2 [twist_zero] twist_loop [])] a = a"
  "twist_interchange.transport
    [Pos (Under 2 [twist_zero] twist_loop []), Pos (Under 2 [] twist_loop [twist_zero])] a = a"
  by (simp_all add: twist_action_def)

lemma twist_binary_distinct_nonidentity:
  "[Pos (Under 2 [] twist_loop [twist_zero]), Pos (Under 2 [twist_zero] twist_loop [])] \<noteq>
     [Pos (Under 2 [twist_zero] twist_loop []), Pos (Under 2 [] twist_loop [twist_zero])] \<and>
   twist_interchange.transport [Pos (Under 2 [] twist_loop [twist_zero])] 1 = -1 \<and>
   twist_interchange.transport [Pos (Under 2 [twist_zero] twist_loop [])] 1 = -1"
  by (simp add: twist_action_def)

text \<open>The two independent occurrences each negate the residual value;
their composites agree on every integer. The recursive collapse generator has
identity action, and its naturality cell relates the same nonidentity loop
under the unary constructor to the loop at its argument. The loop itself is
not the identity in the combined presentation. This proves path sensitivity,
not faithfulness of the entire presentation.\<close>

end
