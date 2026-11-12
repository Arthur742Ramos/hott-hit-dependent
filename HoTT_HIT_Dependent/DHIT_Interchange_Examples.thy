theory DHIT_Interchange_Examples
  imports DHIT_Interchange
begin

section \<open>A binary recursive HIT\<close>

definition binary_signature :: sigenv where
  "binary_signature = (\<lambda>_. \<lparr>pcons = [[], [Rec, Rec]], lcons = [[]],
    lends = [(ECon 0 [], ECon 1 [ECon 0 [], ECon 0 []])]\<rparr>)"

abbreviation binary_leaf :: tm where "binary_leaf \<equiv> PCon 0 0 []"
abbreviation binary_fork :: "tm \<Rightarrow> tm \<Rightarrow> tm" where
  "binary_fork x y \<equiv> PCon 0 1 [x,y]"

definition binary_source :: "unit \<Rightarrow> tm" where "binary_source e = binary_leaf"
definition binary_target :: "unit \<Rightarrow> tm" where
  "binary_target e = binary_fork binary_leaf binary_leaf"

lemma binary_signature_wf: "wf_hsig binary_signature 0"
  by (auto simp: wf_hsig_def binary_signature_def less_Suc_eq intro!: wf_endpt.wfECon)

lemma binary_endpoints:
  "binary_source e = lhsOf binary_signature 0 0 []"
  "binary_target e = rhsOf binary_signature 0 0 []"
  by (simp_all add: binary_source_def binary_target_def lhsOf_def rhsOf_def binary_signature_def)

lemma binary_original_graph:
  "typed_hit_graph binary_signature D G 0 (\<lambda>_::unit. 0) (\<lambda>_. [])"
proof
  show "wf_hsig binary_signature 0" by (rule binary_signature_wf)
  show "\<And>e::unit. (\<lambda>_. 0) e < length (lcons (binary_signature 0))"
    by (simp add: binary_signature_def)
  show "\<And>e::unit. length ((\<lambda>_. []) e) = length (lcons (binary_signature 0) ! ((\<lambda>_. 0) e))"
    by (simp add: binary_signature_def)
  show "\<And>i (e::unit). i < length ((\<lambda>_. []) e) \<Longrightarrow>
    wt binary_signature D G ((\<lambda>_. []) e ! i)
      (argTy 0 (lcons (binary_signature 0) ! ((\<lambda>_. 0) e) ! i))"
    by simp
qed

lemma binary_leaf_tree: "parameter_tree binary_signature 0 (\<lambda>_. {}) binary_leaf"
  by (rule parameter_tree.node) (simp_all add: binary_signature_def external_arity_def)

lemma binary_fork_tree:
  "parameter_tree binary_signature 0 (\<lambda>_. {}) x \<Longrightarrow>
   parameter_tree binary_signature 0 (\<lambda>_. {}) y \<Longrightarrow>
   parameter_tree binary_signature 0 (\<lambda>_. {}) (binary_fork x y)"
  by (rule parameter_tree.node)
    (auto simp: binary_signature_def external_arity_def less_Suc_eq)

lemma binary_source_tree: "parameter_tree binary_signature 0 (\<lambda>_. {}) (binary_source e)"
  by (simp add: binary_source_def binary_leaf_tree)

lemma binary_target_tree: "parameter_tree binary_signature 0 (\<lambda>_. {}) (binary_target e)"
  unfolding binary_target_def by (rule binary_fork_tree; rule binary_leaf_tree)

abbreviation binary_admitted where
  "binary_admitted \<equiv> {c. valid_parameter_context binary_signature 0 (\<lambda>_. {}) UNIV c}"
abbreviation binary_csrc where "binary_csrc \<equiv> context_endpoint 0 binary_source"
abbreviation binary_cdst where "binary_cdst \<equiv> context_endpoint 0 binary_target"

lemma binary_context_count:
  "point_count (binary_cdst c) = point_count (binary_csrc c) + 2"
  by (induct c)
    (simp_all add: binary_source_def binary_target_def sum_list_append)

section \<open>Varying infinite fibers and all-fiber translations\<close>

text \<open>The first integer coordinate is fixed by the base term's node count;
the other two integer coordinates are free. Thus every fiber has many elements,
and transport changes both the dependent index coordinate and free coordinates.
The base path constructor is nullary. Its two independent occurrences below
occupy distinct recursive slots of the binary point constructor; this example
tests interchange, not naturality in arguments of a path constructor.\<close>

type_synonym interchange_vector = "int \<times> int \<times> int"

definition vector_fiber :: "tm \<Rightarrow> interchange_vector set" where
  "vector_fiber t = {v. fst v = int (point_count t)}"

fun coordinate_shift :: "unit constructor_edge \<Rightarrow> int \<times> int" where
  "coordinate_shift (Generator e) = (1,0)"
| "coordinate_shift (Under k before c after) = (if before = [] then (1,0) else (0,1))"

lemma coordinate_shift_sum:
  "fst (coordinate_shift c) + snd (coordinate_shift c) = 1"
  by (cases c) simp_all

definition vector_up :: "unit constructor_edge \<Rightarrow> interchange_vector \<Rightarrow> interchange_vector" where
  "vector_up c v = (fst v + 2, fst (snd v) + fst (coordinate_shift c),
    snd (snd v) + snd (coordinate_shift c))"

definition vector_down :: "unit constructor_edge \<Rightarrow> interchange_vector \<Rightarrow> interchange_vector" where
  "vector_down c v = (fst v - 2, fst (snd v) - fst (coordinate_shift c),
    snd (snd v) - snd (coordinate_shift c))"

interpretation vector_family: graph_family_on binary_admitted binary_csrc binary_cdst
  vector_fiber vector_up vector_down
  by unfold_locales
    (auto simp: vector_fiber_def vector_up_def vector_down_def binary_context_count prod_eq_iff)

lemma vector_fibers_multiple:
  "(int (point_count t),0,0) \<in> vector_fiber t \<and>
   (int (point_count t),1,0) \<in> vector_fiber t \<and>
   ((int (point_count t),0,0)::interchange_vector) \<noteq> (int (point_count t),1,0)"
  by (simp add: vector_fiber_def)

lemma vector_up_commute:
  "vector_up c (vector_up d v) = vector_up d (vector_up c v)"
  by (simp add: vector_up_def algebra_simps)

lemma coordinate_other_argument_independent:
  "coordinate_shift (Under k before c (middle @ [x] @ after)) =
    coordinate_shift (Under k before c (middle @ [y] @ after))"
  "coordinate_shift (Under k (before @ [x] @ middle) d after) =
    coordinate_shift (Under k (before @ [y] @ middle) d after)"
  by simp_all

lemma vector_other_argument_independent:
  "vector_up (Under k before c (middle @ [x] @ after)) =
    vector_up (Under k before c (middle @ [y] @ after))"
  "vector_up (Under k (before @ [x] @ middle) d after) =
    vector_up (Under k (before @ [y] @ middle) d after)"
  by (rule ext; simp add: vector_up_def)+

lemma vector_shell_first_independent:
  "vector_up (plug_edge C (Under k before c (middle @ [x] @ after))) =
    vector_up (plug_edge C (Under k before c (middle @ [y] @ after)))"
  by (rule ext; cases C; simp add: vector_up_def)

lemma vector_shell_second_independent:
  "vector_up (plug_edge C (Under k (before @ [x] @ middle) d after)) =
    vector_up (plug_edge C (Under k (before @ [y] @ middle) d after))"
  by (rule ext; cases C; simp add: vector_up_def)

interpretation binary_graph: mixed_context_graph binary_signature 0 "\<lambda>_. {}"
  UNIV binary_source binary_target
  by unfold_locales (auto intro: binary_source_tree binary_target_tree)

interpretation vector_interchange: interchange_family binary_signature 0 "\<lambda>_. {}"
  UNIV binary_source binary_target vector_fiber vector_up vector_down
  by unfold_locales
    (auto intro: binary_source_tree binary_target_tree vector_family.up_type
      vector_family.down_type vector_family.down_up vector_family.up_down
      vector_shell_first_independent[simplified] vector_shell_second_independent[simplified] vector_up_commute)

section \<open>Two actual recursive-slot paths\<close>

abbreviation binary_left0 where
  "binary_left0 \<equiv> Under 1 [] (Generator ()) [binary_leaf]"
abbreviation binary_right1 where
  "binary_right1 \<equiv> Under 1 [binary_fork binary_leaf binary_leaf] (Generator ()) []"
abbreviation binary_right0 where
  "binary_right0 \<equiv> Under 1 [binary_leaf] (Generator ()) []"
abbreviation binary_left1 where
  "binary_left1 \<equiv> Under 1 [] (Generator ()) [binary_fork binary_leaf binary_leaf]"

definition binary_lr where "binary_lr = [Pos binary_left0, Pos binary_right1]"
definition binary_rl where "binary_rl = [Pos binary_right0, Pos binary_left1]"

lemma binary_first_slot:
  "parameter_tree binary_signature 0 (\<lambda>_. {}) t \<Longrightarrow>
    parameter_slot binary_signature 0 (\<lambda>_. {}) 1 [] [t]"
  unfolding parameter_slot_def
  by (intro conjI exI[where x="[]"] exI[where x="[Rec]"])
    (simp_all add: binary_signature_def parameter_arguments_def external_arity_def parameter_carrier_def)

lemma binary_second_slot:
  "parameter_tree binary_signature 0 (\<lambda>_. {}) t \<Longrightarrow>
    parameter_slot binary_signature 0 (\<lambda>_. {}) 1 [t] []"
  unfolding parameter_slot_def
  by (intro conjI exI[where x="[Rec]"] exI[where x="[]"])
    (simp_all add: binary_signature_def parameter_arguments_def external_arity_def parameter_carrier_def)

lemma binary_square_admitted:
  "binary_left0 \<in> binary_admitted" "binary_right1 \<in> binary_admitted"
  "binary_right0 \<in> binary_admitted" "binary_left1 \<in> binary_admitted"
proof -
  show "binary_left0 \<in> binary_admitted"
    by (simp only: mem_Collect_eq; intro valid_parameter_context.under valid_parameter_context.generator
      binary_first_slot binary_leaf_tree; simp)
  show "binary_right1 \<in> binary_admitted"
    by (simp only: mem_Collect_eq; intro valid_parameter_context.under valid_parameter_context.generator
      binary_second_slot binary_fork_tree binary_leaf_tree; simp)
  show "binary_right0 \<in> binary_admitted"
    by (simp only: mem_Collect_eq; intro valid_parameter_context.under valid_parameter_context.generator
      binary_second_slot binary_leaf_tree; simp)
  show "binary_left1 \<in> binary_admitted"
    by (simp only: mem_Collect_eq; intro valid_parameter_context.under valid_parameter_context.generator
      binary_first_slot binary_fork_tree binary_leaf_tree; simp)
qed

lemma binary_square_paths:
  "walk_on binary_admitted binary_csrc binary_cdst
    (binary_fork binary_leaf binary_leaf) binary_lr
    (binary_fork (binary_fork binary_leaf binary_leaf) (binary_fork binary_leaf binary_leaf))"
  "walk_on binary_admitted binary_csrc binary_cdst
    (binary_fork binary_leaf binary_leaf) binary_rl
    (binary_fork (binary_fork binary_leaf binary_leaf) (binary_fork binary_leaf binary_leaf))"
  by (simp_all add: binary_lr_def binary_rl_def binary_source_def binary_target_def binary_square_admitted[simplified])

lemma binary_two_slot: "two_slot binary_signature 0 (\<lambda>_. {}) 1 [] [] []"
  unfolding two_slot_def
  by (intro conjI exI[where x="[]"] exI[where x="[]"] exI[where x="[]"])
    (simp_all add: binary_signature_def parameter_arguments_def external_arity_def)

lemma binary_interchange_relation:
  "binary_graph.interchange_relation (binary_fork binary_leaf binary_leaf) binary_lr binary_rl
    (binary_fork (binary_fork binary_leaf binary_leaf) (binary_fork binary_leaf binary_leaf))"
proof -
  have G: "Generator () \<in> binary_admitted" by (auto intro: valid_parameter_context.generator)
  from binary_graph.interchange_relation.square[OF valid_shell.hole binary_two_slot G G]
  show ?thesis by (simp add: square_start_def square_lr_def square_rl_def
    binary_lr_def binary_rl_def binary_source_def binary_target_def)
qed

lemma binary_presented_square:
  "presented_eq binary_admitted binary_csrc binary_cdst binary_graph.interchange_relation
    (binary_fork binary_leaf binary_leaf) binary_lr binary_rl
    (binary_fork (binary_fork binary_leaf binary_leaf) (binary_fork binary_leaf binary_leaf))"
  by (rule presented_eq.generator) (rule binary_interchange_relation, rule binary_square_paths(1), rule binary_square_paths(2))

lemma vector_quotient_square:
  "v \<in> vector_fiber (binary_fork binary_leaf binary_leaf) \<Longrightarrow>
    vector_family.transport binary_lr v = vector_family.transport binary_rl v"
  by (rule vector_interchange.all_fiber_interchange_descent[OF binary_presented_square])

lemma vector_binary_square_all_values:
  "vector_family.transport binary_lr v = vector_family.transport binary_rl v"
  by (simp add: binary_lr_def binary_rl_def vector_up_def algebra_simps)

lemma vector_binary_square_result:
  "vector_family.transport binary_lr (3,z,w) = (7,z+1,w+1)"
  by (simp add: binary_lr_def vector_up_def)

lemma binary_square_varying_fibers:
  "vector_fiber (binary_fork binary_leaf binary_leaf) \<noteq>
    vector_fiber (binary_fork (binary_fork binary_leaf binary_leaf) (binary_fork binary_leaf binary_leaf))"
proof -
  have A: "(3,0,0) \<in> vector_fiber (binary_fork binary_leaf binary_leaf)"
    by (simp add: vector_fiber_def)
  have B: "(3,0,0) \<notin> vector_fiber
      (binary_fork (binary_fork binary_leaf binary_leaf) (binary_fork binary_leaf binary_leaf))"
    by (simp add: vector_fiber_def)
  show ?thesis using A B by blast
qed

section \<open>A compatible displayed algebra with free-coordinate data\<close>

definition vector_method :: "nat \<Rightarrow> tm list \<Rightarrow> interchange_vector option list \<Rightarrow> interchange_vector" where
  "vector_method k xs ys = (if k = 0 then (1,0,0) else
    (let a = the (ys ! 0); b = the (ys ! 1) in
      (1 + fst a + fst b, fst (snd a) + snd (snd a) + 1,
       fst (snd b) + snd (snd b))))"

lemma displayed_rec_one:
  "displayed_arguments F [Rec] [x] ys \<longleftrightarrow> (\<exists>a\<in>F x. ys = [Some a])"
  by (auto simp: displayed_arguments_zip list_all2_Cons1)

lemma displayed_rec_pair:
  "displayed_arguments F [Rec,Rec] [x,y] ys \<longleftrightarrow>
    (\<exists>a\<in>F x. \<exists>b\<in>F y. ys = [Some a,Some b])"
  by (auto simp: displayed_arguments_zip list_all2_Cons1)

lemma binary_node_shape:
  assumes T: "parameter_tree binary_signature 0 (\<lambda>_. {}) (PCon 0 k xs)"
  shows "(k = 0 \<and> xs = []) \<or> (k = 1 \<and> (\<exists>x y. xs = [x,y]))"
proof -
  from T have KL: "k < length (pcons (binary_signature 0)) \<and>
      length xs = length (pcons (binary_signature 0) ! k)"
    by (cases rule: parameter_tree.cases) auto
  have Cases: "k = 0 \<or> k = 1"
    using KL by (auto simp: binary_signature_def numeral_2_eq_2 less_Suc_eq)
  show ?thesis using KL Cases
    by (auto simp: binary_signature_def numeral_2_eq_2 length_Suc_conv)
qed

lemma vector_point_algebra:
  "parameter_displayed_algebra binary_signature 0 (\<lambda>_. {}) vector_fiber vector_method"
proof
  fix k xs ys
  assume T: "parameter_tree binary_signature 0 (\<lambda>_. {}) (PCon 0 k xs)"
    and L: "displayed_arguments vector_fiber (pcons (binary_signature 0) ! k) xs ys"
  from binary_node_shape[OF T] show "vector_method k xs ys \<in> vector_fiber (PCon 0 k xs)"
  proof
    assume "k = 0 \<and> xs = []"
    then show ?thesis by (simp add: vector_method_def vector_fiber_def)
  next
    assume "k = 1 \<and> (\<exists>x y. xs = [x,y])"
    then obtain x y where K: "k = 1" and X: "xs = [x,y]" by blast
    from L obtain a b where A: "a \<in> vector_fiber x" and B: "b \<in> vector_fiber y"
      and Y: "ys = [Some a,Some b]"
      by (simp add: K X binary_signature_def displayed_rec_pair; blast)
    show ?thesis using A B
      by (simp add: K X Y vector_method_def vector_fiber_def algebra_simps)
  qed
qed

lemma binary_slot_arity:
  assumes V: "valid_parameter_context binary_signature 0 (\<lambda>_. {}) UNIV (Under k before c after)"
    and R: "pcons (binary_signature 0) ! k = bs @ [Rec] @ zs"
  shows "k = 1 \<and> ((bs = [] \<and> zs = [Rec]) \<or> (bs = [Rec] \<and> zs = []))"
proof -
  have K: "k < 2"
    using V by (auto elim: valid_parameter_context.cases simp: parameter_slot_def binary_signature_def)
  have KP: "k = 1 \<and> bs @ [Rec] @ zs = [Rec,Rec]"
    using K R by (auto simp: binary_signature_def numeral_2_eq_2 less_Suc_eq)
  then show ?thesis by (cases bs; cases zs) (auto simp: append_eq_Cons_conv)
qed

lemma vector_method_naturality:
  assumes V: "valid_parameter_context binary_signature 0 (\<lambda>_. {}) UNIV (Under k before c after)"
    and R: "pcons (binary_signature 0) ! k = bs @ [Rec] @ zs"
    and B: "parameter_arguments binary_signature 0 (\<lambda>_. {}) bs before"
    and Z: "parameter_arguments binary_signature 0 (\<lambda>_. {}) zs after"
    and BV: "displayed_arguments vector_fiber bs before bv"
    and A: "a \<in> vector_fiber (binary_csrc c)"
    and ZV: "displayed_arguments vector_fiber zs after zv"
  shows "vector_up (Under k before c after)
      (vector_method k (before @ [binary_csrc c] @ after) (bv @ [Some a] @ zv)) =
    vector_method k (before @ [binary_cdst c] @ after) (bv @ [Some (vector_up c a)] @ zv)"
proof -
  have K: "k = 1" and Cases: "(bs = [] \<and> zs = [Rec]) \<or> (bs = [Rec] \<and> zs = [])"
    using binary_slot_arity[OF V R] by auto
  show ?thesis using Cases
  proof
    assume L: "bs = [] \<and> zs = [Rec]"
    have Bef: "before = []" and BV': "bv = []"
      using B BV L by (auto simp: parameter_arguments_def displayed_arguments_def)
    obtain y where Af: "after = [y]"
      using Z L by (auto simp: parameter_arguments_def length_Suc_conv)
    obtain b where ZV': "zv = [Some b]"
      using ZV L Af by (auto simp: displayed_rec_one)
    show ?thesis using coordinate_shift_sum[of c]
      by (auto simp: K Bef BV' Af ZV' vector_method_def vector_up_def prod_eq_iff; linarith)
  next
    assume L: "bs = [Rec] \<and> zs = []"
    have Af: "after = []" and ZV': "zv = []"
      using Z ZV L by (auto simp: parameter_arguments_def displayed_arguments_def)
    obtain x where Bef: "before = [x]"
      using B L by (auto simp: parameter_arguments_def length_Suc_conv)
    obtain b where BV': "bv = [Some b]"
      using BV L Bef by (auto simp: displayed_rec_one)
    show ?thesis using coordinate_shift_sum[of c]
      by (auto simp: K Bef BV' Af ZV' vector_method_def vector_up_def prod_eq_iff; linarith)
  qed
qed

lemma vector_base_boundary:
  "vector_up (Generator e) (parameter_fold binary_signature 0 vector_method (binary_source e)) =
    parameter_fold binary_signature 0 vector_method (binary_target e)"
  by (simp add: binary_source_def binary_target_def vector_method_def vector_up_def
    binary_signature_def ih_mask_def)

interpretation vector_context: contextual_parameter_algebra binary_signature 0 "\<lambda>_. {}"
  vector_fiber vector_method UNIV binary_source binary_target vector_up vector_down
  by (unfold_locales,
      (rule parameter_displayed_algebra.method_type[OF vector_point_algebra]; assumption),
      auto intro: binary_source_tree binary_target_tree vector_family.up_type vector_family.down_type
        vector_family.down_up vector_family.up_down vector_base_boundary[simplified]
        vector_method_naturality[simplified])

lemma vector_constructed_elimination:
  "parameter_tree binary_signature 0 (\<lambda>_. {}) x \<Longrightarrow>
    walk_on binary_admitted binary_csrc binary_cdst x p y \<Longrightarrow>
    vector_family.transport p (parameter_fold binary_signature 0 vector_method x) =
      parameter_fold binary_signature 0 vector_method y \<and>
    parameter_fold binary_signature 0 vector_method y \<in> vector_fiber y"
  by (rule vector_context.contextual_dependent_eliminator)

lemma vector_constructed_section_and_square:
  "parameter_fold binary_signature 0 vector_method (binary_fork binary_leaf binary_leaf) = (3,1,0) \<and>
    vector_family.transport binary_lr
      (parameter_fold binary_signature 0 vector_method (binary_fork binary_leaf binary_leaf)) =
    parameter_fold binary_signature 0 vector_method
      (binary_fork (binary_fork binary_leaf binary_leaf) (binary_fork binary_leaf binary_leaf))"
  by (simp add: binary_lr_def vector_up_def vector_method_def binary_signature_def ih_mask_def)

text \<open>The successful displayed method uses arbitrary typed induction
hypotheses, not only the previously selected section. Each child transport
increases the sum of its two free coordinates by one, which is precisely the
change propagated to the corresponding parent coordinate. The same transport
also satisfies interchange on every fiber value, including values outside the
image of the point methods.\<close>

section \<open>Why point-section coherence does not imply interchange\<close>

fun swap12 :: "nat \<Rightarrow> nat" where
  "swap12 x = (if x = 1 then 2 else if x = 2 then 1 else x)"
fun swap23 :: "nat \<Rightarrow> nat" where
  "swap23 x = (if x = 2 then 3 else if x = 3 then 2 else x)"

fun bad_up :: "unit constructor_edge \<Rightarrow> nat \<Rightarrow> nat" where
  "bad_up (Generator e) a = a"
| "bad_up (Under k before c after) a = (if before = [] then swap12 a else swap23 a)"

lemma swaps_inverse [simp]: "swap12 (swap12 a) = a" "swap23 (swap23 a) = a"
  by auto

lemma bad_up_inverse [simp]: "bad_up c (bad_up c a) = a"
  by (cases c) simp_all

lemma bad_up_fixes_zero [simp]: "bad_up c 0 = 0"
  by (cases c) simp_all

lemma bad_up_fiber:
  "a < 4 \<Longrightarrow> bad_up c a < 4"
  by (cases c) auto

lemma zero_point_algebra:
  "parameter_displayed_algebra binary_signature 0 (\<lambda>_. {}) (\<lambda>_. {a::nat. a < 4}) (\<lambda>_ _ _. 0)"
  by unfold_locales simp

lemma zero_parameter_fold:
  "parameter_tree binary_signature 0 (\<lambda>_. {}) t \<Longrightarrow>
    parameter_fold binary_signature 0 (\<lambda>_ _ _. 0) t = 0"
  by (induct rule: parameter_tree.induct) simp

interpretation bad_context: contextual_parameter_algebra binary_signature 0 "\<lambda>_. {}"
  "\<lambda>_. {a::nat. a < 4}" "\<lambda>_ _ _. 0" UNIV binary_source binary_target bad_up bad_up
  apply unfold_locales
  using binary_source_tree binary_target_tree
  by (auto intro: bad_up_fiber simp: zero_parameter_fold)

lemma bad_context_square_fails:
  "bad_context.fibers.transport binary_lr 1 = 3 \<and>
   bad_context.fibers.transport binary_rl 1 = 2"
  by (simp add: binary_lr_def binary_rl_def)

lemma bad_context_selected_section_agrees:
  "bad_context.fibers.transport binary_lr 0 = bad_context.fibers.transport binary_rl 0"
  by (simp add: binary_lr_def binary_rl_def)

lemma binary_square_not_cancellation_equal:
  "\<not> equality_on binary_admitted binary_csrc binary_cdst
    (binary_fork binary_leaf binary_leaf) binary_lr binary_rl
    (binary_fork (binary_fork binary_leaf binary_leaf) (binary_fork binary_leaf binary_leaf))"
proof
  assume E: "equality_on binary_admitted binary_csrc binary_cdst
    (binary_fork binary_leaf binary_leaf) binary_lr binary_rl
    (binary_fork (binary_fork binary_leaf binary_leaf) (binary_fork binary_leaf binary_leaf))"
  have A: "(1::nat) \<in> {a. a < 4}" by simp
  have "bad_context.fibers.transport binary_lr 1 = bad_context.fibers.transport binary_rl 1"
    by (rule bad_context.fibers.transport_equal[OF E A])
  then show False using bad_context_square_fails by auto
qed

lemma bad_context_not_relation_compatible:
  "\<not> (\<forall>x p q y a. binary_graph.interchange_relation x p q y \<longrightarrow>
    walk_on binary_admitted binary_csrc binary_cdst x p y \<longrightarrow>
    walk_on binary_admitted binary_csrc binary_cdst x q y \<longrightarrow>
    a < 4 \<longrightarrow> bad_context.fibers.transport p a = bad_context.fibers.transport q a)"
proof
  assume H: "\<forall>x p q y a. binary_graph.interchange_relation x p q y \<longrightarrow>
    walk_on binary_admitted binary_csrc binary_cdst x p y \<longrightarrow>
    walk_on binary_admitted binary_csrc binary_cdst x q y \<longrightarrow>
    a < 4 \<longrightarrow> bad_context.fibers.transport p a = bad_context.fibers.transport q a"
  have "bad_context.fibers.transport binary_lr 1 = bad_context.fibers.transport binary_rl 1"
    using H[rule_format, OF binary_interchange_relation binary_square_paths(1,2), of 1] by simp
  then show False using bad_context_square_fails by auto
qed

text \<open>The counterexample satisfies the old displayed point-method and
contextual naturality hypotheses. Both permutations fix the selected section,
but they do not commute on another element of the same fiber. Consequently
all-fiber interchange needs an additional law; it cannot be inferred from
coherence only on the image of the point methods.\<close>

end
