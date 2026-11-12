theory DHIT_Affine_Model
  imports DHIT_Coherent_Signature
begin

section \<open>An infinite-fiber family respecting every parallel path equation\<close>

definition affine_fiber :: "('v \<Rightarrow> int) \<Rightarrow> 'v \<Rightarrow> (int \<times> int) set" where
  "affine_fiber q x = {a. fst a = q x}"

definition affine_up :: "('v \<Rightarrow> int) \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow>
    'e \<Rightarrow> (int \<times> int) \<Rightarrow> (int \<times> int)" where
  "affine_up q s t e a = (fst a + q (t e) - q (s e), snd a)"

locale affine_graph =
  fixes E :: "'e set" and s t :: "'e \<Rightarrow> 'v" and q :: "'v \<Rightarrow> int"
begin

sublocale family: graph_family_on E s t "affine_fiber q" "affine_up q s t" "affine_up q t s"
  by unfold_locales (auto simp: affine_fiber_def affine_up_def prod_eq_iff)

lemma transport_formula:
  "walk_on E s t x p y \<Longrightarrow> family.transport p a = (fst a + q y - q x, snd a)"
proof (induct arbitrary: a rule: walk_on_induct)
  case (nil x)
  then show ?case by simp
next
  case (cons d p y)
  have "family.transport (d # p) a =
      (fst (family.step_transport d a) + q y - q (target s t d), snd (family.step_transport d a))"
    by (simp only: family.transport.simps cons(3))
  also have "... = (fst a + q y - q (source s t d), snd a)"
    by (cases d) (simp_all add: affine_up_def algebra_simps)
  finally show ?case .
qed

lemma parallel_transport:
  "walk_on E s t x p y \<Longrightarrow> walk_on E s t x r y \<Longrightarrow>
    family.transport p a = family.transport r a"
  by (simp add: transport_formula)

lemma arbitrary_presentation:
  "quotient_family E s t (affine_fiber q) (affine_up q s t) (affine_up q t s) R"
  by unfold_locales
    (auto intro: family.up_type family.down_type family.down_up family.up_down parallel_transport)

lemma two_distinct_values:
  "(q x, 0) \<in> affine_fiber q x \<and> (q x, 1) \<in> affine_fiber q x \<and> (q x, (0::int)) \<noteq> (q x, 1)"
  by (simp add: affine_fiber_def)

end

section \<open>Count differences are independent of constructor shells\<close>

definition count_difference :: "nat \<Rightarrow> ('e \<Rightarrow> tm) \<Rightarrow> ('e \<Rightarrow> tm) \<Rightarrow>
    'e constructor_edge \<Rightarrow> int" where
  "count_difference h s t c = int (point_count (context_endpoint h t c)) -
    int (point_count (context_endpoint h s c))"

lemma count_difference_under [simp]:
  "count_difference h s t (Under k before c after) = count_difference h s t c"
  by (simp add: count_difference_def sum_list_append)

lemma count_difference_shell [simp]:
  "count_difference h s t (plug_edge C c) = count_difference h s t c"
  by (induct C) simp_all

lemma count_affine_up:
  "affine_up (\<lambda>x. int (point_count x)) (context_endpoint h s) (context_endpoint h t) c a =
    (fst a + count_difference h s t c, snd a)"
  by (simp add: affine_up_def count_difference_def)

context signature_path_structure
begin

abbreviation count_fiber where "count_fiber \<equiv> affine_fiber (\<lambda>x. int (point_count x))"
abbreviation count_up where "count_up \<equiv> affine_up (\<lambda>x. int (point_count x)) paths.cs paths.ct"
abbreviation count_down where "count_down \<equiv> affine_up (\<lambda>x. int (point_count x)) paths.ct paths.cs"

interpretation affine: affine_graph paths.admitted paths.cs paths.ct "\<lambda>x. int (point_count x)" .

lemma count_naturality:
  assumes K: "k < length (lcons (S h))" and A: "paths.argument_motion (lcons (S h) ! k) xs ps ys"
    and V: "valid_shell S h P C"
  shows "affine.family.transport
    (lift_path C (endpoint_motion h xs ys ps (fst (lends (S h) ! k)) @ [Pos (Generator (k,ys))])) a =
    affine.family.transport
    (lift_path C ([Pos (Generator (k,xs))] @ endpoint_motion h xs ys ps (snd (lends (S h) ! k)))) a"
  using naturality_relation_typed[OF naturality_relation.square[OF K A V]]
  by (blast intro: affine.parallel_transport)

sublocale count_model: coherent_signature_family S h P count_fiber count_up count_down
  by unfold_locales
    (auto intro: signature external_points source_tree target_tree affine.family.up_type
      affine.family.down_type affine.family.down_up affine.family.up_down count_naturality[simplified]
      simp: fun_eq_iff count_affine_up algebra_simps)

end

section \<open>A recursive generator naturality square with arbitrary residual values\<close>

interpretation affine_collapse: signature_path_structure collapse_signature 0 "\<lambda>_. {}"
  by unfold_locales
    (rule collapse_signature_wf, auto simp: collapse_signature_def external_arity_def less_Suc_eq)

lemma affine_numeral_tree:
  "parameter_tree collapse_signature 0 (\<lambda>_. {}) (numeral_tree n)"
  by (rule recursive_tree_embedding[OF numeral_point_tree])

lemma affine_collapse_argument_move:
  "affine_collapse.paths.argument_motion [Rec] [numeral_tree 2]
    [[Pos (Generator (0,[numeral_tree 1]))]] [numeral_tree 1]"
proof -
  have K: "0 < length (lcons (collapse_signature 0))" by (simp add: collapse_signature_def)
  have A: "parameter_arguments collapse_signature 0 (\<lambda>_. {}) (lcons (collapse_signature 0) ! 0) [numeral_tree 1]"
    using affine_numeral_tree[of 1]
    by (simp add: parameter_arguments_def collapse_signature_def external_arity_def parameter_carrier_def less_Suc_eq)
  have W: "walk_on affine_collapse.paths.admitted affine_collapse.paths.cs affine_collapse.paths.ct
    (numeral_tree 2) [Pos (Generator (0,[numeral_tree 1]))] (numeral_tree 1)"
    using affine_collapse.canonical_generator_typed[OF K A]
    by (simp add: lhsOf_def rhsOf_def collapse_signature_def numeral_tree.simps numeral_eq_Suc)
  show ?thesis using W affine_numeral_tree[of 1] affine_numeral_tree[of 2]
    unfolding affine_collapse.paths.argument_motion_def affine_collapse.paths.typed_motion_def
    by (simp add: external_arity_def parameter_carrier_def less_Suc_eq)
qed

lemma recursive_generator_naturality_cell:
  "affine_collapse.coherence_relation (numeral_tree 3)
    [Pos (Under 1 [] (Generator (0,[numeral_tree 1])) []), Pos (Generator (0,[numeral_tree 1]))]
    [Pos (Generator (0,[numeral_tree 2])), Pos (Generator (0,[numeral_tree 1]))]
    (numeral_tree 1)"
proof -
  have K: "0 < length (lcons (collapse_signature 0))" by (simp add: collapse_signature_def)
  have A: "affine_collapse.paths.argument_motion (lcons (collapse_signature 0) ! 0)
    [numeral_tree 2] [[Pos (Generator (0,[numeral_tree 1]))]] [numeral_tree 1]"
    using affine_collapse_argument_move by (simp add: collapse_signature_def)
  have V: "valid_shell collapse_signature 0 (\<lambda>_. {}) (Generator ())" by (rule valid_shell.hole)
  note N = affine_collapse.naturality_relation.square[OF K A V]
  show ?thesis using N
    unfolding affine_collapse.coherence_relation_def
    by (simp add: collapse_signature_def lhsOf_def rhsOf_def numeral_tree.simps numeral_eq_Suc)
qed

lemma recursive_generator_naturality_presented:
  "presented_eq affine_collapse.paths.admitted affine_collapse.paths.cs affine_collapse.paths.ct
    affine_collapse.coherence_relation (numeral_tree 3)
    [Pos (Under 1 [] (Generator (0,[numeral_tree 1])) []), Pos (Generator (0,[numeral_tree 1]))]
    [Pos (Generator (0,[numeral_tree 2])), Pos (Generator (0,[numeral_tree 1]))]
    (numeral_tree 1)"
  by (rule presented_eq.generator)
    (rule recursive_generator_naturality_cell,
      use affine_collapse.coherence_relation_typed[OF recursive_generator_naturality_cell] in auto)


lemma recursive_naturality_all_residuals:
  "graph_family_on.transport affine_collapse.count_up affine_collapse.count_down
    [Pos (Under 1 [] (Generator (0,[numeral_tree 1])) []), Pos (Generator (0,[numeral_tree 1]))]
    (4,z) = (2,z)"
  by (simp only: affine_collapse.count_model.fibers.transport.simps
      affine_collapse.count_model.fibers.step_transport.simps;
    simp add: affine_up_def lhsOf_def rhsOf_def collapse_signature_def numeral_tree.simps numeral_eq_Suc)

end
