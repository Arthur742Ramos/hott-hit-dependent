theory DHIT_Displayed_Algebra
  imports DHIT_Syntax_Bridge
begin

section \<open>Constructing a dependent eliminator from point methods\<close>

text \<open>This theory treats the constructor-generated recursive-only fragment
of the original syntax. Point trees contain no variables, applications, old
eliminators, or path terms. Every constructor argument is recursive. The
semantic motive may depend on the entire point tree.\<close>

primrec point_fold :: "(nat \<Rightarrow> tm list \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm \<Rightarrow> 'a" where
  "point_fold M (Var i) = undefined"
| "point_fold M (Lam A u) = undefined"
| "point_fold M (App u v) = undefined"
| "point_fold M (PCon h k xs) = M k xs (map (point_fold M) xs)"
| "point_fold M (LCon h k xs d) = undefined"
| "point_fold M (HElim h C ps ls u) = undefined"

inductive point_tree :: "sigenv \<Rightarrow> nat \<Rightarrow> tm \<Rightarrow> bool" for S h where
  node: "k < length (pcons (S h)) \<Longrightarrow>
    length xs = length (pcons (S h) ! k) \<Longrightarrow>
    (\<forall>r \<in> set (pcons (S h) ! k). r = Rec) \<Longrightarrow>
    (\<forall>x \<in> set xs. point_tree S h x) \<Longrightarrow>
    point_tree S h (PCon h k xs)"

lemma point_tree_typed:
  "point_tree S h u \<Longrightarrow> wt S D G u (Hit h)"
proof (induct rule: point_tree.induct)
  case (node k xs)
  show ?case
  proof (rule wt.wtPCon)
    show "k < length (pcons (S h))" by (rule node(1))
    show "length xs = length (pcons (S h) ! k)" by (rule node(2))
    show "\<forall>i < length xs. wt S D G (xs ! i) (argTy h (pcons (S h) ! k ! i))"
    proof (intro allI impI)
      fix i assume i: "i < length xs"
      have R: "pcons (S h) ! k ! i = Rec" using node(2,3) i by auto
      have "wt S D G (xs ! i) (Hit h)" using node(4) i by auto
      then show "wt S D G (xs ! i) (argTy h (pcons (S h) ! k ! i))"
        by (simp add: R)
    qed
  qed
qed

locale displayed_point_algebra =
  fixes S :: sigenv and h :: nat
    and F :: "tm \<Rightarrow> 'a set"
    and M :: "nat \<Rightarrow> tm list \<Rightarrow> 'a list \<Rightarrow> 'a"
  assumes method_type:
    "k < length (pcons (S h)) \<Longrightarrow>
     length xs = length (pcons (S h) ! k) \<Longrightarrow>
     (\<forall>r \<in> set (pcons (S h) ! k). r = Rec) \<Longrightarrow>
     (\<forall>x \<in> set xs. point_tree S h x) \<Longrightarrow>
     list_all2 (\<lambda>x a. a \<in> F x) xs ys \<Longrightarrow>
     M k xs ys \<in> F (PCon h k xs)"
begin

lemma constructed_section_type:
  "point_tree S h u \<Longrightarrow> point_fold M u \<in> F u"
proof (induct rule: point_tree.induct)
  case (node k xs)
  have "list_all2 (\<lambda>x a. a \<in> F x) xs (map (point_fold M) xs)"
    using node by (simp add: list_all2_conv_all_nth)
  then show ?case using node
    by (simp only: point_fold.simps; intro method_type; auto)
qed

lemma point_computation:
  "point_fold M (PCon h k xs) = M k xs (map (point_fold M) xs)"
  by simp

lemma constructed_section_unique:
  assumes computes: "\<And>k xs. point_tree S h (PCon h k xs) \<Longrightarrow>
    f (PCon h k xs) = M k xs (map f xs)"
    and tree: "point_tree S h u"
  shows "f u = point_fold M u"
  using tree
proof (induct rule: point_tree.induct)
  case (node k xs)
  have tree: "point_tree S h (PCon h k xs)"
    by (rule point_tree.node) (use node in auto)
  have "map f xs = map (point_fold M) xs" using node by simp
  with computes[OF tree] show ?case by simp
qed

end

section \<open>Dependent interpretation of original endpoint expressions\<close>

primrec displayed_endpoint ::
  "nat \<Rightarrow> (nat \<Rightarrow> tm list \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow>
    tm list \<Rightarrow> 'a list \<Rightarrow> endpt \<Rightarrow> 'a" where
  "displayed_endpoint h M xs ys (EArg i) = ys ! i"
| "displayed_endpoint h M xs ys (ECon k es) =
    M k (map (instE h xs) es) (map (displayed_endpoint h M xs ys) es)"

lemma point_fold_endpoint:
  assumes endpoint: "wf_endpt S h ss e A" and len: "length xs = length ss"
  shows "point_fold M (instE h xs e) =
    displayed_endpoint h M xs (map (point_fold M) xs) e"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case using len by simp
next
  case (wfECon k es)
  have "map (point_fold M \<circ> instE h xs) es =
      map (displayed_endpoint h M xs (map (point_fold M) xs)) es"
    using wfECon by (intro nth_equalityI) auto
  then show ?case by (simp only: instE.simps point_fold.simps displayed_endpoint.simps map_map)
qed

lemma endpoint_point_tree:
  assumes endpoint: "wf_endpt S h ss e A"
    and recursive: "\<And>k. k < length (pcons (S h)) \<Longrightarrow>
      \<forall>r \<in> set (pcons (S h) ! k). r = Rec"
    and len: "length xs = length ss"
    and trees: "\<forall>x \<in> set xs. point_tree S h x"
  shows "point_tree S h (instE h xs e)"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case using len trees by simp
next
  case (wfECon k es)
  show ?case
    by (simp only: instE.simps; rule point_tree.node)
      (use wfECon recursive in \<open>auto simp: in_set_conv_nth\<close>)
qed

context displayed_point_algebra
begin

lemma displayed_endpoint_type_general:
  assumes endpoint: "wf_endpt S h ss e A"
    and recursive: "\<And>k. k < length (pcons (S h)) \<Longrightarrow>
      \<forall>r \<in> set (pcons (S h) ! k). r = Rec"
    and len: "length xs = length ss"
    and trees: "\<forall>x \<in> set xs. point_tree S h x"
    and lifts: "list_all2 (\<lambda>x a. a \<in> F x) xs ys"
  shows "displayed_endpoint h M xs ys e \<in> F (instE h xs e)"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case using len lifts by (simp add: list_all2_conv_all_nth)
next
  case (wfECon k es)
  have subtrees: "\<forall>x \<in> set (map (instE h xs) es). point_tree S h x"
  proof (intro ballI)
    fix x assume "x \<in> set (map (instE h xs) es)"
    then obtain i where I: "i < length es" and X: "x = instE h xs (es ! i)"
      by (auto simp: in_set_conv_nth)
    have W: "wf_endpt S h ss (es ! i) (argTy h (pcons (S h) ! k ! i))"
      using wfECon I by simp
    show "point_tree S h x" unfolding X
      by (rule endpoint_point_tree[OF W recursive len trees])
  qed
  have sublifts: "list_all2 (\<lambda>x a. a \<in> F x)
      (map (instE h xs) es) (map (displayed_endpoint h M xs ys) es)"
    using wfECon by (simp add: list_all2_conv_all_nth)
  have "M k (map (instE h xs) es) (map (displayed_endpoint h M xs ys) es)
      \<in> F (PCon h k (map (instE h xs) es))"
    by (rule method_type[OF wfECon(1) _ recursive[OF wfECon(1)] subtrees sublifts])
      (use wfECon in simp)
  then show ?case by simp
qed

lemma displayed_endpoint_type:
  assumes "wf_endpt S h ss e A"
    "\<And>k. k < length (pcons (S h)) \<Longrightarrow>
      \<forall>r \<in> set (pcons (S h) ! k). r = Rec"
    "length xs = length ss" "\<forall>x \<in> set xs. point_tree S h x"
  shows "displayed_endpoint h M xs (map (point_fold M) xs) e \<in> F (instE h xs e)"
  using constructed_section_type[OF endpoint_point_tree[OF assms]]
    point_fold_endpoint[OF assms(1,3), of M] by simp

end

section \<open>Path coherence of the recursively constructed eliminator\<close>

locale displayed_hit_algebra = displayed_point_algebra S h F M +
  graph_family "\<lambda>e. lhsOf S h (constructor e) (arguments e)"
    "\<lambda>e. rhsOf S h (constructor e) (arguments e)" F up down
  for S :: sigenv and h :: nat and F :: "tm \<Rightarrow> 'a set"
    and M :: "nat \<Rightarrow> tm list \<Rightarrow> 'a list \<Rightarrow> 'a"
    and constructor :: "'e \<Rightarrow> nat" and arguments :: "'e \<Rightarrow> tm list"
    and up down :: "'e \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes signature: "wf_hsig S h"
    and recursive_points: "k < length (pcons (S h)) \<Longrightarrow>
      \<forall>r \<in> set (pcons (S h) ! k). r = Rec"
    and edge_bound: "constructor e < length (lcons (S h))"
    and recursive_edges: "\<forall>r \<in> set (lcons (S h) ! constructor e). r = Rec"
    and edge_length: "length (arguments e) = length (lcons (S h) ! constructor e)"
    and edge_trees: "\<forall>x \<in> set (arguments e). point_tree S h x"
    and displayed_boundary:
      "list_all2 (\<lambda>x a. a \<in> F x) (arguments e) ys \<Longrightarrow>
       up e (displayed_endpoint h M (arguments e) ys
        (fst (lends (S h) ! constructor e))) =
       displayed_endpoint h M (arguments e) ys
        (snd (lends (S h) ! constructor e))"
begin

abbreviation src where "src e \<equiv> lhsOf S h (constructor e) (arguments e)"
abbreviation dst where "dst e \<equiv> rhsOf S h (constructor e) (arguments e)"

lemma source_tree: "point_tree S h (src e)"
  unfolding lhsOf_def
  by (rule endpoint_point_tree[OF wf_hsig_lhs[OF signature edge_bound]
        recursive_points edge_length edge_trees])

lemma target_tree: "point_tree S h (dst e)"
  unfolding rhsOf_def
  by (rule endpoint_point_tree[OF wf_hsig_rhs[OF signature edge_bound]
        recursive_points edge_length edge_trees])

lemma selected_path_typed:
  assumes "j \<in> D"
  shows "wt S D G (LCon h (constructor e) (arguments e) (DVar j)) (Hit h)"
proof (rule wt.wtLCon)
  show "j \<in> D" by (rule assms)
  show "constructor e < length (lcons (S h))" by (rule edge_bound)
  show "length (arguments e) = length (lcons (S h) ! constructor e)"
    by (rule edge_length)
  show "\<forall>i < length (arguments e). wt S D G (arguments e ! i)
      (argTy h (lcons (S h) ! constructor e ! i))"
  proof (intro allI impI)
    fix i assume i: "i < length (arguments e)"
    have R: "lcons (S h) ! constructor e ! i = Rec"
      using recursive_edges[of e] edge_length[of e] i by auto
    have T: "point_tree S h (arguments e ! i)" using edge_trees[of e] i by auto
    show "wt S D G (arguments e ! i) (argTy h (lcons (S h) ! constructor e ! i))"
      using point_tree_typed[OF T] by (simp add: R)
  qed
qed

lemma original_typed_graph: "typed_hit_graph S D G h constructor arguments"
proof
  show "wf_hsig S h" by (rule signature)
  show "\<And>e. constructor e < length (lcons (S h))" by (rule edge_bound)
  show "\<And>e. length (arguments e) = length (lcons (S h) ! constructor e)"
    by (rule edge_length)
  fix e i assume i: "i < length (arguments e)"
  have R: "lcons (S h) ! constructor e ! i = Rec"
    using recursive_edges[of e] edge_length[of e] i by auto
  have T: "point_tree S h (arguments e ! i)" using edge_trees[of e] i by auto
  show "wt S D G (arguments e ! i) (argTy h (lcons (S h) ! constructor e ! i))"
    using point_tree_typed[OF T] by (simp add: R)
qed

lemma displayed_source_type:
  assumes "list_all2 (\<lambda>x a. a \<in> F x) (arguments e) ys"
  shows "displayed_endpoint h M (arguments e) ys (fst (lends (S h) ! constructor e))
    \<in> F (src e)"
  unfolding lhsOf_def
  by (rule displayed_endpoint_type_general[OF wf_hsig_lhs[OF signature edge_bound]
      recursive_points edge_length edge_trees assms])

lemma displayed_target_type:
  assumes "list_all2 (\<lambda>x a. a \<in> F x) (arguments e) ys"
  shows "displayed_endpoint h M (arguments e) ys (snd (lends (S h) ! constructor e))
    \<in> F (dst e)"
  unfolding rhsOf_def
  by (rule displayed_endpoint_type_general[OF wf_hsig_rhs[OF signature edge_bound]
      recursive_points edge_length edge_trees assms])

lemma constructed_generator_boundary:
  "up e (point_fold M (src e)) = point_fold M (dst e)"
proof -
  have IHs: "list_all2 (\<lambda>x a. a \<in> F x) (arguments e)
      (map (point_fold M) (arguments e))"
    using edge_trees[of e] constructed_section_type
    by (auto simp: list_all2_conv_all_nth)
  show ?thesis
    using displayed_boundary[OF IHs]
      point_fold_endpoint[OF wf_hsig_lhs[OF signature edge_bound] edge_length, of M]
      point_fold_endpoint[OF wf_hsig_rhs[OF signature edge_bound] edge_length, of M]
    by (simp add: lhsOf_def rhsOf_def)
qed

lemma constructed_step_boundary:
  "step_transport d (point_fold M (source src dst d)) =
    point_fold M (target src dst d)"
proof (cases d)
  case (Pos e)
  then show ?thesis by (simp add: constructed_generator_boundary)
next
  case (Neg e)
  have "down e (up e (point_fold M (src e))) = point_fold M (src e)"
    by (rule down_up[OF constructed_section_type[OF source_tree]])
  then show ?thesis by (simp add: Neg constructed_generator_boundary)
qed

lemma constructed_path_boundary:
  "walk src dst x p y \<Longrightarrow>
    transport p (point_fold M x) = point_fold M y"
  by (induct rule: walk.induct) (simp_all add: constructed_step_boundary)

lemma constructed_dependent_eliminator:
  assumes tree: "point_tree S h x" and path: "walk src dst x p y"
  shows "transport p (point_fold M x) = point_fold M y \<and> point_fold M y \<in> F y"
  using constructed_path_boundary[OF path]
    transport_type[OF path constructed_section_type[OF tree]] by simp

lemma constructed_equality_descent:
  assumes "path_equal src dst x p q y" "point_tree S h x"
  shows "transport p (point_fold M x) = transport q (point_fold M x)"
  by (rule transport_equal[OF assms(1) constructed_section_type[OF assms(2)]])

end

section \<open>A recursive HIT with a genuinely varying motive\<close>

primrec point_count :: "tm \<Rightarrow> nat" where
  "point_count (Var i) = 0"
| "point_count (Lam A u) = 0"
| "point_count (App u v) = 0"
| "point_count (PCon h k xs) = Suc (sum_list (map point_count xs))"
| "point_count (LCon h k xs d) = 0"
| "point_count (HElim h C ps ls u) = 0"

lemma point_count_algebra:
  "displayed_point_algebra S h (\<lambda>u. {point_count u}) (\<lambda>k xs ys. Suc (sum_list ys))"
proof
  fix k xs ys
  assume "k < length (pcons (S h))" "length xs = length (pcons (S h) ! k)"
    "\<forall>r\<in>set (pcons (S h) ! k). r = Rec" "\<forall>x\<in>set xs. point_tree S h x"
    and IH: "list_all2 (\<lambda>x a. a \<in> {point_count x}) xs ys"
  have "ys = map point_count xs"
    using IH by (auto simp: list_all2_conv_all_nth intro!: nth_equalityI)
  then show "Suc (sum_list ys) \<in> {point_count (PCon h k xs)}" by simp
qed

definition collapse_signature :: sigenv where
  "collapse_signature = (\<lambda>h. \<lparr>pcons = [[], [Rec]], lcons = [[Rec]],
    lends = [(ECon 1 [EArg 0], EArg 0)]\<rparr>)"

lemma recursive_argument_endpoint: "wf_endpt S h [Rec] (EArg 0) (Hit h)"
  using wf_endpt.wfEArg[where S=S and h=h and ss="[Rec]" and i=0] by simp

lemma collapse_signature_wf: "wf_hsig collapse_signature 0"
  by (auto simp: wf_hsig_def collapse_signature_def intro!: wf_endpt.wfECon recursive_argument_endpoint)

primrec numeral_tree :: "nat \<Rightarrow> tm" where
  "numeral_tree 0 = PCon 0 0 []"
| "numeral_tree (Suc n) = PCon 0 1 [numeral_tree n]"

lemma numeral_point_tree: "point_tree collapse_signature 0 (numeral_tree n)"
  by (induct n) (auto intro: point_tree.node simp: collapse_signature_def)

lemma count_numeral [simp]: "point_count (numeral_tree n) = Suc n"
  by (induct n) simp_all

lemma recursive_hit_computation:
  "point_fold (\<lambda>k xs ys. Suc (sum_list ys)) (numeral_tree n) = Suc n"
  by (induct n) simp_all


text \<open>The signature has zero, successor, and a recursive path constructor
from successor of an argument to that argument. The motive is the singleton
containing the raw point-tree node count. Its fibers at adjacent numerals are
different, and transport maps between them. This is a semantic dependent
elimination example, not an assertion that node count is constant along a path.\<close>

interpretation collapse: displayed_hit_algebra collapse_signature 0
  "\<lambda>u. {point_count u}" "\<lambda>k xs ys. Suc (sum_list ys)"
  "\<lambda>n::nat. 0" "\<lambda>n. [numeral_tree n]"
  "\<lambda>_ n. n - 1" "\<lambda>_. Suc"
  by (unfold_locales,
      (rule displayed_point_algebra.method_type[OF point_count_algebra]; assumption),
      insert collapse_signature_wf numeral_point_tree,
      auto simp: lhsOf_def rhsOf_def collapse_signature_def
        recursive_hit_computation less_Suc_eq)

lemma recursive_hit_path_computation:
  "collapse.transport [Pos n]
    (point_fold (\<lambda>k xs ys. Suc (sum_list ys)) (numeral_tree (Suc n))) = Suc n"
  by (simp only: recursive_hit_computation collapse.transport.simps collapse.step_transport.simps; simp)

end
