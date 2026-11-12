theory DHIT_Parameter_Algebra
  imports DHIT_Displayed_Algebra
begin

section \<open>External parameters and recursive induction hypotheses\<close>

text \<open>This extension uses the original Par/Rec arities. A parameter of
sort j is supplied as an opaque term in P j, whereas a recursive argument is
a constructor tree. Parameter sorts must differ from the HIT being defined:
an opaque Par h would require a separately supplied dependent section.
The section is constructed on point trees, not on every old well-typed term.
Its path coherence concerns the free path closure of the chosen constructor
instances; point-constructor congruence and the old computational equality
are not identified with these paths. Old typing of opaque parameters is an
explicit premise of the original-typing bridge.\<close>

definition external_arity :: "nat \<Rightarrow> argspec list \<Rightarrow> bool" where
  "external_arity h ss \<longleftrightarrow> (\<forall>j. Par j \<in> set ss \<longrightarrow> j \<noteq> h)"

inductive parameter_tree :: "sigenv \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tm set) \<Rightarrow> tm \<Rightarrow> bool"
  for S h P where
  node: "k < length (pcons (S h)) \<Longrightarrow>
    length xs = length (pcons (S h) ! k) \<Longrightarrow>
    external_arity h (pcons (S h) ! k) \<Longrightarrow>
    (\<forall>i < length xs. pcons (S h) ! k ! i = Rec \<longrightarrow> parameter_tree S h P (xs ! i)) \<Longrightarrow>
    (\<forall>i j. i < length xs \<longrightarrow> pcons (S h) ! k ! i = Par j \<longrightarrow> xs ! i \<in> P j) \<Longrightarrow>
    parameter_tree S h P (PCon h k xs)"

definition ih_mask :: "argspec list \<Rightarrow> 'a list \<Rightarrow> 'a option list" where
  "ih_mask ss ys = map2 (\<lambda>r y. if r = Rec then Some y else None) ss ys"

lemma ih_mask_length [simp]:
  "length ss = length ys \<Longrightarrow> length (ih_mask ss ys) = length ss"
  by (simp add: ih_mask_def)

lemma ih_mask_nth [simp]:
  "i < length ss \<Longrightarrow> i < length ys \<Longrightarrow>
    ih_mask ss ys ! i = (if ss ! i = Rec then Some (ys ! i) else None)"
  by (simp add: ih_mask_def)

primrec parameter_fold ::
  "sigenv \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tm list \<Rightarrow> 'a option list \<Rightarrow> 'a) \<Rightarrow> tm \<Rightarrow> 'a" where
  "parameter_fold S h M (Var i) = undefined"
| "parameter_fold S h M (Lam A u) = undefined"
| "parameter_fold S h M (App u v) = undefined"
| "parameter_fold S h M (PCon H k xs) =
    M k xs (ih_mask (pcons (S h) ! k) (map (parameter_fold S h M) xs))"
| "parameter_fold S h M (LCon H k xs d) = undefined"
| "parameter_fold S h M (HElim H C ps ls u) = undefined"

definition displayed_arguments ::
  "(tm \<Rightarrow> 'a set) \<Rightarrow> argspec list \<Rightarrow> tm list \<Rightarrow> 'a option list \<Rightarrow> bool" where
  "displayed_arguments F ss xs ys \<longleftrightarrow> length ys = length xs \<and>
    (\<forall>i < length xs. case ss ! i of
      Par j \<Rightarrow> ys ! i = None
    | Rec \<Rightarrow> (\<exists>a. ys ! i = Some a \<and> a \<in> F (xs ! i)))"

lemma parameter_tree_typed:
  assumes tree: "parameter_tree S h P u"
    and parameters: "\<And>j u. u \<in> P j \<Longrightarrow> wt S D G u (Hit j)"
  shows "wt S D G u (Hit h)"
  using tree
proof (induct rule: parameter_tree.induct)
  case (node k xs)
  show ?case
  proof (rule wt.wtPCon)
    show "k < length (pcons (S h))" by fact
    show "length xs = length (pcons (S h) ! k)" by fact
    show "\<forall>i<length xs. wt S D G (xs ! i) (argTy h (pcons (S h) ! k ! i))"
    proof (intro allI impI)
      fix i
      assume "i < length xs"
      with node parameters show "wt S D G (xs ! i) (argTy h (pcons (S h) ! k ! i))"
        by (cases "pcons (S h) ! k ! i") auto
    qed
  qed
qed

locale parameter_displayed_algebra =
  fixes S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set"
    and F :: "tm \<Rightarrow> 'a set"
    and M :: "nat \<Rightarrow> tm list \<Rightarrow> 'a option list \<Rightarrow> 'a"
  assumes method_type:
    "parameter_tree S h P (PCon h k xs) \<Longrightarrow>
     displayed_arguments F (pcons (S h) ! k) xs ys \<Longrightarrow>
     M k xs ys \<in> F (PCon h k xs)"
begin

lemma constructed_section_type:
  "parameter_tree S h P u \<Longrightarrow> parameter_fold S h M u \<in> F u"
proof (induct rule: parameter_tree.induct)
  case (node k xs)
  have tree: "parameter_tree S h P (PCon h k xs)"
    by (rule parameter_tree.node) (use node in auto)
  have lifted: "displayed_arguments F (pcons (S h) ! k) xs
    (ih_mask (pcons (S h) ! k) (map (parameter_fold S h M) xs))"
    using node by (auto simp: displayed_arguments_def split: argspec.splits)
  show ?case using method_type[OF tree lifted] by simp
qed

lemma point_computation:
  "parameter_fold S h M (PCon h k xs) =
   M k xs (ih_mask (pcons (S h) ! k) (map (parameter_fold S h M) xs))"
  by simp

lemma constructed_section_unique:
  assumes computes: "\<And>k xs. parameter_tree S h P (PCon h k xs) \<Longrightarrow>
    f (PCon h k xs) = M k xs (ih_mask (pcons (S h) ! k) (map f xs))"
    and tree: "parameter_tree S h P u"
  shows "f u = parameter_fold S h M u"
  using tree
proof (induct rule: parameter_tree.induct)
  case (node k xs)
  have tree: "parameter_tree S h P (PCon h k xs)"
    by (rule parameter_tree.node) (use node in auto)
  have masks: "ih_mask (pcons (S h) ! k) (map f xs) =
      ih_mask (pcons (S h) ! k) (map (parameter_fold S h M) xs)"
    by (rule nth_equalityI) (use node in auto)
  show ?case using computes[OF tree] masks by simp
qed

end

section \<open>Compatibility with the recursive-only construction\<close>

lemma recursive_tree_embedding:
  "point_tree S h u \<Longrightarrow> parameter_tree S h P u"
proof (induct rule: point_tree.induct)
  case (node k xs)
  have R: "\<forall>i < length xs. pcons (S h) ! k ! i = Rec"
    using node(2,3) by (metis nth_mem)
  have T: "\<forall>i < length xs. parameter_tree S h P (xs ! i)"
    using node by (metis nth_mem)
  have E: "external_arity h (pcons (S h) ! k)"
    using node(3) by (auto simp: external_arity_def)
  have Q: "\<forall>i j. i < length xs \<longrightarrow> pcons (S h) ! k ! i = Par j \<longrightarrow> xs ! i \<in> P j"
    using R by (metis argspec.distinct(1))
  show ?case
  proof (rule parameter_tree.node)
    show "k < length (pcons (S h))" by fact
    show "length xs = length (pcons (S h) ! k)" by fact
    show "external_arity h (pcons (S h) ! k)" by (rule E)
    show "\<forall>i < length xs. pcons (S h) ! k ! i = Rec \<longrightarrow> parameter_tree S h P (xs ! i)"
      using T by blast
    show "\<forall>i j. i < length xs \<longrightarrow> pcons (S h) ! k ! i = Par j \<longrightarrow> xs ! i \<in> P j"
      by (rule Q)
  qed
qed

lemma ih_mask_all_recursive:
  assumes "\<forall>r \<in> set ss. r = Rec" "length ss = length ys"
  shows "ih_mask ss ys = map Some ys"
  by (rule nth_equalityI) (use assms in \<open>auto dest: nth_mem\<close>)

lemma recursive_fold_agreement:
  "point_tree S h u \<Longrightarrow>
    parameter_fold S h (\<lambda>k xs ys. M k xs (map the ys)) u = point_fold M u"
proof (induct rule: point_tree.induct)
  case (node k xs)
  have mask: "ih_mask (pcons (S h) ! k)
      (map (parameter_fold S h (\<lambda>k xs ys. M k xs (map the ys))) xs) =
      map Some (map (parameter_fold S h (\<lambda>k xs ys. M k xs (map the ys))) xs)"
    by (rule ih_mask_all_recursive) (use node in auto)
  have eq: "map (parameter_fold S h (\<lambda>k xs ys. M k xs (map the ys))) xs = map (point_fold M) xs"
    using node by simp
  show ?case by (simp only: parameter_fold.simps mask map_map comp_def option.sel; simp add: eq)
qed

section \<open>Dependent endpoints with mixed arguments\<close>

lemma external_argTy:
  assumes "external_arity h ss" "r \<in> set ss"
  shows "(argTy h r = Hit h) = (r = Rec)"
  using assms by (cases r) (auto simp: external_arity_def)

primrec parameter_endpoint ::
  "nat \<Rightarrow> (nat \<Rightarrow> tm list \<Rightarrow> 'a option list \<Rightarrow> 'a) \<Rightarrow>
    tm list \<Rightarrow> 'a option list \<Rightarrow> endpt \<Rightarrow> 'a option" where
  "parameter_endpoint h M xs ys (EArg i) = ys ! i"
| "parameter_endpoint h M xs ys (ECon k es) =
    Some (M k (map (instE h xs) es) (map (parameter_endpoint h M xs ys) es))"

lemma parameter_fold_endpoint:
  assumes endpoint: "wf_endpt S h ss e A"
    and len: "length xs = length ss"
    and ext: "external_arity h ss"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "parameter_endpoint h M xs (ih_mask ss (map (parameter_fold S h M) xs)) e =
    (if A = Hit h then Some (parameter_fold S h M (instE h xs e)) else None)"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  have E: "(argTy h (ss ! i) = Hit h) = (ss ! i = Rec)"
    by (rule external_argTy[OF ext]) (use wfEArg in auto)
  show ?case using wfEArg len by (simp add: E)
next
  case (wfECon k es)
  have masks: "map (parameter_endpoint h M xs (ih_mask ss (map (parameter_fold S h M) xs))) es =
      ih_mask (pcons (S h) ! k) (map (parameter_fold S h M) (map (instE h xs) es))"
  proof (rule nth_equalityI)
    show "length (map (parameter_endpoint h M xs (ih_mask ss (map (parameter_fold S h M) xs))) es) =
      length (ih_mask (pcons (S h) ! k) (map (parameter_fold S h M) (map (instE h xs) es)))"
      using wfECon by simp
    fix i assume I: "i < length (map (parameter_endpoint h M xs (ih_mask ss (map (parameter_fold S h M) xs))) es)"
    have E: "(argTy h (pcons (S h) ! k ! i) = Hit h) = (pcons (S h) ! k ! i = Rec)"
      by (rule external_argTy[OF points[OF wfECon(1)]]) (use I wfECon in auto)
    show "map (parameter_endpoint h M xs (ih_mask ss (map (parameter_fold S h M) xs))) es ! i =
      ih_mask (pcons (S h) ! k) (map (parameter_fold S h M) (map (instE h xs) es)) ! i"
      using I wfECon by (simp add: E)
  qed
  show ?case by (simp add: masks)
qed

definition parameter_carrier :: "sigenv \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tm set) \<Rightarrow> ty \<Rightarrow> tm \<Rightarrow> bool" where
  "parameter_carrier S h P A u \<longleftrightarrow>
    (if A = Hit h then parameter_tree S h P u else (case A of Hit j \<Rightarrow> u \<in> P j | Fun B C \<Rightarrow> False))"

definition parameter_arguments :: "sigenv \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tm set) \<Rightarrow> argspec list \<Rightarrow> tm list \<Rightarrow> bool" where
  "parameter_arguments S h P ss xs \<longleftrightarrow> length xs = length ss \<and> external_arity h ss \<and>
    (\<forall>i < length xs. parameter_carrier S h P (argTy h (ss ! i)) (xs ! i))"

lemma endpoint_parameter_carrier:
  assumes endpoint: "wf_endpt S h ss e A"
    and args: "parameter_arguments S h P ss xs"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "parameter_carrier S h P A (instE h xs e)"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case using args by (simp add: parameter_arguments_def)
next
  case (wfECon k es)
  have tree: "parameter_tree S h P (PCon h k (map (instE h xs) es))"
  proof (rule parameter_tree.node)
    show "k < length (pcons (S h))" by fact
    show "length (map (instE h xs) es) = length (pcons (S h) ! k)" using wfECon by simp
    show "external_arity h (pcons (S h) ! k)" by (rule points[OF wfECon(1)])
    show "\<forall>i<length (map (instE h xs) es).
        pcons (S h) ! k ! i = Rec \<longrightarrow> parameter_tree S h P (map (instE h xs) es ! i)"
      using wfECon by (auto simp: parameter_carrier_def)
    show "\<forall>i j. i < length (map (instE h xs) es) \<longrightarrow>
        pcons (S h) ! k ! i = Par j \<longrightarrow> map (instE h xs) es ! i \<in> P j"
    proof (intro allI impI)
      fix i j
      assume I: "i < length (map (instE h xs) es)"
        and J: "pcons (S h) ! k ! i = Par j"
      have N: "j \<noteq> h"
        using points[OF wfECon(1)] I wfECon(2) J
        unfolding external_arity_def by (metis length_map nth_mem)
      have C: "parameter_carrier S h P (argTy h (pcons (S h) ! k ! i)) (instE h xs (es ! i))"
        using wfECon I by simp
      show "map (instE h xs) es ! i \<in> P j"
        using C I N by (simp add: J parameter_carrier_def)
    qed
  qed
  then show ?case by (simp add: parameter_carrier_def)
qed

definition endpoint_lift :: "(tm \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> tm \<Rightarrow> 'a option \<Rightarrow> bool" where
  "endpoint_lift F h A u z \<longleftrightarrow>
    (if A = Hit h then (\<exists>a \<in> F u. z = Some a) else z = None)"

context parameter_displayed_algebra
begin

lemma displayed_endpoint_arbitrary_type:
  assumes endpoint: "wf_endpt S h ss e A"
    and args: "parameter_arguments S h P ss xs"
    and lifts: "displayed_arguments F ss xs ys"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "endpoint_lift F h A (instE h xs e) (parameter_endpoint h M xs ys e)"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  have I: "i < length xs" using args wfEArg by (simp add: parameter_arguments_def)
  have E: "(argTy h (ss ! i) = Hit h) = (ss ! i = Rec)"
    by (rule external_argTy) (use args wfEArg in \<open>auto simp: parameter_arguments_def\<close>)
  have L: "case ss ! i of Par j \<Rightarrow> ys ! i = None
    | Rec \<Rightarrow> (\<exists>a. ys ! i = Some a \<and> a \<in> F (xs ! i))"
    using lifts I unfolding displayed_arguments_def by blast
  show ?case using L E
    by (cases "ss ! i") (auto simp: endpoint_lift_def)
next
  case (wfECon k es)
  have W: "wf_endpt S h ss (ECon k es) (Hit h)"
    by (rule wf_endpt.wfECon) (use wfECon in auto)
  have T: "parameter_tree S h P (PCon h k (map (instE h xs) es))"
    using endpoint_parameter_carrier[OF W args points]
    by (simp add: parameter_carrier_def)
  have L: "displayed_arguments F (pcons (S h) ! k) (map (instE h xs) es)
      (map (parameter_endpoint h M xs ys) es)"
  proof (unfold displayed_arguments_def, intro conjI)
    show "length (map (parameter_endpoint h M xs ys) es) = length (map (instE h xs) es)" by simp
    show "\<forall>i<length (map (instE h xs) es).
      case pcons (S h) ! k ! i of Par j \<Rightarrow> map (parameter_endpoint h M xs ys) es ! i = None
      | Rec \<Rightarrow> (\<exists>a. map (parameter_endpoint h M xs ys) es ! i = Some a \<and> a \<in> F (map (instE h xs) es ! i))"
    proof (intro allI impI)
      fix i assume I: "i < length (map (instE h xs) es)"
      have E: "(argTy h (pcons (S h) ! k ! i) = Hit h) = (pcons (S h) ! k ! i = Rec)"
        by (rule external_argTy[OF points[OF wfECon(1)]]) (use I wfECon in auto)
      have IH: "endpoint_lift F h (argTy h (pcons (S h) ! k ! i))
        (instE h xs (es ! i)) (parameter_endpoint h M xs ys (es ! i))"
        using wfECon I by simp
      show "case pcons (S h) ! k ! i of Par j \<Rightarrow> map (parameter_endpoint h M xs ys) es ! i = None
        | Rec \<Rightarrow> (\<exists>a. map (parameter_endpoint h M xs ys) es ! i = Some a \<and> a \<in> F (map (instE h xs) es ! i))"
        using IH E I by (cases "pcons (S h) ! k ! i") (auto simp: endpoint_lift_def)
    qed
  qed
  show ?case using method_type[OF T L] by (auto simp: endpoint_lift_def)
qed

lemma displayed_endpoint_type:
  assumes endpoint: "wf_endpt S h ss e (Hit h)"
    and args: "parameter_arguments S h P ss xs"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "\<exists>a \<in> F (instE h xs e).
    parameter_endpoint h M xs (ih_mask ss (map (parameter_fold S h M) xs)) e = Some a"
proof -
  have T: "parameter_tree S h P (instE h xs e)"
    using endpoint_parameter_carrier[OF endpoint args points] by (simp add: parameter_carrier_def)
  have E: "parameter_endpoint h M xs (ih_mask ss (map (parameter_fold S h M) xs)) e =
      Some (parameter_fold S h M (instE h xs e))"
    by (rule parameter_fold_endpoint[OF endpoint _ _ points, simplified])
      (use args in \<open>auto simp: parameter_arguments_def\<close>)
  show ?thesis using E constructed_section_type[OF T] by blast
qed

end

lemma parameter_arguments_typed:
  assumes args: "parameter_arguments S h P ss xs"
    and parameters: "\<And>j u. u \<in> P j \<Longrightarrow> wt S D G u (Hit j)"
    and I: "i < length xs"
  shows "wt S D G (xs ! i) (argTy h (ss ! i))"
proof (cases "ss ! i")
  case (Par j)
  have N: "j \<noteq> h"
    using args I Par unfolding parameter_arguments_def external_arity_def
    by (metis nth_mem)
  have C: "parameter_carrier S h P (argTy h (ss ! i)) (xs ! i)"
    using args I unfolding parameter_arguments_def by blast
  have "xs ! i \<in> P j"
    using C N by (simp add: parameter_carrier_def Par)
  then show ?thesis by (simp add: Par parameters)
next
  case Rec
  have C: "parameter_carrier S h P (argTy h (ss ! i)) (xs ! i)"
    using args I unfolding parameter_arguments_def by blast
  have "parameter_tree S h P (xs ! i)"
    using C by (simp add: parameter_carrier_def Rec)
  from parameter_tree_typed[OF this parameters] show ?thesis by (simp add: Rec)
qed

section \<open>Dependent induction for mixed constructor instances\<close>

locale parameter_hit_algebra = parameter_displayed_algebra S h P F M +
  graph_family "\<lambda>e. lhsOf S h (constructor e) (arguments e)"
    "\<lambda>e. rhsOf S h (constructor e) (arguments e)" F up down
  for S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set" and F :: "tm \<Rightarrow> 'a set"
    and M :: "nat \<Rightarrow> tm list \<Rightarrow> 'a option list \<Rightarrow> 'a"
    and constructor :: "'e \<Rightarrow> nat" and arguments :: "'e \<Rightarrow> tm list"
    and up down :: "'e \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes signature: "wf_hsig S h"
    and external_points: "k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
    and edge_bound: "constructor e < length (lcons (S h))"
    and edge_arguments: "parameter_arguments S h P (lcons (S h) ! constructor e) (arguments e)"
    and displayed_boundary:
      "displayed_arguments F (lcons (S h) ! constructor e) (arguments e) ys \<Longrightarrow>
       map_option (up e) (parameter_endpoint h M (arguments e) ys
        (fst (lends (S h) ! constructor e))) =
       parameter_endpoint h M (arguments e) ys
        (snd (lends (S h) ! constructor e))"
begin

abbreviation src where "src e \<equiv> lhsOf S h (constructor e) (arguments e)"
abbreviation dst where "dst e \<equiv> rhsOf S h (constructor e) (arguments e)"

lemma original_typed_graph:
  assumes parameters: "\<And>j u. u \<in> P j \<Longrightarrow> wt S D G u (Hit j)"
  shows "typed_hit_graph S D G h constructor arguments"
proof
  show "wf_hsig S h" by (rule signature)
  show "constructor e < length (lcons (S h))" for e by (rule edge_bound)
  show "length (arguments e) = length (lcons (S h) ! constructor e)" for e
    using edge_arguments[of e] by (simp add: parameter_arguments_def)
  show "i < length (arguments e) \<Longrightarrow>
    wt S D G (arguments e ! i) (argTy h (lcons (S h) ! constructor e ! i))" for e i
    by (rule parameter_arguments_typed[OF edge_arguments parameters])
qed

lemma source_tree: "parameter_tree S h P (src e)"
  using endpoint_parameter_carrier[OF wf_hsig_lhs[OF signature edge_bound] edge_arguments external_points]
  by (simp add: lhsOf_def parameter_carrier_def)

lemma target_tree: "parameter_tree S h P (dst e)"
  using endpoint_parameter_carrier[OF wf_hsig_rhs[OF signature edge_bound] edge_arguments external_points]
  by (simp add: rhsOf_def parameter_carrier_def)

lemma constructed_generator_boundary:
  "up e (parameter_fold S h M (src e)) = parameter_fold S h M (dst e)"
proof -
  have len: "length (arguments e) = length (lcons (S h) ! constructor e)"
    and ext: "external_arity h (lcons (S h) ! constructor e)"
    using edge_arguments[of e] by (auto simp: parameter_arguments_def)
  have lifts: "displayed_arguments F (lcons (S h) ! constructor e) (arguments e)
      (ih_mask (lcons (S h) ! constructor e) (map (parameter_fold S h M) (arguments e)))"
    using edge_arguments[of e] constructed_section_type
    by (auto simp: displayed_arguments_def parameter_arguments_def parameter_carrier_def
      split: argspec.splits)
  show ?thesis
    using displayed_boundary[OF lifts]
      parameter_fold_endpoint[OF wf_hsig_lhs[OF signature edge_bound] len ext external_points, of M]
      parameter_fold_endpoint[OF wf_hsig_rhs[OF signature edge_bound] len ext external_points, of M]
    by (simp add: lhsOf_def rhsOf_def)
qed

lemma constructed_step_boundary:
  "step_transport d (parameter_fold S h M (source src dst d)) =
    parameter_fold S h M (target src dst d)"
proof (cases d)
  case (Pos e)
  then show ?thesis by (simp add: constructed_generator_boundary)
next
  case (Neg e)
  have "down e (up e (parameter_fold S h M (src e))) = parameter_fold S h M (src e)"
    by (rule down_up[OF constructed_section_type[OF source_tree]])
  then show ?thesis by (simp add: Neg constructed_generator_boundary)
qed

lemma constructed_path_boundary:
  "walk src dst x p y \<Longrightarrow>
    transport p (parameter_fold S h M x) = parameter_fold S h M y"
  by (induct rule: walk.induct) (simp_all add: constructed_step_boundary)

theorem constructed_dependent_eliminator:
  assumes tree: "parameter_tree S h P x" and path: "walk src dst x p y"
  shows "transport p (parameter_fold S h M x) = parameter_fold S h M y \<and>
    parameter_fold S h M y \<in> F y"
  using constructed_path_boundary[OF path]
    transport_type[OF path constructed_section_type[OF tree]] by simp

lemma constructed_equality_descent:
  assumes "path_equal src dst x p q y" "parameter_tree S h P x"
  shows "transport p (parameter_fold S h M x) = transport q (parameter_fold S h M x)"
  by (rule transport_equal[OF assms(1) constructed_section_type[OF assms(2)]])

end

section \<open>A parameterized list HIT and a varying dependent motive\<close>

definition count_parameter_method ::
  "sigenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow> nat option list \<Rightarrow> nat" where
  "count_parameter_method S h k xs ys = Suc (sum_list
    (map (\<lambda>i. case pcons (S h) ! k ! i of
      Par j \<Rightarrow> point_count (xs ! i) | Rec \<Rightarrow> the (ys ! i)) [0..<length xs]))"

lemma count_parameter_algebra:
  "parameter_displayed_algebra S h P (\<lambda>u. {point_count u}) (count_parameter_method S h)"
proof
  fix k xs ys
  assume tree: "parameter_tree S h P (PCon h k xs)"
    and IH: "displayed_arguments (\<lambda>u. {point_count u}) (pcons (S h) ! k) xs ys"
  have counts: "map (\<lambda>i. case pcons (S h) ! k ! i of
      Par j \<Rightarrow> point_count (xs ! i) | Rec \<Rightarrow> the (ys ! i)) [0..<length xs] = map point_count xs"
    by (rule nth_equalityI)
      (use IH in \<open>auto simp: displayed_arguments_def split: argspec.splits\<close>)
  show "count_parameter_method S h k xs ys \<in> {point_count (PCon h k xs)}"
    by (simp add: count_parameter_method_def counts)
qed

lemma count_parameter_fold:
  "parameter_tree S h P u \<Longrightarrow> parameter_fold S h (count_parameter_method S h) u = point_count u"
  using parameter_displayed_algebra.constructed_section_type[OF count_parameter_algebra, where u=u and S=S and h=h and P=P] by simp

definition parameter_list_signature :: sigenv where
  "parameter_list_signature = (\<lambda>h. if h = 0 then
    \<lparr>pcons = [[], [Par 1, Rec]], lcons = [[Par 1, Rec]],
      lends = [(ECon 1 [EArg 0, EArg 1], EArg 1)]\<rparr>
    else \<lparr>pcons = [[]], lcons = [], lends = []\<rparr>)"

definition list_parameters :: "nat \<Rightarrow> tm set" where
  "list_parameters j = (if j = 1 then {PCon 1 0 []} else {})"

primrec parameter_list :: "nat \<Rightarrow> tm" where
  "parameter_list 0 = PCon 0 0 []"
| "parameter_list (Suc n) = PCon 0 1 [PCon 1 0 [], parameter_list n]"

lemma parameter_list_tree:
  "parameter_tree parameter_list_signature 0 list_parameters (parameter_list n)"
  by (induct n; simp only: parameter_list.simps; rule parameter_tree.node;
    auto simp: parameter_list_signature_def external_arity_def list_parameters_def less_Suc_eq)

lemma list_parameters_typed:
  "u \<in> list_parameters j \<Longrightarrow> wt parameter_list_signature D G u (Hit j)"
  by (auto simp: list_parameters_def parameter_list_signature_def split: if_splits intro!: wt.wtPCon)

lemma parameter_list_typed:
  "wt parameter_list_signature D G (parameter_list n) (Hit 0)"
  by (rule parameter_tree_typed[OF parameter_list_tree]) (rule list_parameters_typed)

lemma parameter_list_count [simp]: "point_count (parameter_list n) = 2 * n + 1"
  by (induct n) simp_all

lemma list_parameter_endpoint:
  "wf_endpt S h [Par j, Rec] (EArg 0) (Hit j)"
  using wf_endpt.wfEArg[where S=S and h=h and ss="[Par j, Rec]" and i=0] by simp

lemma list_recursive_endpoint:
  "wf_endpt S h [Par j, Rec] (EArg (Suc 0)) (Hit h)"
  using wf_endpt.wfEArg[where S=S and h=h and ss="[Par j, Rec]" and i="Suc 0"] by simp

lemma parameter_list_signature_wf: "wf_hsig parameter_list_signature 0"
  by (auto simp: wf_hsig_def parameter_list_signature_def less_Suc_eq
    intro!: wf_endpt.wfECon list_parameter_endpoint list_recursive_endpoint)

lemma displayed_pair_arguments:
  "displayed_arguments F [Par j, Rec] [a,x] ys \<longleftrightarrow>
    (\<exists>b \<in> F x. ys = [None, Some b])"
  by (auto simp: displayed_arguments_def length_Suc_conv less_Suc_eq; metis)

text \<open>The path constructor deletes one list cell and has both an external
parameter and a recursive argument. The motive records the complete raw tree's
node count, including opaque parameter terms. Its values change by two along
the displayed instances, so transport is not the identity.\<close>

interpretation parameter_list_hit: parameter_hit_algebra parameter_list_signature 0 list_parameters
  "\<lambda>u. {point_count u}" "count_parameter_method parameter_list_signature 0"
  "\<lambda>n::nat. 0" "\<lambda>n. [PCon 1 0 [], parameter_list n]"
  "\<lambda>_ n. n - 2" "\<lambda>_ n. n + 2"
  by (unfold_locales,
      (rule parameter_displayed_algebra.method_type[OF count_parameter_algebra]; assumption),
      insert parameter_list_signature_wf parameter_list_tree,
      auto simp: lhsOf_def rhsOf_def parameter_list_signature_def
        parameter_arguments_def external_arity_def parameter_carrier_def list_parameters_def
        displayed_pair_arguments count_parameter_method_def less_Suc_eq)

lemma parameter_list_original_graph:
  "typed_hit_graph parameter_list_signature D G 0
    (\<lambda>n::nat. 0) (\<lambda>n. [PCon 1 0 [], parameter_list n])"
  by (rule parameter_list_hit.original_typed_graph) (rule list_parameters_typed)

lemma parameterized_hit_path_computation:
  "parameter_list_hit.transport [Pos n]
    (parameter_fold parameter_list_signature 0 (count_parameter_method parameter_list_signature 0)
      (parameter_list (Suc n))) = 2 * n + 1"
  by (simp only: count_parameter_fold[OF parameter_list_tree] parameter_list_count
    parameter_list_hit.transport.simps parameter_list_hit.step_transport.simps; simp)

end
