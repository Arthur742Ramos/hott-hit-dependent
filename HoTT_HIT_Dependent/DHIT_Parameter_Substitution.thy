theory DHIT_Parameter_Substitution
  imports DHIT_Parameter_Algebra
begin

section \<open>Substitution in the recursively constructed dependent eliminator\<close>

text \<open>Opaque parameter terms may contain variables. Substitution changes
those terms and their permitted carrier sets. Recursive point trees retain
their constructor shape. The method is pulled back by applying the original
term substitution to its ordinary arguments, leaving the dependent induction
hypotheses unchanged.\<close>

definition substitute_method ::
  "nat \<Rightarrow> tm \<Rightarrow> (nat \<Rightarrow> tm list \<Rightarrow> 'a option list \<Rightarrow> 'a) \<Rightarrow>
    nat \<Rightarrow> tm list \<Rightarrow> 'a option list \<Rightarrow> 'a" where
  "substitute_method n u M k xs ys = M k (map (subst n u) xs) ys"

lemma parameter_tree_substitution:
  "parameter_tree S h P t \<Longrightarrow>
    parameter_tree S h (\<lambda>j. subst n u ` P j) (subst n u t)"
proof (induct rule: parameter_tree.induct)
  case (node k xs)
  show ?case
    by (simp only: subst.simps; rule parameter_tree.node)
      (use node in auto)
qed

lemma parameter_fold_substitution:
  "parameter_tree S h P t \<Longrightarrow>
    parameter_fold S h (substitute_method n u M) t =
    parameter_fold S h M (subst n u t)"
proof (induct rule: parameter_tree.induct)
  case (node k xs)
  have masks: "ih_mask (pcons (S h) ! k)
      (map (parameter_fold S h (substitute_method n u M)) xs) =
    ih_mask (pcons (S h) ! k) (map (parameter_fold S h M) (map (subst n u) xs))"
    by (rule nth_equalityI) (use node in auto)
  show ?case by (simp only: parameter_fold.simps subst.simps masks; simp add: substitute_method_def)
qed

lemma displayed_arguments_substitution:
  "displayed_arguments (\<lambda>x. F (subst n u x)) ss xs ys \<longleftrightarrow>
    displayed_arguments F ss (map (subst n u) xs) ys"
  by (auto simp: displayed_arguments_def split: argspec.splits)

lemma parameter_arguments_substitution:
  assumes "parameter_arguments S h P ss xs"
  shows "parameter_arguments S h (\<lambda>j. subst n u ` P j) ss (map (subst n u) xs)"
proof -
  have len: "length xs = length ss" and ext: "external_arity h ss"
    using assms by (auto simp: parameter_arguments_def)
  have C: "\<And>i. i < length xs \<Longrightarrow>
    parameter_carrier S h (\<lambda>j. subst n u ` P j) (argTy h (ss ! i)) (subst n u (xs ! i))"
  proof -
    fix i assume I: "i < length xs"
    have H: "parameter_carrier S h P (argTy h (ss ! i)) (xs ! i)"
      using assms I unfolding parameter_arguments_def by blast
    show "parameter_carrier S h (\<lambda>j. subst n u ` P j) (argTy h (ss ! i)) (subst n u (xs ! i))"
      using H parameter_tree_substitution
      by (cases "ss ! i") (auto simp: parameter_carrier_def)
  qed
  show ?thesis using len ext C by (simp add: parameter_arguments_def)
qed

lemma parameter_endpoint_substitution:
  assumes endpoint: "wf_endpt S h ss e A" and len: "length xs = length ss"
  shows "parameter_endpoint h (substitute_method n u M) xs ys e =
    parameter_endpoint h M (map (subst n u) xs) ys e"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case by simp
next
  case (wfECon k es)
  have actual: "map (subst n u) (map (instE h xs) es) =
      map (instE h (map (subst n u) xs)) es"
    by (rule nth_equalityI)
      (use wfECon instE_term_substitution[OF _ len] in auto)
  have lifted: "map (parameter_endpoint h (substitute_method n u M) xs ys) es =
      map (parameter_endpoint h M (map (subst n u) xs) ys) es"
    by (rule nth_equalityI) (use wfECon in auto)
  show ?case by (simp only: parameter_endpoint.simps lifted; simp only: substitute_method_def actual)
qed

lemma displayed_algebra_substitution:
  assumes A: "parameter_displayed_algebra S h (\<lambda>j. subst n u ` P j) F M"
  shows "parameter_displayed_algebra S h P (\<lambda>x. F (subst n u x)) (substitute_method n u M)"
proof
  fix k xs ys
  assume T: "parameter_tree S h P (PCon h k xs)"
    and L: "displayed_arguments (\<lambda>x. F (subst n u x)) (pcons (S h) ! k) xs ys"
  have T': "parameter_tree S h (\<lambda>j. subst n u ` P j) (PCon h k (map (subst n u) xs))"
    using parameter_tree_substitution[OF T] by simp
  have L': "displayed_arguments F (pcons (S h) ! k) (map (subst n u) xs) ys"
    using L by (simp only: displayed_arguments_substitution)
  from parameter_displayed_algebra.method_type[OF A T' L']
  show "substitute_method n u M k xs ys \<in> F (subst n u (PCon h k xs))"
    by (simp add: substitute_method_def)
qed

section \<open>A substitution which changes an opaque parameter\<close>

definition open_parameter_list :: tm where
  "open_parameter_list = PCon 0 1 [Var 0, PCon 0 0 []]"

lemma open_parameter_list_tree:
  "parameter_tree parameter_list_signature 0
    (\<lambda>j. if j = 1 then {Var 0} else {}) open_parameter_list"
proof -
  have nil: "parameter_tree parameter_list_signature 0
      (\<lambda>j. if j = 1 then {Var 0} else {}) (PCon 0 0 [])"
    by (rule parameter_tree.node)
      (auto simp: parameter_list_signature_def external_arity_def)
  show ?thesis
    unfolding open_parameter_list_def
    by (rule parameter_tree.node)
      (use nil in \<open>auto simp: parameter_list_signature_def external_arity_def less_Suc_eq\<close>)
qed

lemma open_parameter_list_typed:
  "wt parameter_list_signature D [Hit 1] open_parameter_list (Hit 0)"
proof (rule parameter_tree_typed[OF open_parameter_list_tree])
  fix j :: nat and v :: tm
  assume V: "v \<in> (if j = 1 then {Var 0} else {})"
  have variable: "wt parameter_list_signature D [Hit 1] (Var 0) (Hit 1)"
    using wt.wtVar[where S=parameter_list_signature and D=D and G="[Hit 1]" and i=0] by simp
  show "wt parameter_list_signature D [Hit 1] v (Hit j)"
    using V variable by (auto split: if_splits)
qed

lemma parameter_replacement_typed:
  "wt parameter_list_signature D [] (PCon 1 0 []) (Hit 1)"
  by (rule list_parameters_typed) (simp add: list_parameters_def)

lemma substituted_parameter_list_typed:
  "wt parameter_list_signature D []
    (subst 0 (PCon 1 0 []) open_parameter_list) (Hit 0)"
proof -
  have original: "wt parameter_list_signature D (ins_ty 0 (Hit 1) []) open_parameter_list (Hit 0)"
    using open_parameter_list_typed[where D=D] by simp
  show ?thesis by (rule wt_subst[OF original parameter_replacement_typed]) simp
qed

lemma opaque_parameter_substitution_example:
  "parameter_fold parameter_list_signature 0 (count_parameter_method parameter_list_signature 0)
      open_parameter_list = 2 \<and>
   parameter_fold parameter_list_signature 0
      (substitute_method 0 (PCon 1 0 []) (count_parameter_method parameter_list_signature 0))
      open_parameter_list = 3"
  by (simp add: open_parameter_list_def substitute_method_def count_parameter_method_def
    parameter_list_signature_def ih_mask_def)

lemma open_parameter_naturality:
  "parameter_fold parameter_list_signature 0
      (substitute_method 0 (PCon 1 0 []) M) open_parameter_list =
    parameter_fold parameter_list_signature 0 M (subst 0 (PCon 1 0 []) open_parameter_list)"
  by (rule parameter_fold_substitution[OF open_parameter_list_tree])

end
