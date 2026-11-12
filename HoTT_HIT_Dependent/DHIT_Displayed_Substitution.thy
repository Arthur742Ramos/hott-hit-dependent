theory DHIT_Displayed_Substitution
  imports DHIT_Parameter_Substitution DHIT_Parameter_Congruence
begin

section \<open>Pullback of the whole displayed HIT algebra\<close>

text \<open>The target algebra lives over substituted opaque parameters and
constructor arguments. The source methods and motive are pulled back together.
The theorem includes the uniform displayed path-method obligations, not only
the point-fold equation. Original argument admissibility remains explicit:
substitution need not reflect well-formed constructor trees.\<close>

lemma parameter_hit_algebra_substitution:
  assumes target: "parameter_hit_algebra S h (\<lambda>j. subst n u ` P j) F M
      constructor (\<lambda>e. map (subst n u) (arguments e)) up down"
    and args: "\<And>e. parameter_arguments S h P (lcons (S h) ! constructor e) (arguments e)"
  shows "parameter_hit_algebra S h P (\<lambda>x. F (subst n u x))
    (substitute_method n u M) constructor arguments up down"
proof -
  interpret T: parameter_hit_algebra S h "\<lambda>j. subst n u ` P j" F M
    constructor "\<lambda>e. map (subst n u) (arguments e)" up down by (rule target)
  have len: "length (arguments e) = length (lcons (S h) ! constructor e)" for e
    using args[of e] by (simp add: parameter_arguments_def)
  have LS: "subst n u (lhsOf S h (constructor e) (arguments e)) =
      lhsOf S h (constructor e) (map (subst n u) (arguments e))" for e
    by (rule lhsOf_term_substitution[OF T.signature T.edge_bound len])
  have RS: "subst n u (rhsOf S h (constructor e) (arguments e)) =
      rhsOf S h (constructor e) (map (subst n u) (arguments e))" for e
    by (rule rhsOf_term_substitution[OF T.signature T.edge_bound len])
  have D: "parameter_displayed_algebra S h P (\<lambda>x. F (subst n u x)) (substitute_method n u M)"
    by (rule displayed_algebra_substitution) (unfold_locales; rule T.method_type; assumption)
  interpret D: parameter_displayed_algebra S h P "\<lambda>x. F (subst n u x)" "substitute_method n u M"
    by (rule D)
  have Boundary:
    "map_option (up e) (parameter_endpoint h (substitute_method n u M) (arguments e) ys
        (fst (lends (S h) ! constructor e))) =
      parameter_endpoint h (substitute_method n u M) (arguments e) ys
        (snd (lends (S h) ! constructor e))"
    if H: "displayed_arguments (\<lambda>x. F (subst n u x))
      (lcons (S h) ! constructor e) (arguments e) ys" for e ys
  proof -
    have H': "displayed_arguments F (lcons (S h) ! constructor e)
      (map (subst n u) (arguments e)) ys"
      using H by (simp only: displayed_arguments_substitution)
    have LE: "parameter_endpoint h (substitute_method n u M) (arguments e) ys
        (fst (lends (S h) ! constructor e)) =
      parameter_endpoint h M (map (subst n u) (arguments e)) ys
        (fst (lends (S h) ! constructor e))"
      by (rule parameter_endpoint_substitution[OF wf_hsig_lhs[OF T.signature T.edge_bound] len])
    have RE: "parameter_endpoint h (substitute_method n u M) (arguments e) ys
        (snd (lends (S h) ! constructor e)) =
      parameter_endpoint h M (map (subst n u) (arguments e)) ys
        (snd (lends (S h) ! constructor e))"
      by (rule parameter_endpoint_substitution[OF wf_hsig_rhs[OF T.signature T.edge_bound] len])
    show ?thesis using T.displayed_boundary[OF H'] by (simp only: LE RE)
  qed
  show ?thesis
    by (unfold_locales)
      (auto simp: LS RS intro: D.method_type T.up_type T.down_type T.down_up T.up_down
        T.signature T.external_points T.edge_bound args Boundary)
qed

section \<open>Substitution through constructor contexts\<close>

fun substitute_context :: "nat \<Rightarrow> tm \<Rightarrow> 'e constructor_edge \<Rightarrow> 'e constructor_edge" where
  "substitute_context n u (Generator e) = Generator e"
| "substitute_context n u (Under k before c after) =
    Under k (map (subst n u) before) (substitute_context n u c) (map (subst n u) after)"

lemma context_endpoint_substitution:
  "context_endpoint h (\<lambda>e. subst n u (endpoint e)) (substitute_context n u c) =
    subst n u (context_endpoint h endpoint c)"
  by (induct c) simp_all

lemma parameter_slot_substitution:
  assumes "parameter_slot S h P k before after"
  shows "parameter_slot S h (\<lambda>j. subst n u ` P j) k
    (map (subst n u) before) (map (subst n u) after)"
  using assms unfolding parameter_slot_def
  by (blast intro: parameter_arguments_substitution)

lemma valid_parameter_context_substitution:
  "valid_parameter_context S h P E c \<Longrightarrow>
    valid_parameter_context S h (\<lambda>j. subst n u ` P j) E (substitute_context n u c)"
  by (induct rule: valid_parameter_context.induct)
    (auto intro: valid_parameter_context.intros parameter_slot_substitution)

lemma contextual_parameter_algebra_substitution:
  assumes target: "contextual_parameter_algebra S h (\<lambda>j. subst n u ` P j) F M E
      (\<lambda>e. subst n u (base_source e)) (\<lambda>e. subst n u (base_target e)) upC downC"
    and sources: "\<And>e. e \<in> E \<Longrightarrow> parameter_tree S h P (base_source e)"
    and targets: "\<And>e. e \<in> E \<Longrightarrow> parameter_tree S h P (base_target e)"
  shows "contextual_parameter_algebra S h P (\<lambda>x. F (subst n u x)) (substitute_method n u M) E
    base_source base_target (\<lambda>c. upC (substitute_context n u c)) (\<lambda>c. downC (substitute_context n u c))"
proof -
  interpret T: contextual_parameter_algebra S h "\<lambda>j. subst n u ` P j" F M E
    "\<lambda>e. subst n u (base_source e)" "\<lambda>e. subst n u (base_target e)" upC downC
    by (rule target)
  have D: "parameter_displayed_algebra S h P (\<lambda>x. F (subst n u x)) (substitute_method n u M)"
    by (rule displayed_algebra_substitution) (unfold_locales; rule T.method_type; assumption)
  interpret D: parameter_displayed_algebra S h P "\<lambda>x. F (subst n u x)" "substitute_method n u M"
    by (rule D)
  have family: "graph_family_on {c. valid_parameter_context S h P E c}
    (context_endpoint h base_source) (context_endpoint h base_target)
    (\<lambda>x. F (subst n u x)) (\<lambda>c. upC (substitute_context n u c)) (\<lambda>c. downC (substitute_context n u c))"
  proof
    fix c a
    assume C: "c \<in> {c. valid_parameter_context S h P E c}"
      and A: "a \<in> F (subst n u (context_endpoint h base_source c))"
    have V: "substitute_context n u c \<in> T.admitted"
      using valid_parameter_context_substitution C by auto
    show "upC (substitute_context n u c) a \<in> F (subst n u (context_endpoint h base_target c))"
      using T.fibers.up_type[OF V] A by (simp add: context_endpoint_substitution)
  next
    fix c a
    assume C: "c \<in> {c. valid_parameter_context S h P E c}"
      and A: "a \<in> F (subst n u (context_endpoint h base_target c))"
    have V: "substitute_context n u c \<in> T.admitted"
      using valid_parameter_context_substitution C by auto
    show "downC (substitute_context n u c) a \<in> F (subst n u (context_endpoint h base_source c))"
      using T.fibers.down_type[OF V] A by (simp add: context_endpoint_substitution)
  next
    fix c a
    assume C: "c \<in> {c. valid_parameter_context S h P E c}"
      and A: "a \<in> F (subst n u (context_endpoint h base_source c))"
    have V: "substitute_context n u c \<in> T.admitted"
      using valid_parameter_context_substitution C by auto
    show "downC (substitute_context n u c) (upC (substitute_context n u c) a) = a"
      using T.fibers.down_up[OF V] A by (simp add: context_endpoint_substitution)
  next
    fix c a
    assume C: "c \<in> {c. valid_parameter_context S h P E c}"
      and A: "a \<in> F (subst n u (context_endpoint h base_target c))"
    have V: "substitute_context n u c \<in> T.admitted"
      using valid_parameter_context_substitution C by auto
    show "upC (substitute_context n u c) (downC (substitute_context n u c) a) = a"
      using T.fibers.up_down[OF V] A by (simp add: context_endpoint_substitution)
  qed
  interpret C: graph_family_on "{c. valid_parameter_context S h P E c}"
    "context_endpoint h base_source" "context_endpoint h base_target"
    "\<lambda>x. F (subst n u x)" "\<lambda>c. upC (substitute_context n u c)" "\<lambda>c. downC (substitute_context n u c)"
    by (rule family)
  have Base: "upC (substitute_context n u (Generator e))
      (parameter_fold S h (substitute_method n u M) (base_source e)) =
      parameter_fold S h (substitute_method n u M) (base_target e)" if "e \<in> E" for e
    using T.base_boundary[OF that]
    by (simp only: substitute_context.simps parameter_fold_substitution[OF sources[OF that]]
      parameter_fold_substitution[OF targets[OF that]])
  have Natural:
    "upC (substitute_context n u (Under k before c after))
      (substitute_method n u M k (before @ [context_endpoint h base_source c] @ after) (bv @ [Some a] @ zv)) =
     substitute_method n u M k (before @ [context_endpoint h base_target c] @ after)
      (bv @ [Some (upC (substitute_context n u c) a)] @ zv)"
    if V: "valid_parameter_context S h P E (Under k before c after)"
      and R: "pcons (S h) ! k = bs @ [Rec] @ zs"
      and B: "parameter_arguments S h P bs before"
      and Z: "parameter_arguments S h P zs after"
      and BV: "displayed_arguments (\<lambda>x. F (subst n u x)) bs before bv"
      and A: "a \<in> F (subst n u (context_endpoint h base_source c))"
      and ZV: "displayed_arguments (\<lambda>x. F (subst n u x)) zs after zv"
    for k before c after bs zs bv a zv
  proof -
    have V': "valid_parameter_context S h (\<lambda>j. subst n u ` P j) E
        (Under k (map (subst n u) before) (substitute_context n u c) (map (subst n u) after))"
      using valid_parameter_context_substitution[OF V] by simp
    have B': "parameter_arguments S h (\<lambda>j. subst n u ` P j) bs (map (subst n u) before)"
      by (rule parameter_arguments_substitution[OF B])
    have Z': "parameter_arguments S h (\<lambda>j. subst n u ` P j) zs (map (subst n u) after)"
      by (rule parameter_arguments_substitution[OF Z])
    have BV': "displayed_arguments F bs (map (subst n u) before) bv"
      using BV by (simp only: displayed_arguments_substitution)
    have ZV': "displayed_arguments F zs (map (subst n u) after) zv"
      using ZV by (simp only: displayed_arguments_substitution)
    have A': "a \<in> F (T.csrc (substitute_context n u c))"
      using A by (simp add: context_endpoint_substitution)
    show ?thesis using T.point_naturality[OF V' R B' Z' BV' A' ZV']
      by (simp add: substitute_method_def context_endpoint_substitution)
  qed
  show ?thesis
    by (unfold_locales)
      (auto intro: D.method_type sources targets C.up_type C.down_type C.down_up C.up_down Base[simplified] Natural[simplified])
qed

end
