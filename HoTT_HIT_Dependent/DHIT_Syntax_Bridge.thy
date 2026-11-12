theory DHIT_Syntax_Bridge
  imports DHIT_Reindexing "HoTT_HIT_Metatheory.HIT_Substitution"
begin

section \<open>Dependent families over the published HIT syntax\<close>

text \<open>Edges are selected well-typed instances of the original path
constructors, with the original endpoint expressions and recursive arguments.
The free path closure used here does not add point-constructor congruences or
identify paths with computational equality of the old calculus.\<close>

lemma instE_term_substitution:
  assumes "wf_endpt S h ss e A" "length xs = length ss"
  shows "subst n u (instE h xs e) = instE h (map (subst n u) xs) e"
  using assms
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case by simp
next
  case (wfECon k es)
  then have "map (subst n u \<circ> instE h xs) es =
      map (instE h (map (subst n u) xs)) es"
    by (intro nth_equalityI) auto
  then show ?case by (simp add: comp_def)
qed

lemma lhsOf_term_substitution:
  assumes "wf_hsig S h" "k < length (lcons (S h))"
    "length xs = length (lcons (S h) ! k)"
  shows "subst n u (lhsOf S h k xs) = lhsOf S h k (map (subst n u) xs)"
  unfolding lhsOf_def
  by (rule instE_term_substitution[OF wf_hsig_lhs[OF assms(1,2)] assms(3)])

lemma rhsOf_term_substitution:
  assumes "wf_hsig S h" "k < length (lcons (S h))"
    "length xs = length (lcons (S h) ! k)"
  shows "subst n u (rhsOf S h k xs) = rhsOf S h k (map (subst n u) xs)"
  unfolding rhsOf_def
  by (rule instE_term_substitution[OF wf_hsig_rhs[OF assms(1,2)] assms(3)])

locale typed_hit_graph =
  fixes S :: sigenv and D :: "nat set" and G :: "ty list" and h :: nat
    and constructor :: "'e \<Rightarrow> nat" and arguments :: "'e \<Rightarrow> tm list"
  assumes signature: "wf_hsig S h"
    and constructor_bound: "constructor e < length (lcons (S h))"
    and arguments_length:
      "length (arguments e) = length (lcons (S h) ! constructor e)"
    and arguments_typed:
      "i < length (arguments e) \<Longrightarrow>
       wt S D G (arguments e ! i) (argTy h (lcons (S h) ! constructor e ! i))"
begin

definition hit_source :: "'e \<Rightarrow> tm" where
  "hit_source e = lhsOf S h (constructor e) (arguments e)"

definition hit_target :: "'e \<Rightarrow> tm" where
  "hit_target e = rhsOf S h (constructor e) (arguments e)"

lemma hit_source_typed: "wt S D G (hit_source e) (Hit h)"
  unfolding hit_source_def
  by (rule wf_hsig_lhs_typed[OF signature constructor_bound arguments_length])
    (auto intro: arguments_typed)

lemma hit_target_typed: "wt S D G (hit_target e) (Hit h)"
  unfolding hit_target_def
  by (rule wf_hsig_rhs_typed[OF signature constructor_bound arguments_length])
    (auto intro: arguments_typed)

lemma hit_dart_source_typed:
  "wt S D G (source hit_source hit_target d) (Hit h)"
  by (cases d) (simp_all add: hit_source_typed hit_target_typed)

lemma hit_dart_target_typed:
  "wt S D G (target hit_source hit_target d) (Hit h)"
  by (cases d) (simp_all add: hit_source_typed hit_target_typed)

lemma hit_path_target_typed:
  "walk hit_source hit_target x p y \<Longrightarrow> wt S D G x (Hit h) \<Longrightarrow>
    wt S D G y (Hit h)"
  by (induct rule: walk.induct) (auto intro: hit_dart_target_typed)

lemma hit_source_substitution:
  "subst n u (hit_source e) =
    lhsOf S h (constructor e) (map (subst n u) (arguments e))"
  unfolding hit_source_def
  by (rule lhsOf_term_substitution[OF signature constructor_bound arguments_length])

lemma hit_target_substitution:
  "subst n u (hit_target e) =
    rhsOf S h (constructor e) (map (subst n u) (arguments e))"
  unfolding hit_target_def
  by (rule rhsOf_term_substitution[OF signature constructor_bound arguments_length])

lemma hit_substitution_morphism:
  "graph_morphism hit_source hit_target
    (\<lambda>e. lhsOf S h (constructor e) (map (subst n u) (arguments e)))
    (\<lambda>e. rhsOf S h (constructor e) (map (subst n u) (arguments e)))
    (subst n u) id"
  by unfold_locales (simp_all add: hit_source_substitution hit_target_substitution)

lemma hit_substitution_reindexing:
  assumes "graph_family
    (\<lambda>e. lhsOf S h (constructor e) (map (subst n u) (arguments e)))
    (\<lambda>e. rhsOf S h (constructor e) (map (subst n u) (arguments e))) F up down"
  shows "family_reindexing hit_source hit_target
    (\<lambda>e. lhsOf S h (constructor e) (map (subst n u) (arguments e)))
    (\<lambda>e. rhsOf S h (constructor e) (map (subst n u) (arguments e)))
    F up down (subst n u) id"
  by (rule family_reindexing.intro[OF assms hit_substitution_morphism])

lemma hit_path_substitution:
  assumes "walk hit_source hit_target x p y"
  shows "walk
    (\<lambda>e. lhsOf S h (constructor e) (map (subst n u) (arguments e)))
    (\<lambda>e. rhsOf S h (constructor e) (map (subst n u) (arguments e)))
    (subst n u x) p (subst n u y)"
proof -
  have identity: "map_dart id = id" by (rule ext) simp
  show ?thesis
    using graph_morphism.substitution_preserves_paths[OF hit_substitution_morphism[of n u] assms]
    by (simp add: identity)
qed


context
  fixes F :: "tm \<Rightarrow> 'a set" and up down :: "'e \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes family: "graph_family hit_source hit_target F up down"
begin

interpretation fibers: graph_family hit_source hit_target F up down
  by (rule family)

lemma typed_boundary_step:
  assumes points: "\<And>x. wt S D G x (Hit h) \<Longrightarrow> f x \<in> F x"
    and boundary: "\<And>e. up e (f (hit_source e)) = f (hit_target e)"
  shows "fibers.step_transport d (f (source hit_source hit_target d)) =
    f (target hit_source hit_target d)"
proof (cases d)
  case (Pos e)
  then show ?thesis by (simp add: boundary)
next
  case (Neg e)
  have "f (hit_source e) \<in> F (hit_source e)"
    by (rule points[OF hit_source_typed])
  from fibers.down_up[OF this] boundary[of e]
  have "down e (f (hit_target e)) = f (hit_source e)" by simp
  with Neg show ?thesis by simp
qed

text \<open>The dependent motive is required only at well-typed HIT terms.
For an already given point section, boundary equations on constructor instances suffice for every composed path,
including reversed generating paths. No old nondependent eliminator is used
as a dependent eliminator.\<close>

theorem typed_section_coherence:
  assumes points: "\<And>x. wt S D G x (Hit h) \<Longrightarrow> f x \<in> F x"
    and boundary: "\<And>e. up e (f (hit_source e)) = f (hit_target e)"
    and path: "walk hit_source hit_target x p y"
    and typed: "wt S D G x (Hit h)"
  shows "fibers.transport p (f x) = f y \<and> f y \<in> F y"
proof -
  have "fibers.transport p (f x) = f y"
    using path by (induct rule: walk.induct)
      (simp_all add: typed_boundary_step[OF points boundary])
  moreover have "f y \<in> F y"
    by (rule points[OF hit_path_target_typed[OF path typed]])
  ultimately show ?thesis by simp
qed

corollary typed_boundary_coherence_iff:
  assumes points: "\<And>x. wt S D G x (Hit h) \<Longrightarrow> f x \<in> F x"
  shows "(\<forall>e. up e (f (hit_source e)) = f (hit_target e)) \<longleftrightarrow>
    (\<forall>x p y. wt S D G x (Hit h) \<longrightarrow>
      walk hit_source hit_target x p y \<longrightarrow> fibers.transport p (f x) = f y)"
proof
  assume boundary: "\<forall>e. up e (f (hit_source e)) = f (hit_target e)"
  show "\<forall>x p y. wt S D G x (Hit h) \<longrightarrow>
      walk hit_source hit_target x p y \<longrightarrow> fibers.transport p (f x) = f y"
    using typed_section_coherence[OF points] boundary by blast
next
  assume all: "\<forall>x p y. wt S D G x (Hit h) \<longrightarrow>
      walk hit_source hit_target x p y \<longrightarrow> fibers.transport p (f x) = f y"
  show "\<forall>e. up e (f (hit_source e)) = f (hit_target e)"
  proof
    fix e
    have "fibers.transport [Pos e] (f (hit_source e)) = f (hit_target e)"
      using all[rule_format, of "hit_source e" "[Pos e]" "hit_target e"]
        hit_source_typed[of e] by simp
    then show "up e (f (hit_source e)) = f (hit_target e)" by simp
  qed
qed

end

end

section \<open>Typed substitution induces reindexing\<close>

lemma typed_hit_graph_substitution:
  assumes H: "typed_hit_graph S D (ins_ty n A G) h k args"
    and U: "wt S D G u A" and N: "n \<le> length G"
  shows "typed_hit_graph S D G h k (\<lambda>e. map (subst n u) (args e))"
proof -
  interpret H: typed_hit_graph S D "ins_ty n A G" h k args by (rule H)
  show ?thesis
  proof
    show "wf_hsig S h" by (rule H.signature)
    show "k e < length (lcons (S h))" for e by (rule H.constructor_bound)
    show "length (map (subst n u) (args e)) = length (lcons (S h) ! k e)" for e
      by (simp add: H.arguments_length)
    fix e i
    assume I: "i < length (map (subst n u) (args e))"
    have "wt S D (ins_ty n A G) (args e ! i) (argTy h (lcons (S h) ! k e ! i))"
      by (rule H.arguments_typed) (use I in simp)
    from wt_subst[OF this U N]
    show "wt S D G (map (subst n u) (args e) ! i) (argTy h (lcons (S h) ! k e ! i))"
      using I by simp
  qed
qed

end
