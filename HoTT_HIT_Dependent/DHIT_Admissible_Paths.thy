theory DHIT_Admissible_Paths
  imports DHIT_Families
begin

section \<open>Explicitly admitted generating edges\<close>

fun dart_edge :: "'e dart \<Rightarrow> 'e" where
  "dart_edge (Pos e) = e"
| "dart_edge (Neg e) = e"

lemma dart_edge_inverse [simp]: "dart_edge (inverse d) = dart_edge d"
  by (cases d) simp_all

definition walk_on :: "'e set \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow>
    ('e \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'e dart list \<Rightarrow> 'v \<Rightarrow> bool" where
  "walk_on E s t x p y \<longleftrightarrow>
    walk s t x p y \<and> (\<forall>d \<in> set p. dart_edge d \<in> E)"

lemma walk_on_Nil [simp]: "walk_on E s t x [] y \<longleftrightarrow> x = y"
  by (simp add: walk_on_def)

lemma walk_on_Cons [simp]:
  "walk_on E s t x (d # p) y \<longleftrightarrow>
    x = source s t d \<and> dart_edge d \<in> E \<and> walk_on E s t (target s t d) p y"
  by (auto simp: walk_on_def)

lemma walk_on_induct [consumes 1, case_names nil cons]:
  assumes W: "walk_on E s t x p y"
    and nil: "\<And>x. P x [] x"
    and cons: "\<And>d p y. dart_edge d \<in> E \<Longrightarrow>
      walk_on E s t (target s t d) p y \<Longrightarrow>
      P (target s t d) p y \<Longrightarrow> P (source s t d) (d # p) y"
  shows "P x p y"
  using W by (induct p arbitrary: x) (auto intro: nil cons)

lemma walk_on_empty [simp]:
  "walk_on {} s t x p y \<longleftrightarrow> p = [] \<and> x = y"
  by (cases p) auto

lemma walk_on_UNIV [simp]: "walk_on UNIV s t x p y \<longleftrightarrow> walk s t x p y"
  by (simp add: walk_on_def)

lemma walk_on_append [simp]:
  "walk_on E s t x (p @ q) z \<longleftrightarrow>
    (\<exists>y. walk_on E s t x p y \<and> walk_on E s t y q z)"
  by (auto simp: walk_on_def)

lemma walk_on_reverse:
  "walk_on E s t x p y \<Longrightarrow> walk_on E s t y (reverse_path p) x"
proof -
  assume W: "walk_on E s t x p y"
  have R: "walk s t y (reverse_path p) x"
    using W unfolding walk_on_def by (blast intro: walk_reverse)
  show ?thesis using W R by (auto simp: walk_on_def reverse_path_def)
qed

lemma walk_on_edges:
  "walk_on E s t x p y \<Longrightarrow> d \<in> set p \<Longrightarrow> dart_edge d \<in> E"
  by (simp add: walk_on_def)

lemma cancel_edge_subset: "cancel p q \<Longrightarrow> set q \<subseteq> set p"
  by (induct rule: cancel.induct) auto

lemma walk_on_cancel:
  assumes C: "cancel p q" and W: "walk_on E s t x p y"
  shows "walk_on E s t x q y"
proof -
  have raw: "walk s t x q y"
    by (rule cancel_subject_reduction[OF C]) (use W in \<open>simp add: walk_on_def\<close>)
  show ?thesis using raw W cancel_edge_subset[OF C]
    by (auto simp: walk_on_def)
qed

inductive equality_on :: "'e set \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow>
    ('e \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'e dart list \<Rightarrow>
    'e dart list \<Rightarrow> 'v \<Rightarrow> bool" for E s t where
  refl: "walk_on E s t x p y \<Longrightarrow> equality_on E s t x p p y"
| cancel: "walk_on E s t x p y \<Longrightarrow> cancel p q \<Longrightarrow>
    equality_on E s t x p q y"
| sym: "equality_on E s t x p q y \<Longrightarrow> equality_on E s t x q p y"
| trans: "equality_on E s t x p q y \<Longrightarrow> equality_on E s t x q r y \<Longrightarrow>
    equality_on E s t x p r y"

lemma equality_on_typed:
  "equality_on E s t x p q y \<Longrightarrow> walk_on E s t x p y \<and> walk_on E s t x q y"
  by (induct rule: equality_on.induct) (auto dest: walk_on_cancel)

lemma equality_on_forget:
  "equality_on E s t x p q y \<Longrightarrow> path_equal s t x p q y"
proof (induction rule: equality_on.induct)
  case (refl x p y)
  then show ?case by (intro path_equal.refl) (simp add: walk_on_def)
next
  case (cancel x p y q)
  then show ?case by (intro path_equal.cancel) (auto simp: walk_on_def)
next
  case (sym x p q y)
  show ?case by (rule path_equal.sym[OF sym.IH])
next
  case (trans x p q y r)
  show ?case by (rule path_equal.trans[OF trans.IH])
qed

lemma equality_on_context:
  assumes "equality_on E s t x p q y" "walk_on E s t w l x" "walk_on E s t y r z"
  shows "equality_on E s t w (l @ p @ r) (l @ q @ r) z"
  using assms
  by (induct rule: equality_on.induct)
    (meson walk_on_append equality_on.intros cancel_context)+

lemma equality_on_empty:
  "equality_on {} s t x p q y \<longleftrightarrow> p = [] \<and> q = [] \<and> x = y"
proof
  assume Q: "equality_on {} s t x p q y"
  show "p = [] \<and> q = [] \<and> x = y"
    using equality_on_typed[OF Q] by simp
next
  assume "p = [] \<and> q = [] \<and> x = y"
  then show "equality_on {} s t x p q y" by (auto intro: equality_on.refl)
qed

section \<open>Families whose laws hold on admitted edges\<close>

text \<open>The edge-label type need not encode validity. The admitted set may
be empty, and transport functions on rejected labels have no mathematical
obligations. Every path and equality theorem retains admitted-edge hypotheses.\<close>

locale graph_family_on =
  fixes E :: "'e set" and s t :: "'e \<Rightarrow> 'v"
    and F :: "'v \<Rightarrow> 'a set"
    and up down :: "'e \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes up_type: "e \<in> E \<Longrightarrow> a \<in> F (s e) \<Longrightarrow> up e a \<in> F (t e)"
    and down_type: "e \<in> E \<Longrightarrow> a \<in> F (t e) \<Longrightarrow> down e a \<in> F (s e)"
    and down_up: "e \<in> E \<Longrightarrow> a \<in> F (s e) \<Longrightarrow> down e (up e a) = a"
    and up_down: "e \<in> E \<Longrightarrow> a \<in> F (t e) \<Longrightarrow> up e (down e a) = a"
begin

fun step_transport :: "'e dart \<Rightarrow> 'a \<Rightarrow> 'a" where
  "step_transport (Pos e) = up e"
| "step_transport (Neg e) = down e"

fun transport :: "'e dart list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "transport [] a = a"
| "transport (d # p) a = transport p (step_transport d a)"

lemma step_type:
  "dart_edge d \<in> E \<Longrightarrow> a \<in> F (source s t d) \<Longrightarrow>
    step_transport d a \<in> F (target s t d)"
  by (cases d) (simp_all add: up_type down_type)

lemma step_inverse:
  "dart_edge d \<in> E \<Longrightarrow> a \<in> F (source s t d) \<Longrightarrow>
    step_transport (inverse d) (step_transport d a) = a"
  by (cases d) (simp_all add: down_up up_down)

lemma transport_type:
  "walk_on E s t x p y \<Longrightarrow> a \<in> F x \<Longrightarrow> transport p a \<in> F y"
  by (induct p arbitrary: x a) (auto intro: step_type)

lemma transport_append [simp]:
  "transport (p @ q) a = transport q (transport p a)"
  by (induct p arbitrary: a) simp_all

lemma transport_reverse:
  "walk_on E s t x p y \<Longrightarrow> a \<in> F x \<Longrightarrow>
    transport (reverse_path p) (transport p a) = a"
  by (induct p arbitrary: x a) (auto simp: step_inverse step_type)

lemma transport_reverse_right:
  assumes W: "walk_on E s t x p y" and A: "a \<in> F y"
  shows "transport p (transport (reverse_path p) a) = a"
  using transport_reverse[OF walk_on_reverse[OF W] A] by simp

lemma transport_cancel:
  assumes C: "cancel p q" and W: "walk_on E s t x p y" and A: "a \<in> F x"
  shows "transport p a = transport q a"
proof -
  from C obtain l d r where P: "p = l @ d # inverse d # r" and Q: "q = l @ r"
    by (cases rule: cancel.cases) auto
  from W obtain z where L: "walk_on E s t x l z" and D: "z = source s t d"
    and DE: "dart_edge d \<in> E"
    by (auto simp: P)
  have T: "transport l a \<in> F (source s t d)"
    using transport_type[OF L A] D by simp
  show ?thesis by (simp add: P Q step_inverse[OF DE T])
qed

lemma transport_equal:
  "equality_on E s t x p q y \<Longrightarrow> a \<in> F x \<Longrightarrow>
    transport p a = transport q a"
  by (induct rule: equality_on.induct) (auto intro: transport_cancel)

lemma transport_bijective:
  assumes W: "walk_on E s t x p y"
  shows "bij_betw (transport p) (F x) (F y)"
proof (unfold bij_betw_def, intro conjI)
  show "inj_on (transport p) (F x)"
    unfolding inj_on_def using transport_reverse[OF W] by metis
  show "transport p ` F x = F y"
  proof
    show "transport p ` F x \<subseteq> F y" using transport_type[OF W] by blast
    show "F y \<subseteq> transport p ` F x"
      using transport_type[OF walk_on_reverse[OF W]] transport_reverse_right[OF W] by force
  qed
qed

section \<open>Admitted generator coherence\<close>

definition point_section_on :: "('v \<Rightarrow> 'a) \<Rightarrow> bool" where
  "point_section_on f \<longleftrightarrow> (\<forall>x. f x \<in> F x)"

definition boundary_on :: "('v \<Rightarrow> 'a) \<Rightarrow> bool" where
  "boundary_on f \<longleftrightarrow> (\<forall>e \<in> E. up e (f (s e)) = f (t e))"

definition section_on :: "('v \<Rightarrow> 'a) \<Rightarrow> bool" where
  "section_on f \<longleftrightarrow> point_section_on f \<and>
    (\<forall>x p y. walk_on E s t x p y \<longrightarrow> transport p (f x) = f y)"

lemma coherent_step:
  assumes "point_section_on f" "boundary_on f" "dart_edge d \<in> E"
  shows "step_transport d (f (source s t d)) = f (target s t d)"
proof (cases d)
  case (Pos e)
  then show ?thesis using assms by (simp add: boundary_on_def)
next
  case (Neg e)
  have T: "f (s e) \<in> F (s e)" using assms(1) by (simp add: point_section_on_def)
  have DE: "e \<in> E" using assms(3) Neg by simp
  have B: "up e (f (s e)) = f (t e)" using assms(2) DE by (simp add: boundary_on_def)
  show ?thesis using down_up[OF DE T] by (simp add: Neg B)
qed

lemma section_transport_coherence:
  assumes "point_section_on f" "boundary_on f" "walk_on E s t x p y"
  shows "transport p (f x) = f y"
  using assms(3)
  by (induct p arbitrary: x) (auto simp: coherent_step[OF assms(1,2)])

lemma boundary_coherence_iff:
  "section_on f \<longleftrightarrow> point_section_on f \<and> boundary_on f"
proof
  assume S: "section_on f"
  have B: "\<And>e. e \<in> E \<Longrightarrow> up e (f (s e)) = f (t e)"
  proof -
    fix e assume E: "e \<in> E"
    have W: "walk_on E s t (s e) [Pos e] (t e)" using E by simp
    have "transport [Pos e] (f (s e)) = f (t e)"
      using S W unfolding section_on_def by blast
    then show "up e (f (s e)) = f (t e)" by simp
  qed
  with S show "point_section_on f \<and> boundary_on f"
    by (auto simp: section_on_def boundary_on_def)
next
  assume "point_section_on f \<and> boundary_on f"
  then show "section_on f"
    unfolding section_on_def using section_transport_coherence by blast
qed

end

lemma empty_graph_family:
  "graph_family_on {} s t F up down"
  by unfold_locales simp_all

section \<open>Conservativity when every edge is admitted\<close>

lemma equality_on_UNIV:
  "equality_on UNIV s t x p q y \<longleftrightarrow> path_equal s t x p q y"
proof
  assume "equality_on UNIV s t x p q y"
  then show "path_equal s t x p q y" by (rule equality_on_forget)
next
  assume P: "path_equal s t x p q y"
  from P show "equality_on UNIV s t x p q y"
  proof (induction rule: path_equal.induct)
    case (refl x p y)
    show ?case by (rule equality_on.refl) (simp add: refl)
  next
    case (cancel x p y q)
    show ?case by (rule equality_on.cancel) (simp_all add: cancel)
  next
    case (sym x p q y)
    show ?case by (rule equality_on.sym[OF sym.IH])
  next
    case (trans x p q y r)
    show ?case by (rule equality_on.trans[OF trans.IH])
  qed
qed

lemma graph_family_on_UNIV:
  "graph_family_on UNIV s t F up down \<longleftrightarrow> graph_family s t F up down"
  by (auto simp: graph_family_on_def graph_family_def)

context graph_family
begin

sublocale all_edges: graph_family_on UNIV s t F up down
  by unfold_locales (auto intro: up_type down_type down_up up_down)

lemma all_edges_step_transport:
  "all_edges.step_transport d a = step_transport d a"
  by (cases d) simp_all

lemma all_edges_transport:
  "all_edges.transport p a = transport p a"
  by (induct p arbitrary: a) (simp_all add: all_edges_step_transport)

lemma all_edges_sections:
  "all_edges.section_on f \<longleftrightarrow> dependent_section f"
  by (simp add: all_edges.section_on_def dependent_section_def
    all_edges.point_section_on_def point_section_def all_edges_transport)

end

end
