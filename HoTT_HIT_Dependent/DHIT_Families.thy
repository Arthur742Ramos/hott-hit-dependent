theory DHIT_Families
  imports DHIT_Paths
begin

section \<open>Dependent fibers and transport\<close>

locale graph_family =
  fixes s t :: "'e \<Rightarrow> 'v"
    and F :: "'v \<Rightarrow> 'a set"
    and up down :: "'e \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes up_type: "a \<in> F (s e) \<Longrightarrow> up e a \<in> F (t e)"
    and down_type: "a \<in> F (t e) \<Longrightarrow> down e a \<in> F (s e)"
    and down_up: "a \<in> F (s e) \<Longrightarrow> down e (up e a) = a"
    and up_down: "a \<in> F (t e) \<Longrightarrow> up e (down e a) = a"
begin

fun step_transport :: "'e dart \<Rightarrow> 'a \<Rightarrow> 'a" where
  "step_transport (Pos e) = up e"
| "step_transport (Neg e) = down e"

fun transport :: "'e dart list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "transport [] a = a"
| "transport (d # p) a = transport p (step_transport d a)"

lemma step_type:
  "a \<in> F (source s t d) \<Longrightarrow> step_transport d a \<in> F (target s t d)"
  by (cases d) (simp_all add: up_type down_type)

lemma step_inverse:
  "a \<in> F (source s t d) \<Longrightarrow>
    step_transport (inverse d) (step_transport d a) = a"
  by (cases d) (simp_all add: down_up up_down)

lemma transport_type:
  "walk s t x p y \<Longrightarrow> a \<in> F x \<Longrightarrow> transport p a \<in> F y"
  by (induct arbitrary: a rule: walk.induct) (auto intro: step_type)

lemma transport_append [simp]:
  "transport (p @ q) a = transport q (transport p a)"
  by (induct p arbitrary: a) simp_all

lemma transport_reverse:
  "walk s t x p y \<Longrightarrow> a \<in> F x \<Longrightarrow>
    transport (reverse_path p) (transport p a) = a"
  by (induct arbitrary: a rule: walk.induct) (auto simp: step_inverse step_type)

lemma transport_reverse_right:
  assumes W: "walk s t x p y" and A: "a \<in> F y"
  shows "transport p (transport (reverse_path p) a) = a"
  using transport_reverse[OF walk_reverse[OF W] A] by simp

lemma transport_reverse_iff:
  assumes W: "walk s t x p y" and A: "a \<in> F x" and B: "b \<in> F y"
  shows "transport (reverse_path p) b = a \<longleftrightarrow> b = transport p a"
  using transport_reverse[OF W A] transport_reverse_right[OF W B] by metis

lemma transport_bijective:
  assumes W: "walk s t x p y"
  shows "bij_betw (transport p) (F x) (F y)"
proof (unfold bij_betw_def, intro conjI)
  show "inj_on (transport p) (F x)"
    unfolding inj_on_def using transport_reverse[OF W] by metis
  show "transport p ` F x = F y"
  proof
    show "transport p ` F x \<subseteq> F y" using transport_type[OF W] by blast
    show "F y \<subseteq> transport p ` F x"
      using transport_type[OF walk_reverse[OF W]] transport_reverse_right[OF W] by force
  qed
qed

lemma transport_cancel:
  assumes "cancel p q" "walk s t x p y" "a \<in> F x"
  shows "transport p a = transport q a"
  using assms
  by (cases rule: cancel.cases)
    (auto simp: step_inverse dest: transport_type)

lemma transport_equal:
  "path_equal s t x p q y \<Longrightarrow> a \<in> F x \<Longrightarrow>
    transport p a = transport q a"
  by (induct rule: path_equal.induct) (auto intro: transport_cancel)

section \<open>Dependent elimination and boundary coherence\<close>

definition point_section :: "('v \<Rightarrow> 'a) \<Rightarrow> bool" where
  "point_section f \<longleftrightarrow> (\<forall>x. f x \<in> F x)"

definition boundary_coherent :: "('v \<Rightarrow> 'a) \<Rightarrow> bool" where
  "boundary_coherent f \<longleftrightarrow> (\<forall>e. up e (f (s e)) = f (t e))"

definition dependent_section :: "('v \<Rightarrow> 'a) \<Rightarrow> bool" where
  "dependent_section f \<longleftrightarrow> point_section f \<and>
    (\<forall>x p y. walk s t x p y \<longrightarrow> transport p (f x) = f y)"

lemma coherent_step:
  assumes "point_section f" "boundary_coherent f"
  shows "step_transport d (f (source s t d)) = f (target s t d)"
proof (cases d)
  case (Pos e)
  then show ?thesis using assms by (simp add: boundary_coherent_def)
next
  case (Neg e)
  have T: "f (s e) \<in> F (s e)" using assms(1) by (simp add: point_section_def)
  have E: "up e (f (s e)) = f (t e)" using assms(2) by (simp add: boundary_coherent_def)
  show ?thesis using down_up[OF T] by (simp add: Neg E)
qed

lemma section_transport_coherence:
  assumes "point_section f" "boundary_coherent f" "walk s t x p y"
  shows "transport p (f x) = f y"
  using assms(3)
  by (induct rule: walk.induct) (simp_all add: coherent_step[OF assms(1,2)])

lemma boundary_coherence_iff:
  "dependent_section f \<longleftrightarrow> point_section f \<and> boundary_coherent f"
proof
  assume h: "dependent_section f"
  have gen: "\<And>e. transport [Pos e] (f (s e)) = f (t e)"
  proof -
    fix e
    have W: "walk s t (s e) [Pos e] (t e)" by simp
    show "transport [Pos e] (f (s e)) = f (t e)"
      using h W unfolding dependent_section_def by blast
  qed
  have "boundary_coherent f" using gen by (simp add: boundary_coherent_def)
  with h show "point_section f \<and> boundary_coherent f"
    by (simp add: dependent_section_def)
next
  assume "point_section f \<and> boundary_coherent f"
  then show "dependent_section f"
    unfolding dependent_section_def using section_transport_coherence by blast
qed

lemma loop_obstruction:
  assumes "walk s t x p x"
    and "\<And>a. a \<in> F x \<Longrightarrow> transport p a \<noteq> a"
  shows "\<not> dependent_section f"
  using assms unfolding dependent_section_def point_section_def by blast

end

end
