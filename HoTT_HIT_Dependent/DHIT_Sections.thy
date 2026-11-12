theory DHIT_Sections
  imports DHIT_Families
begin

section \<open>Classification by monodromy\<close>

text \<open>In a connected graph, a dependent section is determined by a single
fiber element. Such an element extends precisely when the generator loops
formed using chosen connecting paths fix it. This is an existence and uniqueness
criterion, not an assumption that arbitrary point methods are coherent.\<close>

locale based_graph_family = graph_family s t F up down
  for s t :: "'e \<Rightarrow> 'v" and F :: "'v \<Rightarrow> 'a set"
    and up down :: "'e \<Rightarrow> 'a \<Rightarrow> 'a" +
  fixes root :: 'v and route :: "'v \<Rightarrow> 'e dart list"
  assumes route_typed: "walk s t root (route x) x"
    and route_root: "route root = []"
begin

definition generator_loop :: "'e \<Rightarrow> 'e dart list" where
  "generator_loop e = route (s e) @ [Pos e] @ reverse_path (route (t e))"

lemma generator_loop_typed:
  "walk s t root (generator_loop e) root"
  unfolding generator_loop_def using route_typed walk_reverse[OF route_typed] by auto

definition invariant_fiber :: "'a set" where
  "invariant_fiber = {a \<in> F root. \<forall>e. transport (generator_loop e) a = a}"

definition extend :: "'a \<Rightarrow> 'v \<Rightarrow> 'a" where
  "extend a x = transport (route x) a"

lemma extend_root [simp]: "extend a root = a"
  by (simp add: extend_def route_root)

lemma extension_point_type:
  "a \<in> F root \<Longrightarrow> point_section (extend a)"
  unfolding point_section_def extend_def using transport_type[OF route_typed] by blast

lemma extension_boundary:
  assumes A: "a \<in> invariant_fiber"
  shows "boundary_coherent (extend a)"
proof (unfold boundary_coherent_def, intro allI)
  fix e
  have AR: "a \<in> F root" using A by (simp add: invariant_fiber_def)
  have T: "up e (transport (route (s e)) a) \<in> F (t e)"
    by (rule up_type[OF transport_type[OF route_typed AR]])
  have L: "transport (reverse_path (route (t e)))
      (up e (transport (route (s e)) a)) = a"
    using A unfolding invariant_fiber_def generator_loop_def by simp
  from transport_reverse_iff[OF route_typed AR T] L
  show "up e (extend a (s e)) = extend a (t e)"
    by (simp add: extend_def)
qed

lemma extension_is_section:
  "a \<in> invariant_fiber \<Longrightarrow> dependent_section (extend a)"
  using extension_point_type extension_boundary boundary_coherence_iff
  unfolding invariant_fiber_def by blast

lemma section_determined_by_root:
  assumes S: "dependent_section f"
  shows "f = extend (f root)"
proof (rule ext)
  fix x
  have "transport (route x) (f root) = f x"
    using S route_typed unfolding dependent_section_def by blast
  then show "f x = extend (f root) x" by (simp add: extend_def)
qed

lemma section_root_invariant:
  "dependent_section f \<Longrightarrow> f root \<in> invariant_fiber"
  unfolding dependent_section_def point_section_def invariant_fiber_def
  using generator_loop_typed by blast

lemma section_classification:
  "dependent_section f \<longleftrightarrow>
    (\<exists>a \<in> invariant_fiber. f = extend a)"
  using extension_is_section section_determined_by_root section_root_invariant by blast

lemma section_bijection:
  "bij_betw extend invariant_fiber {f. dependent_section f}"
proof (unfold bij_betw_def, intro conjI)
  show "inj_on extend invariant_fiber"
    unfolding inj_on_def by (metis extend_root)
  show "extend ` invariant_fiber = {f. dependent_section f}"
    using section_classification by blast
qed

lemma invariant_iff_all_loops:
  "a \<in> invariant_fiber \<longleftrightarrow>
    a \<in> F root \<and> (\<forall>p. walk s t root p root \<longrightarrow> transport p a = a)"
proof
  assume A: "a \<in> invariant_fiber"
  have "dependent_section (extend a)" by (rule extension_is_section[OF A])
  then have H: "\<forall>x p y. walk s t x p y \<longrightarrow> transport p (extend a x) = extend a y"
    unfolding dependent_section_def by blast
  have "\<And>p. walk s t root p root \<Longrightarrow> transport p a = a"
  proof -
    fix p assume W: "walk s t root p root"
    have "transport p (extend a root) = extend a root" using H W by blast
    then show "transport p a = a" by simp
  qed
  with A show "a \<in> F root \<and> (\<forall>p. walk s t root p root \<longrightarrow> transport p a = a)"
    by (auto simp: invariant_fiber_def)
next
  assume "a \<in> F root \<and> (\<forall>p. walk s t root p root \<longrightarrow> transport p a = a)"
  then show "a \<in> invariant_fiber"
    using generator_loop_typed unfolding invariant_fiber_def by blast
qed

lemma extension_route_independent:
  assumes A: "a \<in> invariant_fiber" and W: "walk s t root p x"
  shows "transport p a = extend a x"
proof -
  have "dependent_section (extend a)" by (rule extension_is_section[OF A])
  then have "transport p (extend a root) = extend a x"
    using W unfolding dependent_section_def by blast
  then show ?thesis by simp
qed

end

section \<open>A loop with no dependent section\<close>

interpretation twisted_loop: graph_family
  "\<lambda>_::unit. ()" "\<lambda>_::unit. ()"
  "\<lambda>_::unit. UNIV::bool set" "\<lambda>_. Not" "\<lambda>_. Not"
  by unfold_locales auto

lemma twisted_loop_has_no_section:
  "\<not> twisted_loop.dependent_section f"
  by (simp add: twisted_loop.boundary_coherence_iff twisted_loop.boundary_coherent_def)

section \<open>Distinct endpoint fibers\<close>

interpretation shifted_interval: graph_family
  "\<lambda>_::unit. False" "\<lambda>_::unit. True"
  "\<lambda>x. if x then {1::nat} else {0}" "\<lambda>_. Suc" "\<lambda>_ n. n - 1"
  by unfold_locales auto

lemma shifted_interval_section:
  "shifted_interval.dependent_section (\<lambda>x. if x then 1 else 0)"
  apply (rule shifted_interval.boundary_coherence_iff[THEN iffD2])
  by (simp add: shifted_interval.point_section_def shifted_interval.boundary_coherent_def)

end
