theory DHIT_Reindexing
  imports DHIT_Families
begin

section \<open>Substitution of vertices and generating paths\<close>

fun map_dart :: "('e \<Rightarrow> 'f) \<Rightarrow> 'e dart \<Rightarrow> 'f dart" where
  "map_dart E (Pos e) = Pos (E e)"
| "map_dart E (Neg e) = Neg (E e)"

lemma map_dart_id [simp]: "map_dart id a = a"
  by (cases a) simp_all

lemma map_dart_comp [simp]: "map_dart K (map_dart E a) = map_dart (K \<circ> E) a"
  by (cases a) simp_all

lemma map_dart_inverse [simp]: "map_dart E (inverse a) = inverse (map_dart E a)"
  by (cases a) simp_all

locale graph_morphism =
  fixes s t :: "'e \<Rightarrow> 'v" and s' t' :: "'f \<Rightarrow> 'w"
    and V :: "'v \<Rightarrow> 'w" and E :: "'e \<Rightarrow> 'f"
  assumes source_natural: "s' (E e) = V (s e)"
    and target_natural: "t' (E e) = V (t e)"
begin

lemma source_map [simp]: "source s' t' (map_dart E a) = V (source s t a)"
  by (cases a) (simp_all add: source_natural target_natural)

lemma target_map [simp]: "target s' t' (map_dart E a) = V (target s t a)"
  by (cases a) (simp_all add: source_natural target_natural)

lemma substitution_preserves_paths:
  "walk s t x p y \<Longrightarrow> walk s' t' (V x) (map (map_dart E) p) (V y)"
  by (induct rule: walk.induct) auto

lemma substitution_preserves_cancellation:
  "cancel p q \<Longrightarrow> cancel (map (map_dart E) p) (map (map_dart E) q)"
  by (induct rule: cancel.induct) (simp add: cancel.pair)

lemma substitution_preserves_equality:
  "path_equal s t x p q y \<Longrightarrow>
    path_equal s' t' (V x) (map (map_dart E) p) (map (map_dart E) q) (V y)"
  by (induct rule: path_equal.induct)
    (auto intro: path_equal.intros substitution_preserves_paths substitution_preserves_cancellation)

end

lemma graph_morphism_identity: "graph_morphism s t s t id id"
  by unfold_locales simp_all

lemma graph_morphism_composition:
  assumes "graph_morphism s t s' t' V E" "graph_morphism s' t' s'' t'' W K"
  shows "graph_morphism s t s'' t'' (W \<circ> V) (K \<circ> E)"
  using assms unfolding graph_morphism_def by auto

section \<open>Pullback of dependent families\<close>

locale family_reindexing = graph_family s' t' F up down +
  graph_morphism s t s' t' V E
  for s t :: "'e \<Rightarrow> 'v" and s' t' :: "'f \<Rightarrow> 'w"
    and F :: "'w \<Rightarrow> 'a set" and up down :: "'f \<Rightarrow> 'a \<Rightarrow> 'a"
    and V :: "'v \<Rightarrow> 'w" and E :: "'e \<Rightarrow> 'f"
begin

sublocale pullback: graph_family s t "F \<circ> V" "\<lambda>e. up (E e)" "\<lambda>e. down (E e)"
  by unfold_locales
    (simp_all add: up_type down_type down_up up_down source_natural[symmetric] target_natural[symmetric])

lemma step_transport_substitution:
  "pullback.step_transport a u = step_transport (map_dart E a) u"
  by (cases a) simp_all

lemma transport_substitution:
  "pullback.transport p u = transport (map (map_dart E) p) u"
  by (induct p arbitrary: u) (simp_all add: step_transport_substitution)

lemma dependent_section_substitution:
  assumes "dependent_section f"
  shows "pullback.dependent_section (f \<circ> V)"
  using assms
  unfolding dependent_section_def pullback.dependent_section_def
    point_section_def pullback.point_section_def
  by (auto simp: transport_substitution dest: substitution_preserves_paths)

end

end
