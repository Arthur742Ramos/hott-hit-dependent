theory DHIT_Generator_Naturality
  imports DHIT_Parameter_Congruence
begin

section \<open>Interpreting argument paths in endpoint expressions\<close>

fun path_image :: "('e \<Rightarrow> 'd dart list) \<Rightarrow> 'e dart list \<Rightarrow> 'd dart list" where
  "path_image L [] = []"
| "path_image L (Pos e # p) = L e @ path_image L p"
| "path_image L (Neg e # p) = reverse_path (L e) @ path_image L p"

lemma path_image_append [simp]:
  "path_image L (p @ q) = path_image L p @ path_image L q"
  by (induct p; simp; rename_tac a p; case_tac a; simp)

lemma path_image_reverse [simp]:
  "path_image L (reverse_path p) = reverse_path (path_image L p)"
  by (induct p; simp; rename_tac a p; case_tac a; simp)

locale path_interpretation =
  fixes E :: "'e set" and s t :: "'e \<Rightarrow> 'v"
    and D :: "'d set" and u v :: "'d \<Rightarrow> 'w"
    and f :: "'v \<Rightarrow> 'w" and L :: "'e \<Rightarrow> 'd dart list"
  assumes edge_image: "e \<in> E \<Longrightarrow> walk_on D u v (f (s e)) (L e) (f (t e))"
begin

lemma image_typed:
  "walk_on E s t x p y \<Longrightarrow> walk_on D u v (f x) (path_image L p) (f y)"
proof (induct rule: walk_on_induct)
  case (nil x)
  then show ?case by simp
next
  case (cons d p y)
  then show ?case
    by (cases d) (auto intro: edge_image walk_on_reverse)
qed

end

section \<open>Naturality on generators implies naturality on all paths\<close>

context graph_family_on
begin

lemma transport_square_inverse:
  assumes L: "walk_on E s t x l y" and R: "walk_on E s t x' r y'"
    and A: "walk_on E s t x a x'" and B: "walk_on E s t y b y'"
    and square: "\<And>z. z \<in> F x \<Longrightarrow> transport b (transport l z) = transport r (transport a z)"
    and Z: "z \<in> F y"
  shows "transport a (transport (reverse_path l) z) =
    transport (reverse_path r) (transport b z)"
proof -
  have T: "transport (reverse_path l) z \<in> F x"
    by (rule transport_type[OF walk_on_reverse[OF L] Z])
  have AT: "transport a (transport (reverse_path l) z) \<in> F x'"
    by (rule transport_type[OF A T])
  have Q: "transport b z = transport r (transport a (transport (reverse_path l) z))"
    using square[OF T] transport_reverse_right[OF L Z] by simp
  show ?thesis using transport_reverse[OF R AT] Q by metis
qed

end

locale path_natural_family =
  left: path_interpretation E s t D u v f L +
  right: path_interpretation E s t D u v g R +
  fibers: graph_family_on D u v F up down
  for E :: "'e set" and s t :: "'e \<Rightarrow> 'v"
    and D :: "'d set" and u v :: "'d \<Rightarrow> 'w"
    and f g :: "'v \<Rightarrow> 'w" and L R :: "'e \<Rightarrow> 'd dart list"
    and F :: "'w \<Rightarrow> 'a set" and up down :: "'d \<Rightarrow> 'a \<Rightarrow> 'a" +
  fixes V :: "'v set" and component :: "'v \<Rightarrow> 'd dart list"
  assumes source_vertex: "e \<in> E \<Longrightarrow> s e \<in> V"
    and target_vertex: "e \<in> E \<Longrightarrow> t e \<in> V"
    and component_type: "x \<in> V \<Longrightarrow> walk_on D u v (f x) (component x) (g x)"
    and generator_square:
      "e \<in> E \<Longrightarrow> a \<in> F (f (s e)) \<Longrightarrow>
       fibers.transport (component (t e)) (fibers.transport (L e) a) =
       fibers.transport (R e) (fibers.transport (component (s e)) a)"
begin

lemma signed_generator_square:
  assumes DE: "dart_edge d \<in> E" and A: "a \<in> F (f (source s t d))"
  shows "fibers.transport (component (target s t d))
      (fibers.transport (path_image L [d]) a) =
    fibers.transport (path_image R [d])
      (fibers.transport (component (source s t d)) a)"
proof (cases d)
  case (Pos e)
  then show ?thesis using generator_square DE A by simp
next
  case (Neg e)
  have E: "e \<in> E" using DE Neg by simp
  have Z: "a \<in> F (f (t e))" using A Neg by simp
  note Q = fibers.transport_square_inverse[OF left.edge_image[OF E]
    right.edge_image[OF E] component_type[OF source_vertex[OF E]]
    component_type[OF target_vertex[OF E]] generator_square[OF E] Z]
  show ?thesis using Q by (simp add: Neg)
qed

lemma path_naturality:
  assumes W: "walk_on E s t x p y" and A: "a \<in> F (f x)"
  shows "fibers.transport (component y) (fibers.transport (path_image L p) a) =
    fibers.transport (path_image R p) (fibers.transport (component x) a)"
  using W A
proof (induct arbitrary: a rule: walk_on_induct)
  case (nil x)
  then show ?case by simp
next
  case (cons d p y)
  have W: "walk_on E s t (source s t d) [d] (target s t d)" using cons(1) by simp
  have T: "fibers.transport (path_image L [d]) a \<in> F (f (target s t d))"
    by (rule fibers.transport_type[OF left.image_typed[OF W] cons(4)])
  note IH = cons(3)[OF T]
  note Q = signed_generator_square[OF cons(1,4)]
  have PL: "path_image L (d # p) = path_image L [d] @ path_image L p"
    by (cases d) simp_all
  have PR: "path_image R (d # p) = path_image R [d] @ path_image R p"
    by (cases d) simp_all
  show ?case using IH Q by (simp add: PL PR)
qed

lemma walk_vertex:
  "walk_on E s t x p y \<Longrightarrow> x \<in> V \<Longrightarrow> y \<in> V"
proof (induct rule: walk_on_induct)
  case (nil x)
  then show ?case by simp
next
  case (cons d p y)
  have "target s t d \<in> V"
    using cons(1) by (cases d) (auto intro: source_vertex target_vertex)
  then show ?case by (rule cons(3))
qed

lemma square_paths_typed:
  assumes "walk_on E s t x p y" "x \<in> V"
  shows "walk_on D u v (f x) (path_image L p @ component y) (g y)"
    "walk_on D u v (f x) (component x @ path_image R p) (g y)"
  using left.image_typed[OF assms(1)] right.image_typed[OF assms(1)]
    component_type[OF assms(2)] component_type[OF walk_vertex[OF assms]] by auto

end

end
