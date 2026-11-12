theory DHIT_Quotient_Functor
  imports DHIT_Reindexing DHIT_Path_Quotient DHIT_Generator_Naturality
begin

section \<open>Reversing a presented naturality square\<close>

lemma presented_square_inverse:
  assumes L: "walk_on E s t x l y" and R: "walk_on E s t x' r y'"
    and A: "walk_on E s t x a x'" and B: "walk_on E s t y b y'"
    and H: "presented_eq E s t Q x (l @ b) (a @ r) y'"
  shows "presented_eq E s t Q y (reverse_path l @ a) (b @ reverse_path r) x'"
proof -
  have LR: "walk_on E s t y (reverse_path l) x" by (rule walk_on_reverse[OF L])
  have RR: "walk_on E s t y' (reverse_path r) x'" by (rule walk_on_reverse[OF R])
  have LB: "walk_on E s t y (b @ reverse_path r) x'" using B RR by auto
  have LA: "walk_on E s t y (reverse_path l @ a) x'" using LR A by auto
  have W: "presented_eq E s t Q y
      (reverse_path l @ (l @ b) @ reverse_path r)
      (reverse_path l @ (a @ r) @ reverse_path r) x'"
    by (rule presented_context[OF H LR RR])
  have left_reduce: "presented_eq E s t Q y
      (reverse_path l @ (l @ b) @ reverse_path r) (b @ reverse_path r) x'"
    using presented_context[OF presented_inverse_left[OF L],
      where l="[]" and r="b @ reverse_path r" and w=y and z=x'] LB
    by (simp add: append_assoc)
  have right_reduce: "presented_eq E s t Q y
      (reverse_path l @ (a @ r) @ reverse_path r) (reverse_path l @ a) x'"
    using presented_context[OF presented_inverse_right[OF R] LA,
      where r="[]" and z=x'] by (simp add: append_assoc)
  show ?thesis by (rule presented_eq.trans[OF presented_eq.sym[OF right_reduce]
    presented_eq.trans[OF presented_eq.sym[OF W] left_reduce]])
qed

section \<open>Path images preserve inverse cancellation\<close>

context path_interpretation
begin

lemma image_cancellation:
  assumes C: "cancel p q" and W: "walk_on E s t x p y"
  shows "presented_eq D u v Q (f x) (path_image L p) (path_image L q) (f y)"
proof -
  from C obtain a d b where P: "p = a @ d # inverse d # b" and Q: "q = a @ b"
    by (cases rule: cancel.cases) auto
  have A: "walk_on E s t x a (source s t d)"
    and D: "dart_edge d \<in> E" and B: "walk_on E s t (source s t d) b y"
    using W by (auto simp: P)
  have DD: "walk_on E s t (source s t d) [d] (target s t d)" using D by simp
  have Z: "presented_eq D u v Q (f (source s t d))
    (path_image L [d] @ reverse_path (path_image L [d])) [] (f (source s t d))"
    by (rule presented_inverse_right[OF image_typed[OF DD]])
  have K: "presented_eq D u v Q (f x)
      (path_image L a @ (path_image L [d] @ reverse_path (path_image L [d])) @ path_image L b)
      (path_image L a @ [] @ path_image L b) (f y)"
    by (rule presented_context[OF Z image_typed[OF A] image_typed[OF B]])
  show ?thesis using K by (cases d) (simp_all add: P Q append_assoc)
qed

end

section \<open>Maps of presented hom-set quotients\<close>

locale presented_path_map =
  path_interpretation E s t D u v f L +
  domain: path_presentation E s t R +
  codomain: path_presentation D u v Q
  for E :: "'e set" and s t :: "'e \<Rightarrow> 'v"
    and D :: "'d set" and u v :: "'d \<Rightarrow> 'w"
    and f :: "'v \<Rightarrow> 'w" and L :: "'e \<Rightarrow> 'd dart list"
    and R :: "'v \<Rightarrow> 'e dart list \<Rightarrow> 'e dart list \<Rightarrow> 'v \<Rightarrow> bool"
    and Q :: "'w \<Rightarrow> 'd dart list \<Rightarrow> 'd dart list \<Rightarrow> 'w \<Rightarrow> bool" +
  assumes relation_image:
    "R x p q y \<Longrightarrow> walk_on E s t x p y \<Longrightarrow> walk_on E s t x q y \<Longrightarrow>
      presented_eq D u v Q (f x) (path_image L p) (path_image L q) (f y)"
begin

lemma map_presented:
  "presented_eq E s t R x p q y \<Longrightarrow>
    presented_eq D u v Q (f x) (path_image L p) (path_image L q) (f y)"
proof (induction rule: presented_eq.induct)
  case (refl x p y) show ?case by (rule presented_eq.refl[OF image_typed[OF refl]])
next
  case (generator x p q y) show ?case by (rule relation_image[OF generator])
next
  case (cancel x p y q) show ?case by (rule image_cancellation[OF cancel(2,1)])
next
  case (sym x p q y) show ?case by (rule presented_eq.sym[OF sym.IH])
next
  case (trans x p q y r) show ?case by (rule presented_eq.trans[OF trans.IH])
next
  case (compose x p p' y q q' z)
  show ?case using presented_eq.compose[OF compose.IH] by simp
next
  case (inverse x p q y)
  show ?case using presented_eq.inverse[OF inverse.IH] by simp
qed

definition map_hom :: "'v \<Rightarrow> 'v \<Rightarrow> 'e dart list set \<Rightarrow> 'd dart list set" where
  "map_hom x y C = codomain.path_class (f x) (path_image L (domain.representative C)) (f y)"

lemma map_hom_class:
  assumes P: "walk_on E s t x p y"
  shows "map_hom x y (domain.path_class x p y) = codomain.path_class (f x) (path_image L p) (f y)"
  unfolding map_hom_def
  by (rule codomain.class_related[OF presented_eq.sym[OF map_presented[OF domain.representative_related[OF P]]]])

lemma map_hom_typed:
  "C \<in> domain.quotient_hom x y \<Longrightarrow> map_hom x y C \<in> codomain.quotient_hom (f x) (f y)"
  unfolding map_hom_def by (rule codomain.class_in_hom[OF image_typed[OF domain.representative_typed]])

lemma map_hom_identity:
  "map_hom x x (domain.qidentity x) = codomain.qidentity (f x)"
  using map_hom_class[of x "[]" x] by (simp add: domain.qidentity_def codomain.qidentity_def)

lemma map_hom_composition:
  assumes C: "C \<in> domain.quotient_hom x y" and H: "H \<in> domain.quotient_hom y z"
  shows "map_hom x z (domain.qcompose x y z C H) =
    codomain.qcompose (f x) (f y) (f z) (map_hom x y C) (map_hom y z H)"
proof -
  obtain p where P: "walk_on E s t x p y" and CP: "C = domain.path_class x p y"
    using C by (auto simp: domain.quotient_hom_def)
  obtain q where Q: "walk_on E s t y q z" and HQ: "H = domain.path_class y q z"
    using H by (auto simp: domain.quotient_hom_def)
  have PQ: "walk_on E s t x (p @ q) z" using P Q by auto
  show ?thesis by (simp add: CP HQ domain.qcompose_class[OF P Q]
    map_hom_class[OF P] map_hom_class[OF Q] map_hom_class[OF PQ]
    codomain.qcompose_class[OF image_typed[OF P] image_typed[OF Q]])
qed

lemma map_hom_inverse:
  assumes C: "C \<in> domain.quotient_hom x y"
  shows "map_hom y x (domain.qinverse x y C) = codomain.qinverse (f x) (f y) (map_hom x y C)"
proof -
  obtain p where P: "walk_on E s t x p y" and CP: "C = domain.path_class x p y"
    using C by (auto simp: domain.quotient_hom_def)
  show ?thesis by (simp add: CP domain.qinverse_class[OF P]
    map_hom_class[OF P] map_hom_class[OF walk_on_reverse[OF P]]
    codomain.qinverse_class[OF image_typed[OF P]])
qed

end

section \<open>Single-edge images cover constructor-shell lifts\<close>

lemma path_image_singletons:
  "path_image (\<lambda>e. [Pos (H e)]) p = map (map_dart H) p"
  by (induct "\<lambda>e. [Pos (H e)]" p rule: path_image.induct) simp_all

end
