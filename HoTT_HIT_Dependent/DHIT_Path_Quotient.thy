theory DHIT_Path_Quotient
  imports DHIT_Admissible_Paths
begin

section \<open>Typed presentations with additional path equations\<close>

inductive presented_eq :: "'e set \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow>
  ('v \<Rightarrow> 'e dart list \<Rightarrow> 'e dart list \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow>
  'v \<Rightarrow> 'e dart list \<Rightarrow> 'e dart list \<Rightarrow> 'v \<Rightarrow> bool"
  for E s t R where
  refl: "walk_on E s t x p y \<Longrightarrow> presented_eq E s t R x p p y"
| generator: "R x p q y \<Longrightarrow> walk_on E s t x p y \<Longrightarrow>
    walk_on E s t x q y \<Longrightarrow> presented_eq E s t R x p q y"
| cancel: "walk_on E s t x p y \<Longrightarrow> cancel p q \<Longrightarrow> presented_eq E s t R x p q y"
| sym: "presented_eq E s t R x p q y \<Longrightarrow> presented_eq E s t R x q p y"
| trans: "presented_eq E s t R x p q y \<Longrightarrow> presented_eq E s t R x q r y \<Longrightarrow>
    presented_eq E s t R x p r y"
| compose: "presented_eq E s t R x p p' y \<Longrightarrow> presented_eq E s t R y q q' z \<Longrightarrow>
    presented_eq E s t R x (p @ q) (p' @ q') z"
| inverse: "presented_eq E s t R x p q y \<Longrightarrow>
    presented_eq E s t R y (reverse_path p) (reverse_path q) x"

lemma presented_eq_typed:
  "presented_eq E s t R x p q y \<Longrightarrow> walk_on E s t x p y \<and> walk_on E s t x q y"
  by (induct rule: presented_eq.induct)
    (auto intro: walk_on_reverse dest: walk_on_cancel)

lemma equality_on_presented:
  "equality_on E s t x p q y \<Longrightarrow> presented_eq E s t R x p q y"
proof (induction rule: equality_on.induct)
  case (refl x p y) show ?case by (rule presented_eq.refl[OF refl])
next
  case (cancel x p y q) show ?case by (rule presented_eq.cancel[OF cancel])
next
  case (sym x p q y) show ?case by (rule presented_eq.sym[OF sym.IH])
next
  case (trans x p q y r) show ?case by (rule presented_eq.trans[OF trans.IH])
qed

lemma presented_context:
  assumes P: "presented_eq E s t R x p q y"
    and L: "walk_on E s t w l x" and Q: "walk_on E s t y r z"
  shows "presented_eq E s t R w (l @ p @ r) (l @ q @ r) z"
  by (rule presented_eq.compose[OF presented_eq.refl[OF L]
      presented_eq.compose[OF P presented_eq.refl[OF Q]]])

lemma presented_inverse_right:
  assumes W: "walk_on E s t x p y"
  shows "presented_eq E s t R x (p @ reverse_path p) [] x"
  using W
proof (induct rule: walk_on_induct)
  case (nil x) show ?case by (simp add: presented_eq.refl)
next
  case (cons d p y)
  have L: "walk_on E s t (source s t d) [d] (target s t d)" using cons(1) by simp
  have Q: "walk_on E s t (target s t d) [inverse d] (source s t d)" using cons(1) by simp
  have H: "presented_eq E s t R (source s t d)
      ([d] @ (p @ reverse_path p) @ [inverse d]) [d, inverse d] (source s t d)"
    using presented_context[OF cons(3) L Q] by simp
  have C: "cancel [d, inverse d] []" using cancel.pair[of "[]" d "[]"] by simp
  have W2: "walk_on E s t (source s t d) [d, inverse d] (source s t d)" using cons(1) by simp
  from presented_eq.trans[OF H presented_eq.cancel[OF W2 C]]
  show ?case by (simp add: append_assoc)
qed

lemma presented_inverse_left:
  "walk_on E s t x p y \<Longrightarrow>
    presented_eq E s t R y (reverse_path p @ p) [] y"
  using presented_inverse_right[OF walk_on_reverse] by simp

locale path_presentation =
  fixes E :: "'e set" and s t :: "'e \<Rightarrow> 'v"
    and R :: "'v \<Rightarrow> 'e dart list \<Rightarrow> 'e dart list \<Rightarrow> 'v \<Rightarrow> bool"
begin

definition path_class :: "'v \<Rightarrow> 'e dart list \<Rightarrow> 'v \<Rightarrow> 'e dart list set" where
  "path_class x p y = {q. presented_eq E s t R x p q y}"

definition quotient_hom :: "'v \<Rightarrow> 'v \<Rightarrow> 'e dart list set set" where
  "quotient_hom x y = {path_class x p y |p. walk_on E s t x p y}"

lemma class_self:
  "walk_on E s t x p y \<Longrightarrow> p \<in> path_class x p y"
  by (simp add: path_class_def presented_eq.refl)

lemma class_related:
  assumes H: "presented_eq E s t R x p q y"
  shows "path_class x p y = path_class x q y"
proof (rule set_eqI)
  fix r
  show "r \<in> path_class x p y \<longleftrightarrow> r \<in> path_class x q y"
    unfolding path_class_def mem_Collect_eq
    using presented_eq.sym[OF H] H by (meson presented_eq.trans)
qed

lemma class_equal_iff:
  assumes "walk_on E s t x p y" "walk_on E s t x q y"
  shows "path_class x p y = path_class x q y \<longleftrightarrow> presented_eq E s t R x p q y"
  using class_self[OF assms(2)] class_related unfolding path_class_def by blast

lemma class_in_hom:
  "walk_on E s t x p y \<Longrightarrow> path_class x p y \<in> quotient_hom x y"
  by (auto simp: quotient_hom_def)

text \<open>A representative is chosen only for an abstract quotient operation.
It is not an executable normalization algorithm. All operation laws below are
restricted to genuine hom-set classes, which are nonempty sets of typed paths.\<close>

definition representative :: "'e dart list set \<Rightarrow> 'e dart list" where
  "representative C = (SOME p. p \<in> C)"

lemma representative_member:
  assumes "C \<in> quotient_hom x y"
  shows "representative C \<in> C"
proof -
  from assms obtain p where W: "walk_on E s t x p y" and C: "C = path_class x p y"
    by (auto simp: quotient_hom_def)
  show ?thesis unfolding representative_def
    by (rule someI_ex) (use class_self[OF W] C in blast)
qed

lemma representative_typed:
  assumes H: "C \<in> quotient_hom x y"
  shows "walk_on E s t x (representative C) y"
proof -
  from H obtain p where C: "C = path_class x p y"
    by (auto simp: quotient_hom_def)
  have Q: "presented_eq E s t R x p (representative C) y"
    using representative_member[OF H] by (simp add: C path_class_def)
  show ?thesis using presented_eq_typed[OF Q] by simp
qed

lemma representative_class:
  assumes H: "C \<in> quotient_hom x y"
  shows "path_class x (representative C) y = C"
proof -
  from H obtain p where C: "C = path_class x p y"
    by (auto simp: quotient_hom_def)
  have Q: "presented_eq E s t R x p (representative C) y"
    using representative_member[OF H] by (simp add: C path_class_def)
  show ?thesis using class_related[OF Q] C by simp
qed

lemma member_represents:
  assumes H: "C \<in> quotient_hom x y" and M: "p \<in> C"
  shows "walk_on E s t x p y \<and> path_class x p y = C"
proof -
  from H obtain q where C: "C = path_class x q y"
    by (auto simp: quotient_hom_def)
  have Q: "presented_eq E s t R x q p y" using M by (simp add: C path_class_def)
  show ?thesis using presented_eq_typed[OF Q] class_related[OF Q] C by auto
qed

lemma empty_path_class:
  assumes E: "E = {}"
  shows "path_class x [] x = {[]}"
proof (rule set_eqI)
  fix q
  show "q \<in> path_class x [] x \<longleftrightarrow> q \<in> {[]}"
  proof
    assume "q \<in> path_class x [] x"
    then have Q: "presented_eq E s t R x [] q x" by (simp add: path_class_def)
    show "q \<in> {[]}" using presented_eq_typed[OF Q] E by simp
  next
    assume "q \<in> {[]}"
    then show "q \<in> path_class x [] x" using class_self[of x "[]" x] by simp
  qed
qed

lemma empty_quotient_hom:
  assumes E: "E = {}"
  shows "quotient_hom x y = (if x = y then {{[]}} else {})"
proof -
  have W: "\<And>p. walk_on E s t x p y \<longleftrightarrow> p = [] \<and> x = y"
    using E by simp
  show ?thesis unfolding quotient_hom_def
    by (auto simp: W empty_path_class[OF E])
qed

lemma representative_related:
  assumes W: "walk_on E s t x p y"
  shows "presented_eq E s t R x p (representative (path_class x p y)) y"
  using representative_member[OF class_in_hom[OF W]] by (simp add: path_class_def)

definition qidentity :: "'v \<Rightarrow> 'e dart list set" where
  "qidentity x = path_class x [] x"

definition qcompose :: "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow>
    'e dart list set \<Rightarrow> 'e dart list set \<Rightarrow> 'e dart list set" where
  "qcompose x y z C D = path_class x (representative C @ representative D) z"

definition qinverse :: "'v \<Rightarrow> 'v \<Rightarrow> 'e dart list set \<Rightarrow> 'e dart list set" where
  "qinverse x y C = path_class y (reverse_path (representative C)) x"

lemma qidentity_typed: "qidentity x \<in> quotient_hom x x"
  unfolding qidentity_def by (rule class_in_hom) simp

lemma qcompose_class:
  assumes P: "walk_on E s t x p y" and Q: "walk_on E s t y q z"
  shows "qcompose x y z (path_class x p y) (path_class y q z) = path_class x (p @ q) z"
  unfolding qcompose_def
  by (rule class_related[OF presented_eq.sym[OF presented_eq.compose[
        OF representative_related[OF P] representative_related[OF Q]]]])

lemma qinverse_class:
  assumes P: "walk_on E s t x p y"
  shows "qinverse x y (path_class x p y) = path_class y (reverse_path p) x"
  unfolding qinverse_def
  by (rule class_related[OF presented_eq.sym[OF presented_eq.inverse[OF representative_related[OF P]]]])

lemma qcompose_typed:
  "C \<in> quotient_hom x y \<Longrightarrow> D \<in> quotient_hom y z \<Longrightarrow>
    qcompose x y z C D \<in> quotient_hom x z"
  unfolding qcompose_def by (intro class_in_hom) (auto dest: representative_typed)

lemma qinverse_typed:
  "C \<in> quotient_hom x y \<Longrightarrow> qinverse x y C \<in> quotient_hom y x"
  unfolding qinverse_def by (intro class_in_hom walk_on_reverse) (rule representative_typed)

lemma qidentity_left:
  assumes C: "C \<in> quotient_hom x y"
  shows "qcompose x x y (qidentity x) C = C"
proof -
  obtain p where P: "walk_on E s t x p y" and CP: "C = path_class x p y"
    using C by (auto simp: quotient_hom_def)
  have N: "walk_on E s t x [] x" by simp
  show ?thesis using qcompose_class[OF N P] by (simp add: CP qidentity_def)
qed

lemma qidentity_right:
  assumes C: "C \<in> quotient_hom x y"
  shows "qcompose x y y C (qidentity y) = C"
proof -
  obtain p where P: "walk_on E s t x p y" and CP: "C = path_class x p y"
    using C by (auto simp: quotient_hom_def)
  have N: "walk_on E s t y [] y" by simp
  show ?thesis using qcompose_class[OF P N] by (simp add: CP qidentity_def)
qed

lemma qcompose_associative:
  assumes C: "C \<in> quotient_hom w x" and D: "D \<in> quotient_hom x y"
    and H: "H \<in> quotient_hom y z"
  shows "qcompose w y z (qcompose w x y C D) H = qcompose w x z C (qcompose x y z D H)"
proof -
  obtain p where P: "walk_on E s t w p x" and CP: "C = path_class w p x"
    using C by (auto simp: quotient_hom_def)
  obtain q where Q: "walk_on E s t x q y" and DQ: "D = path_class x q y"
    using D by (auto simp: quotient_hom_def)
  obtain r where T: "walk_on E s t y r z" and HR: "H = path_class y r z"
    using H by (auto simp: quotient_hom_def)
  have PQ: "walk_on E s t w (p @ q) y" using P Q by auto
  have QT: "walk_on E s t x (q @ r) z" using Q T by auto
  show ?thesis by (simp add: CP DQ HR qcompose_class[OF P Q]
    qcompose_class[OF Q T] qcompose_class[OF PQ T] qcompose_class[OF P QT] append_assoc)
qed

lemma qinverse_right:
  assumes C: "C \<in> quotient_hom x y"
  shows "qcompose x y x C (qinverse x y C) = qidentity x"
proof -
  obtain p where P: "walk_on E s t x p y" and CP: "C = path_class x p y"
    using C by (auto simp: quotient_hom_def)
  show ?thesis by (simp add: CP qinverse_class[OF P]
    qcompose_class[OF P walk_on_reverse[OF P]]
    class_related[OF presented_inverse_right[OF P]] qidentity_def)
qed

lemma qinverse_left:
  assumes C: "C \<in> quotient_hom x y"
  shows "qcompose y x y (qinverse x y C) C = qidentity y"
proof -
  obtain p where P: "walk_on E s t x p y" and CP: "C = path_class x p y"
    using C by (auto simp: quotient_hom_def)
  show ?thesis by (simp add: CP qinverse_class[OF P]
    qcompose_class[OF walk_on_reverse[OF P] P]
    class_related[OF presented_inverse_left[OF P]] qidentity_def)
qed

end

section \<open>Transport descends to the actual hom-set quotient\<close>

locale quotient_family = graph_family_on E s t F up down + path_presentation E s t R
  for E :: "'e set" and s t :: "'e \<Rightarrow> 'v" and F :: "'v \<Rightarrow> 'a set"
    and up down :: "'e \<Rightarrow> 'a \<Rightarrow> 'a"
    and R :: "'v \<Rightarrow> 'e dart list \<Rightarrow> 'e dart list \<Rightarrow> 'v \<Rightarrow> bool" +
  assumes relation_transport:
    "R x p q y \<Longrightarrow> walk_on E s t x p y \<Longrightarrow> walk_on E s t x q y \<Longrightarrow>
      a \<in> F x \<Longrightarrow> transport p a = transport q a"
begin

lemma reverse_transport_congruence:
  assumes P: "walk_on E s t x p y" and Q: "walk_on E s t x q y"
    and H: "\<And>a. a \<in> F x \<Longrightarrow> transport p a = transport q a"
    and A: "a \<in> F y"
  shows "transport (reverse_path p) a = transport (reverse_path q) a"
proof -
  have B: "transport (reverse_path p) a \<in> F x"
    by (rule transport_type[OF walk_on_reverse[OF P] A])
  have "transport q (transport (reverse_path p) a) = a"
    using H[OF B] transport_reverse_right[OF P A] by simp
  then show ?thesis using transport_reverse[OF Q B] by metis
qed

lemma presented_transport:
  "presented_eq E s t R x p q y \<Longrightarrow> a \<in> F x \<Longrightarrow>
    transport p a = transport q a"
proof (induction arbitrary: a rule: presented_eq.induct)
  case (refl x p y) show ?case by simp
next
  case (generator x p q y) show ?case by (rule relation_transport[OF generator.hyps generator.prems])
next
  case (cancel x p y q) show ?case by (rule transport_cancel[OF cancel.hyps(2,1) cancel.prems])
next
  case (sym x p q y) then show ?case by simp
next
  case (trans x p q y r) then show ?case by simp
next
  case (compose x p p' y q q' z)
  have P: "walk_on E s t x p y" using presented_eq_typed[OF compose.hyps(1)] by simp
  show ?case using compose.IH compose.prems transport_type[OF P compose.prems] by simp
next
  case (inverse x p q y)
  have P: "walk_on E s t x p y" and Q: "walk_on E s t x q y"
    using presented_eq_typed[OF inverse.hyps] by auto
  show ?case by (rule reverse_transport_congruence[OF P Q inverse.IH inverse.prems])
qed

definition quotient_transport :: "'v \<Rightarrow> 'v \<Rightarrow> 'e dart list set \<Rightarrow> 'a \<Rightarrow> 'a" where
  "quotient_transport x y C a = transport (representative C) a"

lemma quotient_transport_class:
  assumes P: "walk_on E s t x p y" and A: "a \<in> F x"
  shows "quotient_transport x y (path_class x p y) a = transport p a"
  using presented_transport[OF representative_related[OF P] A]
  by (simp add: quotient_transport_def)

lemma quotient_transport_member:
  assumes H: "C \<in> quotient_hom x y" and M: "p \<in> C" and A: "a \<in> F x"
  shows "quotient_transport x y C a = transport p a"
  using member_represents[OF H M] quotient_transport_class[OF _ A] by blast

lemma quotient_transport_bijective:
  assumes H: "C \<in> quotient_hom x y"
  shows "bij_betw (quotient_transport x y C) (F x) (F y)"
  unfolding quotient_transport_def by (rule transport_bijective[OF representative_typed[OF H]])

lemma quotient_transport_type:
  "C \<in> quotient_hom x y \<Longrightarrow> a \<in> F x \<Longrightarrow>
    quotient_transport x y C a \<in> F y"
  unfolding quotient_transport_def by (rule transport_type[OF representative_typed])

lemma quotient_transport_identity:
  "a \<in> F x \<Longrightarrow> quotient_transport x x (qidentity x) a = a"
  unfolding qidentity_def using quotient_transport_class[of x "[]" x a] by simp

lemma quotient_transport_composition:
  assumes C: "C \<in> quotient_hom x y" and D: "D \<in> quotient_hom y z" and A: "a \<in> F x"
  shows "quotient_transport x z (qcompose x y z C D) a =
    quotient_transport y z D (quotient_transport x y C a)"
proof -
  have W: "walk_on E s t x (representative C @ representative D) z"
    using representative_typed[OF C] representative_typed[OF D] by auto
  show ?thesis unfolding qcompose_def using quotient_transport_class[OF W A]
    by (simp add: quotient_transport_def)
qed

lemma quotient_transport_inverse:
  assumes C: "C \<in> quotient_hom x y" and A: "a \<in> F x"
  shows "quotient_transport y x (qinverse x y C) (quotient_transport x y C a) = a"
  using quotient_transport_composition[OF C qinverse_typed[OF C] A]
    quotient_transport_identity[OF A] qinverse_right[OF C] by simp

lemma section_descends:
  assumes S: "section_on f" and C: "C \<in> quotient_hom x y"
  shows "quotient_transport x y C (f x) = f y"
  using S representative_typed[OF C]
  unfolding quotient_transport_def section_on_def by blast

end

end
