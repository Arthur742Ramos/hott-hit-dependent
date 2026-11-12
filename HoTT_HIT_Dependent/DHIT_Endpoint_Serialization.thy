theory DHIT_Endpoint_Serialization
  imports DHIT_Endpoint_Functor
begin

text \<open>Endpoint functoriality identifies the elementary argument-graph
interpretation with the original sequential endpoint action. The comparison
uses only the interchange presentation, not generator-naturality equations.\<close>

definition projected_motion where
  "projected_motion n p = map (\<lambda>i. path_image (coordinate_image i) p) [0..<n]"

lemma projected_motion_length [simp]: "length (projected_motion n p) = n"
  by (simp add: projected_motion_def)

lemma projected_motion_nth [simp]:
  "i < n \<Longrightarrow> projected_motion n p ! i = path_image (coordinate_image i) p"
  by (simp add: projected_motion_def)

lemma projected_motion_empty [simp]: "projected_motion n [] = replicate n []"
  by (rule nth_equalityI) (auto simp: projected_motion_def)

lemma projected_motion_append:
  "projected_motion n (p @ q) = map2 (@) (projected_motion n p) (projected_motion n q)"
  by (rule nth_equalityI) auto

lemma projected_motion_reverse:
  "projected_motion n (reverse_path p) = map reverse_path (projected_motion n p)"
  by (rule nth_equalityI) auto

context endpoint_functor
begin

lemma projected_elementary:
  assumes E: "a \<in> paths.argument_edges ss"
  shows "projected_motion (length ss) [Pos a] = paths.elementary_motion a"
proof -
  obtain bs zs before c after where A:
    "a = ArgumentEdge before c after" "ss = bs @ [Rec] @ zs"
    "parameter_arguments S h P bs before"
    "parameter_arguments S h P zs after" "c \<in> admitted"
    using E by (auto simp: paths.argument_edges_def)
  have L: "length ss = length before + 1 + length after"
    using A by (simp add: parameter_arguments_def)
  have C: "map (\<lambda>i. coordinate_image i (ArgumentEdge before c after))
    [0..<length (argument_source h s (ArgumentEdge before c after))] =
    replicate (length before) [] @ [[Pos c]] @ replicate (length after) []"
    by (rule coordinate_elementary)
  show ?thesis using C L
    by (simp add: A(1) paths.elementary_motion.simps projected_motion_def)
qed

lemma projected_signed_motion:
  assumes E: "dart_edge d \<in> paths.argument_edges ss"
  shows "paths.argument_motion ss
    (source (argument_source h s) (argument_source h t) d)
    (projected_motion (length ss) [d])
    (target (argument_source h s) (argument_source h t) d)"
proof (cases d)
  case (Pos a)
  show ?thesis using paths.elementary_motion_typed[of a ss] E
    by (simp add: Pos projected_elementary)
next
  case (Neg a)
  have A: "a \<in> paths.argument_edges ss" using E Neg by simp
  have R: "projected_motion (length ss) [Neg a] = map reverse_path (paths.elementary_motion a)"
    using projected_motion_reverse[of "length ss" "[Pos a]"] projected_elementary[OF A] by simp
  show ?thesis using argument_motion_inverse[OF paths.elementary_motion_typed[OF A]]
    by (simp add: Neg R)
qed

lemma projected_path_motion:
  assumes W: "walk_on (paths.argument_edges ss) (argument_source h s) (argument_source h t) xs p ys"
    and X: "parameter_arguments S h P ss xs"
  shows "paths.argument_motion ss xs (projected_motion (length ss) p) ys"
  using W X
proof (induct rule: walk_on_induct)
  case (nil x)
  show ?case using paths.argument_motion_identity[OF nil] nil
    by (simp add: parameter_arguments_def)
next
  case (cons d p y)
  note D = projected_signed_motion[OF cons(1)]
  note Y = paths.argument_motion_carriers(2)[OF D]
  note T = cons(3)[OF Y]
  show ?case using argument_motion_compose[OF D T]
    projected_motion_append[of "length ss" "[d]" p] by simp
qed

lemma elementary_endpoint_image:
  assumes endpoint: "wf_endpt S h ss e A"
    and E: "dart_edge d \<in> paths.argument_edges ss"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "eqp (instE h (source (argument_source h s) (argument_source h t) d) e)
    (path_image (\<lambda>a. endpoint_motion h (argument_source h s a) (argument_source h t a)
      (paths.elementary_motion a) e) [d])
    (endpoint_motion h (source (argument_source h s) (argument_source h t) d)
      (target (argument_source h s) (argument_source h t) d) (projected_motion (length ss) [d]) e)
    (instE h (target (argument_source h s) (argument_source h t) d) e)"
proof (cases d)
  case (Pos a)
  have AA: "a \<in> paths.argument_edges ss" using E Pos by simp
  note T = paths.endpoint_motion_typed[OF endpoint paths.elementary_motion_typed[OF AA] points]
  show ?thesis using presented_eq.refl[OF typed_motion_walk[OF T]]
    by (simp add: Pos projected_elementary[OF AA])
next
  case (Neg a)
  have AA: "a \<in> paths.argument_edges ss" using E Neg by simp
  have R: "projected_motion (length ss) [Neg a] = map reverse_path (paths.elementary_motion a)"
    using projected_motion_reverse[of "length ss" "[Pos a]"] projected_elementary[OF AA] by simp
  show ?thesis using presented_eq.sym[OF endpoint_motion_inverse[OF endpoint paths.elementary_motion_typed[OF AA] points]]
    by (simp add: Neg R)
qed

lemma endpoint_image_projected:
  assumes endpoint: "wf_endpt S h ss e A"
    and W: "walk_on (paths.argument_edges ss) (argument_source h s) (argument_source h t) xs p ys"
    and X: "parameter_arguments S h P ss xs"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "eqp (instE h xs e)
    (path_image (\<lambda>a. endpoint_motion h (argument_source h s a) (argument_source h t a)
      (paths.elementary_motion a) e) p)
    (endpoint_motion h xs ys (projected_motion (length ss) p) e) (instE h ys e)"
  using W X
proof (induct rule: walk_on_induct)
  case (nil x)
  have L: "length x = length ss" using nil by (simp add: parameter_arguments_def)
  show ?case by (simp add: L[symmetric] endpoint_motion_identity[OF endpoint L] presented_eq.refl)
next
  case (cons d p y)
  note D = projected_signed_motion[OF cons(1)]
  note Y = paths.argument_motion_carriers(2)[OF D]
  note T = projected_path_motion[OF cons(2) Y]
  note H = elementary_endpoint_image[OF endpoint cons(1) points]
  note IH = cons(3)[OF Y]
  note C = endpoint_motion_compose[OF endpoint D T points]
  note Q = presented_eq.trans[OF presented_eq.compose[OF H IH] presented_eq.sym[OF C]]
  show ?case using Q projected_motion_append[of "length ss" "[d]" p]
    by (cases d) simp_all
qed

lemma endpoint_motion_serialization:
  assumes endpoint: "wf_endpt S h ss e A"
    and M: "paths.argument_motion ss xs ps ys"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "eqp (instE h xs e)
    (path_image (\<lambda>a. endpoint_motion h (argument_source h s a) (argument_source h t a)
      (paths.elementary_motion a) e) (serialize_arguments [] xs ys ps))
    (endpoint_motion h xs ys ps e) (instE h ys e)"
proof -
  have L: "length xs = length ss" "length ys = length ss" "length ps = length ss"
    using M by (simp_all add: paths.argument_motion_def)
  have XY: "length xs = length ys" and XP: "length xs = length ps" using L by simp_all
  have P: "projected_motion (length ss) (serialize_arguments [] xs ys ps) = ps"
    using serialize_coordinates_recover[OF XY XP]
    by (simp add: projected_motion_def L)
  show ?thesis using endpoint_image_projected[OF endpoint paths.argument_motion_serialization[OF M]
    paths.argument_motion_carriers(1)[OF M] points] by (simp add: P)
qed

end
end
