theory DHIT_Argument_Projection
  imports DHIT_Argument_Graph
begin

text \<open>Projection of an elementary tuple edge either retains its signed
coordinate move or deletes it. Serialization retains each coordinate word
exactly, not merely up to cancellation or the presented equations.\<close>

fun coordinate_image :: "nat \<Rightarrow> 'e argument_edge \<Rightarrow> 'e constructor_edge dart list" where
  "coordinate_image i (ArgumentEdge before c after) =
    (if i = length before then [Pos c] else [])"

lemma coordinate_image_lift [simp]:
  "path_image (coordinate_image i)
    (map (map_dart (\<lambda>c. ArgumentEdge before c after)) p) =
    (if i = length before then p else [])"
  by (cases "i = length before"; induct p; simp; rename_tac d p; case_tac d; simp)

lemma serialize_coordinate_outside:
  assumes "length xs = length ys" "length xs = length ps"
    "i < length before \<or> length before + length xs \<le> i"
  shows "path_image (coordinate_image i) (serialize_arguments before xs ys ps) = []"
  using assms
proof (induct xs arbitrary: before ys ps i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain y yt p pt where Y: "ys = y # yt" and P: "ps = p # pt"
    using Cons.prems by (cases ys; cases ps) auto
  have L: "length xs = length yt" "length xs = length pt"
    using Cons.prems by (simp_all add: Y P)
  have I: "i < length (before @ [y]) \<or> length (before @ [y]) + length xs \<le> i"
    using Cons.prems(3) by auto
  have N: "i \<noteq> length before" using Cons.prems(3) by auto
  show ?case using Cons.hyps[OF L I] N by (simp add: Y P)
qed

lemma serialize_coordinate_prefix:
  assumes "length xs = length ys" "length xs = length ps" "i < length xs"
  shows "path_image (coordinate_image (length before + i))
    (serialize_arguments before xs ys ps) = ps ! i"
  using assms
proof (induct xs arbitrary: before ys ps i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain y yt p pt where Y: "ys = y # yt" and P: "ps = p # pt"
    using Cons.prems by (cases ys; cases ps) auto
  have L: "length xs = length yt" "length xs = length pt"
    using Cons.prems by (simp_all add: Y P)
  show ?case
  proof (cases i)
    case 0
    have O: "path_image (coordinate_image (length before))
      (serialize_arguments (before @ [y]) xs yt pt) = []"
      by (rule serialize_coordinate_outside[OF L]) simp
    show ?thesis using O by (simp add: 0 Y P)
  next
    case (Suc j)
    have J: "j < length xs" using Cons.prems(3) Suc by simp
    show ?thesis using Cons.hyps[OF L J, of "before @ [y]"]
      by (simp add: Suc Y P add.assoc)
  qed
qed

lemma serialize_coordinate_projection:
  assumes "length xs = length ys" "length xs = length ps" "i < length xs"
  shows "path_image (coordinate_image i) (serialize_arguments [] xs ys ps) = ps ! i"
  using serialize_coordinate_prefix[OF assms, of "[]"] by simp

lemma serialize_coordinates_recover:
  assumes "length xs = length ys" "length xs = length ps"
  shows "map (\<lambda>i. path_image (coordinate_image i)
    (serialize_arguments [] xs ys ps)) [0..<length xs] = ps"
proof (rule nth_equalityI)
  show "length (map (\<lambda>i. path_image (coordinate_image i)
    (serialize_arguments [] xs ys ps)) [0..<length xs]) = length ps"
    using assms by simp
  fix i
  assume "i < length (map (\<lambda>i. path_image (coordinate_image i)
    (serialize_arguments [] xs ys ps)) [0..<length xs])"
  then have I: "i < length xs" by simp
  show "map (\<lambda>i. path_image (coordinate_image i)
    (serialize_arguments [] xs ys ps)) [0..<length xs] ! i = ps ! i"
    using serialize_coordinate_projection[OF assms I] I by simp
qed

lemma coordinate_elementary:
  "map (\<lambda>i. coordinate_image i (ArgumentEdge before c after))
    [0..<length (argument_source h s (ArgumentEdge before c after))] =
    replicate (length before) [] @ [[Pos c]] @ replicate (length after) []"
  by (rule nth_equalityI)
    (auto simp: nth_append nth_Cons split: nat.splits)


end
