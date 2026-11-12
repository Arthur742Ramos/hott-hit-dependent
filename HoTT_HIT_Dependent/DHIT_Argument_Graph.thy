theory DHIT_Argument_Graph
  imports DHIT_Endpoint_Paths
begin

text \<open>Elementary argument edges change exactly one recursive slot. Parameter
slots are opaque and fixed. Serialization below decomposes a simultaneous tuple
motion into a genuine path of elementary moves; it asserts no endpoint-functor
composition law.\<close>

datatype 'e argument_edge = ArgumentEdge "tm list" "'e constructor_edge" "tm list"

fun argument_source where
  "argument_source h s (ArgumentEdge before c after) =
    before @ [context_endpoint h s c] @ after"

fun serialize_arguments where
  "serialize_arguments before [] ys ps = []"
| "serialize_arguments before (x # xs) ys ps =
    map (map_dart (\<lambda>c. ArgumentEdge before c xs)) (hd ps) @
    serialize_arguments (before @ [hd ys]) xs (tl ys) (tl ps)"

context parameter_path_structure
begin

definition argument_edges where
  "argument_edges ss = {a. \<exists>bs zs before c after.
    a = ArgumentEdge before c after \<and> ss = bs @ [Rec] @ zs \<and>
    parameter_arguments S h P bs before \<and>
    parameter_arguments S h P zs after \<and> c \<in> admitted}"

lemma argument_edge_carriers:
  assumes "a \<in> argument_edges ss"
  shows "parameter_arguments S h P ss (argument_source h s a)"
    "parameter_arguments S h P ss (argument_source h t a)"
proof -
  obtain bs zs before c after where A:
    "a = ArgumentEdge before c after" "ss = bs @ [Rec] @ zs"
    "parameter_arguments S h P bs before"
    "parameter_arguments S h P zs after" "c \<in> admitted"
    using assms by (auto simp: argument_edges_def)
  have X: "parameter_tree S h P (cs c)" and Y: "parameter_tree S h P (ct c)"
    using parameter_context_endpoint_tree[OF _ source_tree] parameter_context_endpoint_tree[OF _ target_tree] A(5) by auto
  have RX: "parameter_arguments S h P [Rec] [cs c]"
    and RY: "parameter_arguments S h P [Rec] [ct c]"
    using X Y by (simp_all add: parameter_arguments_def external_arity_def parameter_carrier_def)
  show "parameter_arguments S h P ss (argument_source h s a)"
    using parameter_arguments_append[OF A(3) parameter_arguments_append[OF RX A(4)]] by (simp add: A)
  show "parameter_arguments S h P ss (argument_source h t a)"
    using parameter_arguments_append[OF A(3) parameter_arguments_append[OF RY A(4)]] by (simp add: A)
qed

lemma argument_coordinate_lift:
  assumes W: "walk_on admitted cs ct x p y"
    and shape: "ss = bs @ [Rec] @ zs"
    and B: "parameter_arguments S h P bs before"
    and Z: "parameter_arguments S h P zs after"
  shows "walk_on (argument_edges ss) (argument_source h s) (argument_source h t)
    (before @ [x] @ after)
    (map (map_dart (\<lambda>c. ArgumentEdge before c after)) p)
    (before @ [y] @ after)"
  using W
proof (induct rule: walk_on_induct)
  case (nil x)
  then show ?case by simp
next
  case (cons d p y)
  have V: "\<And>c. c \<in> admitted \<Longrightarrow> ArgumentEdge before c after \<in> argument_edges ss"
    using shape B Z by (auto simp: argument_edges_def)
  show ?case using cons V by (cases d) auto
qed

lemma serialize_arguments_typed_prefix:
  assumes shape: "ss0 = bs @ ss"
    and B: "parameter_arguments S h P bs before"
    and A: "argument_motion ss xs ps ys"
  shows "walk_on (argument_edges ss0) (argument_source h s) (argument_source h t)
    (before @ xs) (serialize_arguments before xs ys ps) (before @ ys)"
  using shape B A
proof (induct ss arbitrary: bs before xs ps ys)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  obtain x xt p pt y yt where X: "xs = x # xt" and Q: "ps = p # pt" and Y: "ys = y # yt"
    using Cons.prems(3) unfolding argument_motion_def by (cases xs; cases ps; cases ys) auto
  have ext: "external_arity h [r]" and T: "typed_motion (argTy h r) x p y"
    and tail: "argument_motion rs xt pt yt"
    using Cons.prems(3) by (simp_all add: X Q Y argument_motion_cons)
  have YB: "parameter_arguments S h P [r] [y]"
    using ext T by (simp add: parameter_arguments_def typed_motion_def)
  have BT: "parameter_arguments S h P (bs @ [r]) (before @ [y])"
    by (rule parameter_arguments_append[OF Cons.prems(2) YB])
  have sh: "ss0 = (bs @ [r]) @ rs" using Cons.prems(1) by simp
  note IH = Cons.hyps[OF sh BT tail]
  show ?case
  proof (cases r)
    case Rec
    have shape: "ss0 = bs @ [Rec] @ rs" using Cons.prems(1) Rec by simp
    have W: "walk_on admitted cs ct x p y" using T Rec by (simp add: typed_motion_def)
    note L = argument_coordinate_lift[OF W shape Cons.prems(2) argument_motion_carriers(1)[OF tail]]
    show ?thesis using L IH by (auto simp: X Q Y)
  next
    case (Par j)
    have J: "j \<noteq> h" using ext Par by (simp add: external_arity_def)
    have "x = y" "p = []" using T J Par by (auto simp: typed_motion_def)
    then show ?thesis using IH by (simp add: X Q Y)
  qed
qed

lemma argument_motion_serialization:
  assumes "argument_motion ss xs ps ys"
  shows "walk_on (argument_edges ss) (argument_source h s) (argument_source h t)
    xs (serialize_arguments [] xs ys ps) ys"
proof -
  have B: "parameter_arguments S h P [] []"
    by (simp add: parameter_arguments_def external_arity_def)
  show ?thesis using serialize_arguments_typed_prefix[OF _ B assms, of ss] by simp
qed


lemma argument_motion_identity:
  assumes "parameter_arguments S h P ss xs"
  shows "argument_motion ss xs (replicate (length xs) []) xs"
  using assms by (auto simp: argument_motion_def parameter_arguments_def typed_motion_def)

lemma argument_motion_append:
  assumes "argument_motion bs xs ps ys" "argument_motion zs us qs vs"
  shows "argument_motion (bs @ zs) (xs @ us) (ps @ qs) (ys @ vs)"
  using assms by (auto simp: argument_motion_def external_arity_def nth_append)

fun elementary_motion where
  "elementary_motion (ArgumentEdge before c after) =
    replicate (length before) [] @ [[Pos c]] @ replicate (length after) []"

lemma elementary_motion_typed:
  assumes "a \<in> argument_edges ss"
  shows "argument_motion ss (argument_source h s a) (elementary_motion a) (argument_source h t a)"
proof -
  obtain bs zs before c after where A:
    "a = ArgumentEdge before c after" "ss = bs @ [Rec] @ zs"
    "parameter_arguments S h P bs before"
    "parameter_arguments S h P zs after" "c \<in> admitted"
    using assms by (auto simp: argument_edges_def)
  have X: "parameter_tree S h P (cs c)" and Y: "parameter_tree S h P (ct c)"
    using parameter_context_endpoint_tree[OF _ source_tree] parameter_context_endpoint_tree[OF _ target_tree] A(5) by auto
  have R: "argument_motion [Rec] [cs c] [[Pos c]] [ct c]"
    using X Y A(5) by (auto simp: argument_motion_def external_arity_def typed_motion_def parameter_carrier_def)
  show ?thesis
    using argument_motion_append[OF argument_motion_identity[OF A(3)]
      argument_motion_append[OF R argument_motion_identity[OF A(4)]]]
    by (simp add: A)
qed

text \<open>Each original endpoint therefore maps an elementary recursive move
into a typed path. Functoriality for composites is deliberately separate.\<close>
lemma elementary_endpoint_typed:
  assumes edge: "a \<in> argument_edges ss"
    and endpoint: "wf_endpt S h ss e A"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "typed_motion A (instE h (argument_source h s a) e)
    (endpoint_motion h (argument_source h s a) (argument_source h t a) (elementary_motion a) e)
    (instE h (argument_source h t a) e)"
  by (rule endpoint_motion_typed[OF endpoint elementary_motion_typed[OF edge] points])


lemma elementary_endpoint_interpretation:
  assumes endpoint: "wf_endpt S h ss e (Hit h)"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "path_interpretation (argument_edges ss) (argument_source h s) (argument_source h t)
    admitted cs ct (\<lambda>xs. instE h xs e)
    (\<lambda>a. endpoint_motion h (argument_source h s a) (argument_source h t a) (elementary_motion a) e)"
  apply unfold_locales
  using elementary_endpoint_typed[OF _ endpoint points]
  by (simp add: typed_motion_def)

end

section \<open>Coordinate projection and exact recovery\<close>

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
proof (induct p)
  case Nil
  then show ?case by simp
next
  case (Cons d p)
  then show ?case by (cases d; cases "i = length before") simp_all
qed

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
