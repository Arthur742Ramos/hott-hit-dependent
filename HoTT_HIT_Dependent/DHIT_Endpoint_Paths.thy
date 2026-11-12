theory DHIT_Endpoint_Paths
  imports DHIT_Generator_Naturality
begin

section \<open>Path action of the original endpoint syntax\<close>

fun constructor_motion :: "nat \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow>
    'e constructor_edge dart list list \<Rightarrow> 'e constructor_edge dart list" where
  "constructor_motion k before [] ys ps = []"
| "constructor_motion k before (x # xs) ys ps =
    map (map_dart (\<lambda>c. Under k before c xs)) (hd ps) @
    constructor_motion k (before @ [hd ys]) xs (tl ys) (tl ps)"

primrec endpoint_motion :: "nat \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow>
    'e constructor_edge dart list list \<Rightarrow> endpt \<Rightarrow> 'e constructor_edge dart list" where
  "endpoint_motion h xs ys ps (EArg i) = ps ! i"
| "endpoint_motion h xs ys ps (ECon k es) =
    constructor_motion k [] (map (instE h xs) es) (map (instE h ys) es)
      (map (endpoint_motion h xs ys ps) es)"

locale parameter_path_structure =
  fixes S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set"
    and E :: "'e set" and s t :: "'e \<Rightarrow> tm"
  assumes source_tree: "e \<in> E \<Longrightarrow> parameter_tree S h P (s e)"
    and target_tree: "e \<in> E \<Longrightarrow> parameter_tree S h P (t e)"
begin

abbreviation admitted where "admitted \<equiv> {c. valid_parameter_context S h P E c}"
abbreviation cs where "cs \<equiv> context_endpoint h s"
abbreviation ct where "ct \<equiv> context_endpoint h t"

definition typed_motion :: "ty \<Rightarrow> tm \<Rightarrow> 'e constructor_edge dart list \<Rightarrow> tm \<Rightarrow> bool" where
  "typed_motion A x p y \<longleftrightarrow>
    parameter_carrier S h P A x \<and> parameter_carrier S h P A y \<and>
    (if A = Hit h then walk_on admitted cs ct x p y else x = y \<and> p = [])"

definition argument_motion :: "argspec list \<Rightarrow> tm list \<Rightarrow>
    'e constructor_edge dart list list \<Rightarrow> tm list \<Rightarrow> bool" where
  "argument_motion ss xs ps ys \<longleftrightarrow> external_arity h ss \<and>
    length xs = length ss \<and> length ys = length ss \<and> length ps = length ss \<and>
    (\<forall>i < length ss. typed_motion (argTy h (ss ! i)) (xs ! i) (ps ! i) (ys ! i))"

lemma argument_motion_nil [simp]: "argument_motion [] xs ps ys \<longleftrightarrow> xs = [] \<and> ps = [] \<and> ys = []"
  by (auto simp: argument_motion_def external_arity_def)

lemma argument_motion_cons:
  "argument_motion (r # rs) (x # xs) (p # ps) (y # ys) \<longleftrightarrow>
    external_arity h [r] \<and> typed_motion (argTy h r) x p y \<and> argument_motion rs xs ps ys"
  by (auto simp: argument_motion_def external_arity_def less_Suc_eq_0_disj)

lemma argument_motion_carriers:
  assumes "argument_motion ss xs ps ys"
  shows "parameter_arguments S h P ss xs" "parameter_arguments S h P ss ys"
  using assms by (auto simp: argument_motion_def parameter_arguments_def typed_motion_def)

lemma lift_motion:
  assumes W: "walk_on admitted cs ct x p y"
    and slot: "parameter_slot S h P k before after"
  shows "walk_on admitted cs ct (PCon h k (before @ [x] @ after))
    (map (map_dart (\<lambda>c. Under k before c after)) p)
    (PCon h k (before @ [y] @ after))"
  using W
proof (induct rule: walk_on_induct)
  case (nil x)
  then show ?case by simp
next
  case (cons d p y)
  have V: "\<And>c. valid_parameter_context S h P E c \<Longrightarrow>
    valid_parameter_context S h P E (Under k before c after)"
    by (rule valid_parameter_context.under) (use slot in auto)
  show ?case using cons V by (cases d) auto
qed

lemma constructor_motion_typed:
  assumes K: "k < length (pcons (S h))" and shape: "pcons (S h) ! k = bs @ ss"
    and B: "parameter_arguments S h P bs before"
    and A: "argument_motion ss xs ps ys"
  shows "walk_on admitted cs ct (PCon h k (before @ xs))
    (constructor_motion k before xs ys ps) (PCon h k (before @ ys))"
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
  have XB: "parameter_arguments S h P [r] [x]" and YB: "parameter_arguments S h P [r] [y]"
    using ext T by (simp_all add: parameter_arguments_def typed_motion_def)
  have BT: "parameter_arguments S h P (bs @ [r]) (before @ [y])"
    by (rule parameter_arguments_append[OF Cons.prems(2) YB])
  have sh: "pcons (S h) ! k = (bs @ [r]) @ rs" using Cons.prems(1) by simp
  note IH = Cons.hyps[OF sh BT tail]
  show ?case
  proof (cases r)
    case Rec
    have slot: "parameter_slot S h P k before xt"
      unfolding parameter_slot_def
      using K Cons.prems(1,2) argument_motion_carriers(1)[OF tail] Rec by auto
    have W: "walk_on admitted cs ct x p y" using T Rec by (simp add: typed_motion_def)
    note L = lift_motion[OF W slot]
    show ?thesis using L IH by (auto simp: X Q Y)
  next
    case (Par j)
    have J: "j \<noteq> h" using ext Par by (simp add: external_arity_def)
    have "x = y" "p = []" using T J Par by (auto simp: typed_motion_def)
    then show ?thesis using IH by (simp add: X Q Y)
  qed
qed


lemma endpoint_motion_typed:
  assumes endpoint: "wf_endpt S h ss e A"
    and motion: "argument_motion ss xs ps ys"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "typed_motion A (instE h xs e) (endpoint_motion h xs ys ps e) (instE h ys e)"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  show ?case using motion wfEArg by (simp add: argument_motion_def)
next
  case (wfECon k es)
  have M: "argument_motion (pcons (S h) ! k) (map (instE h xs) es)
      (map (endpoint_motion h xs ys ps) es) (map (instE h ys) es)"
    using wfECon points[OF wfECon(1)] by (auto simp: argument_motion_def)
  have X: "parameter_tree S h P (PCon h k (map (instE h xs) es))"
    by (rule parameter_arguments_node[OF wfECon(1) argument_motion_carriers(1)[OF M]])
  have Y: "parameter_tree S h P (PCon h k (map (instE h ys) es))"
    by (rule parameter_arguments_node[OF wfECon(1) argument_motion_carriers(2)[OF M]])
  have B: "parameter_arguments S h P [] []"
    by (simp add: parameter_arguments_def external_arity_def)
  have W: "walk_on admitted cs ct (PCon h k (map (instE h xs) es))
    (constructor_motion k [] (map (instE h xs) es) (map (instE h ys) es)
      (map (endpoint_motion h xs ys ps) es)) (PCon h k (map (instE h ys) es))"
    using constructor_motion_typed[OF wfECon(1) _ B M] by simp
  show ?case using X Y W by (simp add: typed_motion_def parameter_carrier_def)
qed

end


section \<open>Canonical instances include changed constructor arguments\<close>

definition signature_edges :: "sigenv \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tm set) \<Rightarrow> (nat \<times> tm list) set" where
  "signature_edges S h P = {(k,xs). k < length (lcons (S h)) \<and>
    parameter_arguments S h P (lcons (S h) ! k) xs}"

locale signature_path_structure =
  fixes S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set"
  assumes signature: "wf_hsig S h"
    and external_points: "k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
begin

abbreviation src where "src e \<equiv> lhsOf S h (fst e) (snd e)"
abbreviation dst where "dst e \<equiv> rhsOf S h (fst e) (snd e)"
abbreviation edges where "edges \<equiv> signature_edges S h P"

lemma source_tree:
  assumes "e \<in> edges"
  shows "parameter_tree S h P (src e)"
proof -
  have K: "fst e < length (lcons (S h))" and A: "parameter_arguments S h P (lcons (S h) ! fst e) (snd e)"
    using assms by (auto simp: signature_edges_def)
  show ?thesis using endpoint_parameter_carrier[OF wf_hsig_lhs[OF signature K] A external_points]
    by (simp add: lhsOf_def parameter_carrier_def)
qed

lemma target_tree:
  assumes "e \<in> edges"
  shows "parameter_tree S h P (dst e)"
proof -
  have K: "fst e < length (lcons (S h))" and A: "parameter_arguments S h P (lcons (S h) ! fst e) (snd e)"
    using assms by (auto simp: signature_edges_def)
  show ?thesis using endpoint_parameter_carrier[OF wf_hsig_rhs[OF signature K] A external_points]
    by (simp add: rhsOf_def parameter_carrier_def)
qed

sublocale paths: parameter_path_structure S h P edges src dst
  by (unfold_locales) (auto intro: source_tree target_tree)

lemma canonical_generator_typed:
  assumes K: "k < length (lcons (S h))"
    and A: "parameter_arguments S h P (lcons (S h) ! k) xs"
  shows "walk_on paths.admitted paths.cs paths.ct (lhsOf S h k xs)
    [Pos (Generator (k,xs))] (rhsOf S h k xs)"
  using K A by (auto simp: signature_edges_def intro: valid_parameter_context.generator)

lemma original_endpoint_paths:
  assumes K: "k < length (lcons (S h))"
    and A: "paths.argument_motion (lcons (S h) ! k) xs ps ys"
  shows "walk_on paths.admitted paths.cs paths.ct (lhsOf S h k xs)
      (endpoint_motion h xs ys ps (fst (lends (S h) ! k))) (lhsOf S h k ys)"
    "walk_on paths.admitted paths.cs paths.ct (rhsOf S h k xs)
      (endpoint_motion h xs ys ps (snd (lends (S h) ! k))) (rhsOf S h k ys)"
  using paths.endpoint_motion_typed[OF wf_hsig_lhs[OF signature K] A external_points]
    paths.endpoint_motion_typed[OF wf_hsig_rhs[OF signature K] A external_points]
  unfolding paths.typed_motion_def
  by (simp_all add: lhsOf_def rhsOf_def)

end


section \<open>Naturality of canonical path constructors\<close>

locale signature_generator_naturality = signature_path_structure S h P +
  fibers: graph_family_on
    "{c. valid_parameter_context S h P (signature_edges S h P) c}"
    "context_endpoint h (\<lambda>e. lhsOf S h (fst e) (snd e))"
    "context_endpoint h (\<lambda>e. rhsOf S h (fst e) (snd e))" F up down
  for S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set"
    and F :: "tm \<Rightarrow> 'a set"
    and up down :: "(nat \<times> tm list) constructor_edge \<Rightarrow> 'a \<Rightarrow> 'a" +
  fixes k :: nat and A :: "'b set" and arg_source arg_target :: "'b \<Rightarrow> tm list"
    and moves :: "'b \<Rightarrow> (nat \<times> tm list) constructor_edge dart list list"
  assumes constructor_bound: "k < length (lcons (S h))"
    and argument_moves: "e \<in> A \<Longrightarrow>
      paths.argument_motion (lcons (S h) ! k) (arg_source e) (moves e) (arg_target e)"
    and local_square:
      "e \<in> A \<Longrightarrow> a \<in> F (lhsOf S h k (arg_source e)) \<Longrightarrow>
       fibers.transport [Pos (Generator (k, arg_target e))]
         (fibers.transport (endpoint_motion h (arg_source e) (arg_target e) (moves e)
           (fst (lends (S h) ! k))) a) =
       fibers.transport (endpoint_motion h (arg_source e) (arg_target e) (moves e)
           (snd (lends (S h) ! k)))
         (fibers.transport [Pos (Generator (k, arg_source e))] a)"
begin

abbreviation left_motion where
  "left_motion e \<equiv> endpoint_motion h (arg_source e) (arg_target e) (moves e) (fst (lends (S h) ! k))"
abbreviation right_motion where
  "right_motion e \<equiv> endpoint_motion h (arg_source e) (arg_target e) (moves e) (snd (lends (S h) ! k))"

sublocale natural: path_natural_family A arg_source arg_target paths.admitted paths.cs paths.ct
  "lhsOf S h k" "rhsOf S h k" left_motion right_motion F up down
  "{xs. parameter_arguments S h P (lcons (S h) ! k) xs}"
  "\<lambda>xs. [Pos (Generator (k,xs))]"
proof
  fix e assume E: "e \<in> A"
  show "walk_on paths.admitted paths.cs paths.ct (lhsOf S h k (arg_source e))
      (left_motion e) (lhsOf S h k (arg_target e))"
    by (rule original_endpoint_paths(1)[OF constructor_bound argument_moves[OF E]])
next
  fix e assume E: "e \<in> A"
  show "walk_on paths.admitted paths.cs paths.ct (rhsOf S h k (arg_source e))
      (right_motion e) (rhsOf S h k (arg_target e))"
    by (rule original_endpoint_paths(2)[OF constructor_bound argument_moves[OF E]])
next
  fix e assume "e \<in> A"
  then show "arg_source e \<in> {xs. parameter_arguments S h P (lcons (S h) ! k) xs}"
    using paths.argument_motion_carriers(1)[OF argument_moves] by auto
next
  fix e assume "e \<in> A"
  then show "arg_target e \<in> {xs. parameter_arguments S h P (lcons (S h) ! k) xs}"
    using paths.argument_motion_carriers(2)[OF argument_moves] by auto
next
  fix xs assume "xs \<in> {xs. parameter_arguments S h P (lcons (S h) ! k) xs}"
  then show "walk_on paths.admitted paths.cs paths.ct (lhsOf S h k xs)
    [Pos (Generator (k,xs))] (rhsOf S h k xs)"
    by (intro canonical_generator_typed constructor_bound) simp
next
  fix e a assume "e \<in> A" "a \<in> F (lhsOf S h k (arg_source e))"
  then show "fibers.transport [Pos (Generator (k,arg_target e))] (fibers.transport (left_motion e) a) =
    fibers.transport (right_motion e) (fibers.transport [Pos (Generator (k,arg_source e))] a)"
    by (rule local_square)
qed

lemma original_generator_path_naturality:
  assumes "walk_on A arg_source arg_target xs p ys" "a \<in> F (lhsOf S h k xs)"
  shows "fibers.transport [Pos (Generator (k,ys))] (fibers.transport (path_image left_motion p) a) =
    fibers.transport (path_image right_motion p) (fibers.transport [Pos (Generator (k,xs))] a)"
  by (rule natural.path_naturality[OF assms])

end

end
