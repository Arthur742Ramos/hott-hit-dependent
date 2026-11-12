theory DHIT_Constructor_Congruence
  imports DHIT_Displayed_Algebra DHIT_Admissible_Paths
begin

section \<open>Constructor contexts around generating paths\<close>

text \<open>A contextual edge is an original generating edge placed inside
zero or more point-constructor arguments. Validity checks the original arity,
recursive argument specifications, and the fixed surrounding point trees.
The admitted-edge set may be empty.\<close>

datatype 'e constructor_edge =
    Generator 'e
  | Under nat "tm list" "'e constructor_edge" "tm list"

fun context_endpoint :: "nat \<Rightarrow> ('e \<Rightarrow> tm) \<Rightarrow> 'e constructor_edge \<Rightarrow> tm" where
  "context_endpoint h endpoint (Generator e) = endpoint e"
| "context_endpoint h endpoint (Under k before c after) =
    PCon h k (before @ [context_endpoint h endpoint c] @ after)"

inductive valid_context :: "sigenv \<Rightarrow> nat \<Rightarrow> 'e set \<Rightarrow>
    'e constructor_edge \<Rightarrow> bool" for S h E where
  generator: "e \<in> E \<Longrightarrow> valid_context S h E (Generator e)"
| under: "valid_context S h E c \<Longrightarrow>
    k < length (pcons (S h)) \<Longrightarrow>
    length before + 1 + length after = length (pcons (S h) ! k) \<Longrightarrow>
    (\<forall>r \<in> set (pcons (S h) ! k). r = Rec) \<Longrightarrow>
    (\<forall>x \<in> set before. point_tree S h x) \<Longrightarrow>
    (\<forall>x \<in> set after. point_tree S h x) \<Longrightarrow>
    valid_context S h E (Under k before c after)"

lemma valid_context_empty:
  "\<not> valid_context S h {} c"
  by (induct c) (auto elim: valid_context.cases)

lemma context_endpoint_tree:
  assumes C: "valid_context S h E c"
    and base: "\<And>e. e \<in> E \<Longrightarrow> point_tree S h (endpoint e)"
  shows "point_tree S h (context_endpoint h endpoint c)"
  using C
proof (induct rule: valid_context.induct)
  case (generator e)
  then show ?case by (simp add: base)
next
  case (under c k before after)
  show ?case
    by (simp only: context_endpoint.simps; rule point_tree.node)
      (use under in auto)
qed

section \<open>Local displayed naturality and contextual elimination\<close>

locale contextual_point_algebra = displayed_point_algebra S h F M
  for S :: sigenv and h :: nat and F :: "tm \<Rightarrow> 'a set"
    and M :: "nat \<Rightarrow> tm list \<Rightarrow> 'a list \<Rightarrow> 'a" +
  fixes E :: "'e set" and base_source base_target :: "'e \<Rightarrow> tm"
    and upC downC :: "'e constructor_edge \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes source_points: "e \<in> E \<Longrightarrow> point_tree S h (base_source e)"
    and target_points: "e \<in> E \<Longrightarrow> point_tree S h (base_target e)"
    and contextual_family:
      "graph_family_on {c. valid_context S h E c}
        (context_endpoint h base_source) (context_endpoint h base_target) F upC downC"
    and base_boundary:
      "e \<in> E \<Longrightarrow> upC (Generator e) (point_fold M (base_source e)) =
        point_fold M (base_target e)"
    and point_naturality:
      "valid_context S h E (Under k before c after) \<Longrightarrow>
       list_all2 (\<lambda>x a. a \<in> F x) before bs \<Longrightarrow>
       a \<in> F (context_endpoint h base_source c) \<Longrightarrow>
       list_all2 (\<lambda>x a. a \<in> F x) after zs \<Longrightarrow>
       upC (Under k before c after)
         (M k (before @ [context_endpoint h base_source c] @ after) (bs @ [a] @ zs)) =
       M k (before @ [context_endpoint h base_target c] @ after) (bs @ [upC c a] @ zs)"
begin

abbreviation csrc where "csrc \<equiv> context_endpoint h base_source"
abbreviation cdst where "cdst \<equiv> context_endpoint h base_target"
abbreviation admitted where "admitted \<equiv> {c. valid_context S h E c}"

sublocale fibers: graph_family_on admitted csrc cdst F upC downC
  by (rule contextual_family)

lemma contextual_source_tree:
  "valid_context S h E c \<Longrightarrow> point_tree S h (csrc c)"
  by (rule context_endpoint_tree[OF _ source_points])

lemma contextual_target_tree:
  "valid_context S h E c \<Longrightarrow> point_tree S h (cdst c)"
  by (rule context_endpoint_tree[OF _ target_points])

lemma contextual_source_typed:
  "valid_context S h E c \<Longrightarrow> wt S D G (csrc c) (Hit h)"
  by (rule point_tree_typed[OF contextual_source_tree])

lemma contextual_target_typed:
  "valid_context S h E c \<Longrightarrow> wt S D G (cdst c) (Hit h)"
  by (rule point_tree_typed[OF contextual_target_tree])

lemma recursive_context_boundary:
  assumes "valid_context S h E c"
  shows "upC c (point_fold M (csrc c)) = point_fold M (cdst c)"
  using assms
proof (induct rule: valid_context.induct)
  case (generator e)
  then show ?case by (simp add: base_boundary)
next
  case (under c k before after)
  have V: "valid_context S h E (Under k before c after)"
    by (rule valid_context.under) (use under in auto)
  have B: "list_all2 (\<lambda>x a. a \<in> F x) before (map (point_fold M) before)"
    using under constructed_section_type by (auto simp: list_all2_conv_all_nth)
  have A: "point_fold M (csrc c) \<in> F (csrc c)"
    by (rule constructed_section_type[OF contextual_source_tree[OF under(1)]])
  have Z: "list_all2 (\<lambda>x a. a \<in> F x) after (map (point_fold M) after)"
    using under constructed_section_type by (auto simp: list_all2_conv_all_nth)
  from point_naturality[OF V B A Z] under
  show ?case by simp
qed

text \<open>The premise above is local and uniform in arbitrary correctly
typed recursive method arguments. The following result is derived by induction
on constructor contexts; it is not assumed for the finished fold.\<close>

lemma contextual_step_boundary:
  assumes "dart_edge d \<in> admitted"
  shows "fibers.step_transport d (point_fold M (source csrc cdst d)) =
    point_fold M (target csrc cdst d)"
proof (cases d)
  case (Pos c)
  with assms show ?thesis by (simp add: recursive_context_boundary)
next
  case (Neg c)
  have C: "valid_context S h E c" using assms Neg by simp
  have T: "point_fold M (csrc c) \<in> F (csrc c)"
    by (rule constructed_section_type[OF contextual_source_tree[OF C]])
  have "downC c (upC c (point_fold M (csrc c))) = point_fold M (csrc c)"
    by (rule fibers.down_up) (use C T in auto)
  then show ?thesis by (simp add: Neg recursive_context_boundary[OF C])
qed

lemma contextual_path_boundary:
  assumes "walk_on admitted csrc cdst x p y"
  shows "fibers.transport p (point_fold M x) = point_fold M y"
  using assms
  by (induct rule: walk_on_induct)
    (simp_all add: contextual_step_boundary)

lemma contextual_dependent_eliminator:
  assumes T: "point_tree S h x" and P: "walk_on admitted csrc cdst x p y"
  shows "fibers.transport p (point_fold M x) = point_fold M y \<and>
    point_fold M y \<in> F y"
  using contextual_path_boundary[OF P]
    fibers.transport_type[OF P constructed_section_type[OF T]] by simp

lemma contextual_equality_descent:
  assumes E: "equality_on admitted csrc cdst x p q y"
    and T: "point_tree S h x"
  shows "fibers.transport p (point_fold M x) = fibers.transport q (point_fold M x)"
  by (rule fibers.transport_equal[OF E constructed_section_type[OF T]])

lemma constructor_path_lifting:
  assumes P: "walk_on admitted csrc cdst x p y"
    and K: "k < length (pcons (S h))"
    and L: "length before + 1 + length after = length (pcons (S h) ! k)"
    and R: "\<forall>r \<in> set (pcons (S h) ! k). r = Rec"
    and B: "\<forall>x \<in> set before. point_tree S h x"
    and A: "\<forall>x \<in> set after. point_tree S h x"
  shows "walk_on admitted csrc cdst
    (PCon h k (before @ [x] @ after))
    (map (map_dart (\<lambda>c. Under k before c after)) p)
    (PCon h k (before @ [y] @ after))"
  using P
proof (induct rule: walk_on_induct)
  case (nil x)
  then show ?case by simp
next
  case (cons d p y)
  have V: "\<And>c. valid_context S h E c \<Longrightarrow>
    valid_context S h E (Under k before c after)"
    by (rule valid_context.under[OF _ K L R B A])
  show ?case using cons V by (cases d) auto
qed

lemma constructor_equality_lifting:
  assumes E: "equality_on admitted csrc cdst x p q y"
    and K: "k < length (pcons (S h))"
    and L: "length before + 1 + length after = length (pcons (S h) ! k)"
    and R: "\<forall>r \<in> set (pcons (S h) ! k). r = Rec"
    and B: "\<forall>x \<in> set before. point_tree S h x"
    and A: "\<forall>x \<in> set after. point_tree S h x"
  shows "equality_on admitted csrc cdst
    (PCon h k (before @ [x] @ after))
    (map (map_dart (\<lambda>c. Under k before c after)) p)
    (map (map_dart (\<lambda>c. Under k before c after)) q)
    (PCon h k (before @ [y] @ after))"
proof -
  have map_cancel: "\<And>(p :: 'e constructor_edge dart list) q. cancel p q \<Longrightarrow>
    cancel (map (map_dart (\<lambda>c. Under k before c after)) p)
      (map (map_dart (\<lambda>c. Under k before c after)) q)"
  proof -
    fix p q :: "'e constructor_edge dart list"
    assume C: "cancel p q"
    then show "cancel (map (map_dart (\<lambda>c. Under k before c after)) p)
      (map (map_dart (\<lambda>c. Under k before c after)) q)"
      by (induct rule: cancel.induct) (simp add: cancel.pair)
  qed
  show ?thesis using E
  proof (induct rule: equality_on.induct)
    case (refl x p y)
    show ?case by (rule equality_on.refl[OF constructor_path_lifting[OF refl K L R B A]])
  next
    case (cancel x p y q)
    show ?case by (rule equality_on.cancel[OF
      constructor_path_lifting[OF cancel(1) K L R B A] map_cancel[OF cancel(2)]])
  next
    case (sym x p q y)
    show ?case by (rule equality_on.sym[OF sym(2)])
  next
    case (trans x p q y r)
    show ?case by (rule equality_on.trans[OF trans(2,4)])
  qed
qed

end

section \<open>Extension of the original displayed HIT algebra\<close>

context displayed_hit_algebra
begin

lemma original_contextual_algebra:
  assumes family: "graph_family_on {c. valid_context S h UNIV c}
      (context_endpoint h src) (context_endpoint h dst) F upC downC"
    and base_up: "\<And>e a. upC (Generator e) a = up e a"
    and natural:
      "\<And>k before c after bs a zs.
       valid_context S h UNIV (Under k before c after) \<Longrightarrow>
       list_all2 (\<lambda>x a. a \<in> F x) before bs \<Longrightarrow>
       a \<in> F (context_endpoint h src c) \<Longrightarrow>
       list_all2 (\<lambda>x a. a \<in> F x) after zs \<Longrightarrow>
       upC (Under k before c after)
         (M k (before @ [context_endpoint h src c] @ after) (bs @ [a] @ zs)) =
       M k (before @ [context_endpoint h dst c] @ after) (bs @ [upC c a] @ zs)"
  shows "contextual_point_algebra S h F M UNIV src dst upC downC"
proof -
  interpret C: graph_family_on "{c. valid_context S h UNIV c}"
    "context_endpoint h src" "context_endpoint h dst" F upC downC
    by (rule family)
  show ?thesis using natural
    by (unfold_locales)
      (auto intro: method_type source_tree target_tree C.up_type C.down_type
        C.down_up C.up_down simp: base_up constructed_generator_boundary)
qed

end

section \<open>A nontrivial recursive contextual instance\<close>

abbreviation collapse_src where
  "collapse_src n \<equiv> lhsOf collapse_signature 0 0 [numeral_tree n]"
abbreviation collapse_dst where
  "collapse_dst n \<equiv> rhsOf collapse_signature 0 0 [numeral_tree n]"

lemma collapse_context_count:
  "point_count (context_endpoint 0 collapse_src c) =
    Suc (point_count (context_endpoint 0 collapse_dst c))"
  by (induct c) (simp_all add: lhsOf_def rhsOf_def collapse_signature_def sum_list_append)

lemma collapse_context_family:
  "graph_family_on {c. valid_context collapse_signature 0 UNIV c}
    (context_endpoint 0 collapse_src) (context_endpoint 0 collapse_dst)
    (\<lambda>u. {point_count u}) (\<lambda>_ n. n - 1) (\<lambda>_. Suc)"
  by unfold_locales (auto simp: collapse_context_count)

interpretation collapse_context: contextual_point_algebra collapse_signature 0
  "\<lambda>u. {point_count u}" "\<lambda>k xs ys. Suc (sum_list ys)"
  UNIV collapse_src collapse_dst "\<lambda>_ n. n - 1" "\<lambda>_. Suc"
proof (rule collapse.original_contextual_algebra)
  show "graph_family_on {c. valid_context collapse_signature 0 UNIV c}
    (context_endpoint 0 collapse_src) (context_endpoint 0 collapse_dst)
    (\<lambda>u. {point_count u}) (\<lambda>_ n. n - 1) (\<lambda>_. Suc)"
    by (rule collapse_context_family)
  show "a - 1 = a - 1" for e a by simp
  fix k before c after bs a zs
  assume "valid_context collapse_signature 0 UNIV (Under k before c after)"
    "list_all2 (\<lambda>x a. a \<in> {point_count x}) before bs"
    and A: "a \<in> {point_count (context_endpoint 0 collapse_src c)}"
    and "list_all2 (\<lambda>x a. a \<in> {point_count x}) after zs"
  have "a = Suc (point_count (context_endpoint 0 collapse_dst c))"
    using A by (simp add: collapse_context_count)
  then show "Suc (sum_list (bs @ [a] @ zs)) - 1 =
    Suc (sum_list (bs @ [a - 1] @ zs))"
    by (simp add: sum_list_append)
qed

lemma successor_context_admitted:
  "valid_context collapse_signature 0 UNIV (Under 1 [] (Generator n) [])"
  by (intro valid_context.under valid_context.generator)
    (simp_all add: collapse_signature_def)

lemma recursive_context_path_computation:
  "collapse_context.fibers.transport [Pos (Under 1 [] (Generator n) [])]
    (point_fold (\<lambda>k xs ys. Suc (sum_list ys)) (numeral_tree (Suc (Suc n)))) =
    Suc (Suc n)"
  by (simp only: collapse_context.fibers.transport.simps collapse_context.fibers.step_transport.simps
    recursive_hit_computation; simp)

end
