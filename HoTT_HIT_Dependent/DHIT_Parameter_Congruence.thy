theory DHIT_Parameter_Congruence
  imports DHIT_Parameter_Algebra DHIT_Constructor_Congruence
begin

section \<open>Constructor contexts with opaque parameters\<close>

text \<open>The hole must occur in an original Rec slot. The surrounding
arguments obey the original mixed arity: external Par arguments remain opaque
and fixed, while other Rec arguments are constructor trees. Displayed
naturality is explicit algebra data, uniform in arbitrary typed option-valued
induction hypotheses. It is not inferred from point-method typing alone.
This theory does not add paths varying external parameters or higher
interchange equations between contextual paths.\<close>

lemma parameter_arguments_list:
  "parameter_arguments S h P ss xs \<longleftrightarrow>
    external_arity h ss \<and> list_all2 (\<lambda>r x. parameter_carrier S h P (argTy h r) x) ss xs"
  by (auto simp: parameter_arguments_def list_all2_conv_all_nth)

lemma external_arity_append [simp]:
  "external_arity h (ss @ ts) \<longleftrightarrow> external_arity h ss \<and> external_arity h ts"
  by (auto simp: external_arity_def)

lemma parameter_arguments_append:
  "parameter_arguments S h P ss xs \<Longrightarrow> parameter_arguments S h P ts ys \<Longrightarrow>
    parameter_arguments S h P (ss @ ts) (xs @ ys)"
  unfolding parameter_arguments_list by (auto intro: list_all2_appendI)

lemma parameter_arguments_rec:
  "parameter_tree S h P x \<Longrightarrow> parameter_arguments S h P [Rec] [x]"
  by (simp add: parameter_arguments_def external_arity_def parameter_carrier_def)

lemma parameter_arguments_node:
  assumes K: "k < length (pcons (S h))"
    and A: "parameter_arguments S h P (pcons (S h) ! k) xs"
  shows "parameter_tree S h P (PCon h k xs)"
proof (rule parameter_tree.node)
  show "k < length (pcons (S h))" by (rule K)
  show "length xs = length (pcons (S h) ! k)"
    using A by (simp add: parameter_arguments_def)
  show "external_arity h (pcons (S h) ! k)"
    using A by (simp add: parameter_arguments_def)
  show "\<forall>i < length xs. pcons (S h) ! k ! i = Rec \<longrightarrow> parameter_tree S h P (xs ! i)"
    using A by (auto simp: parameter_arguments_def parameter_carrier_def)
  show "\<forall>i j. i < length xs \<longrightarrow> pcons (S h) ! k ! i = Par j \<longrightarrow> xs ! i \<in> P j"
  proof (intro allI impI)
    fix i j assume I: "i < length xs" and J: "pcons (S h) ! k ! i = Par j"
    have N: "j \<noteq> h"
      using A I J unfolding parameter_arguments_def external_arity_def
      by (metis nth_mem)
    have C: "parameter_carrier S h P (argTy h (pcons (S h) ! k ! i)) (xs ! i)"
      using A I by (simp add: parameter_arguments_def)
    show "xs ! i \<in> P j" using C N by (simp add: J parameter_carrier_def)
  qed
qed

definition parameter_slot ::
  "sigenv \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tm set) \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> bool" where
  "parameter_slot S h P k before after \<longleftrightarrow> k < length (pcons (S h)) \<and>
    (\<exists>bs zs. pcons (S h) ! k = bs @ [Rec] @ zs \<and>
      parameter_arguments S h P bs before \<and> parameter_arguments S h P zs after)"

lemma parameter_slot_tree:
  assumes slot: "parameter_slot S h P k before after" and tree: "parameter_tree S h P x"
  shows "parameter_tree S h P (PCon h k (before @ [x] @ after))"
proof -
  from slot obtain bs zs where K: "k < length (pcons (S h))"
    and R: "pcons (S h) ! k = bs @ [Rec] @ zs"
    and B: "parameter_arguments S h P bs before"
    and Z: "parameter_arguments S h P zs after"
    unfolding parameter_slot_def by blast
  have Args: "parameter_arguments S h P (bs @ [Rec] @ zs) (before @ [x] @ after)"
    by (intro parameter_arguments_append B Z parameter_arguments_rec[OF tree])
  show ?thesis by (rule parameter_arguments_node) (use K Args R in auto)
qed

inductive valid_parameter_context :: "sigenv \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tm set) \<Rightarrow>
    'e set \<Rightarrow> 'e constructor_edge \<Rightarrow> bool" for S h P E where
  generator: "e \<in> E \<Longrightarrow> valid_parameter_context S h P E (Generator e)"
| under: "valid_parameter_context S h P E c \<Longrightarrow>
    parameter_slot S h P k before after \<Longrightarrow>
    valid_parameter_context S h P E (Under k before c after)"

lemma valid_parameter_context_empty:
  "\<not> valid_parameter_context S h P {} c"
  by (induct c) (auto elim: valid_parameter_context.cases)

lemma parameter_context_endpoint_tree:
  assumes C: "valid_parameter_context S h P E c"
    and base: "\<And>e. e \<in> E \<Longrightarrow> parameter_tree S h P (endpoint e)"
  shows "parameter_tree S h P (context_endpoint h endpoint c)"
  using C
proof (induct rule: valid_parameter_context.induct)
  case (generator e)
  then show ?case by (simp add: base)
next
  case (under c k before after)
  from parameter_slot_tree[OF under(3,2)] show ?case by simp
qed

lemma ih_mask_append:
  "length ss = length ys \<Longrightarrow>
    ih_mask (ss @ ts) (ys @ zs) = ih_mask ss ys @ ih_mask ts zs"
  by (induct ss arbitrary: ys; case_tac ys; simp_all add: ih_mask_def)

lemma displayed_arguments_zip:
  assumes "length ss = length xs"
  shows "displayed_arguments F ss xs ys \<longleftrightarrow>
    list_all2 (\<lambda>rx y. case fst rx of Par j \<Rightarrow> y = None
      | Rec \<Rightarrow> (\<exists>a. y = Some a \<and> a \<in> F (snd rx))) (zip ss xs) ys"
proof -
  have N: "\<And>i. i < length xs \<Longrightarrow> zip ss xs ! i = (ss ! i, xs ! i)"
    using assms by simp
  show ?thesis using assms
    by (auto simp: displayed_arguments_def list_all2_conv_all_nth N split: argspec.splits)
qed

lemma displayed_arguments_append:
  assumes L: "length ss = length xs" "length ts = length zs"
    and D: "displayed_arguments F ss xs ys" "displayed_arguments F ts zs ws"
  shows "displayed_arguments F (ss @ ts) (xs @ zs) (ys @ ws)"
proof -
  have Lsum: "length (ss @ ts) = length (xs @ zs)" using L by simp
  show ?thesis
    unfolding displayed_arguments_zip[OF Lsum] zip_append[OF L(1)]
    by (rule list_all2_appendI)
      (use D in \<open>simp_all add: displayed_arguments_zip[OF L(1)] displayed_arguments_zip[OF L(2)]\<close>)
qed

lemma displayed_arguments_rec:
  "a \<in> F x \<Longrightarrow> displayed_arguments F [Rec] [x] [Some a]"
  by (simp add: displayed_arguments_def)

context parameter_displayed_algebra
begin

lemma context_argument_lifts:
  assumes "parameter_arguments S h P ss xs"
  shows "displayed_arguments F ss xs (ih_mask ss (map (parameter_fold S h M) xs))"
  using assms constructed_section_type
  by (auto simp: displayed_arguments_def parameter_arguments_def parameter_carrier_def
    split: argspec.splits)

end

section \<open>Uniform displayed naturality in recursive slots\<close>

locale contextual_parameter_algebra = parameter_displayed_algebra S h P F M
  for S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set" and F :: "tm \<Rightarrow> 'a set"
    and M :: "nat \<Rightarrow> tm list \<Rightarrow> 'a option list \<Rightarrow> 'a" +
  fixes E :: "'e set" and base_source base_target :: "'e \<Rightarrow> tm"
    and upC downC :: "'e constructor_edge \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes source_points: "e \<in> E \<Longrightarrow> parameter_tree S h P (base_source e)"
    and target_points: "e \<in> E \<Longrightarrow> parameter_tree S h P (base_target e)"
    and contextual_family:
      "graph_family_on {c. valid_parameter_context S h P E c}
        (context_endpoint h base_source) (context_endpoint h base_target) F upC downC"
    and base_boundary:
      "e \<in> E \<Longrightarrow> upC (Generator e) (parameter_fold S h M (base_source e)) =
        parameter_fold S h M (base_target e)"
    and point_naturality:
      "valid_parameter_context S h P E (Under k before c after) \<Longrightarrow>
       pcons (S h) ! k = bs @ [Rec] @ zs \<Longrightarrow>
       parameter_arguments S h P bs before \<Longrightarrow>
       parameter_arguments S h P zs after \<Longrightarrow>
       displayed_arguments F bs before bv \<Longrightarrow>
       a \<in> F (context_endpoint h base_source c) \<Longrightarrow>
       displayed_arguments F zs after zv \<Longrightarrow>
       upC (Under k before c after)
         (M k (before @ [context_endpoint h base_source c] @ after) (bv @ [Some a] @ zv)) =
       M k (before @ [context_endpoint h base_target c] @ after) (bv @ [Some (upC c a)] @ zv)"
begin

abbreviation csrc where "csrc \<equiv> context_endpoint h base_source"
abbreviation cdst where "cdst \<equiv> context_endpoint h base_target"
abbreviation admitted where "admitted \<equiv> {c. valid_parameter_context S h P E c}"

sublocale fibers: graph_family_on admitted csrc cdst F upC downC
  by (rule contextual_family)

lemma contextual_source_tree:
  "valid_parameter_context S h P E c \<Longrightarrow> parameter_tree S h P (csrc c)"
  by (rule parameter_context_endpoint_tree[OF _ source_points])

lemma contextual_target_tree:
  "valid_parameter_context S h P E c \<Longrightarrow> parameter_tree S h P (cdst c)"
  by (rule parameter_context_endpoint_tree[OF _ target_points])

lemma contextual_source_typed:
  assumes C: "valid_parameter_context S h P E c"
    and parameters: "\<And>j u. u \<in> P j \<Longrightarrow> wt S D G u (Hit j)"
  shows "wt S D G (csrc c) (Hit h)"
  by (rule parameter_tree_typed[OF contextual_source_tree[OF C] parameters])

lemma contextual_target_typed:
  assumes C: "valid_parameter_context S h P E c"
    and parameters: "\<And>j u. u \<in> P j \<Longrightarrow> wt S D G u (Hit j)"
  shows "wt S D G (cdst c) (Hit h)"
  by (rule parameter_tree_typed[OF contextual_target_tree[OF C] parameters])

lemma recursive_context_boundary:
  assumes "valid_parameter_context S h P E c"
  shows "upC c (parameter_fold S h M (csrc c)) = parameter_fold S h M (cdst c)"
  using assms
proof (induct rule: valid_parameter_context.induct)
  case (generator e)
  then show ?case by (simp add: base_boundary)
next
  case (under c k before after)
  have V: "valid_parameter_context S h P E (Under k before c after)"
    by (rule valid_parameter_context.under[OF under(1,3)])
  from under(3) obtain bs zs where R: "pcons (S h) ! k = bs @ [Rec] @ zs"
    and B: "parameter_arguments S h P bs before" and Z: "parameter_arguments S h P zs after"
    unfolding parameter_slot_def by blast
  have L: "length bs = length before" "length zs = length after"
    using B Z by (auto simp: parameter_arguments_def)
  have A: "parameter_fold S h M (csrc c) \<in> F (csrc c)"
    by (rule constructed_section_type[OF contextual_source_tree[OF under(1)]])
  from point_naturality[OF V R B Z context_argument_lifts[OF B] A context_argument_lifts[OF Z]] under(2)
  show ?case by (simp add: R ih_mask_append L ih_mask_def)
qed

lemma contextual_step_boundary:
  assumes "dart_edge d \<in> admitted"
  shows "fibers.step_transport d (parameter_fold S h M (source csrc cdst d)) =
    parameter_fold S h M (target csrc cdst d)"
proof (cases d)
  case (Pos c)
  with assms show ?thesis by (simp add: recursive_context_boundary)
next
  case (Neg c)
  have C: "valid_parameter_context S h P E c" using assms Neg by simp
  have T: "parameter_fold S h M (csrc c) \<in> F (csrc c)"
    by (rule constructed_section_type[OF contextual_source_tree[OF C]])
  have "downC c (upC c (parameter_fold S h M (csrc c))) = parameter_fold S h M (csrc c)"
    by (rule fibers.down_up) (use C T in auto)
  then show ?thesis by (simp add: Neg recursive_context_boundary[OF C])
qed

lemma contextual_path_boundary:
  "walk_on admitted csrc cdst x p y \<Longrightarrow>
    fibers.transport p (parameter_fold S h M x) = parameter_fold S h M y"
  by (induct rule: walk_on_induct) (simp_all add: contextual_step_boundary)

lemma contextual_dependent_eliminator:
  assumes T: "parameter_tree S h P x" and W: "walk_on admitted csrc cdst x p y"
  shows "fibers.transport p (parameter_fold S h M x) = parameter_fold S h M y \<and>
    parameter_fold S h M y \<in> F y"
  using contextual_path_boundary[OF W]
    fibers.transport_type[OF W constructed_section_type[OF T]] by simp

lemma contextual_equality_descent:
  assumes "equality_on admitted csrc cdst x p q y" "parameter_tree S h P x"
  shows "fibers.transport p (parameter_fold S h M x) = fibers.transport q (parameter_fold S h M x)"
  by (rule fibers.transport_equal[OF assms(1) constructed_section_type[OF assms(2)]])

lemma constructor_path_lifting:
  assumes W: "walk_on admitted csrc cdst x p y"
    and slot: "parameter_slot S h P k before after"
  shows "walk_on admitted csrc cdst (PCon h k (before @ [x] @ after))
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
    by (rule valid_parameter_context.under[OF _ slot])
  show ?case using cons V by (cases d) auto
qed

lemma constructor_equality_lifting:
  assumes Eq: "equality_on admitted csrc cdst x p q y"
    and slot: "parameter_slot S h P k before after"
  shows "equality_on admitted csrc cdst (PCon h k (before @ [x] @ after))
    (map (map_dart (\<lambda>c. Under k before c after)) p)
    (map (map_dart (\<lambda>c. Under k before c after)) q)
    (PCon h k (before @ [y] @ after))"
proof -
  have C: "\<And>(p :: 'e constructor_edge dart list) q. cancel p q \<Longrightarrow>
    cancel (map (map_dart (\<lambda>c. Under k before c after)) p)
      (map (map_dart (\<lambda>c. Under k before c after)) q)"
  proof -
    fix p q :: "'e constructor_edge dart list"
    assume C: "cancel p q"
    then show "cancel (map (map_dart (\<lambda>c. Under k before c after)) p)
      (map (map_dart (\<lambda>c. Under k before c after)) q)"
      by (induct rule: cancel.induct) (simp add: cancel.pair)
  qed
  show ?thesis using Eq
  proof (induct rule: equality_on.induct)
    case (refl x p y)
    show ?case by (rule equality_on.refl[OF constructor_path_lifting[OF refl slot]])
  next
    case (cancel x p y q)
    show ?case by (rule equality_on.cancel[OF constructor_path_lifting[OF cancel(1) slot] C[OF cancel(2)]])
  next
    case (sym x p q y)
    show ?case by (rule equality_on.sym[OF sym(2)])
  next
    case (trans x p q y r)
    show ?case by (rule equality_on.trans[OF trans(2,4)])
  qed
qed

end

section \<open>Extension of the original mixed displayed algebra\<close>

context parameter_hit_algebra
begin

lemma original_contextual_algebra:
  assumes family: "graph_family_on {c. valid_parameter_context S h P UNIV c}
      (context_endpoint h src) (context_endpoint h dst) F upC downC"
    and base_up: "\<And>e a. upC (Generator e) a = up e a"
    and natural:
      "\<And>k before c after bs zs bv a zv.
       valid_parameter_context S h P UNIV (Under k before c after) \<Longrightarrow>
       pcons (S h) ! k = bs @ [Rec] @ zs \<Longrightarrow>
       parameter_arguments S h P bs before \<Longrightarrow>
       parameter_arguments S h P zs after \<Longrightarrow>
       displayed_arguments F bs before bv \<Longrightarrow>
       a \<in> F (context_endpoint h src c) \<Longrightarrow>
       displayed_arguments F zs after zv \<Longrightarrow>
       upC (Under k before c after)
         (M k (before @ [context_endpoint h src c] @ after) (bv @ [Some a] @ zv)) =
       M k (before @ [context_endpoint h dst c] @ after) (bv @ [Some (upC c a)] @ zv)"
  shows "contextual_parameter_algebra S h P F M UNIV src dst upC downC"
proof -
  interpret C: graph_family_on "{c. valid_parameter_context S h P UNIV c}"
    "context_endpoint h src" "context_endpoint h dst" F upC downC
    by (rule family)
  show ?thesis using natural
    by (unfold_locales)
      (auto intro: method_type source_tree target_tree C.up_type C.down_type
        C.down_up C.up_down simp: base_up constructed_generator_boundary)
qed

end

section \<open>A list-tail context with nonidentity transport\<close>

abbreviation plist_src where
  "plist_src n \<equiv> lhsOf parameter_list_signature 0 0 [PCon 1 0 [], parameter_list n]"
abbreviation plist_dst where
  "plist_dst n \<equiv> rhsOf parameter_list_signature 0 0 [PCon 1 0 [], parameter_list n]"

lemma parameter_context_count:
  "point_count (context_endpoint 0 plist_src c) =
    point_count (context_endpoint 0 plist_dst c) + 2"
  by (induct c) (simp_all add: lhsOf_def rhsOf_def parameter_list_signature_def sum_list_append)

lemma parameter_context_family:
  "graph_family_on {c. valid_parameter_context parameter_list_signature 0 list_parameters UNIV c}
    (context_endpoint 0 plist_src) (context_endpoint 0 plist_dst)
    (\<lambda>u. {point_count u}) (\<lambda>_ n. n - 2) (\<lambda>_ n. n + 2)"
  by unfold_locales (auto simp: parameter_context_count[simplified])

lemma displayed_count_arguments_splice:
  assumes B: "parameter_arguments S h P bs before"
    and Z: "parameter_arguments S h P zs after"
    and BV: "displayed_arguments F bs before bv"
    and A: "a \<in> F x"
    and ZV: "displayed_arguments F zs after zv"
  shows "displayed_arguments F (bs @ [Rec] @ zs) (before @ [x] @ after) (bv @ [Some a] @ zv)"
proof -
  have L: "length bs = length before" "length zs = length after"
    using B Z by (auto simp: parameter_arguments_def)
  have Tail: "displayed_arguments F ([Rec] @ zs) ([x] @ after) ([Some a] @ zv)"
    by (rule displayed_arguments_append)
      (use L A ZV in \<open>auto intro: displayed_arguments_rec\<close>)
  show ?thesis by (rule displayed_arguments_append[OF L(1) _ BV Tail]) (simp add: L)
qed

interpretation parameter_list_context: contextual_parameter_algebra parameter_list_signature 0 list_parameters
  "\<lambda>u. {point_count u}" "count_parameter_method parameter_list_signature 0"
  UNIV plist_src plist_dst "\<lambda>_ n. n - 2" "\<lambda>_ n. n + 2"
proof (rule parameter_list_hit.original_contextual_algebra)
  show "graph_family_on {c. valid_parameter_context parameter_list_signature 0 list_parameters UNIV c}
    (context_endpoint 0 plist_src) (context_endpoint 0 plist_dst)
    (\<lambda>u. {point_count u}) (\<lambda>_ n. n - 2) (\<lambda>_ n. n + 2)"
    by (rule parameter_context_family)
  show "a - 2 = a - 2" for e a by simp
  fix k before c after bs zs bv a zv
  assume V: "valid_parameter_context parameter_list_signature 0 list_parameters UNIV (Under k before c after)"
    and R: "pcons (parameter_list_signature 0) ! k = bs @ [Rec] @ zs"
    and B: "parameter_arguments parameter_list_signature 0 list_parameters bs before"
    and Z: "parameter_arguments parameter_list_signature 0 list_parameters zs after"
    and BV: "displayed_arguments (\<lambda>u. {point_count u}) bs before bv"
    and A: "a \<in> {point_count (context_endpoint 0 plist_src c)}"
    and ZV: "displayed_arguments (\<lambda>u. {point_count u}) zs after zv"
  have C: "valid_parameter_context parameter_list_signature 0 list_parameters UNIV c"
    and Slot: "parameter_slot parameter_list_signature 0 list_parameters k before after"
    using V by (auto elim: valid_parameter_context.cases)
  have Source: "parameter_tree parameter_list_signature 0 list_parameters (context_endpoint 0 plist_src c)"
    by (rule parameter_context_endpoint_tree[OF C]) (rule parameter_list_hit.source_tree)
  have Target: "parameter_tree parameter_list_signature 0 list_parameters (context_endpoint 0 plist_dst c)"
    by (rule parameter_context_endpoint_tree[OF C]) (rule parameter_list_hit.target_tree)
  have A': "a - 2 \<in> {point_count (context_endpoint 0 plist_dst c)}"
    using A by (simp add: parameter_context_count[simplified])
  have SL: "displayed_arguments (\<lambda>u. {point_count u}) (pcons (parameter_list_signature 0) ! k)
      (before @ [context_endpoint 0 plist_src c] @ after) (bv @ [Some a] @ zv)"
    unfolding R by (rule displayed_count_arguments_splice[OF B Z BV A ZV])
  have TL: "displayed_arguments (\<lambda>u. {point_count u}) (pcons (parameter_list_signature 0) ! k)
      (before @ [context_endpoint 0 plist_dst c] @ after) (bv @ [Some (a - 2)] @ zv)"
    unfolding R by (rule displayed_count_arguments_splice[OF B Z BV A' ZV])
  have MS: "count_parameter_method parameter_list_signature 0 k
      (before @ [context_endpoint 0 plist_src c] @ after) (bv @ [Some a] @ zv) =
      point_count (PCon 0 k (before @ [context_endpoint 0 plist_src c] @ after))"
    using parameter_displayed_algebra.method_type[OF count_parameter_algebra
      parameter_slot_tree[OF Slot Source] SL] by simp
  have MT: "count_parameter_method parameter_list_signature 0 k
      (before @ [context_endpoint 0 plist_dst c] @ after) (bv @ [Some (a - 2)] @ zv) =
      point_count (PCon 0 k (before @ [context_endpoint 0 plist_dst c] @ after))"
    using parameter_displayed_algebra.method_type[OF count_parameter_algebra
      parameter_slot_tree[OF Slot Target] TL] by simp
  show "count_parameter_method parameter_list_signature 0 k
      (before @ [context_endpoint 0 plist_src c] @ after) (bv @ [Some a] @ zv) - 2 =
      count_parameter_method parameter_list_signature 0 k
      (before @ [context_endpoint 0 plist_dst c] @ after) (bv @ [Some (a - 2)] @ zv)"
    by (simp only: MS MT; simp add: parameter_context_count[simplified] sum_list_append)
qed

lemma list_tail_slot:
  "parameter_slot parameter_list_signature 0 list_parameters 1 [PCon 1 0 []] []"
  unfolding parameter_slot_def
  by (intro conjI exI[where x="[Par 1]"] exI[where x="[]"])
    (simp_all add: parameter_list_signature_def parameter_arguments_def
      external_arity_def parameter_carrier_def list_parameters_def)

lemma list_tail_context_admitted:
  "valid_parameter_context parameter_list_signature 0 list_parameters UNIV
    (Under 1 [PCon 1 0 []] (Generator n) [])"
  by (intro valid_parameter_context.under valid_parameter_context.generator list_tail_slot) simp

lemma parameterized_context_path_computation:
  "parameter_list_context.fibers.transport [Pos (Under 1 [PCon 1 0 []] (Generator n) [])]
    (parameter_fold parameter_list_signature 0 (count_parameter_method parameter_list_signature 0)
      (parameter_list (Suc (Suc n)))) = 2 * Suc n + 1"
  by (simp only: parameter_list_context.fibers.transport.simps
    parameter_list_context.fibers.step_transport.simps
    count_parameter_fold[OF parameter_list_tree] parameter_list_count; simp)

end
