theory DHIT_Interchange
  imports DHIT_Parameter_Congruence DHIT_Path_Quotient
begin

section \<open>Constructor action on signed paths\<close>

fun plug_edge :: "unit constructor_edge \<Rightarrow> 'e constructor_edge \<Rightarrow> 'e constructor_edge" where
  "plug_edge (Generator u) c = c"
| "plug_edge (Under k before C after) c = Under k before (plug_edge C c) after"

definition plug_term :: "nat \<Rightarrow> unit constructor_edge \<Rightarrow> tm \<Rightarrow> tm" where
  "plug_term h C x = context_endpoint h (\<lambda>_. x) C"

lemma plug_term_simps [simp]:
  "plug_term h (Generator ()) x = x"
  "plug_term h (Under k before C after) x = PCon h k (before @ [plug_term h C x] @ after)"
  by (simp_all add: plug_term_def)

inductive valid_shell :: "sigenv \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tm set) \<Rightarrow> unit constructor_edge \<Rightarrow> bool"
  for S h P where
  hole [intro]: "valid_shell S h P (Generator ())"
| under: "valid_shell S h P C \<Longrightarrow> parameter_slot S h P k before after \<Longrightarrow>
    valid_shell S h P (Under k before C after)"

lemma plug_endpoint [simp]:
  "context_endpoint h s (plug_edge C c) = plug_term h C (context_endpoint h s c)"
  by (induct C) (simp_all add: plug_term_def)

lemma plug_edge_composition [simp]:
  "plug_edge (plug_edge C D) c = plug_edge C (plug_edge D c)"
  by (induct C) simp_all

lemma plug_term_composition [simp]:
  "plug_term h (plug_edge C D) x = plug_term h C (plug_term h D x)"
  by (induct C) (simp_all add: plug_term_def)

lemma valid_shell_composition:
  "valid_shell S h P C \<Longrightarrow> valid_shell S h P D \<Longrightarrow> valid_shell S h P (plug_edge C D)"
  by (induct rule: valid_shell.induct) (auto intro: valid_shell.intros)

lemma valid_shell_edge:
  "valid_shell S h P C \<Longrightarrow> valid_parameter_context S h P E c \<Longrightarrow>
    valid_parameter_context S h P E (plug_edge C c)"
  by (induct rule: valid_shell.induct) (auto intro: valid_parameter_context.intros)

lemma valid_shell_tree:
  "valid_shell S h P C \<Longrightarrow> parameter_tree S h P x \<Longrightarrow>
    parameter_tree S h P (plug_term h C x)"
proof (induct rule: valid_shell.induct)
  case hole
  then show ?case by simp
next
  case (under C k before after)
  have T: "parameter_tree S h P (plug_term h C x)" using under by blast
  from parameter_slot_tree[OF under(3) T] show ?case by simp
qed

definition lift_path :: "unit constructor_edge \<Rightarrow> 'e constructor_edge dart list \<Rightarrow> 'e constructor_edge dart list" where
  "lift_path C p = map (map_dart (plug_edge C)) p"

lemma lift_path_identity [simp]: "lift_path (Generator ()) p = p"
proof -
  have H: "map_dart (plug_edge (Generator ())) = id"
    by (rule ext; rename_tac d; case_tac d; simp)
  show ?thesis by (simp only: lift_path_def H; simp)
qed

lemma lift_path_Nil [simp]: "lift_path C [] = []"
  by (simp add: lift_path_def)

lemma lift_path_append [simp]: "lift_path C (p @ q) = lift_path C p @ lift_path C q"
  by (simp add: lift_path_def)

lemma lift_path_composition [simp]: "lift_path (plug_edge C D) p = lift_path C (lift_path D p)"
  unfolding lift_path_def
proof (simp only: map_map; rule map_cong)
  show "p = p" by simp
  fix d assume "d \<in> set p"
  show "map_dart (plug_edge (plug_edge C D)) d =
    (map_dart (plug_edge C) \<circ> map_dart (plug_edge D)) d"
    by (cases d) simp_all
qed

lemma lift_path_reverse [simp]: "lift_path C (reverse_path p) = reverse_path (lift_path C p)"
  by (simp add: lift_path_def reverse_path_def rev_map map_map comp_def)

lemma lift_path_cancel:
  "cancel p q \<Longrightarrow> cancel (lift_path C p) (lift_path C q)"
  by (induct rule: cancel.induct) (simp add: lift_path_def cancel.pair)

section \<open>Two genuinely distinct recursive argument slots\<close>

definition two_slot :: "sigenv \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tm set) \<Rightarrow> nat \<Rightarrow>
    tm list \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> bool" where
  "two_slot S h P k before middle after \<longleftrightarrow> k < length (pcons (S h)) \<and>
    (\<exists>bs ms zs. pcons (S h) ! k = bs @ [Rec] @ ms @ [Rec] @ zs \<and>
      parameter_arguments S h P bs before \<and> parameter_arguments S h P ms middle \<and>
      parameter_arguments S h P zs after)"

lemma two_slot_left:
  assumes T: "two_slot S h P k before middle after" and Y: "parameter_tree S h P y"
  shows "parameter_slot S h P k before (middle @ [y] @ after)"
proof -
  from T obtain bs ms zs where K: "k < length (pcons (S h))"
    and R: "pcons (S h) ! k = bs @ [Rec] @ ms @ [Rec] @ zs"
    and B: "parameter_arguments S h P bs before" and M: "parameter_arguments S h P ms middle"
    and Z: "parameter_arguments S h P zs after"
    unfolding two_slot_def by blast
  have A: "parameter_arguments S h P (ms @ [Rec] @ zs) (middle @ [y] @ after)"
    by (intro parameter_arguments_append M Z parameter_arguments_rec[OF Y])
  show ?thesis unfolding parameter_slot_def
    using K R B A by blast
qed

lemma two_slot_right:
  assumes T: "two_slot S h P k before middle after" and X: "parameter_tree S h P x"
  shows "parameter_slot S h P k (before @ [x] @ middle) after"
proof -
  from T obtain bs ms zs where K: "k < length (pcons (S h))"
    and R: "pcons (S h) ! k = bs @ [Rec] @ ms @ [Rec] @ zs"
    and B: "parameter_arguments S h P bs before" and M: "parameter_arguments S h P ms middle"
    and Z: "parameter_arguments S h P zs after"
    unfolding two_slot_def by blast
  have A: "parameter_arguments S h P (bs @ [Rec] @ ms) (before @ [x] @ middle)"
    by (intro parameter_arguments_append B M parameter_arguments_rec[OF X])
  show ?thesis unfolding parameter_slot_def
    using K R A Z by (metis append_assoc)
qed

definition square_start where
  "square_start h s k before middle after c d =
    PCon h k (before @ [context_endpoint h s c] @ middle @ [context_endpoint h s d] @ after)"

definition square_lr where
  "square_lr h s t k before middle after c d =
    [Pos (Under k before c (middle @ [context_endpoint h s d] @ after)),
     Pos (Under k (before @ [context_endpoint h t c] @ middle) d after)]"

definition square_rl where
  "square_rl h s t k before middle after c d =
    [Pos (Under k (before @ [context_endpoint h s c] @ middle) d after),
     Pos (Under k before c (middle @ [context_endpoint h t d] @ after))]"

locale mixed_context_graph =
  fixes S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set"
    and E :: "'e set" and s t :: "'e \<Rightarrow> tm"
  assumes source_points: "e \<in> E \<Longrightarrow> parameter_tree S h P (s e)"
    and target_points: "e \<in> E \<Longrightarrow> parameter_tree S h P (t e)"
begin

abbreviation csrc where "csrc \<equiv> context_endpoint h s"
abbreviation cdst where "cdst \<equiv> context_endpoint h t"
abbreviation admitted where "admitted \<equiv> {c. valid_parameter_context S h P E c}"

lemma source_tree: "c \<in> admitted \<Longrightarrow> parameter_tree S h P (csrc c)"
  by (simp only: mem_Collect_eq; rule parameter_context_endpoint_tree[OF _ source_points])

lemma target_tree: "c \<in> admitted \<Longrightarrow> parameter_tree S h P (cdst c)"
  by (simp only: mem_Collect_eq; rule parameter_context_endpoint_tree[OF _ target_points])

lemma shell_path_lifting:
  assumes W: "walk_on admitted csrc cdst x p y" and V: "valid_shell S h P C"
  shows "walk_on admitted csrc cdst (plug_term h C x) (lift_path C p) (plug_term h C y)"
  using W
proof (induct rule: walk_on_induct)
  case (nil x)
  then show ?case by simp
next
  case (cons d p y)
  show ?case using cons valid_shell_edge[OF V]
    by (cases d) (auto simp: lift_path_def)
qed

lemma square_paths_typed:
  assumes T: "two_slot S h P k before middle after" and C: "c \<in> admitted" and D: "d \<in> admitted"
  shows "walk_on admitted csrc cdst (square_start h s k before middle after c d)
      (square_lr h s t k before middle after c d) (square_start h t k before middle after c d)"
    and "walk_on admitted csrc cdst (square_start h s k before middle after c d)
      (square_rl h s t k before middle after c d) (square_start h t k before middle after c d)"
  using C D two_slot_left[OF T source_tree[OF D]] two_slot_left[OF T target_tree[OF D]]
    two_slot_right[OF T source_tree[OF C]] two_slot_right[OF T target_tree[OF C]]
  by (auto simp: square_start_def square_lr_def square_rl_def append_assoc intro: valid_parameter_context.under)

lemma square_start_tree:
  assumes T: "two_slot S h P k before middle after" and C: "c \<in> admitted" and D: "d \<in> admitted"
  shows "parameter_tree S h P (square_start h s k before middle after c d)"
  unfolding square_start_def
  by (rule parameter_slot_tree[OF two_slot_left[OF T source_tree[OF D]] source_tree[OF C]])

lemma square_target_tree:
  assumes T: "two_slot S h P k before middle after" and C: "c \<in> admitted" and D: "d \<in> admitted"
  shows "parameter_tree S h P (square_start h t k before middle after c d)"
  unfolding square_start_def
  by (rule parameter_slot_tree[OF two_slot_left[OF T target_tree[OF D]] target_tree[OF C]])

inductive interchange_relation :: "tm \<Rightarrow> 'e constructor_edge dart list \<Rightarrow>
    'e constructor_edge dart list \<Rightarrow> tm \<Rightarrow> bool" where
  square: "valid_shell S h P C \<Longrightarrow> two_slot S h P k before middle after \<Longrightarrow>
    c \<in> admitted \<Longrightarrow> d \<in> admitted \<Longrightarrow>
    interchange_relation (plug_term h C (square_start h s k before middle after c d))
      (lift_path C (square_lr h s t k before middle after c d))
      (lift_path C (square_rl h s t k before middle after c d))
      (plug_term h C (square_start h t k before middle after c d))"

lemma interchange_relation_typed:
  "interchange_relation x p q y \<Longrightarrow>
    walk_on admitted csrc cdst x p y \<and> walk_on admitted csrc cdst x q y"
  by (induct rule: interchange_relation.induct)
    (blast intro: shell_path_lifting square_paths_typed)

lemma interchange_endpoints_trees:
  "interchange_relation x p q y \<Longrightarrow> parameter_tree S h P x \<and> parameter_tree S h P y"
  by (induct rule: interchange_relation.induct)
    (blast intro: valid_shell_tree square_start_tree square_target_tree)

lemma original_interchange_typing:
  assumes R: "interchange_relation x p q y"
    and parameters: "\<And>j u. u \<in> P j \<Longrightarrow> wt S D G u (Hit j)"
  shows "wt S D G x (Hit h) \<and> wt S D G y (Hit h)"
  using interchange_endpoints_trees[OF R]
  by (auto intro: parameter_tree_typed[OF _ parameters])

lemma interchange_relation_lifting:
  "interchange_relation x p q y \<Longrightarrow> valid_shell S h P C \<Longrightarrow>
    interchange_relation (plug_term h C x) (lift_path C p) (lift_path C q) (plug_term h C y)"
  by (induct rule: interchange_relation.induct)
    (metis interchange_relation.square valid_shell_composition plug_term_composition lift_path_composition)

lemma presented_interchange_lifting:
  assumes Q: "presented_eq admitted csrc cdst interchange_relation x p q y" and V: "valid_shell S h P C"
  shows "presented_eq admitted csrc cdst interchange_relation
    (plug_term h C x) (lift_path C p) (lift_path C q) (plug_term h C y)"
  using Q
  by (induct rule: presented_eq.induct)
    (auto intro: presented_eq.intros shell_path_lifting[OF _ V]
      interchange_relation_lifting[OF _ V] lift_path_cancel)

sublocale presentation: path_presentation admitted csrc cdst interchange_relation .

definition constructor_on_classes where
  "constructor_on_classes C x y X = presentation.path_class (plug_term h C x)
    (lift_path C (presentation.representative X)) (plug_term h C y)"

lemma constructor_on_class:
  assumes W: "walk_on admitted csrc cdst x p y" and V: "valid_shell S h P C"
  shows "constructor_on_classes C x y (presentation.path_class x p y) =
    presentation.path_class (plug_term h C x) (lift_path C p) (plug_term h C y)"
  unfolding constructor_on_classes_def
  by (rule presentation.class_related[OF presented_eq.sym[OF
    presented_interchange_lifting[OF presentation.representative_related[OF W] V]]])

lemma constructor_on_classes_typed:
  assumes X: "X \<in> presentation.quotient_hom x y" and V: "valid_shell S h P C"
  shows "constructor_on_classes C x y X \<in>
    presentation.quotient_hom (plug_term h C x) (plug_term h C y)"
  unfolding constructor_on_classes_def
  by (rule presentation.class_in_hom[OF shell_path_lifting[OF presentation.representative_typed[OF X] V]])

lemma constructor_preserves_identity:
  assumes V: "valid_shell S h P C"
  shows "constructor_on_classes C x x (presentation.qidentity x) =
    presentation.qidentity (plug_term h C x)"
  by (simp add: presentation.qidentity_def constructor_on_class[OF _ V])

lemma constructor_preserves_composition:
  assumes X: "X \<in> presentation.quotient_hom x y" and Y: "Y \<in> presentation.quotient_hom y z"
    and V: "valid_shell S h P C"
  shows "constructor_on_classes C x z (presentation.qcompose x y z X Y) =
    presentation.qcompose (plug_term h C x) (plug_term h C y) (plug_term h C z)
      (constructor_on_classes C x y X) (constructor_on_classes C y z Y)"
proof -
  from X obtain p where P: "walk_on admitted csrc cdst x p y" and XP: "X = presentation.path_class x p y"
    by (auto simp: presentation.quotient_hom_def)
  from Y obtain q where Q: "walk_on admitted csrc cdst y q z" and YQ: "Y = presentation.path_class y q z"
    by (auto simp: presentation.quotient_hom_def)
  have PQ: "walk_on admitted csrc cdst x (p @ q) z" using P Q by auto
  show ?thesis
    by (simp only: XP YQ presentation.qcompose_class[OF P Q]
      constructor_on_class[OF P V] constructor_on_class[OF Q V] constructor_on_class[OF PQ V]
      presentation.qcompose_class[OF shell_path_lifting[OF P V] shell_path_lifting[OF Q V]] lift_path_append)
qed

lemma constructor_preserves_inverse:
  assumes X: "X \<in> presentation.quotient_hom x y" and V: "valid_shell S h P C"
  shows "constructor_on_classes C y x (presentation.qinverse x y X) =
    presentation.qinverse (plug_term h C x) (plug_term h C y) (constructor_on_classes C x y X)"
proof -
  from X obtain p where P: "walk_on admitted csrc cdst x p y" and XP: "X = presentation.path_class x p y"
    by (auto simp: presentation.quotient_hom_def)
  show ?thesis
    by (simp only: XP presentation.qinverse_class[OF P]
      constructor_on_class[OF P V] constructor_on_class[OF walk_on_reverse[OF P] V]
      presentation.qinverse_class[OF shell_path_lifting[OF P V]] lift_path_reverse)
qed

end

section \<open>Sufficient local laws for all-fiber interchange\<close>

text \<open>Point-method naturality only constrains values in the image of the
methods. It does not imply the following laws on every fiber element. We use
explicit independence of actions from the other slot's endpoint, and commuting
initial actions. They are required uniformly under valid outer shells, so
constructor lifting of an imposed equation is also sound.\<close>

locale interchange_family = mixed_context_graph S h P E s t +
  graph_family_on "{c. valid_parameter_context S h P E c}"
    "context_endpoint h s" "context_endpoint h t" F up down
  for S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set"
    and E :: "'e set" and s t :: "'e \<Rightarrow> tm" and F :: "tm \<Rightarrow> 'a set"
    and up down :: "'e constructor_edge \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes first_slot_independent:
    "valid_shell S h P C \<Longrightarrow> two_slot S h P k before middle after \<Longrightarrow>
     valid_parameter_context S h P E c \<Longrightarrow> valid_parameter_context S h P E d \<Longrightarrow>
     up (plug_edge C (Under k before c (middle @ [context_endpoint h t d] @ after))) =
     up (plug_edge C (Under k before c (middle @ [context_endpoint h s d] @ after)))"
    and second_slot_independent:
    "valid_shell S h P C \<Longrightarrow> two_slot S h P k before middle after \<Longrightarrow>
     valid_parameter_context S h P E c \<Longrightarrow> valid_parameter_context S h P E d \<Longrightarrow>
     up (plug_edge C (Under k (before @ [context_endpoint h t c] @ middle) d after)) =
     up (plug_edge C (Under k (before @ [context_endpoint h s c] @ middle) d after))"
    and slot_actions_commute:
    "valid_shell S h P C \<Longrightarrow> two_slot S h P k before middle after \<Longrightarrow>
     valid_parameter_context S h P E c \<Longrightarrow> valid_parameter_context S h P E d \<Longrightarrow>
     a \<in> F (plug_term h C (square_start h s k before middle after c d)) \<Longrightarrow>
     up (plug_edge C (Under k (before @ [context_endpoint h s c] @ middle) d after))
       (up (plug_edge C (Under k before c (middle @ [context_endpoint h s d] @ after))) a) =
     up (plug_edge C (Under k before c (middle @ [context_endpoint h s d] @ after)))
       (up (plug_edge C (Under k (before @ [context_endpoint h s c] @ middle) d after)) a)"
begin

lemma local_square_transport:
  assumes V: "valid_shell S h P C" and T: "two_slot S h P k before middle after"
    and L: "valid_parameter_context S h P E c" and R: "valid_parameter_context S h P E d"
    and A: "a \<in> F (plug_term h C (square_start h s k before middle after c d))"
  shows "transport (lift_path C (square_lr h s t k before middle after c d)) a =
    transport (lift_path C (square_rl h s t k before middle after c d)) a"
  using slot_actions_commute[OF V T L R A]
  by (simp only: square_lr_def square_rl_def lift_path_def list.map map_dart.simps
    transport.simps step_transport.simps first_slot_independent[OF V T L R] second_slot_independent[OF V T L R])

lemma generator_relation_transport:
  "interchange_relation x p q y \<Longrightarrow> a \<in> F x \<Longrightarrow> transport p a = transport q a"
  by (induct rule: interchange_relation.induct) (auto intro: local_square_transport)

sublocale quotient: quotient_family admitted csrc cdst F up down interchange_relation
  by unfold_locales
    (auto intro: up_type down_type down_up up_down generator_relation_transport)

lemma all_fiber_interchange_descent:
  "presented_eq admitted csrc cdst interchange_relation x p q y \<Longrightarrow>
    a \<in> F x \<Longrightarrow> transport p a = transport q a"
  by (rule quotient.presented_transport)

end

end
