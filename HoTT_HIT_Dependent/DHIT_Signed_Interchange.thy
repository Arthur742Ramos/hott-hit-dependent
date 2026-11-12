theory DHIT_Signed_Interchange
  imports DHIT_Interchange DHIT_Quotient_Functor
begin

section \<open>Signed interchange derived from positive generator squares\<close>

definition pair_term where
  "pair_term h k before middle after x y = PCon h k (before @ [x] @ middle @ [y] @ after)"

definition left_motion where
  "left_motion k before middle after y p = lift_path (Under k before (Generator ()) (middle @ [y] @ after)) p"

definition right_motion where
  "right_motion k before middle after x p = lift_path (Under k (before @ [x] @ middle) (Generator ()) after) p"

lemma left_motion_simps [simp]:
  "left_motion k before middle after y [] = []"
  "left_motion k before middle after y (p @ q) =
    left_motion k before middle after y p @ left_motion k before middle after y q"
  by (simp_all add: left_motion_def)

lemma right_motion_simps [simp]:
  "right_motion k before middle after x [] = []"
  "right_motion k before middle after x (p @ q) =
    right_motion k before middle after x p @ right_motion k before middle after x q"
  by (simp_all add: right_motion_def)

context mixed_context_graph
begin

lemma dart_source_tree:
  "dart_edge a \<in> admitted \<Longrightarrow> parameter_tree S h P (source csrc cdst a)"
  by (cases a) (auto intro: source_tree target_tree)

lemma dart_target_tree:
  "dart_edge a \<in> admitted \<Longrightarrow> parameter_tree S h P (target csrc cdst a)"
  by (cases a) (auto intro: source_tree target_tree)

lemma left_motion_typed:
  assumes T: "two_slot S h P k before middle after" and Y: "parameter_tree S h P y"
    and W: "walk_on admitted csrc cdst x p x'"
  shows "walk_on admitted csrc cdst (pair_term h k before middle after x y)
    (left_motion k before middle after y p) (pair_term h k before middle after x' y)"
proof -
  have C: "valid_shell S h P (Under k before (Generator ()) (middle @ [y] @ after))"
    by (intro valid_shell.under valid_shell.hole two_slot_left[OF T Y])
  from shell_path_lifting[OF W C] show ?thesis
    by (simp add: left_motion_def pair_term_def)
qed

lemma right_motion_typed:
  assumes T: "two_slot S h P k before middle after" and X: "parameter_tree S h P x"
    and W: "walk_on admitted csrc cdst y p y'"
  shows "walk_on admitted csrc cdst (pair_term h k before middle after x y)
    (right_motion k before middle after x p) (pair_term h k before middle after x y')"
proof -
  have C: "valid_shell S h P (Under k (before @ [x] @ middle) (Generator ()) after)"
    by (intro valid_shell.under valid_shell.hole two_slot_right[OF T X])
  from shell_path_lifting[OF W C] show ?thesis
    by (simp add: right_motion_def pair_term_def append_assoc)
qed

lemma positive_slot_interchange:
  assumes T: "two_slot S h P k before middle after" and C: "c \<in> admitted" and D: "d \<in> admitted"
  shows "presented_eq admitted csrc cdst interchange_relation
    (pair_term h k before middle after (csrc c) (csrc d))
    (left_motion k before middle after (csrc d) [Pos c] @
      right_motion k before middle after (cdst c) [Pos d])
    (right_motion k before middle after (csrc c) [Pos d] @
      left_motion k before middle after (cdst d) [Pos c])
    (pair_term h k before middle after (cdst c) (cdst d))"
proof -
  have R: "interchange_relation (square_start h s k before middle after c d)
      (square_lr h s t k before middle after c d) (square_rl h s t k before middle after c d)
      (square_start h t k before middle after c d)"
    using interchange_relation.square[OF valid_shell.hole T C D] by simp
  have H: "presented_eq admitted csrc cdst interchange_relation
      (square_start h s k before middle after c d)
      (square_lr h s t k before middle after c d) (square_rl h s t k before middle after c d)
      (square_start h t k before middle after c d)"
    by (rule presented_eq.generator)
      (rule R, rule square_paths_typed(1)[OF T C D], rule square_paths_typed(2)[OF T C D])
  from H show ?thesis
    by (simp add: square_start_def square_lr_def square_rl_def pair_term_def
      left_motion_def right_motion_def lift_path_def)
qed

lemma signed_slot_interchange:
  assumes T: "two_slot S h P k before middle after"
    and A: "dart_edge a \<in> admitted" and B: "dart_edge b \<in> admitted"
  shows "presented_eq admitted csrc cdst interchange_relation
    (pair_term h k before middle after (source csrc cdst a) (source csrc cdst b))
    (left_motion k before middle after (source csrc cdst b) [a] @
      right_motion k before middle after (target csrc cdst a) [b])
    (right_motion k before middle after (source csrc cdst a) [b] @
      left_motion k before middle after (target csrc cdst b) [a])
    (pair_term h k before middle after (target csrc cdst a) (target csrc cdst b))"
proof (cases a; cases b)
  fix c d assume AA: "a = Pos c" and BB: "b = Pos d"
  have C: "c \<in> admitted" and D: "d \<in> admitted" using A B AA BB by simp_all
  show ?thesis using positive_slot_interchange[OF T C D] AA BB by simp
next
  fix c d assume AA: "a = Pos c" and BB: "b = Neg d"
  have C: "c \<in> admitted" and D: "d \<in> admitted" using A B AA BB by simp_all
  have WC: "walk_on admitted csrc cdst (csrc c) [Pos c] (cdst c)" using C by simp
  have WD: "walk_on admitted csrc cdst (csrc d) [Pos d] (cdst d)" using D by simp
  note I = presented_square_inverse[OF
    right_motion_typed[OF T source_tree[OF C] WD]
    right_motion_typed[OF T target_tree[OF C] WD]
    left_motion_typed[OF T source_tree[OF D] WC]
    left_motion_typed[OF T target_tree[OF D] WC]
    presented_eq.sym[OF positive_slot_interchange[OF T C D]]]
  from presented_eq.sym[OF I] show ?thesis
    by (simp add: AA BB left_motion_def right_motion_def lift_path_def)
next
  fix c d assume AA: "a = Neg c" and BB: "b = Pos d"
  have C: "c \<in> admitted" and D: "d \<in> admitted" using A B AA BB by simp_all
  have WC: "walk_on admitted csrc cdst (csrc c) [Pos c] (cdst c)" using C by simp
  have WD: "walk_on admitted csrc cdst (csrc d) [Pos d] (cdst d)" using D by simp
  note I = presented_square_inverse[OF
    left_motion_typed[OF T source_tree[OF D] WC]
    left_motion_typed[OF T target_tree[OF D] WC]
    right_motion_typed[OF T source_tree[OF C] WD]
    right_motion_typed[OF T target_tree[OF C] WD]
    positive_slot_interchange[OF T C D]]
  from I show ?thesis by (simp add: AA BB left_motion_def right_motion_def lift_path_def)
next
  fix c d assume AA: "a = Neg c" and BB: "b = Neg d"
  have C: "c \<in> admitted" and D: "d \<in> admitted" using A B AA BB by simp_all
  from presented_eq.sym[OF presented_eq.inverse[OF positive_slot_interchange[OF T C D]]]
  show ?thesis by (simp add: AA BB left_motion_def right_motion_def lift_path_def)
qed

section \<open>Rectangular interchange for arbitrary signed paths\<close>

lemma walk_endpoint_tree:
  "walk_on admitted csrc cdst x p y \<Longrightarrow> parameter_tree S h P x \<Longrightarrow>
    parameter_tree S h P y"
  by (induct rule: walk_on_induct) (auto intro: dart_target_tree)

lemma dart_path_interchange:
  assumes T: "two_slot S h P k before middle after"
    and A: "dart_edge a \<in> admitted"
    and W: "walk_on admitted csrc cdst y q y'" and Y: "parameter_tree S h P y"
  shows "presented_eq admitted csrc cdst interchange_relation
    (pair_term h k before middle after (source csrc cdst a) y)
    (left_motion k before middle after y [a] @ right_motion k before middle after (target csrc cdst a) q)
    (right_motion k before middle after (source csrc cdst a) q @ left_motion k before middle after y' [a])
    (pair_term h k before middle after (target csrc cdst a) y')"
proof -
  let ?L = "left_motion k before middle after"
  let ?R = "right_motion k before middle after"
  let ?Pair = "pair_term h k before middle after"
  let ?sa = "source csrc cdst a"
  let ?ta = "target csrc cdst a"
  have WA: "walk_on admitted csrc cdst ?sa [a] ?ta" using A by simp
  have SA: "parameter_tree S h P ?sa" by (rule dart_source_tree[OF A])
  have TA: "parameter_tree S h P ?ta" by (rule dart_target_tree[OF A])
  show ?thesis using W Y
  proof (induct rule: walk_on_induct)
    case (nil y)
    from presented_eq.refl[OF left_motion_typed[OF T nil WA]] show ?case by simp
  next
    case (cons b q z)
    let ?sb = "source csrc cdst b"
    let ?tb = "target csrc cdst b"
    have TB: "parameter_tree S h P ?tb" by (rule dart_target_tree[OF cons(1)])
    have WB: "walk_on admitted csrc cdst ?sb [b] ?tb" using cons(1) by simp
    note IH = cons(3)[OF TB]
    note Sq = signed_slot_interchange[OF T A cons(1)]
    have Tail: "walk_on admitted csrc cdst (?Pair ?ta ?tb) (?R ?ta q) (?Pair ?ta z)"
      by (rule right_motion_typed[OF T TA cons(2)])
    have Head: "walk_on admitted csrc cdst (?Pair ?sa ?sb) (?R ?sa [b]) (?Pair ?sa ?tb)"
      by (rule right_motion_typed[OF T SA WB])
    have N: "walk_on admitted csrc cdst (?Pair ?sa ?sb) [] (?Pair ?sa ?sb)" by simp
    have NZ: "walk_on admitted csrc cdst (?Pair ?ta z) [] (?Pair ?ta z)" by simp
    have Q1: "presented_eq admitted csrc cdst interchange_relation (?Pair ?sa ?sb)
        (?L ?sb [a] @ ?R ?ta [b] @ ?R ?ta q)
        (?R ?sa [b] @ ?L ?tb [a] @ ?R ?ta q) (?Pair ?ta z)"
      using presented_context[OF Sq N Tail] by (simp add: append_assoc)
    have Q2: "presented_eq admitted csrc cdst interchange_relation (?Pair ?sa ?sb)
        (?R ?sa [b] @ ?L ?tb [a] @ ?R ?ta q)
        (?R ?sa [b] @ ?R ?sa q @ ?L z [a]) (?Pair ?ta z)"
      using presented_context[OF IH Head NZ] by (simp add: append_assoc)
    from presented_eq.trans[OF Q1 Q2] show ?case
      by (simp add: left_motion_def right_motion_def lift_path_def append_assoc)
  qed
qed

lemma two_path_interchange:
  assumes T: "two_slot S h P k before middle after"
    and X: "parameter_tree S h P x" and Y: "parameter_tree S h P y"
    and WP: "walk_on admitted csrc cdst x p x'" and WQ: "walk_on admitted csrc cdst y q y'"
  shows "presented_eq admitted csrc cdst interchange_relation
    (pair_term h k before middle after x y)
    (left_motion k before middle after y p @ right_motion k before middle after x' q)
    (right_motion k before middle after x q @ left_motion k before middle after y' p)
    (pair_term h k before middle after x' y')"
proof -
  let ?L = "left_motion k before middle after"
  let ?R = "right_motion k before middle after"
  let ?Pair = "pair_term h k before middle after"
  have Y': "parameter_tree S h P y'" by (rule walk_endpoint_tree[OF WQ Y])
  show ?thesis using WP X
  proof (induct rule: walk_on_induct)
    case (nil x)
    from presented_eq.refl[OF right_motion_typed[OF T nil WQ]] show ?case by simp
  next
    case (cons a p z)
    let ?sa = "source csrc cdst a"
    let ?ta = "target csrc cdst a"
    have TA: "parameter_tree S h P ?ta" by (rule dart_target_tree[OF cons(1)])
    have WA: "walk_on admitted csrc cdst ?sa [a] ?ta" using cons(1) by simp
    note IH = cons(3)[OF TA]
    note Sq = dart_path_interchange[OF T cons(1) WQ Y]
    have Head: "walk_on admitted csrc cdst (?Pair ?sa y) (?L y [a]) (?Pair ?ta y)"
      by (rule left_motion_typed[OF T Y WA])
    have Tail: "walk_on admitted csrc cdst (?Pair ?ta y') (?L y' p) (?Pair z y')"
      by (rule left_motion_typed[OF T Y' cons(2)])
    have N: "walk_on admitted csrc cdst (?Pair ?sa y) [] (?Pair ?sa y)" by simp
    have NZ: "walk_on admitted csrc cdst (?Pair z y') [] (?Pair z y')" by simp
    have Q1: "presented_eq admitted csrc cdst interchange_relation (?Pair ?sa y)
        (?L y [a] @ ?L y p @ ?R z q)
        (?L y [a] @ ?R ?ta q @ ?L y' p) (?Pair z y')"
      using presented_context[OF IH Head NZ] by (simp add: append_assoc)
    have Q2: "presented_eq admitted csrc cdst interchange_relation (?Pair ?sa y)
        (?L y [a] @ ?R ?ta q @ ?L y' p)
        (?R ?sa q @ ?L y' [a] @ ?L y' p) (?Pair z y')"
      using presented_context[OF Sq N Tail] by (simp add: append_assoc)
    from presented_eq.trans[OF Q1 Q2] show ?case
      by (simp add: left_motion_def right_motion_def lift_path_def append_assoc)
  qed
qed

end

context interchange_family
begin

lemma arbitrary_path_transport_interchange:
  assumes T: "two_slot S h P k before middle after"
    and X: "parameter_tree S h P x" and Y: "parameter_tree S h P y"
    and WP: "walk_on admitted csrc cdst x p x'" and WQ: "walk_on admitted csrc cdst y q y'"
    and V: "valid_shell S h P C"
    and A: "a \<in> F (plug_term h C (pair_term h k before middle after x y))"
  shows "transport (lift_path C (left_motion k before middle after y p @
      right_motion k before middle after x' q)) a =
    transport (lift_path C (right_motion k before middle after x q @
      left_motion k before middle after y' p)) a"
  by (rule quotient.presented_transport[OF
    presented_interchange_lifting[OF two_path_interchange[OF T X Y WP WQ] V] A])

end

end
