theory DHIT_Coherent_Signature
  imports DHIT_Endpoint_Paths DHIT_Interchange
begin

section \<open>A single presentation for interchange and generator naturality\<close>

lemma presented_eq_mono:
  assumes H: "presented_eq E s t R x p q y"
    and mono: "\<And>x p q y. R x p q y \<Longrightarrow> Q x p q y"
  shows "presented_eq E s t Q x p q y"
  using H
proof (induction rule: presented_eq.induct)
  case (refl x p y) show ?case by (rule presented_eq.refl[OF refl])
next
  case (generator x p q y)
  show ?case
    by (rule presented_eq.generator) (rule mono[OF generator(1)], rule generator(2), rule generator(3))
next
  case (cancel x p y q) show ?case by (rule presented_eq.cancel[OF cancel])
next
  case (sym x p q y) show ?case by (rule presented_eq.sym[OF sym.IH])
next
  case (trans x p q y r) show ?case by (rule presented_eq.trans[OF trans.IH])
next
  case (compose x p p' y q q' z) show ?case by (rule presented_eq.compose[OF compose.IH])
next
  case (inverse x p q y) show ?case by (rule presented_eq.inverse[OF inverse.IH])
qed

context signature_path_structure
begin

sublocale contexts: mixed_context_graph S h P edges src dst
  by (unfold_locales) (auto intro: source_tree target_tree)

inductive naturality_relation :: "tm \<Rightarrow> (nat \<times> tm list) constructor_edge dart list \<Rightarrow>
    (nat \<times> tm list) constructor_edge dart list \<Rightarrow> tm \<Rightarrow> bool" where
  square: "k < length (lcons (S h)) \<Longrightarrow>
    paths.argument_motion (lcons (S h) ! k) xs ps ys \<Longrightarrow>
    valid_shell S h P C \<Longrightarrow>
    naturality_relation (plug_term h C (lhsOf S h k xs))
      (lift_path C (endpoint_motion h xs ys ps (fst (lends (S h) ! k)) @ [Pos (Generator (k,ys))]))
      (lift_path C ([Pos (Generator (k,xs))] @ endpoint_motion h xs ys ps (snd (lends (S h) ! k))))
      (plug_term h C (rhsOf S h k ys))"

lemma naturality_relation_typed:
  "naturality_relation x p q y \<Longrightarrow>
    walk_on paths.admitted paths.cs paths.ct x p y \<and>
    walk_on paths.admitted paths.cs paths.ct x q y"
proof (induct rule: naturality_relation.induct)
  case (square k xs ps ys C)
  note X = paths.argument_motion_carriers(1)[OF square(2)]
  note Y = paths.argument_motion_carriers(2)[OF square(2)]
  note LP = original_endpoint_paths(1)[OF square(1,2)]
  note RP = original_endpoint_paths(2)[OF square(1,2)]
  note GX = canonical_generator_typed[OF square(1) X]
  note GY = canonical_generator_typed[OF square(1) Y]
  have L: "walk_on paths.admitted paths.cs paths.ct (lhsOf S h k xs)
    (endpoint_motion h xs ys ps (fst (lends (S h) ! k)) @ [Pos (Generator (k,ys))]) (rhsOf S h k ys)"
    using LP GY by auto
  have R: "walk_on paths.admitted paths.cs paths.ct (lhsOf S h k xs)
    ([Pos (Generator (k,xs))] @ endpoint_motion h xs ys ps (snd (lends (S h) ! k))) (rhsOf S h k ys)"
    using GX RP by auto
  show ?case using contexts.shell_path_lifting[OF L square(3)] contexts.shell_path_lifting[OF R square(3)]
    by blast
qed

lemma naturality_relation_lifting:
  "naturality_relation x p q y \<Longrightarrow> valid_shell S h P C \<Longrightarrow>
    naturality_relation (plug_term h C x) (lift_path C p) (lift_path C q) (plug_term h C y)"
proof (induct rule: naturality_relation.induct)
  case (square k xs ps ys D)
  have V: "valid_shell S h P (plug_edge C D)"
    by (rule valid_shell_composition[OF square.prems square.hyps(3)])
  from naturality_relation.square[OF square.hyps(1,2) V]
  show ?case by simp
qed

definition coherence_relation where
  "coherence_relation x p q y \<longleftrightarrow> contexts.interchange_relation x p q y \<or> naturality_relation x p q y"

lemma coherence_relation_typed:
  "coherence_relation x p q y \<Longrightarrow>
    walk_on paths.admitted paths.cs paths.ct x p y \<and> walk_on paths.admitted paths.cs paths.ct x q y"
  by (auto simp: coherence_relation_def dest: naturality_relation_typed contexts.interchange_relation_typed)

lemma coherence_relation_lifting:
  "coherence_relation x p q y \<Longrightarrow> valid_shell S h P C \<Longrightarrow>
    coherence_relation (plug_term h C x) (lift_path C p) (lift_path C q) (plug_term h C y)"
  by (auto simp: coherence_relation_def
      intro: naturality_relation_lifting contexts.interchange_relation_lifting)

lemma presented_coherence_lifting:
  assumes Q: "presented_eq paths.admitted paths.cs paths.ct coherence_relation x p q y"
    and V: "valid_shell S h P C"
  shows "presented_eq paths.admitted paths.cs paths.ct coherence_relation
    (plug_term h C x) (lift_path C p) (lift_path C q) (plug_term h C y)"
  using Q
proof (induction rule: presented_eq.induct)
  case (refl x p y)
  show ?case by (rule presented_eq.refl[OF contexts.shell_path_lifting[OF refl V]])
next
  case (generator x p q y)
  show ?case
    by (rule presented_eq.generator)
      (rule coherence_relation_lifting[OF generator(1) V],
       rule contexts.shell_path_lifting[OF generator(2) V],
       rule contexts.shell_path_lifting[OF generator(3) V])
next
  case (cancel x p y q)
  show ?case by (rule presented_eq.cancel[OF contexts.shell_path_lifting[OF cancel(1) V]
    lift_path_cancel[OF cancel(2)]])
next
  case (sym x p q y)
  show ?case by (rule presented_eq.sym[OF sym.IH])
next
  case (trans x p q y r)
  show ?case by (rule presented_eq.trans[OF trans.IH])
next
  case (compose x p p' y q q' z)
  show ?case using presented_eq.compose[OF compose.IH] by simp
next
  case (inverse x p q y)
  show ?case using presented_eq.inverse[OF inverse.IH] by simp
qed

end

locale coherent_signature_family = signature_path_structure S h P +
  fibers: interchange_family S h P "signature_edges S h P"
    "\<lambda>e. lhsOf S h (fst e) (snd e)" "\<lambda>e. rhsOf S h (fst e) (snd e)" F up down
  for S :: sigenv and h :: nat and P :: "nat \<Rightarrow> tm set"
    and F :: "tm \<Rightarrow> 'a set"
    and up down :: "(nat \<times> tm list) constructor_edge \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes naturality_law:
    "k < length (lcons (S h)) \<Longrightarrow>
     paths.argument_motion (lcons (S h) ! k) xs ps ys \<Longrightarrow>
     valid_shell S h P C \<Longrightarrow> a \<in> F (plug_term h C (lhsOf S h k xs)) \<Longrightarrow>
     fibers.transport (lift_path C (endpoint_motion h xs ys ps (fst (lends (S h) ! k)) @
       [Pos (Generator (k,ys))])) a =
     fibers.transport (lift_path C ([Pos (Generator (k,xs))] @
       endpoint_motion h xs ys ps (snd (lends (S h) ! k)))) a"
begin

lemma naturality_transport:
  "naturality_relation x p q y \<Longrightarrow> a \<in> F x \<Longrightarrow>
    fibers.transport p a = fibers.transport q a"
proof (induct rule: naturality_relation.induct)
  case (square k xs ps ys C)
  show ?case by (rule naturality_law[OF square.hyps square.prems])
qed

lemma coherence_transport:
  "coherence_relation x p q y \<Longrightarrow> a \<in> F x \<Longrightarrow>
    fibers.transport p a = fibers.transport q a"
  by (auto simp: coherence_relation_def intro: naturality_transport fibers.generator_relation_transport)

sublocale quotient: quotient_family paths.admitted paths.cs paths.ct F up down coherence_relation
  by unfold_locales
    (auto intro: fibers.up_type fibers.down_type fibers.down_up fibers.up_down coherence_transport)

lemma all_fiber_coherent_descent:
  "presented_eq paths.admitted paths.cs paths.ct coherence_relation x p q y \<Longrightarrow>
    a \<in> F x \<Longrightarrow> fibers.transport p a = fibers.transport q a"
  by (rule quotient.presented_transport)

end

end
