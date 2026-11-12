theory DHIT_Dependent_Transport
  imports DHIT_Type_Formers
begin

section \<open>Transport in a family depending on a transported element\<close>

context dependent_graph_family
begin

fun dependent_step :: "'e dart \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
  "dependent_step (Pos e) a b = upG e a b"
| "dependent_step (Neg e) a b = downG e a b"

fun dependent_transport :: "'e dart list \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
  "dependent_transport [] a b = b"
| "dependent_transport (d # p) a b =
    dependent_transport p (step_transport d a) (dependent_step d a b)"

lemma sigma_step_pair:
  "sigma.step_transport d (a,b) = (step_transport d a, dependent_step d a b)"
  by (cases d) (simp_all add: sigma_up_def sigma_down_def)

lemma sigma_transport_pair:
  "sigma.transport p (a,b) = (transport p a, dependent_transport p a b)"
  by (induct p arbitrary: a b) (simp_all add: sigma_step_pair)

lemma dependent_transport_type:
  assumes "walk s t x p y" "a \<in> F x" "b \<in> G x a"
  shows "dependent_transport p a b \<in> G y (transport p a)"
  using sigma.transport_type[OF assms(1) sigma_pair_type[OF assms(2,3)]]
  by (simp add: sigma_transport_pair sigma_fiber_def)

lemma dependent_transport_composition:
  "dependent_transport (p @ q) a b =
    dependent_transport q (transport p a) (dependent_transport p a b)"
  by (induct p arbitrary: a b) simp_all

lemma dependent_transport_reverse:
  assumes "walk s t x p y" "a \<in> F x" "b \<in> G x a"
  shows "dependent_transport (reverse_path p) (transport p a)
      (dependent_transport p a b) = b"
  using sigma.transport_reverse[OF assms(1) sigma_pair_type[OF assms(2,3)]]
  by (simp add: sigma_transport_pair)

lemma dependent_transport_respects_equality:
  assumes "path_equal s t x p q y" "a \<in> F x" "b \<in> G x a"
  shows "dependent_transport p a b = dependent_transport q a b"
  using sigma.transport_equal[OF assms(1) sigma_pair_type[OF assms(2,3)]]
  by (simp add: sigma_transport_pair)

lemma pi_step_evaluation:
  assumes "a \<in> F (source s t d)"
  shows "pi.step_transport d f (step_transport d a) = dependent_step d a (f a)"
  using assms
  by (cases d) (simp_all add: pi_up_def pi_down_def up_type down_type down_up up_down)

lemma pi_path_evaluation:
  assumes "walk s t x p y" "a \<in> F x"
  shows "pi.transport p f (transport p a) = dependent_transport p a (f a)"
  using assms
  by (induct arbitrary: a f rule: walk.induct)
    (simp_all add: pi_step_evaluation step_type)

text \<open>Cancellation preserves the dependent result in its destination
fiber, not merely the underlying unindexed value. This is the subject-reduction
statement for the transported family, not for a new lambda calculus.\<close>

lemma dependent_cancellation_subject_reduction:
  assumes C: "cancel p q" and W: "walk s t x p y"
    and A: "a \<in> F x" and B: "b \<in> G x a"
  shows "walk s t x q y \<and> transport p a = transport q a \<and>
    dependent_transport p a b = dependent_transport q a b \<and>
    dependent_transport q a b \<in> G y (transport p a)"
proof -
  have Q: "walk s t x q y" by (rule cancel_subject_reduction[OF C W])
  have E: "path_equal s t x p q y" by (rule path_equal.cancel[OF W C])
  show ?thesis using Q transport_equal[OF E A]
    dependent_transport_respects_equality[OF E A B]
    dependent_transport_type[OF Q A B] by simp
qed

end

end
