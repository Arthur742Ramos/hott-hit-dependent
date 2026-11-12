theory DHIT_Type_Formers
  imports DHIT_Families
begin

section \<open>Dependent sums and products of transported families\<close>

text \<open>The second fiber depends on both the vertex and an element of the
first fiber. Product elements are functions normalized to \<open>undefined\<close>
outside their domain. This normalization supplies literal equality of functions,
without identifying functions only up to equality on a fiber. No inhabitant of
any fiber is assumed.\<close>

locale dependent_graph_family = graph_family s t F up down
  for s t :: "'e \<Rightarrow> 'v"
    and F :: "'v \<Rightarrow> 'a set"
    and up down :: "'e \<Rightarrow> 'a \<Rightarrow> 'a" +
  fixes G :: "'v \<Rightarrow> 'a \<Rightarrow> 'b set"
    and upG downG :: "'e \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes upG_type: "a \<in> F (s e) \<Longrightarrow> b \<in> G (s e) a \<Longrightarrow>
      upG e a b \<in> G (t e) (up e a)"
    and downG_type: "a \<in> F (t e) \<Longrightarrow> b \<in> G (t e) a \<Longrightarrow>
      downG e a b \<in> G (s e) (down e a)"
    and downG_upG: "a \<in> F (s e) \<Longrightarrow> b \<in> G (s e) a \<Longrightarrow>
      downG e (up e a) (upG e a b) = b"
    and upG_downG: "a \<in> F (t e) \<Longrightarrow> b \<in> G (t e) a \<Longrightarrow>
      upG e (down e a) (downG e a b) = b"
begin

definition sigma_fiber :: "'v \<Rightarrow> ('a \<times> 'b) set" where
  "sigma_fiber x = {(a,b). a \<in> F x \<and> b \<in> G x a}"

definition sigma_up :: "'e \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b)" where
  "sigma_up e z = (up e (fst z), upG e (fst z) (snd z))"

definition sigma_down :: "'e \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b)" where
  "sigma_down e z = (down e (fst z), downG e (fst z) (snd z))"

sublocale sigma: graph_family s t sigma_fiber sigma_up sigma_down
  by standard
    (auto simp: sigma_fiber_def sigma_up_def sigma_down_def
      intro: up_type down_type upG_type downG_type
      simp: down_up up_down downG_upG upG_downG)

definition pi_fiber :: "'v \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "pi_fiber x = {f. (\<forall>a \<in> F x. f a \<in> G x a) \<and>
    (\<forall>a. a \<notin> F x \<longrightarrow> f a = undefined)}"

definition pi_up :: "'e \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "pi_up e f a = (if a \<in> F (t e)
    then upG e (down e a) (f (down e a)) else undefined)"

definition pi_down :: "'e \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "pi_down e f a = (if a \<in> F (s e)
    then downG e (up e a) (f (up e a)) else undefined)"

lemma pi_up_type:
  "f \<in> pi_fiber (s e) \<Longrightarrow> pi_up e f \<in> pi_fiber (t e)"
  unfolding pi_fiber_def pi_up_def
  by (auto dest: down_type; metis upG_type down_type up_down)

lemma pi_down_type:
  "f \<in> pi_fiber (t e) \<Longrightarrow> pi_down e f \<in> pi_fiber (s e)"
  unfolding pi_fiber_def pi_down_def
  by (auto dest: up_type; metis downG_type up_type down_up)

lemma pi_down_up:
  assumes "f \<in> pi_fiber (s e)"
  shows "pi_down e (pi_up e f) = f"
proof (rule ext)
  fix a
  show "pi_down e (pi_up e f) a = f a"
    using assms
    by (auto simp: pi_fiber_def pi_down_def pi_up_def
      up_type down_up downG_upG)
qed

lemma pi_up_down:
  assumes "f \<in> pi_fiber (t e)"
  shows "pi_up e (pi_down e f) = f"
proof (rule ext)
  fix a
  show "pi_up e (pi_down e f) a = f a"
    using assms
    by (auto simp: pi_fiber_def pi_down_def pi_up_def
      down_type up_down upG_downG)
qed

sublocale pi: graph_family s t pi_fiber pi_up pi_down
  by standard (auto intro: pi_up_type pi_down_type pi_down_up pi_up_down)

subsection \<open>Introduction, elimination, and computation\<close>

lemma sigma_pair_type:
  "a \<in> F x \<Longrightarrow> b \<in> G x a \<Longrightarrow> (a,b) \<in> sigma_fiber x"
  by (simp add: sigma_fiber_def)

lemma sigma_projections_type:
  "z \<in> sigma_fiber x \<Longrightarrow> fst z \<in> F x \<and> snd z \<in> G x (fst z)"
  by (auto simp: sigma_fiber_def)

definition pi_lambda :: "'v \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "pi_lambda x f a = (if a \<in> F x then f a else undefined)"

lemma pi_lambda_type:
  "(\<And>a. a \<in> F x \<Longrightarrow> f a \<in> G x a) \<Longrightarrow>
    pi_lambda x f \<in> pi_fiber x"
  by (simp add: pi_lambda_def pi_fiber_def)

lemma pi_application_type:
  "f \<in> pi_fiber x \<Longrightarrow> a \<in> F x \<Longrightarrow> f a \<in> G x a"
  by (simp add: pi_fiber_def)

lemma pi_beta:
  "a \<in> F x \<Longrightarrow> pi_lambda x f a = f a"
  by (simp add: pi_lambda_def)

lemma pi_eta:
  "f \<in> pi_fiber x \<Longrightarrow> pi_lambda x (\<lambda>a. f a) = f"
  by (rule ext) (auto simp: pi_lambda_def pi_fiber_def)

text \<open>Evaluation commutes with dependent product transport. The argument
itself moves in the first family, and the result moves in the second family.\<close>

lemma pi_evaluation_naturality:
  assumes "a \<in> F (s e)"
  shows "pi_up e f (up e a) = upG e a (f a)"
  using assms by (simp add: pi_up_def up_type down_up)

lemma sigma_first_naturality:
  "fst (sigma_up e z) = up e (fst z)"
  by (simp add: sigma_up_def)

lemma sigma_second_naturality:
  "snd (sigma_up e z) = upG e (fst z) (snd z)"
  by (simp add: sigma_up_def)

end

section \<open>A genuinely dependent instance\<close>

text \<open>The second fiber is the singleton containing the first component at
one endpoint and its successor at the other. Thus the second family depends on
both the base vertex and the chosen first component.\<close>

interpretation successor_fibers: dependent_graph_family
  "\<lambda>_::unit. False" "\<lambda>_::unit. True"
  "\<lambda>_::bool. UNIV::nat set" "\<lambda>_. id" "\<lambda>_. id"
  "\<lambda>x a. {a + (if x then 1 else 0)}"
  "\<lambda>_ _. Suc" "\<lambda>_ _ b. b - 1"
  by unfold_locales auto

lemma successor_sigma_transport:
  "successor_fibers.sigma_up () (n,n) = (n,Suc n)"
  by (simp add: successor_fibers.sigma_up_def)

lemma successor_pi_transport:
  "successor_fibers.pi_up () id = Suc"
  by (rule ext) (simp add: successor_fibers.pi_up_def)

end
