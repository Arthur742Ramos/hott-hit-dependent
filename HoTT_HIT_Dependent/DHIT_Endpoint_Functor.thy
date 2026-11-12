theory DHIT_Endpoint_Functor
  imports DHIT_Signed_Interchange DHIT_Argument_Graph
begin

text \<open>The sequential action of a finite constructor preserves composition
modulo the independently generated interchange presentation. No functor law is
assumed. Opaque parameter slots remain fixed.\<close>

abbreviation slot_motion where
  "slot_motion k bs zs p \<equiv> lift_path (Under k bs (Generator ()) zs) p"

lemma constructor_motion_Cons:
  "constructor_motion k bs (x # xs) (y # ys) (p # ps) =
    slot_motion k bs xs p @ constructor_motion k (bs @ [y]) xs ys ps"
proof -
  have F: "plug_edge (Under k bs (Generator ()) xs) = (\<lambda>c. Under k bs c xs)"
    by (rule ext) simp
  show ?thesis by (simp add: lift_path_def F)
qed

declare constructor_motion.simps(2)[simp del]
declare constructor_motion_Cons[simp]

lemma constructor_motion_identity:
  "constructor_motion k bs xs xs (replicate (length xs) []) = []"
  by (induct xs arbitrary: bs) simp_all

locale endpoint_functor = mixed_context_graph S h P E s t
  for S h P E s t
begin

sublocale paths: parameter_path_structure S h P E s t
  by unfold_locales (auto intro: source_points target_points)

abbreviation eqp where "eqp \<equiv> presented_eq admitted csrc cdst interchange_relation"

lemma slot_motion_typed:
  "parameter_slot S h P k bs zs \<Longrightarrow> walk_on admitted csrc cdst x p y \<Longrightarrow>
   walk_on admitted csrc cdst (PCon h k (bs @ [x] @ zs))
     (slot_motion k bs zs p) (PCon h k (bs @ [y] @ zs))"
  using shell_path_lifting[of x p y "Under k bs (Generator ()) zs"]
  by (auto intro: valid_shell.under)

lemma constructor_tail_interchange:
  assumes K: "k < length (pcons (S h))"
    and shape: "pcons (S h) ! k = bs @ [Rec] @ ms @ ss"
    and B: "parameter_arguments S h P bs before"
    and M: "parameter_arguments S h P ms middle"
    and X: "parameter_tree S h P x"
    and W: "walk_on admitted csrc cdst x p x'"
    and A: "paths.argument_motion ss xs qs ys"
  shows "eqp (PCon h k (before @ [x] @ middle @ xs))
    (slot_motion k before (middle @ xs) p @
      constructor_motion k (before @ [x'] @ middle) xs ys qs)
    (constructor_motion k (before @ [x] @ middle) xs ys qs @
      slot_motion k before (middle @ ys) p)
    (PCon h k (before @ [x'] @ middle @ ys))"
  using shape M A
proof (induct ss arbitrary: ms middle xs qs ys)
  case Nil
  have sl: "parameter_slot S h P k before middle"
    using K Nil.prems(1,2) B unfolding parameter_slot_def by auto
  from presented_eq.refl[OF slot_motion_typed[OF sl W]] Nil.prems(3)
  show ?case by simp
next
  case (Cons r rs)
  obtain y yt q qt z zt where xs: "xs = y # yt" and qs: "qs = q # qt" and ys: "ys = z # zt"
    using Cons.prems(3) unfolding paths.argument_motion_def
    by (cases xs; cases qs; cases ys) auto
  have ext: "external_arity h [r]" and T: "paths.typed_motion (argTy h r) y q z"
    and tail: "paths.argument_motion rs yt qt zt"
    using Cons.prems(3) by (simp_all add: xs qs ys paths.argument_motion_cons)
  have Z: "parameter_arguments S h P [r] [z]"
    using ext T by (simp add: parameter_arguments_def paths.typed_motion_def)
  have MM: "parameter_arguments S h P (ms @ [r]) (middle @ [z])"
    by (rule parameter_arguments_append[OF Cons.prems(2) Z])
  have sh: "pcons (S h) ! k = bs @ [Rec] @ (ms @ [r]) @ rs"
    using Cons.prems(1) by simp
  note IH = Cons.hyps[OF sh MM tail]
  show ?case
  proof (cases r)
    case (Par j)
    have J: "j \<noteq> h" using ext Par by (simp add: external_arity_def)
    have "y = z" "q = []" using T J Par by (auto simp: paths.typed_motion_def)
    with IH show ?thesis by (simp add: xs qs ys constructor_motion_Cons append_assoc)
  next
    case Rec
    have Y: "parameter_tree S h P y" and Q: "walk_on admitted csrc cdst y q z"
      using T Rec by (auto simp: paths.typed_motion_def parameter_carrier_def)
    have TT: "two_slot S h P k before middle yt"
      unfolding two_slot_def using K Cons.prems(1,2) B
        paths.argument_motion_carriers(1)[OF tail] Rec by auto
    note SQ = two_path_interchange[OF TT X Y W Q]
    have XP: "parameter_tree S h P x'" by (rule walk_endpoint_tree[OF W X])
    have BB: "parameter_arguments S h P (bs @ [Rec] @ ms @ [r])
      (before @ [x'] @ middle @ [z])"
      using parameter_arguments_append[OF B parameter_arguments_append[OF parameter_arguments_rec[OF XP]
        parameter_arguments_append[OF Cons.prems(2) Z]]]
      by simp
    have sh2: "pcons (S h) ! k = (bs @ [Rec] @ ms @ [r]) @ rs"
      using Cons.prems(1) by simp
    have WT: "walk_on admitted csrc cdst
      (PCon h k ((before @ [x'] @ middle @ [z]) @ yt))
      (constructor_motion k (before @ [x'] @ middle @ [z]) yt zt qt)
      (PCon h k ((before @ [x'] @ middle @ [z]) @ zt))"
      by (rule paths.constructor_motion_typed[OF K sh2 BB tail])
    have WH: "walk_on admitted csrc cdst
      (pair_term h k before middle yt x y)
      (right_motion k before middle yt x q)
      (pair_term h k before middle yt x z)"
      by (rule right_motion_typed[OF TT X Q])
    have H1: "eqp (PCon h k (before @ [x] @ middle @ xs))
      (slot_motion k before (middle @ xs) p @ constructor_motion k (before @ [x'] @ middle) xs ys qs)
      (right_motion k before middle yt x q @
        slot_motion k before ((middle @ [z]) @ yt) p @
        constructor_motion k (before @ [x'] @ (middle @ [z])) yt zt qt)
      (PCon h k (before @ [x'] @ middle @ ys))"
      using presented_context[OF
        SQ[unfolded pair_term_def, simplified append_assoc append.simps append_Nil]
        _ WT[simplified append_assoc append.simps append_Nil],
        of "pair_term h k before middle yt x y" "[]"]
      by (simp add: xs qs ys constructor_motion_Cons pair_term_def left_motion_def right_motion_def append_assoc)
    have H2: "eqp (PCon h k (before @ [x] @ middle @ xs))
      (right_motion k before middle yt x q @
        slot_motion k before ((middle @ [z]) @ yt) p @
        constructor_motion k (before @ [x'] @ (middle @ [z])) yt zt qt)
      (constructor_motion k (before @ [x] @ middle) xs ys qs @ slot_motion k before (middle @ ys) p)
      (PCon h k (before @ [x'] @ middle @ ys))"
      using presented_context[OF IH[simplified append_assoc append.simps append_Nil]
        WH[unfolded pair_term_def, simplified append_assoc append.simps append_Nil],
        of "[]" "PCon h k (before @ [x'] @ middle @ ys)"]
      by (simp add: xs qs ys constructor_motion_Cons pair_term_def right_motion_def append_assoc)
    show ?thesis by (rule presented_eq.trans[OF H1 H2])
  qed
qed

lemma typed_motion_compose:
  assumes A: "paths.typed_motion A x p y" and B: "paths.typed_motion A y q z"
  shows "paths.typed_motion A x (p @ q) z"
proof (cases "A = Hit h")
  case True
  have P: "walk_on admitted csrc cdst x p y" and Q: "walk_on admitted csrc cdst y q z"
    using A B True by (simp_all add: paths.typed_motion_def)
  have W: "walk_on admitted csrc cdst x (p @ q) z" using P Q by auto
  show ?thesis using A B W True by (simp add: paths.typed_motion_def)
next
  case False
  with A B show ?thesis by (simp add: paths.typed_motion_def)
qed

lemma argument_motion_compose:
  assumes P: "paths.argument_motion ss xs ps ys" and Q: "paths.argument_motion ss ys qs zs"
  shows "paths.argument_motion ss xs (map2 (@) ps qs) zs"
proof -
  have L: "length xs = length ss" "length ps = length ss" "length qs = length ss" "length zs = length ss"
    and X: "external_arity h ss" using P Q by (auto simp: paths.argument_motion_def)
  have T: "\<And>i. i < length ss \<Longrightarrow>
    paths.typed_motion (argTy h (ss ! i)) (xs ! i) ((ps ! i) @ (qs ! i)) (zs ! i)"
  proof -
    fix i assume I: "i < length ss"
    have A: "paths.typed_motion (argTy h (ss ! i)) (xs ! i) (ps ! i) (ys ! i)"
      using P I by (simp add: paths.argument_motion_def)
    have B: "paths.typed_motion (argTy h (ss ! i)) (ys ! i) (qs ! i) (zs ! i)"
      using Q I by (simp add: paths.argument_motion_def)
    show "paths.typed_motion (argTy h (ss ! i)) (xs ! i) ((ps ! i) @ (qs ! i)) (zs ! i)"
      by (rule typed_motion_compose[OF A B])
  qed
  show ?thesis using L X T by (auto simp: paths.argument_motion_def)
qed

lemma constructor_motion_compose:
  assumes K: "k < length (pcons (S h))"
    and shape: "pcons (S h) ! k = bs @ ss"
    and B: "parameter_arguments S h P bs before"
    and A: "paths.argument_motion ss xs ps ys"
    and D: "paths.argument_motion ss ys qs zs"
  shows "eqp (PCon h k (before @ xs))
    (constructor_motion k before xs zs (map2 (@) ps qs))
    (constructor_motion k before xs ys ps @ constructor_motion k before ys zs qs)
    (PCon h k (before @ zs))"
  using shape B A D
proof (induct ss arbitrary: bs before xs ps ys qs zs)
  case Nil
  then show ?case by (simp add: presented_eq.refl)
next
  case (Cons r rs)
  obtain x xt p pt y yt q qt z zt where
    xs: "xs = x # xt" and ps: "ps = p # pt" and ys: "ys = y # yt"
    and qs: "qs = q # qt" and zs: "zs = z # zt"
    using Cons.prems(3,4) unfolding paths.argument_motion_def
    by (cases xs; cases ps; cases ys; cases qs; cases zs) auto
  have ext: "external_arity h [r]" and TP: "paths.typed_motion (argTy h r) x p y"
    and AP: "paths.argument_motion rs xt pt yt"
    and TQ: "paths.typed_motion (argTy h r) y q z"
    and AQ: "paths.argument_motion rs yt qt zt"
    using Cons.prems(3,4) by (simp_all add: xs ps ys qs zs paths.argument_motion_cons)
  have Z: "parameter_arguments S h P [r] [z]"
    using ext TQ by (simp add: parameter_arguments_def paths.typed_motion_def)
  have BB: "parameter_arguments S h P (bs @ [r]) (before @ [z])"
    by (rule parameter_arguments_append[OF Cons.prems(2) Z])
  have sh: "pcons (S h) ! k = (bs @ [r]) @ rs" using Cons.prems(1) by simp
  note IH = Cons.hyps[OF sh BB AP AQ]
  show ?case
  proof (cases r)
    case (Par j)
    have J: "j \<noteq> h" using ext Par by (simp add: external_arity_def)
    have "x = y" "y = z" "p = []" "q = []"
      using TP TQ J Par by (auto simp: paths.typed_motion_def)
    with IH show ?thesis by (simp add: xs ps ys qs zs constructor_motion_Cons)
  next
    case Rec
    have X: "parameter_tree S h P x" and Y: "parameter_tree S h P y"
      and WP: "walk_on admitted csrc cdst x p y" and WQ: "walk_on admitted csrc cdst y q z"
      using TP TQ Rec by (auto simp: paths.typed_motion_def parameter_carrier_def)
    have sl: "parameter_slot S h P k before xt"
      using K Cons.prems(1,2) paths.argument_motion_carriers(1)[OF AP] Rec
      by (auto simp: parameter_slot_def)
    note HP = slot_motion_typed[OF sl WP]
    note HQ = slot_motion_typed[OF sl WQ]
    have HH: "walk_on admitted csrc cdst (PCon h k (before @ [x] @ xt))
      (slot_motion k before xt (p @ q)) (PCon h k (before @ [z] @ xt))"
      by (rule slot_motion_typed[OF sl]) (use WP WQ in auto)
    have H1: "eqp (PCon h k (before @ xs))
      (constructor_motion k before xs zs (map2 (@) ps qs))
      (slot_motion k before xt p @ slot_motion k before xt q @
        constructor_motion k (before @ [z]) xt yt pt @ constructor_motion k (before @ [z]) yt zt qt)
      (PCon h k (before @ zs))"
      using presented_context[OF IH[simplified append_assoc append.simps append_Nil]
        HH[simplified append_assoc append.simps append_Nil],
        of "[]" "PCon h k (before @ zs)"]
      by (simp add: xs ps ys qs zs constructor_motion_Cons append_assoc)
    have sh0: "pcons (S h) ! k = bs @ [Rec] @ [] @ rs"
      using Cons.prems(1) Rec by simp
    have M0: "parameter_arguments S h P [] []"
      by (simp add: parameter_arguments_def external_arity_def)
    note SQ = constructor_tail_interchange[OF K sh0 Cons.prems(2) M0 Y WQ AP]
    have WT: "walk_on admitted csrc cdst (PCon h k ((before @ [z]) @ yt))
      (constructor_motion k (before @ [z]) yt zt qt) (PCon h k ((before @ [z]) @ zt))"
      by (rule paths.constructor_motion_typed[OF K sh BB AQ])
    have H2: "eqp (PCon h k (before @ xs))
      (slot_motion k before xt p @ slot_motion k before xt q @
        constructor_motion k (before @ [z]) xt yt pt @ constructor_motion k (before @ [z]) yt zt qt)
      (constructor_motion k before xs ys ps @ constructor_motion k before ys zs qs)
      (PCon h k (before @ zs))"
      using presented_context[OF SQ[simplified append_assoc append.simps append_Nil]
        HP[simplified append_assoc append.simps append_Nil]
        WT[simplified append_assoc append.simps append_Nil]]
      by (simp add: xs ps ys qs zs constructor_motion_Cons append_assoc)
    show ?thesis by (rule presented_eq.trans[OF H1 H2])
  qed
qed

lemma constructor_motion_cong:
  assumes K: "k < length (pcons (S h))"
    and shape: "pcons (S h) ! k = bs @ ss"
    and B: "parameter_arguments S h P bs before"
    and A: "paths.argument_motion ss xs ps ys"
    and D: "paths.argument_motion ss xs qs ys"
    and C: "\<And>i. i < length ss \<Longrightarrow> eqp (xs ! i) (ps ! i) (qs ! i) (ys ! i)"
  shows "eqp (PCon h k (before @ xs))
    (constructor_motion k before xs ys ps) (constructor_motion k before xs ys qs)
    (PCon h k (before @ ys))"
  using shape B A D C
proof (induct ss arbitrary: bs before xs ps ys qs)
  case Nil
  then show ?case by (simp add: presented_eq.refl)
next
  case (Cons r rs)
  obtain x xt p pt y yt q qt where xs: "xs = x # xt" and ps: "ps = p # pt"
    and ys: "ys = y # yt" and qs: "qs = q # qt"
    using Cons.prems(3,4) unfolding paths.argument_motion_def
    by (cases xs; cases ps; cases ys; cases qs) auto
  have ext: "external_arity h [r]" and TP: "paths.typed_motion (argTy h r) x p y"
    and AP: "paths.argument_motion rs xt pt yt"
    and TQ: "paths.typed_motion (argTy h r) x q y"
    and AQ: "paths.argument_motion rs xt qt yt"
    using Cons.prems(3,4) by (simp_all add: xs ps ys qs paths.argument_motion_cons)
  have Y: "parameter_arguments S h P [r] [y]"
    using ext TP by (simp add: parameter_arguments_def paths.typed_motion_def)
  have BB: "parameter_arguments S h P (bs @ [r]) (before @ [y])"
    by (rule parameter_arguments_append[OF Cons.prems(2) Y])
  have sh: "pcons (S h) ! k = (bs @ [r]) @ rs" using Cons.prems(1) by simp
  have CT: "\<And>i. i < length rs \<Longrightarrow> eqp (xt ! i) (pt ! i) (qt ! i) (yt ! i)"
    using Cons.prems(5)[of "Suc _"] by (simp add: xs ps ys qs)
  have IH: "eqp (PCon h k ((before @ [y]) @ xt))
    (constructor_motion k (before @ [y]) xt yt pt)
    (constructor_motion k (before @ [y]) xt yt qt) (PCon h k ((before @ [y]) @ yt))"
    by (rule Cons.hyps[OF sh BB AP AQ]) (rule CT)
  show ?case
  proof (cases r)
    case (Par j)
    have J: "j \<noteq> h" using ext Par by (simp add: external_arity_def)
    have "x = y" "p = []" "q = []" using TP TQ J Par by (auto simp: paths.typed_motion_def)
    with IH show ?thesis by (simp add: xs ps ys qs constructor_motion_Cons)
  next
    case Rec
    have sl: "parameter_slot S h P k before xt"
      using K Cons.prems(1,2) paths.argument_motion_carriers(1)[OF AP] Rec
      by (auto simp: parameter_slot_def)
    have V: "valid_shell S h P (Under k before (Generator ()) xt)"
      by (intro valid_shell.under valid_shell.hole sl)
    have H: "eqp x p q y" using Cons.prems(5)[of 0] by (simp add: xs ps ys qs)
    note L = presented_interchange_lifting[OF H V]
    from presented_eq.compose[OF L[simplified] IH[simplified]]
    show ?thesis by (simp add: xs ps ys qs constructor_motion_Cons append_assoc)
  qed
qed

lemma typed_motion_walk:
  "paths.typed_motion A x p y \<Longrightarrow> walk_on admitted csrc cdst x p y"
  by (auto simp: paths.typed_motion_def split: if_splits)

lemma endpoint_motion_arguments:
  assumes L: "length es = length ds"
    and E: "\<And>i. i < length es \<Longrightarrow> wf_endpt S h ss (es ! i) (argTy h (ds ! i))"
    and M: "paths.argument_motion ss xs ps ys"
    and X: "external_arity h ds"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "paths.argument_motion ds (map (instE h xs) es)
    (map (endpoint_motion h xs ys ps) es) (map (instE h ys) es)"
proof -
  have T: "\<And>i. i < length es \<Longrightarrow>
    paths.typed_motion (argTy h (ds ! i)) (instE h xs (es ! i))
      (endpoint_motion h xs ys ps (es ! i)) (instE h ys (es ! i))"
    by (rule paths.endpoint_motion_typed[OF E M points]) assumption
  show ?thesis using L X T by (auto simp: paths.argument_motion_def)
qed

lemma endpoint_motion_compose:
  assumes endpoint: "wf_endpt S h ss e A"
    and P: "paths.argument_motion ss xs ps ys"
    and Q: "paths.argument_motion ss ys qs zs"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "eqp (instE h xs e)
    (endpoint_motion h xs zs (map2 (@) ps qs) e)
    (endpoint_motion h xs ys ps e @ endpoint_motion h ys zs qs e)
    (instE h zs e)"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  have T: "paths.typed_motion (argTy h (ss ! i)) (xs ! i) ((map2 (@) ps qs) ! i) (zs ! i)"
    using argument_motion_compose[OF P Q] wfEArg unfolding paths.argument_motion_def by blast
  from presented_eq.refl[OF typed_motion_walk[OF T]] P Q wfEArg
  show ?case by (simp add: paths.argument_motion_def)
next
  case (wfECon k es)
  let ?ss = "pcons (S h) ! k"
  let ?xs = "map (instE h xs) es"
  let ?ys = "map (instE h ys) es"
  let ?zs = "map (instE h zs) es"
  let ?ps = "map (endpoint_motion h xs ys ps) es"
  let ?qs = "map (endpoint_motion h ys zs qs) es"
  let ?cs = "map (endpoint_motion h xs zs (map2 (@) ps qs)) es"
  have M1: "paths.argument_motion ?ss ?xs ?ps ?ys"
    by (rule endpoint_motion_arguments[OF wfECon(2) _ P points[OF wfECon(1)] points])
      (use wfECon(3) in auto)
  have M2: "paths.argument_motion ?ss ?ys ?qs ?zs"
    by (rule endpoint_motion_arguments[OF wfECon(2) _ Q points[OF wfECon(1)] points])
      (use wfECon(3) in auto)
  have M3: "paths.argument_motion ?ss ?xs ?cs ?zs"
    by (rule endpoint_motion_arguments[OF wfECon(2) _ argument_motion_compose[OF P Q] points[OF wfECon(1)] points])
      (use wfECon(3) in auto)
  have B0: "parameter_arguments S h P [] []"
    by (simp add: parameter_arguments_def external_arity_def)
  have C: "\<And>i. i < length ?ss \<Longrightarrow> eqp (?xs ! i) (?cs ! i) ((map2 (@) ?ps ?qs) ! i) (?zs ! i)"
    using wfECon by auto
  have H1: "eqp (PCon h k ?xs) (constructor_motion k [] ?xs ?zs ?cs)
    (constructor_motion k [] ?xs ?zs (map2 (@) ?ps ?qs)) (PCon h k ?zs)"
    using constructor_motion_cong[OF wfECon(1) _ B0 M3 argument_motion_compose[OF M1 M2]] C
    by simp
  have H2: "eqp (PCon h k ?xs) (constructor_motion k [] ?xs ?zs (map2 (@) ?ps ?qs))
    (constructor_motion k [] ?xs ?ys ?ps @ constructor_motion k [] ?ys ?zs ?qs) (PCon h k ?zs)"
    using constructor_motion_compose[OF wfECon(1) _ B0 M1 M2] by simp
  have H: "eqp (PCon h k ?xs) (constructor_motion k [] ?xs ?zs ?cs)
    (constructor_motion k [] ?xs ?ys ?ps @ constructor_motion k [] ?ys ?zs ?qs) (PCon h k ?zs)"
    by (rule presented_eq.trans[OF H1 H2])
  show ?case using H by simp
qed

lemma endpoint_motion_identity:
  assumes W: "wf_endpt S h ss e A" and L: "length xs = length ss"
  shows "endpoint_motion h xs xs (replicate (length xs) ([] :: 'e constructor_edge dart list)) e = []"
  using W
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case using L by simp
next
  case (wfECon k es)
  let ?zero = "replicate (length xs) ([] :: 'e constructor_edge dart list)"
  have H: "\<And>i. i < length es \<Longrightarrow> endpoint_motion h xs xs ?zero (es ! i) = []"
    by (rule conjunct2[OF wfECon(3)[rule_format]]) assumption
  have M: "map (endpoint_motion h xs xs ?zero) es =
    replicate (length es) ([] :: 'e constructor_edge dart list)"
    by (rule nth_equalityI) (auto simp: H)
  have CM: "constructor_motion k [] (map (instE h xs) es) (map (instE h xs) es)
    (replicate (length es) ([] :: 'e constructor_edge dart list)) = []"
    using constructor_motion_identity[of k "[]" "map (instE h xs) es"] by simp
  show ?case by (simp only: endpoint_motion.simps M CM)
qed

lemma endpoint_motion_cong:
  assumes endpoint: "wf_endpt S h ss e A"
    and P: "paths.argument_motion ss xs ps ys"
    and Q: "paths.argument_motion ss xs qs ys"
    and C: "\<And>i. i < length ss \<Longrightarrow> eqp (xs ! i) (ps ! i) (qs ! i) (ys ! i)"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "eqp (instE h xs e) (endpoint_motion h xs ys ps e)
    (endpoint_motion h xs ys qs e) (instE h ys e)"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case using C by simp
next
  case (wfECon k es)
  let ?ss = "pcons (S h) ! k"
  let ?xs = "map (instE h xs) es"
  let ?ys = "map (instE h ys) es"
  let ?ps = "map (endpoint_motion h xs ys ps) es"
  let ?qs = "map (endpoint_motion h xs ys qs) es"
  have M1: "paths.argument_motion ?ss ?xs ?ps ?ys"
    by (rule endpoint_motion_arguments[OF wfECon(2) _ P points[OF wfECon(1)] points])
      (use wfECon(3) in auto)
  have M2: "paths.argument_motion ?ss ?xs ?qs ?ys"
    by (rule endpoint_motion_arguments[OF wfECon(2) _ Q points[OF wfECon(1)] points])
      (use wfECon(3) in auto)
  have B0: "parameter_arguments S h P [] []"
    by (simp add: parameter_arguments_def external_arity_def)
  have C0: "\<And>i. i < length ?ss \<Longrightarrow> eqp (?xs ! i) (?ps ! i) (?qs ! i) (?ys ! i)"
    using wfECon by auto
  from constructor_motion_cong[OF wfECon(1) _ B0 M1 M2 C0]
  show ?case by simp
qed

lemma argument_motion_inverse:
  "paths.argument_motion ss xs ps ys \<Longrightarrow>
    paths.argument_motion ss ys (map reverse_path ps) xs"
  by (auto simp: paths.argument_motion_def paths.typed_motion_def intro: walk_on_reverse)

lemma presented_right_inverse_unique:
  assumes W: "walk_on admitted csrc cdst x p y"
    and V: "walk_on admitted csrc cdst y q x"
    and H: "eqp x (p @ q) [] x"
  shows "eqp y q (reverse_path p) x"
proof -
  have A: "eqp y (reverse_path p @ p @ q) (reverse_path p) x"
    using presented_context[OF H walk_on_reverse[OF W], of "[]" x] by simp
  have B: "eqp y (reverse_path p @ p @ q) q x"
    using presented_context[OF presented_inverse_left[OF W] _ V, of y "[]"]
    by (simp add: append_assoc)
  show ?thesis by (rule presented_eq.trans[OF presented_eq.sym[OF B] A])
qed

lemma endpoint_motion_inverse:
  assumes endpoint: "wf_endpt S h ss e A"
    and P: "paths.argument_motion ss xs ps ys"
    and points: "\<And>k. k < length (pcons (S h)) \<Longrightarrow> external_arity h (pcons (S h) ! k)"
  shows "eqp (instE h ys e)
    (endpoint_motion h ys xs (map reverse_path ps) e)
    (reverse_path (endpoint_motion h xs ys ps e)) (instE h xs e)"
proof -
  note Q = argument_motion_inverse[OF P]
  note C = argument_motion_compose[OF P Q]
  note I = paths.argument_motion_identity[OF paths.argument_motion_carriers(1)[OF P]]
  have L: "length xs = length ss" using P by (simp add: paths.argument_motion_def)
  have CP: "\<And>i. i < length ss \<Longrightarrow>
    eqp (xs ! i) ((map2 (@) ps (map reverse_path ps)) ! i)
      ((replicate (length xs) []) ! i) (xs ! i)"
  proof -
    fix i assume i: "i < length ss"
    have T: "paths.typed_motion (argTy h (ss ! i)) (xs ! i) (ps ! i) (ys ! i)"
      using P i by (simp add: paths.argument_motion_def)
    from presented_inverse_right[OF typed_motion_walk[OF T]] P i L
    show "eqp (xs ! i) ((map2 (@) ps (map reverse_path ps)) ! i)
      ((replicate (length xs) []) ! i) (xs ! i)"
      by (simp add: paths.argument_motion_def)
  qed
  have Z: "eqp (instE h xs e)
    (endpoint_motion h xs xs (map2 (@) ps (map reverse_path ps)) e) [] (instE h xs e)"
    using endpoint_motion_cong[OF endpoint C I CP points]
    by (simp add: endpoint_motion_identity[OF endpoint L])
  have H: "eqp (instE h xs e)
    (endpoint_motion h xs ys ps e @ endpoint_motion h ys xs (map reverse_path ps) e)
    [] (instE h xs e)"
    by (rule presented_eq.trans[OF presented_eq.sym[OF endpoint_motion_compose[OF endpoint P Q points]] Z])
  show ?thesis
    by (rule presented_right_inverse_unique[OF
      typed_motion_walk[OF paths.endpoint_motion_typed[OF endpoint P points]]
      typed_motion_walk[OF paths.endpoint_motion_typed[OF endpoint Q points]] H])
qed

end

text \<open>The original recursive simplification rule is restored for
theories importing this module.\<close>
declare constructor_motion_Cons[simp del]
declare constructor_motion.simps(2)[simp]

end
