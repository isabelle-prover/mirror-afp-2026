theory HIT_Confluence
  imports HIT_Normalization
begin

section \<open>Confluence\<close>

subsection \<open>A dimension-capture critical pair\<close>

definition capture_arg :: tm where
  "capture_arg = LCon 2 0 [] (DVar 0)"

definition capture_body :: tm where
  "capture_body =
    HElim 1 (Hit 2) [] [Var 0] (Var 1)"

definition capture_method :: tm where
  "capture_method =
    App (Lam (Hit 2) capture_body) capture_arg"

definition capture_source :: tm where
  "capture_source =
    HElim 0 (Hit 2) [] [capture_method]
      (LCon 0 0 [] (DVar 1))"

definition capture_left :: tm where
  "capture_left =
    HElim 1 (Hit 2) [] [LCon 2 0 [] (DVar 1)] (Var 0)"

definition capture_right :: tm where
  "capture_right =
    HElim 1 (Hit 2) [] [LCon 2 0 [] (DVar 0)] (Var 0)"

lemma capture_argument_not_dclosed:
  "\<not> dclosed0 S capture_arg"
  unfolding dclosed0_def capture_arg_def by auto

lemma capture_substitute_then_instantiate:
  "dsubst S 0 (DVar 1)
      (subst 0 capture_arg capture_body) = capture_right"
  unfolding capture_arg_def capture_body_def capture_right_def by simp

lemma capture_instantiate_then_substitute:
  "subst 0 (dsubst S 0 (DVar 1) capture_arg)
      (dsubst S 0 (DVar 1) capture_body) = capture_left"
  unfolding capture_arg_def capture_body_def capture_left_def by simp

lemma capture_critical_pair_distinct:
  "dsubst S 0 (DVar 1)
      (subst 0 capture_arg capture_body) \<noteq>
    subst 0 (dsubst S 0 (DVar 1) capture_arg)
      (dsubst S 0 (DVar 1) capture_body)"
  using capture_substitute_then_instantiate
    capture_instantiate_then_substitute
  unfolding capture_left_def capture_right_def by simp

text \<open>
  The critical pair above is the reason that rule \<open>red.beta\<close> requires
  its argument to be stable under instantiation of the reserved dimension.
  A dimension-dependent beta redex is merely postponed until the surrounding
  path method has been instantiated.  This is the smallest restriction that
  makes beta substitution commute with path computation; ordinary ambient
  terms satisfy it by dimension freshness.
\<close>

subsection \<open>Multi-step compatibility\<close>

lemma reds_context:
  assumes mono: "\<And>x y. red S x y \<Longrightarrow> red S (f x) (f y)"
    and steps: "reds S x y"
  shows "reds S (f x) (f y)"
  using steps
proof (induct rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have "red S (f y) (f z)" by (rule mono[OF step.hyps(2)])
  with step.hyps(3) show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma reds_App:
  assumes "reds S t t'" and "reds S u u'"
  shows "reds S (App t u) (App t' u')"
proof -
  have left: "reds S (App t u) (App t' u)"
    by (rule reds_context[OF red.appL assms(1)])
  have right: "reds S (App t' u) (App t' u')"
    by (rule reds_context[OF red.appR assms(2)])
  show ?thesis by (rule rtranclp_trans[OF left right])
qed

lemma reds_Lam:
  "reds S t t' \<Longrightarrow> reds S (Lam A t) (Lam A t')"
  by (rule reds_context[OF red.lam])

abbreviation list_reds ::
  "sigenv \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "list_reds S xs ys \<equiv> list_all2 (reds S) xs ys"

lemma list_reds_refl [simp]: "list_reds S xs xs"
  by (induct xs) auto

lemma list_reds_length:
  "list_reds S xs ys \<Longrightarrow> length xs = length ys"
  by (rule list_all2_lengthD)

lemma list_reds_nth:
  assumes "list_reds S xs ys" and "i < length xs"
  shows "reds S (xs ! i) (ys ! i)"
  using assms by (metis list_all2_nthD)

lemma reds_PCon_lists:
  assumes "list_reds S xs ys"
  shows "reds S (PCon h k (pre @ xs)) (PCon h k (pre @ ys))"
  using assms
proof (induct arbitrary: pre)
  case Nil
  show ?case by simp
next
  case (Cons x xs y ys)
  have head: "reds S
      (PCon h k (pre @ x # xs))
      (PCon h k (pre @ y # xs))"
    by (rule reds_context[
          where f = "\<lambda>z. PCon h k (pre @ z # xs)",
          OF _ Cons.hyps(1)])
      (auto intro: red.pconArg)
  have tail: "reds S
      (PCon h k ((pre @ [y]) @ xs))
      (PCon h k ((pre @ [y]) @ ys))"
    by (rule Cons.hyps(3))
  have tail': "reds S
      (PCon h k (pre @ y # xs))
      (PCon h k (pre @ y # ys))"
    using tail by simp
  show ?case by (rule rtranclp_trans[OF head tail'])
qed

lemma reds_PCon:
  "list_reds S xs ys \<Longrightarrow>
    reds S (PCon h k xs) (PCon h k ys)"
  using reds_PCon_lists[where pre = "[]"] by simp

lemma reds_LCon_lists:
  assumes "list_reds S xs ys"
  shows "reds S (LCon h k (pre @ xs) d) (LCon h k (pre @ ys) d)"
  using assms
proof (induct arbitrary: pre)
  case Nil
  show ?case by simp
next
  case (Cons x xs y ys)
  have head: "reds S
      (LCon h k (pre @ x # xs) d)
      (LCon h k (pre @ y # xs) d)"
    by (rule reds_context[
          where f = "\<lambda>z. LCon h k (pre @ z # xs) d",
          OF _ Cons.hyps(1)])
      (auto intro: red.lconArg)
  have tail: "reds S
      (LCon h k ((pre @ [y]) @ xs) d)
      (LCon h k ((pre @ [y]) @ ys) d)"
    by (rule Cons.hyps(3))
  have tail': "reds S
      (LCon h k (pre @ y # xs) d)
      (LCon h k (pre @ y # ys) d)"
    using tail by simp
  show ?case by (rule rtranclp_trans[OF head tail'])
qed

lemma reds_LCon:
  "list_reds S xs ys \<Longrightarrow>
    reds S (LCon h k xs d) (LCon h k ys d)"
  using reds_LCon_lists[where pre = "[]"] by simp

lemma reds_HElim_pms_lists:
  assumes "list_reds S xs ys"
  shows "reds S
    (HElim h C (pre @ xs) lms t)
    (HElim h C (pre @ ys) lms t)"
  using assms
proof (induct arbitrary: pre)
  case Nil
  show ?case by simp
next
  case (Cons x xs y ys)
  have head: "reds S
      (HElim h C (pre @ x # xs) lms t)
      (HElim h C (pre @ y # xs) lms t)"
    by (rule reds_context[
          where f = "\<lambda>z. HElim h C (pre @ z # xs) lms t",
          OF _ Cons.hyps(1)])
      (auto intro: red.elimPm)
  have tail: "reds S
      (HElim h C ((pre @ [y]) @ xs) lms t)
      (HElim h C ((pre @ [y]) @ ys) lms t)"
    by (rule Cons.hyps(3))
  have tail': "reds S
      (HElim h C (pre @ y # xs) lms t)
      (HElim h C (pre @ y # ys) lms t)"
    using tail by simp
  show ?case by (rule rtranclp_trans[OF head tail'])
qed

lemma reds_HElim_pms:
  "list_reds S pms pms' \<Longrightarrow>
    reds S (HElim h C pms lms t) (HElim h C pms' lms t)"
  using reds_HElim_pms_lists[where pre = "[]"] by simp

lemma reds_HElim_lms_lists:
  assumes "list_reds S xs ys"
  shows "reds S
    (HElim h C pms (pre @ xs) t)
    (HElim h C pms (pre @ ys) t)"
  using assms
proof (induct arbitrary: pre)
  case Nil
  show ?case by simp
next
  case (Cons x xs y ys)
  have head: "reds S
      (HElim h C pms (pre @ x # xs) t)
      (HElim h C pms (pre @ y # xs) t)"
    by (rule reds_context[
          where f = "\<lambda>z. HElim h C pms (pre @ z # xs) t",
          OF _ Cons.hyps(1)])
      (auto intro: red.elimLm)
  have tail: "reds S
      (HElim h C pms ((pre @ [y]) @ xs) t)
      (HElim h C pms ((pre @ [y]) @ ys) t)"
    by (rule Cons.hyps(3))
  have tail': "reds S
      (HElim h C pms (pre @ y # xs) t)
      (HElim h C pms (pre @ y # ys) t)"
    using tail by simp
  show ?case by (rule rtranclp_trans[OF head tail'])
qed

lemma reds_HElim_lms:
  "list_reds S lms lms' \<Longrightarrow>
    reds S (HElim h C pms lms t) (HElim h C pms lms' t)"
  using reds_HElim_lms_lists[where pre = "[]"] by simp

lemma reds_HElim_scrutinee:
  "reds S t t' \<Longrightarrow>
    reds S (HElim h C pms lms t) (HElim h C pms lms t')"
  by (rule reds_context[OF red.elimScrutinee])

lemma reds_HElim:
  assumes "list_reds S pms pms'" and "list_reds S lms lms'"
    and "reds S t t'"
  shows "reds S
    (HElim h C pms lms t) (HElim h C pms' lms' t')"
proof -
  have p: "reds S
      (HElim h C pms lms t) (HElim h C pms' lms t)"
    by (rule reds_HElim_pms[OF assms(1)])
  have l: "reds S
      (HElim h C pms' lms t) (HElim h C pms' lms' t)"
    by (rule reds_HElim_lms[OF assms(2)])
  have s: "reds S
      (HElim h C pms' lms' t) (HElim h C pms' lms' t')"
    by (rule reds_HElim_scrutinee[OF assms(3)])
  show ?thesis
    by (rule rtranclp_trans[OF rtranclp_trans[OF p l] s])
qed

lemma reds_apps:
  assumes "reds S t t'" and "list_reds S xs ys"
  shows "reds S (apps t xs) (apps t' ys)"
  using assms(2) assms(1)
proof (induct arbitrary: t t')
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  have "reds S (App t x) (App t' y)"
    by (rule reds_App[OF Cons.prems Cons.hyps(1)])
  from Cons.hyps(3)[OF this] show ?case by simp
qed

lemma list_reds_trans:
  assumes "list_reds S xs ys" and "list_reds S ys zs"
  shows "list_reds S xs zs"
  using assms
proof (induct arbitrary: zs rule: list_all2_induct)
  case Nil
  then show ?case by (cases zs) auto
next
  case (Cons x xs y ys)
  then obtain z zs' where zs: "zs = z # zs'"
    by (cases zs) auto
  have yz: "reds S y z" and tails: "list_reds S ys zs'"
    using Cons.prems zs by auto
  have "reds S x z"
    by (rule rtranclp_trans[OF Cons.hyps(1) yz])
  moreover have "list_reds S xs zs'"
    by (rule Cons.hyps(3)[OF tails])
  ultimately show ?case using zs by auto
qed

lemma elimArgs_list_reds:
  assumes pms: "list_reds S pms pms'"
    and lms: "list_reds S lms lms'"
    and args: "list_reds S as as'"
  shows "list_reds S
    (elimArgs h C pms lms ss as)
    (elimArgs h C pms' lms' ss as')"
  using args
proof (induct ss arbitrary: as as')
  case Nil
  show ?case by simp
next
  case (Cons s ss)
  show ?case
  proof (cases as)
    case Nil
    then have "as' = []" using Cons.prems by (cases as') auto
    with Nil show ?thesis by simp
  next
    case (Cons a xs)
    then obtain b ys where
      as': "as' = b # ys" and ab: "reds S a b"
      and tails: "list_reds S xs ys"
      using Cons.prems by (cases as') auto
    have rest: "list_reds S
        (elimArgs h C pms lms ss xs)
        (elimArgs h C pms' lms' ss ys)"
      by (rule Cons.hyps[OF tails])
    show ?thesis
    proof (cases s)
      case (Par h')
      with Cons as' ab rest show ?thesis by simp
    next
      case Rec
      have rec: "reds S
          (HElim h C pms lms a)
          (HElim h C pms' lms' b)"
        by (rule reds_HElim[OF pms lms ab])
      with Rec Cons as' ab rest show ?thesis by simp
    qed
  qed
qed

lemma reds_subst_argument:
  assumes step: "red S s s'" and reg: "regular S s"
  shows "reds S (subst n s t) (subst n s' t)"
  using step reg
proof (induct t arbitrary: n s s')
  case (Var i)
  show ?case
  proof (cases "i < n")
    case True
    then show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "i = n")
      case True
      have "reds S s s'"
        by (rule r_into_rtranclp[where r = "red S", OF Var.prems(1)])
      with True show ?thesis by simp
    next
      case False
      with \<open>\<not> i < n\<close> show ?thesis by simp
    qed
  qed
next
  case (Lam A t)
  have lifted: "red S (lift 0 s) (lift 0 s')"
    using red_vrename[OF Lam.prems(1,2), of "shift_ren 0"]
    by (simp add: lift_as_vrename)
  have reg_lift: "regular S (lift 0 s)"
    by (rule regular_lift[OF Lam.prems(2)])
  have "reds S
      (subst (Suc n) (lift 0 s) t)
      (subst (Suc n) (lift 0 s') t)"
    by (rule Lam.hyps[OF lifted reg_lift])
  then show ?case by (auto intro: reds_Lam)
next
  case (App t u)
  have left: "reds S (subst n s t) (subst n s' t)"
    by (rule App.hyps(1)[OF App.prems])
  have right: "reds S (subst n s u) (subst n s' u)"
    by (rule App.hyps(2)[OF App.prems])
  show ?case by (simp add: reds_App[OF left right])
next
  case (PCon h k as)
  have lr: "list_reds S
      (map (subst n s) as) (map (subst n s') as)"
    using PCon.hyps PCon.prems
    by (induct as) auto
  show ?case by (simp add: reds_PCon[OF lr])
next
  case (LCon h k as d)
  have lr: "list_reds S
      (map (subst n s) as) (map (subst n s') as)"
    using LCon.hyps LCon.prems
    by (induct as) auto
  show ?case by (simp add: reds_LCon[OF lr])
next
  case (HElim h C pms lms t)
  have p: "list_reds S
      (map (subst n s) pms) (map (subst n s') pms)"
    using HElim.hyps(1) HElim.prems by (induct pms) auto
  have l: "list_reds S
      (map (subst n s) lms) (map (subst n s') lms)"
    using HElim.hyps(2) HElim.prems by (induct lms) auto
  have q: "reds S (subst n s t) (subst n s' t)"
    by (rule HElim.hyps(3)[OF HElim.prems])
  show ?case by (simp add: reds_HElim[OF p l q])
qed

subsection \<open>Dimension-safe reduction\<close>

lemma dclosed0_lift:
  assumes "variable_dims t" and "dclosed0 S t"
  shows "dclosed0 S (lift n t)"
  using dclosed0_vrename[OF assms(1), of S "shift_ren n"] assms(2)
  by (simp add: lift_as_vrename)

lemma dclosed0_up_sub:
  assumes "\<And>i. dclosed0 S (s i)"
    and "\<And>i. variable_dims (s i)"
  shows "dclosed0 S (up_sub s i)"
  using assms
  by (cases i) (auto intro: dclosed0_lift)

lemma psubst_dsubst_zero_dclosed:
  assumes dims: "variable_dims t"
    and env_closed: "\<And>i. dclosed0 S (s i)"
    and env_dims: "\<And>i. variable_dims (s i)"
  shows "psubst s (dsubst S 0 (DVar j) t) =
    dsubst S 0 (DVar j) (psubst s t)"
  using dims env_closed env_dims
proof (induct t arbitrary: s j)
  case (Var i)
  then show ?case
    using Var.prems(2)[of i] unfolding dclosed0_def by simp
next
  case (Lam A t)
  have closed: "\<And>i. dclosed0 S (up_sub s i)"
    by (rule dclosed0_up_sub[OF Lam.prems(2,3)])
  have dims: "\<And>i. variable_dims (up_sub s i)"
    by (rule variable_dims_up_sub[OF Lam.prems(3)])
  from Lam.hyps[OF _ closed dims] Lam.prems show ?case by simp
next
  case (LCon h k as d)
  then obtain q where d: "d = DVar q" by auto
  from LCon d show ?case
    by (cases "q = 0") (auto simp: list_all_iff map_map)
qed (auto simp: list_all_iff map_map)

lemma dclosed0_psubst_closed:
  assumes dims: "variable_dims t" and closed: "dclosed0 S t"
    and env_closed: "\<And>i. dclosed0 S (s i)"
    and env_dims: "\<And>i. variable_dims (s i)"
  shows "dclosed0 S (psubst s t)"
proof (unfold dclosed0_def, intro allI)
  fix j
  have "dsubst S 0 (DVar j) (psubst s t) =
      psubst s (dsubst S 0 (DVar j) t)"
    using psubst_dsubst_zero_dclosed[
      where S = S and t = t and s = s and j = j,
      OF dims env_closed env_dims]
    by simp
  also have "\<dots> = psubst s t"
    using closed unfolding dclosed0_def by simp
  finally show "dsubst S 0 (DVar j) (psubst s t) = psubst s t" .
qed

lemma dclosed0_subst:
  assumes dims_t: "variable_dims t" and closed_t: "dclosed0 S t"
    and dims_s: "variable_dims s" and closed_s: "dclosed0 S s"
  shows "dclosed0 S (subst n s t)"
proof -
  have env_closed: "\<And>i. dclosed0 S (single_sub n s i)"
    unfolding single_sub_def
    using closed_s by (auto intro: dclosed0_lift)
  have env_dims: "\<And>i. variable_dims (single_sub n s i)"
    unfolding single_sub_def
    using dims_s by (auto intro: variable_dims_lift)
  have "dclosed0 S (psubst (single_sub n s) t)"
    by (rule dclosed0_psubst_closed[
          OF dims_t closed_t env_closed env_dims])
  then show ?thesis by (simp add: subst_as_psubst)
qed

lemma red_psubst_dclosed:
  assumes step: "red S t u" and reg: "regular S t"
    and env_reg: "\<And>i. regular S (s i)"
    and env_closed: "\<And>i. dclosed0 S (s i)"
  shows "red S (psubst s t) (psubst s u)"
  using step reg env_reg env_closed
proof (induct arbitrary: s rule: red.induct)
  case (beta u A t)
  have regt: "regular S t" and regu: "regular S u"
    using beta.prems(1) by simp_all
  have dimst: "variable_dims t"
    by (rule regular_variable_dims[OF regt])
  have dimsu: "variable_dims u"
    by (rule regular_variable_dims[OF regu])
  have env_dims: "\<And>i. variable_dims (s i)"
    by (rule regular_variable_dims[OF beta.prems(2)])
  have closed_arg: "dclosed0 S (psubst s u)"
    by (rule dclosed0_psubst_closed[
          OF dimsu beta.hyps(1) beta.prems(3) env_dims])
  have raw: "red S
      (App (Lam A (psubst (up_sub s) t)) (psubst s u))
      (subst 0 (psubst s u) (psubst (up_sub s) t))"
    by (rule red.beta[OF closed_arg])
  from raw show ?case by (simp add: subst0_psubst)
next
  case (elimPoint k h C pms lms as)
  have raw: "red S
      (HElim h C (map (psubst s) pms) (map (psubst s) lms)
        (PCon h k (map (psubst s) as)))
      (apps ((map (psubst s) pms) ! k)
        (elimArgs h C (map (psubst s) pms) (map (psubst s) lms)
          (pcons (S h) ! k) (map (psubst s) as)))"
    by (rule red.elimPoint[
          where S = S and h = h and k = k and C = C
            and pms = "map (psubst s) pms"
            and lms = "map (psubst s) lms"
            and as = "map (psubst s) as",
          OF elimPoint.hyps(1)])
  from raw show ?case
    using elimPoint by (simp add: psubst_elimArgs)
next
  case (elimPath k h C pms lms as j)
  have mreg: "regular S (lms ! k)"
    using elimPath by (auto simp: list_all_iff)
  have mdims: "variable_dims (lms ! k)"
    by (rule regular_variable_dims[OF mreg])
  have env_dims: "\<And>i. variable_dims (s i)"
    by (rule regular_variable_dims[OF elimPath.prems(2)])
  have method:
      "psubst s (dsubst S 0 (DVar j) (lms ! k)) =
        dsubst S 0 (DVar j) (psubst s (lms ! k))"
    by (rule psubst_dsubst_zero_dclosed[
          OF mdims elimPath.prems(3) env_dims])
  have raw: "red S
      (HElim h C (map (psubst s) pms) (map (psubst s) lms)
        (LCon h k (map (psubst s) as) (DVar j)))
      (apps (dsubst S 0 (DVar j) ((map (psubst s) lms) ! k))
        (elimArgs h C (map (psubst s) pms) (map (psubst s) lms)
          (lcons (S h) ! k) (map (psubst s) as)))"
    by (rule red.elimPath[
          where S = S and h = h and k = k and C = C
            and pms = "map (psubst s) pms"
            and lms = "map (psubst s) lms"
            and as = "map (psubst s) as" and j = j,
          OF elimPath.hyps(1)])
  from raw method show ?case
    using elimPath by (simp add: psubst_elimArgs)
next
  case (appL t t' u)
  then show ?case by (auto intro: red.appL)
next
  case (appR u u' t)
  then show ?case by (auto intro: red.appR)
next
  case (lam t t' A)
  have up_reg: "\<And>i. regular S (up_sub s i)"
    by (rule regular_up_sub[OF lam.prems(2)])
  have env_dims: "\<And>i. variable_dims (s i)"
    by (rule regular_variable_dims[OF lam.prems(2)])
  have up_closed: "\<And>i. dclosed0 S (up_sub s i)"
    by (rule dclosed0_up_sub[OF lam.prems(3) env_dims])
  have "red S (psubst (up_sub s) t) (psubst (up_sub s) t')"
    by (rule lam.hyps(2)[OF _ up_reg up_closed])
      (use lam.prems(1) in simp)
  then show ?case by (auto intro: red.lam)
next
  case (pconArg a a' h k xs ys)
  have rega: "regular S a"
    using pconArg.prems(1) by (auto simp: list_all_iff)
  have "red S (psubst s a) (psubst s a')"
    by (rule pconArg.hyps(2)[OF rega pconArg.prems(2,3)])
  then show ?case by (auto intro: red.pconArg)
next
  case (lconArg a a' h k xs ys d)
  have rega: "regular S a"
    using lconArg.prems(1) by (auto simp: list_all_iff)
  have "red S (psubst s a) (psubst s a')"
    by (rule lconArg.hyps(2)[OF rega lconArg.prems(2,3)])
  then show ?case by (auto intro: red.lconArg)
next
  case (elimPm m m' h C xs ys lms t)
  have regm: "regular S m"
    using elimPm.prems(1) by (auto simp: list_all_iff)
  have "red S (psubst s m) (psubst s m')"
    by (rule elimPm.hyps(2)[OF regm elimPm.prems(2,3)])
  then show ?case by (auto intro: red.elimPm)
next
  case (elimLm m m' h C pms xs ys t)
  have regm: "regular S m"
    using elimLm.prems(1) by (auto simp: list_all_iff)
  have "red S (psubst s m) (psubst s m')"
    by (rule elimLm.hyps(2)[OF regm elimLm.prems(2,3)])
  then show ?case by (auto intro: red.elimLm)
next
  case (elimScrutinee t t' h C pms lms)
  have regt: "regular S t" using elimScrutinee.prems(1) by simp
  have "red S (psubst s t) (psubst s t')"
    by (rule elimScrutinee.hyps(2)[
          OF regt elimScrutinee.prems(2,3)])
  then show ?case by (auto intro: red.elimScrutinee)
qed

lemma red_subst_dclosed:
  assumes step: "red S t t'" and regt: "regular S t"
    and regs: "regular S s" and closeds: "dclosed0 S s"
  shows "red S (subst n s t) (subst n s t')"
proof -
  have env_reg: "\<And>i. regular S (single_sub n s i)"
    unfolding single_sub_def
    using regs by (auto intro: regular_lift)
  have env_closed: "\<And>i. dclosed0 S (single_sub n s i)"
    unfolding single_sub_def
    using regs closeds regular_variable_dims
    by (auto intro: dclosed0_lift)
  have "red S
      (psubst (single_sub n s) t)
      (psubst (single_sub n s) t')"
    by (rule red_psubst_dclosed[
          OF step regt env_reg env_closed])
  then show ?thesis by (simp add: subst_as_psubst)
qed

lemma dclosed0_elimArgs:
  assumes pms: "list_all (dclosed0 S) pms"
    and args: "list_all (dclosed0 S) as"
  shows "list_all (dclosed0 S) (elimArgs h C pms lms ss as)"
  using args
proof (induct ss arbitrary: as)
  case Nil
  show ?case by simp
next
  case (Cons s ss)
  then show ?case
    using pms by (cases as; cases s) auto
qed

lemma dclosed0_apps:
  assumes "dclosed0 S t" and "list_all (dclosed0 S) xs"
  shows "dclosed0 S (apps t xs)"
  using assms by (induct xs arbitrary: t) auto

lemma dsubst_variable_closed:
  assumes reg: "regular S t" and "j \<noteq> 0"
  shows "dclosed0 S (dsubst S 0 (DVar j) t)"
  using reg assms(2)
  by (induct t) (auto simp: list_all_iff)

lemma dclosed0_red:
  assumes step: "red S t u" and reg: "regular S t"
    and closed: "dclosed0 S t"
  shows "dclosed0 S u"
  using step reg closed
proof (induct rule: red.induct)
  case (beta u A t)
  have regt: "regular S t" and regu: "regular S u"
    using beta.prems(1) by simp_all
  have closet: "dclosed0 S t" and closeu: "dclosed0 S u"
    using beta.prems(2) by simp_all
  show ?case
    by (rule dclosed0_subst[
          OF regular_variable_dims[OF regt] closet
            regular_variable_dims[OF regu] closeu])
next
  case (elimPoint k h C pms lms as)
  have cpms: "list_all (dclosed0 S) pms"
    and cas: "list_all (dclosed0 S) as"
    using elimPoint.prems(2) by simp_all
  have kpm: "k < length pms" using elimPoint by simp
  have method: "dclosed0 S (pms ! k)"
    using cpms kpm by (simp add: list_all_iff)
  have eargs: "list_all (dclosed0 S)
      (elimArgs h C pms lms (pcons (S h) ! k) as)"
    by (rule dclosed0_elimArgs[OF cpms cas])
  show ?case by (rule dclosed0_apps[OF method eargs])
next
  case (elimPath k h C pms lms as j)
  have cpms: "list_all (dclosed0 S) pms"
    and cas: "list_all (dclosed0 S) as" and j0: "j \<noteq> 0"
    using elimPath.prems(2) by simp_all
  have k': "k < length lms" using elimPath by simp
  have mreg: "regular S (lms ! k)"
    using elimPath k' by (auto simp: list_all_iff)
  have method: "dclosed0 S (dsubst S 0 (DVar j) (lms ! k))"
    by (rule dsubst_variable_closed[OF mreg j0])
  have eargs: "list_all (dclosed0 S)
      (elimArgs h C pms lms (lcons (S h) ! k) as)"
    by (rule dclosed0_elimArgs[OF cpms cas])
  show ?case by (rule dclosed0_apps[OF method eargs])
next
  case (appL t t' u)
  then show ?case by simp
next
  case (appR u u' t)
  then show ?case by simp
next
  case (lam t t' A)
  then show ?case by simp
next
  case (pconArg a a' h k xs ys)
  then show ?case by (auto simp: list_all_iff)
next
  case (lconArg a a' h k xs ys d)
  then show ?case by (auto simp: list_all_iff)
next
  case (elimPm m m' h C xs ys lms t)
  then show ?case by (auto simp: list_all_iff)
next
  case (elimLm m m' h C pms xs ys t)
  then show ?case by simp
next
  case (elimScrutinee t t' h C pms lms)
  then show ?case by simp
qed

lemma dsubst_same_regular:
  assumes "regular S t"
  shows "dsubst S 0 (DVar 0) t = t"
  using assms
  by (induct t) (auto simp: list_all_iff map_idI)

lemma dsubst_variable_comp:
  assumes "regular S t"
  shows "dsubst S 0 (DVar j) (dsubst S 0 (DVar q) t) =
    dsubst S 0 (DVar (if q = 0 then j else q)) t"
proof (cases "q = 0")
  case True
  then show ?thesis using dsubst_same_regular[OF assms] by simp
next
  case False
  have closed: "dclosed0 S (dsubst S 0 (DVar q) t)"
    by (rule dsubst_variable_closed[OF assms False])
  then have "dsubst S 0 (DVar j) (dsubst S 0 (DVar q) t) =
      dsubst S 0 (DVar q) t"
    unfolding dclosed0_def by simp
  with False show ?thesis by simp
qed

lemma dsubst_apps [simp]:
  "dsubst S 0 (DVar j) (apps t xs) =
    apps (dsubst S 0 (DVar j) t)
      (map (dsubst S 0 (DVar j)) xs)"
  by (induct xs arbitrary: t) simp_all

lemma dsubst_elimArgs:
  "map (dsubst S 0 (DVar j))
      (elimArgs h C pms lms ss as) =
    elimArgs h C (map (dsubst S 0 (DVar j)) pms) lms ss
      (map (dsubst S 0 (DVar j)) as)"
  by (induct ss arbitrary: as)
    (auto split: list.split argspec.split)

lemma red_dsubst_variable:
  assumes step: "red S t u" and reg: "regular S t"
  shows "red S
    (dsubst S 0 (DVar j) t) (dsubst S 0 (DVar j) u)"
  using step reg
proof (induct rule: red.induct)
  case (beta u A t)
  have regt: "regular S t" and regu: "regular S u"
    using beta.prems by simp_all
  have dt: "variable_dims t" by (rule regular_variable_dims[OF regt])
  have du: "variable_dims u" by (rule regular_variable_dims[OF regu])
  have closed: "dclosed0 S u" by (rule beta.hyps(1))
  have fixed: "dsubst S 0 (DVar j) u = u"
    using closed unfolding dclosed0_def by simp
  have commute:
      "dsubst S 0 (DVar j) (subst 0 u t) =
        subst 0 u (dsubst S 0 (DVar j) t)"
  proof -
    have env_closed: "\<And>i. dclosed0 S (single_sub 0 u i)"
      unfolding single_sub_def
      using closed by (auto intro: dclosed0_lift)
    have env_dims: "\<And>i. variable_dims (single_sub 0 u i)"
      unfolding single_sub_def
      using du by (auto intro: variable_dims_lift)
    have "psubst (single_sub 0 u) (dsubst S 0 (DVar j) t) =
        dsubst S 0 (DVar j) (psubst (single_sub 0 u) t)"
      by (rule psubst_dsubst_zero_dclosed[
            OF dt env_closed env_dims])
    then show ?thesis by (simp add: subst_as_psubst)
  qed
  have "red S
      (App (Lam A (dsubst S 0 (DVar j) t)) u)
      (subst 0 u (dsubst S 0 (DVar j) t))"
    by (rule red.beta[OF closed])
  with fixed commute show ?case by simp
next
  case (elimPoint k h C pms lms as)
  have raw: "red S
      (HElim h C (map (dsubst S 0 (DVar j)) pms) lms
        (PCon h k (map (dsubst S 0 (DVar j)) as)))
      (apps ((map (dsubst S 0 (DVar j)) pms) ! k)
        (elimArgs h C (map (dsubst S 0 (DVar j)) pms) lms
          (pcons (S h) ! k)
          (map (dsubst S 0 (DVar j)) as)))"
    by (rule red.elimPoint[
          where S = S and h = h and k = k and C = C
            and pms = "map (dsubst S 0 (DVar j)) pms"
            and lms = lms
            and as = "map (dsubst S 0 (DVar j)) as",
          OF elimPoint.hyps(1)])
  from raw show ?case
    using elimPoint.hyps(1) elimPoint.prems
    by (simp add: dsubst_elimArgs)
next
  case (elimPath k h C pms lms as q)
  have mreg: "regular S (lms ! k)"
    using elimPath by (auto simp: list_all_iff)
  let ?q = "if q = 0 then j else q"
  have raw: "red S
      (HElim h C (map (dsubst S 0 (DVar j)) pms) lms
        (LCon h k (map (dsubst S 0 (DVar j)) as) (DVar ?q)))
      (apps (dsubst S 0 (DVar ?q) (lms ! k))
        (elimArgs h C (map (dsubst S 0 (DVar j)) pms) lms
          (lcons (S h) ! k)
          (map (dsubst S 0 (DVar j)) as)))"
    by (rule red.elimPath[
          where S = S and h = h and k = k and C = C
            and pms = "map (dsubst S 0 (DVar j)) pms"
            and lms = lms
            and as = "map (dsubst S 0 (DVar j)) as"
            and j = ?q,
          OF elimPath.hyps(1)])
  have method:
      "dsubst S 0 (DVar j)
          (dsubst S 0 (DVar q) (lms ! k)) =
        dsubst S 0 (DVar ?q) (lms ! k)"
    by (rule dsubst_variable_comp[OF mreg])
  show ?case
  proof (cases "q = 0")
    case True
    from raw method True show ?thesis
      by (simp add: dsubst_elimArgs)
  next
    case False
    from raw method False show ?thesis
      by (simp add: dsubst_elimArgs)
  qed
next
  case (appL t t' u)
  then show ?case by (auto intro: red.appL)
next
  case (appR u u' t)
  then show ?case by (auto intro: red.appR)
next
  case (lam t t' A)
  then show ?case by (auto intro: red.lam)
next
  case (pconArg a a' h k xs ys)
  have "red S
      (PCon h k
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) a #
          map (dsubst S 0 (DVar j)) ys))
      (PCon h k
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) a' #
          map (dsubst S 0 (DVar j)) ys))"
    by (rule red.pconArg) (use pconArg in auto)
  then show ?case by simp
next
  case (lconArg a a' h k xs ys d)
  then obtain q where d: "d = DVar q" by auto
  have "red S
      (LCon h k
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) a #
          map (dsubst S 0 (DVar j)) ys)
        (DVar (if q = 0 then j else q)))
      (LCon h k
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) a' #
          map (dsubst S 0 (DVar j)) ys)
        (DVar (if q = 0 then j else q)))"
    by (rule red.lconArg) (use lconArg d in auto)
  show ?case
  proof (cases "q = 0")
    case True
    with d \<open>red S
      (LCon h k
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) a #
          map (dsubst S 0 (DVar j)) ys)
        (DVar (if q = 0 then j else q)))
      (LCon h k
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) a' #
          map (dsubst S 0 (DVar j)) ys)
        (DVar (if q = 0 then j else q)))\<close>
    show ?thesis by simp
  next
    case False
    with d \<open>red S
      (LCon h k
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) a #
          map (dsubst S 0 (DVar j)) ys)
        (DVar (if q = 0 then j else q)))
      (LCon h k
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) a' #
          map (dsubst S 0 (DVar j)) ys)
        (DVar (if q = 0 then j else q)))\<close>
    show ?thesis by simp
  qed
next
  case (elimPm m m' h C xs ys lms t)
  have "red S
      (HElim h C
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) m #
          map (dsubst S 0 (DVar j)) ys)
        lms (dsubst S 0 (DVar j) t))
      (HElim h C
        (map (dsubst S 0 (DVar j)) xs @
          dsubst S 0 (DVar j) m' #
          map (dsubst S 0 (DVar j)) ys)
        lms (dsubst S 0 (DVar j) t))"
    by (rule red.elimPm) (use elimPm in auto)
  then show ?case by simp
next
  case (elimLm m m' h C pms xs ys t)
  have "red S
      (HElim h C (map (dsubst S 0 (DVar j)) pms)
        (xs @ m # ys) (dsubst S 0 (DVar j) t))
      (HElim h C (map (dsubst S 0 (DVar j)) pms)
        (xs @ m' # ys) (dsubst S 0 (DVar j) t))"
    by (rule red.elimLm[OF elimLm.hyps(1)])
  then show ?case by simp
next
  case (elimScrutinee t t' h C pms lms)
  then show ?case by (auto intro: red.elimScrutinee)
qed

lemma reds_dsubst_variable:
  assumes "reds S t u" and "regular S t"
  shows "reds S
    (dsubst S 0 (DVar j) t) (dsubst S 0 (DVar j) u)"
proof -
  have invariant: "regular S u \<and> reds S
      (dsubst S 0 (DVar j) t) (dsubst S 0 (DVar j) u)"
    using assms(1)
  proof (induct rule: rtranclp_induct)
    case base
    show ?case using assms(2) by simp
  next
    case (step y z)
    have regy: "regular S y" using step.hyps(3) by blast
    have regz: "regular S z"
      by (rule regular_red[OF step.hyps(2) regy])
    have mapped: "red S
        (dsubst S 0 (DVar j) y) (dsubst S 0 (DVar j) z)"
      by (rule red_dsubst_variable[OF step.hyps(2) regy])
    have path: "reds S
        (dsubst S 0 (DVar j) t) (dsubst S 0 (DVar j) y)"
      using step.hyps(3) by blast
    have "reds S
        (dsubst S 0 (DVar j) t) (dsubst S 0 (DVar j) z)"
      by (rule rtranclp.rtrancl_into_rtrancl[OF path mapped])
    with regz show ?case by blast
  qed
  then show ?thesis by blast
qed

subsection \<open>Local peaks\<close>

lemma red_as_reds:
  "red S t u \<Longrightarrow> reds S t u"
  by (rule r_into_rtranclp[where r = "red S"])

lemma list_red_imp_list_reds:
  assumes "list_red S xs ys"
  shows "list_reds S xs ys"
  using assms
proof induct
  case (lr_head a b xs)
  have "reds S a b"
    by (rule r_into_rtranclp[where r = "red S", OF lr_head.hyps])
  then show ?case by auto
next
  case (lr_tail xs ys a)
  then show ?case by auto
qed

lemma list_red_ConsE:
  assumes "list_red S (a # xs) ys"
  obtains
    (head) b where "red S a b" "ys = b # xs"
  | (tail) zs where "list_red S xs zs" "ys = a # zs"
  using assms by (cases rule: list_red.cases) auto

lemma list_red_local_confluence:
  assumes local: "\<And>a b c. a \<in> set xs \<Longrightarrow>
      red S a b \<Longrightarrow> red S a c \<Longrightarrow> joinable S b c"
    and left: "list_red S xs ys"
    and right: "list_red S xs zs"
  shows "\<exists>ws. list_reds S ys ws \<and> list_reds S zs ws"
  using left right local
proof (induct arbitrary: zs)
  case (lr_head a b xs)
  note ab_step = lr_head.hyps
  note local_all = lr_head.prems(2)
  show ?case
  proof (rule list_red_ConsE[OF lr_head.prems(1)])
    fix c
    assume ac: "red S a c" and zs: "zs = c # xs"
    have mem: "a \<in> set (a # xs)" by simp
    have "joinable S b c"
      by (rule local_all[OF mem ab_step ac])
    then obtain d where bd: "reds S b d" and cd: "reds S c d"
      unfolding joinable_def by blast
    have "list_reds S (b # xs) (d # xs)" using bd by auto
    moreover have "list_reds S (c # xs) (d # xs)" using cd by auto
    ultimately show ?thesis using zs by blast
  next
    fix xs'
    assume tail_step: "list_red S xs xs'" and zs: "zs = a # xs'"
    have tail: "list_reds S xs xs'"
      by (rule list_red_imp_list_reds[OF tail_step])
    have first: "list_reds S (b # xs) (b # xs')" using tail by auto
    have ab: "reds S a b"
      by (rule r_into_rtranclp[where r = "red S", OF ab_step])
    have second: "list_reds S (a # xs') (b # xs')" using ab by auto
    from first second zs show ?thesis by blast
  qed
next
  case (lr_tail xs ys a)
  note tail_step = lr_tail.hyps(1)
  note tail_IH = lr_tail.hyps(2)
  note local_all = lr_tail.prems(2)
  show ?case
  proof (rule list_red_ConsE[OF lr_tail.prems(1)])
    fix b
    assume ab_step: "red S a b" and zs: "zs = b # xs"
    have tail: "list_reds S xs ys"
      by (rule list_red_imp_list_reds[OF tail_step])
    have first: "list_reds S (a # ys) (b # ys)"
    proof -
      have "reds S a b"
        by (rule r_into_rtranclp[where r = "red S", OF ab_step])
      then show ?thesis by auto
    qed
    have second: "list_reds S (b # xs) (b # ys)" using tail by auto
    from first second zs show ?thesis by blast
  next
    fix zs'
    assume right_tail: "list_red S xs zs'"
      and zs: "zs = a # zs'"
    have local_tail: "\<And>x b c. x \<in> set xs \<Longrightarrow>
        red S x b \<Longrightarrow> red S x c \<Longrightarrow> joinable S b c"
      using local_all by auto
    have "\<exists>ws. list_reds S ys ws \<and> list_reds S zs' ws"
      by (rule tail_IH[OF right_tail local_tail])
    then obtain ws where yw: "list_reds S ys ws"
      and zw: "list_reds S zs' ws"
      by blast
    have "list_reds S (a # ys) (a # ws)" using yw by auto
    moreover have "list_reds S (a # zs') (a # ws)" using zw by auto
    ultimately show ?thesis using zs by blast
  qed
qed

lemma point_contractum_reds:
  assumes k: "k < length pms"
    and pms: "list_reds S pms pms'"
    and lms: "list_reds S lms lms'"
    and args: "list_reds S as as'"
  shows "reds S
    (apps (pms ! k)
      (elimArgs h C pms lms ss as))
    (apps (pms' ! k)
      (elimArgs h C pms' lms' ss as'))"
proof -
  have method: "reds S (pms ! k) (pms' ! k)"
    by (rule list_reds_nth[OF pms k])
  have eargs: "list_reds S
      (elimArgs h C pms lms ss as)
      (elimArgs h C pms' lms' ss as')"
    by (rule elimArgs_list_reds[OF pms lms args])
  show ?thesis by (rule reds_apps[OF method eargs])
qed

lemma path_contractum_reds:
  assumes k: "k < length lms"
    and reg: "list_all (regular S) lms"
    and pms: "list_reds S pms pms'"
    and lms: "list_reds S lms lms'"
    and args: "list_reds S as as'"
  shows "reds S
    (apps (dsubst S 0 (DVar j) (lms ! k))
      (elimArgs h C pms lms ss as))
    (apps (dsubst S 0 (DVar j) (lms' ! k))
      (elimArgs h C pms' lms' ss as'))"
proof -
  have method0: "reds S (lms ! k) (lms' ! k)"
    by (rule list_reds_nth[OF lms k])
  have mreg: "regular S (lms ! k)"
    using reg k by (simp add: list_all_iff)
  have method: "reds S
      (dsubst S 0 (DVar j) (lms ! k))
      (dsubst S 0 (DVar j) (lms' ! k))"
    by (rule reds_dsubst_variable[OF method0 mreg])
  have eargs: "list_reds S
      (elimArgs h C pms lms ss as)
      (elimArgs h C pms' lms' ss as')"
    by (rule elimArgs_list_reds[OF pms lms args])
  show ?thesis by (rule reds_apps[OF method eargs])
qed

lemma red_AppE [case_names beta left right]:
  assumes "red S (App t u) v"
  obtains
    (beta) A body where "t = Lam A body" "dclosed0 S u"
      "v = subst 0 u body"
  | (left) t' where "red S t t'" "v = App t' u"
  | (right) u' where "red S u u'" "v = App t u'"
  using assms by (cases rule: red.cases) auto

lemma beta_body_peak:
  assumes body: "red S t t'" and regt: "regular S t"
    and regu: "regular S u" and closed: "dclosed0 S u"
  shows "joinable S
    (subst 0 u t) (App (Lam A t') u)"
proof -
  have left: "reds S (subst 0 u t) (subst 0 u t')"
    by (rule red_as_reds[
          OF red_subst_dclosed[OF body regt regu closed]])
  have right_step: "red S (App (Lam A t') u) (subst 0 u t')"
    by (rule red.beta[OF closed])
  have right: "reds S (App (Lam A t') u) (subst 0 u t')"
    by (rule red_as_reds[OF right_step])
  show ?thesis by (rule joinableI[OF left right])
qed

lemma beta_argument_peak:
  assumes arg: "red S u u'" and regu: "regular S u"
    and closed: "dclosed0 S u"
  shows "joinable S
    (subst 0 u t) (App (Lam A t) u')"
proof -
  have left: "reds S (subst 0 u t) (subst 0 u' t)"
    by (rule reds_subst_argument[OF arg regu])
  have regu': "regular S u'" by (rule regular_red[OF arg regu])
  have closed': "dclosed0 S u'"
    by (rule dclosed0_red[OF arg regu closed])
  have right_step: "red S (App (Lam A t) u') (subst 0 u' t)"
    by (rule red.beta[OF closed'])
  have right: "reds S (App (Lam A t) u') (subst 0 u' t)"
    by (rule red_as_reds[OF right_step])
  show ?thesis by (rule joinableI[OF left right])
qed

lemma point_root_peak:
  assumes reg: "regular S (HElim h C pms lms (PCon h k as))"
    and k: "k < length (pcons (S h))"
    and other: "red S (HElim h C pms lms (PCon h k as)) v"
  shows "joinable S
    (apps (pms ! k)
      (elimArgs h C pms lms (pcons (S h) ! k) as)) v"
  using other
proof (rule red_HElim_PConE)
  assume "k < length (pcons (S h))"
    and v: "v = apps (pms ! k)
      (elimArgs h C pms lms (pcons (S h) ! k) as)"
  then show ?thesis by simp
next
  fix xs m m' ys
  assume pms: "pms = xs @ m # ys" and mm': "red S m m'"
    and v: "v = HElim h C (xs @ m' # ys) lms (PCon h k as)"
  let ?pms' = "xs @ m' # ys"
  have lr: "list_reds S pms ?pms'"
    using pms list_red_imp_list_reds[
      OF list_red_append[OF mm', of xs ys]]
    by simp
  have kp: "k < length pms" using reg k by simp
  have left: "reds S
      (apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k) as))
      (apps (?pms' ! k)
        (elimArgs h C ?pms' lms (pcons (S h) ! k) as))"
    by (rule point_contractum_reds[OF kp lr])
      simp_all
  have right_step: "red S
      (HElim h C ?pms' lms (PCon h k as))
      (apps (?pms' ! k)
        (elimArgs h C ?pms' lms (pcons (S h) ! k) as))"
    by (rule red.elimPoint[
          where S = S and h = h and k = k and C = C
            and pms = ?pms' and lms = lms and as = as,
          OF k])
  have right: "reds S v
      (apps (?pms' ! k)
        (elimArgs h C ?pms' lms (pcons (S h) ! k) as))"
    using v red_as_reds[OF right_step] by simp
  show ?thesis by (rule joinableI[OF left right])
next
  fix xs m m' ys
  assume lms: "lms = xs @ m # ys" and mm': "red S m m'"
    and v: "v = HElim h C pms (xs @ m' # ys) (PCon h k as)"
  let ?lms' = "xs @ m' # ys"
  have lr: "list_reds S lms ?lms'"
    using lms list_red_imp_list_reds[
      OF list_red_append[OF mm', of xs ys]]
    by simp
  have kp: "k < length pms" using reg k by simp
  have left: "reds S
      (apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k) as))
      (apps (pms ! k)
        (elimArgs h C pms ?lms' (pcons (S h) ! k) as))"
    by (rule point_contractum_reds[OF kp])
      (use lr in simp_all)
  have right_step: "red S
      (HElim h C pms ?lms' (PCon h k as))
      (apps (pms ! k)
        (elimArgs h C pms ?lms' (pcons (S h) ! k) as))"
    by (rule red.elimPoint[
          where S = S and h = h and k = k and C = C
            and pms = pms and lms = ?lms' and as = as,
          OF k])
  have right: "reds S v
      (apps (pms ! k)
        (elimArgs h C pms ?lms' (pcons (S h) ! k) as))"
    using v red_as_reds[OF right_step] by simp
  show ?thesis by (rule joinableI[OF left right])
next
  fix t'
  assume step: "red S (PCon h k as) t'"
    and v: "v = HElim h C pms lms t'"
  obtain as' where t': "t' = PCon h k as'"
    and lr0: "list_red S as as'"
    by (rule red_PCon_list[OF step])
  have lr: "list_reds S as as'"
    by (rule list_red_imp_list_reds[OF lr0])
  have kp: "k < length pms" using reg k by simp
  have left: "reds S
      (apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k) as))
      (apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k) as'))"
    by (rule point_contractum_reds[OF kp])
      (use lr in simp_all)
  have right_step: "red S
      (HElim h C pms lms (PCon h k as'))
      (apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k) as'))"
    by (rule red.elimPoint[
          where S = S and h = h and k = k and C = C
            and pms = pms and lms = lms and as = as',
          OF k])
  have right: "reds S v
      (apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k) as'))"
    using v t' red_as_reds[OF right_step] by simp
  show ?thesis by (rule joinableI[OF left right])
qed

lemma path_root_peak:
  assumes reg: "regular S
      (HElim h C pms lms (LCon h k as (DVar j)))"
    and k: "k < length (lcons (S h))"
    and other: "red S
      (HElim h C pms lms (LCon h k as (DVar j))) v"
  shows "joinable S
    (apps (dsubst S 0 (DVar j) (lms ! k))
      (elimArgs h C pms lms (lcons (S h) ! k) as)) v"
  using other
proof (rule red_HElim_LConE)
  assume "k < length (lcons (S h))"
    and v: "v = apps (dsubst S 0 (DVar j) (lms ! k))
      (elimArgs h C pms lms (lcons (S h) ! k) as)"
  then show ?thesis by simp
next
  fix xs m m' ys
  assume pms: "pms = xs @ m # ys" and mm': "red S m m'"
    and v: "v = HElim h C (xs @ m' # ys) lms
      (LCon h k as (DVar j))"
  let ?pms' = "xs @ m' # ys"
  have lr: "list_reds S pms ?pms'"
    using pms list_red_imp_list_reds[
      OF list_red_append[OF mm', of xs ys]]
    by simp
  have kl: "k < length lms" using reg k by simp
  have left: "reds S
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C ?pms' lms (lcons (S h) ! k) as))"
    by (rule path_contractum_reds[OF kl])
      (use reg lr in simp_all)
  have right_step: "red S
      (HElim h C ?pms' lms (LCon h k as (DVar j)))
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C ?pms' lms (lcons (S h) ! k) as))"
    by (rule red.elimPath[
          where S = S and h = h and k = k and C = C
            and pms = ?pms' and lms = lms and as = as and j = j,
          OF k])
  have right: "reds S v
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C ?pms' lms (lcons (S h) ! k) as))"
    using v red_as_reds[OF right_step] by simp
  show ?thesis by (rule joinableI[OF left right])
next
  fix xs m m' ys
  assume lms: "lms = xs @ m # ys" and mm': "red S m m'"
    and v: "v = HElim h C pms (xs @ m' # ys)
      (LCon h k as (DVar j))"
  let ?lms' = "xs @ m' # ys"
  have lr: "list_reds S lms ?lms'"
    using lms list_red_imp_list_reds[
      OF list_red_append[OF mm', of xs ys]]
    by simp
  have kl: "k < length lms" using reg k by simp
  have left: "reds S
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))
      (apps (dsubst S 0 (DVar j) (?lms' ! k))
        (elimArgs h C pms ?lms' (lcons (S h) ! k) as))"
    by (rule path_contractum_reds[OF kl])
      (use reg lr in simp_all)
  have right_step: "red S
      (HElim h C pms ?lms' (LCon h k as (DVar j)))
      (apps (dsubst S 0 (DVar j) (?lms' ! k))
        (elimArgs h C pms ?lms' (lcons (S h) ! k) as))"
    by (rule red.elimPath[
          where S = S and h = h and k = k and C = C
            and pms = pms and lms = ?lms' and as = as and j = j,
          OF k])
  have right: "reds S v
      (apps (dsubst S 0 (DVar j) (?lms' ! k))
        (elimArgs h C pms ?lms' (lcons (S h) ! k) as))"
    using v red_as_reds[OF right_step] by simp
  show ?thesis by (rule joinableI[OF left right])
next
  fix t'
  assume step: "red S (LCon h k as (DVar j)) t'"
    and v: "v = HElim h C pms lms t'"
  obtain as' where t': "t' = LCon h k as' (DVar j)"
    and lr0: "list_red S as as'"
    by (rule red_LCon_list[OF step])
  have lr: "list_reds S as as'"
    by (rule list_red_imp_list_reds[OF lr0])
  have kl: "k < length lms" using reg k by simp
  have left: "reds S
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as'))"
    by (rule path_contractum_reds[OF kl])
      (use reg lr in simp_all)
  have right_step: "red S
      (HElim h C pms lms (LCon h k as' (DVar j)))
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as'))"
    by (rule red.elimPath[
          where S = S and h = h and k = k and C = C
            and pms = pms and lms = lms and as = as' and j = j,
          OF k])
  have right: "reds S v
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as'))"
    using v t' red_as_reds[OF right_step] by simp
  show ?thesis by (rule joinableI[OF left right])
qed

lemma red_HElimE [case_names point path pm lm scrut]:
  assumes "red S (HElim h C pms lms t) u"
  obtains
    (point) k as where "t = PCon h k as"
      "k < length (pcons (S h))"
      "u = apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k) as)"
  | (path) k as j where "t = LCon h k as (DVar j)"
      "k < length (lcons (S h))"
      "u = apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as)"
  | (pm) xs m m' ys where "pms = xs @ m # ys" "red S m m'"
      "u = HElim h C (xs @ m' # ys) lms t"
  | (lm) xs m m' ys where "lms = xs @ m # ys" "red S m m'"
      "u = HElim h C pms (xs @ m' # ys) t"
  | (scrut) t' where "red S t t'"
      "u = HElim h C pms lms t'"
  using assms by (cases rule: red.cases) auto

lemma joinable_App_left:
  assumes "joinable S t u"
  shows "joinable S (App t a) (App u a)"
proof -
  from assms obtain v where tv: "reds S t v" and uv: "reds S u v"
    unfolding joinable_def by blast
  have "reds S (App t a) (App v a)" by (rule reds_App[OF tv]) simp
  moreover have "reds S (App u a) (App v a)" by (rule reds_App[OF uv]) simp
  ultimately show ?thesis by (rule joinableI)
qed

lemma joinable_App_right:
  assumes "joinable S t u"
  shows "joinable S (App a t) (App a u)"
proof -
  from assms obtain v where tv: "reds S t v" and uv: "reds S u v"
    unfolding joinable_def by blast
  have "reds S (App a t) (App a v)" by (rule reds_App) (use tv in simp_all)
  moreover have "reds S (App a u) (App a v)"
    by (rule reds_App) (use uv in simp_all)
  ultimately show ?thesis by (rule joinableI)
qed

lemma joinable_Lam:
  assumes "joinable S t u"
  shows "joinable S (Lam A t) (Lam A u)"
proof -
  from assms obtain v where tv: "reds S t v" and uv: "reds S u v"
    unfolding joinable_def by blast
  have "reds S (Lam A t) (Lam A v)" by (rule reds_Lam[OF tv])
  moreover have "reds S (Lam A u) (Lam A v)" by (rule reds_Lam[OF uv])
  ultimately show ?thesis by (rule joinableI)
qed

lemma red_App_local_confluence:
  assumes regt: "regular S t" and regu: "regular S u"
    and local_t: "\<And>t1 t2. red S t t1 \<Longrightarrow> red S t t2 \<Longrightarrow>
      joinable S t1 t2"
    and local_u: "\<And>u1 u2. red S u u1 \<Longrightarrow> red S u u2 \<Longrightarrow>
      joinable S u1 u2"
    and left: "red S (App t u) x"
    and right: "red S (App t u) y"
  shows "joinable S x y"
proof (rule red_AppE[OF left])
  fix A body
  assume t: "t = Lam A body" and close: "dclosed0 S u"
    and x: "x = subst 0 u body"
  have regbody: "regular S body" using regt t by simp
  show ?thesis
  proof (rule red_AppE[OF right])
    fix B body'
    assume t': "t = Lam B body'" and "dclosed0 S u"
      and y: "y = subst 0 u body'"
    from t t' x y show ?thesis by simp
  next
    fix f'
    assume tf': "red S t f'" and y: "y = App f' u"
    from tf' t obtain body' where f': "f' = Lam A body'"
      and step: "red S body body'"
      by (auto elim: red_LamE)
    have "joinable S (subst 0 u body) (App (Lam A body') u)"
      by (rule beta_body_peak[OF step regbody regu close])
    with x y f' show ?thesis by simp
  next
    fix u'
    assume uu': "red S u u'" and y: "y = App t u'"
    have "joinable S (subst 0 u body) (App (Lam A body) u')"
      by (rule beta_argument_peak[OF uu' regu close])
    with t x y show ?thesis by simp
  qed
next
  fix f'
  assume tf': "red S t f'" and x: "x = App f' u"
  show ?thesis
  proof (rule red_AppE[OF right])
    fix A body
    assume t: "t = Lam A body" and close: "dclosed0 S u"
      and y: "y = subst 0 u body"
    from tf' t obtain body' where f': "f' = Lam A body'"
      and step: "red S body body'"
      by (auto elim: red_LamE)
    have regbody: "regular S body" using regt t by simp
    have "joinable S (subst 0 u body) (App (Lam A body') u)"
      by (rule beta_body_peak[OF step regbody regu close])
    with x y f' show ?thesis by (simp add: joinable_sym)
  next
    fix f''
    assume tf'': "red S t f''" and y: "y = App f'' u"
    have "joinable S f' f''" by (rule local_t[OF tf' tf''])
    then have "joinable S (App f' u) (App f'' u)"
      by (rule joinable_App_left)
    with x y show ?thesis by simp
  next
    fix u'
    assume uu': "red S u u'" and y: "y = App t u'"
    have first: "reds S (App f' u) (App f' u')"
      by (rule red_as_reds[OF red.appR[OF uu']])
    have second: "reds S (App t u') (App f' u')"
      by (rule red_as_reds[OF red.appL[OF tf']])
    have "joinable S (App f' u) (App t u')"
      by (rule joinableI[OF first second])
    with x y show ?thesis by simp
  qed
next
  fix u'
  assume uu': "red S u u'" and x: "x = App t u'"
  show ?thesis
  proof (rule red_AppE[OF right])
    fix A body
    assume t: "t = Lam A body" and close: "dclosed0 S u"
      and y: "y = subst 0 u body"
    have "joinable S (subst 0 u body) (App (Lam A body) u')"
      by (rule beta_argument_peak[OF uu' regu close])
    with t x y show ?thesis by (simp add: joinable_sym)
  next
    fix f'
    assume tf': "red S t f'" and y: "y = App f' u"
    have first: "reds S (App t u') (App f' u')"
      by (rule red_as_reds[OF red.appL[OF tf']])
    have second: "reds S (App f' u) (App f' u')"
      by (rule red_as_reds[OF red.appR[OF uu']])
    have "joinable S (App t u') (App f' u)"
      by (rule joinableI[OF first second])
    with x y show ?thesis by simp
  next
    fix u''
    assume uu'': "red S u u''" and y: "y = App t u''"
    have "joinable S u' u''" by (rule local_u[OF uu' uu''])
    then have "joinable S (App t u') (App t u'')"
      by (rule joinable_App_right)
    with x y show ?thesis by simp
  qed
qed

lemma red_HElim_local_confluence:
    assumes reg: "regular S (HElim h C pms lms t)"
      and local_pms: "\<And>m u v. m \<in> set pms \<Longrightarrow>
        red S m u \<Longrightarrow> red S m v \<Longrightarrow> joinable S u v"
      and local_lms: "\<And>m u v. m \<in> set lms \<Longrightarrow>
        red S m u \<Longrightarrow> red S m v \<Longrightarrow> joinable S u v"
      and local_t: "\<And>u v. red S t u \<Longrightarrow> red S t v \<Longrightarrow>
        joinable S u v"
      and left: "red S (HElim h C pms lms t) x"
      and right: "red S (HElim h C pms lms t) y"
    shows "joinable S x y"
  proof (rule red_HElimE[OF left])
    fix k as
    assume t: "t = PCon h k as" and k: "k < length (pcons (S h))"
      and x: "x = apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k) as)"
    have regroot: "regular S (HElim h C pms lms (PCon h k as))"
      using reg t by simp
    have other: "red S (HElim h C pms lms (PCon h k as)) y"
      using right t by simp
    have "joinable S
        (apps (pms ! k)
          (elimArgs h C pms lms (pcons (S h) ! k) as)) y"
      by (rule point_root_peak[OF regroot k other])
    with x show ?thesis by simp
  next
    fix k as j
    assume t: "t = LCon h k as (DVar j)"
      and k: "k < length (lcons (S h))"
      and x: "x = apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as)"
    have regroot: "regular S
        (HElim h C pms lms (LCon h k as (DVar j)))"
      using reg t by simp
    have other: "red S
        (HElim h C pms lms (LCon h k as (DVar j))) y"
      using right t by simp
    have "joinable S
        (apps (dsubst S 0 (DVar j) (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as)) y"
      by (rule path_root_peak[OF regroot k other])
    with x show ?thesis by simp
  next
    fix xs m m' ys
    assume pms: "pms = xs @ m # ys" and mm': "red S m m'"
      and x: "x = HElim h C (xs @ m' # ys) lms t"
    let ?pms1 = "xs @ m' # ys"
    have lp1: "list_red S pms ?pms1"
      using pms list_red_append[OF mm', of xs ys] by simp
    have rp1: "list_reds S pms ?pms1"
      by (rule list_red_imp_list_reds[OF lp1])
    show ?thesis
    proof (rule red_HElimE[OF right])
      fix k as
      assume t': "t = PCon h k as"
        and k: "k < length (pcons (S h))"
        and y: "y = apps (pms ! k)
          (elimArgs h C pms lms (pcons (S h) ! k) as)"
      have regroot: "regular S (HElim h C pms lms (PCon h k as))"
        using reg t' by simp
      have other: "red S (HElim h C pms lms (PCon h k as)) x"
        using left t' by simp
      have peak: "joinable S
          (apps (pms ! k)
            (elimArgs h C pms lms (pcons (S h) ! k) as)) x"
        by (rule point_root_peak[OF regroot k other])
      from joinable_sym[OF peak] x y show ?thesis by simp
    next
      fix k as j
      assume t': "t = LCon h k as (DVar j)"
        and k: "k < length (lcons (S h))"
        and y: "y = apps (dsubst S 0 (DVar j) (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as)"
      have regroot: "regular S
          (HElim h C pms lms (LCon h k as (DVar j)))"
        using reg t' by simp
      have other: "red S
          (HElim h C pms lms (LCon h k as (DVar j))) x"
        using left t' by simp
      have peak: "joinable S
          (apps (dsubst S 0 (DVar j) (lms ! k))
            (elimArgs h C pms lms (lcons (S h) ! k) as)) x"
        by (rule path_root_peak[OF regroot k other])
      from joinable_sym[OF peak] x y show ?thesis by simp
    next
      fix us n n' vs
      assume pms2: "pms = us @ n # vs" and nn': "red S n n'"
        and y: "y = HElim h C (us @ n' # vs) lms t"
      let ?pms2 = "us @ n' # vs"
      have lp2: "list_red S pms ?pms2"
        using pms2 list_red_append[OF nn', of us vs] by simp
      have "\<exists>ws. list_reds S ?pms1 ws \<and> list_reds S ?pms2 ws"
        by (rule list_red_local_confluence[
              OF local_pms lp1 lp2])
      then obtain ws where one: "list_reds S ?pms1 ws"
        and two: "list_reds S ?pms2 ws"
        by blast
      have left_path: "reds S
          (HElim h C ?pms1 lms t) (HElim h C ws lms t)"
        by (rule reds_HElim[OF one]) simp_all
      have right_path: "reds S
          (HElim h C ?pms2 lms t) (HElim h C ws lms t)"
        by (rule reds_HElim[OF two]) simp_all
      have "joinable S
          (HElim h C ?pms1 lms t) (HElim h C ?pms2 lms t)"
        by (rule joinableI[OF left_path right_path])
      with x y show ?thesis by simp
    next
      fix us n n' vs
      assume lms2: "lms = us @ n # vs" and nn': "red S n n'"
        and y: "y = HElim h C pms (us @ n' # vs) t"
      let ?lms2 = "us @ n' # vs"
      have rl2: "list_reds S lms ?lms2"
        using lms2 list_red_imp_list_reds[
          OF list_red_append[OF nn', of us vs]]
        by simp
      have left_path: "reds S
          (HElim h C ?pms1 lms t) (HElim h C ?pms1 ?lms2 t)"
        by (rule reds_HElim) (use rl2 in simp_all)
      have right_path: "reds S
          (HElim h C pms ?lms2 t) (HElim h C ?pms1 ?lms2 t)"
        by (rule reds_HElim) (use rp1 in simp_all)
      have "joinable S
          (HElim h C ?pms1 lms t) (HElim h C pms ?lms2 t)"
        by (rule joinableI[OF left_path right_path])
      with x y show ?thesis by simp
    next
      fix t'
      assume tt': "red S t t'" and y: "y = HElim h C pms lms t'"
      have left_path: "reds S
          (HElim h C ?pms1 lms t) (HElim h C ?pms1 lms t')"
        by (rule reds_HElim_scrutinee[OF red_as_reds[OF tt']])
      have right_path: "reds S
          (HElim h C pms lms t') (HElim h C ?pms1 lms t')"
        by (rule reds_HElim) (use rp1 in simp_all)
      have "joinable S
          (HElim h C ?pms1 lms t) (HElim h C pms lms t')"
        by (rule joinableI[OF left_path right_path])
      with x y show ?thesis by simp
    qed

  next
    fix xs m m' ys
    assume lms: "lms = xs @ m # ys" and mm': "red S m m'"
      and x: "x = HElim h C pms (xs @ m' # ys) t"
    let ?lms1 = "xs @ m' # ys"
    have ll1: "list_red S lms ?lms1"
      using lms list_red_append[OF mm', of xs ys] by simp
    have rl1: "list_reds S lms ?lms1"
      by (rule list_red_imp_list_reds[OF ll1])
    show ?thesis
    proof (rule red_HElimE[OF right])
      fix k as
      assume t': "t = PCon h k as"
        and k: "k < length (pcons (S h))"
        and y: "y = apps (pms ! k)
          (elimArgs h C pms lms (pcons (S h) ! k) as)"
      have regroot: "regular S (HElim h C pms lms (PCon h k as))"
        using reg t' by simp
      have other: "red S (HElim h C pms lms (PCon h k as)) x"
        using left t' by simp
      have peak: "joinable S
          (apps (pms ! k)
            (elimArgs h C pms lms (pcons (S h) ! k) as)) x"
        by (rule point_root_peak[OF regroot k other])
      from joinable_sym[OF peak] x y show ?thesis by simp
    next
      fix k as j
      assume t': "t = LCon h k as (DVar j)"
        and k: "k < length (lcons (S h))"
        and y: "y = apps (dsubst S 0 (DVar j) (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as)"
      have regroot: "regular S
          (HElim h C pms lms (LCon h k as (DVar j)))"
        using reg t' by simp
      have other: "red S
          (HElim h C pms lms (LCon h k as (DVar j))) x"
        using left t' by simp
      have peak: "joinable S
          (apps (dsubst S 0 (DVar j) (lms ! k))
            (elimArgs h C pms lms (lcons (S h) ! k) as)) x"
        by (rule path_root_peak[OF regroot k other])
      from joinable_sym[OF peak] x y show ?thesis by simp
    next
      fix us n n' vs
      assume pms2: "pms = us @ n # vs" and nn': "red S n n'"
        and y: "y = HElim h C (us @ n' # vs) lms t"
      let ?pms2 = "us @ n' # vs"
      have rp2: "list_reds S pms ?pms2"
        using pms2 list_red_imp_list_reds[
          OF list_red_append[OF nn', of us vs]]
        by simp
      have left_path: "reds S
          (HElim h C pms ?lms1 t) (HElim h C ?pms2 ?lms1 t)"
        by (rule reds_HElim) (use rp2 in simp_all)
      have right_path: "reds S
          (HElim h C ?pms2 lms t) (HElim h C ?pms2 ?lms1 t)"
        by (rule reds_HElim) (use rl1 in simp_all)
      have "joinable S
          (HElim h C pms ?lms1 t) (HElim h C ?pms2 lms t)"
        by (rule joinableI[OF left_path right_path])
      with x y show ?thesis by simp
    next
      fix us n n' vs
      assume lms2: "lms = us @ n # vs" and nn': "red S n n'"
        and y: "y = HElim h C pms (us @ n' # vs) t"
      let ?lms2 = "us @ n' # vs"
      have ll2: "list_red S lms ?lms2"
        using lms2 list_red_append[OF nn', of us vs] by simp
      have "\<exists>ws. list_reds S ?lms1 ws \<and> list_reds S ?lms2 ws"
        by (rule list_red_local_confluence[
              OF local_lms ll1 ll2])
      then obtain ws where one: "list_reds S ?lms1 ws"
        and two: "list_reds S ?lms2 ws"
        by blast
      have left_path: "reds S
          (HElim h C pms ?lms1 t) (HElim h C pms ws t)"
        by (rule reds_HElim) (use one in simp_all)
      have right_path: "reds S
          (HElim h C pms ?lms2 t) (HElim h C pms ws t)"
        by (rule reds_HElim) (use two in simp_all)
      have "joinable S
          (HElim h C pms ?lms1 t) (HElim h C pms ?lms2 t)"
        by (rule joinableI[OF left_path right_path])
      with x y show ?thesis by simp
    next
      fix t'
      assume tt': "red S t t'" and y: "y = HElim h C pms lms t'"
      have left_path: "reds S
          (HElim h C pms ?lms1 t) (HElim h C pms ?lms1 t')"
        by (rule reds_HElim_scrutinee[OF red_as_reds[OF tt']])
      have right_path: "reds S
          (HElim h C pms lms t') (HElim h C pms ?lms1 t')"
        by (rule reds_HElim) (use rl1 in simp_all)
      have "joinable S
          (HElim h C pms ?lms1 t) (HElim h C pms lms t')"
        by (rule joinableI[OF left_path right_path])
      with x y show ?thesis by simp
    qed
  next
    fix t'
    assume tt': "red S t t'" and x: "x = HElim h C pms lms t'"
    show ?thesis
    proof (rule red_HElimE[OF right])
      fix k as
      assume t0: "t = PCon h k as"
        and k: "k < length (pcons (S h))"
        and y: "y = apps (pms ! k)
          (elimArgs h C pms lms (pcons (S h) ! k) as)"
      have regroot: "regular S (HElim h C pms lms (PCon h k as))"
        using reg t0 by simp
      have other: "red S (HElim h C pms lms (PCon h k as)) x"
        using left t0 by simp
      have peak: "joinable S
          (apps (pms ! k)
            (elimArgs h C pms lms (pcons (S h) ! k) as)) x"
        by (rule point_root_peak[OF regroot k other])
      from joinable_sym[OF peak] x y show ?thesis by simp
    next
      fix k as j
      assume t0: "t = LCon h k as (DVar j)"
        and k: "k < length (lcons (S h))"
        and y: "y = apps (dsubst S 0 (DVar j) (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as)"
      have regroot: "regular S
          (HElim h C pms lms (LCon h k as (DVar j)))"
        using reg t0 by simp
      have other: "red S
          (HElim h C pms lms (LCon h k as (DVar j))) x"
        using left t0 by simp
      have peak: "joinable S
          (apps (dsubst S 0 (DVar j) (lms ! k))
            (elimArgs h C pms lms (lcons (S h) ! k) as)) x"
        by (rule path_root_peak[OF regroot k other])
      from joinable_sym[OF peak] x y show ?thesis by simp
    next
      fix xs m m' ys
      assume pms2: "pms = xs @ m # ys" and mm': "red S m m'"
        and y: "y = HElim h C (xs @ m' # ys) lms t"
      let ?pms2 = "xs @ m' # ys"
      have rp2: "list_reds S pms ?pms2"
        using pms2 list_red_imp_list_reds[
          OF list_red_append[OF mm', of xs ys]]
        by simp
      have left_path: "reds S
          (HElim h C pms lms t') (HElim h C ?pms2 lms t')"
        by (rule reds_HElim) (use rp2 in simp_all)
      have right_path: "reds S
          (HElim h C ?pms2 lms t) (HElim h C ?pms2 lms t')"
        by (rule reds_HElim_scrutinee[OF red_as_reds[OF tt']])
      have "joinable S
          (HElim h C pms lms t') (HElim h C ?pms2 lms t)"
        by (rule joinableI[OF left_path right_path])
      with x y show ?thesis by simp
    next
      fix xs m m' ys
      assume lms2: "lms = xs @ m # ys" and mm': "red S m m'"
        and y: "y = HElim h C pms (xs @ m' # ys) t"
      let ?lms2 = "xs @ m' # ys"
      have rl2: "list_reds S lms ?lms2"
        using lms2 list_red_imp_list_reds[
          OF list_red_append[OF mm', of xs ys]]
        by simp
      have left_path: "reds S
          (HElim h C pms lms t') (HElim h C pms ?lms2 t')"
        by (rule reds_HElim) (use rl2 in simp_all)
      have right_path: "reds S
          (HElim h C pms ?lms2 t) (HElim h C pms ?lms2 t')"
        by (rule reds_HElim_scrutinee[OF red_as_reds[OF tt']])
      have "joinable S
          (HElim h C pms lms t') (HElim h C pms ?lms2 t)"
        by (rule joinableI[OF left_path right_path])
      with x y show ?thesis by simp
    next
      fix t''
      assume tt'': "red S t t''" and y: "y = HElim h C pms lms t''"
      from local_t[OF tt' tt''] obtain w where tw: "reds S t' w"
        and ttw: "reds S t'' w"
        unfolding joinable_def by blast
      have left_path: "reds S
          (HElim h C pms lms t') (HElim h C pms lms w)"
        by (rule reds_HElim) (use tw in simp_all)
      have right_path: "reds S
          (HElim h C pms lms t'') (HElim h C pms lms w)"
        by (rule reds_HElim) (use ttw in simp_all)
      have "joinable S
          (HElim h C pms lms t') (HElim h C pms lms t'')"
        by (rule joinableI[OF left_path right_path])
      with x y show ?thesis by simp
  qed
qed

theorem red_local_confluence:
  assumes reg: "regular S t"
    and left: "red S t u" and right: "red S t v"
  shows "joinable S u v"
  using assms
proof (induct t arbitrary: u v)
  case (Var i)
  from Var.prems(2) show ?case
    by (cases rule: red.cases)
next
  case (Lam A t)
  from Lam.prems(2) obtain t1 where u: "u = Lam A t1"
    and one: "red S t t1"
    by (rule red_LamE)
  from Lam.prems(3) obtain t2 where v: "v = Lam A t2"
    and two: "red S t t2"
    by (rule red_LamE)
  have jt: "joinable S t1 t2"
    by (rule Lam.hyps[OF _ one two])
      (use Lam.prems in simp_all)
  from joinable_Lam[OF jt, of A] u v show ?case by simp
next
  case (App t w)
  have regt: "regular S t" and regw: "regular S w"
    using App.prems by simp_all
  have local_t: "\<And>x y. red S t x \<Longrightarrow> red S t y \<Longrightarrow>
      joinable S x y"
    by (rule App.hyps(1)[OF regt])
  have local_w: "\<And>x y. red S w x \<Longrightarrow> red S w y \<Longrightarrow>
      joinable S x y"
    by (rule App.hyps(2)[OF regw])
  show ?case
    by (rule red_App_local_confluence[
          OF regt regw local_t local_w App.prems(2,3)])
next
  case (PCon h k as)
  from PCon.prems(2) obtain xs where u: "u = PCon h k xs"
    and one: "list_red S as xs"
    by (rule red_PCon_list)
  from PCon.prems(3) obtain ys where v: "v = PCon h k ys"
    and two: "list_red S as ys"
    by (rule red_PCon_list)
  have local: "\<And>a b c. a \<in> set as \<Longrightarrow>
      red S a b \<Longrightarrow> red S a c \<Longrightarrow> joinable S b c"
  proof -
    fix a b c
    assume mem: "a \<in> set as" and ab: "red S a b" and ac: "red S a c"
    have rega: "regular S a"
      using PCon.prems(1) mem by (auto simp: list_all_iff)
    show "joinable S b c"
      by (rule PCon.hyps[OF mem rega ab ac])
  qed
  have "\<exists>zs. list_reds S xs zs \<and> list_reds S ys zs"
    by (rule list_red_local_confluence[OF local one two])
  then obtain zs where xz: "list_reds S xs zs"
    and yz: "list_reds S ys zs" by blast
  have left_path: "reds S (PCon h k xs) (PCon h k zs)"
    by (rule reds_PCon[OF xz])
  have right_path: "reds S (PCon h k ys) (PCon h k zs)"
    by (rule reds_PCon[OF yz])
  have "joinable S (PCon h k xs) (PCon h k ys)"
    by (rule joinableI[OF left_path right_path])
  with u v show ?case by simp
next
  case (LCon h k as d)
  from LCon.prems(2) obtain xs where u: "u = LCon h k xs d"
    and one: "list_red S as xs"
    by (rule red_LCon_list)
  from LCon.prems(3) obtain ys where v: "v = LCon h k ys d"
    and two: "list_red S as ys"
    by (rule red_LCon_list)
  have local: "\<And>a b c. a \<in> set as \<Longrightarrow>
      red S a b \<Longrightarrow> red S a c \<Longrightarrow> joinable S b c"
  proof -
    fix a b c
    assume mem: "a \<in> set as" and ab: "red S a b" and ac: "red S a c"
    have rega: "regular S a"
      using LCon.prems(1) mem by (auto simp: list_all_iff)
    show "joinable S b c"
      by (rule LCon.hyps[OF mem rega ab ac])
  qed
  have "\<exists>zs. list_reds S xs zs \<and> list_reds S ys zs"
    by (rule list_red_local_confluence[OF local one two])
  then obtain zs where xz: "list_reds S xs zs"
    and yz: "list_reds S ys zs" by blast
  have left_path: "reds S (LCon h k xs d) (LCon h k zs d)"
    by (rule reds_LCon[OF xz])
  have right_path: "reds S (LCon h k ys d) (LCon h k zs d)"
    by (rule reds_LCon[OF yz])
  have "joinable S (LCon h k xs d) (LCon h k ys d)"
    by (rule joinableI[OF left_path right_path])
  with u v show ?case by simp
next
  case (HElim h C pms lms t)
  have local_pms: "\<And>m x y. m \<in> set pms \<Longrightarrow>
      red S m x \<Longrightarrow> red S m y \<Longrightarrow> joinable S x y"
  proof -
    fix m x y
    assume mem: "m \<in> set pms" and mx: "red S m x" and my: "red S m y"
    have regm: "regular S m"
      using HElim.prems(1) mem by (auto simp: list_all_iff)
    show "joinable S x y"
      by (rule HElim.hyps(1)[OF mem regm mx my])
  qed
  have local_lms: "\<And>m x y. m \<in> set lms \<Longrightarrow>
      red S m x \<Longrightarrow> red S m y \<Longrightarrow> joinable S x y"
  proof -
    fix m x y
    assume mem: "m \<in> set lms" and mx: "red S m x" and my: "red S m y"
    have regm: "regular S m"
      using HElim.prems(1) mem by (auto simp: list_all_iff)
    show "joinable S x y"
      by (rule HElim.hyps(2)[OF mem regm mx my])
  qed
  have local_t: "\<And>x y. red S t x \<Longrightarrow> red S t y \<Longrightarrow>
      joinable S x y"
    by (rule HElim.hyps(3))
      (use HElim.prems in simp_all)
  show ?case
    by (rule red_HElim_local_confluence[
          OF HElim.prems(1) local_pms local_lms local_t
            HElim.prems(2,3)])
qed

lemma reds_first_step:
  assumes "reds S t u"
  shows "t = u \<or> (\<exists>v. red S t v \<and> reds S v u)"
  using assms
proof (induct rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  show ?case
  proof (cases "t = y")
    case True
    have "red S t z" using step.hyps(2) True by simp
    moreover have "reds S z z" by simp
    ultimately show ?thesis by blast
  next
    case False
    from step.hyps(3) False obtain v where tv: "red S t v"
      and vy: "reds S v y" by blast
    have "reds S v z"
      by (rule rtranclp.rtrancl_into_rtrancl[OF vy step.hyps(2)])
    with tv show ?thesis by blast
  qed
qed

lemma nform_reds_eq:
  assumes normal: "nform S t" and steps: "reds S t u"
  shows "u = t"
proof -
  from reds_first_step[OF steps] show ?thesis
  proof
    assume "t = u"
    then show ?thesis by simp
  next
    assume "\<exists>v. red S t v \<and> reds S v u"
    then obtain v where "red S t v" by blast
    with normal show ?thesis unfolding nform_def by blast
  qed
qed

theorem SN_unique_normal_form:
  assumes sn: "SN S t" and reg: "regular S t"
    and tu: "reds S t u" and un: "nform S u"
    and tv: "reds S t v" and vn: "nform S v"
  shows "u = v"
  using sn reg tu un tv vn
proof (induct arbitrary: u v rule: SN.induct)
  case (SNI t)
  show ?case
  proof (cases "t = u")
    case True
    have "v = t" by (rule nform_reds_eq[OF _ SNI.prems(4)])
      (use SNI.prems True in simp)
    with True show ?thesis by simp
  next
    case not_u: False
    from reds_first_step[OF SNI.prems(2)] not_u obtain t1 where
      step1: "red S t t1" and path1: "reds S t1 u"
      by blast
    show ?thesis
    proof (cases "t = v")
      case True
      have "u = t" by (rule nform_reds_eq[OF _ SNI.prems(2)])
        (use SNI.prems True in simp)
      with True show ?thesis by simp
    next
      case not_v: False
      from reds_first_step[OF SNI.prems(4)] not_v obtain t2 where
        step2: "red S t t2" and path2: "reds S t2 v"
        by blast
      have peak: "joinable S t1 t2"
        by (rule red_local_confluence[OF SNI.prems(1) step1 step2])
      then obtain z where one: "reds S t1 z" and two: "reds S t2 z"
        unfolding joinable_def by blast
      have sn1: "SN S t1" by (rule SNI.hyps(1)[OF step1])
      have snz: "SN S z" by (rule SN_reds[OF one sn1])
      from SN_reaches_normal_form[OF snz] obtain n where
        zn: "reds S z n" and nn: "nform S n" by blast
      have reg1: "regular S t1"
        by (rule regular_red[OF step1 SNI.prems(1)])
      have reg2: "regular S t2"
        by (rule regular_red[OF step2 SNI.prems(1)])
      have t1n: "reds S t1 n"
        by (rule rtranclp_trans[OF one zn])
      have t2n: "reds S t2 n"
        by (rule rtranclp_trans[OF two zn])
      have un_eq: "u = n"
        by (rule SNI.hyps(2)[OF step1 reg1 path1
              SNI.prems(3) t1n nn])
      have vn_eq: "v = n"
        by (rule SNI.hyps(2)[OF step2 reg2 path2
              SNI.prems(5) t2n nn])
      from un_eq vn_eq show ?thesis by simp
    qed
  qed
qed

theorem SN_church_rosser:
  assumes sn: "SN S t" and reg: "regular S t"
    and tu: "reds S t u" and tv: "reds S t v"
  shows "\<exists>w. reds S u w \<and> reds S v w"
proof -
  have snu: "SN S u" by (rule SN_reds[OF tu sn])
  have snv: "SN S v" by (rule SN_reds[OF tv sn])
  from SN_reaches_normal_form[OF snu] obtain un where
    uun: "reds S u un" and unn: "nform S un" by blast
  from SN_reaches_normal_form[OF snv] obtain vn where
    vvn: "reds S v vn" and vnn: "nform S vn" by blast
  have tun: "reds S t un" by (rule rtranclp_trans[OF tu uun])
  have tvn: "reds S t vn" by (rule rtranclp_trans[OF tv vvn])
  have "un = vn"
    by (rule SN_unique_normal_form[OF sn reg tun unn tvn vnn])
  with uun vvn show ?thesis by blast
qed

theorem wt_church_rosser:
  assumes typed: "wt S D G t A"
    and "reds S t u" and "reds S t v"
  shows "\<exists>w. reds S u w \<and> reds S v w"
  by (rule SN_church_rosser[
        OF wt_strong_normalization[OF typed]
          regular_wt[OF typed] assms(2,3)])

theorem church_rosser:
  assumes typed: "cwt S D G t A"
    and "reds S t u" and "reds S t v"
  shows "\<exists>w. reds S u w \<and> reds S v w"
  by (rule wt_church_rosser[OF cwt_wt[OF typed] assms(2,3)])

corollary wt_unique_normal_form:
  assumes typed: "wt S D G t A"
    and "reds S t u" and "nform S u"
    and "reds S t v" and "nform S v"
  shows "u = v"
  by (rule SN_unique_normal_form[
        OF wt_strong_normalization[OF typed]
          regular_wt[OF typed] assms(2,3,4,5)])

corollary unique_normal_form:
  assumes typed: "cwt S D G t A"
    and "reds S t u" and "nform S u"
    and "reds S t v" and "nform S v"
  shows "u = v"
  by (rule wt_unique_normal_form[
        OF cwt_wt[OF typed] assms(2,3,4,5)])

end
