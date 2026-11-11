theory HIT_Normalization
  imports HIT_Canonicity
begin

section \<open>Strong normalization\<close>

subsection \<open>Dimension erasure and regular terms\<close>

fun variable_dims :: "tm \<Rightarrow> bool" where
  "variable_dims (Var i) = True"
| "variable_dims (Lam A t) = variable_dims t"
| "variable_dims (App t u) = (variable_dims t \<and> variable_dims u)"
| "variable_dims (PCon h k as) = list_all variable_dims as"
| "variable_dims (LCon h k as d) =
    (list_all variable_dims as \<and> (\<exists>j. d = DVar j))"
| "variable_dims (HElim h C pms lms t) =
    (list_all variable_dims pms \<and> list_all variable_dims lms \<and>
      variable_dims t)"

fun regular :: "sigenv \<Rightarrow> tm \<Rightarrow> bool" where
  "regular S (Var i) = True"
| "regular S (Lam A t) = regular S t"
| "regular S (App t u) = (regular S t \<and> regular S u)"
| "regular S (PCon h k as) =
    (k < length (pcons (S h)) \<and>
      length as = length (pcons (S h) ! k) \<and>
      list_all (regular S) as)"
| "regular S (LCon h k as d) =
    (k < length (lcons (S h)) \<and>
      length as = length (lcons (S h) ! k) \<and>
      list_all (regular S) as \<and> (\<exists>j. d = DVar j))"
| "regular S (HElim h C pms lms t) =
    (length pms = length (pcons (S h)) \<and>
      length lms = length (lcons (S h)) \<and>
      list_all (regular S) pms \<and> list_all (regular S) lms \<and>
      regular S t)"

fun erase_dims :: "sigenv \<Rightarrow> tm \<Rightarrow> tm" where
  "erase_dims S (Var i) = Var i"
| "erase_dims S (Lam A t) = Lam A (erase_dims S t)"
| "erase_dims S (App t u) = App (erase_dims S t) (erase_dims S u)"
| "erase_dims S (PCon h k as) = PCon h k (map (erase_dims S) as)"
| "erase_dims S (LCon h k as d) =
    LCon h k (map (erase_dims S) as) (DVar 1)"
| "erase_dims S (HElim h C pms lms t) =
    HElim h C (map (erase_dims S) pms) (map (erase_dims S) lms)
      (erase_dims S t)"

lemma regular_variable_dims:
  "regular S t \<Longrightarrow> variable_dims t"
  by (induct t) (auto simp: list_all_iff)

lemma variable_dims_erase [simp]: "variable_dims (erase_dims S t)"
  by (induct t) (auto simp: list_all_iff)

lemma dclosed0_erase [simp]: "dclosed0 S (erase_dims S t)"
  by (induct t) (auto simp: list_all_iff)

lemma erase_dims_idem [simp]:
  "erase_dims S (erase_dims S t) = erase_dims S t"
  by (induct t) simp_all

lemma variable_dims_dsubst_erase:
  "erase_dims S (dsubst S n (DVar j) (erase_dims S t)) =
    erase_dims S t"
proof (induct t arbitrary: n j)
  case (LCon h k as d)
  then show ?case by (cases "1 = n") simp_all
qed simp_all

lemma dsubst_zero_erase [simp]:
  "dsubst S 0 (DVar j) (erase_dims S t) = erase_dims S t"
  by (induct t arbitrary: j) simp_all

lemma erase_dims_dsubst_variable:
  assumes "variable_dims t"
  shows "erase_dims S (dsubst S n (DVar j) t) = erase_dims S t"
  using assms
proof (induct t arbitrary: n j)
  case (LCon h k as d)
  then obtain q where d: "d = DVar q" by auto
  from LCon d show ?case
    by (cases "q = n") (auto simp: list_all_iff)
qed (auto simp: list_all_iff)

lemma erase_dims_lift [simp]:
  "erase_dims S (lift n t) = lift n (erase_dims S t)"
  by (induct t arbitrary: n) simp_all

lemma erase_dims_subst [simp]:
  "erase_dims S (subst n s t) =
    subst n (erase_dims S s) (erase_dims S t)"
  by (induct t arbitrary: n s) simp_all

lemma erase_dims_apps [simp]:
  "erase_dims S (apps t xs) =
    apps (erase_dims S t) (map (erase_dims S) xs)"
  by (induct xs arbitrary: t) simp_all

lemma erase_dims_elimArgs:
  "map (erase_dims S)
      (elimArgs h C pms lms ss as) =
    elimArgs h C (map (erase_dims S) pms) (map (erase_dims S) lms) ss
      (map (erase_dims S) as)"
  by (induct ss arbitrary: as) (auto split: list.split argspec.split)

lemma regular_wt:
  assumes "wt S D G t A"
  shows "regular S t"
  using assms
  by (induct rule: wt.induct)
    (auto simp: list_all_iff in_set_conv_nth)

lemma erase_dims_wt:
  assumes "wt S D G t A"
  shows "wt S {1} G (erase_dims S t) A"
  using assms
proof (induct rule: wt.induct)
  case (wtVar i G D)
  then show ?case by (auto intro: wt.wtVar)
next
  case (wtLam D A G t B)
  then show ?case by (auto intro: wt.wtLam)
next
  case (wtApp D G t A B u)
  then show ?case by (auto intro: wt.wtApp)
next
  case (wtPCon k h as D G)
  then show ?case
    by (auto intro!: wt.wtPCon simp: in_set_conv_nth)
next
  case (wtLCon j D k h as G)
  then show ?case
    by (auto intro!: wt.wtLCon simp: in_set_conv_nth)
next
  case (wtElim D G t h pms lms C)
  have lms: "\<forall>k < length (map (erase_dims S) lms).
      wt S (insert 0 {1}) G ((map (erase_dims S) lms) ! k)
        (methodTy h C (lcons (S h) ! k))"
  proof (intro allI impI)
    fix k
    assume k: "k < length (map (erase_dims S) lms)"
    have "wt S {1} G (erase_dims S (lms ! k))
        (methodTy h C (lcons (S h) ! k))"
      using wtElim(6) k by simp
    then have "wt S (insert 0 {1}) G (erase_dims S (lms ! k))
        (methodTy h C (lcons (S h) ! k))"
      by (rule wt_dimension_mono) auto
    with k show "wt S (insert 0 {1}) G
        ((map (erase_dims S) lms) ! k)
        (methodTy h C (lcons (S h) ! k))"
      by simp
  qed
  have "wt S {1} G
      (HElim h C (map (erase_dims S) pms) (map (erase_dims S) lms)
        (erase_dims S t)) C"
  proof (rule wt.wtElim)
    show "wt S {1} G (erase_dims S t) (Hit h)"
      by (rule wtElim(2))
    show "length (map (erase_dims S) pms) = length (pcons (S h))"
      using wtElim(3) by simp
    show "length (map (erase_dims S) lms) = length (lcons (S h))"
      using wtElim(4) by simp
    show "\<forall>k < length (map (erase_dims S) pms).
        wt S {1} G ((map (erase_dims S) pms) ! k)
          (methodTy h C (pcons (S h) ! k))"
      using wtElim(5) by simp
    show "\<forall>k < length (map (erase_dims S) lms).
        wt S (insert 0 {1}) G ((map (erase_dims S) lms) ! k)
          (methodTy h C (lcons (S h) ! k))"
      by (rule lms)
  qed
  then show ?case by simp
qed

lemma regular_lift:
  "regular S t \<Longrightarrow> regular S (lift n t)"
  by (induct t arbitrary: n) (auto simp: list_all_iff)

lemma variable_dims_lift:
  "variable_dims t \<Longrightarrow> variable_dims (lift n t)"
  by (induct t arbitrary: n) (auto simp: list_all_iff)

lemma variable_dims_subst:
  assumes "variable_dims s" and "variable_dims t"
  shows "variable_dims (subst n s t)"
  using assms variable_dims_lift
  by (induct t arbitrary: n s) (auto simp: list_all_iff)

lemma regular_subst:
  assumes "regular S s" and "regular S t"
  shows "regular S (subst n s t)"
  using assms regular_lift
  by (induct t arbitrary: n s) (auto simp: list_all_iff)

lemma regular_dsubst_variable:
  assumes "regular S t"
  shows "regular S (dsubst S n (DVar j) t)"
  using assms
proof (induct t arbitrary: n j)
  case (LCon h k as d)
  then obtain q where d: "d = DVar q" by auto
  from LCon d show ?case
    by (cases "q = n") (auto simp: list_all_iff)
qed (auto simp: list_all_iff)

lemma regular_apps:
  assumes "regular S t" and "list_all (regular S) xs"
  shows "regular S (apps t xs)"
  using assms by (induct xs arbitrary: t) auto

lemma regular_elimArgs:
  assumes plen: "length pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and pms: "list_all (regular S) pms"
    and lms: "list_all (regular S) lms"
    and args: "list_all (regular S) as"
  shows "list_all (regular S) (elimArgs h C pms lms ss as)"
  using args
proof (induct ss arbitrary: as)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  then show ?case
    using plen llen pms lms
    by (cases as; cases s) (auto simp: list_all_iff)
qed

lemma regular_red:
  assumes step: "red S t u" and source: "regular S t"
  shows "regular S u"
  using step source
proof (induct rule: red.induct)
  case (beta u A t)
  then show ?case by (auto intro: regular_subst)
next
  case (elimPoint k h C pms lms as)
  have method: "regular S (pms ! k)"
    using elimPoint by (auto simp: list_all_iff)
  have args: "list_all (regular S) as"
    using elimPoint by simp
  have eargs: "list_all (regular S)
      (elimArgs h C pms lms (pcons (S h) ! k) as)"
    by (rule regular_elimArgs)
      (use elimPoint args in simp_all)
  show ?case by (rule regular_apps[OF method eargs])
next
  case (elimPath k h C pms lms as j)
  have method0: "regular S (lms ! k)"
    using elimPath by (auto simp: list_all_iff)
  have method: "regular S (dsubst S 0 (DVar j) (lms ! k))"
    by (rule regular_dsubst_variable[OF method0])
  have args: "list_all (regular S) as"
    using elimPath by simp
  have eargs: "list_all (regular S)
      (elimArgs h C pms lms (lcons (S h) ! k) as)"
    by (rule regular_elimArgs)
      (use elimPath args in simp_all)
  show ?case by (rule regular_apps[OF method eargs])
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
  then show ?case by (auto simp: list_all_iff)
next
  case (elimScrutinee t t' h C pms lms)
  then show ?case by simp
qed

lemma red_erase_dims:
  assumes step: "red S t u" and source: "regular S t"
  shows "red S (erase_dims S t) (erase_dims S u)"
  using step source
proof (induct rule: red.induct)
  case (beta u A t)
  then show ?case by (simp add: red.beta)
next
  case (elimPoint k h C pms lms as)
  have kpm: "k < length pms" using elimPoint by simp
  have step: "red S
      (HElim h C (map (erase_dims S) pms) (map (erase_dims S) lms)
        (PCon h k (map (erase_dims S) as)))
      (apps ((map (erase_dims S) pms) ! k)
        (elimArgs h C (map (erase_dims S) pms)
          (map (erase_dims S) lms) (pcons (S h) ! k)
          (map (erase_dims S) as)))"
    by (rule red.elimPoint[
          where S = S and h = h and k = k and C = C
            and pms = "map (erase_dims S) pms"
            and lms = "map (erase_dims S) lms"
            and as = "map (erase_dims S) as",
          OF elimPoint(1)])
  from step kpm show ?case
    by (simp add: erase_dims_elimArgs)
next
  case (elimPath k h C pms lms as j)
  have klm: "k < length lms" using elimPath by simp
  have method_regular: "regular S (lms ! k)"
    using elimPath klm by (auto simp: list_all_iff)
  have method_erase:
      "erase_dims S (dsubst S 0 (DVar j) (lms ! k)) =
        erase_dims S (lms ! k)"
    by (rule erase_dims_dsubst_variable[
          OF regular_variable_dims[OF method_regular]])
  have step: "red S
      (HElim h C (map (erase_dims S) pms) (map (erase_dims S) lms)
        (LCon h k (map (erase_dims S) as) (DVar 1)))
      (apps (dsubst S 0 (DVar 1) ((map (erase_dims S) lms) ! k))
        (elimArgs h C (map (erase_dims S) pms)
          (map (erase_dims S) lms) (lcons (S h) ! k)
          (map (erase_dims S) as)))"
    by (rule red.elimPath[
          where S = S and h = h and k = k and C = C
            and pms = "map (erase_dims S) pms"
            and lms = "map (erase_dims S) lms"
            and as = "map (erase_dims S) as" and j = 1,
          OF elimPath(1)])
  from step klm show ?case
    by (simp add: erase_dims_elimArgs method_erase)
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
      (PCon h k (map (erase_dims S) xs @ erase_dims S a #
        map (erase_dims S) ys))
      (PCon h k (map (erase_dims S) xs @ erase_dims S a' #
        map (erase_dims S) ys))"
    by (rule red.pconArg) (use pconArg in auto)
  then show ?case by simp
next
  case (lconArg a a' h k xs ys d)
  have "red S
      (LCon h k (map (erase_dims S) xs @ erase_dims S a #
        map (erase_dims S) ys) (DVar 1))
      (LCon h k (map (erase_dims S) xs @ erase_dims S a' #
        map (erase_dims S) ys) (DVar 1))"
    by (rule red.lconArg) (use lconArg in auto)
  then show ?case by simp
next
  case (elimPm m m' h C xs ys lms t)
  have "red S
      (HElim h C
        (map (erase_dims S) xs @ erase_dims S m #
          map (erase_dims S) ys)
        (map (erase_dims S) lms) (erase_dims S t))
      (HElim h C
        (map (erase_dims S) xs @ erase_dims S m' #
          map (erase_dims S) ys)
        (map (erase_dims S) lms) (erase_dims S t))"
    by (rule red.elimPm) (use elimPm in auto)
  then show ?case by simp
next
  case (elimLm m m' h C pms xs ys t)
  have "red S
      (HElim h C (map (erase_dims S) pms)
        (map (erase_dims S) xs @ erase_dims S m #
          map (erase_dims S) ys) (erase_dims S t))
      (HElim h C (map (erase_dims S) pms)
        (map (erase_dims S) xs @ erase_dims S m' #
          map (erase_dims S) ys) (erase_dims S t))"
    by (rule red.elimLm) (use elimLm in auto)
  then show ?case by simp
next
  case (elimScrutinee t t' h C pms lms)
  then show ?case by (auto intro: red.elimScrutinee)
qed

lemma SN_erase_dims_reflect_aux:
  assumes sn: "SN S e"
  shows "\<And>t D G A. e = erase_dims S t \<Longrightarrow>
    wf_sigenv S \<Longrightarrow> wt S D G t A \<Longrightarrow> SN S t"
  using sn
proof (induct rule: SN.induct)
  case (SNI e)
  show ?case
  proof (rule SN.SNI)
    fix u
    assume step: "red S t u"
    have reg: "regular S t" by (rule regular_wt[OF SNI.prems(3)])
    have erased_step: "red S e (erase_dims S u)"
      using red_erase_dims[OF step reg] SNI.prems(1) by simp
    have typed: "wt S D G u A"
      by (rule subject_reduction[OF SNI.prems(2) step SNI.prems(3)])
    show "SN S u"
      by (rule SNI.hyps(2)[OF erased_step refl SNI.prems(2) typed])
  qed
qed

lemma SN_erase_dims_reflect:
  assumes "wf_sigenv S" and "wt S D G t A"
    and "SN S (erase_dims S t)"
  shows "SN S t"
  by (rule SN_erase_dims_reflect_aux[OF assms(3) refl assms(1,2)])

subsection \<open>Renaming and simultaneous substitution\<close>

fun up_ren :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "up_ren f 0 = 0"
| "up_ren f (Suc i) = Suc (f i)"

fun vrename :: "(nat \<Rightarrow> nat) \<Rightarrow> tm \<Rightarrow> tm" where
  "vrename f (Var i) = Var (f i)"
| "vrename f (Lam A t) = Lam A (vrename (up_ren f) t)"
| "vrename f (App t u) = App (vrename f t) (vrename f u)"
| "vrename f (PCon h k as) = PCon h k (map (vrename f) as)"
| "vrename f (LCon h k as d) = LCon h k (map (vrename f) as) d"
| "vrename f (HElim h C pms lms t) =
    HElim h C (map (vrename f) pms) (map (vrename f) lms)
      (vrename f t)"

fun up_sub :: "(nat \<Rightarrow> tm) \<Rightarrow> nat \<Rightarrow> tm" where
  "up_sub s 0 = Var 0"
| "up_sub s (Suc i) = lift 0 (s i)"

fun psubst :: "(nat \<Rightarrow> tm) \<Rightarrow> tm \<Rightarrow> tm" where
  "psubst s (Var i) = s i"
| "psubst s (Lam A t) = Lam A (psubst (up_sub s) t)"
| "psubst s (App t u) = App (psubst s t) (psubst s u)"
| "psubst s (PCon h k as) = PCon h k (map (psubst s) as)"
| "psubst s (LCon h k as d) = LCon h k (map (psubst s) as) d"
| "psubst s (HElim h C pms lms t) =
    HElim h C (map (psubst s) pms) (map (psubst s) lms)
      (psubst s t)"

definition ext_sub :: "tm \<Rightarrow> (nat \<Rightarrow> tm) \<Rightarrow> nat \<Rightarrow> tm" where
  "ext_sub u s i = (case i of 0 \<Rightarrow> u | Suc j \<Rightarrow> s j)"

definition Ren :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "Ren n m f \<longleftrightarrow> (\<forall>i < n. f i < m)"

lemma up_ren_id [simp]: "up_ren id = id"
  by (rule ext) (case_tac x; simp)

lemma up_ren_id_apply [simp]: "up_ren (\<lambda>x. x) i = i"
  by (cases i) simp_all

lemma up_ren_comp:
  "up_ren (f \<circ> g) = up_ren f \<circ> up_ren g"
  by (rule ext) (case_tac x; simp)

lemma vrename_id [simp]: "vrename id t = t"
proof (induct t)
  case (Lam A t)
  then show ?case by (simp only: vrename.simps up_ren_id)
qed (simp_all add: map_idI)

lemma vrename_comp:
  "vrename f (vrename g t) = vrename (f \<circ> g) t"
  by (induct t arbitrary: f g)
    (simp_all add: up_ren_comp map_map)

lemma erase_dims_vrename [simp]:
  "erase_dims S (vrename f t) = vrename f (erase_dims S t)"
  by (induct t arbitrary: f) (simp_all add: map_map)

lemma regular_vrename [simp]:
  "regular S (vrename f t) = regular S t"
  by (induct t arbitrary: f) (auto simp: list_all_iff)

lemma variable_dims_vrename [simp]:
  "variable_dims (vrename f t) = variable_dims t"
  by (induct t arbitrary: f) (auto simp: list_all_iff)

lemma up_sub_Var [simp]: "up_sub Var = Var"
  by (rule ext) (case_tac x; simp)

lemma psubst_Var [simp]: "psubst Var t = t"
  by (induct t) (simp_all add: map_idI)

lemma erase_dims_up_sub:
  "(\<lambda>i. erase_dims S (up_sub s i)) =
    up_sub (\<lambda>i. erase_dims S (s i))"
proof
  fix i
  show "erase_dims S (up_sub s i) =
      up_sub (\<lambda>i. erase_dims S (s i)) i"
    by (cases i) simp_all
qed

lemma erase_dims_psubst:
  "erase_dims S (psubst s t) =
    psubst (\<lambda>i. erase_dims S (s i)) (erase_dims S t)"
  by (induct t arbitrary: s)
    (simp_all add: map_map erase_dims_up_sub)

lemma regular_up_sub:
  assumes "\<And>i. regular S (s i)"
  shows "regular S (up_sub s i)"
  using assms by (cases i) (auto intro: regular_lift)

lemma variable_dims_up_sub:
  assumes "\<And>i. variable_dims (s i)"
  shows "variable_dims (up_sub s i)"
  using assms by (cases i) (auto intro: variable_dims_lift)

lemma regular_psubst:
  assumes reg: "regular S t"
    and env: "\<And>i. regular S (s i)"
  shows "regular S (psubst s t)"
  using reg env
  by (induct t arbitrary: s)
    (auto simp: list_all_iff intro: regular_up_sub)

lemma variable_dims_psubst:
  assumes dims: "variable_dims t"
    and env: "\<And>i. variable_dims (s i)"
  shows "variable_dims (psubst s t)"
  using dims env
  by (induct t arbitrary: s)
    (auto simp: list_all_iff intro: variable_dims_up_sub)

lemma Ren_id [simp]: "Ren n n id"
  unfolding Ren_def by simp

lemma Ren_comp:
  assumes "Ren n m f" and "Ren m k g"
  shows "Ren n k (g \<circ> f)"
  using assms unfolding Ren_def by auto

lemma Ren_up:
  assumes "Ren n m f"
  shows "Ren (Suc n) (Suc m) (up_ren f)"
  using assms unfolding Ren_def
  by (intro allI impI) (case_tac i; auto)

lemma Ren_Suc: "Ren n (Suc n) Suc"
  unfolding Ren_def by auto

definition shift_ren :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "shift_ren n i = (if i < n then i else Suc i)"

lemma up_ren_shift:
  "up_ren (shift_ren n) = shift_ren (Suc n)"
  unfolding shift_ren_def
proof
  fix i
  show "up_ren (\<lambda>i. if i < n then i else Suc i) i =
      (if i < Suc n then i else Suc i)"
    by (cases i) simp_all
qed

lemma lift_as_vrename:
  "lift n t = vrename (shift_ren n) t"
  by (induct t arbitrary: n)
    (simp_all add: shift_ren_def up_ren_shift map_map)

lemma vrename_lift0:
  "vrename (up_ren f) (lift 0 t) = lift 0 (vrename f t)"
proof -
  have eq: "up_ren f \<circ> shift_ren 0 = shift_ren 0 \<circ> f"
    unfolding shift_ren_def
    by (rule ext) simp
  show ?thesis
    by (simp add: lift_as_vrename vrename_comp eq)
qed

lemma up_sub_vrename:
  "(\<lambda>i. vrename (up_ren f) (up_sub s i)) =
    up_sub (\<lambda>i. vrename f (s i))"
proof
  fix i
  show "vrename (up_ren f) (up_sub s i) =
      up_sub (\<lambda>i. vrename f (s i)) i"
    by (cases i) (simp_all add: vrename_lift0)
qed

lemma vrename_psubst:
  "vrename f (psubst s t) =
    psubst (\<lambda>i. vrename f (s i)) t"
  by (induct t arbitrary: f s)
    (simp_all add: up_sub_vrename map_map)

lemma up_sub_comp:
  "up_sub s \<circ> up_ren f = up_sub (s \<circ> f)"
proof
  fix i
  show "(up_sub s \<circ> up_ren f) i = up_sub (s \<circ> f) i"
    by (cases i) simp_all
qed

lemma psubst_vrename:
  "psubst s (vrename f t) = psubst (s \<circ> f) t"
  by (induct t arbitrary: f s)
    (simp_all add: up_sub_comp map_map)

definition single_sub :: "nat \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> tm" where
  "single_sub n s i =
    (if i < n then Var i else if i = n then s else Var (i - 1))"

lemma up_sub_single:
  "up_sub (single_sub n s) = single_sub (Suc n) (lift 0 s)"
  unfolding single_sub_def
proof
  fix i
  show "up_sub (\<lambda>i.
      if i < n then Var i else if i = n then s else Var (i - 1)) i =
    (if i < Suc n then Var i
      else if i = Suc n then lift 0 s else Var (i - 1))"
    by (cases i) simp_all
qed

lemma subst_as_psubst:
  "subst n s t = psubst (single_sub n s) t"
  by (induct t arbitrary: n s)
    (simp_all add: single_sub_def up_sub_single map_map)

lemma vrename_subst0:
  "vrename f (subst 0 s t) =
    subst 0 (vrename f s) (vrename (up_ren f) t)"
proof -
  have eq: "(\<lambda>i. vrename f (single_sub 0 s i)) =
      single_sub 0 (vrename f s) \<circ> up_ren f"
  proof
    fix i
    show "vrename f (single_sub 0 s i) =
        (single_sub 0 (vrename f s) \<circ> up_ren f) i"
      by (cases i) (simp_all add: single_sub_def)
  qed
  show ?thesis
    by (simp add: subst_as_psubst vrename_psubst psubst_vrename eq)
qed

lemma vrename_apps [simp]:
  "vrename f (apps t xs) = apps (vrename f t) (map (vrename f) xs)"
  by (induct xs arbitrary: t) simp_all

lemma vrename_elimArgs:
  "map (vrename f) (elimArgs h C pms lms ss as) =
    elimArgs h C (map (vrename f) pms) (map (vrename f) lms) ss
      (map (vrename f) as)"
  by (induct ss arbitrary: as) (auto split: list.split argspec.split)

lemma vrename_dsubst_variable:
  assumes "variable_dims t"
  shows "vrename f (dsubst S n (DVar j) t) =
    dsubst S n (DVar j) (vrename f t)"
  using assms
proof (induct t arbitrary: f n j)
  case (LCon h k as d)
  then obtain q where d: "d = DVar q" by auto
  from LCon d show ?case
    by (cases "q = n") (auto simp: list_all_iff map_map)
qed (auto simp: list_all_iff map_map)

lemma dclosed0_vrename:
  assumes "variable_dims t"
  shows "dclosed0 S (vrename f t) \<longleftrightarrow> dclosed0 S t"
  using assms
  by (induct t arbitrary: f)
    (auto simp: list_all_iff)

lemma red_vrename:
  assumes step: "red S t u" and source: "regular S t"
  shows "red S (vrename f t) (vrename f u)"
  using step source
proof (induct arbitrary: f rule: red.induct)
  case (beta u A t)
  have dims: "variable_dims u"
    by (rule regular_variable_dims[where S = S]) (use beta in simp)
  have closed: "dclosed0 S (vrename f u)"
    using beta.hyps(1) dclosed0_vrename[OF dims, of S f] by simp
  show ?case
    by (simp add: vrename_subst0 red.beta[OF closed])
next
  case (elimPoint k h C pms lms as)
  have kpm: "k < length pms" using elimPoint by simp
  have step: "red S
      (HElim h C (map (vrename f) pms) (map (vrename f) lms)
        (PCon h k (map (vrename f) as)))
      (apps ((map (vrename f) pms) ! k)
        (elimArgs h C (map (vrename f) pms) (map (vrename f) lms)
          (pcons (S h) ! k) (map (vrename f) as)))"
    by (rule red.elimPoint[
          where S = S and h = h and k = k and C = C
            and pms = "map (vrename f) pms"
            and lms = "map (vrename f) lms"
            and as = "map (vrename f) as",
          OF elimPoint(1)])
  from step kpm show ?case
    by (simp add: vrename_elimArgs)
next
  case (elimPath k h C pms lms as j)
  have klm: "k < length lms" using elimPath by simp
  have method_regular: "regular S (lms ! k)"
    using elimPath klm by (auto simp: list_all_iff)
  have method_dims: "variable_dims (lms ! k)"
    by (rule regular_variable_dims[OF method_regular])
  have method:
      "vrename f (dsubst S 0 (DVar j) (lms ! k)) =
        dsubst S 0 (DVar j) (vrename f (lms ! k))"
    by (rule vrename_dsubst_variable[OF method_dims])
  have step: "red S
      (HElim h C (map (vrename f) pms) (map (vrename f) lms)
        (LCon h k (map (vrename f) as) (DVar j)))
      (apps (dsubst S 0 (DVar j) ((map (vrename f) lms) ! k))
        (elimArgs h C (map (vrename f) pms) (map (vrename f) lms)
          (lcons (S h) ! k) (map (vrename f) as)))"
    by (rule red.elimPath[
          where S = S and h = h and k = k and C = C
            and pms = "map (vrename f) pms"
            and lms = "map (vrename f) lms"
            and as = "map (vrename f) as" and j = j,
          OF elimPath(1)])
  from step klm method show ?case
    by (simp add: vrename_elimArgs)
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
      (PCon h k (map (vrename f) xs @ vrename f a #
        map (vrename f) ys))
      (PCon h k (map (vrename f) xs @ vrename f a' #
        map (vrename f) ys))"
    by (rule red.pconArg) (use pconArg in auto)
  then show ?case by simp
next
  case (lconArg a a' h k xs ys d)
  have "red S
      (LCon h k (map (vrename f) xs @ vrename f a #
        map (vrename f) ys) d)
      (LCon h k (map (vrename f) xs @ vrename f a' #
        map (vrename f) ys) d)"
    by (rule red.lconArg) (use lconArg in auto)
  then show ?case by simp
next
  case (elimPm m m' h C xs ys lms t)
  have "red S
      (HElim h C
        (map (vrename f) xs @ vrename f m # map (vrename f) ys)
        (map (vrename f) lms) (vrename f t))
      (HElim h C
        (map (vrename f) xs @ vrename f m' # map (vrename f) ys)
        (map (vrename f) lms) (vrename f t))"
    by (rule red.elimPm) (use elimPm in auto)
  then show ?case by simp
next
  case (elimLm m m' h C pms xs ys t)
  have "red S
      (HElim h C (map (vrename f) pms)
        (map (vrename f) xs @ vrename f m # map (vrename f) ys)
        (vrename f t))
      (HElim h C (map (vrename f) pms)
        (map (vrename f) xs @ vrename f m' # map (vrename f) ys)
        (vrename f t))"
    by (rule red.elimLm) (use elimLm in auto)
  then show ?case by simp
next
  case (elimScrutinee t t' h C pms lms)
  then show ?case by (auto intro: red.elimScrutinee)
qed

lemma map_decompE:
  assumes "xs @ a # ys = map f zs"
  obtains us b vs where
    "zs = us @ b # vs" "xs = map f us" "a = f b" "ys = map f vs"
proof -
  have mapped: "map f zs = xs @ (a # ys)" using assms by simp
  have "\<exists>us ws. zs = us @ ws \<and> xs = map f us \<and>
      a # ys = map f ws"
    by (rule map_eq_append_conv[THEN iffD1, OF mapped])
  then obtain us ws where
    zs: "zs = us @ ws" and xs: "xs = map f us"
    and rest: "a # ys = map f ws"
    by (elim exE conjE)
  from rest obtain b vs where ws: "ws = b # vs"
    and a: "a = f b" and ys: "ys = map f vs"
    by (cases ws) auto
  from zs xs ws a ys that show thesis by simp
qed

lemma red_vrenameE_aux:
  assumes step: "red S a v"
  shows "\<And>q f. regular S q \<Longrightarrow> a = vrename f q \<Longrightarrow>
    \<exists>u. red S q u \<and> v = vrename f u"
  using step
proof (induct arbitrary: q f rule: red.induct)
  case (beta u A t)
  from beta show ?case
  proof (cases q)
    case (App x y)
    from beta App show ?thesis
    proof (cases x)
      case (Lam A' body)
      from beta App Lam have
        type: "A' = A"
        and body: "t = vrename (up_ren f) body"
        and arg: "u = vrename f y"
        by auto
      have red: "red S (App (Lam A' body) y) (subst 0 y body)"
      proof (rule red.beta)
        have regy: "regular S y" using beta.prems App Lam by simp
        have dims: "variable_dims y"
          by (rule regular_variable_dims[OF regy])
        show "dclosed0 S y"
          using beta.hyps(1) arg dclosed0_vrename[OF dims, of S f]
          by simp
      qed
      have eq: "subst 0 u t = vrename f (subst 0 y body)"
        using body arg by (simp add: vrename_subst0)
      from red eq App Lam show ?thesis by auto
    qed auto
  qed auto
next
  case (elimPoint k h C pms lms as)
  from elimPoint show ?case
  proof (cases q)
    case (HElim h' C' pms' lms' scrut)
    from elimPoint HElim show ?thesis
    proof (cases scrut)
      case (PCon h'' k' as')
      with HElim elimPoint show ?thesis
        by (auto simp: vrename_elimArgs intro: red.elimPoint)
    qed auto
  qed auto
next
  case (elimPath k h C pms lms as j)
  from elimPath show ?case
  proof (cases q)
    case (HElim h' C' pms' lms' scrut)
    from elimPath HElim show ?thesis
    proof (cases scrut)
      case (LCon h'' k' as' d)
      from elimPath HElim LCon show ?thesis
      proof (cases d)
        case (DVar j')
        have klm: "k' < length lms'"
          using DVar LCon HElim elimPath by simp
        have mreg: "regular S (lms' ! k')"
          using DVar LCon HElim elimPath klm
          by (auto simp: list_all_iff)
        have mdims: "variable_dims (lms' ! k')"
          by (rule regular_variable_dims[OF mreg])
        let ?u = "apps (dsubst S 0 (DVar j') (lms' ! k'))
          (elimArgs h'' C' pms' lms' (lcons (S h'') ! k') as')"
        have r: "red S
            (HElim h'' C' pms' lms'
              (LCon h'' k' as' (DVar j'))) ?u"
          by (rule red.elimPath) (use DVar LCon HElim elimPath in simp)
        have eq:
            "vrename f ?u =
              apps (dsubst S 0 (DVar j') (vrename f (lms' ! k')))
                (elimArgs h'' C' (map (vrename f) pms')
                  (map (vrename f) lms') (lcons (S h'') ! k')
                  (map (vrename f) as'))"
          by (simp add: vrename_elimArgs
              vrename_dsubst_variable[OF mdims])
        from r eq DVar LCon HElim elimPath show ?thesis by auto
      qed auto
    qed auto
  qed auto
next
  case (appL t t' u)
  from appL show ?case
  proof (cases q)
    case (App x y)
    have regx: "regular S x" using appL App by simp
    obtain x' where r: "red S x x'" and eq: "t' = vrename f x'"
      using appL.hyps(2)[OF regx, of f] appL App by auto
    have "red S (App x y) (App x' y)" by (rule red.appL[OF r])
    with eq appL App show ?thesis by auto
  qed auto
next
  case (appR u u' t)
  from appR show ?case
  proof (cases q)
    case (App x y)
    have regy: "regular S y" using appR App by simp
    obtain y' where r: "red S y y'" and eq: "u' = vrename f y'"
      using appR.hyps(2)[OF regy, of f] appR App by auto
    have "red S (App x y) (App x y')" by (rule red.appR[OF r])
    with eq appR App show ?thesis by auto
  qed auto
next
  case (lam t t' A)
  from lam show ?case
  proof (cases q)
    case (Lam B body)
    have regbody: "regular S body" using lam Lam by simp
    obtain body' where r: "red S body body'"
      and eq: "t' = vrename (up_ren f) body'"
      using lam.hyps(2)[OF regbody, of "up_ren f"] lam Lam by auto
    have "red S (Lam B body) (Lam B body')" by (rule red.lam[OF r])
    with eq lam Lam show ?thesis by auto
  qed auto
next
  case (pconArg a a' h k xs ys)
  from pconArg show ?case
  proof (cases q)
    case (PCon h' k' as)
    from pconArg PCon obtain us b vs where
      as: "as = us @ b # vs" and xs: "xs = map (vrename f) us"
      and a: "a = vrename f b" and ys: "ys = map (vrename f) vs"
      by (auto elim: map_decompE)
    have regb: "regular S b"
      using pconArg PCon as by (auto simp: list_all_iff)
    obtain b' where r: "red S b b'" and eq: "a' = vrename f b'"
      using pconArg.hyps(2)[OF regb a] by blast
    have red: "red S (PCon h k (us @ b # vs))
        (PCon h k (us @ b' # vs))"
      by (rule red.pconArg[OF r])
    from red eq pconArg PCon as xs a ys show ?thesis by auto
  qed auto
next
  case (lconArg a a' h k xs ys d)
  from lconArg show ?case
  proof (cases q)
    case (LCon h' k' as d')
    from lconArg LCon obtain us b vs where
      as: "as = us @ b # vs" and xs: "xs = map (vrename f) us"
      and a: "a = vrename f b" and ys: "ys = map (vrename f) vs"
      by (auto elim: map_decompE)
    have regb: "regular S b"
      using lconArg LCon as by (auto simp: list_all_iff)
    obtain b' where r: "red S b b'" and eq: "a' = vrename f b'"
      using lconArg.hyps(2)[OF regb a] by blast
    have red: "red S (LCon h k (us @ b # vs) d)
        (LCon h k (us @ b' # vs) d)"
      by (rule red.lconArg[OF r])
    from red eq lconArg LCon as xs a ys show ?thesis by auto
  qed auto
next
  case (elimPm m m' h C xs ys lms t)
  from elimPm show ?case
  proof (cases q)
    case (HElim h' C' pms' lms' t')
    from elimPm HElim obtain us b vs where
      pms: "pms' = us @ b # vs" and xs: "xs = map (vrename f) us"
      and m: "m = vrename f b" and ys: "ys = map (vrename f) vs"
      by (auto elim: map_decompE)
    have regb: "regular S b"
      using elimPm HElim pms by (auto simp: list_all_iff)
    obtain b' where r: "red S b b'" and eq: "m' = vrename f b'"
      using elimPm.hyps(2)[OF regb m] by blast
    have red: "red S
        (HElim h C (us @ b # vs) lms' t')
        (HElim h C (us @ b' # vs) lms' t')"
      by (rule red.elimPm[OF r])
    from red eq elimPm HElim pms xs m ys show ?thesis by auto
  qed auto
next
  case (elimLm m m' h C pms xs ys t)
  from elimLm show ?case
  proof (cases q)
    case (HElim h' C' pms' lms' t')
    from elimLm HElim obtain us b vs where
      lms: "lms' = us @ b # vs" and xs: "xs = map (vrename f) us"
      and m: "m = vrename f b" and ys: "ys = map (vrename f) vs"
      by (auto elim: map_decompE)
    have regb: "regular S b"
      using elimLm HElim lms by (auto simp: list_all_iff)
    obtain b' where r: "red S b b'" and eq: "m' = vrename f b'"
      using elimLm.hyps(2)[OF regb m] by blast
    have red: "red S
        (HElim h C pms' (us @ b # vs) t')
        (HElim h C pms' (us @ b' # vs) t')"
      by (rule red.elimLm[OF r])
    from red eq elimLm HElim lms xs m ys show ?thesis by auto
  qed auto
next
  case (elimScrutinee t t' h C pms lms)
  from elimScrutinee show ?case
  proof (cases q)
    case (HElim h' C' pms' lms' body)
    have regbody: "regular S body" using elimScrutinee HElim by simp
    obtain body' where r: "red S body body'"
      and eq: "t' = vrename f body'"
      using elimScrutinee.hyps(2)[OF regbody, of f] elimScrutinee HElim
      by auto
    have red: "red S (HElim h C pms' lms' body)
        (HElim h C pms' lms' body')"
      by (rule red.elimScrutinee[OF r])
    from red eq elimScrutinee HElim show ?thesis by auto
  qed auto
qed

lemma red_vrenameE:
  assumes reg: "regular S q" and step: "red S (vrename f q) v"
  obtains u where "red S q u" and "v = vrename f u"
  using red_vrenameE_aux[OF step reg refl] that by blast

definition erased :: "sigenv \<Rightarrow> tm \<Rightarrow> bool" where
  "erased S t \<longleftrightarrow> erase_dims S t = t"

lemma map_eq_self_iff:
  "map f xs = xs \<longleftrightarrow> (\<forall>x \<in> set xs. f x = x)"
  by (induct xs) auto

lemma erased_red:
  assumes step: "red S t u" and reg: "regular S t" and fixed: "erased S t"
  shows "erased S u"
  using step reg fixed
proof (induct rule: red.induct)
  case (beta u A t)
  then show ?case
    unfolding erased_def by simp
next
  case (elimPoint k h C pms lms as)
  have fpms: "\<forall>m \<in> set pms. erase_dims S m = m"
    using elimPoint(3) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have flms: "\<forall>m \<in> set lms. erase_dims S m = m"
    using elimPoint(3) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have fas: "\<forall>a \<in> set as. erase_dims S a = a"
    using elimPoint(3) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have kpm: "k < length pms" using elimPoint by simp
  have method: "erase_dims S (pms ! k) = pms ! k"
    using fpms kpm by simp
  have epms: "map (erase_dims S) pms = pms"
    using fpms by (simp add: map_eq_self_iff)
  have elms: "map (erase_dims S) lms = lms"
    using flms by (simp add: map_eq_self_iff)
  have eas: "map (erase_dims S) as = as"
    using fas by (simp add: map_eq_self_iff)
  show ?case
    unfolding erased_def
    by (simp add: erase_dims_elimArgs method epms elms eas)
next
  case (elimPath k h C pms lms as j)
  have fpms: "\<forall>m \<in> set pms. erase_dims S m = m"
    using elimPath(3) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have flms: "\<forall>m \<in> set lms. erase_dims S m = m"
    using elimPath(3) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have fas: "\<forall>a \<in> set as. erase_dims S a = a"
    using elimPath(3) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have klm: "k < length lms" using elimPath by simp
  have method_fixed: "erase_dims S (lms ! k) = lms ! k"
    using flms klm by simp
  have method_regular: "regular S (lms ! k)"
    using elimPath klm by (auto simp: list_all_iff)
  have method:
      "erase_dims S (dsubst S 0 (DVar j) (lms ! k)) = lms ! k"
    using erase_dims_dsubst_variable[
        OF regular_variable_dims[OF method_regular], of S 0 j]
      method_fixed
    by simp
  have method_same:
      "dsubst S 0 (DVar j) (lms ! k) = lms ! k"
  proof -
    have "dsubst S 0 (DVar j) (lms ! k) =
        dsubst S 0 (DVar j) (erase_dims S (lms ! k))"
      using method_fixed by simp
    also have "\<dots> = erase_dims S (lms ! k)" by simp
    also have "\<dots> = lms ! k" by (rule method_fixed)
    finally show ?thesis .
  qed
  have epms: "map (erase_dims S) pms = pms"
    using fpms by (simp add: map_eq_self_iff)
  have elms: "map (erase_dims S) lms = lms"
    using flms by (simp add: map_eq_self_iff)
  have eas: "map (erase_dims S) as = as"
    using fas by (simp add: map_eq_self_iff)
  show ?case
    unfolding erased_def
    by (simp add: erase_dims_elimArgs method method_fixed method_same
        epms elms eas)
next
  case (appL t t' u)
  then show ?case unfolding erased_def by simp
next
  case (appR u u' t)
  then show ?case unfolding erased_def by simp
next
  case (lam t t' A)
  then show ?case unfolding erased_def by simp
next
  case (pconArg a a' h k xs ys)
  have fixed_a: "erased S a"
    using pconArg(4) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have fixed_a': "erased S a'"
    by (rule pconArg.hyps(2)) (use pconArg fixed_a in auto)
  show ?case
    using pconArg(4) fixed_a'
    unfolding erased_def
    by (simp add: map_eq_self_iff)
next
  case (lconArg a a' h k xs ys d)
  have fixed_a: "erased S a"
    using lconArg(4) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have fixed_a': "erased S a'"
    by (rule lconArg.hyps(2)) (use lconArg fixed_a in auto)
  show ?case
    using lconArg(4) fixed_a'
    unfolding erased_def
    by (simp add: map_eq_self_iff)
next
  case (elimPm m m' h C xs ys lms t)
  have fixed_m: "erased S m"
    using elimPm(4) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have fixed_m': "erased S m'"
    by (rule elimPm.hyps(2)) (use elimPm fixed_m in auto)
  show ?case
    using elimPm(4) fixed_m'
    unfolding erased_def
    by (simp add: map_eq_self_iff)
next
  case (elimLm m m' h C pms xs ys t)
  have fixed_m: "erased S m"
    using elimLm(4) unfolding erased_def
    by (simp add: map_eq_self_iff)
  have fixed_m': "erased S m'"
    by (rule elimLm.hyps(2)) (use elimLm fixed_m in auto)
  show ?case
    using elimLm(4) fixed_m'
    unfolding erased_def
    by (simp add: map_eq_self_iff)
next
  case (elimScrutinee t t' h C pms lms)
  have fixed_t: "erased S t"
    using elimScrutinee(4) unfolding erased_def by simp
  have fixed_t': "erased S t'"
    by (rule elimScrutinee.hyps(2)) (use elimScrutinee fixed_t in auto)
  show ?case
    using elimScrutinee(4) fixed_t'
    unfolding erased_def by simp
qed

subsection \<open>Hereditary computability at HIT types\<close>

fun neutral :: "tm \<Rightarrow> bool" where
  "neutral (Var i) = True"
| "neutral (App t u) = True"
| "neutral (HElim h C pms lms t) = True"
| "neutral _ = False"

lemma neutral_vrename:
  "neutral t \<Longrightarrow> neutral (vrename f t)"
  by (cases t) simp_all

inductive hcomp :: "sigenv \<Rightarrow> nat \<Rightarrow> tm \<Rightarrow> bool"
  for S :: sigenv
where
  hneutral:
    "neutral t \<Longrightarrow>
      (\<And>u. red S t u \<Longrightarrow> hcomp S h u) \<Longrightarrow>
      hcomp S h t"
| hpcon:
    "k < length (pcons (S h)) \<Longrightarrow>
      length as = length (pcons (S h) ! k) \<Longrightarrow>
      (\<And>i. i < length as \<Longrightarrow>
        hcomp S (argHit h (pcons (S h) ! k ! i)) (as ! i)) \<Longrightarrow>
      (\<And>u. red S (PCon h k as) u \<Longrightarrow> hcomp S h u) \<Longrightarrow>
      hcomp S h (PCon h k as)"
| hlcon:
    "k < length (lcons (S h)) \<Longrightarrow>
      length as = length (lcons (S h) ! k) \<Longrightarrow>
      (\<And>i. i < length as \<Longrightarrow>
        hcomp S (argHit h (lcons (S h) ! k ! i)) (as ! i)) \<Longrightarrow>
      (\<And>u. red S (LCon h k as (DVar j)) u \<Longrightarrow> hcomp S h u) \<Longrightarrow>
      hcomp S h (LCon h k as (DVar j))"

lemma hcomp_step:
  "hcomp S h t \<Longrightarrow> red S t u \<Longrightarrow> hcomp S h u"
  by (induct rule: hcomp.induct) blast+

lemma hcomp_SN:
  "hcomp S h t \<Longrightarrow> SN S t"
  by (induct rule: hcomp.induct) (blast intro: SN.SNI)+

lemma hcomp_Var: "hcomp S h (Var i)"
  by (rule hcomp.hneutral) (auto elim: red.cases)

inductive list_red :: "sigenv \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> bool"
  for S :: sigenv
where
  lr_head: "red S a b \<Longrightarrow> list_red S (a # xs) (b # xs)"
| lr_tail: "list_red S xs ys \<Longrightarrow> list_red S (a # xs) (a # ys)"

inductive SN_list :: "sigenv \<Rightarrow> tm list \<Rightarrow> bool"
  for S :: sigenv
where
  SNL: "(\<And>ys. list_red S xs ys \<Longrightarrow> SN_list S ys) \<Longrightarrow>
    SN_list S xs"

lemma SN_list_step:
  "SN_list S xs \<Longrightarrow> list_red S xs ys \<Longrightarrow> SN_list S ys"
  by (induct rule: SN_list.induct) blast

lemma SN_list_Cons:
  assumes head: "SN S a" and tail: "SN_list S xs"
  shows "SN_list S (a # xs)"
  using head tail
proof (induct arbitrary: xs rule: SN.induct)
  case (SNI a)
  show ?case
    using SNI.prems
  proof (induct rule: SN_list.induct)
    case (SNL xs)
    have snxs: "SN_list S xs"
      by (rule SN_list.SNL) (use SNL.hyps in blast)
    show ?case
    proof (rule SN_list.SNL)
      fix ys
      assume step: "list_red S (a # xs) ys"
      then show "SN_list S ys"
      proof cases
        case (lr_head b)
        from SNI.hyps(2) snxs lr_head show ?thesis by blast
      next
        case (lr_tail zs)
        from SNL.hyps lr_tail show ?thesis by blast
      qed
    qed
  qed
qed

lemma SN_list_Nil: "SN_list S []"
  by (rule SN_list.SNL) (auto elim: list_red.cases)

lemma SN_list_all:
  assumes "list_all (SN S) xs"
  shows "SN_list S xs"
  using assms
  by (induct xs) (auto intro: SN_list_Nil SN_list_Cons)

lemma SN_lists_induct [consumes 2, case_names step]:
  assumes xs: "SN_list S xs" and ys: "SN_list S ys"
    and step: "\<And>xs ys.
      (\<And>xs'. list_red S xs xs' \<Longrightarrow> P xs' ys) \<Longrightarrow>
      (\<And>ys'. list_red S ys ys' \<Longrightarrow> P xs ys') \<Longrightarrow>
      P xs ys"
  shows "P xs ys"
  using xs ys
proof (induct arbitrary: ys rule: SN_list.induct)
  case (SNL xs)
  note x_IH = SNL.hyps(2)
  show ?case
    using SNL.prems
  proof (induct rule: SN_list.induct)
    case (SNL ys)
    note y_IH = SNL.hyps(2)
    have snys: "SN_list S ys"
      by (rule SN_list.SNL) (use SNL.hyps(1) in blast)
    show ?case
    proof (rule step)
      fix xs'
      assume lr: "list_red S xs xs'"
      show "P xs' ys" by (rule x_IH[OF lr snys])
    next
      fix ys'
      assume lr: "list_red S ys ys'"
      show "P xs ys'" by (rule y_IH[OF lr])
    qed
  qed
qed

lemma list_red_append:
  "red S a b \<Longrightarrow>
    list_red S (xs @ a # ys) (xs @ b # ys)"
  by (induct xs) (auto intro: list_red.intros)

lemma red_PCon_list:
  assumes "red S (PCon h k as) u"
  obtains bs where "u = PCon h k bs" and "list_red S as bs"
  using assms
  by (cases rule: red.cases) (auto intro: list_red_append)

lemma red_LCon_list:
  assumes "red S (LCon h k as d) u"
  obtains bs where "u = LCon h k bs d" and "list_red S as bs"
  using assms
  by (cases rule: red.cases) (auto intro: list_red_append)

fun hargs ::
  "sigenv \<Rightarrow> nat \<Rightarrow> argspec list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "hargs S h [] [] = True"
| "hargs S h [] (a # as) = False"
| "hargs S h (s # ss) [] = False"
| "hargs S h (s # ss) (a # as) =
    (hcomp S (argHit h s) a \<and> hargs S h ss as)"

lemma hargs_length:
  "hargs S h ss as \<Longrightarrow> length as = length ss"
  by (induct ss arbitrary: as) (case_tac as; auto)+

lemma hargs_nth:
  assumes "hargs S h ss as" and "i < length as"
  shows "hcomp S (argHit h (ss ! i)) (as ! i)"
  using assms
proof (induct ss arbitrary: as i)
  case Nil
  then show ?case by (cases as) auto
next
  case (Cons s ss)
  then obtain a as' where as: "as = a # as'"
    by (cases as) auto
  show ?case
  proof (cases i)
    case 0
    with Cons.prems as show ?thesis by simp
  next
    case (Suc j)
    have tail: "hargs S h ss as'"
      using Cons.prems as by simp
    have bound: "j < length as'"
      using Cons.prems as Suc by simp
    have "hcomp S (argHit h (ss ! j)) (as' ! j)"
      by (rule Cons.hyps[OF tail bound])
    with as Suc show ?thesis by simp
  qed
qed

lemma hargsI:
  assumes "length as = length ss"
    and "\<And>i. i < length as \<Longrightarrow>
      hcomp S (argHit h (ss ! i)) (as ! i)"
  shows "hargs S h ss as"
  using assms
proof (induct ss arbitrary: as)
  case Nil
  then show ?case by (cases as) auto
next
  case (Cons s ss)
  then obtain a as' where as: "as = a # as'"
    by (cases as) auto
  have head: "hcomp S (argHit h s) a"
    using Cons.prems(2)[of 0] as by simp
  have tail: "hargs S h ss as'"
  proof (rule Cons.hyps)
    show "length as' = length ss" using Cons.prems(1) as by simp
    fix i
    assume "i < length as'"
    then have "Suc i < length as" using as by simp
    from Cons.prems(2)[OF this] as
    show "hcomp S (argHit h (ss ! i)) (as' ! i)" by simp
  qed
  from head tail as show ?case by simp
qed

lemma hargs_SN:
  assumes "hargs S h ss as"
  shows "list_all (SN S) as"
  using assms
  by (induct ss arbitrary: as)
    (case_tac as; auto dest: hcomp_SN)+

lemma hargs_list_red:
  assumes step: "list_red S as bs" and args: "hargs S h ss as"
  shows "hargs S h ss bs"
  using step args
proof (induct arbitrary: ss rule: list_red.induct)
  case (lr_head a b xs)
  then show ?case
    by (cases ss) (auto intro: hcomp_step)
next
  case (lr_tail xs ys a)
  then show ?case by (cases ss) auto
qed

lemma hcomp_PCon:
  assumes k: "k < length (pcons (S h))"
    and args: "hargs S h (pcons (S h) ! k) as"
  shows "hcomp S h (PCon h k as)"
proof -
  have snl: "SN_list S as"
    by (rule SN_list_all[OF hargs_SN[OF args]])
  from snl args show ?thesis
  proof (induct rule: SN_list.induct)
    case (SNL as)
    have len: "length as = length (pcons (S h) ! k)"
      by (rule hargs_length[OF SNL.prems])
    show ?case
    proof (rule hcomp.hpcon[
          where S = S and h = h and k = k and as = as, OF k len])
      fix i
      assume "i < length as"
      then show "hcomp S (argHit h (pcons (S h) ! k ! i)) (as ! i)"
        by (rule hargs_nth[OF SNL.prems])
    next
      fix u
      assume step: "red S (PCon h k as) u"
      then obtain bs where u: "u = PCon h k bs"
        and lr: "list_red S as bs"
        by (rule red_PCon_list)
      have hargs: "hargs S h (pcons (S h) ! k) bs"
        by (rule hargs_list_red[OF lr SNL.prems])
      have "hcomp S h (PCon h k bs)"
        by (rule SNL.hyps(2)[OF lr hargs])
      with u show "hcomp S h u" by simp
    qed
  qed
qed

lemma hcomp_LCon:
  assumes k: "k < length (lcons (S h))"
    and args: "hargs S h (lcons (S h) ! k) as"
  shows "hcomp S h (LCon h k as (DVar j))"
proof -
  have snl: "SN_list S as"
    by (rule SN_list_all[OF hargs_SN[OF args]])
  from snl args show ?thesis
  proof (induct rule: SN_list.induct)
    case (SNL as)
    have len: "length as = length (lcons (S h) ! k)"
      by (rule hargs_length[OF SNL.prems])
    show ?case
    proof (rule hcomp.hlcon[
          where S = S and h = h and k = k and as = as and j = j,
          OF k len])
      fix i
      assume "i < length as"
      then show "hcomp S (argHit h (lcons (S h) ! k ! i)) (as ! i)"
        by (rule hargs_nth[OF SNL.prems])
    next
      fix u
      assume step: "red S (LCon h k as (DVar j)) u"
      then obtain bs where u: "u = LCon h k bs (DVar j)"
        and lr: "list_red S as bs"
        by (rule red_LCon_list)
      have hargs: "hargs S h (lcons (S h) ! k) bs"
        by (rule hargs_list_red[OF lr SNL.prems])
      have "hcomp S h (LCon h k bs (DVar j))"
        by (rule SNL.hyps(2)[OF lr hargs])
      with u show "hcomp S h u" by simp
    qed
  qed
qed

lemma hcomp_vrename:
  assumes comp: "hcomp S h t" and reg: "regular S t"
  shows "hcomp S h (vrename f t)"
  using comp reg
proof (induct arbitrary: f rule: hcomp.induct)
  case (hneutral t h)
  show ?case
  proof (rule hcomp.hneutral)
    show "neutral (vrename f t)"
      by (rule neutral_vrename[OF hneutral.hyps(1)])
    fix v
    assume step: "red S (vrename f t) v"
    then obtain u where r: "red S t u" and v: "v = vrename f u"
      by (rule red_vrenameE[OF hneutral.prems])
    have regu: "regular S u"
      by (rule regular_red[OF r hneutral.prems])
    have "hcomp S h (vrename f u)"
      by (rule hneutral.hyps(3)[OF r regu])
    with v show "hcomp S h v" by simp
  qed
next
  case (hpcon k h as)
  have args: "hargs S h (pcons (S h) ! k) (map (vrename f) as)"
  proof (rule hargsI)
    show "length (map (vrename f) as) = length (pcons (S h) ! k)"
      using hpcon.hyps(2) by simp
    fix i
    assume i: "i < length (map (vrename f) as)"
    have ia: "i < length as" using i by simp
    have regi: "regular S (as ! i)"
      using hpcon.prems i by (auto simp: list_all_iff)
    have "hcomp S (argHit h (pcons (S h) ! k ! i))
        (vrename f (as ! i))"
      by (rule hpcon.hyps(4)[OF ia regi])
    with i show "hcomp S (argHit h (pcons (S h) ! k ! i))
        ((map (vrename f) as) ! i)"
      by simp
  qed
  have "hcomp S h (PCon h k (map (vrename f) as))"
    by (rule hcomp_PCon[OF hpcon.hyps(1) args])
  then show ?case by simp
next
  case (hlcon k h as j)
  have args: "hargs S h (lcons (S h) ! k) (map (vrename f) as)"
  proof (rule hargsI)
    show "length (map (vrename f) as) = length (lcons (S h) ! k)"
      using hlcon.hyps(2) by simp
    fix i
    assume i: "i < length (map (vrename f) as)"
    have ia: "i < length as" using i by simp
    have regi: "regular S (as ! i)"
      using hlcon.prems i by (auto simp: list_all_iff)
    have "hcomp S (argHit h (lcons (S h) ! k ! i))
        (vrename f (as ! i))"
      by (rule hlcon.hyps(4)[OF ia regi])
    with i show "hcomp S (argHit h (lcons (S h) ! k ! i))
        ((map (vrename f) as) ! i)"
      by simp
  qed
  have "hcomp S h (LCon h k (map (vrename f) as) (DVar j))"
    by (rule hcomp_LCon[OF hlcon.hyps(1) args])
  then show ?case by simp
qed

lemma SN_vrename:
  assumes sn: "SN S t" and reg: "regular S t"
  shows "SN S (vrename f t)"
  using sn reg
proof (induct arbitrary: f rule: SN.induct)
  case (SNI t)
  show ?case
  proof (rule SN.SNI)
    fix v
    assume step: "red S (vrename f t) v"
    then obtain u where r: "red S t u" and v: "v = vrename f u"
      by (rule red_vrenameE[OF SNI.prems])
    have regu: "regular S u" by (rule regular_red[OF r SNI.prems])
    have "SN S (vrename f u)" by (rule SNI.hyps(2)[OF r regu])
    with v show "SN S v" by simp
  qed
qed

subsection \<open>A Kripke logical relation\<close>

primrec RC :: "sigenv \<Rightarrow> ty \<Rightarrow> tm \<Rightarrow> bool" where
  "RC S (Hit h) t =
    (regular S t \<and> erased S t \<and> hcomp S h t)"
| "RC S (Fun A B) t =
    (regular S t \<and> erased S t \<and>
      (\<forall>u. RC S A u \<longrightarrow> RC S B (App t u)))"

lemma RC_regular:
  "RC S A t \<Longrightarrow> regular S t"
  by (cases A) auto

lemma RC_erased:
  "RC S A t \<Longrightarrow> erased S t"
  by (cases A) auto

definition CR1 :: "sigenv \<Rightarrow> ty \<Rightarrow> bool" where
  "CR1 S A \<longleftrightarrow> (\<forall>t. RC S A t \<longrightarrow> SN S t)"

definition CR2 :: "sigenv \<Rightarrow> ty \<Rightarrow> bool" where
  "CR2 S A \<longleftrightarrow>
    (\<forall>t u. RC S A t \<longrightarrow> red S t u \<longrightarrow> RC S A u)"

definition CR3 :: "sigenv \<Rightarrow> ty \<Rightarrow> bool" where
  "CR3 S A \<longleftrightarrow>
    (\<forall>t. neutral t \<longrightarrow> regular S t \<longrightarrow> erased S t \<longrightarrow>
      (\<forall>u. red S t u \<longrightarrow> RC S A u) \<longrightarrow> RC S A t)"

lemma RC_props:
  "CR1 S A" "CR2 S A" "CR3 S A"
proof (induct A)
  case (Hit h)
  show "CR1 S (Hit h)"
    unfolding CR1_def by (auto intro: hcomp_SN)
  show "CR2 S (Hit h)"
    unfolding CR2_def
    by (auto intro: regular_red erased_red hcomp_step)
  show "CR3 S (Hit h)"
    unfolding CR3_def
    by (auto intro: hcomp.hneutral)
next
  case (Fun A B)
  show "CR1 S (Fun A B)"
    unfolding CR1_def
  proof (intro allI impI)
    fix t
    assume t: "RC S (Fun A B) t"
    have var: "RC S A (Var 0)"
    proof -
      have cr3: "neutral (Var 0) \<longrightarrow> regular S (Var 0) \<longrightarrow>
          erased S (Var 0) \<longrightarrow>
          (\<forall>u. red S (Var 0) u \<longrightarrow> RC S A u) \<longrightarrow>
          RC S A (Var 0)"
        using Fun(3) unfolding CR3_def by blast
      show ?thesis
        by (rule cr3[rule_format])
          (auto simp: erased_def elim: red.cases)
    qed
    from t var have "RC S B (App t (Var 0))" by simp
    then have "SN S (App t (Var 0))"
      using Fun(4) unfolding CR1_def by blast
    then show "SN S t" by (rule SN_App1)
  qed
  show "CR2 S (Fun A B)"
    unfolding CR2_def
  proof (intro allI impI)
    fix t u
    assume t: "RC S (Fun A B) t" and step: "red S t u"
    have reg: "regular S u"
      by (rule regular_red[OF step]) (use t in simp)
    have fixed: "erased S u"
      by (rule erased_red[OF step]) (use t in simp_all)
    have app: "\<forall>x. RC S A x \<longrightarrow> RC S B (App u x)"
    proof (intro allI impI)
      fix x
      assume x: "RC S A x"
      from t x have old: "RC S B (App t x)" by simp
      have "red S (App t x) (App u x)" by (rule red.appL[OF step])
      with old Fun(5) show "RC S B (App u x)"
        unfolding CR2_def by blast
    qed
    from reg fixed app show "RC S (Fun A B) u" by simp
  qed
  show "CR3 S (Fun A B)"
    unfolding CR3_def
  proof (intro allI impI)
    fix t
    assume neu: "neutral t" and reg: "regular S t" and fixed: "erased S t"
      and reducts: "\<forall>u. red S t u \<longrightarrow> RC S (Fun A B) u"
    have app: "\<forall>x. RC S A x \<longrightarrow> RC S B (App t x)"
    proof (intro allI impI)
      fix x
      assume x: "RC S A x"
      have snx: "SN S x"
        using Fun(1) x unfolding CR1_def by blast
      from snx x show "RC S B (App t x)"
      proof (induct rule: SN.induct)
        case (SNI x)
        have regx: "regular S x" by (rule RC_regular[OF SNI.prems])
        have fixedx: "erased S x" by (rule RC_erased[OF SNI.prems])
        have cr3: "neutral (App t x) \<longrightarrow>
            regular S (App t x) \<longrightarrow> erased S (App t x) \<longrightarrow>
            (\<forall>u. red S (App t x) u \<longrightarrow> RC S B u) \<longrightarrow>
            RC S B (App t x)"
          using Fun(6) unfolding CR3_def by blast
        have red_app: "\<And>u. red S (App t x) u \<Longrightarrow> RC S B u"
        proof -
          fix u
          assume step: "red S (App t x) u"
          then show "RC S B u"
          proof cases
            case beta
            with neu show ?thesis by simp
          next
            case (appL q')
            from reducts appL have "RC S (Fun A B) q'" by blast
            with SNI.prems appL show ?thesis by simp
          next
            case (appR q')
            have x': "RC S A q'"
              using Fun(2) SNI.prems appR unfolding CR2_def by blast
            have "RC S B (App t q')"
              using SNI.hyps(2) appR x' by blast
            with appR show ?thesis by blast
          qed
        qed
        show ?case
        proof (rule cr3[rule_format])
          show "neutral (App t x)" by simp
          show "regular S (App t x)" using reg regx by simp
          show "erased S (App t x)"
            using fixed fixedx red_app unfolding erased_def by simp
          fix u
          assume "red S (App t x) u"
          then show "RC S B u" by (rule red_app)
        qed
      qed
    qed
    from reg fixed app show "RC S (Fun A B) t" by simp
  qed
qed

lemma RC_SN:
  "RC S A t \<Longrightarrow> SN S t"
  using RC_props(1) unfolding CR1_def by blast

lemma RC_red:
  "RC S A t \<Longrightarrow> red S t u \<Longrightarrow> RC S A u"
  using RC_props(2) unfolding CR2_def by blast

lemma RC_neutral:
  assumes "neutral t" "regular S t" "erased S t"
    "\<And>u. red S t u \<Longrightarrow> RC S A u"
  shows "RC S A t"
  using assms RC_props(3) unfolding CR3_def by blast

definition KR :: "sigenv \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> tm \<Rightarrow> bool" where
  "KR S n A t \<longleftrightarrow>
    (\<forall>m f. Ren n m f \<longrightarrow> RC S A (vrename f t))"

lemma KR_core:
  "KR S n A t \<Longrightarrow> RC S A t"
proof -
  assume rel: "KR S n A t"
  from rel have all: "\<forall>m f. Ren n m f \<longrightarrow> RC S A (vrename f t)"
    unfolding KR_def by blast
  from all[rule_format, OF Ren_id[of n]] show "RC S A t" by simp
qed

lemma KR_regular:
  "KR S n A t \<Longrightarrow> regular S t"
proof -
  assume rel: "KR S n A t"
  have "RC S A t" by (rule KR_core[OF rel])
  then show "regular S t" by (cases A) auto
qed

lemma KR_erased:
  "KR S n A t \<Longrightarrow> erased S t"
proof -
  assume rel: "KR S n A t"
  have "RC S A t" by (rule KR_core[OF rel])
  then show "erased S t" by (cases A) auto
qed

lemma KR_SN:
  "KR S n A t \<Longrightarrow> SN S t"
  by (auto intro: RC_SN dest: KR_core)

lemma KR_Hit_hcomp:
  "KR S n (Hit h) t \<Longrightarrow> hcomp S h t"
  by (auto dest: KR_core)

lemma KR_App:
  assumes "KR S n (Fun A B) t" and "KR S n A u"
  shows "KR S n B (App t u)"
  unfolding KR_def
proof (intro allI impI)
  fix m f
  assume ren: "Ren n m f"
  from assms ren have
    "RC S (Fun A B) (vrename f t)" "RC S A (vrename f u)"
    unfolding KR_def by blast+
  then show "RC S B (vrename f (App t u))" by simp
qed

lemma KR_vrename:
  assumes "KR S n A t" and "Ren n m f"
  shows "KR S m A (vrename f t)"
  unfolding KR_def
proof (intro allI impI)
  fix k g
  assume "Ren m k g"
  then have "Ren n k (g \<circ> f)" by (rule Ren_comp[OF assms(2)])
  from assms(1) this show "RC S A (vrename g (vrename f t))"
    unfolding KR_def by (simp add: vrename_comp)
qed

lemma KR_red:
  assumes rel: "KR S n A t" and step: "red S t u"
  shows "KR S n A u"
  unfolding KR_def
proof (intro allI impI)
  fix m f
  assume ren: "Ren n m f"
  from rel ren have source: "RC S A (vrename f t)"
    unfolding KR_def by blast
  have r: "red S (vrename f t) (vrename f u)"
    by (rule red_vrename[OF step KR_regular[OF rel]])
  show "RC S A (vrename f u)" by (rule RC_red[OF source r])
qed

lemma KR_reds:
  assumes "KR S n A t" and "reds S t u"
  shows "KR S n A u"
  using assms(2,1)
  by (induct rule: rtranclp_induct) (auto intro: KR_red)

lemma KR_neutral:
  assumes reg: "regular S t" and fixed: "erased S t" and neu: "neutral t"
    and reducts: "\<And>m f u. Ren n m f \<Longrightarrow>
      red S (vrename f t) u \<Longrightarrow> RC S A u"
  shows "KR S n A t"
  unfolding KR_def
proof (intro allI impI)
  fix m f
  assume ren: "Ren n m f"
  show "RC S A (vrename f t)"
  proof (rule RC_neutral)
    show "neutral (vrename f t)" by (rule neutral_vrename[OF neu])
    show "regular S (vrename f t)" using reg by simp
    show "erased S (vrename f t)"
      using fixed unfolding erased_def by simp
    fix u
    assume "red S (vrename f t) u"
    then show "RC S A u" by (rule reducts[OF ren])
  qed
qed

subsection \<open>The hereditary Kripke candidate\<close>

primrec KC :: "sigenv \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> tm \<Rightarrow> bool" where
  "KC S n (Hit h) t =
    (regular S t \<and> erased S t \<and> hcomp S h t)"
| "KC S n (Fun A B) t =
    (regular S t \<and> erased S t \<and> SN S t \<and>
      (\<forall>m f u. Ren n m f \<longrightarrow> KC S m A u \<longrightarrow>
        KC S m B (App (vrename f t) u)))"

lemma KC_regular:
  "KC S n A t \<Longrightarrow> regular S t"
  by (cases A) auto

lemma KC_erased:
  "KC S n A t \<Longrightarrow> erased S t"
  by (cases A) auto

lemma KC_SN:
  "KC S n A t \<Longrightarrow> SN S t"
  by (cases A) (auto intro: hcomp_SN)

lemma KC_Hit_hcomp:
  "KC S n (Hit h) t \<Longrightarrow> hcomp S h t"
  by simp

lemma erased_vrename:
  "erased S t \<Longrightarrow> erased S (vrename f t)"
  unfolding erased_def by simp

lemma KC_vrename:
  assumes rel: "KC S n A t" and ren: "Ren n m f"
  shows "KC S m A (vrename f t)"
  using rel ren
proof (induct A arbitrary: n m f t)
  case (Hit h)
  have reg: "regular S t" using Hit.prems by simp
  have comp: "hcomp S h t" using Hit.prems by simp
  have "hcomp S h (vrename f t)"
    by (rule hcomp_vrename[OF comp reg])
  moreover have "erased S (vrename f t)"
    by (rule erased_vrename) (use Hit.prems in simp)
  ultimately show ?case using Hit.prems by simp
next
  case (Fun A B)
  have reg: "regular S t" using Fun.prems by simp
  have fixed: "erased S t" using Fun.prems by simp
  have sn: "SN S t" using Fun.prems by simp
  have sn': "SN S (vrename f t)" by (rule SN_vrename[OF sn reg])
  have fixed': "erased S (vrename f t)"
    by (rule erased_vrename[OF fixed])
  have app: "\<forall>k g u. Ren m k g \<longrightarrow> KC S k A u \<longrightarrow>
      KC S k B (App (vrename g (vrename f t)) u)"
  proof (intro allI impI)
    fix k g u
    assume g: "Ren m k g" and u: "KC S k A u"
    have comp: "Ren n k (g \<circ> f)" by (rule Ren_comp[OF Fun.prems(2) g])
    from Fun.prems(1) comp u
    have "KC S k B (App (vrename (g \<circ> f) t) u)" by simp
    then show "KC S k B (App (vrename g (vrename f t)) u)"
      by (simp add: vrename_comp)
  qed
  from reg fixed' sn' app show ?case by simp
qed

lemma KC_App:
  assumes "KC S n (Fun A B) t" and "KC S n A u"
  shows "KC S n B (App t u)"
proof -
  from assms(1) have app: "\<forall>m f u. Ren n m f \<longrightarrow>
      KC S m A u \<longrightarrow> KC S m B (App (vrename f t) u)"
    by simp
  from app[rule_format, OF Ren_id[of n] assms(2)]
  show ?thesis by simp
qed

lemma KC_red:
  assumes rel: "KC S n A t" and step: "red S t u"
  shows "KC S n A u"
  using rel step
proof (induct A arbitrary: n t u)
  case (Hit h)
  then show ?case
    by (auto intro: regular_red erased_red hcomp_step)
next
  case (Fun A B)
  have reg: "regular S u"
    by (rule regular_red[OF Fun.prems(2) KC_regular[OF Fun.prems(1)]])
  have fixed: "erased S u"
    by (rule erased_red[
          OF Fun.prems(2) KC_regular[OF Fun.prems(1)]
            KC_erased[OF Fun.prems(1)]])
  have sn: "SN S u" by (rule SN_step[OF KC_SN[OF Fun.prems(1)] Fun.prems(2)])
  have app: "\<forall>m f x. Ren n m f \<longrightarrow> KC S m A x \<longrightarrow>
      KC S m B (App (vrename f u) x)"
  proof (intro allI impI)
    fix m f x
    assume ren: "Ren n m f" and x: "KC S m A x"
    from Fun.prems(1) ren x
    have old: "KC S m B (App (vrename f t) x)" by simp
    have r: "red S (vrename f t) (vrename f u)"
      by (rule red_vrename[OF Fun.prems(2) KC_regular[OF Fun.prems(1)]])
    have "red S (App (vrename f t) x) (App (vrename f u) x)"
      by (rule red.appL[OF r])
    then show "KC S m B (App (vrename f u) x)"
      by (rule Fun.hyps(2)[OF old])
  qed
  from reg fixed sn app show ?case by simp
qed

lemma KC_reds:
  assumes "KC S n A t" and "reds S t u"
  shows "KC S n A u"
  using assms(2,1)
  by (induct rule: rtranclp_induct) (auto intro: KC_red)

lemma KC_neutral:
  assumes neu: "neutral t" and reg: "regular S t" and fixed: "erased S t"
    and reducts: "\<And>u. red S t u \<Longrightarrow> KC S n A u"
  shows "KC S n A t"
  using neu reg fixed reducts
proof (induct A arbitrary: n t)
  case (Hit h)
  have "hcomp S h t"
    by (rule hcomp.hneutral[OF Hit.prems(1)])
      (use Hit.prems(4) in auto)
  with Hit.prems show ?case by simp
next
  case (Fun A B)
  have sn: "SN S t"
  proof (rule SN.SNI)
    fix u
    assume "red S t u"
    then have "KC S n (Fun A B) u" by (rule Fun.prems(4))
    then show "SN S u" by (rule KC_SN)
  qed
  have app: "\<forall>m f x. Ren n m f \<longrightarrow> KC S m A x \<longrightarrow>
      KC S m B (App (vrename f t) x)"
  proof (intro allI impI)
    fix m f x
    assume ren: "Ren n m f" and x: "KC S m A x"
    have snx: "SN S x" by (rule KC_SN[OF x])
    from snx x show "KC S m B (App (vrename f t) x)"
    proof (induct rule: SN.induct)
      case (SNI x)
      have head_reg: "regular S (vrename f t)"
        using Fun.prems(2) by simp
      have head_fixed: "erased S (vrename f t)"
        using Fun.prems(3) unfolding erased_def by simp
      have app_reg: "regular S (App (vrename f t) x)"
        using head_reg KC_regular[OF SNI.prems] by simp
      have app_fixed: "erased S (App (vrename f t) x)"
        using head_fixed KC_erased[OF SNI.prems]
        unfolding erased_def by simp
      show ?case
      proof (rule Fun.hyps(2)[OF _ app_reg app_fixed])
        show "neutral (App (vrename f t) x)" by simp
        fix y
        assume step: "red S (App (vrename f t) x) y"
        then show "KC S m B y"
        proof cases
          case beta
          have "neutral (vrename f t)"
            by (rule neutral_vrename[OF Fun.prems(1)])
          with beta have False by simp
          then show ?thesis by blast
        next
          case (appL q')
          obtain t' where r: "red S t t'" and q': "q' = vrename f t'"
            using red_vrenameE[OF Fun.prems(2) appL(2)] by blast
          have rel': "KC S n (Fun A B) t'" by (rule Fun.prems(4)[OF r])
          have "KC S m (Fun A B) (vrename f t')"
            by (rule KC_vrename[OF rel' ren])
          with q' have head': "KC S m (Fun A B) q'" by simp
          have "KC S m B (App q' x)"
            by (rule KC_App[OF head' SNI.prems])
          with appL show ?thesis by simp
        next
          case (appR q')
          have x': "KC S m A q'" by (rule KC_red[OF SNI.prems appR(2)])
          have "KC S m B (App (vrename f t) q')"
            by (rule SNI.hyps(2)[OF appR(2) x'])
          with appR show ?thesis by simp
        qed
      qed
    qed
  qed
  from Fun.prems(2,3) sn app show ?case by simp
qed

lemma KC_Var: "KC S n A (Var i)"
proof (rule KC_neutral)
  show "neutral (Var i)" by simp
  show "regular S (Var i)" by simp
  show "erased S (Var i)" unfolding erased_def by simp
  fix u
  assume "red S (Var i) u"
  then show "KC S n A u" by (cases rule: red.cases)
qed

subsection \<open>Substitution and reducibility\<close>

lemma subst_lift_same [simp]:
  "subst n s (lift n t) = t"
  by (induct t arbitrary: n s) (simp_all add: map_idI)

lemma shift_ren_zero [simp]: "shift_ren 0 = Suc"
  unfolding shift_ren_def by (rule ext) simp

lemma lift_zero_as_vrename: "lift 0 t = vrename Suc t"
  by (simp add: lift_as_vrename)

lemma psubst_lift0:
  "psubst (up_sub s) (lift 0 t) = lift 0 (psubst s t)"
proof -
  have env:
      "up_sub s \<circ> shift_ren 0 =
        (\<lambda>i. vrename (shift_ren 0) (s i))"
  proof
    fix i
    show "(up_sub s \<circ> shift_ren 0) i =
        vrename (shift_ren 0) (s i)"
      by (simp add: shift_ren_def lift_zero_as_vrename)
  qed
  have "psubst (up_sub s) (lift 0 t) =
      psubst (up_sub s) (vrename (shift_ren 0) t)"
    by (simp add: lift_as_vrename)
  also have "\<dots> = psubst (up_sub s \<circ> shift_ren 0) t"
    by (rule psubst_vrename)
  also have "\<dots> =
      psubst (\<lambda>i. vrename (shift_ren 0) (s i)) t"
    by (simp only: env)
  also have "\<dots> = vrename (shift_ren 0) (psubst s t)"
    by (simp add: vrename_psubst)
  also have "\<dots> = lift 0 (psubst s t)"
    by (simp add: lift_as_vrename)
  finally show ?thesis .
qed

lemma up_sub_psubst_comp:
  "(\<lambda>i. psubst (up_sub r) (up_sub s i)) =
    up_sub (\<lambda>i. psubst r (s i))"
proof
  fix i
  show "psubst (up_sub r) (up_sub s i) =
      up_sub (\<lambda>i. psubst r (s i)) i"
    by (cases i) (simp_all add: psubst_lift0)
qed

lemma psubst_comp:
  "psubst r (psubst s t) =
    psubst (\<lambda>i. psubst r (s i)) t"
  by (induct t arbitrary: r s)
    (simp_all add: up_sub_psubst_comp map_map)

lemma subst0_psubst:
  "subst 0 (psubst s u) (psubst (up_sub s) t) =
    psubst s (subst 0 u t)"
proof -
  have env:
      "(\<lambda>i. psubst (single_sub 0 (psubst s u)) (up_sub s i)) =
       (\<lambda>i. psubst s (single_sub 0 u i))"
  proof
    fix i
    show "psubst (single_sub 0 (psubst s u)) (up_sub s i) =
        psubst s (single_sub 0 u i)"
    proof (cases i)
      case 0
      then show ?thesis by (simp add: single_sub_def)
    next
      case (Suc j)
      have "psubst (single_sub 0 (psubst s u)) (lift 0 (s j)) = s j"
        by (simp add: subst_as_psubst[symmetric])
      with Suc show ?thesis by (simp add: single_sub_def)
    qed
  qed
  show ?thesis
    by (simp add: subst_as_psubst psubst_comp env)
qed

lemma subst0_psubst_up:
  "subst 0 x (psubst (up_sub s) t) =
    psubst (ext_sub x s) t"
proof -
  have env:
      "(\<lambda>i. psubst (single_sub 0 x) (up_sub s i)) = ext_sub x s"
  proof
    fix i
    show "psubst (single_sub 0 x) (up_sub s i) = ext_sub x s i"
    proof (cases i)
      case 0
      then show ?thesis by (simp add: single_sub_def ext_sub_def)
    next
      case (Suc j)
      have "psubst (single_sub 0 x) (lift 0 (s j)) = s j"
        by (simp add: subst_as_psubst[symmetric])
      with Suc show ?thesis by (simp add: ext_sub_def)
    qed
  qed
  show ?thesis
    by (simp add: subst_as_psubst psubst_comp env)
qed

lemma psubst_apps [simp]:
  "psubst s (apps t xs) = apps (psubst s t) (map (psubst s) xs)"
  by (induct xs arbitrary: t) simp_all

lemma psubst_elimArgs:
  "map (psubst s) (elimArgs h C pms lms ss as) =
    elimArgs h C (map (psubst s) pms) (map (psubst s) lms) ss
      (map (psubst s) as)"
  by (induct ss arbitrary: as) (auto split: list.split argspec.split)

lemma erased_dsubst_zero:
  assumes "erased S t"
  shows "dsubst S 0 (DVar j) t = t"
proof -
  have "dsubst S 0 (DVar j) t =
      dsubst S 0 (DVar j) (erase_dims S t)"
    using assms unfolding erased_def by simp
  also have "\<dots> = erase_dims S t" by simp
  also have "\<dots> = t" using assms unfolding erased_def .
  finally show ?thesis .
qed

lemma erased_up_sub:
  assumes "\<And>i. erased S (s i)"
  shows "erased S (up_sub s i)"
  using assms
proof (cases i)
  case 0
  then show ?thesis unfolding erased_def by simp
next
  case (Suc j)
  have "erase_dims S (s j) = s j"
    using assms[of j] unfolding erased_def .
  with Suc show ?thesis unfolding erased_def by simp
qed

lemma psubst_dsubst_zero:
  assumes dims: "variable_dims t"
    and env: "\<And>i. erased S (s i)"
  shows "psubst s (dsubst S 0 (DVar j) t) =
    dsubst S 0 (DVar j) (psubst s t)"
  using dims env
proof (induct t arbitrary: s j)
  case (Var i)
  then show ?case by (simp add: erased_dsubst_zero)
next
  case (Lam A t)
  have up: "\<And>i. erased S (up_sub s i)"
    by (rule erased_up_sub[OF Lam.prems(2)])
  have dims: "variable_dims t" using Lam.prems(1) by simp
  from Lam.hyps[OF dims up] show ?case by simp
next
  case (LCon h k as d)
  then obtain q where d: "d = DVar q" by auto
  from LCon d show ?case
    by (cases "q = 0") (auto simp: list_all_iff map_map)
qed (auto simp: list_all_iff map_map)

lemma dclosed0_psubst:
  assumes dims: "variable_dims t"
    and closed: "dclosed0 S t"
    and env: "\<And>i. erased S (s i)"
  shows "dclosed0 S (psubst s t)"
proof (unfold dclosed0_def, intro allI)
  fix j
  have "dsubst S 0 (DVar j) (psubst s t) =
      psubst s (dsubst S 0 (DVar j) t)"
    using psubst_dsubst_zero[
      where S = S and t = t and s = s and j = j, OF dims env]
    by simp
  also have "\<dots> = psubst s t"
    using closed unfolding dclosed0_def by simp
  finally show "dsubst S 0 (DVar j) (psubst s t) = psubst s t" .
qed

lemma red_psubst:
  assumes step: "red S t u" and reg: "regular S t"
    and env: "\<And>i. regular S (s i)"
    and fixed: "\<And>i. erased S (s i)"
  shows "red S (psubst s t) (psubst s u)"
  using step reg env fixed
proof (induct arbitrary: s rule: red.induct)
  case (beta u A t)
  have dimsu: "variable_dims u"
    by (rule regular_variable_dims[where S = S]) (use beta in simp)
  have closed: "dclosed0 S (psubst s u)"
    by (rule dclosed0_psubst[OF dimsu beta.hyps(1) beta.prems(3)])
  have r: "red S
      (App (Lam A (psubst (up_sub s) t)) (psubst s u))
      (subst 0 (psubst s u) (psubst (up_sub s) t))"
    by (rule red.beta[OF closed])
  from r show ?case by (simp add: subst0_psubst)
next
  case (elimPoint k h C pms lms as)
  have kpm: "k < length pms" using elimPoint by simp
  have r: "red S
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
          OF elimPoint(1)])
  from r kpm show ?case by (simp add: psubst_elimArgs)
next
  case (elimPath k h C pms lms as j)
  have klm: "k < length lms" using elimPath by simp
  have mreg: "regular S (lms ! k)"
    using elimPath klm by (auto simp: list_all_iff)
  have mdims: "variable_dims (lms ! k)"
    by (rule regular_variable_dims[OF mreg])
  have method:
      "psubst s (dsubst S 0 (DVar j) (lms ! k)) =
        dsubst S 0 (DVar j) (psubst s (lms ! k))"
    by (rule psubst_dsubst_zero[OF mdims elimPath.prems(3)])
  have r: "red S
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
          OF elimPath(1)])
  from r klm method show ?case by (simp add: psubst_elimArgs)
next
  case (appL t t' u)
  then show ?case by (auto intro: red.appL)
next
  case (appR u u' t)
  then show ?case by (auto intro: red.appR)
next
  case (lam t t' A)
  have env': "\<And>i. regular S (up_sub s i)"
    by (rule regular_up_sub[OF lam.prems(2)])
  have fixed': "\<And>i. erased S (up_sub s i)"
    by (rule erased_up_sub[OF lam.prems(3)])
  have regt: "regular S t" using lam.prems(1) by simp
  have "red S (psubst (up_sub s) t) (psubst (up_sub s) t')"
    by (rule lam.hyps(2)[OF regt env' fixed'])
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

lemma red_subst0:
  assumes step: "red S t t'" and regt: "regular S t"
    and regs: "regular S s" and fixeds: "erased S s"
  shows "red S (subst 0 s t) (subst 0 s t')"
proof -
  have env_reg: "\<And>i. regular S (single_sub 0 s i)"
    unfolding single_sub_def
    using regs by (case_tac i; simp)
  have env_fixed: "\<And>i. erased S (single_sub 0 s i)"
  proof -
    fix i
    show "erased S (single_sub 0 s i)"
      using fixeds unfolding single_sub_def erased_def
      by (cases i) simp_all
  qed
  have "red S
      (psubst (single_sub 0 s) t)
      (psubst (single_sub 0 s) t')"
    by (rule red_psubst[OF step regt env_reg env_fixed])
  then show ?thesis by (simp add: subst_as_psubst)
qed

lemma red_LamE:
  assumes "red S (Lam A t) u"
  obtains t' where "u = Lam A t'" and "red S t t'"
  using assms by (cases rule: red.cases) auto

lemma SN_LamI:
  assumes "SN S t"
  shows "SN S (Lam A t)"
  using assms
proof (induct rule: SN.induct)
  case (SNI t)
  show ?case
  proof (rule SN.SNI)
    fix u
    assume "red S (Lam A t) u"
    then obtain t' where u: "u = Lam A t'" and r: "red S t t'"
      by (rule red_LamE)
    have "SN S (Lam A t')" by (rule SNI.hyps(2)[OF r])
    with u show "SN S u" by simp
  qed
qed

lemma KC_beta_app:
  assumes sn: "SN S b" and reg: "regular S b" and fixed: "erased S b"
    and bodies: "\<And>x. KC S n A x \<Longrightarrow>
      KC S n B (subst 0 x b)"
    and arg: "KC S n A a"
  shows "KC S n B (App (Lam A b) a)"
  using sn reg fixed bodies arg
proof (induct arbitrary: a rule: SN.induct)
  case (SNI b)
  note body_IH = SNI.hyps(2)
  have regb: "regular S b" by (rule SNI.prems(1))
  have fixedb: "erased S b" by (rule SNI.prems(2))
  have bodyfun: "\<And>x. KC S n A x \<Longrightarrow>
      KC S n B (subst 0 x b)"
    by (rule SNI.prems(3))
  have arga: "KC S n A a" by (rule SNI.prems(4))
  have sna: "SN S a" by (rule KC_SN[OF arga])
  from sna arga show ?case
  proof (induct rule: SN.induct)
    case (SNI a)
    have xrel: "KC S n A a" by (rule SNI.prems)
    have app_reg: "regular S (App (Lam A b) a)"
      using regb KC_regular[OF xrel] by simp
    have app_fixed: "erased S (App (Lam A b) a)"
      using fixedb KC_erased[OF xrel]
      unfolding erased_def by simp
    show ?case
    proof (rule KC_neutral[OF _ app_reg app_fixed])
      show "neutral (App (Lam A b) a)" by simp
      fix u
      assume step: "red S (App (Lam A b) a) u"
      then show "KC S n B u"
      proof cases
        case beta
        with bodyfun xrel show ?thesis by blast
      next
        case (appL q')
        then obtain b' where q': "q' = Lam A b'" and r: "red S b b'"
          by (auto elim: red_LamE)
        have regb': "regular S b'"
          by (rule regular_red[OF r regb])
        have fixedb': "erased S b'"
          by (rule erased_red[OF r regb fixedb])
        have bodies': "\<And>x. KC S n A x \<Longrightarrow>
            KC S n B (subst 0 x b')"
        proof -
          fix x
          assume x: "KC S n A x"
          have old: "KC S n B (subst 0 x b)"
            by (rule bodyfun[OF x])
          have substep: "red S (subst 0 x b) (subst 0 x b')"
            by (rule red_subst0[
                  OF r regb KC_regular[OF x] KC_erased[OF x]])
          show "KC S n B (subst 0 x b')" by (rule KC_red[OF old substep])
        qed
        have "KC S n B (App (Lam A b') a)"
          by (rule body_IH[OF r regb' fixedb' bodies' xrel])
        with q' appL show ?thesis by simp
      next
        case (appR a')
        have a': "KC S n A a'" by (rule KC_red[OF xrel appR(2)])
        have "KC S n B (App (Lam A b) a')"
          by (rule SNI.hyps(2)[OF appR(2) a'])
        with appR show ?thesis by simp
      qed
    qed
  qed
qed

lemma KC_Lam:
  assumes reg: "regular S b" and fixed: "erased S b" and sn: "SN S b"
    and bodies: "\<And>m f x. Ren n m f \<Longrightarrow> KC S m A x \<Longrightarrow>
      KC S m B (subst 0 x (vrename (up_ren f) b))"
  shows "KC S n (Fun A B) (Lam A b)"
proof -
  have snlam: "SN S (Lam A b)" by (rule SN_LamI[OF sn])
  have fixedlam: "erased S (Lam A b)"
    using fixed unfolding erased_def by simp
  have app: "\<forall>m f x. Ren n m f \<longrightarrow> KC S m A x \<longrightarrow>
      KC S m B (App (vrename f (Lam A b)) x)"
  proof (intro allI impI)
    fix m f x
    assume ren: "Ren n m f" and x: "KC S m A x"
    have regbody: "regular S (vrename (up_ren f) b)" using reg by simp
    have fixedbody: "erased S (vrename (up_ren f) b)"
      by (rule erased_vrename[OF fixed])
    have snbody: "SN S (vrename (up_ren f) b)"
      by (rule SN_vrename[OF sn reg])
    have body: "\<And>y. KC S m A y \<Longrightarrow>
        KC S m B (subst 0 y (vrename (up_ren f) b))"
      by (rule bodies[OF ren])
    have "KC S m B
        (App (Lam A (vrename (up_ren f) b)) x)"
      by (rule KC_beta_app[OF snbody regbody fixedbody body x])
    then show "KC S m B (App (vrename f (Lam A b)) x)" by simp
  qed
  from reg fixedlam snlam app show ?thesis by simp
qed

subsection \<open>Constructor and method arguments\<close>

fun kc_args ::
  "sigenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> argspec list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "kc_args S n h [] [] = True"
| "kc_args S n h [] (a # as) = False"
| "kc_args S n h (s # ss) [] = False"
| "kc_args S n h (s # ss) (a # as) =
    (KC S n (argTy h s) a \<and> kc_args S n h ss as)"

lemma kc_args_length:
  "kc_args S n h ss as \<Longrightarrow> length as = length ss"
  by (induct ss arbitrary: as) (case_tac as; auto)+

lemma kc_args_nth:
  assumes "kc_args S n h ss as" and "i < length as"
  shows "KC S n (argTy h (ss ! i)) (as ! i)"
  using assms
proof (induct ss arbitrary: as i)
  case Nil
  then show ?case by (cases as) auto
next
  case (Cons s ss)
  then obtain a as' where as: "as = a # as'" by (cases as) auto
  show ?case
  proof (cases i)
    case 0
    with Cons.prems as show ?thesis by simp
  next
    case (Suc j)
    have tail: "kc_args S n h ss as'" using Cons.prems as by simp
    have bound: "j < length as'" using Cons.prems as Suc by simp
    have "KC S n (argTy h (ss ! j)) (as' ! j)"
      by (rule Cons.hyps[OF tail bound])
    with as Suc show ?thesis by simp
  qed
qed

lemma kc_argsI:
  assumes "length as = length ss"
    and "\<And>i. i < length as \<Longrightarrow>
      KC S n (argTy h (ss ! i)) (as ! i)"
  shows "kc_args S n h ss as"
  using assms
proof (induct ss arbitrary: as)
  case Nil
  then show ?case by (cases as) auto
next
  case (Cons s ss)
  then obtain a as' where as: "as = a # as'" by (cases as) auto
  have head: "KC S n (argTy h s) a"
    using Cons.prems(2)[of 0] as by simp
  have tail: "kc_args S n h ss as'"
  proof (rule Cons.hyps)
    show "length as' = length ss" using Cons.prems(1) as by simp
    fix i
    assume "i < length as'"
    then have "Suc i < length as" using as by simp
    from Cons.prems(2)[OF this] as
    show "KC S n (argTy h (ss ! i)) (as' ! i)" by simp
  qed
  from head tail as show ?case by simp
qed

lemma kc_args_regular:
  assumes "kc_args S n h ss as"
  shows "list_all (regular S) as"
  using assms
  by (induct ss arbitrary: as)
    (case_tac as; auto dest: KC_regular)+

lemma kc_args_erased:
  assumes "kc_args S n h ss as"
  shows "list_all (erased S) as"
  using assms
  by (induct ss arbitrary: as)
    (case_tac as; auto dest: KC_erased)+

lemma kc_args_hargs:
  assumes "kc_args S n h ss as"
  shows "hargs S h ss as"
  using assms
proof (induct ss arbitrary: as)
  case Nil
  then show ?case by (cases as) auto
next
  case (Cons s ss)
  then obtain a as' where as: "as = a # as'" by (cases as) auto
  have rel: "KC S n (argTy h s) a" using Cons.prems as by simp
  have "hcomp S (argHit h s) a"
    using rel by (cases s) (auto dest: KC_Hit_hcomp)
  with Cons as show ?case by simp
qed

lemma KC_PCon:
  assumes k: "k < length (pcons (S h))"
    and args: "kc_args S n h (pcons (S h) ! k) as"
  shows "KC S n (Hit h) (PCon h k as)"
proof -
  have len: "length as = length (pcons (S h) ! k)"
    by (rule kc_args_length[OF args])
  have reg: "regular S (PCon h k as)"
    using k len kc_args_regular[OF args] by simp
  have fixed: "erased S (PCon h k as)"
    using kc_args_erased[OF args]
    unfolding erased_def
    by (simp add: list_all_iff map_eq_self_iff)
  have comp: "hcomp S h (PCon h k as)"
    by (rule hcomp_PCon[OF k kc_args_hargs[OF args]])
  from reg fixed comp show ?thesis by simp
qed

lemma KC_LCon:
  assumes k: "k < length (lcons (S h))"
    and args: "kc_args S n h (lcons (S h) ! k) as"
  shows "KC S n (Hit h) (LCon h k as (DVar 1))"
proof -
  have len: "length as = length (lcons (S h) ! k)"
    by (rule kc_args_length[OF args])
  have reg: "regular S (LCon h k as (DVar 1))"
    using k len kc_args_regular[OF args] by simp
  have fixed: "erased S (LCon h k as (DVar 1))"
    using kc_args_erased[OF args]
    unfolding erased_def
    by (simp add: list_all_iff map_eq_self_iff)
  have comp: "hcomp S h (LCon h k as (DVar 1))"
    by (rule hcomp_LCon[OF k kc_args_hargs[OF args]])
  from reg fixed comp show ?thesis by simp
qed

fun k_methods ::
  "sigenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow>
    argspec list list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "k_methods S n h C [] [] = True"
| "k_methods S n h C [] (m # ms) = False"
| "k_methods S n h C (ss # css) [] = False"
| "k_methods S n h C (ss # css) (m # ms) =
    (KC S n (methodTy h C ss) m \<and> k_methods S n h C css ms)"

lemma k_methods_length:
  "k_methods S n h C css ms \<Longrightarrow> length ms = length css"
  by (induct css arbitrary: ms) (case_tac ms; auto)+

lemma k_methods_nth:
  assumes "k_methods S n h C css ms" and "i < length ms"
  shows "KC S n (methodTy h C (css ! i)) (ms ! i)"
  using assms
proof (induct css arbitrary: ms i)
  case Nil
  then show ?case by (cases ms) auto
next
  case (Cons ss css)
  then obtain m ms' where ms: "ms = m # ms'" by (cases ms) auto
  show ?case
  proof (cases i)
    case 0
    with Cons.prems ms show ?thesis by simp
  next
    case (Suc j)
    have tail: "k_methods S n h C css ms'" using Cons.prems ms by simp
    have bound: "j < length ms'" using Cons.prems ms Suc by simp
    have "KC S n (methodTy h C (css ! j)) (ms' ! j)"
      by (rule Cons.hyps[OF tail bound])
    with ms Suc show ?thesis by simp
  qed
qed

lemma k_methodsI:
  assumes "length ms = length css"
    and "\<And>i. i < length ms \<Longrightarrow>
      KC S n (methodTy h C (css ! i)) (ms ! i)"
  shows "k_methods S n h C css ms"
  using assms
proof (induct css arbitrary: ms)
  case Nil
  then show ?case by (cases ms) auto
next
  case (Cons ss css)
  then obtain m ms' where ms: "ms = m # ms'" by (cases ms) auto
  have head: "KC S n (methodTy h C ss) m"
    using Cons.prems(2)[of 0] ms by simp
  have tail: "k_methods S n h C css ms'"
  proof (rule Cons.hyps)
    show "length ms' = length css" using Cons.prems(1) ms by simp
    fix i
    assume "i < length ms'"
    then have "Suc i < length ms" using ms by simp
    from Cons.prems(2)[OF this] ms
    show "KC S n (methodTy h C (css ! i)) (ms' ! i)" by simp
  qed
  from head tail ms show ?case by simp
qed

lemma k_methods_regular:
  "k_methods S n h C css ms \<Longrightarrow> list_all (regular S) ms"
  by (induct css arbitrary: ms)
    (case_tac ms; auto dest: KC_regular)+

lemma k_methods_erased:
  "k_methods S n h C css ms \<Longrightarrow> list_all (erased S) ms"
  by (induct css arbitrary: ms)
    (case_tac ms; auto dest: KC_erased)+

lemma k_methods_SN:
  "k_methods S n h C css ms \<Longrightarrow> list_all (SN S) ms"
  by (induct css arbitrary: ms)
    (case_tac ms; auto dest: KC_SN)+

lemma k_methods_list_red:
  assumes "list_red S ms ms'" and "k_methods S n h C css ms"
  shows "k_methods S n h C css ms'"
  using assms
proof (induct arbitrary: css rule: list_red.induct)
  case (lr_head m m' ms)
  then show ?case by (cases css) (auto intro: KC_red)
next
  case (lr_tail ms ms' m)
  then show ?case by (cases css) auto
qed

lemma KC_apps_elimArgs:
  assumes args: "kc_args S n h ss as"
    and method: "KC S n (methodTy h C ss) m"
    and recursive: "\<And>a. KC S n (Hit h) a \<Longrightarrow>
      KC S n C (HElim h C pms lms a)"
  shows "KC S n C (apps m (elimArgs h C pms lms ss as))"
  using args method
proof (induct ss arbitrary: as m)
  case Nil
  then have "as = []" by (cases as) auto
  with Nil show ?case by simp
next
  case (Cons s ss)
  then obtain a as' where as: "as = a # as'" by (cases as) auto
  have tail: "kc_args S n h ss as'" using Cons.prems(1) as by simp
  show ?case
  proof (cases s)
    case (Par h')
    have a: "KC S n (Hit h') a" using Cons.prems(1) as Par by simp
    have m: "KC S n (Fun (Hit h') (methodTy h C ss)) m"
      using Cons.prems(2) Par by simp
    have "KC S n (methodTy h C ss) (App m a)"
      by (rule KC_App[OF m a])
    from Cons.hyps[OF tail this] as Par show ?thesis by simp
  next
    case Rec
    have a: "KC S n (Hit h) a" using Cons.prems(1) as Rec by simp
    have m: "KC S n (Fun (Hit h) (Fun C (methodTy h C ss))) m"
      using Cons.prems(2) Rec by simp
    have first: "KC S n (Fun C (methodTy h C ss)) (App m a)"
      by (rule KC_App[OF m a])
    have ea: "KC S n C (HElim h C pms lms a)"
      by (rule recursive[OF a])
    have "KC S n (methodTy h C ss) (App (App m a) (HElim h C pms lms a))"
      by (rule KC_App[OF first ea])
    from Cons.hyps[OF tail this] as Rec show ?thesis by simp
  qed
qed

lemma KC_apps_elimArgs_indexed:
  assumes args: "kc_args S n h ss as"
    and method: "KC S n (methodTy h C ss) m"
    and recursive: "\<And>i. i < length as \<Longrightarrow> ss ! i = Rec \<Longrightarrow>
      KC S n C (HElim h C pms lms (as ! i))"
  shows "KC S n C (apps m (elimArgs h C pms lms ss as))"
  using args method recursive
proof (induct ss arbitrary: as m)
  case Nil
  then have "as = []" by (cases as) auto
  with Nil show ?case by simp
next
  case (Cons s ss)
  then obtain a as' where as: "as = a # as'" by (cases as) auto
  have tail: "kc_args S n h ss as'" using Cons.prems(1) as by simp
  have rec_tail: "\<And>i. i < length as' \<Longrightarrow> ss ! i = Rec \<Longrightarrow>
      KC S n C (HElim h C pms lms (as' ! i))"
  proof -
    fix i
    assume i: "i < length as'" and rec: "ss ! i = Rec"
    have "Suc i < length as" using i as by simp
    moreover have "(s # ss) ! Suc i = Rec" using rec by simp
    ultimately have "KC S n C
        (HElim h C pms lms (as ! Suc i))"
      by (rule Cons.prems(3))
    with as show "KC S n C (HElim h C pms lms (as' ! i))" by simp
  qed
  show ?case
  proof (cases s)
    case (Par h')
    have a: "KC S n (Hit h') a" using Cons.prems(1) as Par by simp
    have m: "KC S n (Fun (Hit h') (methodTy h C ss)) m"
      using Cons.prems(2) Par by simp
    have "KC S n (methodTy h C ss) (App m a)"
      by (rule KC_App[OF m a])
    from Cons.hyps[OF tail this rec_tail] as Par show ?thesis by simp
  next
    case Rec
    have a: "KC S n (Hit h) a" using Cons.prems(1) as Rec by simp
    have m: "KC S n (Fun (Hit h) (Fun C (methodTy h C ss))) m"
      using Cons.prems(2) Rec by simp
    have ea: "KC S n C (HElim h C pms lms a)"
    proof -
      have "0 < length as" using as by simp
      moreover have "(s # ss) ! 0 = Rec" using Rec by simp
      ultimately have "KC S n C (HElim h C pms lms (as ! 0))"
        by (rule Cons.prems(3))
      with as show ?thesis by simp
    qed
    have first: "KC S n (Fun C (methodTy h C ss)) (App m a)"
      by (rule KC_App[OF m a])
    have "KC S n (methodTy h C ss) (App (App m a) (HElim h C pms lms a))"
      by (rule KC_App[OF first ea])
    from Cons.hyps[OF tail this rec_tail] as Rec show ?thesis by simp
  qed
qed

lemma regular_PCon_arg:
  "regular S (PCon h k as) \<Longrightarrow> i < length as \<Longrightarrow>
    regular S (as ! i)"
  by (auto simp: list_all_iff)

lemma regular_LCon_arg:
  "regular S (LCon h k as d) \<Longrightarrow> i < length as \<Longrightarrow>
    regular S (as ! i)"
  by (auto simp: list_all_iff)

lemma erased_PCon_arg:
  assumes "erased S (PCon h k as)" and "i < length as"
  shows "erased S (as ! i)"
  using assms unfolding erased_def
  by (auto simp: map_eq_self_iff)

lemma erased_LCon_arg:
  assumes "erased S (LCon h k as d)" and "i < length as"
  shows "erased S (as ! i)"
  using assms unfolding erased_def
  by (auto simp: map_eq_self_iff)

lemma regular_HElim:
  assumes "regular S t"
    and "k_methods S n h C (pcons (S h)) pms"
    and "k_methods S n h C (lcons (S h)) lms"
  shows "regular S (HElim h C pms lms t)"
  using assms k_methods_length k_methods_regular by simp

lemma erased_HElim:
  assumes "erased S t"
    and "k_methods S n h C (pcons (S h)) pms"
    and "k_methods S n h C (lcons (S h)) lms"
  shows "erased S (HElim h C pms lms t)"
proof -
  have p: "map (erase_dims S) pms = pms"
    using k_methods_erased[OF assms(2)]
    unfolding erased_def
    by (simp add: list_all_iff map_eq_self_iff)
  have l: "map (erase_dims S) lms = lms"
    using k_methods_erased[OF assms(3)]
    unfolding erased_def
    by (simp add: list_all_iff map_eq_self_iff)
  from assms(1) p l show ?thesis unfolding erased_def by simp
qed

lemma KC_HElim_method_access:
  assumes pms: "k_methods S n h C (pcons (S h)) pms"
    and lms: "k_methods S n h C (lcons (S h)) lms"
    and close: "\<And>pms lms.
      k_methods S n h C (pcons (S h)) pms \<Longrightarrow>
      k_methods S n h C (lcons (S h)) lms \<Longrightarrow>
      (\<And>pms'. list_red S pms pms' \<Longrightarrow>
        KC S n C (HElim h C pms' lms t)) \<Longrightarrow>
      (\<And>lms'. list_red S lms lms' \<Longrightarrow>
        KC S n C (HElim h C pms lms' t)) \<Longrightarrow>
      KC S n C (HElim h C pms lms t)"
  shows "KC S n C (HElim h C pms lms t)"
proof -
  have snp: "SN_list S pms"
    by (rule SN_list_all[OF k_methods_SN[OF pms]])
  have snl: "SN_list S lms"
    by (rule SN_list_all[OF k_methods_SN[OF lms]])
  from snp snl pms lms show ?thesis
  proof (induct rule: SN_lists_induct)
    case (step pms lms)
    show ?case
    proof (rule close[OF step.prems(1,2)])
      fix pms'
      assume lr: "list_red S pms pms'"
      have kp: "k_methods S n h C (pcons (S h)) pms'"
        by (rule k_methods_list_red[OF lr step.prems(1)])
      show "KC S n C (HElim h C pms' lms t)"
        by (rule step.hyps(1)[OF lr kp step.prems(2)])
    next
      fix lms'
      assume lr: "list_red S lms lms'"
      have kl: "k_methods S n h C (lcons (S h)) lms'"
        by (rule k_methods_list_red[OF lr step.prems(2)])
      show "KC S n C (HElim h C pms lms' t)"
        by (rule step.hyps(2)[OF lr step.prems(1) kl])
    qed
  qed
qed

lemma red_HElim_PConE [case_names head pm lm scrut]:
  assumes step: "red S (HElim h C pms lms (PCon h k as)) u"
  obtains
    (head) "k < length (pcons (S h))"
      "u = apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k) as)"
  | (pm) xs m m' ys where
      "pms = xs @ m # ys" "red S m m'"
      "u = HElim h C (xs @ m' # ys) lms (PCon h k as)"
  | (lm) xs m m' ys where
      "lms = xs @ m # ys" "red S m m'"
      "u = HElim h C pms (xs @ m' # ys) (PCon h k as)"
  | (scrut) t' where "red S (PCon h k as) t'"
      "u = HElim h C pms lms t'"
  using step
  by (cases rule: red.cases) (auto intro: head pm lm scrut)

lemma red_HElim_LConE [case_names head pm lm scrut]:
  assumes step: "red S (HElim h C pms lms (LCon h k as (DVar j))) u"
  obtains
    (head) "k < length (lcons (S h))"
      "u = apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as)"
  | (pm) xs m m' ys where
      "pms = xs @ m # ys" "red S m m'"
      "u = HElim h C (xs @ m' # ys) lms (LCon h k as (DVar j))"
  | (lm) xs m m' ys where
      "lms = xs @ m # ys" "red S m m'"
      "u = HElim h C pms (xs @ m' # ys) (LCon h k as (DVar j))"
  | (scrut) t' where "red S (LCon h k as (DVar j)) t'"
      "u = HElim h C pms lms t'"
  using step
  by (cases rule: red.cases) (auto intro: head pm lm scrut)

lemma KC_HElim_aux:
    assumes comp: "hcomp S h t" and reg: "regular S t" and fixed: "erased S t"
      and pms: "k_methods S n h C (pcons (S h)) pms"
      and lms: "k_methods S n h C (lcons (S h)) lms"
    shows "KC S n C (HElim h C pms lms t)"
    using comp reg fixed pms lms
  proof (induct arbitrary: n C pms lms rule: hcomp.induct)
    case (hneutral t h)
    show ?case
    proof (rule KC_HElim_method_access[
          OF hneutral.prems(3,4)])
      fix pms lms
      assume kp: "k_methods S n h C (pcons (S h)) pms"
        and kl: "k_methods S n h C (lcons (S h)) lms"
        and pstep: "\<And>pms'. list_red S pms pms' \<Longrightarrow>
          KC S n C (HElim h C pms' lms t)"
        and lstep: "\<And>lms'. list_red S lms lms' \<Longrightarrow>
          KC S n C (HElim h C pms lms' t)"
      have rh: "regular S (HElim h C pms lms t)"
        by (rule regular_HElim[OF hneutral.prems(1) kp kl])
      have eh: "erased S (HElim h C pms lms t)"
        by (rule erased_HElim[OF hneutral.prems(2) kp kl])
      show "KC S n C (HElim h C pms lms t)"
      proof (rule KC_neutral[OF _ rh eh])
        show "neutral (HElim h C pms lms t)" by simp
        fix u
        assume red: "red S (HElim h C pms lms t) u"
        then show "KC S n C u"
        proof cases
          case elimPoint
          with hneutral.hyps(1) show ?thesis by simp
        next
          case elimPath
          with hneutral.hyps(1) show ?thesis by simp
        next
          case elimPm
          from pstep elimPm list_red_append show ?thesis by metis
        next
          case elimLm
          from lstep elimLm list_red_append show ?thesis by metis
        next
          case (elimScrutinee t')
          have rt: "regular S t'"
            by (rule regular_red[OF elimScrutinee(2) hneutral.prems(1)])
          have et: "erased S t'"
            by (rule erased_red[
                  OF elimScrutinee(2) hneutral.prems(1,2)])
          have "KC S n C (HElim h C pms lms t')"
            by (rule hneutral.hyps(3)[
                  OF elimScrutinee(2) rt et kp kl])
          with elimScrutinee show ?thesis by simp
        qed
      qed
    qed
  next
    case (hpcon k h as)
    have args: "kc_args S n h (pcons (S h) ! k) as"
    proof (rule kc_argsI[OF hpcon.hyps(2)])
      fix i
      assume i: "i < length as"
      have ri: "regular S (as ! i)"
        by (rule regular_PCon_arg[OF hpcon.prems(1) i])
      have ei: "erased S (as ! i)"
        by (rule erased_PCon_arg[OF hpcon.prems(2) i])
      have hi: "hcomp S (argHit h (pcons (S h) ! k ! i)) (as ! i)"
        by (rule hpcon.hyps(3)[OF i])
      from ri ei hi show
        "KC S n (argTy h (pcons (S h) ! k ! i)) (as ! i)"
        by (cases "pcons (S h) ! k ! i") simp_all
    qed
    show ?case
    proof (rule KC_HElim_method_access[
          OF hpcon.prems(3,4)])
      fix pms lms
      assume kp: "k_methods S n h C (pcons (S h)) pms"
        and kl: "k_methods S n h C (lcons (S h)) lms"
        and pstep: "\<And>pms'. list_red S pms pms' \<Longrightarrow>
          KC S n C (HElim h C pms' lms (PCon h k as))"
        and lstep: "\<And>lms'. list_red S lms lms' \<Longrightarrow>
          KC S n C (HElim h C pms lms' (PCon h k as))"
      have rh: "regular S (HElim h C pms lms (PCon h k as))"
        by (rule regular_HElim[OF hpcon.prems(1) kp kl])
      have eh: "erased S (HElim h C pms lms (PCon h k as))"
        by (rule erased_HElim[OF hpcon.prems(2) kp kl])
      show "KC S n C (HElim h C pms lms (PCon h k as))"
      proof (rule KC_neutral[OF _ rh eh])
        show "neutral (HElim h C pms lms (PCon h k as))" by simp
        fix u
        assume red: "red S (HElim h C pms lms (PCon h k as)) u"
        show "KC S n C u"
        proof (rule red_HElim_PConE[OF red])
          assume head_guard: "k < length (pcons (S h))"
            and head_eq: "u = apps (pms ! k)
              (elimArgs h C pms lms (pcons (S h) ! k) as)"
          have kpm: "k < length pms"
            using hpcon.hyps(1) k_methods_length[OF kp] by simp
          have method: "KC S n (methodTy h C (pcons (S h) ! k)) (pms ! k)"
            by (rule k_methods_nth[OF kp kpm])
          have recursive: "\<And>i. i < length as \<Longrightarrow>
              pcons (S h) ! k ! i = Rec \<Longrightarrow>
              KC S n C (HElim h C pms lms (as ! i))"
          proof -
            fix i
            assume i: "i < length as"
              and rec: "pcons (S h) ! k ! i = Rec"
            have ri: "regular S (as ! i)"
              by (rule regular_PCon_arg[OF hpcon.prems(1) i])
            have ei: "erased S (as ! i)"
              by (rule erased_PCon_arg[OF hpcon.prems(2) i])
            from hpcon.hyps(4)[OF i, of n C pms lms] ri ei kp kl rec
            show "KC S n C (HElim h C pms lms (as ! i))" by simp
          qed
          have head: "KC S n C
              (apps (pms ! k)
                (elimArgs h C pms lms (pcons (S h) ! k) as))"
            by (rule KC_apps_elimArgs_indexed[
                  OF args method recursive])
          with head_eq show ?thesis by simp
        next
          fix xs m m' ys
          assume pms_eq: "pms = xs @ m # ys" and mred: "red S m m'"
            and u_eq: "u =
              HElim h C (xs @ m' # ys) lms (PCon h k as)"
          have lr: "list_red S pms (xs @ m' # ys)"
            using pms_eq mred by (auto intro: list_red_append)
          have "KC S n C
              (HElim h C (xs @ m' # ys) lms (PCon h k as))"
            by (rule pstep[OF lr])
          with u_eq show ?thesis by simp
        next
          fix xs m m' ys
          assume lms_eq: "lms = xs @ m # ys" and mred: "red S m m'"
            and u_eq: "u =
              HElim h C pms (xs @ m' # ys) (PCon h k as)"
          have lr: "list_red S lms (xs @ m' # ys)"
            using lms_eq mred by (auto intro: list_red_append)
          have "KC S n C
              (HElim h C pms (xs @ m' # ys) (PCon h k as))"
            by (rule lstep[OF lr])
          with u_eq show ?thesis by simp
        next
          fix t'
          assume tred: "red S (PCon h k as) t'"
            and u_eq: "u = HElim h C pms lms t'"
          have rt: "regular S t'"
            by (rule regular_red[OF tred hpcon.prems(1)])
          have et: "erased S t'"
            by (rule erased_red[
                  OF tred hpcon.prems(1,2)])
          have "KC S n C (HElim h C pms lms t')"
            by (rule hpcon.hyps(6)[
                  OF tred rt et kp kl])
          with u_eq show ?thesis by simp
        qed
      qed
    qed
  next
    case (hlcon k h as j)
    have args: "kc_args S n h (lcons (S h) ! k) as"
    proof (rule kc_argsI[OF hlcon.hyps(2)])
      fix i
      assume i: "i < length as"
      have ri: "regular S (as ! i)"
        by (rule regular_LCon_arg[OF hlcon.prems(1) i])
      have ei: "erased S (as ! i)"
        by (rule erased_LCon_arg[OF hlcon.prems(2) i])
      have hi: "hcomp S (argHit h (lcons (S h) ! k ! i)) (as ! i)"
        by (rule hlcon.hyps(3)[OF i])
      from ri ei hi show
        "KC S n (argTy h (lcons (S h) ! k ! i)) (as ! i)"
        by (cases "lcons (S h) ! k ! i") simp_all
    qed
    show ?case
    proof (rule KC_HElim_method_access[
          OF hlcon.prems(3,4)])
      fix pms lms
      assume kp: "k_methods S n h C (pcons (S h)) pms"
        and kl: "k_methods S n h C (lcons (S h)) lms"
        and pstep: "\<And>pms'. list_red S pms pms' \<Longrightarrow>
          KC S n C (HElim h C pms' lms (LCon h k as (DVar j)))"
        and lstep: "\<And>lms'. list_red S lms lms' \<Longrightarrow>
          KC S n C (HElim h C pms lms' (LCon h k as (DVar j)))"
      have rh: "regular S (HElim h C pms lms (LCon h k as (DVar j)))"
        by (rule regular_HElim[OF hlcon.prems(1) kp kl])
      have eh: "erased S (HElim h C pms lms (LCon h k as (DVar j)))"
        by (rule erased_HElim[OF hlcon.prems(2) kp kl])
      show "KC S n C (HElim h C pms lms (LCon h k as (DVar j)))"
      proof (rule KC_neutral[OF _ rh eh])
        show "neutral (HElim h C pms lms (LCon h k as (DVar j)))" by simp
        fix u
        assume red: "red S (HElim h C pms lms (LCon h k as (DVar j))) u"
        show "KC S n C u"
        proof (rule red_HElim_LConE[OF red])
          assume head_guard: "k < length (lcons (S h))"
            and head_eq: "u =
              apps (dsubst S 0 (DVar j) (lms ! k))
                (elimArgs h C pms lms (lcons (S h) ! k) as)"
          have klm: "k < length lms"
            using hlcon.hyps(1) k_methods_length[OF kl] by simp
          have method: "KC S n (methodTy h C (lcons (S h) ! k)) (lms ! k)"
            by (rule k_methods_nth[OF kl klm])
          have same: "dsubst S 0 (DVar j) (lms ! k) = lms ! k"
            by (rule erased_dsubst_zero[OF KC_erased[OF method]])
          have recursive: "\<And>i. i < length as \<Longrightarrow>
              lcons (S h) ! k ! i = Rec \<Longrightarrow>
              KC S n C (HElim h C pms lms (as ! i))"
          proof -
            fix i
            assume i: "i < length as"
              and rec: "lcons (S h) ! k ! i = Rec"
            have ri: "regular S (as ! i)"
              by (rule regular_LCon_arg[OF hlcon.prems(1) i])
            have ei: "erased S (as ! i)"
              by (rule erased_LCon_arg[OF hlcon.prems(2) i])
            from hlcon.hyps(4)[OF i, of n C pms lms] ri ei kp kl rec
            show "KC S n C (HElim h C pms lms (as ! i))" by simp
          qed
          have head: "KC S n C
              (apps (lms ! k)
                (elimArgs h C pms lms (lcons (S h) ! k) as))"
            by (rule KC_apps_elimArgs_indexed[
                  OF args method recursive])
          with head_eq same show ?thesis by simp
        next
          fix xs m m' ys
          assume pms_eq: "pms = xs @ m # ys" and mred: "red S m m'"
            and u_eq: "u =
              HElim h C (xs @ m' # ys) lms (LCon h k as (DVar j))"
          have lr: "list_red S pms (xs @ m' # ys)"
            using pms_eq mred by (auto intro: list_red_append)
          have "KC S n C
              (HElim h C (xs @ m' # ys) lms (LCon h k as (DVar j)))"
            by (rule pstep[OF lr])
          with u_eq show ?thesis by simp
        next
          fix xs m m' ys
          assume lms_eq: "lms = xs @ m # ys" and mred: "red S m m'"
            and u_eq: "u =
              HElim h C pms (xs @ m' # ys) (LCon h k as (DVar j))"
          have lr: "list_red S lms (xs @ m' # ys)"
            using lms_eq mred by (auto intro: list_red_append)
          have "KC S n C
              (HElim h C pms (xs @ m' # ys) (LCon h k as (DVar j)))"
            by (rule lstep[OF lr])
          with u_eq show ?thesis by simp
        next
          fix t'
          assume tred: "red S (LCon h k as (DVar j)) t'"
            and u_eq: "u = HElim h C pms lms t'"
          have rt: "regular S t'"
            by (rule regular_red[OF tred hlcon.prems(1)])
          have et: "erased S t'"
            by (rule erased_red[
                  OF tred hlcon.prems(1,2)])
          have "KC S n C (HElim h C pms lms t')"
            by (rule hlcon.hyps(6)[
                  OF tred rt et kp kl])
          with u_eq show ?thesis by simp
        qed
      qed
    qed
  qed

lemma KC_HElim:
  assumes "KC S n (Hit h) t"
    and "k_methods S n h C (pcons (S h)) pms"
    and "k_methods S n h C (lcons (S h)) lms"
  shows "KC S n C (HElim h C pms lms t)"
  by (rule KC_HElim_aux[
        OF KC_Hit_hcomp[OF assms(1)] KC_regular[OF assms(1)]
          KC_erased[OF assms(1)] assms(2,3)])

subsection \<open>The fundamental theorem\<close>

definition k_env ::
  "sigenv \<Rightarrow> nat \<Rightarrow> ty list \<Rightarrow> (nat \<Rightarrow> tm) \<Rightarrow> bool"
where
  "k_env S n G s \<longleftrightarrow>
    (\<forall>i < length G. KC S n (G ! i) (s i))"

lemma k_env_up:
  assumes "k_env S n G s"
  shows "k_env S (Suc n) (A # G) (up_sub s)"
  unfolding k_env_def
proof (intro allI impI)
  fix i
  assume i: "i < length (A # G)"
  show "KC S (Suc n) ((A # G) ! i) (up_sub s i)"
  proof (cases i)
    case 0
    then show ?thesis by (simp add: KC_Var)
  next
    case (Suc j)
    from assms i Suc have rel: "KC S n (G ! j) (s j)"
      unfolding k_env_def by simp
    have "KC S (Suc n) (G ! j) (vrename Suc (s j))"
      by (rule KC_vrename[OF rel Ren_Suc])
    with Suc show ?thesis by (simp add: lift_zero_as_vrename)
  qed
qed

lemma k_env_vrename:
  assumes env: "k_env S n G s" and ren: "Ren n m f"
  shows "k_env S m G (\<lambda>i. vrename f (s i))"
  using env unfolding k_env_def
  by (auto intro: KC_vrename[OF _ ren])

lemma k_env_ext:
  assumes env: "k_env S n G s" and x: "KC S n A x"
  shows "k_env S n (A # G) (ext_sub x s)"
  using env x unfolding k_env_def ext_sub_def
  by (intro allI impI) (case_tac i; auto)

theorem fundamental_erased:
  assumes deriv: "wt S D G t A" and env: "k_env S n G s"
  shows "KC S n A (psubst s (erase_dims S t))"
  using deriv env
proof (induct arbitrary: n s rule: wt.induct)
  case (wtVar i G D)
  then show ?case unfolding k_env_def by simp
next
  case (wtLam D A G t B)
  have up: "k_env S (Suc n) (A # G) (up_sub s)"
    by (rule k_env_up[OF wtLam.prems])
  have body: "KC S (Suc n) B
      (psubst (up_sub s) (erase_dims S t))"
    by (rule wtLam.hyps(2)[OF up])
  let ?b = "psubst (up_sub s) (erase_dims S t)"
  have reg: "regular S ?b" by (rule KC_regular[OF body])
  have fixed: "erased S ?b" by (rule KC_erased[OF body])
  have sn: "SN S ?b" by (rule KC_SN[OF body])
  have bodies: "\<And>m f x. Ren n m f \<Longrightarrow> KC S m A x \<Longrightarrow>
      KC S m B (subst 0 x (vrename (up_ren f) ?b))"
  proof -
    fix m f x
    assume ren: "Ren n m f" and x: "KC S m A x"
    have renamed: "k_env S m G (\<lambda>i. vrename f (s i))"
      by (rule k_env_vrename[OF wtLam.prems ren])
    have extended:
        "k_env S m (A # G)
          (ext_sub x (\<lambda>i. vrename f (s i)))"
      by (rule k_env_ext[OF renamed x])
    have ih: "KC S m B
        (psubst (ext_sub x (\<lambda>i. vrename f (s i)))
          (erase_dims S t))"
      by (rule wtLam.hyps(2)[OF extended])
    have eq: "subst 0 x (vrename (up_ren f) ?b) =
        psubst (ext_sub x (\<lambda>i. vrename f (s i)))
          (erase_dims S t)"
    proof -
      have renamed_body:
          "vrename (up_ren f) ?b =
            psubst (up_sub (\<lambda>i. vrename f (s i)))
              (erase_dims S t)"
        by (simp add: vrename_psubst up_sub_vrename)
      show ?thesis
        by (simp add: renamed_body subst0_psubst_up)
    qed
    from ih eq show
      "KC S m B (subst 0 x (vrename (up_ren f) ?b))"
      by simp
  qed
  have "KC S n (Fun A B) (Lam A ?b)"
    by (rule KC_Lam[OF reg fixed sn bodies])
  then show ?case by simp
next
  case (wtApp D G t A B u)
  have fnrel: "KC S n (Fun A B) (psubst s (erase_dims S t))"
    by (rule wtApp.hyps(2)[OF wtApp.prems])
  have arg: "KC S n A (psubst s (erase_dims S u))"
    by (rule wtApp.hyps(4)[OF wtApp.prems])
  from KC_App[OF fnrel arg] show ?case by simp
next
  case (wtPCon k h as D G)
  have args: "kc_args S n h (pcons (S h) ! k)
      (map (psubst s \<circ> erase_dims S) as)"
  proof (rule kc_argsI)
    show "length (map (psubst s \<circ> erase_dims S) as) =
        length (pcons (S h) ! k)"
      using wtPCon.hyps(2) by simp
    fix i
    assume i: "i < length (map (psubst s \<circ> erase_dims S) as)"
    have ia: "i < length as" using i by simp
    have ih: "\<forall>x env.
        k_env S x G env \<longrightarrow>
        KC S x (argTy h (pcons (S h) ! k ! i))
          (psubst env (erase_dims S (as ! i)))"
      using wtPCon.hyps(3)[rule_format, OF ia] by blast
    have "KC S n (argTy h (pcons (S h) ! k ! i))
        (psubst s (erase_dims S (as ! i)))"
      using ih wtPCon.prems by blast
    with i show "KC S n (argTy h (pcons (S h) ! k ! i))
        ((map (psubst s \<circ> erase_dims S) as) ! i)"
      by simp
  qed
  have "KC S n (Hit h)
      (PCon h k (map (psubst s \<circ> erase_dims S) as))"
    by (rule KC_PCon[OF wtPCon.hyps(1) args])
  then show ?case by simp
next
  case (wtLCon j D k h as G)
  have args: "kc_args S n h (lcons (S h) ! k)
      (map (psubst s \<circ> erase_dims S) as)"
  proof (rule kc_argsI)
    show "length (map (psubst s \<circ> erase_dims S) as) =
        length (lcons (S h) ! k)"
      using wtLCon.hyps(3) by simp
    fix i
    assume i: "i < length (map (psubst s \<circ> erase_dims S) as)"
    have ia: "i < length as" using i by simp
    have ih: "\<forall>x env.
        k_env S x G env \<longrightarrow>
        KC S x (argTy h (lcons (S h) ! k ! i))
          (psubst env (erase_dims S (as ! i)))"
      using wtLCon.hyps(4)[rule_format, OF ia] by blast
    have "KC S n (argTy h (lcons (S h) ! k ! i))
        (psubst s (erase_dims S (as ! i)))"
      using ih wtLCon.prems by blast
    with i show "KC S n (argTy h (lcons (S h) ! k ! i))
        ((map (psubst s \<circ> erase_dims S) as) ! i)"
      by simp
  qed
  have "KC S n (Hit h)
      (LCon h k (map (psubst s \<circ> erase_dims S) as) (DVar 1))"
    by (rule KC_LCon[OF wtLCon.hyps(2) args])
  then show ?case by simp
next
  case (wtElim D G t h pms lms C)
  have scrut: "KC S n (Hit h) (psubst s (erase_dims S t))"
    by (rule wtElim.hyps(2)[OF wtElim.prems])
  have pmethods: "k_methods S n h C (pcons (S h))
      (map (psubst s \<circ> erase_dims S) pms)"
  proof (rule k_methodsI)
    show "length (map (psubst s \<circ> erase_dims S) pms) =
        length (pcons (S h))"
      using wtElim.hyps(3) by simp
    fix i
    assume i: "i < length (map (psubst s \<circ> erase_dims S) pms)"
    have ip: "i < length pms" using i by simp
    have ih: "\<forall>x env.
        k_env S x G env \<longrightarrow>
        KC S x (methodTy h C (pcons (S h) ! i))
          (psubst env (erase_dims S (pms ! i)))"
      using wtElim.hyps(5)[rule_format, OF ip] by blast
    have "KC S n (methodTy h C (pcons (S h) ! i))
        (psubst s (erase_dims S (pms ! i)))"
      using ih wtElim.prems by blast
    with i show "KC S n (methodTy h C (pcons (S h) ! i))
        ((map (psubst s \<circ> erase_dims S) pms) ! i)"
      by simp
  qed
  have lmethods: "k_methods S n h C (lcons (S h))
      (map (psubst s \<circ> erase_dims S) lms)"
  proof (rule k_methodsI)
    show "length (map (psubst s \<circ> erase_dims S) lms) =
        length (lcons (S h))"
      using wtElim.hyps(4) by simp
    fix i
    assume i: "i < length (map (psubst s \<circ> erase_dims S) lms)"
    have il: "i < length lms" using i by simp
    have ih: "\<forall>x env.
        k_env S x G env \<longrightarrow>
        KC S x (methodTy h C (lcons (S h) ! i))
          (psubst env (erase_dims S (lms ! i)))"
      using wtElim.hyps(6)[rule_format, OF il] by blast
    have "KC S n (methodTy h C (lcons (S h) ! i))
        (psubst s (erase_dims S (lms ! i)))"
      using ih wtElim.prems by blast
    with i show "KC S n (methodTy h C (lcons (S h) ! i))
        ((map (psubst s \<circ> erase_dims S) lms) ! i)"
      by simp
  qed
  have "KC S n C
      (HElim h C (map (psubst s \<circ> erase_dims S) pms)
        (map (psubst s \<circ> erase_dims S) lms)
        (psubst s (erase_dims S t)))"
    by (rule KC_HElim[OF scrut pmethods lmethods])
  then show ?case by simp
qed

lemma k_env_Var: "k_env S (length G) G Var"
  unfolding k_env_def by (auto intro: KC_Var)

lemma SN_erase_dims_reflect_regular_aux:
  assumes sn: "SN S e"
  shows "\<And>t. e = erase_dims S t \<Longrightarrow> regular S t \<Longrightarrow> SN S t"
  using sn
proof (induct rule: SN.induct)
  case (SNI e)
  show ?case
  proof (rule SN.SNI)
    fix u
    assume step: "red S t u"
    have erased_step: "red S e (erase_dims S u)"
      using red_erase_dims[OF step SNI.prems(2)] SNI.prems(1) by simp
    have regu: "regular S u"
      by (rule regular_red[OF step SNI.prems(2)])
    show "SN S u"
      by (rule SNI.hyps(2)[OF erased_step refl regu])
  qed
qed

lemma SN_erase_dims_reflect_regular:
  assumes "regular S t" and "SN S (erase_dims S t)"
  shows "SN S t"
  by (rule SN_erase_dims_reflect_regular_aux[OF assms(2) refl assms(1)])

theorem wt_strong_normalization:
  assumes typed: "wt S D G t A"
  shows "SN S t"
proof -
  have rel: "KC S (length G) A (erase_dims S t)"
    using fundamental_erased[OF typed k_env_Var] by simp
  have erased_sn: "SN S (erase_dims S t)" by (rule KC_SN[OF rel])
  show ?thesis
    by (rule SN_erase_dims_reflect_regular[
          OF regular_wt[OF typed] erased_sn])
qed

theorem cwt_strong_normalization:
  assumes "wf_sigenv S" and "cwt S D G t A"
  shows "SN S t"
  by (rule wt_strong_normalization[OF cwt_wt[OF assms(2)]])

corollary strong_normalization:
  assumes "wf_sigenv S" and "cwt S D G t A"
  shows "SN S t"
  by (rule cwt_strong_normalization[OF assms])

theorem SN_reaches_normal_form:
  assumes "SN S t"
  shows "\<exists>u. reds S t u \<and> nform S u"
  using assms
proof (induct rule: SN.induct)
  case (SNI t)
  show ?case
  proof (cases "nform S t")
    case True
    then show ?thesis by blast
  next
    case False
    then obtain u where step: "red S t u"
      unfolding nform_def by blast
    from SNI.hyps(2)[OF step] obtain v where
      uv: "reds S u v" and normal: "nform S v"
      by blast
    have tu: "reds S t u" using step by (rule r_into_rtranclp)
    have "reds S t v" by (rule rtranclp_trans[OF tu uv])
    with normal show ?thesis by blast
  qed
qed

corollary SN_normalizes:
  assumes "SN S t"
  shows "normalizes S t"
  using SN_reaches_normal_form[OF assms]
  unfolding normalizes_def by blast

corollary wt_reaches_normal_form:
  assumes "wt S D G t A"
  shows "\<exists>u. reds S t u \<and> nform S u"
  by (rule SN_reaches_normal_form[OF wt_strong_normalization[OF assms]])

corollary cwt_reaches_normal_form:
  assumes "wf_sigenv S" and "cwt S D G t A"
  shows "\<exists>u. reds S t u \<and> nform S u"
  by (rule SN_reaches_normal_form[
        OF cwt_strong_normalization[OF assms]])

corollary cwt_normalizes:
  assumes "wf_sigenv S" and "cwt S D G t A"
  shows "normalizes S t"
  by (rule SN_normalizes[OF cwt_strong_normalization[OF assms]])

section \<open>Unconditional canonical results and consistency\<close>

theorem checked_term_has_canonical_normal_form:
  assumes wf: "wf_sigenv S" and typed: "cwt S {} [] t A"
  shows "\<exists>u. reds S t u \<and> nform S u \<and> canonAt S A u"
proof -
  from cwt_reaches_normal_form[OF wf typed]
  obtain u where reduces: "reds S t u" and normal: "nform S u"
    by blast
  have target: "cwt S {} [] u A"
    by (rule checked_source_subject_reduction_steps[OF wf typed reduces])
  have "canonAt S A u" by (rule canonical_forms[OF target normal])
  with reduces normal show ?thesis by blast
qed

corollary checked_hit_has_canonical_normal_form:
  assumes wf: "wf_sigenv S" and typed: "cwt S {} [] t (Hit h)"
  shows "\<exists>u. reds S t u \<and> nform S u \<and> canonical S h u"
  using checked_term_has_canonical_normal_form[OF wf typed] by auto

corollary empty_signature_consistency:
  assumes wf: "wf_sigenv S" and empty: "pcons (S h) = []"
  shows "\<not> (\<exists>t. cwt S {} [] t (Hit h))"
proof
  assume "\<exists>t. cwt S {} [] t (Hit h)"
  then obtain t where typed: "cwt S {} [] t (Hit h)" by blast
  from checked_hit_has_canonical_normal_form[OF wf typed]
  obtain u where "canonical S h u" by blast
  with no_canonical_without_constructors[
      where S = S and h = h and t = u, OF empty]
  show False by blast
qed

end
