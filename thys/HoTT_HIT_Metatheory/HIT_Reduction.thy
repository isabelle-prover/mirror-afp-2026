theory HIT_Reduction
  imports HIT_Syntax
begin

section \<open>Reduction and conversion\<close>

text \<open>
  There are exactly two computation rules: the usual \<open>\<beta>\<close>-rule, and the rule
  that an eliminator applied to a constructor hands the arguments to the
  corresponding method.  The second rule has two instances, one for point
  constructors and one for path constructors.  The instance for path
  constructors is the cubical-style computation rule: the method is a term with a
  free dimension variable, namely the reserved index \<open>0\<close>, and the reduct first
  instantiates that variable with the dimension of the path constructor and only
  then applies the constructor and recursive arguments.  This order is
  significant under nested eliminators: the bound dimension of a method must not
  capture a dimension occurring freely in an argument supplied to that method.
  There is no boundary rule: applying a path constructor at a constant dimension
  is, by the definition of \<^const>\<open>mkL\<close>, already the corresponding endpoint.
\<close>

definition dclosed0 :: "sigenv \<Rightarrow> tm \<Rightarrow> bool" where
  "dclosed0 S t \<longleftrightarrow> (\<forall>j. dsubst S 0 (DVar j) t = t)"

lemma dclosed0_list_iff:
  "(\<forall>j. map (dsubst S 0 (DVar j)) xs = xs) \<longleftrightarrow>
    list_all (dclosed0 S) xs"
  by (induct xs) (auto simp: dclosed0_def)

lemma dclosed0_Var [simp]: "dclosed0 S (Var i)"
  unfolding dclosed0_def by simp

lemma dclosed0_Lam [simp]:
  "dclosed0 S (Lam A t) \<longleftrightarrow> dclosed0 S t"
  unfolding dclosed0_def by simp

lemma dclosed0_App [simp]:
  "dclosed0 S (App t u) \<longleftrightarrow>
    dclosed0 S t \<and> dclosed0 S u"
  unfolding dclosed0_def by auto

lemma dclosed0_PCon [simp]:
  "dclosed0 S (PCon h k as) \<longleftrightarrow>
    list_all (dclosed0 S) as"
  unfolding dclosed0_def
  by (induct as) auto

lemma dclosed0_LCon [simp]:
  "dclosed0 S (LCon h k as (DVar i)) \<longleftrightarrow>
    i \<noteq> 0 \<and> list_all (dclosed0 S) as"
proof (cases i)
  case 0
  then show ?thesis
    unfolding dclosed0_def by auto
next
  case (Suc i)
  then show ?thesis
    unfolding dclosed0_def
    by (induct as) auto
qed

lemma dclosed0_HElim [simp]:
  "dclosed0 S (HElim h C pms lms t) \<longleftrightarrow>
    list_all (dclosed0 S) pms \<and> dclosed0 S t"
  unfolding dclosed0_def
  by (induct pms) auto

inductive red :: "sigenv \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> bool" for S :: sigenv where
  beta:
    "dclosed0 S u \<Longrightarrow>
      red S (App (Lam A t) u) (subst 0 u t)"
| elimPoint:
    "k < length (pcons (S h)) \<Longrightarrow>
      red S (HElim h C pms lms (PCon h k as))
        (apps (pms ! k) (elimArgs h C pms lms (pcons (S h) ! k) as))"
| elimPath:
    "k < length (lcons (S h)) \<Longrightarrow>
      red S (HElim h C pms lms (LCon h k as (DVar j)))
        (apps (dsubst S 0 (DVar j) (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as))"
| appL: "red S t t' \<Longrightarrow> red S (App t u) (App t' u)"
| appR: "red S u u' \<Longrightarrow> red S (App t u) (App t u')"
| lam: "red S t t' \<Longrightarrow> red S (Lam A t) (Lam A t')"
| pconArg:
    "red S a a' \<Longrightarrow>
      red S (PCon h k (xs @ a # ys)) (PCon h k (xs @ a' # ys))"
| lconArg:
    "red S a a' \<Longrightarrow>
      red S (LCon h k (xs @ a # ys) d) (LCon h k (xs @ a' # ys) d)"
| elimPm:
    "red S m m' \<Longrightarrow>
      red S (HElim h C (xs @ m # ys) lms t)
        (HElim h C (xs @ m' # ys) lms t)"
| elimLm:
    "red S m m' \<Longrightarrow>
      red S (HElim h C pms (xs @ m # ys) t)
        (HElim h C pms (xs @ m' # ys) t)"
| elimScrutinee:
    "red S t t' \<Longrightarrow>
      red S (HElim h C pms lms t) (HElim h C pms lms t')"

abbreviation reds :: "sigenv \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> bool" where
  "reds S \<equiv> (red S)\<^sup>*\<^sup>*"

definition conv :: "sigenv \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> bool" where
  "conv S = (\<lambda>t u. (\<lambda>a b. red S a b \<or> red S b a)\<^sup>*\<^sup>* t u)"

lemma conv_refl: "conv S t t"
  by (simp add: conv_def)

lemma conv_sym:
  assumes "conv S t u"
  shows "conv S u t"
proof -
  have "symp (\<lambda>a b. red S a b \<or> red S b a)"
    by (simp add: symp_def)
  then have "symp ((\<lambda>a b. red S a b \<or> red S b a)\<^sup>*\<^sup>*)"
    by (rule symp_rtranclp)
  with assms show ?thesis
    unfolding conv_def by (simp add: symp_def)
qed

lemma conv_trans:
  "conv S t u \<Longrightarrow> conv S u v \<Longrightarrow> conv S t v"
  unfolding conv_def by (rule rtranclp_trans)

lemma red_conv: "red S t u \<Longrightarrow> conv S t u"
  unfolding conv_def by auto

lemma reds_conv: "reds S t u \<Longrightarrow> conv S t u"
proof (induct rule: rtranclp_induct)
  case base
  show ?case by (rule conv_refl)
next
  case (step y z)
  from step(3) red_conv[OF step(2)] show ?case by (rule conv_trans)
qed

definition joinable :: "sigenv \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> bool" where
  "joinable S t u \<longleftrightarrow> (\<exists>v. reds S t v \<and> reds S u v)"

lemma joinable_refl [simp]: "joinable S t t"
  unfolding joinable_def by auto

lemma joinable_sym:
  "joinable S t u \<Longrightarrow> joinable S u t"
  unfolding joinable_def by blast

lemma joinableI:
  "reds S t v \<Longrightarrow> reds S u v \<Longrightarrow> joinable S t u"
  unfolding joinable_def by blast

lemma joinable_conv:
  assumes "joinable S t u"
  shows "conv S t u"
proof -
  from assms obtain v where tv: "reds S t v" and uv: "reds S u v"
    unfolding joinable_def by blast
  show ?thesis
    by (rule conv_trans[OF reds_conv[OF tv] conv_sym[OF reds_conv[OF uv]]])
qed

subsection \<open>Normal forms and the strong-normalization predicate\<close>

definition nform :: "sigenv \<Rightarrow> tm \<Rightarrow> bool" where
  "nform S t \<longleftrightarrow> (\<nexists>u. red S t u)"

inductive SN :: "sigenv \<Rightarrow> tm \<Rightarrow> bool" for S :: sigenv where
  SNI: "(\<And>u. red S t u \<Longrightarrow> SN S u) \<Longrightarrow> SN S t"

lemma SN_step: "SN S t \<Longrightarrow> red S t u \<Longrightarrow> SN S u"
  by (induct rule: SN.induct) blast

lemma SN_reds: "reds S t u \<Longrightarrow> SN S t \<Longrightarrow> SN S u"
  by (induct rule: rtranclp_induct) (auto intro: SN_step)

lemma SN_nform: "nform S t \<Longrightarrow> SN S t"
  unfolding nform_def by (rule SNI) blast

text \<open>
  The strong-normalization predicate passes from a one-hole context to the term filling it,
  provided the context is monotone for reduction.
\<close>

lemma SN_context:
  assumes mono: "\<And>a b. red S a b \<Longrightarrow> red S (f a) (f b)"
    and sn: "SN S s"
    and eq: "s = f t"
  shows "SN S t"
  using sn eq
proof (induct arbitrary: t rule: SN.induct)
  case (SNI s)
  show ?case
  proof (rule SN.SNI)
    fix v
    assume "red S t v"
    then have "red S (f t) (f v)" by (rule mono)
    with SNI(3) have "red S s (f v)" by simp
    from SNI(2)[OF this refl] show "SN S v" .
  qed
qed

lemma SN_App1: "SN S (App t u) \<Longrightarrow> SN S t"
  by (rule SN_context[where f = "\<lambda>x. App x u"]) (auto intro: red.appL)

lemma SN_App2: "SN S (App t u) \<Longrightarrow> SN S u"
  by (rule SN_context[where f = "\<lambda>x. App t x"]) (auto intro: red.appR)

lemma SN_apps_head: "SN S (apps t xs) \<Longrightarrow> SN S t"
  by (induct xs arbitrary: t) (auto dest: SN_App1)

subsection \<open>Reduction inside constructor arguments\<close>

lemma red_PCon_arg:
  assumes "i < length as" and "red S (as ! i) a'"
  shows "red S (PCon h k as) (PCon h k (as[i := a']))"
proof -
  have "as = take i as @ as ! i # drop (Suc i) as"
    using assms(1) by (simp add: id_take_nth_drop)
  moreover have "as[i := a'] = take i as @ a' # drop (Suc i) as"
    using assms(1) by (simp add: upd_conv_take_nth_drop)
  ultimately show ?thesis
    using red.pconArg[OF assms(2), of h k "take i as" "drop (Suc i) as"]
    by simp
qed

lemma SN_PCon_arg:
  assumes sn: "SN S (PCon h k as)" and i: "i < length as"
  shows "SN S (as ! i)"
proof (rule SN_context[where f = "\<lambda>x. PCon h k (as[i := x])"])
  fix a b
  assume "red S a b"
  moreover have "as[i := a] ! i = a" using i by simp
  ultimately have "red S (PCon h k (as[i := a]))
      (PCon h k ((as[i := a])[i := b]))"
    using i by (metis length_list_update red_PCon_arg)
  then show "red S (PCon h k (as[i := a])) (PCon h k (as[i := b]))"
    by simp
next
  show "SN S (PCon h k as)" by (rule sn)
next
  show "PCon h k as = PCon h k (as[i := as ! i])" by simp
qed

lemma red_LCon_arg:
  assumes "i < length as" and "red S (as ! i) a'"
  shows "red S (LCon h k as d) (LCon h k (as[i := a']) d)"
proof -
  have "as = take i as @ as ! i # drop (Suc i) as"
    using assms(1) by (simp add: id_take_nth_drop)
  moreover have "as[i := a'] = take i as @ a' # drop (Suc i) as"
    using assms(1) by (simp add: upd_conv_take_nth_drop)
  ultimately show ?thesis
    using red.lconArg[OF assms(2), of h k "take i as" "drop (Suc i) as" d]
    by simp
qed

lemma SN_LCon_arg:
  assumes sn: "SN S (LCon h k as d)" and i: "i < length as"
  shows "SN S (as ! i)"
proof (rule SN_context[where f = "\<lambda>x. LCon h k (as[i := x]) d"])
  fix a b
  assume "red S a b"
  moreover have "as[i := a] ! i = a" using i by simp
  ultimately have "red S (LCon h k (as[i := a]) d)
      (LCon h k ((as[i := a])[i := b]) d)"
    using i by (metis length_list_update red_LCon_arg)
  then show "red S (LCon h k (as[i := a]) d)
      (LCon h k (as[i := b]) d)"
    by simp
next
  show "SN S (LCon h k as d)" by (rule sn)
next
  show "LCon h k as d = LCon h k (as[i := as ! i]) d" by simp
qed

end
