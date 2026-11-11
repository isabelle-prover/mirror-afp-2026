theory HIT_Dimensions
  imports HIT_Signature
begin

section \<open>Dimension support\<close>

fun dim_support :: "dim \<Rightarrow> nat set" where
  "dim_support D0 = {}"
| "dim_support D1 = {}"
| "dim_support (DVar j) = {j}"

fun fdims :: "tm \<Rightarrow> nat set" where
  "fdims (Var i) = {}"
| "fdims (Lam A t) = fdims t"
| "fdims (App t u) = fdims t \<union> fdims u"
| "fdims (PCon h k as) = \<Union>(fdims ` set as)"
| "fdims (LCon h k as d) = \<Union>(fdims ` set as) \<union> dim_support d"
| "fdims (HElim h C pms lms t) =
    \<Union>(fdims ` set pms) \<union> (\<Union>(fdims ` set lms) - {0}) \<union> fdims t"

text \<open>
  The reserved dimension index \<open>0\<close> is bound in path methods, hence it is
  removed from the free support of the path-method list of an eliminator.
\<close>

lemma fdims_list_subset:
  assumes "\<forall>i < length xs. fdims (xs ! i) \<subseteq> D"
  shows "\<Union>(fdims ` set xs) \<subseteq> D"
proof
  fix x
  assume "x \<in> \<Union>(fdims ` set xs)"
  then obtain a where a: "a \<in> set xs" and x: "x \<in> fdims a"
    by blast
  from a obtain i where i: "i < length xs" and a': "a = xs ! i"
    by (auto simp: in_set_conv_nth)
  have x': "x \<in> fdims (xs ! i)" using x by (simp add: a')
  from subsetD[OF assms[rule_format, OF i] x'] show "x \<in> D" .
qed

theorem wt_fdims:
  assumes "wt S D G t A"
  shows "fdims t \<subseteq> D"
  using assms
proof (induct rule: wt.induct)
  case wtVar
  then show ?case by simp
next
  case wtLam
  then show ?case by simp
next
  case wtApp
  then show ?case by simp
next
  case (wtPCon k h as D G)
  have args: "\<forall>i < length as. fdims (as ! i) \<subseteq> D"
    using wtPCon(2,3) by simp
  have "\<Union>(fdims ` set as) \<subseteq> D"
    by (rule fdims_list_subset[OF args])
  then show ?case by simp
next
  case (wtLCon j D k h as G)
  have args: "\<forall>i < length as. fdims (as ! i) \<subseteq> D"
    using wtLCon(3,4) by simp
  have "\<Union>(fdims ` set as) \<subseteq> D"
    by (rule fdims_list_subset[OF args])
  then show ?case using wtLCon(1) by auto
next
  case (wtElim D G t h pms lms C)
  have pms: "\<forall>i < length pms. fdims (pms ! i) \<subseteq> D"
    using wtElim(3,5) by simp
  have lms: "\<forall>i < length lms. fdims (lms ! i) \<subseteq> insert 0 D"
    using wtElim(4,6) by simp
  have pms': "\<Union>(fdims ` set pms) \<subseteq> D"
    by (rule fdims_list_subset[OF pms])
  have lms': "\<Union>(fdims ` set lms) \<subseteq> insert 0 D"
    by (rule fdims_list_subset[OF lms])
  have "\<Union>(fdims ` set lms) - {0} \<subseteq> D"
    using lms' by blast
  with wtElim(2) pms' show ?case by auto
qed

lemma dsubstD_fresh:
  assumes "n \<notin> dim_support e"
  shows "dsubstD n d e = e"
  using assms by (cases e) auto

theorem wt_dsubst_fresh:
  assumes typed: "wt S D G t A" and fresh: "n \<notin> D"
  shows "dsubst S n d t = t"
  using typed fresh
proof (induct arbitrary: n d rule: wt.induct)
  case wtVar
  then show ?case by simp
next
  case wtLam
  then show ?case by simp
next
  case wtApp
  then show ?case by simp
next
  case (wtPCon k h as D G)
  have args: "\<forall>a \<in> set as. dsubst S n d a = a"
  proof
    fix a
    assume "a \<in> set as"
    then obtain i where i: "i < length as" and a: "a = as ! i"
      by (auto simp: in_set_conv_nth)
    from wtPCon(2,3) i have "dsubst S n d (as ! i) = as ! i"
      using wtPCon.prems by blast
    then show "dsubst S n d a = a" by (simp add: a)
  qed
  then show ?case by (simp add: map_idI)
next
  case (wtLCon j D k h as G)
  have args: "\<forall>a \<in> set as. dsubst S n d a = a"
  proof
    fix a
    assume "a \<in> set as"
    then obtain i where i: "i < length as" and a: "a = as ! i"
      by (auto simp: in_set_conv_nth)
    from wtLCon(3,4) i have "dsubst S n d (as ! i) = as ! i"
      using wtLCon.prems by blast
    then show "dsubst S n d a = a" by (simp add: a)
  qed
  have "j \<noteq> n" using wtLCon(1) wtLCon.prems by blast
  with args show ?case by (simp add: map_idI)
next
  case (wtElim D G t h pms lms C)
  have t: "dsubst S n d t = t"
    using wtElim(2) wtElim.prems by blast
  have pms: "\<forall>m \<in> set pms. dsubst S n d m = m"
  proof
    fix m
    assume "m \<in> set pms"
    then obtain i where i: "i < length pms" and m: "m = pms ! i"
      by (auto simp: in_set_conv_nth)
    from wtElim(5) i have "dsubst S n d (pms ! i) = pms ! i"
      using wtElim.prems by blast
    then show "dsubst S n d m = m" by (simp add: m)
  qed
  show ?case
  proof (cases "n = 0")
    case True
    with t pms show ?thesis by (simp add: map_idI)
  next
    case False
    have fresh0: "n \<notin> insert 0 D"
      using False wtElim.prems by simp
    have lms: "\<forall>m \<in> set lms. dsubst S n d m = m"
    proof
      fix m
      assume "m \<in> set lms"
      then obtain i where i: "i < length lms" and m: "m = lms ! i"
        by (auto simp: in_set_conv_nth)
      from wtElim(6) i have "dsubst S n d (lms ! i) = lms ! i"
        using fresh0 by blast
      then show "dsubst S n d m = m" by (simp add: m)
    qed
    with False t pms show ?thesis by (simp add: map_idI)
  qed
qed

end
