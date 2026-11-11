theory HIT_Preservation
  imports HIT_Substitution
begin

section \<open>Subject reduction\<close>

lemma all_nth_list_update:
  assumes all: "\<forall>j < length xs. P j (xs ! j)"
    and i: "i < length xs"
    and replacement: "P i x"
  shows "\<forall>j < length (xs[i := x]). P j ((xs[i := x]) ! j)"
  using assms by (auto simp: nth_list_update)

theorem subject_reduction:
  assumes wf: "wf_sigenv S"
    and step: "red S t u"
    and typing: "wt S D G t A"
  shows "wt S D G u A"
  using step typing
proof (induct arbitrary: D G A rule: red.induct)
  case (beta u B t)
  then obtain C where
    body: "wt S D (B # G) t C"
    and arg: "wt S D G u B"
    and A: "A = C"
    by (auto elim: wt.cases)
  have "wt S D G (subst 0 u t) C"
    by (rule wt_subst[OF _ arg, of 0]) (use body in simp_all)
  with A show ?case by simp
next
  case (elimPoint k h C pms lms as)
  from elimPoint.prems obtain
    scrut: "wt S D G (PCon h k as) (Hit h)"
    and plen: "length pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and ptyped: "\<forall>i < length pms.
      wt S D G (pms ! i) (methodTy h C (pcons (S h) ! i))"
    and ltyped: "\<forall>i < length lms.
      wt S (insert 0 D) G (lms ! i) (methodTy h C (lcons (S h) ! i))"
    and A: "A = C"
    by (auto elim: wt.cases)
  from scrut obtain
    len: "length as = length (pcons (S h) ! k)"
    and args: "\<forall>i < length as.
      wt S D G (as ! i) (argTy h (pcons (S h) ! k ! i))"
    by (auto elim: wt.cases)
  have method: "wt S D G (pms ! k) (methodTy h C (pcons (S h) ! k))"
    using elimPoint(1) plen ptyped by auto
  have args': "\<forall>i < length (pcons (S h) ! k).
      wt S D G (as ! i) (argTy h (pcons (S h) ! k ! i))"
    using len args by simp
  have recursive:
    "\<And>a. wt S D G a (Hit h) \<Longrightarrow> wt S D G (HElim h C pms lms a) C"
    by (rule wt.wtElim[OF _ plen llen ptyped ltyped])
  have "wt S D G
      (apps (pms ! k) (elimArgs h C pms lms (pcons (S h) ! k) as)) C"
    by (rule wt_apps_elimArgs[OF recursive len args' method])
  with A show ?case by simp
next
  case (elimPath k h C pms lms as j)
  from elimPath.prems obtain
    scrut: "wt S D G (LCon h k as (DVar j)) (Hit h)"
    and plen: "length pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and ptyped: "\<forall>i < length pms.
      wt S D G (pms ! i) (methodTy h C (pcons (S h) ! i))"
    and ltyped: "\<forall>i < length lms.
      wt S (insert 0 D) G (lms ! i) (methodTy h C (lcons (S h) ! i))"
    and A: "A = C"
    by (auto elim: wt.cases)
  from scrut obtain
    jD: "j \<in> D"
    and len: "length as = length (lcons (S h) ! k)"
    and args: "\<forall>i < length as.
      wt S D G (as ! i) (argTy h (lcons (S h) ! k ! i))"
    by (auto elim: wt.cases)
  have method: "wt S (insert 0 D) G (lms ! k)
      (methodTy h C (lcons (S h) ! k))"
    using elimPath(1) llen ltyped by auto
  have args0: "\<forall>i < length as.
      wt S (insert 0 D) G (as ! i) (argTy h (lcons (S h) ! k ! i))"
    using args by (metis subset_insertI wt_dimension_mono)
  have args0': "\<forall>i < length (lcons (S h) ! k).
      wt S (insert 0 D) G (as ! i) (argTy h (lcons (S h) ! k ! i))"
    using len args0 by simp
  have ptyped0: "\<forall>i < length pms.
      wt S (insert 0 D) G (pms ! i) (methodTy h C (pcons (S h) ! i))"
    using ptyped by (metis subset_insertI wt_dimension_mono)
  have recursive:
    "\<And>a. wt S (insert 0 D) G a (Hit h) \<Longrightarrow>
      wt S (insert 0 D) G (HElim h C pms lms a) C"
  proof -
    fix a
    assume a: "wt S (insert 0 D) G a (Hit h)"
    show "wt S (insert 0 D) G (HElim h C pms lms a) C"
    proof (rule wt.wtElim)
      show "wt S (insert 0 D) G a (Hit h)" by (rule a)
    next
      show "length pms = length (pcons (S h))" by (rule plen)
    next
      show "length lms = length (lcons (S h))" by (rule llen)
    next
      show "\<forall>i < length pms.
          wt S (insert 0 D) G (pms ! i)
            (methodTy h C (pcons (S h) ! i))"
        by (rule ptyped0)
    next
      show "\<forall>i < length lms.
          wt S (insert 0 (insert 0 D)) G (lms ! i)
            (methodTy h C (lcons (S h) ! i))"
        using ltyped by simp
    qed
  qed
  have method': "wt S (dctx_subst 0 (DVar j) (insert 0 D)) G
      (dsubst S 0 (DVar j) (lms ! k))
      (methodTy h C (lcons (S h) ! k))"
    by (rule wt_dimension_subst[OF method wf])
  have methodD: "wt S D G (dsubst S 0 (DVar j) (lms ! k))
      (methodTy h C (lcons (S h) ! k))"
  proof (rule wt_dimension_mono[OF method'])
    show "dctx_subst 0 (DVar j) (insert 0 D) \<subseteq> D"
      using jD unfolding dctx_subst_def by auto
  qed
  have recursiveD:
    "\<And>a. wt S D G a (Hit h) \<Longrightarrow> wt S D G (HElim h C pms lms a) C"
    by (rule wt.wtElim[OF _ plen llen ptyped ltyped])
  have argsD: "\<forall>i < length (lcons (S h) ! k).
      wt S D G (as ! i) (argTy h (lcons (S h) ! k ! i))"
    using len args by simp
  have "wt S D G
      (apps (dsubst S 0 (DVar j) (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as)) C"
    by (rule wt_apps_elimArgs[OF recursiveD len argsD methodD])
  with A show ?case by simp
next
  case (appL t t' u)
  from appL.prems obtain B where
    t: "wt S D G t (Fun B A)" and u: "wt S D G u B"
    by (auto elim: wt.cases)
  have "wt S D G t' (Fun B A)" by (rule appL(2)[OF t])
  from wt.wtApp[OF this u] show ?case .
next
  case (appR u u' t)
  from appR.prems obtain B where
    t: "wt S D G t (Fun B A)" and u: "wt S D G u B"
    by (auto elim: wt.cases)
  have "wt S D G u' B" by (rule appR(2)[OF u])
  from wt.wtApp[OF t this] show ?case .
next
  case (lam t t' B)
  from lam.prems obtain C where
    body: "wt S D (B # G) t C" and A: "A = Fun B C"
    by (auto elim: wt.cases)
  have "wt S D (B # G) t' C" by (rule lam(2)[OF body])
  from wt.wtLam[OF this] A show ?case by simp
next
  case (pconArg a a' h k xs ys)
  let ?as = "xs @ a # ys"
  let ?i = "length xs"
  from pconArg.prems obtain
    k: "k < length (pcons (S h))"
    and len: "length ?as = length (pcons (S h) ! k)"
    and args: "\<forall>j < length ?as.
      wt S D G (?as ! j) (argTy h (pcons (S h) ! k ! j))"
    and A: "A = Hit h"
    by (auto elim: wt.cases)
  have i: "?i < length ?as" by simp
  have a: "wt S D G a (argTy h (pcons (S h) ! k ! ?i))"
    using args[rule_format, OF i] by simp
  have a': "wt S D G a' (argTy h (pcons (S h) ! k ! ?i))"
    by (rule pconArg(2)[OF a])
  have updated: "\<forall>j < length (?as[?i := a']).
      wt S D G ((?as[?i := a']) ! j)
        (argTy h (pcons (S h) ! k ! j))"
    by (rule all_nth_list_update[OF args i a'])
  have target: "xs @ a' # ys = ?as[?i := a']" by simp
  have "wt S D G (PCon h k (?as[?i := a'])) (Hit h)"
  proof (rule wt.wtPCon)
    show "k < length (pcons (S h))" by (rule k)
  next
    show "length (?as[?i := a']) = length (pcons (S h) ! k)"
      using len by simp
  next
    show "\<forall>j < length (?as[?i := a']).
        wt S D G ((?as[?i := a']) ! j)
          (argTy h (pcons (S h) ! k ! j))"
      by (rule updated)
  qed
  with target A show ?case by simp
next
  case (lconArg a a' h k xs ys d)
  let ?as = "xs @ a # ys"
  let ?i = "length xs"
  from lconArg.prems obtain j where d: "d = DVar j"
    and jD: "j \<in> D"
    and k: "k < length (lcons (S h))"
    and len: "length ?as = length (lcons (S h) ! k)"
    and args: "\<forall>q < length ?as.
      wt S D G (?as ! q) (argTy h (lcons (S h) ! k ! q))"
    and A: "A = Hit h"
    by (auto elim: wt.cases)
  have i: "?i < length ?as" by simp
  have a: "wt S D G a (argTy h (lcons (S h) ! k ! ?i))"
    using args[rule_format, OF i] by simp
  have a': "wt S D G a' (argTy h (lcons (S h) ! k ! ?i))"
    by (rule lconArg(2)[OF a])
  have updated: "\<forall>q < length (?as[?i := a']).
      wt S D G ((?as[?i := a']) ! q)
        (argTy h (lcons (S h) ! k ! q))"
    by (rule all_nth_list_update[OF args i a'])
  have target: "xs @ a' # ys = ?as[?i := a']" by simp
  have "wt S D G (LCon h k (?as[?i := a']) (DVar j)) (Hit h)"
  proof (rule wt.wtLCon)
    show "j \<in> D" by (rule jD)
  next
    show "k < length (lcons (S h))" by (rule k)
  next
    show "length (?as[?i := a']) = length (lcons (S h) ! k)"
      using len by simp
  next
    show "\<forall>q < length (?as[?i := a']).
        wt S D G ((?as[?i := a']) ! q)
          (argTy h (lcons (S h) ! k ! q))"
      by (rule updated)
  qed
  with target d A show ?case by simp
next
  case (elimPm m m' h C xs ys lms t)
  let ?pms = "xs @ m # ys"
  let ?i = "length xs"
  from elimPm.prems obtain
    scrut: "wt S D G t (Hit h)"
    and plen: "length ?pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and ptyped: "\<forall>q < length ?pms.
      wt S D G (?pms ! q) (methodTy h C (pcons (S h) ! q))"
    and ltyped: "\<forall>q < length lms.
      wt S (insert 0 D) G (lms ! q) (methodTy h C (lcons (S h) ! q))"
    and A: "A = C"
    by (auto elim: wt.cases)
  have i: "?i < length ?pms" by simp
  have m: "wt S D G m (methodTy h C (pcons (S h) ! ?i))"
    using ptyped[rule_format, OF i] by simp
  have m': "wt S D G m' (methodTy h C (pcons (S h) ! ?i))"
    by (rule elimPm(2)[OF m])
  have updated: "\<forall>q < length (?pms[?i := m']).
      wt S D G ((?pms[?i := m']) ! q)
        (methodTy h C (pcons (S h) ! q))"
    by (rule all_nth_list_update[OF ptyped i m'])
  have target: "xs @ m' # ys = ?pms[?i := m']" by simp
  have "wt S D G (HElim h C (?pms[?i := m']) lms t) C"
    by (rule wt.wtElim[OF scrut]) (use plen llen updated ltyped in simp_all)
  with target A show ?case by simp
next
  case (elimLm m m' h C pms xs ys t)
  let ?lms = "xs @ m # ys"
  let ?i = "length xs"
  from elimLm.prems obtain
    scrut: "wt S D G t (Hit h)"
    and plen: "length pms = length (pcons (S h))"
    and llen: "length ?lms = length (lcons (S h))"
    and ptyped: "\<forall>q < length pms.
      wt S D G (pms ! q) (methodTy h C (pcons (S h) ! q))"
    and ltyped: "\<forall>q < length ?lms.
      wt S (insert 0 D) G (?lms ! q) (methodTy h C (lcons (S h) ! q))"
    and A: "A = C"
    by (auto elim: wt.cases)
  have i: "?i < length ?lms" by simp
  have m: "wt S (insert 0 D) G m (methodTy h C (lcons (S h) ! ?i))"
    using ltyped[rule_format, OF i] by simp
  have m': "wt S (insert 0 D) G m' (methodTy h C (lcons (S h) ! ?i))"
    by (rule elimLm(2)[OF m])
  have updated: "\<forall>q < length (?lms[?i := m']).
      wt S (insert 0 D) G ((?lms[?i := m']) ! q)
        (methodTy h C (lcons (S h) ! q))"
    by (rule all_nth_list_update[OF ltyped i m'])
  have target: "xs @ m' # ys = ?lms[?i := m']" by simp
  have "wt S D G (HElim h C pms (?lms[?i := m']) t) C"
    by (rule wt.wtElim[OF scrut]) (use plen llen ptyped updated in simp_all)
  with target A show ?case by simp
next
  case (elimScrutinee t t' h C pms lms)
  from elimScrutinee.prems obtain
    scrut: "wt S D G t (Hit h)"
    and plen: "length pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and ptyped: "\<forall>q < length pms.
      wt S D G (pms ! q) (methodTy h C (pcons (S h) ! q))"
    and ltyped: "\<forall>q < length lms.
      wt S (insert 0 D) G (lms ! q) (methodTy h C (lcons (S h) ! q))"
    and A: "A = C"
    by (auto elim: wt.cases)
  have "wt S D G t' (Hit h)" by (rule elimScrutinee(2)[OF scrut])
  then have "wt S D G (HElim h C pms lms t') C"
    by (rule wt.wtElim[OF _ plen llen ptyped ltyped])
  with A show ?case by simp
qed

corollary subject_reduction_steps:
  assumes "wf_sigenv S" and "wt S D G t A" and "reds S t u"
  shows "wt S D G u A"
  using assms(3,2)
proof (induct rule: rtranclp_induct)
  case base
  then show ?case .
next
  case step
  then show ?case
    by (meson subject_reduction[OF assms(1)])
qed

corollary checked_source_subject_reduction:
  assumes "wf_sigenv S" and "cwt S D G t A" and "red S t u"
  shows "cwt S D G u A"
proof (rule cwtI)
  show "0 \<notin> D" by (rule cwt_dimension_context[OF assms(2)])
  show "wt S D G u A"
    by (rule subject_reduction[OF assms(1,3) cwt_wt[OF assms(2)]])
  show "hereditarily_checked S u"
    by (rule hereditarily_checked_step[
          OF cwt_hereditarily_checked[OF assms(2)] assms(3)])
qed

corollary checked_source_subject_reduction_steps:
  assumes "wf_sigenv S" and "cwt S D G t A" and "reds S t u"
  shows "cwt S D G u A"
proof (rule cwtI)
  show "0 \<notin> D" by (rule cwt_dimension_context[OF assms(2)])
  show "wt S D G u A"
    by (rule subject_reduction_steps[OF assms(1) cwt_wt[OF assms(2)] assms(3)])
  show "hereditarily_checked S u"
    by (rule hereditarily_checked_steps[
          OF cwt_hereditarily_checked[OF assms(2)] assms(3)])
qed

end
