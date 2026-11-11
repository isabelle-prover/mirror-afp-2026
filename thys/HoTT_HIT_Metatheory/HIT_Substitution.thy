theory HIT_Substitution
  imports HIT_Coherence
begin

section \<open>Structural properties of typing\<close>

fun ins_ty :: "nat \<Rightarrow> ty \<Rightarrow> ty list \<Rightarrow> ty list" where
  "ins_ty 0 A G = A # G"
| "ins_ty (Suc n) A [] = [A]"
| "ins_ty (Suc n) A (B # G) = B # ins_ty n A G"

lemma length_ins_ty [simp]:
  assumes "n \<le> length G"
  shows "length (ins_ty n A G) = Suc (length G)"
  using assms
proof (induct n arbitrary: G)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain B G' where G: "G = B # G'"
    by (cases G) auto
  from Suc.prems G have "n \<le> length G'" by simp
  from Suc.hyps[OF this] show ?case by (simp add: G)
qed

lemma nth_ins_ty_lt:
  assumes "i < n" and "n \<le> length G"
  shows "ins_ty n A G ! i = G ! i"
  using assms
proof (induct n arbitrary: G i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain B G' where G: "G = B # G'"
    by (cases G) auto
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by (simp add: G)
  next
    case (Suc i')
    from Suc.prems G Suc have "i' < n" and "n \<le> length G'"
      by simp_all
    from Suc.hyps[OF this] Suc show ?thesis by (simp add: G)
  qed
qed

lemma nth_ins_ty_eq:
  assumes "n \<le> length G"
  shows "ins_ty n A G ! n = A"
  using assms
proof (induct n arbitrary: G)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain B G' where G: "G = B # G'"
    by (cases G) auto
  from Suc.prems G have "n \<le> length G'" by simp
  from Suc.hyps[OF this] show ?case by (simp add: G)
qed

lemma nth_ins_ty_ge:
  assumes "n \<le> i" and "i < length G"
  shows "ins_ty n A G ! Suc i = G ! i"
  using assms
proof (induct n arbitrary: G i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain B G' where G: "G = B # G'"
    by (cases G) auto
  from Suc.prems(1) obtain i' where i: "i = Suc i'"
    by (cases i) auto
  from Suc.prems G i have "n \<le> i'" and "i' < length G'"
    by simp_all
  from Suc.hyps[OF this] show ?case by (simp add: G i)
qed

lemma wt_dimension_mono:
  assumes deriv: "wt S D G t A" and sub: "D \<subseteq> D'"
  shows "wt S D' G t A"
  using deriv sub
proof (induct arbitrary: D' rule: wt.induct)
  case (wtVar i G D)
  then show ?case by (auto intro: wt.wtVar)
next
  case (wtLam D A G t B)
  from wtLam(2)[OF wtLam.prems] show ?case
    by (rule wt.wtLam)
next
  case (wtApp D G t A B u)
  from wtApp(2)[OF wtApp.prems] wtApp(4)[OF wtApp.prems]
  show ?case by (rule wt.wtApp)
next
  case (wtPCon k h as D G)
  have args: "\<forall>i < length as.
      wt S D' G (as ! i) (argTy h (pcons (S h) ! k ! i))"
    using wtPCon(3) wtPCon.prems by blast
  show ?case by (rule wt.wtPCon[OF wtPCon(1,2) args])
next
  case (wtLCon j D k h as G)
  have args: "\<forall>i < length as.
      wt S D' G (as ! i) (argTy h (lcons (S h) ! k ! i))"
    using wtLCon(4) wtLCon.prems by blast
  have "j \<in> D'" using wtLCon(1) wtLCon.prems by blast
  then show ?case by (rule wt.wtLCon[OF _ wtLCon(2,3) args])
next
  case (wtElim D G t h pms lms C)
  have t: "wt S D' G t (Hit h)"
    by (rule wtElim(2)[OF wtElim.prems])
  have pms: "\<forall>k < length pms.
      wt S D' G (pms ! k) (methodTy h C (pcons (S h) ! k))"
    using wtElim(5) wtElim.prems by blast
  have sub0: "insert 0 D \<subseteq> insert 0 D'"
    using wtElim.prems by blast
  have lms: "\<forall>k < length lms.
      wt S (insert 0 D') G (lms ! k) (methodTy h C (lcons (S h) ! k))"
    using wtElim(6) sub0 by blast
  show ?case by (rule wt.wtElim[OF t wtElim(3,4) pms lms])
qed

theorem wt_lift:
  assumes deriv: "wt S D G t A" and n: "n \<le> length G"
  shows "wt S D (ins_ty n B G) (lift n t) A"
  using deriv n
proof (induct arbitrary: n B rule: wt.induct)
  case (wtVar i G D)
  show ?case
  proof (cases "i < n")
    case True
    have nth: "ins_ty n B G ! i = G ! i"
      by (rule nth_ins_ty_lt[OF True wtVar.prems])
    have "i < length (ins_ty n B G)"
      using wtVar(1) wtVar.prems by simp
    then have "wt S D (ins_ty n B G) (Var i)
        (ins_ty n B G ! i)"
      by (rule wt.wtVar)
    then have "wt S D (ins_ty n B G) (Var i) (G ! i)"
      using nth by simp
    with True show ?thesis by simp
  next
    case False
    have nth: "ins_ty n B G ! Suc i = G ! i"
      by (rule nth_ins_ty_ge) (use False wtVar in auto)
    have "Suc i < length (ins_ty n B G)"
      using wtVar(1) wtVar.prems by simp
    then have "wt S D (ins_ty n B G) (Var (Suc i))
        (ins_ty n B G ! Suc i)"
      by (rule wt.wtVar)
    then have "wt S D (ins_ty n B G) (Var (Suc i)) (G ! i)"
      using nth by simp
    with False show ?thesis by simp
  qed
next
  case (wtLam D A G t C)
  have "Suc n \<le> length (A # G)"
    using wtLam.prems by simp
  from wtLam(2)[OF this, of B]
  have "wt S D (A # ins_ty n B G) (lift (Suc n) t) C"
    by simp
  then have "wt S D (ins_ty n B G) (Lam A (lift (Suc n) t)) (Fun A C)"
    by (rule wt.wtLam)
  then show ?case by simp
next
  case (wtApp D G t A C u)
  from wtApp(2)[OF wtApp.prems, of B]
    wtApp(4)[OF wtApp.prems, of B]
  show ?case by (auto intro: wt.wtApp)
next
  case (wtPCon k h as D G)
  have "wt S D (ins_ty n B G) (PCon h k (map (lift n) as)) (Hit h)"
  proof (rule wt.wtPCon)
    show "k < length (pcons (S h))" by (rule wtPCon(1))
  next
    show "length (map (lift n) as) = length (pcons (S h) ! k)"
      using wtPCon(2) by simp
  next
    show "\<forall>i < length (map (lift n) as).
        wt S D (ins_ty n B G) ((map (lift n) as) ! i)
          (argTy h (pcons (S h) ! k ! i))"
      using wtPCon by simp
  qed
  then show ?case by simp
next
  case (wtLCon j D k h as G)
  have "wt S D (ins_ty n B G)
      (LCon h k (map (lift n) as) (DVar j)) (Hit h)"
  proof (rule wt.wtLCon)
    show "j \<in> D" by (rule wtLCon(1))
  next
    show "k < length (lcons (S h))" by (rule wtLCon(2))
  next
    show "length (map (lift n) as) = length (lcons (S h) ! k)"
      using wtLCon(3) by simp
  next
    show "\<forall>i < length (map (lift n) as).
        wt S D (ins_ty n B G) ((map (lift n) as) ! i)
          (argTy h (lcons (S h) ! k ! i))"
      using wtLCon by simp
  qed
  then show ?case by simp
next
  case (wtElim D G t h pms lms C)
  have "wt S D (ins_ty n B G)
      (HElim h C (map (lift n) pms) (map (lift n) lms) (lift n t)) C"
  proof (rule wt.wtElim)
    show "wt S D (ins_ty n B G) (lift n t) (Hit h)"
      using wtElim by simp
  next
    show "length (map (lift n) pms) = length (pcons (S h))"
      using wtElim by simp
  next
    show "length (map (lift n) lms) = length (lcons (S h))"
      using wtElim by simp
  next
    show "\<forall>k < length (map (lift n) pms).
        wt S D (ins_ty n B G) ((map (lift n) pms) ! k)
          (methodTy h C (pcons (S h) ! k))"
      using wtElim by simp
  next
    show "\<forall>k < length (map (lift n) lms).
        wt S (insert 0 D) (ins_ty n B G) ((map (lift n) lms) ! k)
          (methodTy h C (lcons (S h) ! k))"
      using wtElim by simp
  qed
  then show ?case by simp
qed

section \<open>Term substitution\<close>

lemma nth_ins_ty_gt:
  assumes "n < i" and "i < Suc (length G)" and "n \<le> length G"
  shows "ins_ty n A G ! i = G ! (i - 1)"
proof -
  from assms(1) obtain j where i: "i = Suc j" and n: "n \<le> j"
    by (cases i) auto
  from assms(2) i have j: "j < length G" by simp
  from nth_ins_ty_ge[OF n j, of A] show ?thesis
    by (simp add: i)
qed

theorem wt_subst_aux:
  assumes deriv: "wt S D H t B"
    and ctx: "H = ins_ty n A G"
    and replacement: "wt S D G s A"
    and n: "n \<le> length G"
  shows "wt S D G (subst n s t) B"
  using deriv ctx replacement n
proof (induct arbitrary: n A G s rule: wt.induct)
  case (wtVar i H D)
  have ilen: "i < Suc (length G)"
    using wtVar(1) wtVar.prems(1,3) by simp
  show ?case
  proof (cases "i < n")
    case True
    have nth: "H ! i = G ! i"
      using wtVar.prems(1,3) True nth_ins_ty_lt by blast
    have "i < length G" using True wtVar.prems(3) by linarith
    then have "wt S D G (Var i) (G ! i)" by (rule wt.wtVar)
    with True nth show ?thesis by simp
  next
    case False
    have not_lt: "\<not> i < n" by (rule False)
    show ?thesis
    proof (cases "i = n")
      case True
      have "H ! i = A"
        using wtVar.prems(1,3) True nth_ins_ty_eq by blast
      with True wtVar.prems(2) show ?thesis by simp
    next
      case False
      have ni: "n < i" using not_lt False by linarith
      have nth: "H ! i = G ! (i - 1)"
        using wtVar.prems(1,3) ilen ni nth_ins_ty_gt by blast
      have "i - 1 < length G" using ilen ni by linarith
      then have "wt S D G (Var (i - 1)) (G ! (i - 1))"
        by (rule wt.wtVar)
      with not_lt False nth show ?thesis by simp
    qed
  qed
next
  case (wtLam D B0 H t C)
  have source: "B0 # H = ins_ty (Suc n) A (B0 # G)"
    using wtLam.prems(1) by simp
  have n': "Suc n \<le> length (B0 # G)"
    using wtLam.prems(3) by simp
  have lifted: "wt S D (B0 # G) (lift 0 s) A"
    using wt_lift[OF wtLam.prems(2), of 0 B0] by simp
  from wtLam(2)[OF source lifted n']
  have "wt S D (B0 # G) (subst (Suc n) (lift 0 s) t) C" .
  then have "wt S D G (Lam B0 (subst (Suc n) (lift 0 s) t)) (Fun B0 C)"
    by (rule wt.wtLam)
  then show ?case by simp
next
  case (wtApp D H t A0 B0 u)
  have t: "wt S D G (subst n s t) (Fun A0 B0)"
    by (rule wtApp(2)[OF wtApp.prems])
  have u: "wt S D G (subst n s u) A0"
    by (rule wtApp(4)[OF wtApp.prems])
  from wt.wtApp[OF t u] show ?case by simp
next
  case (wtPCon k h as D H)
  have args: "\<forall>i < length as.
      wt S D G (subst n s (as ! i))
        (argTy h (pcons (S h) ! k ! i))"
    using wtPCon(3) wtPCon.prems by blast
  have "wt S D G (PCon h k (map (subst n s) as)) (Hit h)"
  proof (rule wt.wtPCon)
    show "k < length (pcons (S h))" by (rule wtPCon(1))
  next
    show "length (map (subst n s) as) = length (pcons (S h) ! k)"
      using wtPCon(2) by simp
  next
    show "\<forall>i < length (map (subst n s) as).
        wt S D G ((map (subst n s) as) ! i)
          (argTy h (pcons (S h) ! k ! i))"
      using args by simp
  qed
  then show ?case by simp
next
  case (wtLCon j D k h as H)
  have args: "\<forall>i < length as.
      wt S D G (subst n s (as ! i))
        (argTy h (lcons (S h) ! k ! i))"
    using wtLCon(4) wtLCon.prems by blast
  have "wt S D G (LCon h k (map (subst n s) as) (DVar j)) (Hit h)"
  proof (rule wt.wtLCon)
    show "j \<in> D" by (rule wtLCon(1))
  next
    show "k < length (lcons (S h))" by (rule wtLCon(2))
  next
    show "length (map (subst n s) as) = length (lcons (S h) ! k)"
      using wtLCon(3) by simp
  next
    show "\<forall>i < length (map (subst n s) as).
        wt S D G ((map (subst n s) as) ! i)
          (argTy h (lcons (S h) ! k ! i))"
      using args by simp
  qed
  then show ?case by simp
next
  case (wtElim D H t h pms lms C)
  have t: "wt S D G (subst n s t) (Hit h)"
    by (rule wtElim(2)[OF wtElim.prems])
  have pms: "\<forall>k < length pms.
      wt S D G (subst n s (pms ! k))
        (methodTy h C (pcons (S h) ! k))"
    using wtElim(5) wtElim.prems by blast
  have replacement0: "wt S (insert 0 D) G s A"
    by (rule wt_dimension_mono[OF wtElim.prems(2)]) blast
  have lms: "\<forall>k < length lms.
      wt S (insert 0 D) G (subst n s (lms ! k))
        (methodTy h C (lcons (S h) ! k))"
    using wtElim(6) wtElim.prems(1,3) replacement0 by blast
  have "wt S D G
      (HElim h C (map (subst n s) pms) (map (subst n s) lms)
        (subst n s t)) C"
  proof (rule wt.wtElim[OF t])
    show "length (map (subst n s) pms) = length (pcons (S h))"
      using wtElim(3) by simp
  next
    show "length (map (subst n s) lms) = length (lcons (S h))"
      using wtElim(4) by simp
  next
    show "\<forall>k < length (map (subst n s) pms).
        wt S D G ((map (subst n s) pms) ! k)
          (methodTy h C (pcons (S h) ! k))"
      using pms by simp
  next
    show "\<forall>k < length (map (subst n s) lms).
        wt S (insert 0 D) G ((map (subst n s) lms) ! k)
          (methodTy h C (lcons (S h) ! k))"
      using lms by simp
  qed
  then show ?case by simp
qed

corollary wt_subst:
  assumes "wt S D (ins_ty n A G) t B"
    and "wt S D G s A"
    and "n \<le> length G"
  shows "wt S D G (subst n s t) B"
  by (rule wt_subst_aux[OF assms(1) refl assms(2,3)])

section \<open>Dimension substitution\<close>

fun dim_set :: "dim \<Rightarrow> nat set" where
  "dim_set D0 = {}"
| "dim_set D1 = {}"
| "dim_set (DVar j) = {j}"

definition dctx_subst :: "nat \<Rightarrow> dim \<Rightarrow> nat set \<Rightarrow> nat set" where
  "dctx_subst n d D = (D - {n}) \<union> dim_set d"

lemma dctx_subst_insert_nonzero:
  assumes "n \<noteq> 0"
  shows "dctx_subst n d (insert 0 D) = insert 0 (dctx_subst n d D)"
  using assms unfolding dctx_subst_def by auto

lemma dctx_subst_bound_subset:
  "insert 0 D \<subseteq> insert 0 (dctx_subst 0 d D)"
  unfolding dctx_subst_def by auto

theorem wt_dimension_subst:
  assumes deriv: "wt S D G t A" and wf: "wf_sigenv S"
  shows "wt S (dctx_subst n d D) G (dsubst S n d t) A"
  using deriv wf
proof (induct arbitrary: n d rule: wt.induct)
  case (wtVar i G D)
  then show ?case by (auto intro: wt.wtVar)
next
  case (wtLam D A G t B)
  from wtLam(2)[OF wtLam.prems, of n d]
  show ?case by (auto intro: wt.wtLam)
next
  case (wtApp D G t A B u)
  from wtApp(2)[OF wtApp.prems, of n d]
    wtApp(4)[OF wtApp.prems, of n d]
  show ?case by (auto intro: wt.wtApp)
next
  case (wtPCon k h as D G)
  have args: "\<forall>i < length as.
      wt S (dctx_subst n d D) G (dsubst S n d (as ! i))
        (argTy h (pcons (S h) ! k ! i))"
    using wtPCon(3) wtPCon.prems by blast
  have "wt S (dctx_subst n d D) G
      (PCon h k (map (dsubst S n d) as)) (Hit h)"
  proof (rule wt.wtPCon)
    show "k < length (pcons (S h))" by (rule wtPCon(1))
  next
    show "length (map (dsubst S n d) as) = length (pcons (S h) ! k)"
      using wtPCon(2) by simp
  next
    show "\<forall>i < length (map (dsubst S n d) as).
        wt S (dctx_subst n d D) G ((map (dsubst S n d) as) ! i)
          (argTy h (pcons (S h) ! k ! i))"
      using args by simp
  qed
  then show ?case by simp
next
  case (wtLCon j D k h as G)
  let ?D' = "dctx_subst n d D"
  let ?as' = "map (dsubst S n d) as"
  have args: "\<forall>i < length as.
      wt S ?D' G (dsubst S n d (as ! i))
        (argTy h (lcons (S h) ! k ! i))"
    using wtLCon(4) wtLCon.prems by blast
  have args': "\<forall>i < length ?as'.
      wt S ?D' G (?as' ! i) (argTy h (lcons (S h) ! k ! i))"
    using args by simp
  have len: "length ?as' = length (lcons (S h) ! k)"
    using wtLCon(3) by simp
  have sig: "wf_hsig S h"
    using wtLCon.prems unfolding wf_sigenv_def by blast
  show ?case
  proof (cases "j = n")
    case False
    have "j \<in> ?D'"
      using wtLCon(1) False unfolding dctx_subst_def by auto
    then have "wt S ?D' G (LCon h k ?as' (DVar j)) (Hit h)"
      by (rule wt.wtLCon[OF _ wtLCon(2) len args'])
    with False show ?thesis by simp
  next
    case True
    show ?thesis
    proof (cases d)
      case D0
      have "wt S ?D' G (lhsOf S h k ?as') (Hit h)"
        by (rule wf_hsig_lhs_typed[OF sig wtLCon(2) len args'])
      with True D0 show ?thesis by simp
    next
      case D1
      have "wt S ?D' G (rhsOf S h k ?as') (Hit h)"
        by (rule wf_hsig_rhs_typed[OF sig wtLCon(2) len args'])
      with True D1 show ?thesis by simp
    next
      case (DVar m)
      have "m \<in> ?D'"
        unfolding dctx_subst_def DVar by simp
      then have "wt S ?D' G (LCon h k ?as' (DVar m)) (Hit h)"
        by (rule wt.wtLCon[OF _ wtLCon(2) len args'])
      with True DVar show ?thesis by simp
    qed
  qed
next
  case (wtElim D G t h pms lms C)
  let ?D' = "dctx_subst n d D"
  let ?pms' = "map (dsubst S n d) pms"
  let ?lms' = "if n = 0 then lms else map (dsubst S n d) lms"
  have t: "wt S ?D' G (dsubst S n d t) (Hit h)"
    by (rule wtElim(2)[OF wtElim.prems])
  have pms: "\<forall>k < length pms.
      wt S ?D' G (dsubst S n d (pms ! k))
        (methodTy h C (pcons (S h) ! k))"
    using wtElim(5) wtElim.prems by blast
  have pms': "\<forall>k < length ?pms'.
      wt S ?D' G (?pms' ! k) (methodTy h C (pcons (S h) ! k))"
    using pms by simp
  have lms': "\<forall>k < length ?lms'.
      wt S (insert 0 ?D') G (?lms' ! k)
        (methodTy h C (lcons (S h) ! k))"
  proof (cases "n = 0")
    case True
    have source: "\<forall>k < length lms.
        wt S (insert 0 D) G (lms ! k)
          (methodTy h C (lcons (S h) ! k))"
      using wtElim(6) by blast
    have sub: "insert 0 D \<subseteq> insert 0 ?D'"
      using True dctx_subst_bound_subset by simp
    have "\<forall>k < length lms.
        wt S (insert 0 ?D') G (lms ! k)
          (methodTy h C (lcons (S h) ! k))"
      using source
      by (metis wt_dimension_mono sub)
    with True show ?thesis by simp
  next
    case False
    have target: "\<forall>k < length lms.
        wt S (dctx_subst n d (insert 0 D)) G
          (dsubst S n d (lms ! k))
          (methodTy h C (lcons (S h) ! k))"
      using wtElim(6) wtElim.prems by blast
    have eq: "dctx_subst n d (insert 0 D) = insert 0 ?D'"
      by (rule dctx_subst_insert_nonzero[OF False])
    from target False eq show ?thesis by simp
  qed
  have "wt S ?D' G (HElim h C ?pms' ?lms' (dsubst S n d t)) C"
  proof (rule wt.wtElim[OF t])
    show "length ?pms' = length (pcons (S h))"
      using wtElim(3) by simp
  next
    show "length ?lms' = length (lcons (S h))"
      using wtElim(4) by simp
  next
    show "\<forall>k < length ?pms'.
        wt S ?D' G (?pms' ! k) (methodTy h C (pcons (S h) ! k))"
      by (rule pms')
  next
    show "\<forall>k < length ?lms'.
        wt S (insert 0 ?D') G (?lms' ! k)
          (methodTy h C (lcons (S h) ! k))"
      by (rule lms')
  qed
  then show ?case by simp
qed

end
