theory HIT_Signature
  imports HIT_Typing
begin

section \<open>Well-formed signatures and endpoints\<close>

text \<open>
  Endpoint expressions are checked against the constructor arguments in
  scope.  An endpoint argument has the type declared by its argument
  specification, while an endpoint constructor must be a declared point
  constructor with well-typed endpoint arguments of its own.
\<close>

inductive wf_endpt ::
  "sigenv \<Rightarrow> nat \<Rightarrow> argspec list \<Rightarrow> endpt \<Rightarrow> ty \<Rightarrow> bool"
  for S :: sigenv and h :: nat and ss :: "argspec list"
where
  wfEArg:
    "i < length ss \<Longrightarrow>
      wf_endpt S h ss (EArg i) (argTy h (ss ! i))"
| wfECon:
    "k < length (pcons (S h)) \<Longrightarrow>
      length es = length (pcons (S h) ! k) \<Longrightarrow>
      (\<forall>i < length es.
        wf_endpt S h ss (es ! i)
          (argTy h (pcons (S h) ! k ! i))) \<Longrightarrow>
      wf_endpt S h ss (ECon k es) (Hit h)"

definition wf_hsig :: "sigenv \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_hsig S h \<longleftrightarrow>
    length (lends (S h)) = length (lcons (S h)) \<and>
    (\<forall>k < length (lcons (S h)).
      wf_endpt S h (lcons (S h) ! k) (fst (lends (S h) ! k)) (Hit h) \<and>
      wf_endpt S h (lcons (S h) ! k) (snd (lends (S h) ! k)) (Hit h))"

definition wf_sigenv :: "sigenv \<Rightarrow> bool" where
  "wf_sigenv S \<longleftrightarrow> (\<forall>h. wf_hsig S h)"

lemma wf_hsig_lend:
  assumes "wf_hsig S h" and "k < length (lcons (S h))"
  shows "k < length (lends (S h))"
  using assms unfolding wf_hsig_def by simp

lemma wf_hsig_lhs:
  assumes "wf_hsig S h" and "k < length (lcons (S h))"
  shows "wf_endpt S h (lcons (S h) ! k) (fst (lends (S h) ! k)) (Hit h)"
  using assms unfolding wf_hsig_def by blast

lemma wf_hsig_rhs:
  assumes "wf_hsig S h" and "k < length (lcons (S h))"
  shows "wf_endpt S h (lcons (S h) ! k) (snd (lends (S h) ! k)) (Hit h)"
  using assms unfolding wf_hsig_def by blast

theorem wf_endpt_instE:
  assumes wf: "wf_endpt S h ss e A"
    and len: "length as = length ss"
    and args: "\<forall>i < length as. wt S D G (as ! i) (argTy h (ss ! i))"
  shows "wt S D G (instE h as e) A"
  using wf
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case
    using len args by simp
next
  case (wfECon k es)
  have "wt S D G (PCon h k (map (instE h as) es)) (Hit h)"
  proof (rule wt.wtPCon)
    show "k < length (pcons (S h))" by (rule wfECon(1))
  next
    show "length (map (instE h as) es) = length (pcons (S h) ! k)"
      using wfECon(2) by simp
  next
    show "\<forall>i < length (map (instE h as) es).
        wt S D G ((map (instE h as) es) ! i)
          (argTy h (pcons (S h) ! k ! i))"
      using wfECon by simp
  qed
  then show ?case by simp
qed

corollary wf_hsig_lhs_typed:
  assumes wf: "wf_hsig S h"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and args: "\<forall>i < length as.
      wt S D G (as ! i) (argTy h (lcons (S h) ! k ! i))"
  shows "wt S D G (lhsOf S h k as) (Hit h)"
  unfolding lhsOf_def
  by (rule wf_endpt_instE[OF wf_hsig_lhs[OF wf k] len args])

corollary wf_hsig_rhs_typed:
  assumes wf: "wf_hsig S h"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and args: "\<forall>i < length as.
      wt S D G (as ! i) (argTy h (lcons (S h) ! k ! i))"
  shows "wt S D G (rhsOf S h k as) (Hit h)"
  unfolding rhsOf_def
  by (rule wf_endpt_instE[OF wf_hsig_rhs[OF wf k] len args])

end
