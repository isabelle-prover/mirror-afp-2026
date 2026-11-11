theory HIT_Canonicity
  imports HIT_Preservation
begin

section \<open>Progress and canonical forms\<close>

text \<open>
  Progress says that a well-typed closed term is canonical at its type or
  takes a reduction step.  Together with multi-step subject reduction this
  gives type safety for every reduct of a closed checked term.  Canonical forms
  for normal terms follow immediately.

    \<^item> Path constructors do not contribute closed values.  A path constructor
      term needs a dimension variable, and there are none in the empty
      dimension context, so the only closed values of a higher inductive type
      are the point-constructor ones.  This is the sense in which the
      cubical-style computation rule for path constructors does not destroy
      the canonical-forms classification.

    \<^item> The proof is a \<^emph>\<open>progress\<close> argument: at every stage, if the term were
      not already a value, a computation rule would apply, contradicting
      normality.  In particular the eliminator case uses the computation rule
      for point constructors, and the constructor case uses the fact that a
      normal constructor term has normal arguments.

  A signature with no point constructors therefore has no closed normal
  inhabitant.  This theory records the general bridge from normalization to
  empty-signature consistency; \<open>HIT_Normalization\<close> subsequently proves the
  premise and derives the unconditional corollary.
\<close>

subsection \<open>Canonical values\<close>

primrec argHit :: "nat \<Rightarrow> argspec \<Rightarrow> nat" where
  "argHit h (Par h') = h'"
| "argHit h Rec = h"

inductive canonical :: "sigenv \<Rightarrow> nat \<Rightarrow> tm \<Rightarrow> bool"
  for S :: sigenv
where
  canonicalI:
    "k < length (pcons (S h)) \<Longrightarrow>
      length as = length (pcons (S h) ! k) \<Longrightarrow>
      (\<forall>i < length as.
        canonical S (argHit h (pcons (S h) ! k ! i)) (as ! i)) \<Longrightarrow>
      canonical S h (PCon h k as)"

definition canonAt :: "sigenv \<Rightarrow> ty \<Rightarrow> tm \<Rightarrow> bool" where
  "canonAt S A t =
    (case A of
       Hit h \<Rightarrow> canonical S h t
     | Fun A1 A2 \<Rightarrow> (\<exists>B u. t = Lam B u))"

lemma canonAt_Hit [simp]: "canonAt S (Hit h) t = canonical S h t"
  by (simp add: canonAt_def)

lemma canonAt_Fun [simp]:
  "canonAt S (Fun A1 A2) t = (\<exists>B u. t = Lam B u)"
  by (simp add: canonAt_def)

subsection \<open>Normal forms are closed under the relevant subterms\<close>

lemma nform_App1: "nform S (App t u) \<Longrightarrow> nform S t"
  unfolding nform_def by (blast intro: red.appL)

lemma nform_elim_scrutinee:
  "nform S (HElim h C pms lms t) \<Longrightarrow> nform S t"
  unfolding nform_def by (blast intro: red.elimScrutinee)

lemma nform_PCon_arg:
  assumes "nform S (PCon h k as)" and "i < length as"
  shows "nform S (as ! i)"
  using assms unfolding nform_def by (blast intro: red_PCon_arg)

subsection \<open>Progress\<close>

theorem progress_aux:
  assumes "wt S D G t A"
  shows "D = {} \<longrightarrow> G = [] \<longrightarrow>
    canonAt S A t \<or> (\<exists>u. red S t u)"
  using assms
proof (induct rule: wt.induct)
  case (wtVar i G D)
  show ?case
  proof (intro impI)
    assume "G = []"
    with wtVar show "canonAt S (G ! i) (Var i) \<or> (\<exists>u. red S (Var i) u)"
      by simp
  qed
next
  case (wtLam D A G t B)
  show ?case by auto
next
  case (wtApp D G t A B u)
  show ?case
  proof (intro impI)
    assume d: "D = {}" and g: "G = []"
    from wtApp(2) d g have
      "canonAt S (Fun A B) t \<or> (\<exists>t'. red S t t')" by blast
    then show "canonAt S B (App t u) \<or> (\<exists>v. red S (App t u) v)"
    proof
      assume "canonAt S (Fun A B) t"
      then obtain A' body where "t = Lam A' body" by auto
      have closed: "dclosed0 S u"
        unfolding dclosed0_def
        using wt_dsubst_fresh[OF wtApp.hyps(3)] d by simp
      have "red S (App (Lam A' body) u) (subst 0 u body)"
        by (rule red.beta[OF closed])
      with \<open>t = Lam A' body\<close>
      have "red S (App t u) (subst 0 u body)" by simp
      then show ?thesis by blast
    next
      assume "\<exists>t'. red S t t'"
      then show ?thesis by (blast intro: red.appL)
    qed
  qed
next
  case (wtPCon k h as D G)
  show ?case
  proof (intro impI)
    assume d: "D = {}" and g: "G = []"
    have alternatives: "\<forall>i < length as.
        canonical S (argHit h (pcons (S h) ! k ! i)) (as ! i) \<or>
        (\<exists>u. red S (as ! i) u)"
    proof (intro allI impI)
      fix i
      assume i: "i < length as"
      from wtPCon(3) i d g have
        "canonAt S (argTy h (pcons (S h) ! k ! i)) (as ! i) \<or>
          (\<exists>u. red S (as ! i) u)"
        by blast
      then show "canonical S (argHit h (pcons (S h) ! k ! i)) (as ! i) \<or>
          (\<exists>u. red S (as ! i) u)"
        by (cases "pcons (S h) ! k ! i") simp_all
    qed
    show "canonAt S (Hit h) (PCon h k as) \<or>
        (\<exists>u. red S (PCon h k as) u)"
    proof (cases "\<forall>i < length as.
        canonical S (argHit h (pcons (S h) ! k ! i)) (as ! i)")
      case True
      have "canonical S h (PCon h k as)"
        by (rule canonicalI[OF wtPCon(1,2) True])
      then show ?thesis by simp
    next
      case False
      then obtain i where i: "i < length as"
        and not_canonical:
          "\<not> canonical S (argHit h (pcons (S h) ! k ! i)) (as ! i)"
        by blast
      from alternatives[rule_format, OF i] not_canonical obtain u where
        "red S (as ! i) u" by blast
      from red_PCon_arg[OF i this] show ?thesis by blast
    qed
  qed
next
  case (wtLCon j D k h as G)
  show ?case
  proof (intro impI)
    assume "D = {}"
    with wtLCon(1) show
      "canonAt S (Hit h) (LCon h k as (DVar j)) \<or>
        (\<exists>u. red S (LCon h k as (DVar j)) u)"
      by simp
  qed
next
  case (wtElim D G t h pms lms C)
  show ?case
  proof (intro impI)
    assume d: "D = {}" and g: "G = []"
    from wtElim(2) d g have
      "canonical S h t \<or> (\<exists>t'. red S t t')" by simp
    then show "canonAt S C (HElim h C pms lms t) \<or>
        (\<exists>u. red S (HElim h C pms lms t) u)"
    proof
      assume "canonical S h t"
      then obtain k as where t: "t = PCon h k as"
        and k: "k < length (pcons (S h))"
        by (auto elim: canonical.cases)
      have "red S (HElim h C pms lms (PCon h k as))
          (apps (pms ! k) (elimArgs h C pms lms (pcons (S h) ! k) as))"
        by (rule red.elimPoint[where S = S and h = h and k = k, OF k])
      with t show ?thesis by blast
    next
      assume "\<exists>t'. red S t t'"
      then show ?thesis by (blast intro: red.elimScrutinee)
    qed
  qed
qed

theorem progress:
  assumes "cwt S {} [] t A"
  shows "canonAt S A t \<or> (\<exists>u. red S t u)"
  using progress_aux[OF cwt_wt[OF assms]] by simp

theorem type_safety:
  assumes wf: "wf_sigenv S"
    and typed: "cwt S {} [] t A"
    and reduces: "reds S t u"
  shows "canonAt S A u \<or> (\<exists>v. red S u v)"
proof -
  have "cwt S {} [] u A"
    by (rule checked_source_subject_reduction_steps[OF wf typed reduces])
  from progress[OF this] show ?thesis .
qed

theorem canonical_forms_raw:
  assumes "wt S {} [] t A" and "nform S t"
  shows "canonAt S A t"
  using progress_aux[OF assms(1)] assms(2)
  unfolding nform_def by blast

theorem canonical_forms:
  assumes "cwt S {} [] t A" and "nform S t"
  shows "canonAt S A t"
  using canonical_forms_raw[OF cwt_wt[OF assms(1)] assms(2)] .

corollary canonical_forms_hit:
  assumes "cwt S {} [] t (Hit h)" and "nform S t"
  shows "canonical S h t"
  using canonical_forms[OF assms] by simp

definition normalizes :: "sigenv \<Rightarrow> tm \<Rightarrow> bool" where
  "normalizes S t \<longleftrightarrow> (\<exists>u. reds S t u \<and> nform S u)"

theorem normalizing_term_has_canonical_result:
  assumes wf: "wf_sigenv S"
    and typed: "cwt S {} [] t A"
    and normalization: "normalizes S t"
  shows "\<exists>u. reds S t u \<and> nform S u \<and> canonAt S A u"
proof -
  from normalization obtain u where reduces: "reds S t u"
    and normal: "nform S u"
    unfolding normalizes_def by blast
  have "wt S {} [] u A"
    by (rule subject_reduction_steps[OF wf cwt_wt[OF typed] reduces])
  from canonical_forms_raw[OF this normal] reduces normal show ?thesis by blast
qed

subsection \<open>The empty signature\<close>

text \<open>
  A signature with no point constructors has no closed normal inhabitant.
  At this stage the conclusion classifies normal terms only.  The following
  bridge is discharged by the strong-normalization theorem in the next theory.
\<close>

theorem no_canonical_without_constructors:
  assumes "pcons (S h) = []"
  shows "\<not> canonical S h t"
proof
  assume "canonical S h t"
  then show False using assms by (auto elim: canonical.cases)
qed

corollary no_closed_normal_inhabitant:
  assumes "pcons (S h) = []"
    and "cwt S {} [] t (Hit h)"
    and "nform S t"
  shows False
  using canonical_forms_hit[OF assms(2,3)]
    no_canonical_without_constructors[where S = S and h = h, OF assms(1)]
  by simp

text \<open>
  Subject reduction connects this classification to any explicitly supplied
  normalization sequence.  Thus no checked closed inhabitant of an empty
  signature can reduce to a normal form.
\<close>

corollary empty_type_has_no_normalizing_inhabitant:
  assumes wf: "wf_sigenv S"
    and empty: "pcons (S h) = []"
    and typed: "cwt S {} [] t (Hit h)"
    and reduces: "reds S t u"
    and normal: "nform S u"
  shows False
proof -
  have "wt S {} [] u (Hit h)"
    by (rule subject_reduction_steps[OF wf cwt_wt[OF typed] reduces])
  from canonical_forms_raw[OF this normal]
    no_canonical_without_constructors[where S = S and h = h and t = u, OF empty]
  show False by simp
qed

corollary normalization_implies_empty_consistency:
  assumes wf: "wf_sigenv S"
    and empty: "pcons (S h) = []"
    and normalization: "\<And>t. cwt S {} [] t (Hit h) \<Longrightarrow> normalizes S t"
  shows "\<not> (\<exists>t. cwt S {} [] t (Hit h))"
proof
  assume "\<exists>t. cwt S {} [] t (Hit h)"
  then obtain t where typed: "cwt S {} [] t (Hit h)" by blast
  from normalizing_term_has_canonical_result[OF wf typed normalization[OF typed]]
  obtain u where "canonical S h u" by auto
  with no_canonical_without_constructors[
      where S = S and h = h and t = u, OF empty]
  show False by blast
qed

end
