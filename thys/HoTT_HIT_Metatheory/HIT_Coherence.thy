theory HIT_Coherence
  imports HIT_Dimensions
begin

section \<open>Boundary-coherent elimination\<close>

text \<open>
  Eliminating an endpoint is defined structurally.  Endpoint arguments are
  recursive occurrences and are therefore eliminated recursively; endpoint
  point constructors compute with the corresponding point method.
\<close>

primrec elimEnd ::
  "sigenv \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow>
    tm list \<Rightarrow> endpt \<Rightarrow> tm"
where
  "elimEnd S h C pms lms as (EArg i) =
    HElim h C pms lms (as ! i)"
| "elimEnd S h C pms lms as (ECon k es) =
    apps (pms ! k)
      (elimArgs h C pms lms (pcons (S h) ! k)
        (map (instE h as) es))"

theorem wt_elimEnd:
  assumes endpoint: "wf_endpt S h ss e (Hit h)"
    and len: "length as = length ss"
    and args: "\<forall>i < length as.
      wt S D G (as ! i) (argTy h (ss ! i))"
    and plen: "length pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and ptyped: "\<forall>k < length pms.
      wt S D G (pms ! k) (methodTy h C (pcons (S h) ! k))"
    and ltyped: "\<forall>k < length lms.
      wt S (insert 0 D) G (lms ! k)
        (methodTy h C (lcons (S h) ! k))"
  shows "wt S D G (elimEnd S h C pms lms as e) C"
  using endpoint
proof cases
  case (wfEArg i)
  have ai: "wt S D G (as ! i) (Hit h)"
    using wfEArg len args by simp
  have "wt S D G (HElim h C pms lms (as ! i)) C"
    by (rule wt.wtElim[OF ai plen llen ptyped ltyped])
  then show ?thesis using wfEArg by simp
next
  case (wfECon k es)
  have inst_args: "\<forall>i < length es.
      wt S D G (instE h as (es ! i))
        (argTy h (pcons (S h) ! k ! i))"
  proof (intro allI impI)
    fix i
    assume i: "i < length es"
    from wfECon(4)[rule_format, OF i]
    show "wt S D G (instE h as (es ! i))
        (argTy h (pcons (S h) ! k ! i))"
      by (rule wf_endpt_instE[OF _ len args])
  qed
  have inst_args': "\<forall>i < length (pcons (S h) ! k).
      wt S D G ((map (instE h as) es) ! i)
        (argTy h (pcons (S h) ! k ! i))"
    using wfECon(3) inst_args by simp
  have method: "wt S D G (pms ! k)
      (methodTy h C (pcons (S h) ! k))"
    using wfECon(2) plen ptyped by auto
  have recursive:
    "\<And>a. wt S D G a (Hit h) \<Longrightarrow>
      wt S D G (HElim h C pms lms a) C"
    by (rule wt.wtElim[OF _ plen llen ptyped ltyped])
  have "wt S D G
      (apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k)
          (map (instE h as) es))) C"
    by (rule wt_apps_elimArgs[OF recursive])
      (use wfECon(3) inst_args' method in simp_all)
  then show ?thesis using wfECon by simp
qed

theorem conv_HElim_instE_elimEnd:
  assumes endpoint: "wf_endpt S h ss e (Hit h)"
  shows "conv S
    (HElim h C pms lms (instE h as e))
    (elimEnd S h C pms lms as e)"
  using endpoint
proof cases
  case (wfEArg i)
  then show ?thesis by (simp add: conv_refl)
next
  case (wfECon k es)
  have "red S
      (HElim h C pms lms (PCon h k (map (instE h as) es)))
      (apps (pms ! k)
        (elimArgs h C pms lms (pcons (S h) ! k)
          (map (instE h as) es)))"
    by (rule red.elimPoint[where S = S and h = h and k = k])
      (rule wfECon(2))
  from red_conv[OF this] show ?thesis using wfECon by simp
qed

definition boundary_args :: "sigenv \<Rightarrow> tm list \<Rightarrow> bool" where
  "boundary_args S as \<longleftrightarrow>
    map (dsubst S 0 D0) as = as \<and>
    map (dsubst S 0 D1) as = as"

lemma typed_terms_boundary_args:
  assumes zero: "0 \<notin> D"
    and typed: "\<forall>i < length as. \<exists>A. wt S D G (as ! i) A"
  shows "boundary_args S as"
proof -
  have fixed: "\<forall>a \<in> set as.
      dsubst S 0 D0 a = a \<and> dsubst S 0 D1 a = a"
  proof
    fix a
    assume "a \<in> set as"
    then obtain i where i: "i < length as" and a: "a = as ! i"
      by (auto simp: in_set_conv_nth)
    from typed[rule_format, OF i] obtain A where
      "wt S D G (as ! i) A" by blast
    from wt_dsubst_fresh[OF this zero, of D0]
      wt_dsubst_fresh[OF this zero, of D1]
    show "dsubst S 0 D0 a = a \<and> dsubst S 0 D1 a = a"
      by (simp add: a)
  qed
  have "map (dsubst S 0 D0) as = as"
    using fixed by (simp add: map_idI)
  moreover have "map (dsubst S 0 D1) as = as"
    using fixed by (simp add: map_idI)
  ultimately show ?thesis unfolding boundary_args_def by blast
qed

corollary typed_constructor_args_boundary:
  assumes "0 \<notin> D"
    and "\<forall>i < length as. wt S D G (as ! i) (argTy h (ss ! i))"
  shows "boundary_args S as"
  by (rule typed_terms_boundary_args[OF assms(1)]) (use assms(2) in blast)

definition coherent_methods ::
  "sigenv \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "coherent_methods S h C pms lms \<longleftrightarrow>
    length pms = length (pcons (S h)) \<and>
    length lms = length (lcons (S h)) \<and>
    (\<forall>k < length (lcons (S h)). \<forall>as.
      length as = length (lcons (S h) ! k) \<longrightarrow>
      boundary_args S as \<longrightarrow>
      conv S
        (apps (dsubst S 0 D0 (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as))
        (elimEnd S h C pms lms as (fst (lends (S h) ! k))) \<and>
      conv S
        (apps (dsubst S 0 D1 (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as))
        (elimEnd S h C pms lms as (snd (lends (S h) ! k))))"

lemma coherent_methods_lengths:
  assumes "coherent_methods S h C pms lms"
  shows "length pms = length (pcons (S h))"
    and "length lms = length (lcons (S h))"
  using assms unfolding coherent_methods_def by blast+

lemma coherent_methods_zero:
  assumes coh: "coherent_methods S h C pms lms"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and boundary: "boundary_args S as"
  shows "conv S
    (apps (dsubst S 0 D0 (lms ! k))
      (elimArgs h C pms lms (lcons (S h) ! k) as))
    (elimEnd S h C pms lms as (fst (lends (S h) ! k)))"
  using coh k len boundary unfolding coherent_methods_def by blast

lemma coherent_methods_one:
  assumes coh: "coherent_methods S h C pms lms"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and boundary: "boundary_args S as"
  shows "conv S
    (apps (dsubst S 0 D1 (lms ! k))
      (elimArgs h C pms lms (lcons (S h) ! k) as))
    (elimEnd S h C pms lms as (snd (lends (S h) ! k)))"
  using coh k len boundary unfolding coherent_methods_def by blast

definition typed_coherent_methods ::
  "sigenv \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "typed_coherent_methods S h C pms lms \<longleftrightarrow>
    length pms = length (pcons (S h)) \<and>
    length lms = length (lcons (S h)) \<and>
    (\<forall>k D G as.
      k < length (lcons (S h)) \<longrightarrow>
      length as = length (lcons (S h) ! k) \<longrightarrow>
      0 \<notin> D \<longrightarrow>
      (\<forall>i < length as.
        wt S D G (as ! i) (argTy h (lcons (S h) ! k ! i))) \<longrightarrow>
      joinable S
        (apps (dsubst S 0 D0 (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as))
        (elimEnd S h C pms lms as (fst (lends (S h) ! k))) \<and>
      joinable S
        (apps (dsubst S 0 D1 (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as))
        (elimEnd S h C pms lms as (snd (lends (S h) ! k))))"

lemma typed_coherent_methods_lengths:
  assumes "typed_coherent_methods S h C pms lms"
  shows "length pms = length (pcons (S h))"
    and "length lms = length (lcons (S h))"
  using assms unfolding typed_coherent_methods_def by blast+

lemma typed_coherent_methods_zero:
  assumes coh: "typed_coherent_methods S h C pms lms"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and zero: "0 \<notin> D"
    and args: "\<forall>i < length as.
      wt S D G (as ! i) (argTy h (lcons (S h) ! k ! i))"
  shows "joinable S
    (apps (dsubst S 0 D0 (lms ! k))
      (elimArgs h C pms lms (lcons (S h) ! k) as))
    (elimEnd S h C pms lms as (fst (lends (S h) ! k)))"
  using assms unfolding typed_coherent_methods_def by blast

lemma typed_coherent_methods_one:
  assumes coh: "typed_coherent_methods S h C pms lms"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and zero: "0 \<notin> D"
    and args: "\<forall>i < length as.
      wt S D G (as ! i) (argTy h (lcons (S h) ! k ! i))"
  shows "joinable S
    (apps (dsubst S 0 D1 (lms ! k))
      (elimArgs h C pms lms (lcons (S h) ! k) as))
    (elimEnd S h C pms lms as (snd (lends (S h) ! k)))"
  using assms unfolding typed_coherent_methods_def by blast

subsection \<open>The boundary-computation square\<close>

theorem elim_path_face_zero:
  assumes sig: "wf_hsig S h"
    and coh: "coherent_methods S h C pms lms"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and boundary: "boundary_args S as"
  shows   "conv S
    (HElim h C pms lms (mkL S h k as D0))
    (apps (dsubst S 0 D0 (lms ! k))
      (elimArgs h C pms lms (lcons (S h) ! k) as))"
proof -
  let ?e = "fst (lends (S h) ! k)"
  have endpoint: "wf_endpt S h (lcons (S h) ! k) ?e (Hit h)"
    by (rule wf_hsig_lhs[OF sig k])
  have left: "conv S
      (HElim h C pms lms (mkL S h k as D0))
      (elimEnd S h C pms lms as ?e)"
    using conv_HElim_instE_elimEnd[OF endpoint,
        where C = C and pms = pms and lms = lms and as = as]
    by (simp add: lhsOf_def)
  have right: "conv S
      (apps (dsubst S 0 D0 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))
      (elimEnd S h C pms lms as ?e)"
    by (rule coherent_methods_zero[OF coh k len boundary])
  from conv_trans[OF left conv_sym[OF right]] show ?thesis .
qed

theorem elim_path_face_one:
  assumes sig: "wf_hsig S h"
    and coh: "coherent_methods S h C pms lms"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and boundary: "boundary_args S as"
  shows   "conv S
    (HElim h C pms lms (mkL S h k as D1))
    (apps (dsubst S 0 D1 (lms ! k))
      (elimArgs h C pms lms (lcons (S h) ! k) as))"
proof -
  let ?e = "snd (lends (S h) ! k)"
  have endpoint: "wf_endpt S h (lcons (S h) ! k) ?e (Hit h)"
    by (rule wf_hsig_rhs[OF sig k])
  have left: "conv S
      (HElim h C pms lms (mkL S h k as D1))
      (elimEnd S h C pms lms as ?e)"
    using conv_HElim_instE_elimEnd[OF endpoint,
        where C = C and pms = pms and lms = lms and as = as]
    by (simp add: rhsOf_def)
  have right: "conv S
      (apps (dsubst S 0 D1 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))
      (elimEnd S h C pms lms as ?e)"
    by (rule coherent_methods_one[OF coh k len boundary])
  from conv_trans[OF left conv_sym[OF right]] show ?thesis .
qed

theorem elim_path_boundary_square:
  assumes "wf_hsig S h"
    and "coherent_methods S h C pms lms"
    and "k < length (lcons (S h))"
    and "length as = length (lcons (S h) ! k)"
    and "boundary_args S as"
  shows "conv S
      (HElim h C pms lms (mkL S h k as D0))
      (apps (dsubst S 0 D0 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
    and "conv S
      (HElim h C pms lms (mkL S h k as D1))
      (apps (dsubst S 0 D1 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
proof -
  show "conv S
      (HElim h C pms lms (mkL S h k as D0))
      (apps (dsubst S 0 D0 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
    by (rule elim_path_face_zero[OF assms])
  show "conv S
      (HElim h C pms lms (mkL S h k as D1))
      (apps (dsubst S 0 D1 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
    by (rule elim_path_face_one[OF assms])
qed

corollary typed_elim_path_boundary_square:
  assumes sig: "wf_hsig S h"
    and coh: "typed_coherent_methods S h C pms lms"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and zero: "0 \<notin> D"
    and args: "\<forall>i < length as.
      wt S D G (as ! i) (argTy h (lcons (S h) ! k ! i))"
  shows "conv S
      (HElim h C pms lms (mkL S h k as D0))
      (apps (dsubst S 0 D0 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
    and "conv S
      (HElim h C pms lms (mkL S h k as D1))
      (apps (dsubst S 0 D1 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
proof -
  show "conv S
      (HElim h C pms lms (mkL S h k as D0))
      (apps (dsubst S 0 D0 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
  proof -
    let ?e = "fst (lends (S h) ! k)"
    have endpoint: "wf_endpt S h (lcons (S h) ! k) ?e (Hit h)"
      by (rule wf_hsig_lhs[OF sig k])
    have left: "conv S
        (HElim h C pms lms (mkL S h k as D0))
        (elimEnd S h C pms lms as ?e)"
      using conv_HElim_instE_elimEnd[OF endpoint,
          where C = C and pms = pms and lms = lms and as = as]
      by (simp add: lhsOf_def)
    have right_join: "joinable S
        (apps (dsubst S 0 D0 (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as))
        (elimEnd S h C pms lms as ?e)"
      by (rule typed_coherent_methods_zero[OF coh k len zero args])
    have right: "conv S
        (apps (dsubst S 0 D0 (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as))
        (elimEnd S h C pms lms as ?e)"
      by (rule joinable_conv[OF right_join])
    from conv_trans[OF left conv_sym[OF right]] show ?thesis .
  qed
  show "conv S
      (HElim h C pms lms (mkL S h k as D1))
      (apps (dsubst S 0 D1 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
  proof -
    let ?e = "snd (lends (S h) ! k)"
    have endpoint: "wf_endpt S h (lcons (S h) ! k) ?e (Hit h)"
      by (rule wf_hsig_rhs[OF sig k])
    have left: "conv S
        (HElim h C pms lms (mkL S h k as D1))
        (elimEnd S h C pms lms as ?e)"
      using conv_HElim_instE_elimEnd[OF endpoint,
          where C = C and pms = pms and lms = lms and as = as]
      by (simp add: rhsOf_def)
    have right_join: "joinable S
        (apps (dsubst S 0 D1 (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as))
        (elimEnd S h C pms lms as ?e)"
      by (rule typed_coherent_methods_one[OF coh k len zero args])
    have right: "conv S
        (apps (dsubst S 0 D1 (lms ! k))
          (elimArgs h C pms lms (lcons (S h) ! k) as))
        (elimEnd S h C pms lms as ?e)"
      by (rule joinable_conv[OF right_join])
    from conv_trans[OF left conv_sym[OF right]] show ?thesis .
  qed
qed

text \<open>
  The raw typing relation is useful for syntax-directed metatheory.  The
  local \<open>checked\<close> predicate requires every constructor signature to be well
  formed, every subterm to be checked, and every eliminator to carry path
  methods whose typed boundary instances are joinable.  The \<open>cwt\<close> judgment
  is deliberately a hereditary semantic safety predicate, not an algorithmic
  type-checking judgment: every reduct must pass that local check.  This makes
  the safety invariant explicit rather than assuming that an unindexed
  structural predicate is stable under arbitrary binder substitution.  A
  later theory supplies a finite open-term boundary criterion and proves it
  sound for all typed constructor instances, together with an equivalent
  canonical-normal-form comparison criterion.
\<close>

primrec checked :: "sigenv \<Rightarrow> tm \<Rightarrow> bool" where
  "checked S (Var i) = True"
| "checked S (Lam A t) = checked S t"
| "checked S (App t u) = (checked S t \<and> checked S u)"
| "checked S (PCon h k as) =
    (wf_hsig S h \<and> list_all (checked S) as)"
| "checked S (LCon h k as d) =
    (wf_hsig S h \<and> list_all (checked S) as)"
| "checked S (HElim h C pms lms t) =
    (wf_hsig S h \<and> typed_coherent_methods S h C pms lms \<and>
      list_all (checked S) pms \<and> list_all (checked S) lms \<and>
      checked S t)"

definition hereditarily_checked :: "sigenv \<Rightarrow> tm \<Rightarrow> bool" where
  "hereditarily_checked S t \<longleftrightarrow>
    (\<forall>u. reds S t u \<longrightarrow> checked S u)"

definition cwt ::
  "sigenv \<Rightarrow> nat set \<Rightarrow> ty list \<Rightarrow> tm \<Rightarrow> ty \<Rightarrow> bool"
where
  "cwt S D G t A \<longleftrightarrow>
    0 \<notin> D \<and> wt S D G t A \<and> hereditarily_checked S t"

lemma cwt_wt: "cwt S D G t A \<Longrightarrow> wt S D G t A"
  unfolding cwt_def by blast

lemma cwt_checked: "cwt S D G t A \<Longrightarrow> checked S t"
  unfolding cwt_def hereditarily_checked_def by blast

lemma cwt_dimension_context: "cwt S D G t A \<Longrightarrow> 0 \<notin> D"
  unfolding cwt_def by blast

lemma cwt_hereditarily_checked:
  "cwt S D G t A \<Longrightarrow> hereditarily_checked S t"
  unfolding cwt_def by blast

lemma cwtI:
  assumes "0 \<notin> D" and "wt S D G t A"
    and "hereditarily_checked S t"
  shows "cwt S D G t A"
  using assms unfolding cwt_def by blast

lemma hereditarily_checked_step:
  assumes source: "hereditarily_checked S t" and step: "red S t u"
  shows "hereditarily_checked S u"
proof (unfold hereditarily_checked_def, intro allI impI)
  fix v
  assume uv: "reds S u v"
  have tu: "reds S t u"
    by (rule r_into_rtranclp[where r = "red S", OF step])
  have "reds S t v" by (rule rtranclp_trans[OF tu uv])
  with source show "checked S v"
    unfolding hereditarily_checked_def by blast
qed

lemma hereditarily_checked_steps:
  assumes source: "hereditarily_checked S t" and steps: "reds S t u"
  shows "hereditarily_checked S u"
proof (unfold hereditarily_checked_def, intro allI impI)
  fix v
  assume uv: "reds S u v"
  have "reds S t v" by (rule rtranclp_trans[OF steps uv])
  with source show "checked S v"
    unfolding hereditarily_checked_def by blast
qed

lemma checked_PCon_wf:
  "checked S (PCon h k as) \<Longrightarrow> wf_hsig S h"
  by simp

lemma checked_LCon_wf:
  "checked S (LCon h k as d) \<Longrightarrow> wf_hsig S h"
  by simp

lemma checked_HElim_coherent:
  "checked S (HElim h C pms lms t) \<Longrightarrow>
    typed_coherent_methods S h C pms lms"
  by simp

end
