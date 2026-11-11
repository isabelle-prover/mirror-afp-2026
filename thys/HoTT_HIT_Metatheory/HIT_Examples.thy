theory HIT_Examples
  imports HIT_Open_Boundary_Check
begin

section \<open>The schema at work\<close>

text \<open>
  The standard examples that fit the schema are represented by individual
  signatures.  They are collected in one signature environment so that they
  can refer to one another: the suspension of the unit type, and the
  propositional truncation of the natural numbers, are parametrised by the
  codes of those types.
\<close>

definition emptySig :: hsig where
  "emptySig = \<lparr> pcons = [], lcons = [], lends = [] \<rparr>"

definition unitSig :: hsig where
  "unitSig = \<lparr> pcons = [[]], lcons = [], lends = [] \<rparr>"

definition natSig :: hsig where
  "natSig = \<lparr> pcons = [[], [Rec]], lcons = [], lends = [] \<rparr>"

definition circleSig :: hsig where
  "circleSig =
    \<lparr> pcons = [[]], lcons = [[]], lends = [(ECon 0 [], ECon 0 [])] \<rparr>"

definition intervalSig :: hsig where
  "intervalSig =
    \<lparr> pcons = [[], []], lcons = [[]],
      lends = [(ECon 0 [], ECon 1 [])] \<rparr>"

definition suspSig :: "nat \<Rightarrow> hsig" where
  "suspSig a =
    \<lparr> pcons = [[], []], lcons = [[Par a]],
      lends = [(ECon 0 [], ECon 1 [])] \<rparr>"

definition truncSig :: "nat \<Rightarrow> hsig" where
  "truncSig a =
    \<lparr> pcons = [[Par a]], lcons = [[Rec, Rec]],
      lends = [(EArg 0, EArg 1)] \<rparr>"

text \<open>
  Codes: \<open>0\<close> the circle, \<open>1\<close> the interval, \<open>2\<close> the natural numbers, \<open>3\<close> the
  empty type, \<open>4\<close> the unit type, \<open>5\<close> the suspension of the unit type, \<open>6\<close>
  the propositional truncation of the natural numbers.
\<close>

definition demo :: sigenv where
  "demo n =
    (if n = 0 then circleSig
     else if n = 1 then intervalSig
     else if n = 2 then natSig
     else if n = 3 then emptySig
     else if n = 4 then unitSig
     else if n = 5 then suspSig 4
     else if n = 6 then truncSig 2
     else emptySig)"

lemma demo_simps [simp]:
  "demo 0 = circleSig"
  "demo 1 = intervalSig"
  "demo 2 = natSig"
  "demo 3 = emptySig"
  "demo 4 = unitSig"
  "demo 5 = suspSig 4"
  "demo 6 = truncSig 2"
  by (simp_all add: demo_def)

subsection \<open>Well-formed signatures\<close>

lemma demo_wf_circle: "wf_hsig demo 0"
  by (auto simp: wf_hsig_def circleSig_def demo_def
      intro!: wf_endpt.wfECon)

lemma demo_wf_interval: "wf_hsig demo 1"
  by (auto simp: wf_hsig_def intervalSig_def demo_def
      intro!: wf_endpt.wfECon)

lemma demo_wf_nat: "wf_hsig demo 2"
  by (simp add: wf_hsig_def natSig_def demo_def)

lemma demo_wf_empty: "wf_hsig demo 3"
  by (simp add: wf_hsig_def emptySig_def demo_def)

lemma demo_wf_unit: "wf_hsig demo 4"
  by (simp add: wf_hsig_def unitSig_def demo_def)

lemma demo_wf_suspension: "wf_hsig demo 5"
  by (auto simp: wf_hsig_def suspSig_def demo_def
      intro!: wf_endpt.wfECon)

lemma demo_wf_truncation: "wf_hsig demo 6"
proof -
  have e0: "wf_endpt demo 6 [Rec, Rec] (EArg 0) (Hit 6)"
  proof -
    have "wf_endpt demo 6 [Rec, Rec] (EArg 0)
        (argTy 6 ([Rec, Rec] ! 0))"
      by (rule wf_endpt.wfEArg) simp
    then show ?thesis by simp
  qed
  have e1: "wf_endpt demo 6 [Rec, Rec] (EArg 1) (Hit 6)"
  proof -
    have "wf_endpt demo 6 [Rec, Rec] (EArg 1)
        (argTy 6 ([Rec, Rec] ! 1))"
      by (rule wf_endpt.wfEArg) simp
    then show ?thesis by simp
  qed
  show ?thesis
    using e0 e1 by (simp add: wf_hsig_def truncSig_def demo_def)
qed

lemma demo_ge_seven:
  assumes "7 \<le> h"
  shows "demo h = emptySig"
  using assms by (simp add: demo_def)

theorem demo_wf: "wf_sigenv demo"
  unfolding wf_sigenv_def
proof
  fix h :: nat
  consider "h = 0" | "h = 1" | "h = 2" | "h = 3" |
    "h = 4" | "h = 5" | "h = 6" | "7 \<le> h"
    by linarith
  then show "wf_hsig demo h"
  proof cases
    case 1
    with demo_wf_circle show ?thesis by simp
  next
    case 2
    with demo_wf_interval show ?thesis by simp
  next
    case 3
    with demo_wf_nat show ?thesis by simp
  next
    case 4
    with demo_wf_empty show ?thesis by simp
  next
    case 5
    with demo_wf_unit show ?thesis by simp
  next
    case 6
    with demo_wf_suspension show ?thesis by simp
  next
    case 7
    with demo_wf_truncation show ?thesis by simp
  next
    case 8
    with demo_ge_seven[OF this] show ?thesis
      by (simp add: wf_hsig_def emptySig_def)
  qed
qed

subsection \<open>Boundaries of path constructors\<close>

text \<open>
  The two endpoints of a path constructor are not extra rules: they are what
  the path constructor \<^emph>\<open>is\<close> at the two constant dimensions.
\<close>

abbreviation base :: tm where "base \<equiv> PCon 0 0 []"
abbreviation loop :: "nat \<Rightarrow> tm" where "loop j \<equiv> LCon 0 0 [] (DVar j)"

theorem loop_boundary_zero: "mkL demo 0 0 [] D0 = base"
  by (simp add: lhsOf_def circleSig_def)

theorem loop_boundary_one: "mkL demo 0 0 [] D1 = base"
  by (simp add: rhsOf_def circleSig_def)

theorem loop_dsubst_zero: "dsubst demo j D0 (loop j) = base"
  by (simp add: lhsOf_def circleSig_def)

theorem loop_dsubst_one: "dsubst demo j D1 (loop j) = base"
  by (simp add: rhsOf_def circleSig_def)

abbreviation izero :: tm where "izero \<equiv> PCon 1 0 []"
abbreviation ione :: tm where "ione \<equiv> PCon 1 1 []"
abbreviation seg :: "nat \<Rightarrow> tm" where "seg j \<equiv> LCon 1 0 [] (DVar j)"

theorem seg_boundary:
  "dsubst demo j D0 (seg j) = izero"
  "dsubst demo j D1 (seg j) = ione"
  by (simp_all add: lhsOf_def rhsOf_def intervalSig_def demo_def)

text \<open>
  For the suspension, the meridian at a point of the parameter type joins the
  two poles; for the propositional truncation, the squashing path joins its
  own two arguments, which is the case in which an endpoint is an argument
  rather than a point constructor.
\<close>

theorem merid_boundary:
  "dsubst demo j D0 (LCon 5 0 [a] (DVar j)) = PCon 5 0 []"
  "dsubst demo j D1 (LCon 5 0 [a] (DVar j)) = PCon 5 1 []"
  by (simp_all add: lhsOf_def rhsOf_def suspSig_def)

theorem squash_boundary:
  "dsubst demo j D0 (LCon 6 0 [x, y] (DVar j)) =
    dsubst demo j D0 x"
  "dsubst demo j D1 (LCon 6 0 [x, y] (DVar j)) =
    dsubst demo j D1 y"
  by (simp_all add: lhsOf_def rhsOf_def truncSig_def)

subsection \<open>Boundary-coherent path methods\<close>

text \<open>
  The identity eliminator for the interval uses its two point constructors as
  point methods and its segment as path method.  The checked boundary
  condition verifies both faces.
\<close>

theorem interval_identity_coherent:
  "coherent_methods demo 1 (Hit 1) [izero, ione] [seg 0]"
  by (auto simp: coherent_methods_def boundary_args_def intervalSig_def
      demo_def lhsOf_def rhsOf_def intro: conv_refl)

theorem interval_identity_open_boundary_check:
  assumes "0 \<notin> D"
  shows "open_boundary_check demo D [] 1 (Hit 1)
    [izero, ione] [seg 0]"
proof -
  have ptyped: "\<forall>k < length [izero, ione].
      wt demo D [] ([izero, ione] ! k)
        (methodTy 1 (Hit 1) (pcons (demo 1) ! k))"
  proof (intro allI impI)
    fix k
    assume "k < length [izero, ione]"
    then have "k < 2" by simp
    then have "k = 0 \<or> k = 1" by arith
    then show "wt demo D [] ([izero, ione] ! k)
        (methodTy 1 (Hit 1) (pcons (demo 1) ! k))"
      by (auto simp: intervalSig_def demo_def intro!: wt.intros)
  qed
  have ltyped: "\<forall>k < length [seg 0].
      wt demo (insert 0 D) [] ([seg 0] ! k)
        (methodTy 1 (Hit 1) (lcons (demo 1) ! k))"
    by (auto simp: intervalSig_def demo_def intro!: wt.intros)
  show ?thesis
    using demo_wf assms ptyped ltyped
    by (auto simp: open_boundary_check_def open_face_def open_endpoint_def
        open_args_def intervalSig_def demo_def lhsOf_def rhsOf_def
        joinable_def)
qed

theorem interval_identity_normal_boundary_check:
  assumes "0 \<notin> D"
  shows "normal_boundary_check demo D [] 1 (Hit 1)
    [izero, ione] [seg 0]"
  using interval_identity_open_boundary_check[OF assms]
    normal_boundary_check_iff_open_boundary_check by blast

theorem interval_identity_typed_coherent:
  "typed_coherent_methods demo 1 (Hit 1) [izero, ione] [seg 0]"
  by (rule normal_boundary_check_sound[
        OF interval_identity_normal_boundary_check, where D = "{}"])
    simp

text \<open>
  In contrast, a constant path method can be coherent only if its value is
  convertible to the right point method.  Thus the unchecked counterexample
  with unrelated endpoint methods is rejected by the checked judgment.
\<close>

theorem interval_constant_method_requires_right_endpoint:
  assumes coh: "coherent_methods demo 1 C [u, v] [u]"
    and fixed: "dsubst demo 0 D1 u = u"
  shows "conv demo u v"
proof -
  have "conv demo
      (apps (dsubst demo 0 D1 ([u] ! 0))
        (elimArgs 1 C [u, v] [u] (lcons (demo 1) ! 0) []))
      (elimEnd demo 1 C [u, v] [u] []
        (snd (lends (demo 1) ! 0)))"
    by (rule coherent_methods_one[OF coh, of 0 "[]"])
      (simp_all add: intervalSig_def demo_def boundary_args_def)
  with fixed show ?thesis
    by (simp add: intervalSig_def demo_def)
qed

theorem interval_open_check_rejects_constant_method:
  assumes check: "open_boundary_check demo D G 1 C [u, v] [u]"
    and fixed: "dsubst demo 0 D1 u = u"
  shows "conv demo u v"
proof -
  have "joinable demo u v"
    using check fixed
    unfolding open_boundary_check_def open_face_def open_endpoint_def
      open_args_def intervalSig_def demo_def
    by simp
  then show ?thesis by (rule joinable_conv)
qed

abbreviation interval_id :: "nat \<Rightarrow> tm" where
  "interval_id j \<equiv>
    HElim 1 (Hit 1) [izero, ione] [seg 0] (seg j)"

lemma interval_identity_locally_checked:
  "checked demo (interval_id j)"
  using demo_wf_interval interval_identity_typed_coherent by simp

lemma seg_locally_checked: "checked demo (seg j)"
  using demo_wf_interval by simp

lemma seg_normal: "nform demo (seg j)"
  unfolding nform_def
  by (auto elim: red.cases)

lemma interval_point_method_no_step:
  assumes "[izero, ione] = xs @ m # ys" and "red demo m m'"
  shows False
proof -
  have "m \<in> set [izero, ione]" using assms(1) by auto
  with assms(2) show False by (auto elim: red.cases)
qed

lemma interval_path_method_no_step:
  assumes "[seg 0] = xs @ m # ys" and "red demo m m'"
  shows False
proof -
  have "m \<in> set (xs @ m # ys)" by simp
  then have "m \<in> set [seg 0]" using assms(1) by simp
  then have "m = seg 0" by simp
  with assms(2) show False by (auto elim: red.cases)
qed

lemma interval_identity_red:
  assumes "red demo (interval_id j) u"
  shows "u = seg j"
using assms
proof (rule red_HElimE)
  fix k as
  assume source: "seg j = PCon 1 k as"
    and "k < length (pcons (demo 1))"
    and "u = apps ([izero, ione] ! k)
      (elimArgs 1 (Hit 1) [izero, ione] [seg 0]
        (pcons (demo 1) ! k) as)"
  from source show "u = seg j" by simp
next
  fix k as q
  assume source: "seg j = LCon 1 k as (DVar q)"
    and k: "k < length (lcons (demo 1))"
    and target: "u =
      apps (dsubst demo 0 (DVar q) ([seg 0] ! k))
        (elimArgs 1 (Hit 1) [izero, ione] [seg 0]
          (lcons (demo 1) ! k) as)"
  from source have "k = 0" "as = []" "q = j" by simp_all
  with target show "u = seg j"
    by (simp add: intervalSig_def demo_def)
next
  fix xs m m' ys
  assume methods: "[izero, ione] = xs @ m # ys"
    and step: "red demo m m'"
    and "u = HElim 1 (Hit 1) (xs @ m' # ys) [seg 0] (seg j)"
  from interval_point_method_no_step[OF methods step]
  show "u = seg j" by blast
next
  fix xs m m' ys
  assume methods: "[seg 0] = xs @ m # ys"
    and step: "red demo m m'"
    and "u = HElim 1 (Hit 1) [izero, ione] (xs @ m' # ys) (seg j)"
  from interval_path_method_no_step[OF methods step]
  show "u = seg j" by blast
next
  fix t'
  assume step: "red demo (seg j) t'"
    and "u = HElim 1 (Hit 1) [izero, ione] [seg 0] t'"
  with seg_normal show "u = seg j"
    unfolding nform_def by blast
qed

lemma interval_identity_reducts:
  assumes "reds demo (interval_id j) u"
  shows "u = interval_id j \<or> u = seg j"
  using assms
  by (metis interval_identity_red nform_reds_eq reds_first_step seg_normal)

lemma interval_identity_hereditarily_checked:
  "hereditarily_checked demo (interval_id j)"
  unfolding hereditarily_checked_def
  using interval_identity_locally_checked interval_identity_reducts
    seg_locally_checked by blast

theorem interval_identity_checked:
  assumes j: "j \<in> D" and zero: "0 \<notin> D"
  shows "cwt demo D []
    (interval_id j) (Hit 1)"
proof (rule cwtI[OF zero])
  show "wt demo D [] (interval_id j) (Hit 1)"
  proof (rule wt.wtElim)
    show "wt demo D [] (seg j) (Hit 1)"
      by (rule wt.wtLCon[OF j])
        (simp_all add: intervalSig_def demo_def)
  next
    show "\<forall>k < length [izero, ione].
            wt demo D [] ([izero, ione] ! k) (methodTy 1 (Hit 1) (pcons (demo 1) ! k))"
         "\<forall>k < length [seg 0].
            wt demo (insert 0 D) [] ([seg 0] ! k) (methodTy 1 (Hit 1) (lcons (demo 1) ! k))"
      using interval_identity_open_boundary_check open_boundary_check_def zero
      by auto
  qed (auto simp: intervalSig_def demo_def)
next
  show "hereditarily_checked demo (interval_id j)"
    by (rule interval_identity_hereditarily_checked)
qed

theorem interval_identity_boundary_square:
  "conv demo
    (HElim 1 (Hit 1) [izero, ione] [seg 0] izero)
    izero"
  "conv demo
    (HElim 1 (Hit 1) [izero, ione] [seg 0] ione)
    ione"
  using elim_path_boundary_square[
      OF demo_wf_interval interval_identity_coherent,
      where k = 0 and as = "[]"]
  by (simp_all add: intervalSig_def demo_def lhsOf_def rhsOf_def
      boundary_args_def)

subsection \<open>Computation rules\<close>

text \<open>
  The eliminator computes on the point constructor of the circle, and
  \<^emph>\<open>judgmentally\<close> on its path constructor: this is the cubical-style computation
  rule that distinguishes this operational presentation from axiomatic
  presentations whose path computation is only propositional.
\<close>

theorem circle_rec_base:
  "red demo (HElim 0 C [b] [l] base) b"
proof -
  have "red demo (HElim 0 C [b] [l] (PCon 0 0 []))
      (apps ([b] ! 0) (elimArgs 0 C [b] [l] (pcons (demo 0) ! 0) []))"
    by (rule red.elimPoint) (simp add: circleSig_def)
  then show ?thesis by (simp add: circleSig_def)
qed

theorem circle_rec_loop:
  "red demo (HElim 0 C [b] [l] (loop j)) (dsubst demo 0 (DVar j) l)"
proof -
  have "red demo (HElim 0 C [b] [l] (LCon 0 0 [] (DVar j)))
      (apps (dsubst demo 0 (DVar j) ([l] ! 0))
        (elimArgs 0 C [b] [l] (lcons (demo 0) ! 0) []))"
    by (rule red.elimPath) (simp add: circleSig_def)
  then show ?thesis by (simp add: circleSig_def)
qed

theorem interval_rec_seg:
  "red demo (HElim 1 C [u, v] [p] (seg j)) (dsubst demo 0 (DVar j) p)"
proof -
  have "red demo (HElim 1 C [u, v] [p] (LCon 1 0 [] (DVar j)))
      (apps (dsubst demo 0 (DVar j) ([p] ! 0))
        (elimArgs 1 C [u, v] [p] (lcons (demo 1) ! 0) []))"
    by (rule red.elimPath) (simp add: intervalSig_def demo_def)
  then show ?thesis by (simp add: intervalSig_def demo_def)
qed

theorem susp_rec_merid:
  "red demo (HElim 5 C [u, v] [p] (LCon 5 0 [a] (DVar j)))
    (App (dsubst demo 0 (DVar j) p) a)"
proof -
  have "red demo (HElim 5 C [u, v] [p] (LCon 5 0 [a] (DVar j)))
      (apps (dsubst demo 0 (DVar j) ([p] ! 0))
        (elimArgs 5 C [u, v] [p] (lcons (demo 5) ! 0) [a]))"
    by (rule red.elimPath) (simp add: suspSig_def)
  then show ?thesis by (simp add: suspSig_def)
qed

text \<open>
  Ordinary inductive types are the signatures with no path constructors, and
  their computation rules are the same rule at a signature whose list of path
  constructors is empty.
\<close>

theorem nat_rec_zero:
  "red demo (HElim 2 C [z, s] [] (PCon 2 0 [])) z"
proof -
  have "red demo (HElim 2 C [z, s] [] (PCon 2 0 []))
      (apps ([z, s] ! 0) (elimArgs 2 C [z, s] [] (pcons (demo 2) ! 0) []))"
    by (rule red.elimPoint) (simp add: natSig_def)
  then show ?thesis by (simp add: natSig_def)
qed

theorem nat_rec_succ:
  "red demo (HElim 2 C [z, s] [] (PCon 2 1 [n]))
    (App (App s n) (HElim 2 C [z, s] [] n))"
proof -
  have "red demo (HElim 2 C [z, s] [] (PCon 2 1 [n]))
      (apps ([z, s] ! 1)
        (elimArgs 2 C [z, s] [] (pcons (demo 2) ! 1) [n]))"
    by (rule red.elimPoint) (simp add: natSig_def)
  then show ?thesis by (simp add: natSig_def)
qed

subsection \<open>Typing\<close>

theorem base_typed: "wt demo D [] base (Hit 0)"
  by (rule wt.wtPCon) (simp_all add: circleSig_def)

theorem loop_typed:
  assumes "j \<in> D"
  shows "wt demo D [] (loop j) (Hit 0)"
  by (rule wt.wtLCon[OF assms]) (simp_all add: circleSig_def)

text \<open>
  A path constructor needs a dimension variable, so in the empty dimension
  context the circle has no path-constructor terms at all.  This is the
  syntactic shadow of the canonical-forms theorem: the closed values of a higher inductive
  type in dimension context zero are its point constructors.
\<close>

theorem no_loop_without_dimension:
  "\<not> wt demo {} G (LCon h k as (DVar j)) A"
  by (auto elim: wt.cases)

text \<open>
  The empty type is the signature with no constructors, and it has neither
  point nor path constructor terms.
\<close>

theorem empty_no_constructors:
  "\<not> wt demo D G (PCon 3 k as) A"
  "\<not> wt demo D G (LCon 3 k as d) A"
  by (auto simp add: emptySig_def elim: wt.cases)

subsection \<open>The loop is a value that only a dimension makes possible\<close>

text \<open>
  Both the base point and the loop are normal forms: no computation rule
  applies to a bare constructor term without arguments.
\<close>

theorem base_nform: "nform demo base"
  using nform_def red.cases by fastforce

theorem loop_nform: "nform demo (loop j)"
  unfolding nform_def
proof
  assume "\<exists>u. red demo (loop j) u"
  then obtain u where "red demo (LCon 0 0 [] (DVar j)) u" by blast
  then show False by (cases rule: red.cases) auto
qed

text \<open>
  The loop is not a canonical value: canonical values are point constructors,
  while a path constructor needs a dimension variable.  The loop is therefore
  a term that exists only relative to a dimension, which is exactly the
  cubical-style reading of a path.
\<close>

theorem loop_not_canonical: "\<not> canonical demo 0 (loop j)"
  by (auto elim: canonical.cases)

theorem base_canonical: "canonical demo 0 base"
  by (rule canonicalI) (simp_all add: circleSig_def)

end
