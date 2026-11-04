(*  Title:   Regular_Variation.thy
    Author:  Michikazu Hirata
*)

section \<open>Regularly Varying Functions\<close>
theory Regular_Variation
  imports
   "Lemmas_Regular_Variation"
   "Cauchy_Functional_Equation.Cauchy_Functional_Equation"
begin

text \<open>We refer to Chapter~1 of the book by Bingham et al.~\cite{BGT}, and
      Chapter~2 of the book by Resnick~\cite{Resnick}.\<close>
subsection \<open> Definition and Basic Properties \<close>
subsubsection \<open> Regularly Varying Functions \<close>
definition regularly_varying :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
"regularly_varying U \<rho> \<longleftrightarrow>
   U \<in> borel_measurable (restrict_space borel {0<..}) \<and>
   U ` {0<..} \<subseteq> {0<..} \<and>
   (\<forall>x>0. ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top)"

lemma regularly_varyingI:
  assumes "U \<in> borel_measurable (restrict_space borel {0<..})"
    and "\<And>r. 0 < r \<Longrightarrow> 0 < U r"
    and "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top"
  shows "regularly_varying U \<rho>"
  using assms by(auto simp: regularly_varying_def)

lemma regularly_varyingI'':
  assumes "set_borel_measurable borel {0<..} U"
    and "\<And>r. 0 < r \<Longrightarrow> 0 < U r"
    and "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top"
  shows "regularly_varying U \<rho>"
  using assms by(auto intro!: regularly_varyingI
      simp: set_borel_measurable_iff_restrict_space)

lemma regularly_varyingI_total:
  assumes "U \<in> borel_measurable borel"
    and "\<And>r. 0 < r \<Longrightarrow> 0 < U r"
    and "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top"
  shows "regularly_varying U \<rho>"
  using assms by(auto intro!: regularly_varyingI measurable_restrict_space1)

lemma
  assumes "regularly_varying U \<rho>"
  shows regularly_varying_meas':"set_borel_measurable borel {0<..} U"
    and regularly_varying_meas:"U \<in> borel_measurable (restrict_space borel {0<..})"
    and regularly_varying_pos:"\<And>r. 0 < r \<Longrightarrow> 0 < U r"
    and regularly_varying_lim:"\<And>x. x > 0 \<Longrightarrow> ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top"
  using assms
  by(auto simp: regularly_varying_def set_borel_measurable_iff_restrict_space)

lemma regularly_varying_meas_log_exp:
  assumes "regularly_varying U \<rho>"
  shows "(\<lambda>t. ln (U (exp t))) \<in> borel_measurable borel"
  by(intro borel_measurable_ln measurable_compose[OF _ regularly_varying_meas[OF assms]]
      measurable_restrict_space2) auto

lemma
  assumes "regularly_varying U \<rho>"
  shows regularly_varying_meas_o:
    "\<And>a. 0 \<le> a \<Longrightarrow> (\<lambda>x. indicat_real {a<..} x * U x) \<in> borel_measurable borel"
    and regularly_varying_meas_c:
    "\<And>a. 0 < a \<Longrightarrow> (\<lambda>x. indicat_real {a..} x * U x) \<in> borel_measurable borel"
    and regularly_varying_meas_Ioo:
    "\<And>a b. 0 \<le> a \<Longrightarrow> (\<lambda>x. indicat_real {a<..<b} x * U x) \<in> borel_measurable borel"
    and regularly_varying_meas_Ico:
    "\<And>a b. 0 < a \<Longrightarrow> (\<lambda>x. indicat_real {a..<b} x * U x) \<in> borel_measurable borel"
    and regularly_varying_meas_Ioc:
    "\<And>a b. 0 \<le> a \<Longrightarrow> (\<lambda>x. indicat_real {a<..b} x * U x) \<in> borel_measurable borel"
    and regularly_varying_meas_Icc:
    "\<And>a b. 0 < a \<Longrightarrow> (\<lambda>x. indicat_real {a..b} x * U x) \<in> borel_measurable borel"
    and regularly_varying_meas_o_ennreal:
    "\<And>a. 0 \<le> a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a<..} x) \<in> borel_measurable borel"
    and regularly_varying_meas_c_ennreal:
    "\<And>a. 0 < a \<Longrightarrow> (\<lambda>x.  ennreal (U x) * indicator {a..} x) \<in> borel_measurable borel"
    and regularly_varying_meas_Ioo_ennreal:
    "\<And>a b. 0 \<le> a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a<..<b} x) \<in> borel_measurable borel"
    and regularly_varying_meas_Ico_ennreal:
    "\<And>a b. 0 < a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a..<b} x) \<in> borel_measurable borel"
    and regularly_varying_meas_Ioc_ennreal:
    "\<And>a b. 0 \<le> a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a<..b} x) \<in> borel_measurable borel"
    and regularly_varying_meas_Icc_ennreal:
    "\<And>a b. 0 < a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a..b} x) \<in> borel_measurable borel"
proof -
  have *:"(\<lambda>x. indicat_real A x * U x) \<in> borel_measurable borel"
    if A:"A \<in> sets borel" "A \<subseteq> {0<..}" for A
  proof -
    have "(\<lambda>x. indicat_real A x * U x) = (\<lambda>x. indicat_real {0<..} x *  U x * indicat_real A x)"
      by standard (use A in "auto simp: indicator_eq_0_iff indicator_eq_1_iff")
    moreover have "... \<in> borel_measurable borel"
      using regularly_varying_meas'[OF assms] A
      by(auto simp: set_borel_measurable_def)
    ultimately show ?thesis
      by argo
  qed
  have **:"(\<lambda>x. ennreal (U x) * indicator A x) \<in> borel_measurable borel"
    if A:"A \<in> sets borel" "A \<subseteq> {0<..}" for A
    using measurable_compose[OF *[OF A] measurable_ennreal]
    by(simp add: mult.commute ennreal_mult''[OF indicator_pos_le] ennreal_indicator)
  show"\<And>a. 0 \<le> a \<Longrightarrow> (\<lambda>x. indicat_real {a<..} x * U x) \<in> borel_measurable borel"
    and "\<And>a. 0 < a \<Longrightarrow> (\<lambda>x. indicat_real {a..} x * U x) \<in> borel_measurable borel"
    and "\<And>a b. 0 \<le> a \<Longrightarrow> (\<lambda>x. indicat_real {a<..<b} x * U x) \<in> borel_measurable borel"
    and "\<And>a b. 0 < a \<Longrightarrow> (\<lambda>x. indicat_real {a..<b} x * U x) \<in> borel_measurable borel"
    and "\<And>a b. 0 \<le> a \<Longrightarrow> (\<lambda>x. indicat_real {a<..b} x * U x) \<in> borel_measurable borel"
    and "\<And>a b. 0 < a \<Longrightarrow> (\<lambda>x. indicat_real {a..b} x * U x) \<in> borel_measurable borel"
    and "\<And>a. 0 \<le> a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a<..} x) \<in> borel_measurable borel"
    and "\<And>a. 0 < a \<Longrightarrow> (\<lambda>x.  ennreal (U x) * indicator {a..} x) \<in> borel_measurable borel"
    and "\<And>a b. 0 \<le> a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a<..<b} x) \<in> borel_measurable borel"
    and "\<And>a b. 0 < a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a..<b} x) \<in> borel_measurable borel"
    and "\<And>a b. 0 \<le> a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a<..b} x) \<in> borel_measurable borel"
    and "\<And>a b. 0 < a \<Longrightarrow> (\<lambda>x. ennreal (U x) * indicator {a..b} x) \<in> borel_measurable borel"
    by(auto intro!: * **)
qed

lemma regularly_varying_asymp_equiv:
  assumes "regularly_varying U \<rho>"
    and x:"0 < x"
  shows "(\<lambda>t. U (t * x)) \<sim>[at_top] (\<lambda>t. x powr \<rho> * U t)"
  using x by(auto intro!: asymp_equivI'_const regularly_varying_lim assms)

lemma regularly_varying_def2:
"regularly_varying U \<rho> \<longleftrightarrow>
   U \<in> borel_measurable (restrict_space borel {0<..}) \<and>
   U ` {0<..} \<subseteq> {0<..} \<and>
   (\<forall>x>0. (\<lambda>t. U (t * x)) \<sim>[at_top] (\<lambda>t. x powr \<rho> * U t))"
proof safe
  assume [simp]:"U \<in> borel_measurable
          (restrict_space borel {0<..})"
    and h'':"U ` {0<..} \<subseteq> {0<..}"
    and h:"\<forall>x>0. (\<lambda>t. U (t * x)) \<sim>[at_top] (\<lambda>t. x powr \<rho> * U t)"
  hence h':"\<And>x y. x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> \<not> (U (y * x) = 0 \<and> x powr \<rho> * U y = 0)"
    by fastforce
  have "((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top" if x:"x > 0" for x
  proof -
    have "(\<lambda>t. U (t * x)) \<sim>[at_top] (\<lambda>t. x powr \<rho> * U t)"
      using x h by blast
    hence "((\<lambda>y. U (y * x) / (x powr \<rho> * U y)) \<longlongrightarrow> 1) at_top"
      using x h'[of x] by(fastforce intro!: asymp_equivD_strong simp: eventually_at_top_dense)
    from tendsto_mult_right[where c="x powr \<rho>",OF this]
    show ?thesis
      using x by simp
  qed
  thus "regularly_varying U \<rho>"
    using h'' by(auto intro!: regularly_varyingI)
qed(auto simp: regularly_varying_asymp_equiv regularly_varying_meas regularly_varying_pos)

lemma regularly_varying_cong:
  assumes "\<And>x. 0 < x \<Longrightarrow> U x = T x"
  shows "regularly_varying U \<rho> \<longleftrightarrow> regularly_varying T \<rho>"
proof -
  have "regularly_varying T \<rho>"
    if U:"regularly_varying U \<rho>" and x:"\<And>x. 0 < x \<Longrightarrow> U x = T x" for U T
  proof(rule regularly_varyingI)
    show "T \<in> borel_measurable
          (restrict_space borel {0<..})"
      using regularly_varying_meas[OF U] x
      by(simp cong: measurable_cong')
  next
    show "((\<lambda>t. T (t * x) / T t) \<longlongrightarrow> x powr \<rho>) at_top" if x_pos:"0 < x" for x
      by(rule tendsto_cong[THEN iffD1,OF _ regularly_varying_lim[OF U]])
        (use x_pos x in "auto intro!: eventually_at_top_linorderI[where c=1]")
  qed(use U x regularly_varying_pos in fastforce)
  thus ?thesis
    using assms by auto
qed

lemma regularly_varying_ln_exp_iff:
"regularly_varying U \<rho> \<longleftrightarrow>
   U \<in> borel_measurable (restrict_space borel {0<..}) \<and>
   U ` {0<..} \<subseteq> {0<..} \<and>
   (\<forall>x. ((\<lambda>t. ln (U (exp (t + x))) - ln (U (exp t))) \<longlongrightarrow> \<rho> * x) at_top)"
  unfolding regularly_varying_def
proof safe
  fix x
  assume " U ` {0<..} \<subseteq> {0<..}"
         "\<forall>y>0. ((\<lambda>t. U (t * y) / U t) \<longlongrightarrow> y powr \<rho>) at_top"
  hence U:"\<And>x. 0 < x \<Longrightarrow> 0 < U x"
    and lim:"\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. U (t * y) / U t) \<longlongrightarrow> y powr \<rho>) at_top"
    by auto
  hence "\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. U (exp t * y) / U (exp t)) \<longlongrightarrow> y powr \<rho>) at_top"
    using exp_at_top filterlim_compose by fast
  hence "((\<lambda>t. U (exp t * exp x) / U (exp t)) \<longlongrightarrow> exp x powr \<rho>) at_top"
    using exp_gt_zero by blast
  hence "((\<lambda>t. U (exp (t + x)) / U (exp t)) \<longlongrightarrow> exp (x * \<rho>)) at_top"
    using exp_gt_zero by (simp add: exp_add exp_powr_real)
  hence "((\<lambda>t. ln (U (exp (t + x)) / U (exp t))) \<longlongrightarrow> ln (exp (x * \<rho>))) at_top"
    by(intro tendsto_ln) auto
  thus "((\<lambda>t. ln (U (exp (t + x))) - ln (U (exp t))) \<longlongrightarrow> \<rho> * x) at_top"
    by(subst ln_divide_pos[symmetric]) (use U in "auto simp: mult.commute")
next
  fix x :: real
  assume h:"U ` {0<..} \<subseteq> {0<..}"
         "\<forall>y. ((\<lambda>t. ln (U (exp (t + y))) - ln (U (exp t))) \<longlongrightarrow> \<rho> * y) at_top"
   and x:"0 < x"
  hence U:"\<And>x. 0 < x \<Longrightarrow> 0 < U x"
    by blast
  obtain a where a:"x = exp a"
    using x exp_total by blast
  have "((\<lambda>t. ln (U (exp (t + a))) - ln (U (exp t))) \<longlongrightarrow> \<rho> * a) at_top"
    using h by fast
  hence "((\<lambda>t. ln (U (exp (t + a)) / U (exp t))) \<longlongrightarrow> \<rho> * a) at_top"
    by(subst ln_divide_pos) (use U in auto)
  hence "((\<lambda>t. ln (U (exp (t + a)) / U (exp t))) \<longlongrightarrow> ln (x powr \<rho>)) at_top"
    by(simp add: a)
  from tendsto_exp[OF this]
  have "((\<lambda>t. U (exp (t + a)) / U (exp t)) \<longlongrightarrow> x powr \<rho>) at_top"
    using exp_ln[OF powr_gt_zero[of x,THEN iffD2]] x
    by(simp add: exp_ln[OF divide_pos_pos[OF U[OF exp_gt_zero] U[OF exp_gt_zero]]])
  hence *:"((\<lambda>t. U (exp t * exp a) / U (exp t)) \<longlongrightarrow> x powr \<rho>) at_top"
    by (simp add: mult_exp_exp)
  have "((\<lambda>t. U (t * exp a) / U t) \<longlongrightarrow> x powr \<rho>) at_top"
    by(rule tendsto_cong[THEN iffD2,OF _ filterlim_compose[OF * ln_at_top]])
      (auto intro!: eventually_at_top_linorderI[where c=1])
  thus "((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top"
    by(simp add: a)
qed

lemma regularly_varying_ln_exp:
  assumes "regularly_varying U \<rho>"
  shows "((\<lambda>t. ln (U (exp (t + x))) - ln (U (exp t))) \<longlongrightarrow> \<rho> * x) at_top"
  using assms by(simp add: regularly_varying_ln_exp_iff)


subsubsection \<open> Slowly Varying Functions \<close>
abbreviation "slowly_varying L \<equiv> regularly_varying L 0"

lemma slowly_varyingI:
  assumes "L \<in> borel_measurable (restrict_space borel {0<..})"
    and "\<And>r. 0 < r \<Longrightarrow> 0 < L r"
    and "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. L (t * x) / L t) \<longlongrightarrow> 1) at_top"
  shows "slowly_varying L"
  by(auto intro!: regularly_varyingI assms)

lemma slowly_varyingI_total:
  assumes "L \<in> borel_measurable borel"
    and "\<And>r. 0 < r \<Longrightarrow> 0 < L r"
    and "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. L (t * x) / L t) \<longlongrightarrow> 1) at_top"
  shows "slowly_varying L"
  by(auto intro!: regularly_varyingI_total assms)

lemma slowly_varying_lim:
 "slowly_varying L \<Longrightarrow> 0 < x \<Longrightarrow> ((\<lambda>t. L (t * x) / L t) \<longlongrightarrow> 1) at_top"
  by(auto dest: regularly_varying_lim)

lemma slowly_varying_asymp_equiv:
  assumes "slowly_varying L"
    and x:"0 < x"
  shows "(\<lambda>t. L (t * x)) \<sim>[at_top] (\<lambda>t. L t)"
  using assms by(auto dest: regularly_varying_asymp_equiv)

lemma slowly_varying_def2:
"slowly_varying L \<longleftrightarrow>
   L \<in> borel_measurable (restrict_space borel {0<..}) \<and>
   L ` {0<..} \<subseteq> {0<..} \<and>
   (\<forall>x>0. (\<lambda>t. L (t * x)) \<sim>[at_top] (\<lambda>t. L t))"
  unfolding regularly_varying_def2 by auto

lemma slowly_varying_ln_exp:
  assumes "slowly_varying L"
  shows "((\<lambda>t. ln (L (exp (t + x))) - ln (L (exp t))) \<longlongrightarrow> 0) at_top"
  using regularly_varying_ln_exp[OF assms] by simp

lemma slowly_varying_const[simp]: "0 < c \<Longrightarrow> slowly_varying (\<lambda>x. c)"
  by(auto intro!: slowly_varyingI_total)

lemma regularly_varying_powr[simp]: "regularly_varying (\<lambda>x. x powr \<rho>) \<rho>"
  by (auto simp: powr_mult
      intro!: regularly_varyingI_total tendsto_eventually
      eventually_at_top_linorderI[where c=1])

lemma regularly_varying_id[simp]: "regularly_varying (\<lambda>x. x) 1"
  by(auto intro!: regularly_varyingI_total simp: tendsto_iff frequently_def)

lemma slowly_varying_1: "slowly_varying (\<lambda>x. 1)"
  by simp

lemma regularly_varying_mult:
  assumes U:"regularly_varying U \<rho>"
    and V:"regularly_varying V \<eta>"
  shows "regularly_varying (\<lambda>x. U x * V x) (\<rho> + \<eta>)"
proof(rule regularly_varyingI)
  fix x :: real
  assume "0 < x"
  then have *:"((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top"
    and **:"((\<lambda>t. V (t * x) / V t) \<longlongrightarrow> x powr \<eta>) at_top"
    using assms by(auto simp: regularly_varying_lim)
  show "((\<lambda>t. U (t * x) * V (t * x) / (U t * V t)) \<longlongrightarrow> x powr (\<rho> + \<eta>)) at_top"
    using tendsto_mult[OF * **] by(simp add: powr_add)
qed(use assms in
        "auto simp: regularly_varying_pos regularly_varying_meas
         intro!: mult_pos_pos borel_measurable_times")

corollary
  shows regularly_varying_cmult:
    "0 < c \<Longrightarrow> regularly_varying U \<rho> \<Longrightarrow> regularly_varying (\<lambda>x. c * U x) \<rho>"
    and regularly_varying_multc:
    "0 < c \<Longrightarrow> regularly_varying U \<rho> \<Longrightarrow> regularly_varying (\<lambda>x. U x * c) \<rho>"
  using regularly_varying_mult[OF _ slowly_varying_const[of c],of U \<rho>]
  by(auto simp: mult.commute)

lemma regularly_varying_inverse:
  assumes "regularly_varying U \<rho>"
  shows "regularly_varying (\<lambda>x. 1 / U x) (- \<rho>)"
proof(rule regularly_varyingI)
  fix x :: real
  assume [arith]:"0 < x"
  then have *:"((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top"
    by(simp add: regularly_varying_lim assms)
  show "((\<lambda>t. 1 / U (t * x) / (1 / U t)) \<longlongrightarrow> x powr - \<rho>) at_top"
    using tendsto_inverse[OF *] by(auto simp: powr_minus[symmetric])
qed(use assms in "auto dest: regularly_varying_meas regularly_varying_pos")

corollary regularly_varying_inverse_iff:
  "regularly_varying (\<lambda>x. 1 / U x) (- \<rho>) \<longleftrightarrow> regularly_varying U \<rho>"
  using regularly_varying_inverse[of "\<lambda>x. 1 / U x" "- \<rho>"]
    regularly_varying_inverse[of U \<rho>] by fastforce

lemma regularly_varying_divide:
  assumes U:"regularly_varying U \<rho>"
    and V:"regularly_varying V \<eta>"
  shows "regularly_varying (\<lambda>x. U x / V x) (\<rho> - \<eta>)"
  using regularly_varying_mult[OF U regularly_varying_inverse[OF V]]
  by simp

lemma regularly_varying_comp_cmult:
  assumes rv:"regularly_varying U \<rho>"
    and c:"0 < c"
  shows "regularly_varying (\<lambda>x. U (c * x)) \<rho>"
proof(rule regularly_varyingI)
  show "(\<lambda>x. U (c * x)) \<in> borel_measurable (restrict_space borel {0<..})"
    by(intro measurable_compose[OF _ regularly_varying_meas[OF rv]] measurable_restrict_space3)
      (use c in auto)
  show "((\<lambda>t. U (c * (t * x)) / U (c * t)) \<longlongrightarrow> x powr \<rho>) at_top" if x:"0 < x" for x
    unfolding mult.assoc[symmetric]
    by(rule filterlim_compose[OF regularly_varying_lim[OF rv x]])
      (use c filterlim_ident filterlim_tendsto_pos_mult_at_top in fastforce)
qed(use assms in "auto simp: regularly_varying_pos")

lemma regularly_varying_comp_multc:
  assumes "regularly_varying U \<rho>"
    and "0 < c"
  shows "regularly_varying (\<lambda>x. U (x * c)) \<rho>"
  using regularly_varying_comp_cmult[OF assms] by(simp add: mult.commute)

lemma regularly_varying_iff_slowly_varying_divide_powr:
  "regularly_varying U \<rho> \<longleftrightarrow> slowly_varying (\<lambda>x. U x / x powr \<rho>)"
proof
  assume "slowly_varying (\<lambda>x. U x / x powr \<rho>)"
  from regularly_varying_mult[OF this regularly_varying_powr[of \<rho>],simplified]
  show "regularly_varying U \<rho>"
    by(simp cong: regularly_varying_cong)
next
  assume "regularly_varying U \<rho>"
  from regularly_varying_divide[OF this regularly_varying_powr[of \<rho>]]
  show "slowly_varying (\<lambda>x. U x / x powr \<rho>)"
    by simp
qed

corollary regularly_varying_decomp:
  assumes "regularly_varying U \<rho>"
  obtains L where
   "slowly_varying L"
   "\<And>x. 0 < x \<Longrightarrow> U x = x powr \<rho> * L x"
  using assms regularly_varying_iff_slowly_varying_divide_powr by fastforce

lemma slowly_varying_ln:"slowly_varying (\<lambda>x. ln (1 + x))"
proof(safe intro!: slowly_varyingI_total)
  fix x :: real
  assume x[arith]:"0 < x"
  have tendsto_add':"(f \<longlongrightarrow> (0::real)) F \<Longrightarrow> (g \<longlongrightarrow> b) F
                       \<Longrightarrow> ((\<lambda>x::real. f x + g x) \<longlongrightarrow> b) F" for f g b F
    using tendsto_add by fastforce
  show "((\<lambda>t. ln (1 + t * x) / ln (1 + t)) \<longlongrightarrow> 1) at_top"
  proof(rule Lim_transform_eventually)
    show "((\<lambda>t. ln (1 / (1 + t) + (t * x) / (1 + t)) / ln (1 + t) + 1) \<longlongrightarrow> 1) at_top"
    proof -
      have "((\<lambda>y. y * x / (1 + y)) \<longlongrightarrow> x) at_top"
      proof(rule Lim_transform_eventually)
        have "((\<lambda>y. x / (1 / y + 1)) \<longlongrightarrow> x / 1) at_top"
          by(intro tendsto_divide tendsto_add')
            (use filterlim_ident real_tendsto_divide_at_top in fastforce)+
        thus "((\<lambda>y. x / (1 / y + 1)) \<longlongrightarrow> x) at_top"
          by simp
        show " \<forall>\<^sub>F y in at_top. x / (1 / y + 1) = y * x / (1 + y)"
          by(rule eventually_at_top_linorderI[where c=1])
            (smt (verit, ccfv_SIG) Groups.mult_ac(2) add_divide_eq_if_simps(1) div_by_1
              divide_divide_eq_right)
      qed
      show ?thesis
        apply(rule tendsto_add')
         apply(rule real_tendsto_divide_at_top[where c="ln x"])
          apply(rule tendsto_ln)
           apply(rule tendsto_add')
            apply(rule real_tendsto_divide_at_top[where c=1])
             apply simp
        using filterlim_ident filterlim_tendsto_add_at_top
            apply fastforce
           apply fact
          apply arith
        using filterlim_compose filterlim_ident filterlim_tendsto_add_at_top ln_at_top
         apply blast
        apply simp
        done
    qed
  next
    show " \<forall>\<^sub>F y in at_top. ln (1 / (1 + y) + y * x / (1 + y)) / ln (1 + y) + 1 =
                           ln (1 + y * x) / ln (1 + y)"
    proof(rule eventually_at_top_linorderI[where c=1])
      fix y :: real
      assume y[arith]: "1 \<le> y"
      have "ln (1 / (1 + y) + y * x / (1 + y)) / ln (1 + y) + 1
          = ln (1 / (1 + y) + y * x / (1 + y)) / ln (1 + y) + ln (1 + y) / ln (1 + y)"
        by simp
      also have "... = (ln (1 / (1 + y) + y * x / (1 + y)) + ln (1 + y)) / ln (1 + y)"
        by algebra
      also have "... = ln ((1 / (1 + y) + y * x / (1 + y)) * (1 + y)) / ln (1 + y)"
        by(subst ln_mult_pos) (auto simp add: add_sign_intros(2))
      also have "... = ln (1 + y * x) / ln (1 + y)"
        by (metis add_divide_distrib divide_cancel_right ln_0 nonzero_eq_divide_eq)
      finally show "ln (1 / (1 + y) + y * x / (1 + y)) / ln (1 + y) + 1 =
                    ln (1 + y * x) / ln (1 + y)" .
    qed
  qed
qed auto

text \<open> Exercise 2.8 of the book~\cite{Resnick}.\<close>
lemma slowly_varying_tendsto_gr_le_eq:
  fixes U :: "'a :: linordered_field \<Rightarrow> 'b::{real_normed_div_algebra, field}"
  shows "(\<forall>x>1. ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> 1) at_top)
     \<longleftrightarrow> (\<forall>x. 0 < x \<longrightarrow> x < 1 \<longrightarrow> ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> 1) at_top)"
proof safe
  assume h:"(\<forall>x>1. ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> 1) at_top)"
  fix x :: 'a
  assume x[arith]:"0 < x" "x < 1"
  then have "1 < 1 / x"
    by simp
  hence "((\<lambda>t. U (t * (1 / x)) / U t) \<longlongrightarrow> 1) at_top"
    using h by blast
  hence "((\<lambda>t. U ((t * x) * (1 / x)) / U (t * x)) \<longlongrightarrow> 1) at_top"
    by(rule filterlim_compose)
      (use x in
        "auto simp: filterlim_at_top eventually_at_top_linorder pos_divide_le_eq[of x,symmetric]")
  hence *:"((\<lambda>t. U t / U (t * x)) \<longlongrightarrow> 1 / 1) at_top"
    by simp
  thus "((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> 1) at_top"
    using tendsto_inverse[OF *] by simp
next
  assume h:"\<forall>x>0. x < 1 \<longrightarrow> ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> 1)  at_top"
  fix x :: 'a
  assume x[arith]:"1 < x"
  then have "0 < 1 / x" "1 / x < 1"
    by simp_all
  hence "((\<lambda>t. U (t * (1 / x)) / U t) \<longlongrightarrow> 1) at_top"
    using h by blast
  hence "((\<lambda>t. U ((t * x) * (1 / x)) / U (t * x)) \<longlongrightarrow> 1) at_top"
    by(rule filterlim_compose)
      (use x in
        "auto simp: filterlim_at_top eventually_at_top_linorder pos_divide_le_eq[of x,symmetric]")
  hence *:"((\<lambda>t. U t / U (t * x)) \<longlongrightarrow> 1 / 1) at_top"
    by simp
  thus "((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> 1) at_top"
    using tendsto_inverse[OF *] by simp
qed

lemma slowly_varying_iff_all_gr_1:
  assumes "L \<in> borel_measurable (restrict_space borel {0<..})"
    and "\<And>x. 0 < x \<Longrightarrow> 0 < L x"
  shows "slowly_varying L \<longleftrightarrow> (\<forall>x>1. ((\<lambda>t. L (t * x) / L t) \<longlongrightarrow> 1) at_top)"
proof
  assume h:"\<forall>x>1. ((\<lambda>t. L (t * x) / L t) \<longlongrightarrow> 1) at_top"
  show "slowly_varying L"
  proof(rule slowly_varyingI)
    fix x :: real
    have *:"x = 1 \<Longrightarrow> ((\<lambda>t. L (t * x) / L t) \<longlongrightarrow> 1) at_top"
      using assms
      by(intro tendsto_eventually eventually_at_top_linorderI[where c=1])
        (metis divide_self less_irrefl mult_1_right less_le_trans zero_less_one)
    assume "0 < x"
    then consider "0 < x" "x < 1" | "x = 1" | "1 < x"
      by linarith
    thus "((\<lambda>t. L (t * x) / L t) \<longlongrightarrow> 1) at_top"
      by cases (use h slowly_varying_tendsto_gr_le_eq assms * in auto)
  qed(use assms in auto)
qed(auto intro!: slowly_varying_lim)

lemma slowly_varying_iff_ne_1:
  assumes L_meas:"L \<in> borel_measurable (restrict_space borel {0<..})"
    and L_pos:"\<And>x. 0 < x \<Longrightarrow> 0 < L x"
    and L_mono:"mono_on {0<..} L"
  shows "slowly_varying L \<longleftrightarrow> (\<exists>x\<noteq>1. x > 0 \<and> ((\<lambda>t. L (t * x) / L t) \<longlongrightarrow> 1) at_top)"
proof safe
  fix x' :: real
  assume x'_ne1:"x' \<noteq> 1"
    and x'_pos:"0 < x'"
    and lim':"((\<lambda>t. L (t * x') / L t) \<longlongrightarrow> 1) at_top"
  have lim'':"((\<lambda>t. L (t * (1 / x')) / L t) \<longlongrightarrow> 1) at_top"
    using filterlim_compose[OF lim'
               filterlim_compose[OF filterlim_ident
                          filterlim_tendsto_pos_mult_at_top[OF _ _ filterlim_ident,
                            where c="1 / x'" and f="\<lambda>x. 1 / x'"]]]
          tendsto_inverse_real x'_pos
    by fastforce
  define x where "x \<equiv> if 1 < x' then x' else 1 / x'"
  have x1[arith]:"1 < x" and x_pos[arith]:"0 < x" and x_pos'[arith]:"0 < 1 / x" "1 / x < 1"
    using x'_ne1 x'_pos
    by(auto simp: x_def)
  have lim_x1:"((\<lambda>t. L (t * x) / L t) \<longlongrightarrow> 1) at_top"
    and lim_x2:"((\<lambda>t. L (t * (1 / x)) / L t) \<longlongrightarrow> 1) at_top"
    using lim' lim'' by(auto simp: x_def)
  have lim_y1:"((\<lambda>t. L (t * y) / L t) \<longlongrightarrow> 1) at_top"
    if y[arith]:"1 / x \<le> y" "y \<le> x" for y
    by(rule tendsto_sandwich[OF _ _ lim_x2 lim_x1])
      (auto intro!: eventually_at_top_linorderI[where c=1] less_imp_le[OF L_pos]
        divide_right_mono mono_onD[OF L_mono] mult_pos_pos simp del: times_divide_eq_right)
  have lim_y:"1 \<le> y \<Longrightarrow> y \<le> x^n \<Longrightarrow> ((\<lambda>t. L (t * y) / L t) \<longlongrightarrow> 1) at_top" for y n
  proof(induction n arbitrary: y)
    case 0
    then show ?case
      using L_pos
      by(auto intro!: tendsto_cong[THEN iffD1,OF _ tendsto_const]
          eventually_at_top_linorderI[where c=1] simp: order.strict_iff_order)
  next
    fix y n
    assume ih:"\<And>z. 1 \<le> z \<Longrightarrow> z \<le> x ^ n \<Longrightarrow>
                 ((\<lambda>t. L (t * z) / L t) \<longlongrightarrow> 1) at_top"
      and y1[arith]:"1 \<le> y" and y2:"y \<le> x ^ Suc n"
    show "((\<lambda>t. L (t * y) / L t) \<longlongrightarrow> 1) at_top"
    proof(cases "x < y")
      assume [arith]:"x < y"
      then have y:"1 \<le> y / x" "y / x \<le> x ^ n"
        using y2 by (auto simp add: cross3_simps pos_divide_le_eq)
      note lim_ih =ih[OF this]
      have 1:"\<forall>\<^sub>F t in at_top. L (t * y) / L t
                           = (L (t * (y / x)) / L t) * (L (t * y) / L (t * y * 1 / x))"
        using  y order.strict_iff_order[THEN iffD1,OF L_pos]
        by(auto intro!: eventually_at_top_linorderI[where c=1])
      have "((\<lambda>t. (L (t * (y / x)) / L t) * (L (t * y) / L (t * y * 1 / x))) \<longlongrightarrow> 1 * 1) at_top"
        using tendsto_inverse[OF filterlim_compose[OF lim_x2
              filterlim_at_top_mult_tendsto_pos[OF tendsto_const[of y] _ filterlim_ident]]]
        by(intro tendsto_mult lim_ih) simp
      thus ?thesis
        using tendsto_cong[OF 1] by auto
    qed(auto intro!: lim_y1)
  qed
  show "slowly_varying L"
  proof(safe intro!: slowly_varying_iff_all_gr_1[THEN iffD2] assms)
    fix y :: real
    assume y:"1 < y"
    then obtain n where n:"y \<le> x ^ n"
      using power_of_nat_log_ge x1 by blast
    thus "((\<lambda>t. L (t * y) / L t) \<longlongrightarrow> 1) at_top"
      using y by(auto intro!: lim_y)
  qed
qed(auto simp: slowly_varying_lim intro!: exI[where x=2])


subsection \<open>Uniform Convergence Theorem on Intervals\<close>
theorem slowly_varying_UCT:
  assumes sv:"slowly_varying L"
    and a: "0 < a"
  shows "uniform_limit {a..b} (\<lambda>t x. L (t * x) / L t) (\<lambda>x. 1) at_top"
proof(cases "a < b")
  assume a_le_b:"a < b"
  have lna_le_lnb:"ln a < ln b"
    using a_le_b a by simp
  have eb: "\<forall>\<^sub>F i in at_top.
            \<forall>x\<in>{ln a..ln b}. ln (L (exp i * exp x) / L (exp i)) \<in> {- 1..1}" (is ?eb)
    and "uniform_limit {ln a..ln b}
         (\<lambda>t x. ln (L (exp (t + x)) / L (exp t))) (\<lambda>x. 0) at_top" (is ?ul)
  proof -
    show g1:?ul
    proof(safe intro!: uniform_limitI)
      fix e :: real
      assume e:"0 < e"
      let ?h = "\<lambda>t. ln (L (exp t))"
      let ?A = "abs (ln b) + abs (ln a)"
      have A:"0 < ?A"
        using a lna_le_lnb by linarith 
      note [measurable] = regularly_varying_meas_log_exp[OF sv]
      define I where "I \<equiv> \<lambda>t. {t..t + 2 * ?A}"
      define E  where "E  \<equiv> \<lambda>t. I t \<inter> {x. e / 2 \<le> \<bar>?h x - ?h t\<bar>}"
      define E' where "E' \<equiv> \<lambda>t. I 0 \<inter> {x. e / 2 \<le> \<bar>?h (x + t) - ?h t\<bar>}"
      have [measurable]: "\<And>t. I t \<in> sets borel" "\<And>t. E t \<in> sets borel"
        "\<And>t. E' t \<in> sets borel"
        by(auto simp: E_def E'_def I_def)
      have measE_eq_measE':"measure lborel (E t) = measure lborel (E' t)" for t
      proof -
        {
          fix x
          have "x \<in> (\<lambda>x. x - t) ` E t \<longleftrightarrow> x + t \<in> (+) t ` (\<lambda>x. x - t) ` E t"
            by (simp add: image_iff)
          also have "... \<longleftrightarrow> x + t \<in> E t"
            by(auto simp: image_image)
          also have "x + t \<in> E t \<longleftrightarrow> x \<in> E' t"
            by(auto simp: E_def E'_def I_def)
          finally have "x \<in> (\<lambda>x. x - t) ` E t \<longleftrightarrow> x \<in> E' t" .
        }
        hence 1:"(\<lambda>x. x - t) ` E t = E' t"
          by blast
        have "measure lborel (E t) = measure lebesgue (E t)"
          by simp
        also have "... = measure lebesgue ((\<lambda>x. x - t) ` E t)"
          by(simp add: measure_translation_subtract)
        also have "... = measure lebesgue (E' t)"
          by (simp add: 1)
        also have "... = measure lborel (E' t)"
          by simp
        finally show ?thesis .
      qed
      have "((\<lambda>t. integral\<^sup>L lborel (indicat_real (E' t)))
               \<longlongrightarrow> integral\<^sup>L lborel (\<lambda>x::real. 0)) at_top"
      proof(rule integral_dominated_convergence_real)
        show "AE x in lborel. norm (indicat_real (E' t) (x :: real)) 
                              \<le> indicat_real {0..2 * ?A} x" for t
          by(auto simp: E'_def I_def indicator_def)
      next
        have "\<forall>\<^sub>F t in at_top. \<bar>?h (x + t) - ?h t\<bar> < e / 2" for x
          using tendstoD[OF tendsto_rabs[OF regularly_varying_ln_exp[OF sv,of x]]
                half_gt_zero[OF e]]
          by(simp add: dist_real_def add.commute)
        then obtain T where T:"\<And>x t. T x \<le> t \<Longrightarrow> \<bar>?h (x + t) - ?h t\<bar> < e / 2"
          unfolding eventually_at_top_linorder by meson
        hence "\<forall>\<^sub>F t in at_top. indicat_real (E' t) x = 0" for x
          unfolding eventually_at_top_linorder
          by(fastforce intro!: exI[where x="T x"] simp: indicator_def E'_def)
        hence "((\<lambda>t. indicat_real (E' t) x) \<longlongrightarrow> 0) at_top" for x
          by (simp add: tendsto_eventually)
        thus "AE x in lborel. ((\<lambda>t. indicat_real (E' t) x) \<longlongrightarrow> 0) at_top"
          by blast
      qed (auto simp: emeasure_lborel_Icc_eq)
      from tendstoD[OF this min_less_iff_conj[THEN iffD2
          ,OF conjI[OF half_gt_zero[OF e] half_gt_zero[OF A]]]]
      obtain t0 where t0:"\<And>t. t0 \<le> t \<Longrightarrow> measure lborel (E t) < min (e / 2) (?A / 2)"
        unfolding measE_eq_measE' dist_real_def eventually_at_top_linorder
        by auto
      show "\<forall>\<^sub>F i in at_top. \<forall>x\<in>{ln a..ln b}. dist (ln (L (exp (i + x)) / L (exp i))) 0 < e"
      proof(safe intro!: eventually_at_top_linorderI[where c="t0 + \<bar>ln b\<bar> + \<bar>ln a\<bar>"])
        fix t x
        assume t:"t0 + \<bar>ln b\<bar> + \<bar>ln a\<bar> \<le> t" and x:"x \<in> {ln a..ln b}"
        have "(I (t + x) \<inter> I t) - (E (t + x) \<union> E t) \<noteq> {}"
        proof
          assume ne:"I (t + x) \<inter> I t - (E (t + x) \<union> E t) = {}"
          have "0 \<le> x \<Longrightarrow> I (t + x) \<inter> I t = {t + x ..t + 2*?A}"
               "x \<le> 0 \<Longrightarrow> I (t + x) \<inter> I t = {t..t + x + 2*?A}"
            unfolding Int_atLeastAtMost I_def using x lna_le_lnb by force+
          hence "0 \<le> x \<Longrightarrow> measure lborel (I (t + x) \<inter> I t) = 2 * ?A - x"
                "x \<le> 0 \<Longrightarrow> measure lborel (I (t + x) \<inter> I t) = 2 * ?A + x"
            using x lna_le_lnb by auto
          hence *:"measure lborel (I (t + x) \<inter> I t) \<ge> ?A"
            using x by fastforce
          have "measure lborel (E (t + x) \<union> E t)
                \<le> measure lborel (E (t + x)) + measure lborel (E t)"
            by(simp add: measure_Un_le)
          also have "... < ?A / 2 + ?A / 2"
            by(rule add_strict_mono)
              (use t0[of t] t t0[of "t + x"] x in fastforce)+
          finally have **:"measure lborel (E (t + x) \<union> E t) < ?A"
            by argo
          have "0 = ?A - ?A"
            by simp
          also have "... < measure lborel (I (t + x) \<inter> I t) - measure lborel (E (t + x) \<union> E t)"
            using * ** by argo
          also have "... \<le> measure lborel ((I (t + x) \<inter> I t) - (E (t + x) \<union> E t))"
            by (metis Diff_Diff_Int E_def I_def \<open>\<And>t. E t \<in> sets borel\<close>
                \<open>\<And>t. I t \<in> sets borel\<close> compact_Icc fmeasurable.Un fmeasurableI2
                fmeasurable_compact inf_le1 measure_diff_le_measure_setdiff
                sets.Diff sets_lborel)
          also have "... = 0"
            unfolding ne by simp
          finally show False
            by simp
        qed
        then obtain k where k:"k \<in> I (t + x)" "k \<in> I t"
          "k \<notin> {y. e / 2 \<le> \<bar>?h y - ?h (t + x)\<bar>}" "k \<notin> {y. e / 2 \<le> \<bar>?h y - ?h t\<bar>}"
          unfolding E_def by blast
        have "\<bar>ln (L (exp (t + x)) / L (exp t)) - 0\<bar> = \<bar>?h (t + x) - ?h t\<bar>"
          by(auto intro!: ln_divide_pos arg_cong[where f=abs] regularly_varying_pos[OF sv])
        also have "... \<le> \<bar>?h k - ?h (t + x) \<bar> + \<bar>?h k - ?h t\<bar>"
          by force
        also have "... < e / 2 + e / 2"
          by(intro add_strict_mono) (use k in fastforce)+ 
        finally show "dist (ln (L (exp (t + x)) / L (exp t))) 0 < e"
          by (simp add: dist_real_def)
      qed
    qed
    show ?eb
      by(rule eventually_mono[OF  uniform_limitD[OF g1,of 1]])
        (auto simp:  exp_add)
  qed
  hence "uniform_limit {ln a..ln b} (\<lambda>t x. ln (L (exp t * exp x) / L (exp t))) (\<lambda>x. 0) at_top"
    by (simp add: exp_add)
  hence "uniform_limit {ln a..ln b}
          (\<lambda>i x. exp (ln (L (exp i * exp x) / L (exp i)))) (\<lambda>x. exp 0) at_top"
    by(safe intro!: compact_uniformly_continuous continuous_on_exp
        eb uniform_limit_compose_uniformly_continuous_on[where B="{-1..1}" and g' = "\<lambda>x. 0"])
      auto
  hence "uniform_limit {ln a..ln b} (\<lambda>i x. L (exp i * exp x) / L (exp i)) (\<lambda>x. 1) at_top"
    using exp_ln[OF divide_pos_pos[OF regularly_varying_pos[OF sv] regularly_varying_pos[OF sv]]]
    by auto
  hence "uniform_limit {a..b} (\<lambda>i x. L (exp i * exp (ln x)) / L (exp i)) (\<lambda>x. 1) at_top"
    using uniform_limit_compose'[where A="{ln a..ln b}"
        and f="\<lambda>i x. L (exp i * exp x) / L (exp i)"
        and g="\<lambda>x. 1" and h=ln and B="{a..b}"] a by auto
  hence "uniform_limit {a..b} (\<lambda>i x. L (exp i * x) / L (exp i)) (\<lambda>x. 1) at_top"
    by(intro uniform_limit_cong[of _ _ "\<lambda>i x. L (exp i * x) / L (exp i)",THEN iffD1])
      (use a in auto)
  hence "uniform_limit {a..b} (\<lambda>i x. L (exp (ln i) * x) / L (exp (ln i))) (\<lambda>x. 1) at_top"
    by(intro filterlim_compose[OF _ ln_at_top])
  thus "uniform_limit {a..b} (\<lambda>i x. L (i * x) / L i) (\<lambda>x. 1) at_top"
    by(intro uniform_limit_cong[of _ _ "\<lambda>i x. L (i * x) / L i",THEN iffD1]
        eventually_at_top_linorderI[where c=1]) auto
next
  assume "\<not> a < b"
  then consider "a = b" | "b < a"
    by fastforce
  thus ?thesis
    by cases (use a slowly_varying_lim[OF sv] in auto)
qed

corollary regularly_varying_UCT_interval:
  assumes sv:"regularly_varying U \<rho>"
    and a: "0 < a"
  shows "uniform_limit {a..b} (\<lambda>t x. U (t * x) / U t) (\<lambda>x. x powr \<rho>) at_top"
proof -
  obtain L where L_sv: "slowly_varying L"
    and eq_L: "\<And>x. 0 < x \<Longrightarrow> U x = x powr \<rho> * L x"
    using regularly_varying_decomp[OF sv] by blast
  have 1:"uniform_limit {a..b} (\<lambda>t x. x powr \<rho> * (L (t * x) / L t)) (\<lambda>x. x powr \<rho> * 1) at_top"
    by(intro uniform_lim_mult_bdd1[OF slowly_varying_UCT] assms L_sv
        compact_imp_bounded compact_continuous_image continuous_on_powr)
      (use a in auto)
  have 2:"uniform_limit {a..b} (\<lambda>t x. (x powr \<rho> * t powr \<rho> * L (t * x) / (t powr \<rho> * L t)))
                             (\<lambda>x. x powr \<rho>) at_top"
    by(auto intro!: uniform_limit_cong[THEN iffD1,OF _ _ 1] eventually_at_top_linorderI[of 1])
  show ?thesis
    using a
    by(auto intro!: uniform_limit_cong[THEN iffD1,OF _ _ 2] eventually_at_top_linorderI[of 1]
        simp: powr_mult eq_L)
qed

corollary regularly_varying_UCT_interval_ln_exp:
  assumes rv:"regularly_varying U \<rho>"
  defines "h \<equiv> \<lambda>x. ln (U (exp x))"
  shows "uniform_limit {a..b} (\<lambda>t x. h (t + x) - h t) (\<lambda>x. \<rho> * x) at_top"
proof -
  have 1:"uniform_limit {exp a..exp b} (\<lambda>t x. U (t * x) / U t) (\<lambda>x. x powr \<rho>) at_top"
    by(auto intro!: regularly_varying_UCT_interval[OF rv])
  have "uniform_limit {exp a..exp b} (\<lambda>t x. ln (U (t * x) / U t)) (\<lambda>x. ln (x powr \<rho>)) at_top"
  proof(intro uniform_limit_compose_uniformly_continuous_on[OF 1]
              uniform_limit_eventually_in[OF regularly_varying_UCT_interval[OF rv]])
    define e where "e \<equiv> min (exp (a * \<rho>)) (exp (b * \<rho>))"
    have e:"0 < e"
      by(simp add: e_def)
    define e' where "e' \<equiv> e / 2"
    have e':"e' < e" "0 < e'"
      using dense e'_def e by auto
    have pos:"0 < min (exp (a * \<rho>)) (exp (b * \<rho>)) - e'"
      using e' by(auto simp: e_def)
    thus "uniformly_continuous_on
            {min (exp (a * \<rho>)) (exp (b * \<rho>)) - e'..max (exp (a * \<rho>)) (exp (b * \<rho>)) + e'} ln"
          (is "uniformly_continuous_on ?B ln")
      using e' by(auto intro!: continuous_on_ln compact_uniformly_continuous)
    show "0 < e'"
      by fact
    fix x y
    assume x:"x \<in> {exp a .. exp b}"
      and d:"dist (x powr \<rho>) y < e'"
    have a_le_b:"a \<le> b"
      by(rule ccontr) (use x in auto)
    have xin:"x powr \<rho> \<in> {min (exp (a * \<rho>)) (exp (b * \<rho>))..max (exp (a * \<rho>)) (exp (b * \<rho>))}"
      (is "_ \<in> ?C")
    proof(cases "0 \<le> \<rho>")
      assume h:"0 \<le> \<rho>"
      then have mono:"mono_on {exp a .. exp b} (\<lambda>x. x powr \<rho>)"
        by(auto intro!: mono_onI powr_mono2 order.trans[OF exp_ge_zero])
      have 1:"min (exp (a * \<rho>)) (exp (b * \<rho>)) = exp (a * \<rho>)"
        and 2: "max (exp (a * \<rho>)) (exp (b * \<rho>)) = exp (b * \<rho>)"
        using h a_le_b by (simp_all add: mult_le_cancel_right)
      have "(\<lambda>x. x powr \<rho>) ` {exp a .. exp b} = {exp (a * \<rho>) .. exp (b * \<rho>)}"
        unfolding exp_powr_real[symmetric]
        by(intro image_mono_on_continuous_on_Icc mono continuous_on_powr)
          (use a_le_b in auto)
      thus ?thesis
        using x by(auto simp: 1 2)
    next
      assume h:"\<not> 0 \<le> \<rho>"
      then have mono:"mono_on {exp a .. exp b} (\<lambda>x. - (x powr \<rho>))"
        by(intro mono_onI)
          (metis atLeastAtMost_iff basic_trans_rules(22) exp_gt_zero neg_le_iff_le nle_le
            powr_mono2')
      have 1:"min (exp (a * \<rho>)) (exp (b * \<rho>)) = exp (b * \<rho>)"
        and 2: "max (exp (a * \<rho>)) (exp (b * \<rho>)) = exp (a * \<rho>)"
        using h a_le_b by (simp_all add: mult_le_cancel_right)
      have "(\<lambda>x. x powr \<rho>) ` {exp a .. exp b} = uminus ` (\<lambda>x. - (x powr \<rho>)) ` {exp a .. exp b}"
        by force
      also have "... = uminus ` {- (exp (a * \<rho>))..- (exp (b * \<rho>))}"
        unfolding exp_powr_real[symmetric]
        by(intro image_mono_on_continuous_on_Icc mono continuous_on_minus
                 continuous_on_powr arg_cong[where f="(`) uminus"])
          (use a_le_b in auto)
      also have "... = {exp (b * \<rho>) .. exp (a * \<rho>)}"
        by auto
      finally show ?thesis
        using x by(auto simp: 1 2)
    qed
    show "y \<in> ?B"
      using xin d by(auto simp: dist_real_def)
  qed auto
  hence "uniform_limit {exp a..exp b}
          (\<lambda>t x. ln (U (exp t * x) / U (exp t))) (\<lambda>x. \<rho> * ln x) at_top"
    using filterlim_compose[OF _ exp_at_top] by auto
  hence "uniform_limit {a..b}
          (\<lambda>t x. ln (U (exp t * exp x) / U (exp t))) (\<lambda>x. \<rho> * ln (exp x)) at_top"
    by(intro uniform_limit_compose'[where h=exp]) auto
  hence "uniform_limit {a..b} (\<lambda>t x. ln (U (exp (t + x)) / U (exp t))) (\<lambda>x. \<rho> * x) at_top"
    by (simp add: exp_add)
  thus "uniform_limit {a..b} (\<lambda>t x. h (t + x) - h t) (\<lambda>x. \<rho> * x) at_top"
    using regularly_varying_pos[OF rv exp_gt_zero] ln_divide_pos
    by(simp add: h_def cong: uniform_limit_cong')
qed

corollary slowly_varying_UCT_interval_ln_exp:
  assumes sv:"slowly_varying L"
  defines "h \<equiv> \<lambda>x. ln (L (exp x))"
  shows "uniform_limit {a..b} (\<lambda>t x. h (t + x) - h t) (\<lambda>x. 0) at_top"
  using regularly_varying_UCT_interval_ln_exp[OF sv] by(simp add: h_def)

corollary regularly_varying_compose:
  assumes rv1:"regularly_varying U \<rho>"
    and rv2:"regularly_varying V \<eta>"
    and lim:"filterlim U at_top at_top"
  shows "regularly_varying (\<lambda>x. V (U x)) (\<rho> * \<eta>)"
proof(rule regularly_varyingI)
  fix x ::real
  assume x:"0 < x"
  hence "x powr \<rho> > 0"
    by simp
  then obtain i where i_pos:"0 < i" and i: "0 < x powr \<rho> - i"
    by (meson diff_gt_0_iff_gt field_lbound_gt_zero)
  show "((\<lambda>t. V (U (t * x)) / V (U t)) \<longlongrightarrow> x powr (\<rho> * \<eta>)) at_top"
    unfolding tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e:"0 < e"
    from regularly_varying_UCT_interval[OF rv2 i,of "x powr \<rho> + i"] half_gt_zero[OF e]
    obtain Tv where Tv:"\<And>y t. Tv \<le> t \<Longrightarrow> x powr \<rho> - i \<le> y \<Longrightarrow> y \<le> x powr \<rho> + i
      \<Longrightarrow> \<bar>V (t * y) / V t - y powr \<eta>\<bar> < e / 2"
      unfolding uniform_limit_iff dist_real_def eventually_at_top_linorder
      by (meson atLeastAtMost_iff)
    obtain T1 where T1:"\<And>t. T1 \<le> t \<Longrightarrow> Tv \<le> U t"
      using lim unfolding filterlim_at_top eventually_at_top_linorder
      by fastforce
    obtain T2 where T2:"\<And>t. T2 \<le> t \<Longrightarrow> \<bar>U (t * x) / U t - x powr \<rho>\<bar> < i"
      using regularly_varying_lim[OF rv1 x] i_pos
      by(fastforce simp: tendsto_iff eventually_at_top_linorder dist_real_def)
    obtain T3 where T3:"\<And>t. T3 \<le> t \<Longrightarrow> \<bar>(U (t * x) / U t) powr \<eta> -  x powr (\<rho> * \<eta>)\<bar> < e / 2"
      using tendstoD[OF tendsto_powr[OF regularly_varying_lim[OF rv1 x]
            tendsto_const[of \<eta>]] half_gt_zero[OF e]]
            x
      by(fastforce simp: eventually_at_top_linorder powr_powr dist_real_def)
    define T where "T \<equiv> max (max 1 T1) (max T2 T3)"
    show " \<forall>\<^sub>F t in at_top. \<bar>V (U (t * x)) / V (U t) - x powr (\<rho> * \<eta>)\<bar> < e"
    proof(safe intro!: eventually_at_top_linorderI[where c=T])
      fix t
      assume t:"T \<le> t"
      then have t_pos:"0 < t" and Tvt:"Tv \<le> U t"
        and ti:"\<bar>U (t * x) / U t - x powr \<rho>\<bar> < i"
        and tpowr:"\<bar>(U (t * x) / U t) powr \<eta> -  x powr (\<rho> * \<eta>)\<bar> < e / 2"
        using T1 T2 T3 by(auto simp: T_def)
      have "\<bar>V (U (t * x)) / V (U t) - x powr (\<rho> * \<eta>)\<bar>
             = \<bar>V (U t * (U (t * x) / U t)) / V (U t) - x powr (\<rho> * \<eta>)\<bar>"
        using regularly_varying_pos[OF rv1 t_pos] by simp
      also have "... \<le> \<bar>V (U t * (U (t * x) / U t)) / V (U t) - (U (t * x) / U t) powr \<eta>\<bar>
                        + \<bar>(U (t * x) / U t) powr \<eta> - x powr (\<rho> * \<eta>)\<bar>"
        by linarith
      also have "... < e / 2 + e / 2"
        using ti by(intro add_strict_mono tpowr Tv Tvt) auto
      finally show "\<bar>V (U (t * x)) / V (U t) - x powr (\<rho> * \<eta>)\<bar> < e"
        by argo
    qed
  qed
qed(use measurable_compose[OF
      measurable_restrict_space2[OF _ regularly_varying_meas[OF rv1]]
      regularly_varying_meas[OF rv2]]
  in "auto intro!: regularly_varying_pos[OF rv1] regularly_varying_pos[OF rv2]")


lemma
  assumes sv:"slowly_varying L"
  defines "h \<equiv> \<lambda>x. ln (L (exp x))"
  shows slowly_varying_eventually_bounded_interval:
    "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. bounded (L ` {a..b})"
    and slowly_varying_eventually_bounded_interval_strong:
    "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. \<exists>A>0. \<exists>B. L ` {a..b} \<subseteq> {A..B}"
    and slowly_varying_eventually_bounded_interval_ln_exp:
    "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. bounded (h ` {a..b})"
proof -
  have "\<exists>T::real. \<forall>t\<ge>T. \<forall>n. t \<le> T + Suc n \<longrightarrow> \<bar>h t\<bar> < Suc n + \<bar>h T\<bar>"
  proof -
    from uniform_limitD[where e=1,OF slowly_varying_UCT_interval_ln_exp[OF sv,of 0 1]]
    obtain T where T':"\<And>t x. t \<ge> T \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> \<bar>h (t + x) - h t\<bar> < 1"
      by(fastforce simp: eventually_at_top_linorder h_def)
    have "\<And>t. T \<le> t \<Longrightarrow> t \<le> T + Suc n \<Longrightarrow> \<bar>h t\<bar> < Suc n + \<bar>h T\<bar>" for n
    proof(induction n)
      case ih:(Suc n')
      then consider "t \<le> T + Suc n'" | "T + Suc n' \<le> t" "t \<le> T + Suc (Suc n')"
        by argo
      thus ?case
      proof cases
        assume t:"T + Suc n' \<le> t" "t \<le> T + Suc (Suc n')"
        define t' where "t' \<equiv> t - 1"
        have t':"T \<le> t'" "t' \<le> T + Suc n'"
          using t by(auto simp: t'_def)
        then have "\<bar>h t\<bar> < 1 + \<bar>h t'\<bar>"
          using T'[of t' 1] by(simp add: t'_def)
        also have "... < real (Suc (Suc n')) + \<bar>h T\<bar>"
          using ih t' by fastforce
        finally show ?thesis .
      qed(use ih in fastforce)
    qed(use T'[of T "_ - T"] in fastforce)
    thus ?thesis
      by blast
  qed
  then obtain T :: real where T:"\<And>t n. T \<le> t \<Longrightarrow> t \<le> T + Suc n \<Longrightarrow> \<bar>h t\<bar> < Suc n + \<bar>h T\<bar>"
    by fast
  show h:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. bounded (h ` {a..b})"
  proof(intro eventually_at_top_linorderI[where c=T] allI impI)
    fix t a b :: real
    assume tab:"T \<le> t" "t \<le> a" "a \<le> b"
    then obtain N where N:"b \<le> T + Suc N"
      by (metis Multiseries_Expansion.intyness_simps(5) add.commute
          add_mono_thms_linordered_semiring(1) arithmetic_simps(49) diff_le_eq
          not0_implies_Suc of_nat_0_le_iff real_arch_simple)
    show "bounded (h ` {a..b})"
      using tab N
      by(auto intro!: boundedI[where B="Suc N + \<bar>h T\<bar>"]
          less_imp_le[of _ "Suc N + \<bar>h T\<bar>"] T simp del: of_nat_Suc)
  qed
  have *:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. \<exists>A>0. \<exists>B. (\<lambda>x. L (exp x)) ` {a..b} \<subseteq> {A..B}"
  proof(safe intro!: eventually_mono[OF h])
    fix t a b
    assume "\<forall>a\<ge>t. \<forall>b\<ge>a. bounded (h ` {a..b})"
      and "t \<le> a" "a \<le> b"
    then obtain A B where AB:"h ` {a..b} \<subseteq> {A..B}"
      unfolding bounded_subset_cball cball_eq_atLeastAtMost by blast
    show "\<exists>A>0. \<exists>B. (\<lambda>x. L (exp x)) ` {a..b} \<subseteq> {A..B}"
      by(intro exI[where x="exp A"] conjI[OF _ exI[where x="exp B"]] image_subsetI exp_gt_zero)
        (metis AB regularly_varying_pos[OF sv exp_gt_zero] h_def
          atLeastAtMost_iff exp_le_cancel_iff exp_ln_iff image_subset_iff) 
  qed
  then obtain T  where T:
  "\<And>a b. T \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow> \<exists>A>0. \<exists>B. (\<lambda>x. L (exp x)) ` {a..b} \<subseteq> {A..B}"
    unfolding eventually_at_top_linorder by metis
  have **:"a \<le> b \<Longrightarrow> exp ` {a..b} = {exp a..exp b}" for a b :: real
    by(intro image_mono_on_continuous_on_Icc)
      (auto intro!: continuous_on_exp ord.mono_onI)
  show ***:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. \<exists>A>0. \<exists>B. L ` {a..b} \<subseteq> {A..B}"
  proof(safe intro!: eventually_at_top_linorderI[where c="exp T"])
    fix t a b :: real
    assume tab:"exp T \<le> t" "t \<le> a" "a \<le> b"
    hence tab0:"0 < t" "0 < a" "0 < b"
      using exp_gt_zero[of T] by linarith+
    hence lnab:"T \<le> ln a" "ln a \<le> ln b"
      using tab ln_ge_iff by(auto intro!: ln_mono)
    then obtain A B where AB:"0 < A" "(\<lambda>x. L (exp x)) ` {ln a..ln b} \<subseteq> {A..B}"
      using T by meson
    moreover have "(\<lambda>x. L (exp x)) ` {ln a..ln b} = L ` {a..b}"
      unfolding h_def image_image[symmetric]
      by(simp add: ** lnab tab0)
    ultimately show "\<exists>A>0. \<exists>B. L ` {a..b} \<subseteq> {A..B}"
      by fast
  qed
  show "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. bounded (L ` {a..b})"
    by(intro eventually_mono[OF ***])
      (meson bounded_closed_interval bounded_subset)
qed

lemma
  assumes rv:"regularly_varying U \<rho>"
  defines "h \<equiv> \<lambda>x. ln (U (exp x))"
  shows regularly_varying_eventually_bounded_interval:
    "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. bounded (U ` {a..b})"
    and regularly_varying_eventually_bounded_interval_strong:
    "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. \<exists>A>0. \<exists>B. U ` {a..b} \<subseteq> {A..B}"
    and regularly_varying_eventually_bounded_interval_ln_exp:
    "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. bounded (h ` {a..b})"
    and regularly_varying_eventually_locally_integrable:
    "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. set_integrable lborel {a..b} U"
    and regularly_varying_eventually_locally_integrable_ln_exp:
    "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. set_integrable lborel {a..b} h"
proof -
  define L where "L \<equiv> \<lambda>x. U x / x powr \<rho>"
  define h' where "h' \<equiv> \<lambda>x. ln (L (exp x))"
  have sv:"slowly_varying L"
    by(simp add: regularly_varying_iff_slowly_varying_divide_powr[of U,symmetric] L_def rv)
  have U_L:"\<And>x. 0 < x \<Longrightarrow> U x = x powr \<rho> * L x"
    by(auto simp: L_def)
  have h_h':"h = (\<lambda>x. \<rho> * x + h' x)"
    using regularly_varying_pos[OF sv exp_gt_zero]
    by(auto simp add: h'_def h_def U_L ln_mult less_le)
  hence 1:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. bounded (L ` {a..b})"
    and 2:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. \<exists>A>0. \<exists>B. L ` {a..b} \<subseteq> {A..B}"
    and 3:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. bounded (h' ` {a..b})"
    using slowly_varying_eventually_bounded_interval
          slowly_varying_eventually_bounded_interval_strong
          slowly_varying_eventually_bounded_interval_ln_exp sv
    by(auto simp: h'_def)
  have *:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. bounded (L ` {a..b})"
    by(intro eventually_mono[OF 1])
      (metis atLeastatMost_empty_iff2 bounded_closed_interval image_empty)
  have **:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. \<exists>A>0. \<exists>B. L ` {a..b} \<subseteq> {A..B}"
    by(intro eventually_mono[OF 2])
      (metis atLeastatMost_empty' empty_iff exp_gt_zero image_subset_iff)
  have ***:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. bounded (h' ` {a..b})"
    by(intro eventually_mono[OF 3])
      (metis atLeastatMost_empty_iff2 bounded_closed_interval image_empty)+
  have bdd1:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. bounded ((\<lambda>x. x powr \<rho>) ` {a..b})"
    by(auto intro!: compact_imp_bounded compact_continuous_image continuous_on_powr
        eventually_at_top_linorderI[where c=1])
  have bdd2:"bounded ((\<lambda>x. \<rho> * x) ` {a..b})" for a b
    by (metis bounded_closed_interval bounded_scaling image_cong real_scaleR_def)
  have U':"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. bounded ((\<lambda>x. x powr \<rho> * L x) ` {a..b})"
    by(intro eventually_mono[OF eventually_conj[OF * bdd1]] bounded_times_comp allI impI)
       auto
  show g1:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. bounded (U ` {a..b})"
  proof(intro eventually_at_top_linorderI[where c=1,THEN eventually_mp[OF _ U']] impI allI)
    fix x a b :: real
    assume h:"1 \<le> x" "\<forall>a\<ge>x. \<forall>b. bounded ((\<lambda>x. x powr \<rho> * L x) ` {a..b})" "x \<le> a"
    then have "(\<lambda>x. x powr \<rho> * L x) ` {a..b} = U ` {a..b}"
      using U_L by auto
    thus "bounded (U ` {a..b})"
      using h by metis
  qed
  show g2:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. bounded (h ` {a..b})"
    using bdd2 by(auto simp: h_h' intro!: bounded_plus_comp eventually_mono[OF ***])
  show "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. set_integrable lborel {a..b} U"
  proof(safe intro!: eventually_at_top_linorderI[where c=1,THEN eventually_mp[OF _ g1]])
    fix a b x :: real
    assume h:"1 \<le> x" "\<forall>a\<ge>x. \<forall>b. bounded (U ` {a..b})" "x \<le> a"
    then obtain K where "\<forall>x\<in>{a..b}. \<bar>U x\<bar> \<le> K"
      by(fastforce simp: bounded_iff)
    thus "set_integrable lborel {a..b} U"
      using regularly_varying_meas_Icc[OF rv] h
      by(auto simp: set_integrable_def emeasure_lborel_Icc_eq
          intro!: integrableI_bounded_set[where A="{a..b}" and B=K])
  qed
  show "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. set_integrable lborel {a..b} h"
  proof(safe intro!: eventually_mono[OF g2])
    fix a b x :: real
    assume h:"\<forall>a\<ge>x. \<forall>b. bounded (h ` {a..b})" "x \<le> a"
    then obtain K where "\<forall>x\<in>{a..b}. \<bar>h x\<bar> \<le> K"
      by(fastforce simp: bounded_iff)
    thus "set_integrable lborel {a..b} h"
      using regularly_varying_meas_log_exp[OF rv]
      by(auto simp: set_integrable_def emeasure_lborel_Icc_eq h_def
          intro!: integrableI_bounded_set[where A="{a..b}" and B=K])
  qed
  have ****:"\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b\<ge>a. \<exists>A>0. \<exists>B. U ` {a..b} \<subseteq> {A..B}"
  proof(safe intro!: eventually_mp[OF eventually_at_top_linorderI[of 1] **])
    fix x a b :: real
    assume xab:"1 \<le> x" "x \<le> a" "a \<le> b" "\<forall>a\<ge>x. \<forall>b. \<exists>A>0. \<exists>B. L ` {a..b} \<subseteq> {A..B}"
    then obtain A B where A:"A > 0" and AB:"L ` {a..b} \<subseteq> {A..B}"
      by blast
    have a:"0 < a"
      using xab by linarith
    have "\<exists>C>0. \<exists>D. (\<lambda>x. x powr \<rho>) ` {a..b} = {C..D}"
    proof(cases "0 \<le> \<rho>")
      assume "0 \<le> \<rho>"
      then have "(\<lambda>x. x powr \<rho>) ` {a..b} = {a powr \<rho>..b powr \<rho>}"
        using xab
        by(intro image_mono_on_continuous_on_Icc xab mono_onI
            powr_mono2 continuous_on_powr) auto
      thus ?thesis
        using a
        by(intro exI[where x="a powr \<rho>"] conjI[OF _ exI[where x="b powr \<rho>"]]) auto
    next
      assume "\<not> 0 \<le> \<rho>"
      then have "(\<lambda>x. x powr \<rho>) ` {a..b} = {b powr \<rho>..a powr \<rho>}"
        using xab
        by(intro image_antimono_on_continuous_on_Icc monotone_onI powr_mono2'
            continuous_on_powr) auto
      thus ?thesis
        using xab
        by(intro exI[where x="b powr \<rho>"] conjI[OF _ exI[where x="a powr \<rho>"]]) auto
    qed
    then obtain C D where CD:"0 < C" "(\<lambda>x. x powr \<rho>) ` {a..b} = {C..D}"
      by blast
    have "U ` {a..b} \<subseteq> (\<lambda>(x, y). x * y) ` ((\<lambda>x. x powr \<rho>) ` {a..b} \<times> L ` {a..b})"
      using a U_L by auto
    also have "... \<subseteq> (\<lambda>(x, y). x * y) ` ({C..D} \<times> {A..B})"
      using AB CD by fast
    also have "... \<subseteq> {C*A..D*B}"
      using A CD mult_mono by fastforce
    finally show "\<exists>A>0. \<exists>B. U ` {a..b} \<subseteq> {A..B}"
      using A CD by(intro exI[where x="C*A"]) auto
  qed
  show "\<forall>\<^sub>F x in at_top. \<forall>a\<ge>x. \<forall>b. \<exists>A>0. \<exists>B. U ` {a..b} \<subseteq> {A..B}"
    by(rule eventually_mono[OF ****])
      (metis atLeastatMost_empty_iff dual_order.refl empty_iff image_subset_iff)
qed

(* TODO: compare this proof and book's proof *)
subsection \<open>Weakening the Definition of Regularly Varying Functions \<close>
text \<open>We prove Proposition 2.3 in \cite{Resnick}.
      In the definition of a regularly varying function,
      $U(tx)/U(t)$ needs to converge to $x^\rho$ as $t\to\infty$.
      However, we can weaken this assumption to: $U(tx)/U(t)$
      converges to some function $h$.\<close>
lemma
  assumes [measurable]:"U \<in> borel_measurable (restrict_space borel {0<..})"
    and U:"\<And>x. 0 < x \<Longrightarrow> 0 < U x"
    and lim:"\<And>x. x > 0 \<Longrightarrow> ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> h x) at_top"
  shows divide_limit_power:"\<And>x. x > 0 \<Longrightarrow> h x = x powr ln (h (exp 1))"
    and divide_limit_imp_regularly_varying:"regularly_varying U (ln (h (exp 1)))"
    and divide_limit_imp_regularly_varying_ex:"\<exists>\<rho>. regularly_varying U \<rho>"
proof -
  have lim':"0 < x \<Longrightarrow> 0 < y \<Longrightarrow>
           ((\<lambda>t. U (t * x * y) / U (t * x)) \<longlongrightarrow> h y) at_top" for x y
    by(rule filterlim_compose[of _ _ at_top "\<lambda>t. t * x"])
       (auto intro!: lim eventually_at_top_linorderI[where c="_ / x"]
         simp: divide_le_eq filterlim_at_top)
  have cong:"\<And>x y. 0 < x \<Longrightarrow> 0 < y \<Longrightarrow>
           \<forall>\<^sub>F t in at_top. U (t * (x * y)) / U t
                           = U (t * x) / U t * (U (t * x * y) / U (t * x))"
    using U by(intro eventually_at_top_linorderI[where c=1])
              (simp add: mult.assoc less_le)
  have lim1:"\<And>x y. 0 < x \<Longrightarrow> 0 < y \<Longrightarrow>
                 ((\<lambda>t. U (t * (x * y)) / U t) \<longlongrightarrow> h (x * y)) at_top"
    using lim by simp
  have lim2:"\<And>x y. 0 < x \<Longrightarrow> 0 < y \<Longrightarrow>
                  ((\<lambda>t. U (t * x) / U t * (U (t * x * y) / U (t * x))) \<longlongrightarrow> h x * h y) at_top"
    by(intro tendsto_mult lim lim') simp_all
  have h_eq:"0 < x \<Longrightarrow> 0 < y \<Longrightarrow> h (x * y) = h x * h y" for x y
    using lim1[of x y] lim2[of x y]
    by(intro tendsto_unique) (auto simp: tendsto_cong[OF cong[of x y]])
  have [measurable]:"(*) r \<in> restrict_space borel {0::real<..} \<rightarrow>\<^sub>M restrict_space borel {0<..}"
    if r:"r > 0" for r
    using r by(auto intro!: measurable_restrict_space3)
  have h_meas[measurable]:"h \<in> borel_measurable (restrict_space borel {0<..})"
    by(rule borel_measurable_LIMSEQ_metric_at_top[where f="\<lambda>t x. U (t * x) / U t" and K=1])
      (auto intro!: lim)
  have h_pos:"0 < h x" if x:"0 < x" for x
  proof(rule ccontr)
    assume cc:"\<not> 0 < h x"
    moreover have "0 \<le> h x"
      by(rule tendsto_lowerbound[OF lim[OF x]])
        (use U in "auto intro!: eventually_at_top_linorderI[where c=1]
                                order.strict_implies_order simp: x")
    ultimately have "h x = 0"
      by linarith
    hence "h 1 = 0"
      using h_eq[of x "1 / x"] x by simp
    hence "((\<lambda>t. U t / U t) \<longlongrightarrow> 0) at_top"
      using lim[of 1] by auto
    moreover have "((\<lambda>t. U t / U t) \<longlongrightarrow> 1) at_top"
      by(intro tendstoI eventually_at_top_linorderI[where c=1])
        (metis U dist_self divide_self less_irrefl order_less_le_trans zero_less_one)
    ultimately show False
      using tendsto_unique by force
  qed
  hence "h 1 = 1"
    using h_eq[of 1 1] by (metis less_irrefl mult_cancel_right1 zero_less_one)
  define g where "g \<equiv> \<lambda>r. ln (h (exp r))"
  have g_meas:"g \<in> borel_measurable borel"
    unfolding g_def
    by(rule measurable_compose[where N=borel,OF measurable_compose
          [where g=h and N="restrict_space borel {0<..}"]])
      (auto simp: measurable_restrict_space2_iff)
  have g_eq:"g (x + y) = g x + g y" for x y
    by(simp add: g_def exp_add h_eq[OF exp_gt_zero exp_gt_zero] ln_mult_pos[OF h_pos h_pos])
  have "g = (\<lambda>x. x * g 1)"
    using g_meas g_eq Cauchy_equation_measurable' by blast
  hence "x * g 1 = ln (h (exp x))" for x
    by (metis g_def)  
  hence "x > 0 \<Longrightarrow> ln x * g 1 = ln (h x)" for x
    by simp
  thus hx:"x > 0 \<Longrightarrow> h x = x powr ln (h (exp 1))" for x
    by (simp add: h_pos powr_def g_def mult.commute)
  show "regularly_varying U (ln (h (exp 1)))"
    using assms by(auto intro!: regularly_varyingI simp: hx[symmetric])
  thus "\<exists>\<rho>. regularly_varying U \<rho>"
    by blast
qed

lemma
  assumes mono:"mono_on {0<..} U" and U_pos: "\<And>x. 0 < x \<Longrightarrow> 0 < U x"
    and b_pos:"\<forall>\<^sub>F n in sequentially. 0 < b n"
    and l_pos:"\<forall>\<^sub>F n in sequentially. 0 < l n"
    and lim_b:"filterlim b at_top sequentially"
    and l_equiv:"l \<sim>[sequentially] (\<lambda>n. l (Suc n))"
    and lim:"\<And>x. 0 < x \<Longrightarrow> (\<lambda>n. l n * U (b n * x)) \<longlonglongrightarrow> h x"
    and h_pos: "\<And>x. 0 < x \<Longrightarrow> 0 < h x"
  shows regularly_varying_sequentialy_lim:
    "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> h x / h 1) at_top"
    and regularly_varying_sequentialy:"regularly_varying U (ln (h (exp 1) / h 1))"
    and regularly_varying_sequentialy_ex:"\<exists>\<rho>. regularly_varying U \<rho>"
proof -
  have l_Spos:"\<forall>\<^sub>F n in sequentially. 0 < l (Suc n)"
    using l_pos le_Suc_eq by(auto simp: eventually_sequentially)
  have lim_l:"(\<lambda>n. l n / l (Suc n)) \<longlonglongrightarrow> 1"
    using l_pos eventually_mono
    by(fastforce intro!: asymp_equivD_strong[OF l_equiv])
  have lim_S:"\<And>x. 0 < x \<Longrightarrow> (\<lambda>n. l (Suc n) * U (b (Suc n) * x)) \<longlonglongrightarrow> h x"
    using lim by(auto intro!: LIMSEQ_Suc)
  define n where "n \<equiv> (\<lambda>t. LEAST m. t < b (m + 1))"
  have n_less_b:"t < b (n t + 1)" for t
    unfolding n_def
    by(rule LeastI_ex)
      (metis lim_b eventually_sequentially filterlim_at_top_dense nat_le_iff_add)
  have b_le_n:"b (n t) \<le> t" if t:"b 0 \<le> t" for t
    by(rule ccontr)
      (metis Least_le Suc_n_not_le_n n_def not0_implies_Suc not_le Suc_eq_plus1 t)
  have lim_n:"filterlim n sequentially at_top"
  proof(rule ccontr)
    assume "\<not> filterlim n sequentially at_top"
    then obtain M where M':"\<And>T. \<exists>t\<ge>T. n t + 1 \<le> M + 1"
      unfolding filterlim_at_top eventually_at_top_linorder
      by (meson add_right_mono linear)
    define bM where "bM \<equiv> Max (b ` {..M + 1})"
    have "\<And>T. \<exists>t\<ge>T. b (n t + 1) \<le> bM"
      using M' unfolding bM_def
      by (meson Max.coboundedI atMost_iff finite_atMost finite_imageI image_eqI)
    then obtain t where "bM \<le> t" "b (n t + 1) \<le> bM"
      by blast
    thus False
      using n_less_b[of t] by linarith
  qed
  have b_pos':"\<forall>\<^sub>F t in at_top. 0 < b (n t)"
    and l_pos':"\<forall>\<^sub>F t in at_top. 0 < l (n t)"
    and l_Spos':"\<forall>\<^sub>F t in at_top. 0 < l (Suc (n t))"
    and lim_b':"filterlim (\<lambda>t. b (n t)) at_top at_top"
    and lim_l':"((\<lambda>t. l (n t) / l (Suc (n t))) \<longlongrightarrow> 1) at_top"
    and lim':"\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. l (n t) * U (b (n t) * x)) \<longlongrightarrow> h x) at_top"
    and lim_S':"\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. l (Suc (n t)) * U (b (Suc (n t)) * x)) \<longlongrightarrow> h x) at_top"
    by(auto intro!: b_pos l_pos lim_b lim_l eventually_compose_filterlim[OF _ lim_n]
        filterlim_compose[OF _ lim_n] l_Spos lim lim_S)
  show *:"((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> h x / h 1) at_top" if x:"0 < x" for x
  proof(rule tendsto_sandwich)
    show "\<forall>\<^sub>F t in at_top. (l (Suc (n t)) / l (n t))
                          * (l (n t) * U (b (n t) * x) / (l (Suc (n t)) * U (b (Suc (n t)))))
                          \<le> U (t * x) / U t" (is "\<forall>\<^sub>F t in at_top. ?lhs t \<le> _")
    proof(intro impI eventually_mp[OF eventually_at_top_linorderI[where c="max (b 0) 1"]
          eventually_conj[OF b_pos' eventually_conj[OF l_pos' l_Spos']]])
      fix t
      assume t: "max (b 0) 1 \<le> t" and h:"0 < b (n t) \<and>  0 < l (n t) \<and> 0 < l (Suc (n t))"
      have "?lhs t = U (b (n t) * x) / U (b (Suc (n t)))"
        using h by simp
      also have "... \<le> U (t * x) / U t"
        by(rule frac_le)
          (use U_pos x h t n_less_b[of t] mono_onD[OF mono] b_le_n[of t]
               in "auto intro!: order.strict_implies_order[of 0]")
      finally show "?lhs t \<le> U (t * x) / U t" .
    qed
  next
    show "\<forall>\<^sub>F t in at_top. U (t * x) / U t
                          \<le> (l (n t) / l (Suc (n t)))
                          * (l (Suc (n t)) * U (b (Suc (n t)) * x) / (l (n t) * U (b (n t))))
                          " (is "\<forall>\<^sub>F t in at_top. _ \<le> ?rhs t")
    proof(intro impI eventually_mp[OF eventually_at_top_linorderI[where c="max (b 0) 1"]
          eventually_conj[OF b_pos' eventually_conj[OF l_pos' l_Spos']]])
      fix t
      assume t: "max (b 0) 1 \<le> t" and h:"0 < b (n t) \<and>  0 < l (n t) \<and> 0 < l (Suc (n t))"
      have "U (t * x) / U t \<le> U (b (Suc (n t)) * x) / U (b (n t))"
        by(rule frac_le)
          (use U_pos x h t n_less_b[of t] mono_onD[OF mono] b_le_n[of t]
               in "auto intro!: order.strict_implies_order[of 0]")
      also have "... \<le> ?rhs t"
        using h by simp
      finally show "U (t * x) / U t \<le> ?rhs t" .
    qed
  next
    have 1:"((\<lambda>t. l (Suc (n t)) / l (n t)) \<longlongrightarrow> 1) at_top"
      using tendsto_divide[OF tendsto_const[of 1] lim_l'] by simp
    have 2:"((\<lambda>t. l (n t) * U (b (n t) * x)) \<longlongrightarrow> h x) at_top"
      using x lim' by simp
    have 3:"((\<lambda>t. l (Suc (n t)) * U (b (Suc (n t)))) \<longlongrightarrow> h 1) at_top"
      using lim_S'[of 1] by simp
    show "((\<lambda>t. l (Suc (n t)) / l (n t) *
                (l (n t) * U (b (n t) * x) / (l (Suc (n t)) * U (b (Suc (n t))))))
           \<longlongrightarrow> h x / h 1) at_top"
      using tendsto_mult[OF 1 tendsto_divide[OF 2 3]] h_pos[of 1] by argo
  next
    thm lim_l'
    have 2:"((\<lambda>t. l (Suc (n t)) * U (b (Suc (n t)) * x)) \<longlongrightarrow> h x) at_top"
      using x lim_S' by simp
    have 3:"((\<lambda>t. l (n t) * U (b (n t))) \<longlongrightarrow> h 1) at_top"
      using lim'[of 1] by simp
    show "((\<lambda>t. l (n t) / l (Suc (n t)) *
           (l (Suc (n t)) * U (b (Suc (n t)) * x) / (l (n t) * U (b (n t)))))
            \<longlongrightarrow> h x / h 1) at_top"
      using tendsto_mult[OF lim_l' tendsto_divide[OF 2 3]] h_pos[of 1] by argo
  qed
  show "regularly_varying U (ln (h (exp 1) / h 1))"
    by(auto intro!: divide_limit_imp_regularly_varying
        borel_measurable_mono_on_fnc mono U_pos *)
  thus "\<exists>\<rho>. regularly_varying U \<rho>"
    by blast
qed

lemma regularly_varying_integral_infinity:
  assumes rv:"regularly_varying U \<rho>"
  assumes rho:"- 1 < \<rho>"
  shows "(\<integral>\<^sup>+ t\<in>{a<..}. ennreal (U t) \<partial>lborel) = \<top>"
proof -
  have [measurable]:"\<And>n. (\<lambda>x. ennreal (U x) * indicator {2^n<..2 * 2^n} x)
                           \<in> borel_measurable borel"
    "(\<lambda>x. ennreal (U x) * indicator {0<..} x) \<in> borel_measurable borel"
    by(auto intro!: regularly_varying_meas_Ioc_ennreal
                    regularly_varying_meas_o_ennreal rv)
  have "2 powr \<rho> > 1 / 2"
    by (metis rho powr_less_cancel_iff powr_neg_one rel_simps(49,51) semiring_norm(76))
  with regularly_varying_lim[where x=2,OF rv]
  obtain s' where s':"\<And>t. s' \<le> t \<Longrightarrow> 1 / 2 <  U (t * 2) / U t"
    by (metis (lifting) eventually_at_top_linorder rel_simps(51) order_tendstoD(1))
  obtain s'' where s'': "\<And>t k. s'' \<le> t \<Longrightarrow> set_integrable lborel {t..k} U"
    using regularly_varying_eventually_locally_integrable[OF rv]
    by (metis (lifting) eventually_at_top_linorder)
  define s where "s \<equiv> max (max 1 a) (max s' s'')"
  have s_pos:"0 < s" and s:"\<And>t. s \<le> t \<Longrightarrow> U t < 2 * U (t * 2)"
    and s2:"\<And>t k. s \<le> t \<Longrightarrow> set_integrable lborel {t..k} U"
    using s' s'' regularly_varying_pos[OF rv] by(fastforce simp: s_def)+
  have as:"a \<le> s"
    by(simp add: s_def)
  obtain N where N:"s \<le> 2 ^ N"
    using power_of_nat_log_ge [of 2 s] by auto
  hence N':"\<And>n. N \<le> n \<Longrightarrow> 2 ^ n \<le> t \<Longrightarrow> U t <  2 * U (t * 2)" for t
    using s[of t] s_pos order.trans less_num_simps
    by (metis power_increasing power_one_right two_realpow_ge_one)
  have integrable:"N \<le> n \<Longrightarrow> set_integrable lborel {2^n<..2 * 2^n} U" for n
    using s2[OF order.trans[OF N]]
    by(auto intro!: set_integrable_subset[where A="{2^n..2 * 2^n}" and B="{2^n<..2 * 2^n}"])
  have less':"(\<integral>\<^sup>+ t\<in>{2^n<..2 * 2^n}. U t \<partial>lborel) < (\<integral>\<^sup>+ t\<in>{2*2^n<..4 * 2^n}. U t \<partial>lborel)"
    if n:"N \<le> n" for n
  proof -
    have "(\<integral>\<^sup>+ t\<in>{2^n<..2 * 2^n}. ennreal (U t) \<partial>lborel)
           < (\<integral>\<^sup>+ t\<in>{2^n<..2 * 2^n}. ennreal (2 * U (t * 2)) \<partial>lborel)"
    proof(rule set_nn_integral_less)
      have "(\<integral>\<^sup>+x\<in>{2 ^ n<..2 * 2 ^ n}. ennreal (U x) \<partial>lborel)
             \<le> (\<integral>\<^sup>+x. ennreal \<bar>indicat_real {2 ^ n<..2 * 2 ^ n} x * U x\<bar> \<partial>lborel)"
        by(auto intro!: nn_integral_mono arg_cong[where f=ennreal] 
            simp: ennreal_indicator[symmetric] ennreal_mult''[OF indicator_pos_le,symmetric]
            mult.commute)
      also have "... < \<infinity>"
        using integrable[OF n] by(auto simp: set_integrable_def integrable_iff_bounded)
      finally show "(\<integral>\<^sup>+x\<in>{2 ^ n<..2 * 2 ^ n}. ennreal (U x) \<partial>lborel) \<noteq> \<infinity>"
        by order
    next
      show "AE x\<in>{2 ^ n<..2 * 2 ^ n} in lborel. ennreal (U x)
                            < ennreal (2 * U (x * 2)) "
        by(fastforce intro!: ennreal_lessI N'[OF n] regularly_varying_pos[OF rv])
      show "(\<lambda>x. ennreal (2 * U (x * 2)) * indicator {2 ^ n<..2 * 2 ^ n} x)
             \<in> borel_measurable lborel"
        by(auto intro!: regularly_varying_meas_Ioc_ennreal
                        regularly_varying_comp_multc regularly_varying_cmult rv)
    qed auto
    also have "... = (\<integral>\<^sup>+x\<in>{2 ^ n<..2 * 2 ^ n}. ennreal (\<bar>2\<bar> * U (x * 2)) \<partial>lborel)"
      by simp
    also have "... = (\<integral>\<^sup>+x\<in>(\<lambda>x. x * 2) ` {2 ^ n<..2 * 2 ^ n}. ennreal (U x) \<partial>lborel)"
      by(rule nn_integral_change_of_variables_real1'[symmetric])
        (use integrable[of "n + 1"] n in
         "auto intro!: measurable_restrict_space1 inj_on_mult less_imp_le
                       regularly_varying_pos[OF rv] simp: mult_commute_abs")
    also have "... = (\<integral>\<^sup>+ t\<in>{2*2^n<..4 * 2^n}. U t \<partial>lborel)"
      by simp
    finally show ?thesis .
  qed
  have less:"(\<integral>\<^sup>+ t\<in>{2^N<..2 * 2^N}. U t \<partial>lborel) < (\<integral>\<^sup>+ t\<in>{2*2^n<..4 * 2^n}. U t \<partial>lborel)"
    if n:"N \<le> n" for n
  proof(rule nat_induct_at_least[OF n])
    fix m
    assume m:"N \<le> m"
      and "(\<integral>\<^sup>+x\<in>{2 ^ N<..2 * 2 ^ N}. ennreal (U x) \<partial>lborel)
           < (\<integral>\<^sup>+x\<in>{2 * 2 ^ m<..4 * 2 ^ m}. ennreal (U x) \<partial>lborel)"
    hence "(\<integral>\<^sup>+x\<in>{2 ^ N<..2 * 2 ^ N}. ennreal (U x) \<partial>lborel)
           < (\<integral>\<^sup>+x\<in>{2 * 2 ^ m<..4 * 2 ^ m}. ennreal (U x) \<partial>lborel)"
      by simp
    also have "... = (\<integral>\<^sup>+x\<in>{2 ^ Suc m<..2 * 2 ^ Suc m}. ennreal (U x) \<partial>lborel)"
      by simp
    also have "... < (\<integral>\<^sup>+x\<in>{2 * 2 ^ Suc m<..4 * 2 ^ Suc m}. ennreal (U x) \<partial>lborel)"
      by(intro less') (use m in auto)
    finally show "(\<integral>\<^sup>+x\<in>{2 ^ N<..2 * 2 ^ N}. ennreal (U x) \<partial>lborel)
           < (\<integral>\<^sup>+x\<in>{2 * 2 ^ Suc m<..4 * 2 ^ Suc m}. ennreal (U x) \<partial>lborel)" .
  qed(use less' in auto)
  have disj:"disjoint_family (\<lambda>n. {2 * 2 ^ (n + N) <..4 * 2 ^ (n + N)::real})"
    unfolding disjoint_family_on_def
  proof safe
    fix m n x
    assume mn:"m \<noteq> n"
      and x:"x \<in> {2 * 2 ^ (m + N)<..4 * 2 ^ (m + N)::real}"
            "x \<in> {2 * 2 ^ (n + N)<..4 * 2 ^ (n + N)}"
    have 1:"m < n \<Longrightarrow> (2 :: real) ^ (m + 1 + (N + 1)) \<le> 2 ^ (n + N + 1)"
      by(intro power_increasing) (auto simp: less_eq_Suc_le)
    have 2:"n < m \<Longrightarrow> (2 :: real) ^ (n + 1 + (N + 1)) \<le> 2 ^ (m + N + 1)"
      by(intro power_increasing) (auto simp: less_eq_Suc_le)
    consider "m < n" | "n < m"
      using mn by linarith
    thus "x \<in> {}"
      by cases (use 1 2 x in auto)
  qed
  have subst:"(\<Union>m. {2*2^(m + N)<..4 * 2^(m + N)}) \<subseteq> {a<..}"
  proof safe
    fix x m
    assume x: "x \<in> {2 * 2 ^ (m + N)<..4 * 2 ^ (m + N) :: real}"
    have "(2 :: real) ^ N \<le> 2 * 2 ^ (m + N)"
      by(auto simp del: power_Suc simp: power_Suc[symmetric])
    thus "a < x"
      using as N x by simp
  qed
  have "\<top> = (\<Sum>m. (\<integral>\<^sup>+ t\<in>{2 ^ N<..2 * 2 ^ N}. ennreal (U t) \<partial>lborel))"
    by(intro suminf_const_infinity[symmetric] set_nn_integral_zero_less AE_I2)
      (use regularly_varying_pos[OF rv] in auto)
  also have "... \<le> (\<Sum>m. (\<integral>\<^sup>+ t\<in>{2*2^(m + N)<..4 * 2^(m + N)}. U t \<partial>lborel))"
    by(auto intro!: suminf_le less_imp_le[OF less])
  also have "... =
    (\<Sum>m. (\<integral>\<^sup>+ t\<in>{2*2^(m + N)<..4 * 2^(m + N)}. ennreal (U t) * indicator {0<..} t \<partial>lborel))"
    by(auto intro!: suminf_cong nn_integral_cong ennreal_mult_right_cong
              simp: indicator_eq_0_iff)
  also have "... =
    (\<integral>\<^sup>+ t\<in>\<Union>m. {2*2^(m + N)<..4 * 2^(m + N)}. ennreal (U t) * indicator {0<..} t \<partial>lborel)"
    by(rule nn_integral_disjoint_family[symmetric]) (auto simp: disj)
   also have "... \<le> (\<integral>\<^sup>+t\<in>{a<..}. ennreal (U t) \<partial>lborel)"
     using subst by(intro nn_integral_mono) (fastforce simp: indicator_def)
  finally show ?thesis
    using neq_top_trans by blast
qed

subsection \<open>Karamata's Representation Theorem\<close>
text \<open>Lemma 1.3.1 in \cite{BGT}.\<close>
lemma Karamata_representation_ln_exp_slowly_varying:
  fixes L
  defines "h \<equiv> (\<lambda>x. ln (L (exp x)))"
  assumes sv:"slowly_varying L"
    and A: "0 < A"
    and bdd:"\<And>a b. A \<le> a \<Longrightarrow> \<exists>X>0. \<exists>Y. L ` {a..b} \<subseteq> {X..Y}"
  shows "\<exists>c e C.
              (\<forall>x \<ge> ln A. h x = c x + (\<integral>u\<in>{ln A<..x}. e u \<partial>lborel))
            \<and> (\<forall>x \<ge> ln A. set_integrable lborel {ln A<..x} e)
            \<and> e \<in> borel_measurable borel
            \<and> (e \<longlongrightarrow> 0) at_top
            \<and> bounded (e ` {ln A..})
            \<and> c \<in> borel_measurable borel
            \<and> (c \<longlongrightarrow> C) at_top"
proof -
  have [measurable]:"h \<in> borel_measurable borel"
    using regularly_varying_meas_log_exp sv by(simp add: h_def)
  have bddh:"bounded (h ` {a..b})" if a:"ln A \<le> a" for a b
  proof(cases "a \<le> b")
    assume b:"a \<le> b"
    then obtain A' B where A': "A \<le> A'" "a = ln A'" and B:"A' \<le> B" "b = ln B"
      by (metis a exp_gt_zero landau_omega.R_trans ln_exp ln_mono nle_le)
    hence A'_pos:"0 < A'" and B_pos:"0 < B"
      using A by auto
    obtain X Y where XY:"X > 0" "X \<le> Y" "L ` {A'..B} \<subseteq> {X..Y}"
      using bdd A' B by (meson A'_pos atLeastatMost_subset_iff order.trans) 
    have "exp ` {a..b} = {A'..B}"
      unfolding A' B
      by(subst image_mono_on_continuous_on_Icc)
        (use A' B A'_pos B_pos in
         "auto intro!: mono_on_subset[OF Multiseries_Expansion_Bounds.mono_exp_real]
                       continuous_on_exp")
    hence "h ` {a..b} = (\<lambda>x. ln (L x)) ` {A'..B}"
      by (metis (no_types, lifting) ext h_def image_image)
    also have "... = ln ` (L ` {A'..B})"
      by blast
    also have "... \<subseteq> ln ` {X..Y}"
      using XY by blast
    also have "... = {ln X..ln Y}"
      using XY
      by(intro image_mono_on_continuous_on_Icc XY continuous_on_ln mono_onI ln_mono)
         auto
    finally show ?thesis
      by (metis bounded_closed_interval bounded_subset)
  qed simp
  have integrableh:"set_integrable lborel {a<..b} h" if a:"ln A \<le> a" for a b
    unfolding set_integrable_def
  proof(safe intro!: integrableI_bounded)
    obtain K where K:"\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> \<bar>h x\<bar>  \<le> K"
      using bddh[OF a] by (metis atLeastAtMost_iff bounded_real image_eqI)
    have "(\<integral>\<^sup>+ x. ennreal (norm (indicat_real {a<..b} x *\<^sub>R h x)) \<partial>lborel)
          = (\<integral>\<^sup>+ x\<in>{a<..b}. ennreal \<bar>h x\<bar> \<partial>lborel)"
      by(auto intro!: nn_integral_cong simp: indicator_times_eq_if)
    also have "... \<le> (\<integral>\<^sup>+ x\<in>{a..b}. ennreal K \<partial>lborel)"
      using K by(auto intro!: nn_integral_mono simp: indicator_def ennreal_leI)
    also have "... =  ennreal K * (\<integral>\<^sup>+ x. indicator {a..b} x \<partial>lborel)"
      by(subst nn_integral_cmult) simp_all
    also have "... < \<infinity>"
      by (simp add: emeasure_lborel_Icc_eq ennreal_mult_less_top)
    finally show "(\<integral>\<^sup>+ x. ennreal (norm (indicat_real {a<..b} x *\<^sub>R h x)) \<partial>lborel) < \<infinity>" .
  qed simp
  define C where "C \<equiv> (\<integral>t\<in>{ln A<..ln A + 1}. h t \<partial>lborel)"
  define c where "c \<equiv> (\<lambda>x. C + (\<integral>t\<in>{x<..x+ 1}. h x - h t \<partial>lborel))"
  define e where "e \<equiv> (\<lambda>x. h (x + 1) - h x)"
  have integrableh':"set_integrable lborel {ln A<..x} (\<lambda>t. h (t + 1))" for x
  proof -
    have "(\<lambda>t. indicat_real {ln A + 1<..x + 1} (1 + t) * h (1 + t))
           = (\<lambda>t. indicat_real {ln A<..x} t * h (t + 1))"
      by standard (auto simp: indicator_def add.commute)
    thus ?thesis
      using integrableh[of "ln A + 1" "x + 1"]
      by(auto simp:
          lborel_integrable_real_affine_iff[symmetric,
            where f="\<lambda>t. indicat_real {ln A+1<..x+1} t * h t" and t=1 and c=1]
            set_integrable_def) 
  qed
  have *:"\<forall>x \<ge> ln A. h x = c x + (\<integral>u\<in>{ln A<..x}. e u \<partial>lborel)"
  proof safe
    fix x
    assume x:"ln A \<le> x"
    have "h x = h x + (\<integral>t\<in>{ln A<..ln A + 1} \<union> {ln A + 1<.. x+ 1}. h t \<partial>lborel)
                    - (\<integral>t\<in>{ln A<..x} \<union> {x<..x+ 1}. h t \<partial>lborel)"
      using x by(auto intro!: arg_cong[where f="\<lambda>A. set_lebesgue_integral lborel A h"])
    also have "... = h x + (\<integral>t\<in>{ln A<..ln A + 1}. h t \<partial>lborel)
                         + (\<integral>t\<in>{ln A + 1<.. x+ 1}. h t \<partial>lborel)
                         - (\<integral>t\<in>{ln A<..x} \<union> {x<..x+ 1}. h t \<partial>lborel)"
      by(subst set_integral_Un) (auto intro!: integrableh)
    also have "... = h x + (\<integral>t\<in>{ln A<..ln A + 1}. h t \<partial>lborel)
                         + (\<integral>t\<in>{ln A + 1<.. x+ 1}. h t \<partial>lborel)
                         - ((\<integral>t\<in>{ln A<..x}. h t \<partial>lborel)
                             + (\<integral>t\<in>{x<..x+ 1}. h t \<partial>lborel))"
      by(subst set_integral_Un) (auto intro!: integrableh x)
    also have "... = h x + (\<integral>t\<in>{ln A<..ln A + 1}. h t \<partial>lborel)
                         + (\<integral>t\<in>{ln A<.. x}. h (t + 1) \<partial>lborel)
                         - ((\<integral>t\<in>{ln A<..x}. h t \<partial>lborel)
                             + (\<integral>t\<in>{x<..x+ 1}. h t \<partial>lborel))"
      unfolding set_lebesgue_integral_def real_scaleR_def
      by(subst lborel_integral_real_affine
          [where f="\<lambda>t. indicat_real {ln A+1<..x+1} t * h t" and t=1 and c=1])
        (auto intro!: Bochner_Integration.integral_cong simp: indicator_def add.commute)
    also have "... = C + (h x + (\<integral>t\<in>{x<..x+ 1}. - h t \<partial>lborel))
                         + ((\<integral>t\<in>{ln A<.. x}. h (t + 1) \<partial>lborel)
                             + (\<integral>t\<in>{ln A<..x}. - h t \<partial>lborel))"
      by(simp add: set_integral_uminus[OF integrableh] x C_def)
    also have "... = C + ((\<integral>t\<in>{x<..x+ 1}. h x \<partial>lborel) + (\<integral>t\<in>{x<..x+ 1}. - h t \<partial>lborel))
                         + ((\<integral>t\<in>{ln A<.. x}. h (t + 1) \<partial>lborel)
                             + (\<integral>t\<in>{ln A<..x}. - h t \<partial>lborel))"
      by(auto simp: set_lebesgue_integral_def)
    also have "... = C + ((\<integral>t\<in>{x<..x+ 1}. h x + (- h t) \<partial>lborel))
                         + ((\<integral>t\<in>{ln A<.. x}. h (t + 1) \<partial>lborel)
                             + (\<integral>t\<in>{ln A<..x}. - h t \<partial>lborel))"
      by(subst set_integral_add)
        (auto intro!: integrableh x set_integrable_const simp: set_integrable_uminus)
    also have "... = c x + ((\<integral>t\<in>{ln A<.. x}. h (t + 1) + (- h t) \<partial>lborel))"
      by(subst set_integral_add[where f="\<lambda>t. h (t + 1)"])
        (auto intro!: integrableh x integrableh' simp: set_integrable_uminus c_def)
    finally show "h x = c x + (\<integral>u\<in>{ln A<..x}. e u \<partial>lborel)"
      by(simp add: e_def)
  qed
  have **:"\<forall>x\<ge>ln A. set_integrable lborel {ln A<..x} e"
    by(auto simp: e_def intro!: integrableh' integrableh)
  have *****:"e \<in> borel_measurable borel"
    by(simp add: e_def)
  have ***:"(e \<longlongrightarrow> 0) at_top"
    using slowly_varying_ln_exp[OF sv] by(simp add: e_def h_def)
  have ******:"bounded (e ` {ln A..})"
  proof -
    obtain X where X:"\<And>x. X < x \<Longrightarrow> \<bar>e x\<bar> < 1"
      using tendstoD[OF ***,of 1] unfolding eventually_at_top_dense
      by auto
    have 1:"bounded (e ` {ln A..X})"
      unfolding e_def
      by(intro bounded_minus_comp bounded_subset[where T="h ` {ln A..X}" and S="h ` {ln A<..X}"]
          bounded_subset[where T="(\<lambda>x. h (x + 1)) ` {ln A..X}"
                               and S="(\<lambda>x. h (x + 1)) ` {ln A<..X}"])
        (auto simp: image_image[symmetric,where g="\<lambda>x. x + 1"] intro!: bddh)
    have 2:"bounded (e ` {X<..})"
      using X by(fastforce intro!: boundedI[where B=2])
    show ?thesis
      by(rule bounded_subset[where T="e ` {ln A..X} \<union> e ` {X<..}"])
        (use 1 2 in fastforce)+
  qed
  have ****:"c \<in> borel_measurable borel"
  proof -
    have "Measurable.pred (borel \<Otimes>\<^sub>M borel) (\<lambda>x::real \<times> real. snd x \<in> {fst x<..fst x + 1})"
      by simp
    thus ?thesis
      unfolding c_def set_lebesgue_integral_def
      by measurable
  qed
  have "(c \<longlongrightarrow> C) at_top"
  proof -
    have "\<forall>\<^sub>F x in at_top. (\<integral>t\<in>{x<..x+ 1}. h x - h t \<partial>lborel)
                          = (\<integral>t\<in>{0<..1}. h x - h (x + t) \<partial>lborel)"
    proof(safe intro!: eventually_at_top_linorderI[where c="ln A"])
      fix x
      assume x:"ln A \<le> x"
      thus "(\<integral>t\<in>{x<..x+ 1}. h x - h t \<partial>lborel) = (\<integral>t\<in>{0<..1}. h x - h (x + t) \<partial>lborel)"
        unfolding set_lebesgue_integral_def
        by(subst lborel_integral_real_affine[where c=1 and t=x])
          (auto intro!: Bochner_Integration.integral_cong simp: indicator_def)
    qed
    moreover have "((\<lambda>x. (\<integral>t\<in>{0<..1}. h x - h (x + t) \<partial>lborel)) \<longlongrightarrow> 0) at_top"
    proof(rule tendstoI)
      fix e :: real
      assume e:"0 < e"
      define e' where "e' \<equiv> e / 2"
      have e':"0 < e'"
        using e by(simp add: e'_def)
      obtain X where X:"\<And>x t. X \<le> x \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow> \<bar>h x - h (x + t)\<bar> < e'"
        using uniform_limitD[OF slowly_varying_UCT_interval_ln_exp[OF sv,of 0 1] e']
        by(fastforce simp: h_def dist_real_def eventually_at_top_linorder abs_minus_commute)
      show "\<forall>\<^sub>F x in at_top. dist (\<integral>t\<in>{0<..1}. h x - h (x + t) \<partial>lborel) 0 < e"
      proof(safe intro!: eventually_at_top_linorderI[where c=X])
        fix x
        assume x:"X \<le> x"
        then have [simp]:"set_integrable lborel {0<..1} (\<lambda>t. \<bar>h x - h (x + t)\<bar>)"
          using less_imp_le[OF X]
          by(auto intro!: integrableI_bounded_set[where A="{0<..1}" and B=e']
              simp: set_integrable_def)
        have "dist (\<integral>t\<in>{0<..1}. h x - h (x + t) \<partial>lborel) 0
              \<le> (\<integral>t\<in>{0<..1}. \<bar>h x - h (x + t)\<bar> \<partial>lborel)"
          by(auto simp: set_lebesgue_integral_def abs_mult_pos')
        also have "... \<le> (\<integral>t\<in>{0::real<..1}. e' \<partial>lborel)"
          by(auto intro!: set_integral_mono less_imp_le[OF X] x integrableh set_integrable_const)
        also have "... < e"
          by(simp add: set_lebesgue_integral_def e'_def e)
        finally show "dist (\<integral>t\<in>{0<..1}. h x - h (x + t) \<partial>lborel) 0 < e" .
      qed
    qed
    ultimately have "((\<lambda>x. (\<integral>t\<in>{x<..x+ 1}. h x - h t \<partial>lborel)) \<longlongrightarrow> 0) at_top"
      by(simp cong: tendsto_cong)
    thus ?thesis
      by (metis (lifting) ext c_def group_cancel.rule0 tendsto_add_const_iff)
  qed
  thus ?thesis
    using * ** *** **** ***** ****** by blast
qed

lemma Karamata_representation_ln_exp2:
  fixes U
  defines "h \<equiv> (\<lambda>x. ln (U (exp x)))"
  assumes rv:"regularly_varying U \<rho>"
    and A: "0 < A"
    and bdd:"\<And>a b. A \<le> a \<Longrightarrow> \<exists>X>0. \<exists>Y. U ` {a..b} \<subseteq> {X..Y}"
  shows "\<exists>c e C.
              (\<forall>x \<ge> ln A. h x = c x + \<rho> * ln A + (\<integral>u\<in>{ln A<..x}. \<rho> +  e u \<partial>lborel))
            \<and> (\<forall>x \<ge> ln A. set_integrable lborel {ln A<..x} e)
            \<and> e \<in> borel_measurable borel
            \<and> (e \<longlongrightarrow> 0) at_top
            \<and> bounded (e ` {ln A..})
            \<and> c \<in> borel_measurable borel
            \<and> (c \<longlongrightarrow> C) at_top"
proof -
  define L where "L \<equiv> \<lambda>x. U x / x powr \<rho>"
  define h' where "h' \<equiv> \<lambda>x. ln (L (exp x))"
  have sv:"slowly_varying L"
    by(simp add: regularly_varying_iff_slowly_varying_divide_powr[of U,symmetric] L_def rv)
  have U_L:"\<And>x. 0 < x \<Longrightarrow> U x = x powr \<rho> * L x"
    by(auto simp: L_def)
  have h_h':"h = (\<lambda>x. \<rho> * x + h' x)"
    using regularly_varying_pos[OF sv exp_gt_zero]
    by(auto simp add: h'_def h_def U_L ln_mult less_le)
  have "\<exists>X>0. \<exists>Y. L ` {a..b} \<subseteq> {X..Y}" if Aa:"A \<le> a" for a b
  proof -
    obtain X' Y' where X'_pos:"X' > 0"
      and X': "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> X' \<le> U x"
      and Y':"\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> U x \<le> Y'"
      using bdd[OF Aa,of b] by fastforce
    consider "\<rho> \<le> 0" "a \<le> b" | "0 \<le> \<rho>" "a \<le> b" | "b < a"
      by linarith
    thus ?thesis
    proof cases
      assume h: "\<rho> \<le> 0" "a \<le> b"
      have "X' / a powr \<rho> \<le> U x / x powr \<rho>"
        and "U x / x powr \<rho> \<le> Y' / b powr \<rho>" if "a \<le> x" "x \<le> b" for x
        using X'[OF that] Y'[OF that] Aa A X'_pos h that
        by(auto intro!: frac_le powr_mono2')
      thus ?thesis
        using X'_pos h Aa A
        by(intro exI[where x="X' / a powr \<rho>",OF conjI[OF _ exI[where x="Y' / b powr \<rho>"]]])
          (auto simp: L_def)
    next
      assume h: "\<rho> \<ge> 0" "a \<le> b"
      have "X' / b powr \<rho> \<le> U x / x powr \<rho>"
        and "U x / x powr \<rho> \<le> Y' / a powr \<rho>" if "a \<le> x" "x \<le> b" for x
        using X'[OF that] Y'[OF that] Aa A X'_pos h that
        by(auto intro!: frac_le powr_mono2)
      thus ?thesis
        using X'_pos h Aa A
        by(intro exI[where x="X' / b powr \<rho>",OF conjI[OF _ exI[where x="Y' / a powr \<rho>"]]])
          (auto simp: L_def)
    qed (auto intro!: exI[where x=1])
  qed
  from Karamata_representation_ln_exp_slowly_varying[OF sv A this]
  obtain c e C where
    h'_eq:"\<And>x. ln A \<le> x \<Longrightarrow> h' x = c x + (\<integral>u\<in>{ln A<..x}. e u \<partial>lborel)"
    and e_integrable:"\<And>x. ln A \<le> x \<Longrightarrow> set_integrable lborel {ln A<..x} e"
    and e_meas[measurable]:"e \<in> borel_measurable borel"
    and e_lim:"(e \<longlongrightarrow> 0) at_top"
    and e_bdd:"bounded (e ` {ln A..})"
    and c_meas[measurable]:"c \<in> borel_measurable borel"
    and c_lim:"(c \<longlongrightarrow> C) at_top"
    by(auto simp: h'_def)
  have h_eq:"h x = c x + \<rho> * ln A + (\<integral>u\<in>{ln A<..x}. \<rho> +  e u \<partial>lborel)" if x:"ln A \<le> x" for x
  proof -
    have "h x = h' x + \<rho> * x"
      by(simp add: h_h')
    also have "... = c x + (\<integral>u\<in>{ln A<..x}. e u \<partial>lborel) + \<rho> * x"
      by(simp add: x h'_eq)
    also have "... = c x + (\<integral>u\<in>{ln A<..x}. \<rho> \<partial>lborel) + (\<integral>u\<in>{ln A<..x}. e u \<partial>lborel) + \<rho> * ln A"
      by(simp add: interval_integral_Ioc[OF x,symmetric] right_diff_distrib')
    also have "... = c x + \<rho> * ln A + (\<integral>u\<in>{ln A<..x}. \<rho> +  e u \<partial>lborel)"
      by (rule sym) (auto intro!: e_integrable set_integrable_const simp: x)
    finally show ?thesis .
  qed
  thus ?thesis
    using e_integrable e_lim c_lim c_meas e_meas e_bdd by blast
qed

lemma Karamata_representation_ln_exp:
  fixes U
  defines "h \<equiv> (\<lambda>x. ln (U (exp x)))"
  assumes rv:"regularly_varying U \<rho>"
   shows "\<exists>A>0. \<exists>c e C.
              (\<forall>x \<ge> ln A. h x = c x + \<rho> * ln A + (\<integral>u\<in>{ln A<..x}. \<rho> +  e u \<partial>lborel))
            \<and> (\<forall>x \<ge> ln A. set_integrable lborel {ln A<..x} e)
            \<and> e \<in> borel_measurable borel
            \<and> (e \<longlongrightarrow> 0) at_top
            \<and> bounded (e ` {ln A..})
            \<and> c \<in> borel_measurable borel
            \<and> (c \<longlongrightarrow> C) at_top"
proof -
  obtain A where "0 < A" "\<And>a b. A \<le> a \<Longrightarrow> \<exists>X>0. \<exists>Y. U ` {a..b} \<subseteq> {X..Y}"
    using regularly_varying_eventually_bounded_interval_strong[OF rv]
    unfolding eventually_at_top_linorder
    by (meson exp_gt_self exp_gt_zero less_eq_real_def)
  from Karamata_representation_ln_exp2[OF rv this] this
  show ?thesis
    unfolding h_def by blast
qed

text \<open>This equation for @{term ln} is useful for transforming equations in proofs.\<close>
lemma Karamata_representation_ex1:
  assumes rv:"regularly_varying U \<rho>"
    and A:"0 < A"
    and bdd:"\<And>a b. A \<le> a \<Longrightarrow> \<exists>X>0. \<exists>Y. U ` {a..b} \<subseteq> {X..Y}"
  shows "\<exists>c r C.
              (\<forall>x \<ge> A. U x = c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel))
            \<and> (\<forall>x \<ge> A. set_integrable lborel {A<..x} (\<lambda>t. r t / t))
            \<and> r \<in> borel_measurable borel
            \<and> (r \<longlongrightarrow> \<rho>) at_top
            \<and> bounded (r ` {A..})
            \<and> c \<in> borel_measurable borel
            \<and> (\<forall>x. 0 < c x)
            \<and> (c \<longlongrightarrow> C) at_top
            \<and> 0 < C"
proof -
  define h where "h \<equiv> \<lambda>x. ln (U (exp x))"
  from Karamata_representation_ln_exp2[OF assms]
  obtain c' e C' where
   h_eq:"\<And>x. ln A \<le> x \<Longrightarrow> h x = c' x + \<rho> * ln A + (\<integral>u\<in>{ln A<..x}. \<rho> + e u \<partial>lborel)"
    and e_integrable:"\<And>x. ln A \<le> x \<Longrightarrow> set_integrable lborel {ln A<..x} e"
    and e_meas[measurable]:"e \<in> borel_measurable borel"
    and e_lim:"(e \<longlongrightarrow> 0) at_top"
    and e_bdd:"bounded (e ` {ln A..})"
    and c_meas[measurable]:"c' \<in> borel_measurable borel"
    and c_lim:"(c' \<longlongrightarrow> C') at_top"
    unfolding h_def by blast
  define C where "C \<equiv> exp C' * (A powr \<rho>)"
  define c where "c \<equiv> \<lambda>x. exp (c' (ln x)) * A powr \<rho>"
  define r where "r \<equiv> \<lambda>x. \<rho> + e (ln x)"
  have im_ln:"A \<le> x \<Longrightarrow> ln ` {A<..x} = {ln A<..ln x}" for x
    using A
    by(intro image_mono_on_continuous_on_Ioc continuous_on_ln strict_mono_onI ln_strict_mono)
      auto
  have im_ln2:"ln ` {A..} = {ln A..}"
    using A
    by(intro image_mono_on_continuous_on_Ic continuous_on_ln mono_onI ln_mono ln_at_top)
      auto
  have *:"\<forall>x \<ge> A. set_integrable lborel {A<..x} (\<lambda>t. r t / t)
                   \<and> U x = c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)"
  proof safe
    fix x
    assume x:"A \<le> x"
    have [simp]:"set_integrable lborel ({ln A<..ln x}) e"
      unfolding im_ln[OF x]
      by(auto intro!: e_integrable ln_mono x A)
    have 1:"set_integrable lborel {A<..x} (\<lambda>x. \<bar>1 / x\<bar> * e (ln x))"
      using A x
      by(intro lebesgue_integrable_change_of_variables_real
          [where g'="\<lambda>x. 1 / x" and f=e,THEN iffD1]
          strict_mono_on_imp_inj_on)
        (auto simp: set_borel_measurable_def im_ln[OF x] DERIV_ln_divide
          has_field_derivative_at_within
          intro!: measurable_restrict_space1 strict_mono_onI ln_strict_mono)
    have integ1:"set_integrable lborel {A<..x} (\<lambda>t. e (ln t) / t)"
      by(rule set_integrable_cong[THEN iffD1,OF _ _ _ 1]) (use A in auto)
    have integ2:"set_integrable lborel {A<..x} (\<lambda>t. \<rho> / t)"
      unfolding set_integrable_def
      using x A by(auto intro!: integrableI_bounded_set[where A="{A<..x}" and B="\<bar>\<rho>\<bar> / A"]
          simp: divide_mono)
    show "set_integrable lborel {A<..x} (\<lambda>t. r t / t)"
      by(auto simp: r_def add_divide_distrib integ1 integ2)
    have "(\<integral>u\<in>{ln A<..ln x}. \<rho> + e u \<partial>lborel) = (\<integral>u\<in>ln ` {A<..x}. \<rho> + e u \<partial>lborel)"
      by(simp add: im_ln x)
    also have "... = (\<integral>x\<in>{A<..x}. \<bar>1 / x\<bar> * (\<rho> + e (ln x)) \<partial>lborel)"
      using A x
      by(intro lebesgue_integral_change_of_variables_real1
          [where g'="\<lambda>x. 1 / x" and f="\<lambda>x. \<rho> + e x"] strict_mono_on_imp_inj_on)
      (auto simp: set_borel_measurable_def im_ln[OF x] DERIV_ln_divide
        has_field_derivative_at_within
        intro!: set_integrable_const measurable_restrict_space1 strict_mono_onI ln_strict_mono)
    finally have eq:"(\<integral>u\<in>{ln A<..ln x}. \<rho> + e u \<partial>lborel) = (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)"
      using A by(auto simp: r_def intro!: set_lebesgue_integral_cong)
    have "U x = exp (h (ln x))"
      using A x regularly_varying_pos[OF rv] by(simp add: h_def)
    also have "... = exp (c' (ln x) + \<rho> * ln A + (\<integral>u\<in>{ln A<..ln x}. \<rho> + e u \<partial>lborel))"
      using A x by(simp add: h_eq)
    also have "... = c x * exp (\<integral>u\<in>{ln A<..ln x}. \<rho> + e u \<partial>lborel)"
      using A by(simp add: c_def exp_add ln_powr[symmetric] del: ln_powr)
    also have "... = c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)"
      by(simp add: eq)
    finally show "U x = c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)" .
  qed
  have **:"r \<in> borel_measurable borel"
    by(simp add: r_def)
  have ***:"(r \<longlongrightarrow> \<rho>) at_top"
    unfolding r_def
    by(rule filterlim_compose[OF _ ln_at_top])
      (use tendsto_add[OF tendsto_const e_lim] in simp)
  have ****:"bounded (r ` {A..})"
    unfolding r_def image_image[symmetric,where g=ln and f="\<lambda>x. \<rho> + e x"] im_ln2
    by(auto intro!: bounded_plus_comp[OF boundedI e_bdd])
  have *****:"c \<in> borel_measurable borel"
    by (simp add: c_def)
  have ******:"\<forall>x. 0 < c x"
    using A by(simp add: c_def)
  have cC:"(c \<longlongrightarrow> C) at_top"
    unfolding c_def C_def 
    by(rule filterlim_compose[OF _ ln_at_top])
      (auto intro!: tendsto_mult_right tendsto_exp c_lim)
  have C:"0 < C"
    using A by(simp add: C_def)
  show ?thesis
    using * ** *** **** ***** ****** C cC by blast
qed

lemma Karamata_representation_ex:
  assumes rv:"regularly_varying U \<rho>"
  shows "\<exists>A>0. \<exists>c r C.
              (\<forall>x \<ge> A. U x = c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel))
            \<and> (\<forall>x \<ge> A. set_integrable lborel {A<..x} (\<lambda>t. r t / t))
            \<and> r \<in> borel_measurable borel
            \<and> (r \<longlongrightarrow> \<rho>) at_top
            \<and> bounded (r ` {A..})
            \<and> c \<in> borel_measurable borel
            \<and> (\<forall>x. 0 < c x)
            \<and> (c \<longlongrightarrow> C) at_top
            \<and> 0 < C"
proof -
  obtain A where "0 < A" "\<And>a b. A \<le> a \<Longrightarrow> \<exists>X>0. \<exists>Y. U ` {a..b} \<subseteq> {X..Y}"
    using regularly_varying_eventually_bounded_interval_strong[OF rv]
    unfolding eventually_at_top_linorder
    by (meson exp_gt_self exp_gt_zero less_eq_real_def)
  from Karamata_representation_ex1[OF rv this] this
  show ?thesis
    by blast
qed

corollary Karamata_representation_ex_total:
  assumes rv:"regularly_varying U \<rho>"
  shows "\<exists>c r C.
              (\<forall>x. U x = c x * exp (\<integral>t\<in>{0<..x}. r t / t \<partial>lborel))
            \<and> (\<forall>x y. set_integrable lborel {..y} (\<lambda>t. r t / t))
            \<and> r \<in> borel_measurable borel
            \<and> (r \<longlongrightarrow> \<rho>) at_top
            \<and> bounded (range r)
            \<and> c \<in> borel_measurable (restrict_space borel {0<..})
            \<and> (\<forall>x>0. 0 < c x)
            \<and> (c \<longlongrightarrow> C) at_top
            \<and> 0 < C"
proof -
  from Karamata_representation_ex[OF rv]
  obtain A c' r' C where A_pos:"0 < A"
    and eq': "\<And>x. A \<le> x \<Longrightarrow> U x = c' x * exp (\<integral>t\<in>{A<..x}. r' t / t \<partial>lborel)"
    and integ':"\<And>x. A \<le> x \<Longrightarrow> set_integrable lborel {A<..x} (\<lambda>t. r' t / t)"
    and r'[measurable]:"r' \<in> borel_measurable borel"
    and lim_r':"(r' \<longlongrightarrow> \<rho>) at_top"
    and bdd:"bounded (r' ` {A..})"
    and c'[measurable]:"c' \<in> borel_measurable borel"
    and c'_pos:"\<And>x. 0 < c' x"
    and lim_c':"(c' \<longlongrightarrow> C) at_top"
    and C_pos:"0 < C"
    by blast
  define c where "c \<equiv> \<lambda>x. if A < x then c' x else U x"
  define r where "r \<equiv> \<lambda>x. if A < x then r' x else 0"
  have r_integral:"(\<integral>t\<in>{0<..x}. r t / t \<partial>lborel) = 0" if Ax:"x \<le> A" for x
  proof -
    have "(\<integral>t\<in>{0<..x}. r t / t \<partial>lborel) = (\<integral>t\<in>{0<..x}. 0 \<partial>lborel)"
      unfolding set_lebesgue_integral_def using Ax
      by(intro Bochner_Integration.integral_cong)
        (auto simp: r_def indicator_def)
    thus ?thesis
      by simp
  qed
  have r_integrable1:"x \<le> A \<Longrightarrow> set_integrable lborel {..x} (\<lambda>t. r t / t)" for x
   by(subst set_integrable_cong[where f'="\<lambda>x. 0",OF refl refl])
     (auto simp: r_def)
  hence r_integrable1'[simp]:"x \<le> A \<Longrightarrow> set_integrable lborel {0<..x} (\<lambda>t. r t / t)" for x
    using set_integrable_subset[where A="{..x}" and B="{0<..x}"]
    by fastforce
  have r_integrabl2[simp]: "A \<le> x \<Longrightarrow> set_integrable lborel {A<..x} (\<lambda>t. r t / t)" for x
    by(subst set_integrable_cong[where f'="\<lambda>t. r' t / t",OF refl refl])
      (auto simp: r_def integ')
  have 1:"U x = c x * exp (\<integral>t\<in>{0<..x}. r t / t \<partial>lborel)" for x
  proof(cases "A \<le> x")
    assume Ax:"A \<le> x"
    have "(\<integral>t\<in>{0<..x}. r t / t \<partial>lborel) = (\<integral>t\<in>{0<..A}\<union>{A<..x}. r t / t \<partial>lborel)"
      using Ax A_pos by(intro arg_cong[where f="\<lambda>B. (\<integral>t\<in>B. r t / t \<partial>lborel)"]) auto
    also have "... = (\<integral>t\<in>{0<..A}. r t / t \<partial>lborel) + (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)"
      by(subst set_integral_Un) (auto simp: Ax)
    also have "... = (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)"
      by(simp add: r_integral)
    also have "... = (\<integral>t\<in>{A<..x}. r' t / t \<partial>lborel)"
      by(auto intro!: Bochner_Integration.integral_cong simp: set_lebesgue_integral_def r_def)
    finally show ?thesis
      using Ax by(simp add: c_def eq')
  qed(auto simp: c_def r_integral)
  have 2:"set_integrable lborel {..x} (\<lambda>t. r t / t)" for x
  proof -
    consider "A \<le> x" | "x \<le> A"
      by fastforce
    then show ?thesis
    proof cases
      assume Ax:"A \<le> x"
      then have [simp]:"{..A} \<union> {A<..x} = {..x}"
        by auto
      with set_integrable_Un[OF r_integrable1[OF order.refl] r_integrabl2[OF Ax]]
      show ?thesis
        by simp
    qed fact
  qed
  have 3:"r \<in> borel_measurable borel"
    by(simp add: r_def)
  have 4:"(r \<longlongrightarrow> \<rho>) at_top"
    by(rule tendsto_cong[THEN iffD1,OF eventually_at_top_linorderI[where c="A + 1"] lim_r'])
      (simp add: r_def)
  have 5:"bounded (range r)"
  proof -
    have eq:"r ` {A..} \<union> r ` {..<A} = range r"
      by fastforce
    have *:"bounded (r ` {A..})"
      using bdd bounded_iff by(auto simp: r_def bounded_subset image_mono)
    have **:"bounded (r ` {..<A})"
      by(auto simp: bounded_iff r_def)
    have "bounded (r ` {A..} \<union> r ` {..<A})"
      by(simp add: * **)
    thus ?thesis
      by(simp add: eq)
  qed
  have 6:"c \<in> borel_measurable (restrict_space borel {0<..})"
    unfolding c_def
  proof(subst measurable_If)
    show "c' \<in> borel_measurable (restrict_space borel {0<..})"
      by(auto intro!: measurable_restrict_space1)
    show "{x \<in> space (restrict_space borel {0<..}). A < x} \<in> sets (restrict_space borel {0<..})"
      using borel_measurable_const measurable_id measurable_inequality_set_flipped
        measurable_restrict_space1 by blast
  qed(use regularly_varying_meas[OF rv] in auto)
  have 7:"\<forall>x>0. 0 < c x"
    using c'_pos regularly_varying_pos[OF rv] by(simp add: c_def)
  have 8:"(c \<longlongrightarrow> C) at_top"
    by(rule tendsto_cong[THEN iffD1,OF eventually_at_top_linorderI[where c="A + 1"] lim_c'])
      (simp add: c_def)
  show ?thesis
    using 1 2 3 4 5 6 7 8 C_pos by blast
qed

lemma Karamata_representation_iff:
  assumes U_meas:"U \<in> borel_measurable (restrict_space borel {0<..})"
    and U_pos:"\<And>x. 0 < x \<Longrightarrow> 0 < U x"
  shows "regularly_varying U \<rho> \<longleftrightarrow>
    (\<exists>A>0.  \<exists>c r C.
              (\<forall>x \<ge> A. U x = c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel))
            \<and> (\<forall>x \<ge> A. set_integrable lborel {A<..x} (\<lambda>t. r t / t))
            \<and> (r \<longlongrightarrow> \<rho>) at_top
            \<and> (c \<longlongrightarrow> C) at_top
            \<and> 0 < C)"
proof(safe intro!: regularly_varyingI)
  fix A c r C x
  assume A:"0 < A" and x_pos:"(0 :: real) < x"
    and eq_U:"\<forall>x\<ge>A. U x =
              c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)"
    and integ:"\<forall>x\<ge>A. set_integrable lborel {A<..x}
               (\<lambda>t. r t / t)"
    and lim_r:"(r \<longlongrightarrow> \<rho>) at_top"
    and C_pos:"0 < C"
    and lim_c:"(c \<longlongrightarrow> C) at_top"
  have lim_powr1:"((\<lambda>s. x powr s) \<longlongrightarrow> 1) (at_right 0)"
    using tendsto_powr[OF tendsto_const[of x] tendsto_ident_at[of 0]] x_pos by simp
  have lim_powr2:"((\<lambda>s. x powr (- s)) \<longlongrightarrow> 1) (at_right 0)"
    using tendsto_powr[OF tendsto_const[of x] tendsto_minus[OF tendsto_ident_at[of 0]]] x_pos
    by simp
  have *:"\<forall>\<^sub>F t in at_top. U (t * x) / U t
         = (c (t * x) / c t)
          * exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel) - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel))"
    using x_pos A eq_U
    by(auto intro!: eventually_at_top_linorderI[where c="max (A / x) A"]
        simp: divide_le_eq exp_diff)
  have **:"((\<lambda>t. c (t * x) / c t) \<longlongrightarrow> C / C) at_top"
    using C_pos
    by(intro tendsto_divide filterlim_ident lim_c tendsto_const
        filterlim_compose[OF lim_c filterlim_at_top_mult_tendsto_pos[OF _ x_pos]]) simp
  have ***:"((\<lambda>t. exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel) - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)))
            \<longlongrightarrow> x powr \<rho>) at_top"
  proof -
    consider "x < 1" | "x = 1" | "1 < x"
      by linarith
    then show ?thesis
    proof cases
      assume x:"x < 1"
      show ?thesis
      proof(rule tendsto_sandwich_mult_const[OF _ lim_powr1 lim_powr2])
        fix e :: real
        assume e:"0 < e"
        obtain T1 where T1:"\<And>t. T1 \<le> t \<Longrightarrow> r t \<le> \<rho> + e" "\<And>t. T1 \<le> t \<Longrightarrow> \<rho> - e \<le> r t"
          using tendstoD[OF lim_r e] unfolding eventually_at_top_linorder dist_real_def
          by (metis abs_diff_le_iff less_eq_real_def)
        define T where "T \<equiv> max (A / x) (T1 / x)"
        show "\<forall>\<^sub>F t in at_top.
            x powr e \<le> exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                             - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) / x powr \<rho>
      \<and> exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
              - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) / x powr \<rho>
        \<le> x powr - e"
        proof(safe intro!: eventually_at_top_linorderI[where c=T])
          fix t
          assume t:"T \<le> t"
          then have t_pos:"0 < t" and tx:"t * x \<le> t"
            using A x_pos x
            by(auto simp: T_def order.strict_trans2[OF divide_pos_pos[OF A x_pos]])
          hence Atx:"A \<le> t * x" and At:"A \<le> t"
            using A t x_pos x
            by(auto simp: T_def divide_le_eq intro!: order.trans[of A "t * x" t] mult_left_le)
          have t_le:"\<And>s. t * x \<le> s \<Longrightarrow> r s \<le> \<rho> + e" and le_t:"\<And>s. t * x \<le> s \<Longrightarrow> \<rho> - e \<le> r s"
            using t x_pos x by(auto simp: T_def divide_le_eq intro!: T1)
          have "exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel) - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel))
               = exp ((\<integral>s\<in>{t * x<..t}. - r s / s \<partial>lborel))"
            unfolding set_lebesgue_integral_def
            using integ At Atx tx
            by(subst Bochner_Integration.integral_diff[symmetric])
              (auto simp: set_lebesgue_integral_def set_integrable_def indicator_def
                simp del: integral_minus Bochner_Integration.integral_diff
                intro!: Bochner_Integration.integral_cong)
          also have "... \<le> exp ((\<integral>s\<in>{t * x<..t}. - (\<rho> - e) / s \<partial>lborel))"
            using integ At Atx A
            by(auto simp: set_integrable_uminus simp del: minus_diff_eq
                intro!: le_t set_integral_mono divide_right_mono set_integrable_inverse'
                set_integrable_subset[where A="{A<..t}" and B="{t * x<..t}"])
          also have "... = exp ((\<rho> - e) * ln x)"
            using A Atx x_pos t_pos x
            by(subst set_integral_inverse) (auto simp: left_diff_distrib' ln_mult)
          also have "... = x powr (\<rho> - e)"
            by (metis nless_le powr_def x_pos)
          finally have "exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                             - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) \<le> x powr (\<rho> - e)" .
          from divide_right_mono[OF this,of "x powr \<rho>"]
          show "exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                      - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) / x powr \<rho> \<le> x powr - e"
            using x_pos by(auto simp: powr_diff[symmetric])
          have "x powr (\<rho> + e) = exp ((\<rho> + e) * ln x)"
            using x_pos by(simp add: powr_def)
          also have "... = exp ((\<integral>s\<in>{t* x<..t}. - (\<rho> + e) / s \<partial>lborel))"
            using t_pos A Atx tx 
            by(subst set_integral_inverse) (auto simp: ln_mult left_diff_distrib' distrib_right)
          also have "... \<le> exp ((\<integral>s\<in>{t * x<..t}. - r s / s \<partial>lborel))"
           using integ At Atx A
            by(auto simp: set_integrable_uminus simp del: minus_add_distrib
                intro!: t_le set_integral_mono divide_right_mono set_integrable_inverse'
                set_integrable_subset[where A="{A<..t}" and B="{t * x<..t}"])
          also have "... = exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                                 - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel))"
            unfolding set_lebesgue_integral_def
            using integ At Atx tx
            by(subst Bochner_Integration.integral_diff[symmetric])
              (auto simp: set_lebesgue_integral_def set_integrable_def indicator_def
                simp del: integral_minus Bochner_Integration.integral_diff
                intro!: Bochner_Integration.integral_cong)
          finally have "x powr (\<rho> + e) \<le> exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                                               - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel))" .
          from divide_right_mono[OF this,of "x powr \<rho>"]
          show "x powr e \<le> exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                                 - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) / x powr \<rho>"
            using x_pos by(auto simp: powr_diff[symmetric])
        qed
      qed
    next
      assume x:"1 < x"
      show ?thesis
      proof(rule tendsto_sandwich_mult_const[OF _ lim_powr2 lim_powr1])
        fix e :: real
        assume e:"0 < e"
        obtain T1 where T1:"\<And>t. T1 \<le> t \<Longrightarrow> r t \<le> \<rho> + e" "\<And>t. T1 \<le> t \<Longrightarrow> \<rho> - e \<le> r t"
          using tendstoD[OF lim_r e] unfolding eventually_at_top_linorder dist_real_def
          by (metis abs_diff_le_iff less_eq_real_def)
        define T where "T \<equiv> max A T1"
        show "\<forall>\<^sub>F t in at_top.
            x powr (- e) \<le> exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                                 - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) / x powr \<rho>
      \<and> exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
              - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) / x powr \<rho>
        \<le> x powr e"
        proof(safe intro!: eventually_at_top_linorderI[where c=T])
          fix t
          assume t:"T \<le> t"
          then have t_pos:"0 < t" and tx:"t \<le> t * x"
            using A x_pos x
            by(auto simp: T_def order.strict_trans2[OF divide_pos_pos[OF A x_pos]])
          hence Atx:"A \<le> t * x" and At:"A \<le> t"
            using t tx by(auto simp: T_def order.trans)
          have t_le:"\<And>s. t \<le> s \<Longrightarrow> r s \<le> \<rho> + e" and le_t:"\<And>s. t \<le> s \<Longrightarrow> \<rho> - e \<le> r s"
            using t by(auto simp: T_def intro!:T1)
          have "exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel) - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel))
               = exp ((\<integral>s\<in>{t<..t * x}. r s / s \<partial>lborel))"
            unfolding set_lebesgue_integral_def
            using integ At Atx tx
            by(subst Bochner_Integration.integral_diff[symmetric])
              (auto simp: set_lebesgue_integral_def set_integrable_def indicator_def
                simp del: integral_minus Bochner_Integration.integral_diff
                intro!: Bochner_Integration.integral_cong)
          also have "... \<le> exp ((\<integral>s\<in>{t<..t * x}. (\<rho> + e) / s \<partial>lborel))"
            using integ At Atx A tx
            by(fastforce simp:
                intro!: t_le set_integral_mono divide_right_mono set_integrable_inverse'
                set_integrable_subset[where A="{A<..t*x}" and B="{t<..t * x}"])
          also have "... = exp ((\<rho> + e) * ln x)"
            using A Atx x_pos t_pos x
            by(subst set_integral_inverse) (auto simp: left_diff_distrib' ln_mult)
          also have "... = x powr (\<rho> + e)"
            by (metis nless_le powr_def x_pos)
          finally have "exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                              - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) \<le> x powr (\<rho> + e)" .
          from divide_right_mono[OF this,of "x powr \<rho>"]
          show "exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                      - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) / x powr \<rho> \<le> x powr e"
            using x_pos by(auto simp: powr_diff[symmetric])
          have "x powr (\<rho> - e) = exp ((\<rho> - e) * ln x)"
            using x_pos by(simp add: powr_def)
          also have "... = exp ((\<integral>s\<in>{t<..t*x}. (\<rho> - e) / s \<partial>lborel))"
            using t_pos A Atx tx 
            by(subst set_integral_inverse) (auto simp: ln_mult left_diff_distrib' distrib_right)
          also have "... \<le> exp ((\<integral>s\<in>{t<..t * x}. r s / s \<partial>lborel))"
            using integ At Atx A tx
            by(fastforce simp:
                intro!: le_t set_integral_mono divide_right_mono set_integrable_inverse'
                set_integrable_subset[where A="{A<..t*x}" and B="{t<..t * x}"])
          also have "... = exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                                - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel))"
            unfolding set_lebesgue_integral_def
            using integ At Atx tx
            by(subst Bochner_Integration.integral_diff[symmetric])
              (auto simp: set_lebesgue_integral_def set_integrable_def indicator_def
                simp del: integral_minus Bochner_Integration.integral_diff
                intro!: Bochner_Integration.integral_cong)
          finally have "x powr (\<rho> - e) \<le> exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                                               - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel))" .
          from divide_right_mono[OF this,of "x powr \<rho>"]
          show "x powr (- e) \<le> exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel)
                                     - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)) / x powr \<rho>"
            using x_pos by(auto simp: powr_diff[symmetric])
        qed
      qed
    qed simp
  qed
  have "((\<lambda>t. (c (t * x) / c t)
          * exp ((\<integral>s\<in>{A<..t * x}. r s / s \<partial>lborel) - (\<integral>s\<in>{A<..t}. r s / s \<partial>lborel)))
       \<longlongrightarrow> x powr \<rho>) at_top"
    using tendsto_mult[OF ** ***] C_pos by simp 
  thus "((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<rho>) at_top"
    using tendsto_cong * by fast
qed(use assms Karamata_representation_ex in blast)+

subsubsection \<open>Theorems Obtained from Karamata's Representation Theorem\<close>
lemma
  assumes rv:"regularly_varying U \<rho>"
  shows regularly_varying_pos_at_top:"0 < \<rho> \<Longrightarrow> filterlim U at_top at_top"
    and regularly_varying_neg_at_top:"\<rho> < 0 \<Longrightarrow> (U \<longlongrightarrow> 0) at_top"
proof -
  let ?h = "\<lambda>x. ln (U (exp x))"
  from Karamata_representation_ln_exp[OF rv]
  obtain A c e C where A:"0 < A"
    and eq_h: "\<And>x. ln A \<le> x \<Longrightarrow> ?h x = c x + \<rho> * ln A + (\<integral>u\<in>{ln A<..x}. \<rho> + e u \<partial>lborel)"
    and integrable: "\<And>x. ln A \<le> x \<Longrightarrow>  set_integrable lborel {ln A<..x} e"
    and lim_e: "(e \<longlongrightarrow> 0) at_top"
    and lim_c: "(c \<longlongrightarrow> C) at_top"
    by blast
  obtain X1 where X1:"\<And>x. X1 \<le> x \<Longrightarrow> C - 1 < c x" "\<And>x. X1 \<le> x \<Longrightarrow> c x < C + 1"
    using tendstoD[OF lim_c,of 1]
    unfolding eventually_at_top_linorder dist_real_def abs_less_iff
    by fastforce
  have lim_h_pos: "0 < \<rho> \<Longrightarrow> filterlim ?h at_top at_top"
  proof -
    assume rho:"0 < \<rho>"
    obtain X2 where X2:"\<And>x. X2 \<le> x \<Longrightarrow> \<bar>e x\<bar> < \<rho> / 2"
      using tendstoD[OF lim_e half_gt_zero[OF rho]]
      by (metis (no_types, lifting) eventually_at_top_linorder norm_conv_dist real_norm_def)
    define X where "X \<equiv> max (ln A) (max X1 X2)"
    have le_X:"ln A \<le> X" "X1 \<le> X" "X2 \<le> X"
      by(simp_all add: X_def)
    have X:"\<And>x. X \<le> x \<Longrightarrow> - \<rho> / 2 \<le> e x" "\<And>x. X \<le> x \<Longrightarrow> C - 1 \<le> c x"
      using X2 X1 X_def by force+
    have "\<forall>\<^sub>F x in at_top. ?h x \<ge> C - 1 + \<rho> * ln A + (\<integral>u\<in>{ln A<..X}. \<rho> + e u \<partial>lborel)
                                  + (- \<rho> / 2) * X + (\<rho> / 2) * x" (is "\<forall>\<^sub>F x in at_top. ?h x \<ge> ?f x")
    proof(rule eventually_at_top_linorderI[where c=X])
      fix x
      assume x:"X \<le> x"
      have "?f x = C - 1 + \<rho> * ln A + (\<integral>u\<in>{ln A<..X}. \<rho> + e u \<partial>lborel) + (\<rho> / 2) * (x - X)"
        by argo
      also have "... = C - 1 + \<rho> * ln A
                       + ((\<integral>u\<in>{ln A<..X}. \<rho> + e u \<partial>lborel) + (\<integral>u\<in>{X<..x}. \<rho> / 2 \<partial>lborel))"
        by(simp add: interval_integral_Ioc[OF x,symmetric])
      also have "... \<le> C - 1 + \<rho> * ln A
                       + ((\<integral>u\<in>{ln A<..X}. \<rho> + e u \<partial>lborel) + (\<integral>u\<in>{X<..x}. \<rho> + e u \<partial>lborel))"
        using X x le_X by(auto simp del: set_integral_divide_zero
            simp: real_0_le_add_iff minus_divide_le_eq
            intro!: set_integral_mono_banach set_integrable_subset[OF integrable[of x]]
            set_integrable_const)
      also have "... = C - 1 + \<rho> * ln A + ((\<integral>u\<in>{ln A<..X} \<union> {X<..x}. \<rho> + e u \<partial>lborel))"
        using le_X x by(auto intro!: set_integral_Un[symmetric]
            set_integrable_subset[OF integrable[of x]] set_integrable_const)
      also have "... = C - 1 + \<rho> * ln A + ((\<integral>u\<in>{ln A<..x}. \<rho> + e u \<partial>lborel))"
        using x le_X by(subst ivl_disj_un_two) auto
      also have "... \<le> ?h x"
        using le_X x X by(simp add: eq_h[of x])
      finally show "?f x \<le> ?h x" .
    qed
    moreover have "filterlim ?f at_top at_top"
      by(intro filterlim_tendsto_add_at_top
          filterlim_tendsto_pos_mult_at_top[OF _ half_gt_zero[OF rho]] filterlim_ident)
         blast+
    ultimately show ?thesis
      using filterlim_at_top_mono by fast
  qed
  show "filterlim U at_top at_top" if rho:"0 < \<rho>"
  proof -
    note filterlim_compose[OF exp_at_top filterlim_compose[OF lim_h_pos[OF rho] ln_at_top]]
    moreover have "\<forall>\<^sub>F x in at_top. exp (?h (ln x)) = U x"
      using regularly_varying_pos[OF rv] by(auto intro!: eventually_at_top_linorderI[where c=1])
    ultimately show ?thesis
      by(simp cong: filterlim_cong)
  qed
  have lim_h_neg: "\<rho> < 0 \<Longrightarrow> filterlim ?h at_bot at_top"
  proof -
    assume rho:"\<rho> < 0"
    obtain X2 where X2:"\<And>x. X2 \<le> x \<Longrightarrow> \<bar>e x\<bar> < - \<rho> / 2"
      using tendstoD[OF lim_e half_gt_zero[OF neg_0_less_iff_less[THEN iffD2,OF rho]]]
      by (metis (no_types, lifting) eventually_at_top_linorder norm_conv_dist real_norm_def)
    define X where "X \<equiv> max (ln A) (max X1 X2)"
    have le_X:"ln A \<le> X" "X1 \<le> X" "X2 \<le> X"
      by(simp_all add: X_def)
    have X:"\<And>x. X \<le> x \<Longrightarrow> e x \<le> - \<rho> / 2" "\<And>x. X \<le> x \<Longrightarrow> c x \<le> C + 1"
      using X2 X1 X_def by force+
    have "\<forall>\<^sub>F x in at_top. ?h x \<le> C + 1 + \<rho> * ln A + (\<integral>u\<in>{ln A<..X}. \<rho> + e u \<partial>lborel)
                                  + (- \<rho> / 2) * X + (\<rho> / 2) * x"
         (is "\<forall>\<^sub>F x in at_top. ?h x \<le> ?g x")
    proof(rule eventually_at_top_linorderI[where c=X])
      fix x
      assume x:"X \<le> x"
      have "?h x \<le> C + 1 + \<rho> * ln A + ((\<integral>u\<in>{ln A<..x}. \<rho> + e u \<partial>lborel))"
        using le_X x X by(simp add: eq_h[of x])
      also have "... = C + 1 + \<rho> * ln A + ((\<integral>u\<in>{ln A<..X} \<union> {X<..x}. \<rho> + e u \<partial>lborel))"
        using x le_X by(subst ivl_disj_un_two) auto
      also have "... = C + 1 + \<rho> * ln A
                       + ((\<integral>u\<in>{ln A<..X}. \<rho> + e u \<partial>lborel) + (\<integral>u\<in>{X<..x}. \<rho> + e u \<partial>lborel))"
        using le_X x by(auto intro!: set_integral_Un
            set_integrable_subset[OF integrable[of x]] set_integrable_const)
      also have "... \<le> C + 1 + \<rho> * ln A
                       + ((\<integral>u\<in>{ln A<..X}. \<rho> + e u \<partial>lborel) + (\<integral>u\<in>{X<..x}. \<rho> / 2 \<partial>lborel))"
        using X x le_X by(auto simp del: set_integral_divide_zero
            simp: real_add_le_0_iff le_minus_divide_eq
            intro!: set_integral_mono_banach set_integrable_subset[OF integrable[of x]]
            set_integrable_const)
      also have "... = ?g x"
        by(simp add: interval_integral_Ioc[OF x,symmetric] right_diff_distrib)
      finally show "?h x \<le> ?g x" .
    qed
    moreover have "filterlim ?g at_bot at_top"
      using rho
      by (intro filterlim_tendsto_add_at_bot_iff[THEN iffD2]
          filterlim_tendsto_neg_mult_at_bot[where c="\<rho> / 2"] filterlim_ident)
          fastforce+
    ultimately show ?thesis
      using filterlim_at_bot_mono by fast
  qed
  show "(U \<longlongrightarrow> 0) at_top" if rho:"\<rho> < 0"
  proof -
    note filterlim_compose[OF exp_at_bot filterlim_compose[OF lim_h_neg[OF rho] ln_at_top]]
    moreover have "\<forall>\<^sub>F x in at_top. exp (?h (ln x)) = U x"
      using regularly_varying_pos[OF rv] by(auto intro!: eventually_at_top_linorderI[where c=1])
    ultimately show ?thesis
      by(simp cong: filterlim_cong)
  qed
qed

subsubsection \<open>Uniform Convergence Theorem for $\rho \neq 0$\<close>
corollary regularly_varying_pos_UCT:
  assumes rv:"regularly_varying U \<rho>"
    and bdd:"\<And>x. 0 < x \<Longrightarrow> bounded (U ` {0<..x})"
    and rho:"0 < \<rho>"
    and a: "0 < a"
  shows "uniform_limit {0<..a} (\<lambda>t x. U (t * x) / U t) (\<lambda>x. x powr \<rho>) at_top"
  unfolding uniform_limit_iff dist_real_def
proof safe
  fix e :: real
  assume e:"0 < e"
  define e' where "e' \<equiv> min e (1 / 2)"
  have e'_pos:"0 < e'" and e'_le_1:"e' < 1"
    using e by(simp_all add: e'_def)
  obtain i where i_pos:"0 < i" and i:"\<rho> - i > 0"
    using rho dense by auto
  from Karamata_representation_ex[OF rv]
  obtain A c r C where A_pos:"0 < A"
    and eq_U:"\<And>x. A \<le> x \<Longrightarrow> U x = c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)"
    and integ:"\<And>x. A \<le> x \<Longrightarrow> set_integrable lborel {A<..x} (\<lambda>t. r t / t)"
    and lim_r:"(r \<longlongrightarrow> \<rho>) at_top"
    and r_meas[measurable]: "r \<in> borel_measurable borel"
    and lim_c:"(c \<longlongrightarrow> C) at_top"
    and C_pos:"0 < C"
    by blast
  define X where "X \<equiv> min (min (1 / 2) ((e' / 4) powr (1 / \<rho>))) ((e' / 16) powr (1 / (\<rho> - i)))"
  have X_pos:"0 < X" and X_le_1:"X < 1"
    and X_e':"X powr \<rho> < e' / 2"
    using e'_pos rho by(auto simp: X_def powr_powr simp del: less_divide_eq_numeral1
        intro!: order.strict_trans1[OF powr_mono2[OF _ _ min.coboundedI2[THEN min.coboundedI1]]])
  have X_e2':"X powr (\<rho> - i) < e' / 8"
    using e'_pos e'_le_1 i by(auto simp: X_def powr_powr simp del: less_divide_eq_numeral1
        intro!: order.strict_trans1[OF powr_mono2[OF _ _ min.coboundedI2]]
        order.strict_trans2[OF powr_less_mono'[where x="e' / 8" and a = i]])
  have X_e:"\<And>x. 0 < x \<Longrightarrow> x \<le> X \<Longrightarrow> x powr \<rho> < e / 2"
    using X_e' by (smt (verit, del_insts) rho e'_def field_sum_of_halves powr_mono2)
  have X_e2:"x powr (\<rho> - i) < e / 8" if xX:"x \<le> X" and x:"0 < x" for x
    using i
    by(intro order.strict_trans2[OF order.strict_trans1
          [OF powr_mono2[OF _ less_imp_le[OF x] xX,of "\<rho> - i"] X_e2']])
      (simp_all add: e'_def)
  obtain T1 where T1:"\<And>x. T1 \<le> x \<Longrightarrow> \<rho> - i \<le> r x" "\<And>x. T1 \<le> x \<Longrightarrow> 0 < r x"
    using tendstoD[OF lim_r i_pos] tendstoD[OF lim_r rho] rho i_pos i
    unfolding eventually_at_top_linorder dist_real_def abs_less_iff
    by fastforce
  obtain T2 where T2':"\<And>x. T2 \<le> x \<Longrightarrow> \<bar>c x - C\<bar> \<le> C / 2"
    using tendstoD[OF lim_c half_gt_zero[OF C_pos]]
    unfolding eventually_at_top_linorder dist_real_def
    by fastforce
  have T2:"C / 2 \<le> c x" "c x \<le> 2 * C" if x:"T2 \<le> x" for x
    using T2'[OF x] by argo+

  define L where "L \<equiv> \<lambda>x. U x / x powr \<rho>"
  have sv:"slowly_varying L"
    by(simp add: regularly_varying_iff_slowly_varying_divide_powr[of U,symmetric] L_def rv)
  have "0 < e / a powr \<rho>"
    using e a by auto
  from uniform_limitD[OF slowly_varying_UCT[OF sv X_pos,of a] this]
  obtain T3 where T3:"\<And>t x. T3 \<le> t \<Longrightarrow> X \<le> x \<Longrightarrow> x \<le> a
                            \<Longrightarrow> \<bar>L (t * x) / L t - 1\<bar> < e / a powr \<rho>"
    unfolding dist_real_def eventually_at_top_linorder
    by (meson atLeastAtMost_iff)
  define T' where "T' \<equiv> max (max (max (A / X) A) T3) (max T1 T2)"
  have T':"A \<le> T'" "0 < T'" "A / X\<le> T'"
    and T'_le1:"\<And>x. T' \<le> x \<Longrightarrow> \<rho> - i \<le> r x" "\<And>x. T' \<le> x \<Longrightarrow> 0 < r x"
    and T'_le2:"\<And>x. T' \<le> x \<Longrightarrow> C / 2 \<le> c x"
    and T'_le2': "\<And>x. T' \<le> x \<Longrightarrow> c x \<le> 2 * C"
    and T'_le3:"\<And>t x. T' \<le> t \<Longrightarrow> X \<le> x \<Longrightarrow> x \<le> a \<Longrightarrow> \<bar>L (t * x) / L t - 1\<bar> < e / a powr \<rho>"
    using T1 T2 T3 A_pos by(auto simp: T'_def)
  from bdd[of T'] regularly_varying_pos[OF rv] T'
  obtain K where K:"\<And>x. 0 < x \<Longrightarrow> x \<le> T' \<Longrightarrow> \<bar>U x\<bar> \<le> K"
    unfolding bounded_iff by fastforce
  have "((\<lambda>x. K / U x) \<longlongrightarrow> 0) at_top"
    by(intro real_tendsto_divide_at_top regularly_varying_pos_at_top[OF rv rho]) auto
  then obtain T'' where T'':"\<And>t. T'' \<le> t \<Longrightarrow> \<bar>K / U t\<bar> < e / 2"
    by (metis (mono_tags, lifting) divide_pos_pos e eventually_at_top_linorder
        less_le norm_conv_dist real_norm_def tendstoD zero_le_numeral zero_neq_numeral)
  define T where "T \<equiv> max T' T''"
  have T:"T' \<le> T" "T'' \<le> T"
    by(simp_all add: T_def)
  show "\<forall>\<^sub>F t in at_top. \<forall>x\<in>{0<..a}. \<bar>U (t * x) / U t - x powr \<rho>\<bar> < e"
  proof(safe intro!: eventually_at_top_linorderI[where c=T])
    fix t x
    assume t:"T \<le> t" and "x \<in> {0<..a}"
    then have x_pos:"0 < x" and x_a: "x \<le> a"
      and T't:"T' \<le> t" and t_pos:"0 < t" and T''t:"T'' \<le> t"
      using T A_pos by (auto simp: T'_def)
    then consider "x \<le> X" "T' \<le> t * x" | "x \<le> X" "t * x \<le> T'" | "X \<le> x"
      by fastforce
    thus "\<bar>U (t * x) / U t - x powr \<rho>\<bar> < e"
    proof cases
      assume x:"X \<le> x"
      have "\<bar>U (t * x) / U t - x powr \<rho>\<bar> = x powr \<rho> * \<bar>L (t * x) / L t - 1\<bar>"
        using T T' t x_pos by(simp add: L_def powr_mult abs_mult_pos' right_diff_distrib)
      also have "... \<le> a powr \<rho> * \<bar>L (t * x) / L t - 1\<bar>"
        using x_pos x_a rho by(intro mult_mono powr_mono2) auto
      also have "... < e"
        using a mult_le_less_imp_less[OF order.refl[of "a powr \<rho>"] T'_le3[OF T't x x_a]] by force
      finally show ?thesis .
    next
     assume x:"x \<le> X" and txT:"t * x \<le> T'"
     have "\<bar>U (t * x) / U t\<bar> \<le> \<bar>K / U t\<bar>"
       using K[OF _ txT] x_pos t_pos by (simp add: divide_right_mono)
     also have "... < e / 2"
       by(intro T'' T''t)
     finally have *:"\<bar>U (t * x) / U t\<bar> < e / 2" .
     have "\<bar>U (t * x) / U t - x powr \<rho>\<bar> \<le> \<bar>U (t * x) / U t\<bar> + \<bar>x powr \<rho>\<bar>"
       by argo
     also have "... < e / 2 + e / 2"
       unfolding abs_of_nonneg[OF powr_ge_zero]
       by(intro add_strict_mono * X_e x_pos x)
     finally show ?thesis
       by simp
   next
     assume x:"x \<le> X" and Ttx:"T' \<le> t * x"
     have Atx:"A \<le> t * x" and At:"A \<le> t" and ttx:"t * x \<le> t" and tx_pos:"0 < t * x"
       using x T' t T Ttx X_pos A_pos x_pos X_le_1 by auto
      have im_ln:"ln ` {t * x<..t} = {ln (t * x) <..ln t}"
        using ttx tx_pos
        by(intro image_mono_on_continuous_on_Ioc ttx monotone_onI continuous_on_ln ln_strict_mono)
           auto
      have "U (t * x) / U t = c (t * x) * exp (\<integral>u\<in>{A<..t * x}. r u / u \<partial>lborel)
                              / (c t * exp (\<integral>u\<in>{A<..t}. r u / u \<partial>lborel))"
        by(simp add: eq_U Atx At)
      also have "... = (c (t * x) / c t) * exp ((\<integral>u\<in>{A<..t * x}. r u / u \<partial>lborel)
                                                 - (\<integral>u\<in>{A<..t}. r u / u \<partial>lborel))"
        by (simp add: exp_diff)
      also have "... \<le> (2 * C / (C / 2)) * exp ((\<integral>u\<in>{A<..t * x}. r u / u \<partial>lborel)
                                                 - (\<integral>u\<in>{A<..t}. r u / u \<partial>lborel))"
        using frac_le[OF _ T'_le2'[OF Ttx] _ T'_le2[OF T't]] C_pos by(intro mult_mono) auto
      also have "... = 4 * exp ((\<integral>u. indicat_real {A<..t * x} u * r u / u
                                    - indicat_real {A<..t} u * r u / u \<partial>lborel))"
        using integ[OF Atx] integ[OF At] C_pos
        by(auto simp: set_lebesgue_integral_def set_integrable_def)
      also have "... = 4 * exp (\<integral>u\<in>{t*x<..t}. - (r u / u) \<partial>lborel)"
        using ttx Atx At
        by(auto intro!: Bochner_Integration.integral_cong
            simp: set_lebesgue_integral_def indicator_def simp del: integral_minus)
      also have "... \<le> 4 * exp (\<integral>u\<in>{t*x<..t}. - (\<rho> - i) / u \<partial>lborel)"
        unfolding divide_minus_left
        using Atx ttx tx_pos Ttx rho i T'_le1
        by(intro mult_mono exp_mono set_integral_mono
            set_integrable_subset[THEN set_integrable_uminus[THEN iffD2],OF integ,of t])
          (fastforce simp: set_integrable_def
            intro!: integrableI_bounded_set[where A="{t * x<..t}" and B="\<bar>\<rho> - i\<bar> / (t * x)"]
            divide_mono)+
      also have "... = 4 * exp (- (\<rho> - i) * (ln t - ln (t * x)))"
        by(subst set_integral_inverse) (use ttx tx_pos in auto)
      also have "... = 4 * exp (- (\<rho> - i) * ln (1 / x))"
        using A_pos At Atx
        by(subst ln_divide_pos[symmetric]) auto
      also have "... = 4 * exp ((\<rho> - i) * ln x)"
        by(simp add: x_pos ln_divide_pos[of 1 x] minus_mult_right mult.commute)
      also have "... = 4 * x powr (\<rho> - i)"
        using x_pos i by(simp add: powr_def X_def)
      also have "... < e / 2"
        using x X_e2 x_pos by force
      finally have *:"\<bar>U (t * x) / U t\<bar> < e / 2"
        by (simp add: regularly_varying_pos[OF rv] abs_of_pos t_pos tx_pos)
      have "\<bar>U (t * x) / U t - x powr \<rho>\<bar> \<le> \<bar>U (t * x) / U t\<bar> + \<bar>x powr \<rho>\<bar>"
        by linarith
      also have "... < e / 2 + e / 2"
        using * X_e[OF x_pos x] by(intro add_strict_mono) auto
      finally show ?thesis
        by fastforce
    qed
  qed
qed

corollary regularly_varying_neg_UCT:
  assumes rv:"regularly_varying U \<rho>"
    and rho:"\<rho> < 0"
    and a: "0 < a"
  shows "uniform_limit {a..} (\<lambda>t x. U (t * x) / U t) (\<lambda>x. x powr \<rho>) at_top"
  unfolding uniform_limit_iff dist_real_def
proof safe
  fix e :: real
  assume e:"0 < e"
  obtain i where i_pos:"0 < i" and i:"\<rho> + i < 0"
    by (metis rho neg_0_less_iff_less real_add_less_0_iff real_arch_inverse)
  from Karamata_representation_ex[OF rv]
  obtain A c r C where A_pos:"0 < A"
    and eq_U:"\<And>x. A \<le> x \<Longrightarrow> U x = c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)"
    and integ:"\<And>x. A \<le> x \<Longrightarrow> set_integrable lborel {A<..x} (\<lambda>t. r t / t)"
    and lim_r:"(r \<longlongrightarrow> \<rho>) at_top"
    and lim_c:"(c \<longlongrightarrow> C) at_top"
    and C_pos:"0 < C"
    by blast
  from tendstoD[OF tendsto_neg_powr[OF rho filterlim_ident] half_gt_zero[OF e]]
  obtain X1 where X1:"\<And>x. X1 \<le> x \<Longrightarrow> x powr \<rho> < e / 2"
    unfolding eventually_at_top_linorder dist_real_def by auto
  from tendstoD[OF tendsto_mult_right_zero[OF tendsto_neg_powr[OF i filterlim_ident],of 4]
      half_gt_zero[OF e]]
  obtain X2 where X2:"\<And>x. X2 \<le> x \<Longrightarrow> 4 * x powr (\<rho> + i) < e / 2"
    unfolding eventually_at_top_linorder dist_real_def by auto
  define X where "X \<equiv> max (max 1 a) (max X1 X2)"
  have X:"\<And>x. X  \<le> x \<Longrightarrow> x powr \<rho> < e / 2" "\<And>x. X \<le> x  \<Longrightarrow> 4 * x powr (\<rho> + i) < e / 2"
         "\<And>x. X \<le> x \<Longrightarrow> 0 < x powr \<rho>" "\<And>x. X \<le> x \<Longrightarrow> 0 < 4 * x powr \<rho>"
    using X1 X2 by(auto simp: X_def)
  obtain T1 where T1:"\<And>x. T1 \<le> x \<Longrightarrow> r x \<le> \<rho> + i"
    using tendstoD[OF lim_r i_pos] unfolding eventually_at_top_linorder dist_real_def abs_less_iff
    by fastforce
  obtain T2 where T2':"\<And>x. T2 \<le> x \<Longrightarrow> \<bar>c x - C\<bar> \<le> C / 2"
    using tendstoD[OF lim_c half_gt_zero[OF C_pos]]
    unfolding eventually_at_top_linorder dist_real_def
    by fastforce
  have T2:"C / 2 \<le> c x" "c x \<le> 2 * C" if x:"T2 \<le> x" for x
    using T2'[OF x] by argo+

  define L where "L \<equiv> \<lambda>x. U x / x powr \<rho>"
  have sv:"slowly_varying L"
    by(simp add: regularly_varying_iff_slowly_varying_divide_powr[of U,symmetric] L_def rv)
  have "0 < e / a powr \<rho>"
    using e a by auto
  from uniform_limitD[OF slowly_varying_UCT[OF sv a,of X] this]
  obtain T3 where T3:"\<And>t x. T3 \<le> t \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> X \<Longrightarrow> \<bar>L (t * x) / L t - 1\<bar> < e / a powr \<rho>"
    unfolding dist_real_def eventually_at_top_linorder
    by (meson atLeastAtMost_iff)
  define T where "T \<equiv> max (max A T3) (max T1 T2)"
  have T:"A \<le> T" "0 < T"
    and T_le1:"\<And>x. T \<le> x \<Longrightarrow> r x \<le> \<rho> + i"
    and T_le2:"\<And>x. T \<le> x \<Longrightarrow> C / 2 \<le> c x" and T_le2': "\<And>x. T \<le> x \<Longrightarrow>c x \<le> 2 * C"
    and T_le3:"\<And>t x. T \<le> t \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> X \<Longrightarrow> \<bar>L (t * x) / L t - 1\<bar> < e / a powr \<rho>"
    using T1 T2 T3 A_pos by(auto simp: T_def)
  show "\<forall>\<^sub>F t in at_top. \<forall>x\<in>{a..}. \<bar>U (t * x) / U t - x powr \<rho>\<bar> < e"
  proof(safe intro!: eventually_at_top_linorderI[where c=T])
    fix t x
    assume t:"T \<le> t" and "a \<le> x"
    then consider "a \<le> x" "x \<le> X" | "X \<le> x"
      by fastforce
    thus "\<bar>U (t * x) / U t - x powr \<rho>\<bar> < e"
    proof cases
      assume x:"a \<le> x" "x \<le> X"
      have "\<bar>U (t * x) / U t - x powr \<rho>\<bar> = x powr \<rho> * \<bar>L (t * x) / L t - 1\<bar>"
        using T t x a by(simp add: L_def powr_mult abs_mult_pos' right_diff_distrib)
      also have "... \<le> a powr \<rho> * \<bar>L (t * x) / L t - 1\<bar>"
        using x a rho by(intro mult_mono powr_mono2') auto
      also have "... < e"
        using a mult_le_less_imp_less[OF order.refl[of "a powr \<rho>"] T_le3[OF t x]] by force
      finally show ?thesis .
    next
      assume x:"X \<le> x"
      have Atx:"A \<le> t * x" and At:"A \<le> t" and ttx:"t \<le> t * x"
        using x t mult_mono[of A t 1 x] A_pos by(auto simp: X_def T_def)
      hence Ttx:"T \<le> t * x"
        using t by linarith
      have im_ln:"ln ` {t<..t * x} = {ln t <..ln (t * x)}"
        using At A_pos
        by(intro image_mono_on_continuous_on_Ioc ttx monotone_onI continuous_on_ln ln_strict_mono)
          auto
      have "U (t * x) / U t = c (t * x) * exp (\<integral>u\<in>{A<..t * x}. r u / u \<partial>lborel)
                              / (c t * exp (\<integral>u\<in>{A<..t}. r u / u \<partial>lborel))"
        by(simp add: eq_U Atx At)
      also have "... = (c (t * x) / c t) * exp ((\<integral>u\<in>{A<..t * x}. r u / u \<partial>lborel)
                                                 - (\<integral>u\<in>{A<..t}. r u / u \<partial>lborel))"
        by (simp add: exp_diff)
      also have "... \<le> (2 * C / (C / 2)) * exp ((\<integral>u\<in>{A<..t * x}. r u / u \<partial>lborel)
                                                 - (\<integral>u\<in>{A<..t}. r u / u \<partial>lborel))"
        using frac_le[OF _ T_le2'[OF Ttx] _ T_le2[OF t]] C_pos by(intro mult_mono) auto
      also have "... = 4 * exp ((\<integral>u. indicat_real {A<..t * x} u * r u / u
                                     - indicat_real {A<..t} u * r u / u \<partial>lborel))"
        using integ[OF Atx] integ[OF At] C_pos
        by(auto simp: set_lebesgue_integral_def set_integrable_def)
      also have "... = 4 * exp (\<integral>u\<in>{t<..t * x}. r u / u \<partial>lborel)"
        using ttx Atx At by(auto intro!: Bochner_Integration.integral_cong
            simp: set_lebesgue_integral_def indicator_def)
      also have "... \<le> 4 * exp (\<integral>u\<in>{t<..t * x}. (\<rho> + i) / u \<partial>lborel)"
        using ttx At T_le1 T t Atx
        by(fastforce intro!: set_integral_mono set_integrable_subset[OF integ,of "t * x"]
            divide_right_mono integrableI_bounded_set[where A="{t<..t * x}" and B="\<bar>\<rho> + i\<bar> / t"]
            divide_mono simp: set_borel_measurable_def set_integrable_def)
      also have "... = 4 * exp ((\<rho> + i) * (ln (t * x) - ln t))"
        by(subst set_integral_inverse) (use A_pos At ttx in auto)
      also have "... = 4 * exp ((\<rho> + i) * ln x)"
        using A_pos At Atx
        by(subst ln_divide_pos[symmetric]) auto
      also have "... = 4 * x powr (\<rho> + i)"
        using x a by(simp add: powr_def X_def)
      also have "... < e / 2"
        using X x by blast
      finally have *:"\<bar>U (t * x) / U t\<bar> < e / 2"
        by (smt (verit, best) A_pos At rv divide_pos_pos regularly_varying_pos ttx)
      have "\<bar>U (t * x) / U t - x powr \<rho>\<bar> \<le> \<bar>U (t * x) / U t\<bar> + \<bar>x powr \<rho>\<bar>"
        by linarith
      also have "... < e / 2 + e / 2"
        using * X[OF x] by(intro add_strict_mono) auto
      finally show ?thesis
        by fastforce
    qed
  qed
qed

subsubsection \<open>Potter Bounds\<close>
corollary 
  assumes rv:"regularly_varying U \<rho>"
    and A:"1 < A" and d:"0 < d"
  shows Potter_bounds1:
    "\<exists>T>0. \<forall>x\<ge>T. \<forall>y\<ge>x. U y / U x \<le> A * (y / x) powr (\<rho> + d)" (is ?g1)
    and Potter_bounds2:
    "\<exists>T>0. \<forall>y\<ge>T. \<forall>x\<ge>y. U y / U x \<le> A * (y / x) powr (\<rho> - d)" (is ?g2)
    and Potter_bounds:
    "\<exists>T>0. \<forall>x\<ge>T. \<forall>y\<ge>T. U y / U x \<le> A * max ((y / x) powr (\<rho> + d)) ((y / x) powr (\<rho> - d))"
    (is ?g3)
proof -
  from Karamata_representation_ex[OF rv]
  obtain B c r C where A_pos:"0 < B"
    and eq_U:"\<And>x. B \<le> x \<Longrightarrow> U x = c x * exp (\<integral>t\<in>{B<..x}. r t / t \<partial>lborel)"
    and integ:"\<And>x. B \<le> x \<Longrightarrow> set_integrable lborel {B<..x} (\<lambda>t. r t / t)"
    and lim_r:"(r \<longlongrightarrow> \<rho>) at_top"
    and lim_c:"(c \<longlongrightarrow> C) at_top"
    and C_pos:"0 < C"
    by blast
  obtain T1 where T1:"\<And>t. T1 \<le> t \<Longrightarrow> r t \<le> \<rho> + d" "\<And>t. T1 \<le> t \<Longrightarrow> \<rho> - d \<le> r t"
    using tendstoD[OF lim_r d] unfolding eventually_at_top_linorder dist_real_def
    by (metis abs_diff_le_iff less_eq_real_def)
  have pos:"C * (A - 1) / (A + 1) > 0"
    using A C_pos by fastforce
  obtain T2 where "\<And>t. T2 \<le> t \<Longrightarrow> \<bar>c t - C\<bar> \<le> C * (A - 1) / (A + 1)"
    using tendstoD[OF lim_c pos] unfolding eventually_at_top_linorder dist_real_def
    by fastforce
  hence T2':"C - C * (A - 1) / (A + 1) \<le> c t" "c t \<le> C + C * (A - 1) / (A + 1)"
    if t:"T2 \<le> t" for t
    using t by(auto simp: abs_diff_le_iff)
  have ct_pos:"0 < c t" if t:"T2 \<le> t" for t
    using T2'[OF t] C_pos A
    by (smt (verit, ccfv_threshold) mult.commute le_divide_eq le_divide_eq_1
        nonzero_mult_divide_mult_cancel_left2)
  have T2:"c y / c x \<le> A" if x:"T2 \<le> x" and y:"T2 \<le> y" for x y
  proof -
    have "c y / c x \<le> (C + C * (A - 1) / (A + 1)) / (C - C * (A - 1) / (A + 1))"
      using T2'[OF x] T2'[OF y] ct_pos[OF y] C_pos A
      by(auto intro!: divide_mono simp del: times_divide_eq_right
          simp: times_divide_eq_right[symmetric])
    also have "... = (C * (1 + (A - 1) / (A + 1))) / (C * (1 - (A - 1) / (A + 1)))"
      by (simp add: distrib_left right_diff_distrib')
    also have "... = (C * ((A + 1) / (A + 1) + (A - 1) / (A + 1)))
                     / (C * ((A + 1) / (A + 1) - (A - 1) / (A + 1)))"
      using A by simp
    also have "... = A"
      unfolding add_divide_distrib[symmetric] diff_divide_distrib[symmetric]
      using C_pos A by simp
    finally show ?thesis .
  qed
  define T where "T \<equiv> max (max 1 B) (max T1 T2)"
  have T_pos: "0 < T" and TB:"B \<le> T"
    and Tr1:"\<And>t. T \<le> t \<Longrightarrow> r t \<le> \<rho> + d" and Tr2:"\<And>t. T \<le> t \<Longrightarrow> \<rho> - d \<le> r t"
    and Tc:"\<And>x y. T \<le> x \<Longrightarrow> T \<le> y \<Longrightarrow> c y / c x \<le> A"
    using T1 T2 by(auto simp: T_def)
  have 1:"U y / U x \<le> A * (y / x) powr (\<rho> + d)" if x:"T \<le> x" and xy:"x \<le> y" for x y
  proof -
    have y:"T \<le> y"
      using x xy by simp
    have "U y / U x = c y * exp (\<integral>t\<in>{B<..y}. r t / t \<partial>lborel)
                     / (c x * exp (\<integral>t\<in>{B<..x}. r t / t \<partial>lborel))"
      using x y eq_U TB by simp
    also have "... = (c y / c x)
                    * exp ((\<integral>t\<in>{B<..y}. r t / t \<partial>lborel) - (\<integral>t\<in>{B<..x}. r t / t \<partial>lborel))"
      by (simp add: exp_diff)
    also have "... \<le> A * exp ((\<integral>t\<in>{B<..y}. r t / t \<partial>lborel) - (\<integral>t\<in>{B<..x}. r t / t \<partial>lborel))"
      using Tc[OF x y] A by(intro mult_mono) auto
    also have "... = A * exp ((\<integral>t. indicat_real {B<..y} t * r t / t
                                   - indicat_real {B<..x} t * r t / t \<partial>lborel))"
      using integ[of x] integ[of y] TB x y A
      by(auto simp: set_lebesgue_integral_def set_integrable_def)
    also have "... = A * exp ((\<integral>t\<in>{x<..y}. r t / t \<partial>lborel))"
      using x y TB xy by(auto intro!: Bochner_Integration.integral_cong
          simp: set_lebesgue_integral_def indicator_def)
    also have "... \<le> A * exp ((\<integral>t\<in>{x<..y}. (\<rho> + d) / t \<partial>lborel))"
      using A x TB T_pos Tr1 y
      by(auto intro!: set_integral_mono set_integrable_subset[OF integ[of y]]
          set_integrable_inverse' divide_right_mono)
    also have "... = A * exp ((\<rho> + d) * ln (y / x))"
      using x y xy T_pos
      by(subst set_integral_inverse) (auto simp: ln_divide_pos)
    also have "... = A * (y / x) powr (\<rho> + d)"
      using x y T_pos by(simp add: powr_def)
    finally show ?thesis .
  qed
  have 2:"U y / U x \<le> A * (y / x) powr (\<rho> - d)" if yx:"y \<le> x" and y:"T \<le> y" for x y
  proof -
    have x:"T \<le> x"
      using yx y by simp
    have "U y / U x = c y * exp (\<integral>t\<in>{B<..y}. r t / t \<partial>lborel)
                     / (c x * exp (\<integral>t\<in>{B<..x}. r t / t \<partial>lborel))"
      using x y eq_U TB by simp
    also have "... = (c y / c x)
                    * exp ((\<integral>t\<in>{B<..y}. r t / t \<partial>lborel) - (\<integral>t\<in>{B<..x}. r t / t \<partial>lborel))"
      by (simp add: exp_diff)
    also have "... \<le> A * exp ((\<integral>t\<in>{B<..y}. r t / t \<partial>lborel) - (\<integral>t\<in>{B<..x}. r t / t \<partial>lborel))"
      using Tc[OF x y] A by(intro mult_mono) auto
    also have "... = A * exp ((\<integral>t. indicat_real {B<..y} t * r t / t
                                   - indicat_real {B<..x} t * r t / t \<partial>lborel))"
      using integ[of x] integ[of y] TB x y A
      by(auto simp: set_lebesgue_integral_def set_integrable_def)
    also have "... = A * exp ((\<integral>t\<in>{y<..x}. - r t / t \<partial>lborel))"
      using x y TB yx A by(auto intro!: Bochner_Integration.integral_cong
          simp: set_lebesgue_integral_def indicator_def simp del: integral_minus)
    also have "... \<le> A * exp ((\<integral>t\<in>{y<..x}. - (\<rho> - d) / t \<partial>lborel))"
      using A x TB T_pos Tr2 y yx
      by(auto intro!: set_integral_mono set_integrable_subset[OF integ[of x]]
          set_integrable_inverse' divide_right_mono simp: set_integrable_uminus
          simp del: minus_diff_eq)
    also have "... = A * exp((\<rho> - d) * ln (y / x))"
      using x y yx T_pos
      by(subst set_integral_inverse)
        (auto simp: ln_divide_pos left_diff_distrib right_diff_distrib)
    also have "... = A * (y / x) powr (\<rho> - d)"
      using x y T_pos by(simp add: powr_def)
    finally show ?thesis .
  qed
  have 3:"U y / U x \<le> A * max ((y / x) powr (\<rho> + d)) ((y / x) powr (\<rho> - d))"
    if x:"T \<le> x" and y:"T \<le> y" for x y
  proof(cases "x \<le> y")
    assume xy:"x \<le> y"
    then have "U y / U x \<le> A * (y / x) powr (\<rho> + d)"
      using 1 x by blast
    thus ?thesis
      using T_pos xy d powr_mono x by force
  next
    assume yx:"\<not> x \<le> y"
    then have "U y / U x \<le> A * (y / x) powr (\<rho> - d)"
      using 2 y by simp
    thus ?thesis
      by (smt (verit, best) A mult_mono powr_ge_zero)
  qed
  show ?g1 ?g2 ?g3
    using 1 2 3 T_pos by blast+
qed

corollary 
  assumes rv:"regularly_varying U \<rho>"
    and A:"A < 1" and d:"0 < d"
  shows Potter_bounds_lower1:
    "\<exists>T>0. \<forall>x\<ge>T. \<forall>y\<ge>x. A * (y / x) powr (\<rho> - d) \<le> U y / U x" (is ?g1)
    and Potter_bounds_lower2:
    "\<exists>T>0. \<forall>y\<ge>T. \<forall>x\<ge>y. A * (y / x) powr (\<rho> + d) \<le> U y / U x" (is ?g2)
    and Potter_bounds_lower:
    "\<exists>T>0. \<forall>x\<ge>T. \<forall>y\<ge>T. A * min ((y / x) powr (\<rho> + d)) ((y / x) powr (\<rho> - d)) \<le> U y / U x"
    (is ?g3)
proof -
  show g1:?g1
  proof(cases "A \<le> 0")
    assume "A \<le> 0"
    thus ?thesis
      by (smt (verit, best) divide_pos_pos mult_cancel_right2 mult_less_cancel_left
          powr_non_neg regularly_varying_pos rv)
  next
    assume A_pos:"\<not> A \<le> 0"
    then have invA:"1 < 1 / A"
      using A by force
    from Potter_bounds2[OF rv this d]
    obtain T where T_pos:"T > 0" and T:"\<And>x y. y \<ge> T \<Longrightarrow> x \<ge> y \<Longrightarrow>
                     U y / U x \<le> 1 / A * (y / x) powr (\<rho> - d)"
      by fast
    have "A * (y / x) powr (\<rho> - d) \<le> U y / U x" if x:"T \<le> x" and xy:"x \<le> y" for x y
    proof -
      have "1 / (1 / A * (x / y) powr (\<rho> - d)) \<le> 1 / (U x / U y)"
        using A_pos regularly_varying_pos[OF rv] T_pos x xy
        by(intro divide_left_mono T[OF x xy] T[OF x xy]) auto
      thus ?thesis
        by (simp add: powr_divide)
    qed
    thus ?thesis
      using T_pos by blast
  qed
  show g2:?g2
  proof(cases "A \<le> 0")
    assume "A \<le> 0"
    thus ?thesis
      by (smt (verit, best) divide_pos_pos mult_cancel_right2 mult_less_cancel_left
          powr_non_neg regularly_varying_pos rv)
  next
    assume A_pos:"\<not> A \<le> 0"
    then have invA:"1 < 1 / A"
      using A by force
    from Potter_bounds1[OF rv this d]
    obtain T where T_pos:"T > 0" and T:"\<And>x y. x \<ge> T \<Longrightarrow> y \<ge> x \<Longrightarrow>
                     U y / U x \<le> 1 / A * (y / x) powr (\<rho> + d)"
      by fast
    have "A * (y / x) powr (\<rho> + d) \<le> U y / U x" if y:"T \<le> y" and yx:"y \<le> x" for x y
    proof -
      have "1 / (1 / A * (x / y) powr (\<rho> + d)) \<le> 1 / (U x / U y)"
        using A_pos regularly_varying_pos[OF rv] T_pos y yx
        by(intro divide_left_mono T[OF y yx]) auto
      thus ?thesis
        by (simp add: powr_divide)
    qed
    thus ?thesis
      using T_pos by blast
  qed
  from g1 g2 obtain T1 T2 where
    T1:"T1 > 0" "\<forall>x\<ge>T1. \<forall>y\<ge>x. A * (y / x) powr (\<rho> - d) \<le> U y / U x"
    and T2:"T2 > 0" "\<forall>y\<ge>T2. \<forall>x\<ge>y. A * (y / x) powr (\<rho> + d) \<le> U y / U x"
    by auto
  thus ?g3
    by(safe intro!: exI[where x="max T1 T2"] max.strict_coboundedI1)
      (smt (verit, best) assms(3) divide_pos_pos less_divide_eq_1_pos powr_less_mono powr_mono')
qed

subsection \<open>Karamata's Theorem\<close>
subsubsection \<open>Direct Half\<close>
lemma Karamata_theorem_half1:
  assumes rv: "regularly_varying U \<rho>"
    and a: "0 \<le> a" and rho:"- 1 < \<rho>"
    and integrable:"\<And>c d. a \<le> c \<Longrightarrow> set_integrable lborel {c<..d} U"
  shows "((\<lambda>t. (\<integral>x\<in>{a<..t}. U x \<partial>lborel) / (t * U t)) \<longlongrightarrow> 1 / (\<rho> + 1)) at_top"
proof -
  obtain d where d_pos:"0 < d" and d:"d < \<rho> + 1"
    by (metis rho minus_less_iff real_0_less_add_iff real_arch_inverse)
  with Potter_bounds2[OF rv,of 2 d]
  obtain T' where T':"T' > 0" "\<And>x y. T' \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> U y / U x \<le> 2 * (y / x) powr (\<rho> - d)"
    by auto
  define T where "T \<equiv> max T' a"
  have T_pos:"0 < T" and aT:"a \<le> T"
    and T:"\<And>x y. T \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> U y / U x \<le> 2 * (y / x) powr (\<rho> - d)"
    using T' by(auto simp: T_def)
   have eq:"(\<integral>x\<in>{T<..t}. U x \<partial>lborel) / (t * U t) = (\<integral>s\<in>{T/t<..1}. U (t * s) / U t \<partial>lborel)"
    if t:"T \<le> t" for t
  proof -
    have "(\<integral>x\<in>{T<..t}. U x \<partial>lborel) = t * (\<integral>s. indicat_real {T<..t} (t * s) *\<^sub>R U (t * s) \<partial>lborel)"
      using lborel_integral_real_affine[of t "\<lambda>x. indicat_real {T<..t} x * U x" 0] T_pos t
      by(auto simp: set_lebesgue_integral_def)
    also have "... = t * (\<integral>s\<in>{T/t<..1}. U (t * s) \<partial>lborel)"
      unfolding set_lebesgue_integral_def using T_pos t
      by(intro arg_cong[where f="(*) t"]
          Bochner_Integration.integral_cong arg_cong[where f="\<lambda>y. y *\<^sub>R U (t * _)"])
        (auto simp: mult.commute indicator_def pos_divide_less_eq)
    finally show ?thesis
      using T_pos t by simp
  qed
  have "set_integrable lborel {T/t<..1} (\<lambda>s. U (t * s) / U t)"
    if t:"T < t" for t
  proof -
    have *:"indicat_real {T<..t} (t * x) = indicat_real {T/t<..1} x" for x
      using T_pos t by(auto simp: indicator_def divide_less_eq mult.commute)
    have "integrable lborel (\<lambda>x. indicat_real {T<..t} (t * x) * U (t * x))"
      using lborel_integrable_real_affine[of "\<lambda>x. indicat_real {T<..t} x * U x" t 0]
            T_pos aT integrable[of T t] t
      by(auto simp: set_integrable_def)
    thus ?thesis
      unfolding * by(simp add: set_integrable_def)
  qed
  hence *:"(\<lambda>s. indicat_real {T/t<..1} s * U (t * s) / U t) \<in> borel_measurable lborel"
    if t:"T + 1 \<le> t" for t
    using t T_pos by(auto simp: set_integrable_def)
  have **:"integrable lborel (\<lambda>s. indicator {0<..1} s * 2 * s powr (\<rho> - d))"
    using d set_integrable_mult_right_iff[THEN iffD2,OF _ set_integrable_powr_from_0[of "\<rho> - d"]]
    by(auto simp: set_integrable_def mult.assoc)
  have ***:"AE s in lborel.
             ((\<lambda>t. indicat_real {T/t<..1} s * U (t * s) / U t)
                \<longlongrightarrow> indicat_real {0<..1} s * s powr \<rho>) at_top"
  proof(rule AE_I2)
    fix s :: real
    consider "0 < s" "s \<le> 1" | "s \<le> 0" | "1 < s"
      by linarith
    then show "((\<lambda>t. indicat_real {T / t<..1} s * U (t * s) / U t)
            \<longlongrightarrow> indicat_real {0<..1} s * s powr \<rho>) at_top"
    proof cases
      assume s:"0 < s" "s \<le> 1"
      then obtain X where X:"0 < X" "T / X < s"
        by (metis linordered_field_no_ub mult.commute not_less_iff_gr_or_eq order.strict_trans
            pos_divide_less_eq)
      hence "\<And>t. X \<le> t \<Longrightarrow> T / t < s"
        by (metis T_pos order.strict_trans frac_less2 less_eq_real_def)
      hence "\<forall>\<^sub>F t in at_top. indicat_real {T / t<..1} s * U (t * s) / U t = U (t * s) / U t"
        using s by(auto intro!: eventually_at_top_linorderI[where c=X])
      moreover have "((\<lambda>t. U (t * s) / U t) \<longlongrightarrow> indicat_real {0<..1} s * s powr \<rho>) at_top"
        using regularly_varying_lim[OF rv] s
        by(simp add: indicator_def)
      ultimately show ?thesis
        by(simp only: tendsto_cong)
    next
      assume s:"s \<le> 0"
      hence "\<forall>\<^sub>F t in at_top. indicat_real {T / t<..1} s * U (t * s) / U t = 0"
        by(intro eventually_at_top_linorderI[where c=1])
          (simp add: linorder_class.not_less[of "T / _" s]
            T_pos dual_order.trans[of "0" "T / _" s]
            less_eq_real_def[of "0"])
      thus ?thesis
        using s by (simp add: tendsto_eventually)
    qed simp
  qed
  have ****:"AE x in lborel. norm (indicat_real {T / t<..1} x * U (t * x) / U t)
                      \<le> indicat_real {0<..1} x * 2 * x powr (\<rho> - d)"
    if t:"T + 1 \<le> t" for t
  proof(rule AE_I2)
    fix s::real
    consider "T / t < s" "s \<le> 1" | "s \<le> T / t" | "1 < s"
      by linarith
    then show "norm (indicat_real {T / t<..1} s * U (t * s) / U t)
                      \<le> indicat_real {0<..1} s * 2 * s powr (\<rho> - d)"
    proof cases
      assume s:"T / t < s" "s \<le> 1"
      then have Tts:"T \<le> t * s" "t * s \<le> t" and s_pos:"s > 0"
        using t T_pos by(auto simp: mult.commute pos_divide_less_eq
            order.strict_trans[of 0 "T / t" s])
      have "norm (indicat_real {T / t<..1} s * U (t * s) / U t)
            = U (t * s) / U t"
        using s T_pos t s_pos
        by(auto simp del: abs_divide intro!: abs_of_pos
            regularly_varying_pos[OF rv] divide_pos_pos)
      also have "... \<le>  indicat_real {0<..1} s * 2 * s powr (\<rho> - d)"
        using s_pos T[OF Tts] t s T_pos by auto
      finally show ?thesis .
    qed auto
  qed
  have lim:"((\<lambda>t. (\<integral>s\<in>{T/t<..1}. U (t * s) / U t \<partial>lborel))
               \<longlongrightarrow> (\<integral>s\<in>{0<..1}. s powr \<rho> \<partial>lborel)) at_top"
    using integral_dominated_convergence_real[OF _ * ** *** ****]
    by(auto simp: set_lebesgue_integral_def)
  have cong:"\<forall>\<^sub>F t in at_top.
          (\<integral>x\<in>{a<..t}. U x \<partial>lborel) / (t * U t)
           = (\<integral>x\<in>{a<..T}. U x \<partial>lborel)/ (t * U t) + (\<integral>s\<in>{T/t<..1}. U (t * s) / U t \<partial>lborel)"
  proof(safe intro!: eventually_at_top_linorderI[where c=T])
    fix t
    assume t:"T \<le> t"
    with aT have "(\<integral>x\<in>{a<..t}. U x \<partial>lborel) = (\<integral>x\<in>{a<..T} \<union> {T<..t}. U x \<partial>lborel)"
      by(intro arg_cong[where f="\<lambda>B. set_lebesgue_integral lborel B _"]) auto
    also have "... = (\<integral>x\<in>{a<..T}. U x \<partial>lborel) + (\<integral>x\<in>{T<..t}. U x \<partial>lborel)"
      by(intro set_integral_Un integrable aT) auto
    finally show "(\<integral>x\<in>{a<..t}. U x \<partial>lborel) / (t * U t)
           = (\<integral>x\<in>{a<..T}. U x \<partial>lborel)/ (t * U t) + (\<integral>s\<in>{T/t<..1}. U (t * s) / U t \<partial>lborel)"
      by(simp add: add_divide_distrib eq[OF t])
  qed
  have lim2:"((\<lambda>t. (\<integral>x\<in>{a<..T}. U x \<partial>lborel)/ (t * U t)
                    + (\<integral>s\<in>{T/t<..1}. U (t * s) / U t \<partial>lborel))
              \<longlongrightarrow> 0 + 1 / (\<rho> + 1)) at_top"
    using rho lim set_integral_powr_from_0
    by(intro tendsto_add real_tendsto_divide_at_top
        regularly_varying_pos_at_top[where \<rho>="1 + \<rho>"] regularly_varying_mult rv)
       auto
  show ?thesis
    using lim2 cong tendsto_cong
    by fastforce
qed


lemma Karamata_theorem_half_uminus1:
  assumes rv:"regularly_varying U (- 1)"
    and a: "0 \<le> a"
    and integrable:"\<And>c d. a \<le> c \<Longrightarrow> set_integrable lborel {c<..d} U"
  shows "filterlim (\<lambda>t. (\<integral>x\<in>{a<..t}. U x \<partial>lborel) / (t * U t)) at_top at_top"
  unfolding filterlim_at_top
proof safe
  fix Z :: real
  define Z' where "Z' \<equiv> max (Z + 1) 2"
  define c where "c \<equiv> exp (- Z')"
  have c_pos:"0 < c" and c_1:"c < 1"
    by (simp_all add: c_def Z'_def)
  obtain T1 where T1:"\<And>t. T1 \<le> t \<Longrightarrow> a \<le> c * t"
    by (metis mult.commute c_pos pos_divide_le_eq)
  obtain T2 where T2:"\<And>t x. T2 \<le> t \<Longrightarrow> c \<le> x \<Longrightarrow> x \<le> 1
                      \<Longrightarrow> \<bar>U (t * x) / U t - x powr (- 1)\<bar> < 1"
    using uniform_limitD[OF regularly_varying_UCT_interval[OF rv c_pos,of 1],of 1]
    by(fastforce simp: eventually_at_top_linorder dist_real_def )
  define T where "T \<equiv> max 1 (max T1 T2)"
  have Tact:"\<And>t. T \<le> t \<Longrightarrow> a \<le> c * t"
    by(auto simp: T_def intro!: T1)
  have Tle:"\<And>t x. T \<le> t \<Longrightarrow> c \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 1 / x - 1 \<le> U (t * x) / U t"
    using T2 T_def c_pos by fastforce
  show "\<forall>\<^sub>F t in at_top. Z \<le> (\<integral>x\<in>{a<..t}. U x \<partial>lborel) / (t * U t)"
  proof(safe intro!: eventually_at_top_linorderI[where c=T])
    fix t
    assume t:"T \<le> t"
    then have t_pos:"0 < t"
      by(simp add: T_def)
    have integ1[simp]:"set_integrable lborel {c * t<..t} U"
      by(auto intro!: assms Tact[OF t])
    have integ2[simp]:"set_integrable lborel {c<..1} (\<lambda>x. U (t * x) / U t)"
    proof -
      have *:"indicat_real {c * t<..t} (t * x) = indicat_real {c<..1} x" for x
        using t_pos by(auto simp: indicator_def divide_less_eq mult.commute)
      have "integrable lborel (\<lambda>x. indicat_real {c * t<..t} (t * x) * U (t * x))"
        using lborel_integrable_real_affine[of "\<lambda>x. indicat_real {c * t<..t} x * U x" t 0]
          integ1 t_pos
        unfolding set_integrable_def
        by simp
      thus ?thesis
        unfolding *  by(simp add: set_integrable_def)
    qed
    note [simp] = set_integral_diff[OF set_integrable_inverse'[OF c_pos]
          set_integrable_const[of lborel "{c<..1}"]]

    have "Z \<le> Z' - 1"
      by(simp add: Z'_def)
    also have "... = - ln c - 1"
      by(simp add: c_def)
    also have "... \<le> - ln c - (1 - c)"
      using c_1 c_pos by argo
    also have "... = (\<integral>x\<in>{c<..1}. 1 / x \<partial>lborel) - (1 - c)"
      using c_pos c_1 by(subst set_integral_inverse) auto
    also have "... = (\<integral>x\<in>{c<..1}. 1 / x \<partial>lborel) - (\<integral>x\<in>{c<..1}. 1 \<partial>lborel)"
      using c_1 by(subst set_integral_const) auto
    also have "... = (\<integral>x\<in>{c<..1}. 1 / x - 1 \<partial>lborel)"
      using c_1 by auto
    also have "... \<le> (\<integral>x\<in>{c<..1}. U (t * x) / U t \<partial>lborel)"
      using t c_1 by(intro set_integral_mono Tle) auto
    also have "... = (\<integral>x\<in>{c * t<..t}. U x \<partial>lborel) / (t * U t)"
    proof -
      have "(\<integral>x\<in>{c * t<..t}. U x \<partial>lborel)
            = t * (\<integral>s. indicat_real {c * t<..t} (t * s) *\<^sub>R U (t * s) \<partial>lborel)"
        using lborel_integral_real_affine[of t "\<lambda>x. indicat_real {c*t<..t} x * U x" 0] t_pos
        by(auto simp: set_lebesgue_integral_def)
      also have "... = t * (\<integral>s\<in>{c<..1}. U (t * s) \<partial>lborel)"
        unfolding set_lebesgue_integral_def using t_pos
        by(intro arg_cong[where f="(*) t"]
            Bochner_Integration.integral_cong arg_cong[where f="\<lambda>y. y *\<^sub>R U (t * _)"])
          (auto simp: mult.commute indicator_def pos_divide_less_eq)
      finally show ?thesis
        using t_pos by simp
    qed
    also have "... \<le> (\<integral>x\<in>{a<..t}. U x \<partial>lborel) / (t * U t)"
      using t_pos less_imp_le[OF regularly_varying_pos[OF rv]]
        integrable[OF order.refl] Tact[OF t] a
      by(intro divide_right_mono set_integral_subset) auto
    finally show "Z \<le> (\<integral>x\<in>{a<..t}. U x \<partial>lborel) / (t * U t)" .
  qed
qed

corollary Karamata_theorem_half1_inverse:
  assumes rv: "regularly_varying U \<rho>"
    and rho:"- 1 \<le> \<rho>" and a: "0 \<le> a"
    and integrable:"\<And>c d. a \<le> c \<Longrightarrow> set_integrable lborel {c<..d} U"
  shows "((\<lambda>t. (t * U t) / (\<integral>x\<in>{a<..t}. U x \<partial>lborel)) \<longlongrightarrow> \<rho> + 1) at_top"
proof(cases "\<rho> = -1")
    show "\<rho> = -1 \<Longrightarrow> ?thesis"
      using tendsto_inverse_0_at_top[OF Karamata_theorem_half_uminus1[OF _ a integrable]] rv
      by simp
qed(use assms tendsto_inverse[OF Karamata_theorem_half1] in auto)

lemma Karamata_theorem_half1_ex:
  assumes rv: "regularly_varying U \<rho>"
    and rho:"- 1 \<le> \<rho>"
  shows "\<exists>a. ((\<lambda>t. (t * U t) / (\<integral>x\<in>{a<..t}. U x \<partial>lborel)) \<longlongrightarrow> \<rho> + 1) at_top"
proof -
  from regularly_varying_eventually_locally_integrable[OF rv]
  obtain x' where x':"\<And>a b. x' \<le> a \<Longrightarrow> set_integrable lborel {a..b} U"
    by (metis (lifting) eventually_at_top_linorder)
  define x where "x \<equiv> max 0 x'"
  have x:"0 \<le> x" "\<And>c d. x \<le> c \<Longrightarrow> set_integrable lborel {c<..d} U"
    by(auto intro!: set_integrable_subset[where A="{_.._}" and B="{_<.._}"] x' simp: x_def)
  from Karamata_theorem_half1_inverse[OF rv rho this]
  show ?thesis
    by fast
qed

lemma regularly_varying_integral_limit:
  assumes rv: "regularly_varying U \<rho>"
    and rho:"- 1 \<le> \<rho>"  and a: "0 \<le> a"
    and integrable:"\<And>c d. a \<le> c \<Longrightarrow> set_integrable lborel {c<..d} U"
    and x: "0 < x"
  shows "((\<lambda>t. (\<integral>s\<in>{a<..t * x}. U s \<partial>lborel) / (\<integral>s\<in>{a<..t}. U s \<partial>lborel))
                 \<longlongrightarrow> x powr (\<rho> + 1)) at_top"
        (is "(?g \<longlongrightarrow> x powr (\<rho> + 1)) at_top")
proof(cases "\<rho> = -1")
  assume "\<rho> \<noteq> - 1"
  then have rho':"- 1 < \<rho>"
    using rho by force
  have "(\<lambda>t. (\<integral>s\<in>{a<..t * x}. U s \<partial>lborel) / (\<integral>s\<in>{a<..t}. U s \<partial>lborel)) \<sim>[at_top]
        (\<lambda>t. (t * x * U (t * x)) / (t * U t))"
    using asymp_equiv_divide[OF asymp_equivI'_const[OF
          filterlim_compose[OF Karamata_theorem_half1[OF rv a rho' integrable]
            filterlim_tendsto_pos_mult_at_top[OF tendsto_const x filterlim_ident]]]
     asymp_equivI'_const[OF Karamata_theorem_half1[OF rv a rho' integrable]]] rho'
    by(simp add: mult.commute)
  moreover have "(\<lambda>t. (t * x * U (t * x)) / (t * U t))
                 \<sim>[at_top] (\<lambda>t. (x * (U (t * x)) / U t))"
    using x regularly_varying_pos[OF rv] regularly_varying_pos[OF rv  mult_pos_pos[OF _ x]]
    by(intro asymp_equivI' tendstoI eventually_at_top_linorderI[where c=1])
      (smt (verit, ccfv_threshold) dist_real_def divide_divide_eq_right
        divide_divide_times_eq divide_eq_1_iff nonzero_mult_div_cancel_left)
  ultimately have "(\<lambda>t. (\<integral>s\<in>{a<..t * x}. U s \<partial>lborel) / (\<integral>s\<in>{a<..t}. U s \<partial>lborel))
                   \<sim>[at_top] (\<lambda>t. (x * (U (t * x)) / U t))"
    using asymp_equiv_trans by blast
  moreover have "((\<lambda>t. (x * (U (t * x)) / U t)) \<longlongrightarrow> x powr (\<rho> + 1)) at_top"
    using tendsto_mult[OF tendsto_const[of x] regularly_varying_lim[OF rv x]]
          powr_mult_base' x
    by (simp add: add.commute powr_mult_base)
  ultimately show ?thesis
    using tendsto_asymp_equiv_cong by blast
next
  assume rho':"\<rho> = - 1" 
  show ?thesis
  proof(cases "set_integrable lborel {a<..} U")
    assume h:"set_integrable lborel {a<..} U"
    then have *:"((\<lambda>t. (\<integral>s\<in>{a<..t}. U s \<partial>lborel)) \<longlongrightarrow> (\<integral>s\<in>{a<..}. U s \<partial>lborel)) at_top"
      using a
      by(intro interval_integral_inf2 less_imp_le[OF regularly_varying_pos[OF rv]]
          set_integrable_subset[OF h])
         auto
    have "0 < (\<integral>s\<in>{a<..}. U s \<partial>lborel)"
      using a
      by(auto intro!: set_integral_zero_less h regularly_varying_pos[OF rv]
          order.strict_trans2[where b="emeasure lborel {a<..a+1}" and c="emeasure lborel {a<..}",
            OF _ emeasure_mono])
    thus ?thesis
      using tendsto_divide[OF filterlim_compose[OF
            * filterlim_tendsto_pos_mult_at_top[OF tendsto_const x filterlim_ident]]
          *] x
      by(simp add: mult.commute rho')
  next
    assume h:"\<not> set_integrable lborel {a<..} U"
    have integ_infa:"(\<integral>\<^sup>+s\<in>{a<..}. ennreal (U s) \<partial>lborel) = \<top>"
    proof -
      have "\<not> (\<integral>\<^sup>+ x. ennreal \<bar>indicat_real {a<..} x * U x\<bar> \<partial>lborel) < \<infinity>"
        using h regularly_varying_meas_o[OF rv a]
        by(auto simp: set_integrable_def integrable_iff_bounded)
      moreover have "(\<integral>\<^sup>+ x. ennreal \<bar>indicat_real {a<..} x * U x\<bar> \<partial>lborel)
                      = (\<integral>\<^sup>+s\<in>{a<..}. U s \<partial>lborel)"
        using a regularly_varying_pos[OF rv]
        by(auto intro!: nn_integral_cong simp: indicator_def abs_of_pos)
      ultimately show ?thesis
        using top.not_eq_extremum by fastforce
    qed
    have filterlim1:"filterlim (\<lambda>t. (\<integral>s\<in>{a<..t}. U s \<partial>lborel)) at_top at_top"
    proof -
      have 1:"\<forall>\<^sub>F t in at_top.
             ennreal (\<integral>s\<in>{a<..t}. U s \<partial>lborel) = (\<integral>\<^sup>+s\<in>{a<..t}. ennreal (U s) \<partial>lborel)"
        using integrable[OF order.refl] a
        unfolding nn_integral_set_ennreal set_lebesgue_integral_def
        apply(intro eventually_at_top_linorderI[where c="a + 1"])
        by(subst nn_integral_eq_integral)
          (auto simp: set_integrable_def mult.commute indicator_def
            less_imp_le[OF regularly_varying_pos[OF rv]])
      have 2:"((\<lambda>t. (\<integral>\<^sup>+s\<in>{a<..t}. ennreal (U s) \<partial>lborel))
                 \<longlongrightarrow> (\<integral>\<^sup>+s\<in>{a<..}. ennreal (U s) \<partial>lborel)) at_top"
      proof(rule nn_integral_at_top_real[where K="0"])
        show "mono_on {0..} (\<lambda>r x. ennreal (U x) * indicator {a<..r} x)"
          by(auto intro!: mono_onI le_funI simp: indicator_def)
      next
        show "\<And>t. (\<lambda>x. ennreal (U x) * indicator {a<..t} x) \<in> borel_measurable lborel"
          using regularly_varying_meas_Ioc_ennreal[OF rv a] by simp
      next
        fix y
        show "((\<lambda>t. ennreal (U y) * indicator {a<..t} y) \<longlongrightarrow>
                ennreal (U y) * indicator {a<..} y) at_top"
        proof(cases "a < y")
          assume "a < y"
          then obtain T where "\<And>t. T \<le> t \<Longrightarrow> y \<le> t"
            by simp
          thus ?thesis
            unfolding mult.commute[where a="ennreal (U y)"] indicator_mult_ennreal
            by(intro tendsto_ennrealI tendstoI eventually_at_top_linorderI[where c=T])
              (auto simp: dist_real_def indicator_def)
        qed simp
      qed
      show ?thesis
        unfolding ennreal_tendsto_top_eq_at_top[symmetric]
        using 1 2 integ_infa
        by (simp add: tendsto_cong)
    qed
    have filterlim2:"filterlim (\<lambda>t. (\<integral>s\<in>{X<..t}. U s \<partial>lborel)) at_top at_top"
      if X:"a \<le> X" for X
    proof -
      have "\<forall>\<^sub>F t in at_top. (\<integral>s\<in>{a<..t}. U s \<partial>lborel)
                            = (\<integral>s\<in>{a<..X}. U s \<partial>lborel) + (\<integral>s\<in>{X<..t}. U s \<partial>lborel)"
        using X unfolding eventually_at_top_linorder
        by(subst set_integral_Un[symmetric])
          (auto intro!: integrable arg_cong[where f="\<lambda>B. (\<integral>s\<in>B. U s \<partial>lborel)"] exI[where x=X])
      hence "\<forall>\<^sub>F t in at_top. (\<integral>s\<in>{X<..t}. U s \<partial>lborel)
                              = - (\<integral>s\<in>{a<..X}. U s \<partial>lborel) + (\<integral>s\<in>{a<..t}. U s \<partial>lborel)"
        by (rule eventually_mono) simp
      moreover have "filterlim (\<lambda>t. - (\<integral>s\<in>{a<..X}. U s \<partial>lborel) + (\<integral>s\<in>{a<..t}. U s \<partial>lborel))
                               at_top at_top"
        by(subst filterlim_tendsto_add_at_top_iff)
          (auto simp: filterlim1)
      ultimately show ?thesis
        by(simp add: filterlim_cong)
    qed
    have integ_pos:"\<And>b c. a \<le> b \<Longrightarrow> b < c \<Longrightarrow> 0 < (\<integral>s\<in>{b<..c}. U s \<partial>lborel)"
      using a
      by(intro set_integral_zero_less set_integrable_subset[OF integrable])
        (auto intro!: regularly_varying_pos[OF rv])
    have integ_le_0:"\<forall>\<^sub>F t in at_top. 0 < (\<integral>s\<in>{X<..t}. U s \<partial>lborel)" if X:"a \<le> X" for X
      using filterlim_at_top_dense[THEN iffD1,OF filterlim2[OF X]]
      by fast
    have asymp_eq:"(\<lambda>t. (\<integral>s\<in>{a<..t}. U s \<partial>lborel)) \<sim>[at_top] (\<lambda>t. \<integral>s\<in>{X<..t}. U s \<partial>lborel)"
      if X:"a \<le> X" for X
    proof -
      have "\<forall>\<^sub>F t in at_top. (\<integral>s\<in>{a<..t}. U s \<partial>lborel)
                            = (\<integral>s\<in>{a<..X}. U s \<partial>lborel) + (\<integral>s\<in>{X<..t}. U s \<partial>lborel)"
        using X unfolding eventually_at_top_linorder
        by(subst set_integral_Un[symmetric])
          (auto intro!: integrable arg_cong[where f="\<lambda>B. (\<integral>s\<in>B. U s \<partial>lborel)"] exI[where x=X])
      hence "\<forall>\<^sub>F t in at_top. (\<integral>s\<in>{a<..t}. U s \<partial>lborel) / (\<integral>s\<in>{X<..t}. U s \<partial>lborel)
                            = (\<integral>s\<in>{a<..X}. U s \<partial>lborel) / (\<integral>s\<in>{X<..t}. U s \<partial>lborel) + 1"
        by(rule eventually_mono[OF eventually_conj[OF integ_le_0[OF X]]])
          (use filterlim_at_top[THEN iffD1,OF filterlim2[OF X]]
           in "simp add: add_divide_distrib")
      moreover have "((\<lambda>t. (\<integral>s\<in>{a<..X}. U s \<partial>lborel) / (\<integral>s\<in>{X<..t}. U s \<partial>lborel) + 1)
                      \<longlongrightarrow> 0 + 1) at_top"
        by(intro tendsto_add real_tendsto_divide_at_top filterlim2 X) auto
      ultimately show ?thesis
        by(auto intro!: asymp_equivI' simp: tendsto_cong)
    qed
    have asymp_eq':"(\<lambda>t. (\<integral>s\<in>{a<..t * x}. U s \<partial>lborel))
                     \<sim>[at_top] (\<lambda>t. \<integral>s\<in>{X<..t * x}. U s \<partial>lborel)"
      if X:"a \<le> X" for X
      using filterlim_tendsto_pos_mult_at_top[OF tendsto_const x filterlim_ident]
      by(intro asymp_equiv_compose'[OF asymp_eq] X)
        (simp add: mult.commute)
    have le1:"1
          \<le> Liminf at_top (\<lambda>t. ereal (?g t))
            + ereal e"
      and le2:"Limsup at_top (\<lambda>t. ereal (?g t))
          \<le> 1 + ereal e"
         if e:"0 < e" for e
    proof -
      define e' where "e' \<equiv> e / x"
      have e':"0 < e'"
        using e x by(simp add: e'_def)
      obtain T' where T':"\<And>t. T' \<le> t \<Longrightarrow>  \<bar>U (t * x) / U t - 1 / x\<bar> < e'"
        using tendstoD[OF regularly_varying_lim[OF rv x] e'] x
        by(auto simp: rho' eventually_at_top_linorder dist_real_def)
      define T where "T \<equiv> max 1 (max (a + 1) (max (a / x) T'))"
      have T_pos:"0 < T" and aT2:"a + 1 \<le> T" and TT':"T' \<le> T" and "a / x \<le> T"
        using x by(auto simp: T_def)
      hence aTx:"a \<le> T * x" and aT1:"a \<le> T"
        using x a pos_divide_le_eq by auto
      have T1:"T \<le> t \<Longrightarrow> U (t * x) \<le> U t * (1 / x + e')" for t
        using T'[OF order.trans[OF TT'],of t] T_pos regularly_varying_pos[OF rv,of t]
        by(auto simp: abs_less_iff diff_less_eq add.commute mult.commute pos_divide_less_eq)
      have T2:"T \<le> t \<Longrightarrow> U t * (1 / x - e') \<le> U (t * x)" for t
        using T'[OF order.trans[OF TT'],of t] T_pos regularly_varying_pos[OF rv,of t]
        by (metis (no_types, lifting) linorder_not_le abs_diff_less_iff dual_order.trans
             mult.commute mult_imp_div_pos_less not_less_iff_gr_or_eq)
      have integT:"set_integrable lborel {T<..y} (\<lambda>t. U (t * x))" for y
      proof -
        have 1:"indicat_real {T * x<..y * x} (s * x) * U (s * x)
                = indicat_real {T<..y} s * U (s * x)" for s
          using x by(auto simp: indicator_def)
        have "integrable lborel (\<lambda>t. indicat_real {T * x<..y * x} t * U t)"
          using integrable[OF aTx] unfolding set_integrable_def by simp
        from lborel_integrable_real_affine[where c=x and t=0,OF this] x
        have "integrable lborel (\<lambda>s. indicat_real {T * x<..y * x} (s * x) * U (s * x))"
          by(simp add: mult.commute)
        thus ?thesis
          unfolding 1 by(simp add: set_integrable_def)
      qed
      have "Limsup at_top (\<lambda>t. ereal (?g t))
            = Limsup at_top (\<lambda>t. ereal ((\<integral>s\<in>{T * x<..t * x}. U s \<partial>lborel)
                                        / (\<integral>s\<in>{T<..t}. U s \<partial>lborel)))"
        using aTx aT2 aT1 a T_pos x
        by(intro asymp_equiv_Limsup_cong_ereal[OF asymp_equiv_divide[OF asymp_eq'[OF aTx]
                asymp_eq[OF aT1]]]
            eventually_at_top_linorderI[where c="max (T * x + 1) (T + 1)"]
              less_imp_le divide_pos_pos )
          (auto intro!: integ_pos order.strict_trans1
            [OF aTx mult_less_cancel_right_pos[THEN iffD2,OF x]])
      also have "... = Limsup at_top
                        (\<lambda>t. ereal (x * (\<integral>s\<in>{T<..t}. U (s * x) \<partial>lborel)
                                         / (\<integral>s\<in>{T<..t}. U s \<partial>lborel)))"
      proof(intro Limsup_eq eventually_at_top_linorderI[where c="T * x + 1"])
        fix y
        assume y:"T * x + 1 \<le> y"
        have "(\<integral>s\<in>{T * x<..y * x}. U s \<partial>lborel)
               = x * (\<integral>s. indicat_real {T * x<..y * x} (s * x) * U (s * x) \<partial>lborel)"
          using x unfolding set_lebesgue_integral_def
          by(subst lborel_integral_real_affine[of x "\<lambda>t. indicat_real {T*x<..y*x} t *\<^sub>R U t" 0])
            (auto simp: mult.commute)
        also have "... = x * (\<integral>s\<in>{T<..y}. U (s * x) \<partial>lborel)"
          using x
          by(auto simp: set_lebesgue_integral_def indicator_def
              intro!: Bochner_Integration.integral_cong)
        finally show "ereal ((\<integral>s\<in>{T * x<..y * x}. U s \<partial>lborel) / (\<integral>s\<in>{T<..y}. U s \<partial>lborel))
                     = ereal (x * (\<integral>s\<in>{T<..y}. U (s * x) \<partial>lborel) / (\<integral>s\<in>{T<..y}. U s \<partial>lborel))"
          by presburger
      qed
      also have "... \<le> Limsup at_top (\<lambda>t. ereal (x * (\<integral>s\<in>{T<..t}. U s * (1 / x + e') \<partial>lborel)
                                                    / (\<integral>s\<in>{T<..t}. U s \<partial>lborel)))"
        using x
        by(auto intro!: Limsup_mono eventually_at_top_linorderI[where c="T + 1"]
            T1 mult_left_mono divide_right_mono set_integral_mono integrable[OF aT1]
             less_imp_le[OF integ_pos[OF aT1]] integT
            simp del: set_integral_mult_left)
      also have "... = Limsup at_top (\<lambda>t::real. ereal (1 + x * e'))"
        using x
        by(intro Limsup_eq eventually_mono[OF integ_le_0[OF aT1]])
          (simp add: distrib_left[of x])
      also have "... = ereal (1 + e)"
        using x by(simp add: e'_def Limsup_const)
      also have "... = 1 + ereal e"
        by simp
      finally show "Limsup at_top (\<lambda>t. ereal (?g t)) \<le> 1 + ereal e" .
      have "1 - ereal e = ereal (1 - e)"
        by (simp add: one_ereal_def)
      also have "... = Liminf at_top (\<lambda>t::real. ereal (1 - x * e'))"
        using x by(simp add: e'_def Liminf_const)
      also have "... = Liminf at_top (\<lambda>t. ereal (x * (\<integral>s\<in>{T<..t}. U s * (1 / x - e') \<partial>lborel)
                                                  / (\<integral>s\<in>{T<..t}. U s \<partial>lborel)))"
        using x e'
        by(intro Liminf_eq eventually_mono[OF integ_le_0[OF aT1]])
          (simp add: right_diff_distrib[of x])
      also have "... \<le> Liminf at_top (\<lambda>t. ereal (x * (\<integral>s\<in>{T<..t}. U (s * x) \<partial>lborel)
                                                    / (\<integral>s\<in>{T<..t}. U s \<partial>lborel)))"
        using x
        by(auto intro!: Liminf_mono eventually_at_top_linorderI[where c="T + 1"]
            T2 mult_left_mono divide_right_mono set_integral_mono integrable[OF aT1]
             less_imp_le[OF integ_pos[OF aT1]] integT
            simp del: set_integral_mult_left)
      also have "... = Liminf at_top (\<lambda>t. ereal ((\<integral>s\<in>{T * x<..t * x}. U s \<partial>lborel)
                                                  / (\<integral>s\<in>{T<..t}. U s \<partial>lborel)))"
      proof(intro Liminf_eq eventually_at_top_linorderI[where c="T * x + 1"])
        fix y
        assume y:"T * x + 1 \<le> y"
        have "(\<integral>s\<in>{T * x<..y * x}. U s \<partial>lborel)
               = x * (\<integral>s. indicat_real {T * x<..y * x} (s * x) * U (s * x) \<partial>lborel)"
          using x unfolding set_lebesgue_integral_def
          by(subst lborel_integral_real_affine
              [of x "\<lambda>t. indicat_real {T*x<..y*x} t *\<^sub>R U t" 0])
            (auto simp: mult.commute)
        also have "... = x * (\<integral>s\<in>{T<..y}. U (s * x) \<partial>lborel)"
          using x
          by(auto simp: set_lebesgue_integral_def indicator_def
              intro!: Bochner_Integration.integral_cong)
        finally show "ereal (x * (\<integral>s\<in>{T<..y}. U (s * x) \<partial>lborel) / (\<integral>s\<in>{T<..y}. U s \<partial>lborel))
                       = ereal ((\<integral>s\<in>{T * x<..y * x}. U s \<partial>lborel) / (\<integral>s\<in>{T<..y}. U s \<partial>lborel))"
          by presburger
      qed
      also have "... = Liminf at_top (\<lambda>t. ereal (?g t))"
        using aTx aT2 aT1 a T_pos x
        by(intro asymp_equiv_Liminf_cong_ereal[OF asymp_equiv_divide[OF asymp_eq'[OF aTx]
                asymp_eq[OF aT1]],symmetric]
              eventually_at_top_linorderI[where c="max (T * x + 1) (T + 1)"]
              less_imp_le divide_pos_pos)
          (auto intro!: integ_pos order.strict_trans1[OF aTx
              mult_less_cancel_right_pos[THEN iffD2,OF x]] )
      finally
      show "1
          \<le> Liminf at_top (\<lambda>t. ereal (?g t)) + ereal e"
        by (smt (verit, best) \<open>1 - ereal e = ereal (1 - e)\<close> add_mono one_ereal_def order.refl
            plus_ereal.simps(1))
    qed
    have le3:"1 \<le> Liminf at_top (\<lambda>t. ereal (?g t))"
      by(rule ereal_le_epsilon2) (intro le1)
    moreover have le4:"Limsup at_top (\<lambda>t. ereal (?g t)) \<le> 1"
      by(rule ereal_le_epsilon2) (intro le2)
    ultimately 
    have "Liminf at_top (\<lambda>t. ereal (?g t)) = ereal 1"
      and "Limsup at_top (\<lambda>t. ereal (?g t)) = ereal 1"
      using Liminf_le_Limsup[of at_top]
      by (metis (no_types, lifting) one_ereal_def order.antisym order_trans
          trivial_limit_at_top_linorder)+
    hence "((\<lambda>t. ereal (?g t)) \<longlongrightarrow> ereal 1) at_top"
      by(intro Liminf_eq_Limsup) auto
    thus ?thesis
      using x by(simp add: rho')
  qed
qed

lemma
  assumes rv: "regularly_varying U \<rho>"
    and rho:"\<rho> < - 1"
  shows Karamata_theorem_half2:"((\<lambda>t. (\<integral>x\<in>{t<..}. U x \<partial>lborel) / (t * U t))
                                 \<longlongrightarrow> - 1 / (\<rho> + 1)) at_top"
    and regularly_varying_tail_integrable:"\<exists>T>0. set_integrable lborel {T<..} U"
proof -
  obtain i where i_pos:"0 < i" and i:"\<rho> + i < -1"
    by (metis add_minus_cancel rho dense less_add_same_cancel1)
  from Potter_bounds1[OF rv _ i_pos,of 2]
  obtain T where T_pos:"0 < T"
    and T:"\<And>x y. T \<le> x \<Longrightarrow> x \<le> y
          \<Longrightarrow> U y / U x \<le> 2 * (y / x) powr (\<rho> + i)"
    by auto
  have *:"(\<lambda>s. indicat_real {1<..} s * U (t * s) / U t) \<in> borel_measurable lborel"
    if t:"T \<le> t" for t
  proof -
    have [measurable]:"(*) t \<in> restrict_space borel {0<..} \<rightarrow>\<^sub>M restrict_space borel {0<..}"
      using t T_pos
      by(auto intro!: measurable_restrict_space3)
    note [measurable] = regularly_varying_meas[OF rv]
    have [measurable]:"(\<lambda>s. U (t * s)) \<in> borel_measurable (restrict_space borel {1<..})"
      by(rule measurable_restrict_mono[where A="{0<..}"]) measurable
    have "(\<lambda>s. indicat_real {1<..} s * U (t * s) / U t) =
         (\<lambda>s. if s \<in> {1<..} then U (t * s) / U t else 0)"
      by fastforce
    also have "... \<in> borel_measurable lborel"
      by(intro measurable_restrict_space_iff[THEN iffD1]) auto
    finally show ?thesis .
  qed
  have **: "integrable lborel (\<lambda>x. indicat_real {1<..} x * 2 * x powr (\<rho> + i))"
    using set_integrable_mult_right_iff[THEN iffD2,OF _ set_integrable_powr_inf[OF i]]
    by(simp add: set_integrable_def mult.assoc)
  have ***:"AE s in lborel. ((\<lambda>t. indicat_real {1<..} s * U (t * s) / U t)
                             \<longlongrightarrow> indicat_real {1<..} s * s powr \<rho>) at_top"
    by(auto simp: indicator_def regularly_varying_lim[OF rv])
  have ****:"AE s in lborel.
     norm (indicat_real {1<..} s * U (t * s) / U t)
                      \<le> indicat_real {1<..} s * 2 * s powr (\<rho> + i)"
    if t:"T \<le> t" for t
  proof(rule AE_I2)
    fix s
    show "norm (indicat_real {1<..} s * U (t * s) / U t)
                      \<le> indicat_real {1<..} s * 2 * s powr (\<rho> + i)"
    proof(cases "1 < s")
      assume s:"1 < s"
      then have "norm (indicat_real {1<..} s * U (t * s) / U t)
                 = U (t * s) / U t"
        using regularly_varying_pos[OF rv] t T_pos
        by(fastforce simp del: abs_divide
            intro!: abs_of_pos regularly_varying_pos[OF rv] divide_pos_pos)
      also have "... \<le> indicat_real {1<..} s * 2 * s powr (\<rho> + i)"
        using T[OF t,of "t * s"] s T_pos t by auto
      finally show ?thesis .
    qed simp
  qed
  have lim:"((\<lambda>t. (\<integral>x\<in>{1<..}. U (t * x) / U t \<partial>lborel)) \<longlongrightarrow> - 1 / (\<rho> + 1)) at_top"
    using integral_dominated_convergence_real[OF _ * ** *** ****]
          set_integral_powr_inf[OF rho]
    by(auto simp: set_lebesgue_integral_def)
  have eq:"\<forall>\<^sub>F t in at_top. (\<integral>x\<in>{t<..}. U x \<partial>lborel) / (t * U t)
                           = (\<integral>x\<in>{1<..}. U (t * x) / U t \<partial>lborel)"
  proof(rule eventually_at_top_linorderI[where c=1])
    fix t :: real
    assume t:"1 \<le> t"
    have "(\<integral>x\<in>{t<..}. U x \<partial>lborel) = t * (\<integral>s. indicat_real {t<..} (t * s) *\<^sub>R U (t * s) \<partial>lborel)"
      using lborel_integral_real_affine[of t "\<lambda>x. indicat_real {t<..} x * U x" 0] t
      by(simp add: set_lebesgue_integral_def)
    also have "... = t * (\<integral>x\<in>{1<..}. U (t * x) \<partial>lborel)"
      using t
      by(auto intro!: Bochner_Integration.integral_cong
          simp: set_lebesgue_integral_def mult.commute indicator_def pos_divide_less_eq)
    finally show "(\<integral>x\<in>{t<..}. U x \<partial>lborel) / (t * U t) = (\<integral>x\<in>{1<..}. U (t * x) / U t \<partial>lborel)"
      using t by simp
  qed
  show "((\<lambda>t. (\<integral>x\<in>{t<..}. U x \<partial>lborel) / (t * U t)) \<longlongrightarrow> - 1 / (\<rho> + 1)) at_top"
    using lim eq tendsto_cong by fast
  have "set_integrable lborel {1<..} (\<lambda>x. U (t * x) / U t)" if t:"T \<le> t" for t
    using ** ****[OF t] t
    by(auto intro!: Bochner_Integration.integrable_bound
        [where f="\<lambda>s. indicat_real {1<..} s * 2 * s powr (\<rho> + i)",OF _ * ]
        simp: set_integrable_def)
  from this[OF order.refl]
  have "integrable lborel (\<lambda>x. indicat_real {1<..} (x / T) * U x / U T)"
    using lborel_integrable_real_affine
      [of  "\<lambda>x. indicat_real {1<..} x * U (T * x) / U T" "1 / T" 0]
          T_pos by(auto simp: set_integrable_def)
  from this[THEN integrable_divide[where y="1 / U T"]] regularly_varying_pos[OF rv T_pos]
  have "integrable lborel (\<lambda>x. indicat_real {1<..} (x / T) * U x)"
    by simp
  moreover have "indicat_real {1<..} (x / T) * U x = indicat_real {T<..} x * U x" for x
    using T_pos regularly_varying_pos[OF rv] by(auto simp: indicator_def)
  ultimately have "set_integrable lborel {T<..} U"
    by (simp add: set_integrable_def cong: Bochner_Integration.integrable_cong)
  thus "\<exists>T>0. set_integrable lborel {T<..} U"
    using T_pos by fast
qed

lemma Karamata_theorem_half_uminus2_at_top:
  assumes rv: "regularly_varying U (- 1)"
    and a:"0 \<le> a"
    and integ:"set_integrable lborel {a<..} U"
  shows "filterlim (\<lambda>t. (\<integral>x\<in>{t<..}. U x \<partial>lborel) / (t * U t)) at_top at_top"
  unfolding filterlim_at_top
proof safe
  fix Z :: real
  define Z' where "Z' \<equiv> max (Z + 1) 2"
  define A where "A \<equiv> exp Z'"
  have A1:"1 \<le> A"
    by(simp add: A_def Z'_def)
  obtain T1 where T1:"\<And>x t. T1 \<le> t \<Longrightarrow> 1 \<le> x \<Longrightarrow> \<bar>U (t * x) / U t - x powr (- 1)\<bar> < 1 / A"
    using uniform_limitD[OF regularly_varying_neg_UCT[OF rv,of 1],of "1 / A"] A1
    by(fastforce simp: eventually_at_top_linorder dist_real_def)
  define T where "T \<equiv> max (max 1 a) T1"
  have Tle:"\<And>t x. T \<le> t \<Longrightarrow> 1 \<le> x \<Longrightarrow> 1 / x - 1 / A \<le> U (t * x) / U t"
    using T1 T_def by fastforce
  show "\<forall>\<^sub>F t in at_top. Z \<le> (\<integral>x\<in>{t<..}. U x \<partial>lborel) / (t * U t)"
  proof(rule eventually_at_top_linorderI[where c=T])
    fix t
    assume t:"T \<le> t"
    hence t_pos:"0 < t"
      by(simp add: T_def)

    have integ1[simp]: "set_integrable lborel {t<..} U"
      using t by(auto intro!: set_integrable_subset[OF integ] simp: T_def)
    have integ2[simp]:"set_integrable lborel {1<..} (\<lambda>x. U (t * x) / U t)"
    proof -
      have *:"indicat_real {t<..} (t * x) = indicat_real {1<..} x" for x
        using t_pos by(auto simp: indicator_def divide_less_eq mult.commute)
      have "integrable lborel (\<lambda>x. indicat_real {t<..} (t * x) * U (t * x))"
        using lborel_integrable_real_affine[of "\<lambda>x. indicat_real {t<..} x * U x" t 0]
          integ1 t_pos unfolding set_integrable_def
        by simp
      thus ?thesis
        unfolding * by(simp add: set_integrable_def)
    qed
    have integ3[simp]:"set_integrable lborel {1<..A} (\<lambda>x. U (t * x) / U t)"
      by(auto intro!: set_integrable_subset[OF integ2])
    note [simp] = set_integral_diff[OF set_integrable_inverse'[of 1]
          set_integrable_const[of lborel "{1<..A}" "1 / A"]]

    have "Z \<le> ln A - 1"
      by(simp add: A_def Z'_def)
    also have "... \<le> ln A - (1 - 1 / A)"
      using A1 by simp
    also have "... = (\<integral>x\<in>{1<..A}. 1 / x \<partial>lborel) - (1 - 1 / A)"
      using A1 by(subst set_integral_inverse) auto
    also have "... = (\<integral>x\<in>{1<..A}. 1 / x \<partial>lborel) - (\<integral>x\<in>{1<..A}. 1 / A \<partial>lborel)"
      using A1 by(subst set_integral_const) (auto simp: diff_divide_distrib)
    also have "... = (\<integral>x\<in>{1<..A}. 1 / x - 1 / A \<partial>lborel)"
      using A1 by simp
    also have "... \<le> (\<integral>x\<in>{1<..A}. U (t * x) / U t \<partial>lborel)"
      using A1 by(intro set_integral_mono Tle t) auto
    also have "... \<le> (\<integral>x\<in>{1<..}. U (t * x) / U t \<partial>lborel)"
      using t_pos
      by(intro set_integral_subset)
        (auto intro!: divide_pos_pos less_imp_le[of 0] regularly_varying_pos[OF rv])
    also have "... = (\<integral>x\<in>{t<..}. U x \<partial>lborel) / (t * U t)"
    proof -
      have "(\<integral>x\<in>{t<..}. U x \<partial>lborel)
             = t * (\<integral>s. indicat_real {t<..} (t * s) *\<^sub>R U (t * s) \<partial>lborel)"
        using lborel_integral_real_affine[of t "\<lambda>x. indicat_real {t<..} x * U x" 0] t_pos
        by(simp add: set_lebesgue_integral_def)
      also have "... = t * (\<integral>x\<in>{1<..}. U (t * x) \<partial>lborel)"
        using t_pos
        by(auto intro!: Bochner_Integration.integral_cong
            simp: set_lebesgue_integral_def mult.commute indicator_def pos_divide_less_eq)
      finally show ?thesis
        using t_pos by simp
    qed
    finally show "Z \<le> (\<integral>x\<in>{t<..}. U x \<partial>lborel) / (t * U t)" .
  qed
qed

corollary Karamata_theorem_half_uminus2:
  assumes rv: "regularly_varying U (- 1)"
    and a:"0 \<le> a"
    and integ:"set_integrable lborel {a<..} U"
  shows "((\<lambda>t. (t * U t) / (\<integral>x\<in>{t<..}. U x \<partial>lborel)) \<longlongrightarrow> 0) at_top"
  using real_tendsto_divide_at_top[OF tendsto_const[of 1]
      Karamata_theorem_half_uminus2_at_top[OF assms]]
  by simp

lemma regularly_varying_integral_tail_limit:
  assumes rv: "regularly_varying U \<rho>"
    and rho:"\<rho> < - 1"
    and x: "0 < x"
  shows "((\<lambda>t. (\<integral>s\<in>{t * x<..}. U s \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel))
         \<longlongrightarrow> x powr (\<rho> + 1)) at_top"
proof -
  have "(\<lambda>t. (\<integral>s\<in>{t * x<..}. U s \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel)) \<sim>[at_top]
        (\<lambda>t. (t * x * U (t * x)) / (t * U t))"
    using asymp_equiv_divide[OF asymp_equivI'_const[OF
          filterlim_compose[OF Karamata_theorem_half2[OF rv rho]
            filterlim_tendsto_pos_mult_at_top[OF tendsto_const x filterlim_ident]]]
        asymp_equivI'_const[OF Karamata_theorem_half2[OF rv rho]]] rho
    by(simp add: mult.commute)
  moreover have "(\<lambda>t. (t * x * U (t * x)) / (t * U t))
                 \<sim>[at_top] (\<lambda>t. (x * (U (t * x)) / U t))"
    using x regularly_varying_pos[OF rv] regularly_varying_pos[OF rv  mult_pos_pos[OF _ x]]
    by(intro asymp_equivI' tendstoI eventually_at_top_linorderI[where c=1])
      (smt (verit, ccfv_threshold) dist_real_def divide_divide_eq_right
        divide_divide_times_eq divide_eq_1_iff nonzero_mult_div_cancel_left)
  ultimately have "(\<lambda>t. (\<integral>s\<in>{t * x<..}. U s \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel))
                   \<sim>[at_top] (\<lambda>t. (x * (U (t * x)) / U t))"
    using asymp_equiv_trans by blast
  moreover have "((\<lambda>t. (x * (U (t * x)) / U t)) \<longlongrightarrow> x powr (\<rho> + 1)) at_top"
    using tendsto_mult[OF tendsto_const[of x] regularly_varying_lim[OF rv x]]
          powr_mult_base' x
    by (simp add: add.commute powr_mult_base)
  ultimately show ?thesis
    using tendsto_asymp_equiv_cong by blast
qed

lemma regularly_varying_integral_tail_limit2:
  assumes rv: "regularly_varying U (- 1)"
    and integ:"set_integrable lborel {a<..} U"
    and x:"0 < x"
  shows "((\<lambda>t. (\<integral>s\<in>{t * x<..}. U s \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel)) \<longlongrightarrow> 1) at_top"
  unfolding tendsto_iff eventually_at_top_linorder dist_real_def
proof safe
  define a' where "a' \<equiv> max 1 a"
  have a':"0 < a'"
    by(simp add: a'_def)
  have integ':"\<And>t. a' \<le> t \<Longrightarrow> set_integrable lborel {t<..} U"
    by(auto intro!: set_integrable_subset[OF integ] simp: a'_def)
  fix e :: real
  assume e:"0 < e"
  define e' where "e' \<equiv> e / (2 * x)"
  have e':"0 < e'"
    using x e by(simp add: e'_def)
  obtain T' where T':"\<And>t. T' \<le> t \<Longrightarrow> \<bar>U (t * x) / U t - 1 / x\<bar> < e'"
    using tendstoD[OF regularly_varying_lim[OF rv x] e'] x
    by(auto simp: eventually_at_top_linorder dist_real_def)
  define T where "T \<equiv> max a' (max (a' / x) T')"
  have T_pos:"0 < T" and aT2:"a' \<le> T" and TT':"T' \<le> T" and "a' / x \<le> T"
    using a' x by(auto simp: T_def)
  hence aTx:"a' \<le> T * x" and aT1:"a' \<le> T"
    using x a' pos_divide_le_eq by auto
  have T1:"T \<le> t \<Longrightarrow> U (t * x) \<le> U t * (1 / x + e')" for t
    using T'[OF order.trans[OF TT'],of t] T_pos regularly_varying_pos[OF rv,of t]
    by(auto simp: abs_less_iff diff_less_eq add.commute mult.commute pos_divide_less_eq)
  have T2:"T \<le> t \<Longrightarrow> U t * (1 / x - e') \<le> U (t * x)" for t
    using T'[OF order.trans[OF TT'],of t] T_pos regularly_varying_pos[OF rv,of t]
    by (metis (no_types, lifting) linorder_not_le abs_diff_less_iff dual_order.trans
        mult.commute mult_imp_div_pos_less not_less_iff_gr_or_eq)
  have integT:"set_integrable lborel {T<..} (\<lambda>t. U (t * x))"
  proof -
    have 1:"indicat_real {T * x<..} (s * x) * U (s * x)
            = indicat_real {T<..} s * U (s * x)" for s
      using x by(auto simp: indicator_def)
    have "integrable lborel (\<lambda>t. indicat_real {T * x<..} t * U t)"
      using integ'[OF aTx] unfolding set_integrable_def by simp
    from lborel_integrable_real_affine[where c=x and t=0,OF this] x
    have "integrable lborel (\<lambda>s. indicat_real {T * x<..} (s * x) * U (s * x))"
      by(simp add: mult.commute)
    thus ?thesis
      unfolding 1 by(simp add: set_integrable_def)
  qed
  show "\<exists>T. \<forall>t\<ge>T. \<bar>(\<integral>s\<in>{t * x<..}. U s \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel) - 1\<bar> < e"
  proof(safe intro!: exI[where x=T])
    fix t
    assume t:"T \<le> t"
    then have t_pos:"0 < t"
      using T_pos by simp
    have integ_pos[arith]:"0 < (\<integral>s\<in>{t<..}. U s \<partial>lborel)"
      using t_pos
      by(intro set_integral_zero_less integ' order.trans[OF aT1 t] emeasure_mono
          order.strict_trans2[of 0 "emeasure lborel {t<..t+1}" "emeasure lborel {t<..}"])
        (auto intro!: regularly_varying_pos[OF rv])
    have eq:"(\<integral>s\<in>{t * x<..}. U s \<partial>lborel) = x * (\<integral>s\<in>{t<..}. U (s * x) \<partial>lborel)"
    proof -
      have "(\<integral>s\<in>{t * x<..}. U s \<partial>lborel)
             = x * (\<integral>s. indicat_real {t * x<..} (s * x) * U (s * x) \<partial>lborel)"
        using lborel_integral_real_affine[of x "\<lambda>s. indicat_real {t*x<..} s * U s" 0] x
        by(simp add: set_lebesgue_integral_def mult.commute)
      also have "... = x * (\<integral>s\<in>{t<..}. U (s * x) \<partial>lborel)"
        using x t_pos regularly_varying_pos[OF rv]
        by(auto simp: set_lebesgue_integral_def indicator_def
            intro!: Bochner_Integration.integral_cong)
      finally show ?thesis .
    qed
    have "(\<integral>s\<in>{t * x<..}. U s \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel)
          = x * (\<integral>s\<in>{t<..}. U (s * x) \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel)"
      by(simp add: eq)
    also have "... \<le> x * (\<integral>s\<in>{t<..}. U s * (1 / x + e') \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel)"
      using x t aT1
      by(auto simp del: set_integral_mult_left
          intro!: divide_right_mono set_integral_mono set_integrable_subset[OF integT]
                  set_integrable_mult_left[OF integ'] T1)
    also have "... < 1 + e"
      using x e by(simp add: distrib_left[of x] e'_def)
    finally have *:"(\<integral>s\<in>{t * x<..}. U s \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel)
                  < 1 + e" .
    have "1 - e < x * (\<integral>s\<in>{t<..}. U s * (1 / x - e') \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel)"
      using x e by(simp add: right_diff_distrib'[of x] e'_def)
    also have "... \<le> x * (\<integral>s\<in>{t<..}. U (s * x) \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel)"
      using x t aT1
      by(auto simp del: set_integral_mult_left
          intro!: divide_right_mono set_integral_mono set_integrable_subset[OF integT]
                  set_integrable_mult_left[OF integ'] T2)
    also have "... = (\<integral>s\<in>{t * x<..}. U s \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel)"
      by(simp add: eq)
    finally show "\<bar>(\<integral>s\<in>{t * x<..}. U s \<partial>lborel) / (\<integral>s\<in>{t<..}. U s \<partial>lborel) - 1\<bar> < e"
      using * by linarith
  qed
qed

lemma regularly_varying_integral_measurable:
  assumes rv: "regularly_varying U \<rho>"
    and a:"0 \<le> a"
  shows "(\<lambda>x. (\<integral>s\<in>{a<..x}. U s \<partial>lborel)) \<in> borel_measurable borel"
proof -
  define U' where "U' \<equiv> \<lambda>x. if x \<le> a then 0 else U x"
  have [measurable]:"U' \<in> borel_measurable borel"
    unfolding U'_def using regularly_varying_meas[OF rv] a
    by(subst measurable_If_restrict_space_iff)
      (auto intro!: measurable_restrict_mono[where A="{0<..}" and B="{x. \<not> x \<le> a}"])
  have *:"(\<lambda>x. (\<integral>s\<in>{a<..x}. U' s \<partial>lborel)) = (\<lambda>x. (\<integral>s\<in>{a<..x}. U s \<partial>lborel))"
    by (auto intro!: set_lebesgue_integral_cong simp: U'_def)
  have "(\<lambda>x. (\<integral>s\<in>{a<..x}. U' s \<partial>lborel)) \<in> borel_measurable borel"
    unfolding set_lebesgue_integral_def
    by measurable auto
  thus ?thesis
    unfolding * by simp
qed

lemma regularly_varying_tail_integral_measurable:
  assumes rv: "regularly_varying U \<rho>"
  shows "(\<lambda>x. (\<integral>s\<in>{x<..}. U s \<partial>lborel)) \<in> borel_measurable (restrict_space borel {0<..})"
proof -
  define U' where "U' \<equiv> \<lambda>x. if 0 < x then U x else 0"
  have [measurable]:"U' \<in> borel_measurable borel"
    unfolding U'_def using regularly_varying_meas[OF rv]
    by(subst measurable_If_restrict_space_iff)
      (auto intro!: measurable_restrict_mono[where A="{0<..}" and B="{x. 0 < x}"])
  have "(\<lambda>x. (\<integral>s\<in>{x<..}. U' s \<partial>lborel)) \<in> borel_measurable borel"
    unfolding set_lebesgue_integral_def
    by measurable auto
  hence *:"(\<lambda>x. (\<integral>s\<in>{x<..}. U' s \<partial>lborel)) \<in> borel_measurable (restrict_space borel {0<..})"
    using measurable_restrict_space1 by blast
  have "\<And>x. x \<in> space (restrict_space borel {0<..})
             \<Longrightarrow> (\<integral>s\<in>{x<..}. U' s \<partial>lborel) = (\<integral>s\<in>{x<..}. U s \<partial>lborel)"
    by(auto intro!: set_lebesgue_integral_cong simp: U'_def)
  from measurable_cong[OF this] *
  show ?thesis
    by fast
qed

lemma regularly_varying_integral:
  assumes rv:"regularly_varying U \<rho>"
    and rho:"- 1 \<le> \<rho>"
    and integrable:"\<And>x. set_integrable lborel {0<..x} U"
  shows "regularly_varying (\<lambda>x. (\<integral>t\<in>{0<..x}. U t \<partial>lborel)) (\<rho> + 1)"
  using regularly_varying_pos[OF rv]
  by(intro regularly_varyingI[OF _ _ regularly_varying_integral_limit] rho
      measurable_restrict_space1[OF regularly_varying_integral_measurable[OF rv]]
      rv set_integral_zero_less integrable set_integrable_subset[OF integrable])
     fastforce+

lemma regularly_varying_tail_integral:
  assumes rv:"regularly_varying U \<rho>"
    and rho:"\<rho> \<le> - 1"
    and integrable:"set_integrable lborel {0<..} U"
  shows "regularly_varying (\<lambda>x. (\<integral>t\<in>{x<..}. U t \<partial>lborel)) (\<rho> + 1)"
proof -
  have 1:"0 < x \<Longrightarrow> 0 < (\<integral>t\<in>{x<..}. U t \<partial>lborel)" for x
    by(intro set_integral_zero_less set_integrable_subset[OF integrable]
        order.strict_trans2[of 0 "emeasure lborel {x<..x+1}"
                                 "emeasure lborel {x<..}"] emeasure_mono)
      (auto intro!: regularly_varying_pos[OF rv])
  consider "\<rho> < - 1" | "\<rho> = - 1"
    using rho by argo
  thus ?thesis
  proof cases
    assume rho:"\<rho> = - 1"
    show "regularly_varying (\<lambda>x. set_lebesgue_integral lborel {x<..} U) (\<rho> + 1)"
      using rv 1
      by(auto intro!: slowly_varyingI
          [OF _ _ regularly_varying_integral_tail_limit2[OF _ integrable]]
        regularly_varying_tail_integral_measurable[OF rv] rv simp: rho)
  qed(intro regularly_varyingI[OF _ _ regularly_varying_integral_tail_limit]
      regularly_varying_tail_integral_measurable[OF rv] rv 1)
qed

subsubsection \<open>Converse Half\<close>
lemma
  assumes U_pos:"\<And>r. 0 < r \<Longrightarrow> 0 < U r"
    and U_meas:"U \<in> borel_measurable (restrict_space borel {0<..})"
    and rho:"- 1 < \<rho>" and a[arith]:"0 \<le> a"
    and lim: "((\<lambda>t. (t * U t) / (\<integral>x\<in>{a<..t}. U x \<partial>lborel)) \<longlongrightarrow> \<rho> + 1) at_top"
  shows Karamata_theorem_converse1:"regularly_varying U \<rho>"
    and Karamata_theorem_converse1_integrable:
    "\<And>c d. a \<le> c \<Longrightarrow> set_integrable lborel {c..d} U"
proof -
  show integrable:"set_integrable lborel {c..d} U" if le:"a \<le> c" for c d
  proof -
    obtain T where T:"\<And>t. T \<le> t \<Longrightarrow> 0 < t * U t / (\<integral>x\<in>{a<..t}. U x \<partial>lborel)"
      using order_tendstoD[where a=0,OF lim] rho
      by(auto simp: eventually_at_top_linorder)
    have [arith]:"a < T"
      by(rule ccontr) (use T[of T] in simp)
    have "T \<le> t \<Longrightarrow> 0 < (\<integral>x\<in>{a<..t}. U x \<partial>lborel)" for t
      using T[of t] U_pos[of t]
      by(auto simp: zero_less_divide_iff mult_less_0_iff)
    hence "T \<le> t \<Longrightarrow> set_integrable lborel {a<..t} U" for t
      using not_set_integrable_integral_eq by fastforce
    hence "T \<le> t \<Longrightarrow> set_integrable lborel {a..t} U" for t
      using set_integrable_Ioc_eq_Icc by blast
    thus "set_integrable lborel {c..d} U"
      by (metis (mono_tags, opaque_lifting) atLeastAtMost_borel atLeastatMost_subset_iff
          le le_cases set_integrable_subset sets_lborel)
  qed
  let ?F = "\<lambda>x. (\<integral>t\<in>{a<..x}. U t \<partial>lborel)"
  define g where "g \<equiv> \<lambda>t. (t * U t) / ?F t"
  have F_pos[simp]:"a < x \<Longrightarrow> 0 < ?F x" for x
    using U_pos
    by(intro set_integral_zero_less set_integrable_subset[OF integrable[of a x]]) auto
  obtain b where b[arith]:"a < b"
    using linordered_field_no_ub by blast
  have lnF_eq: "ln (?F b) + (\<integral>t\<in>{b<..x}. g t / t \<partial>lborel) = ln (?F x)"
    if x[arith]:"b \<le> x" for x
  proof -
    have "(\<integral>t\<in>{b<..x}. g t / t \<partial>lborel) = (\<integral>t\<in>{b<..x}. 1 / ?F t * U t \<partial>lborel)"
      using U_pos
      by(intro set_integral_cong) (auto simp: g_def)
    also have "... = (\<integral>t\<in>{?F b<..?F x}. 1 / t \<partial>lborel)"
      by(intro set_integral_compose_integral_Ioc U_pos integrable measurable_restrict_space1)
         auto
    also have "... = ln (?F x) - ln (?F b)"
      by(subst set_integral_inverse)
        (auto intro!: set_integral_subset set_integrable_subset
          [OF integrable[of a x]] less_imp_le[OF U_pos])
    finally show ?thesis
      by simp
  qed
  have g_integ:"set_integrable lborel {b<..x} (\<lambda>t. g t / t)"
    if x[arith]:"b \<le> x" for x
  proof -
    have 1:"set_integrable lborel {b<..x} (\<lambda>t. 1 / ?F t * U t)"
      by(intro set_integrable_compose_integral_Ioc U_pos integrable set_integrable_inverse')
         auto
    have 2:"\<And>t. t \<in> {b<..x} \<Longrightarrow> 1 / ?F t * U t = g t / t"
      by(simp add: g_def)
    show ?thesis
      using set_integrable_cong[THEN iffD1,OF refl refl 2 1]
      by fastforce
  qed
  define r where "r \<equiv> \<lambda>x. g x - 1"
  define c where "c \<equiv> \<lambda>x. g x * ?F b / b"
  define C where "C \<equiv> (\<rho> + 1) * ?F b / b"
  have 1:"\<forall>x\<ge>b. U x = c x * exp (\<integral>t\<in>{b<..x}. r t / t \<partial>lborel)"
  proof safe
    fix x
    assume x[arith]:"b \<le> x"
    have [arith]:"0 < ?F x"
      by simp
    have "U x = g x * ?F x / x"
      by(simp add: g_def)
    also have "... = g x * exp (- ln x) * exp (ln (?F x))"
      by(simp add: ln_inverse[symmetric] divide_real_def)
    also have "... = g x * exp (ln (1 / b) - (\<integral>t\<in>{b<..x}. 1 / t \<partial>lborel))
                         * exp (ln (?F b) + (\<integral>t\<in>{b<..x}. g t / t \<partial>lborel))"
      by(simp add: set_integral_inverse lnF_eq ln_divide_pos)
    also have "... = c x * exp ((\<integral>t\<in>{b<..x}. g t / t \<partial>lborel) - (\<integral>t\<in>{b<..x}. 1 / t \<partial>lborel))"
      by(simp add: c_def exp_diff exp_add)
    also have "... = c x * exp (\<integral>t\<in>{b<..x}. r t / t \<partial>lborel)"
      using g_integ[OF x] set_integrable_inverse'
      by(auto simp: r_def diff_divide_distrib)
    finally show "U x = c x * exp (\<integral>t\<in>{b<..x}. r t / t \<partial>lborel)" .
  qed
  have 2:"\<forall>x\<ge>b. set_integrable lborel {b<..x} (\<lambda>t. r t / t)"
    unfolding r_def diff_divide_distrib
    by(intro allI impI set_integral_diff set_integrable_inverse' g_integ) auto
  have 3:"(r \<longlongrightarrow> \<rho>) at_top"
    using tendsto_diff[OF lim tendsto_const[where k=1]]
    by(simp add: r_def g_def)
  have 4:"(c \<longlongrightarrow> C) at_top"
    unfolding c_def C_def times_divide_eq_right[symmetric]
    by(intro tendsto_mult) (auto simp: g_def lim)
  have 5:"0 < C"
    using rho by(simp add: C_def)
  show "regularly_varying U \<rho>"
    using 1 2 3 4 5
    by(subst Karamata_representation_iff[OF U_meas U_pos])
      (auto intro!:  exI[where x=b,OF conjI
          [OF _ exI[where x=c,OF exI[where x=r,OF exI[where x=C]]]]]
        simp del: ex_simps)
qed

lemma
  assumes U_pos:"\<And>r. 0 < r \<Longrightarrow> 0 < U r"
    and U_meas:"U \<in> borel_measurable (restrict_space borel {0<..})"
    and rho:"- 1 > \<rho>"
    and lim: "((\<lambda>t. t * U t / (\<integral>x\<in>{t<..}. U x \<partial>lborel)) \<longlongrightarrow> - (\<rho> + 1)) at_top"
  shows Karamata_theorem_converse2:"regularly_varying U \<rho>"
    and Karamata_theorem_converse2_itegrable: "\<exists>a>0. set_integrable lborel {a..} U"
proof -
  show "\<exists>a>0. set_integrable lborel {a..} U"
  proof -
    obtain T' where T':"\<And>t. T' \<le> t \<Longrightarrow> 0 < (t * U t) / (\<integral>x\<in>{t<..}. U x \<partial>lborel)"
      using order_tendstoD[where a=0,OF lim] rho
      by(auto simp: eventually_at_top_linorder)
    define a where "a \<equiv> max T' 1"
    have [arith]:"0 < a"
      by(simp add: a_def)
    have "0 < (\<integral>x\<in>{a<..}. U x \<partial>lborel)"
      using T'[of a] U_pos[of a]
      by(auto simp: a_def zero_less_divide_iff mult_less_0_iff)
    thus ?thesis
      using not_set_integrable_integral_eq
      by(fastforce intro!: exI[where x=a] simp: set_integrable_atLeast_eq[symmetric])
  qed
  then obtain a where a_pos[arith]:"0 < a"
    and integrable:"set_integrable lborel {a..} U"
    by blast
  let ?F = "\<lambda>x. (\<integral>t\<in>{x<..}. U t \<partial>lborel)"
  define g where "g \<equiv> \<lambda>x. - x * U x / ?F x"
  have F_pos[simp]:"a \<le> x \<Longrightarrow> 0 < ?F x" for x
    using U_pos
    by(intro set_integral_zero_less set_integrable_subset[OF integrable]
        order.strict_trans2[of 0 "emeasure lborel {x<..x+1}"
                                 "emeasure lborel {x<..}",OF _ emeasure_mono])
      auto
  have g_integ[simp]:"set_integrable lborel {a<..x} (\<lambda>t. g t / t)"
    if x[arith]:"a \<le> x" for x
  proof -
    have 1:"set_integrable lborel {a<..x} (\<lambda>t. - 1 / ?F t * U t)"
      by(intro set_integrable_compose_integral_tail[where a=a]
          U_pos integrable set_integrable_inverse')
        auto
    have 2:"\<And>t. t \<in> {a<..x} \<Longrightarrow> - 1 / ?F t * U t = g t / t"
      by(simp add: g_def)
    show ?thesis
      using set_integrable_cong[THEN iffD1,OF refl refl 2 1]
      by fastforce
  qed

  have lnF_eq: "ln (?F a) + (\<integral>t\<in>{a<..x}. g t / t \<partial>lborel) = ln (?F x)"
    if x[arith]:"a \<le> x" for x
  proof -
    have "(\<integral>t\<in>{a<..x}. - g t / t \<partial>lborel) = (\<integral>t\<in>{a<..x}. 1 / ?F t * U t \<partial>lborel)"
      using U_pos
      by(intro set_integral_cong) (auto simp: g_def)
    also have "... = (\<integral>t\<in>{?F x<..?F a}. 1 / t \<partial>lborel)"
      by(intro set_integral_compose_integral_tail[where a=a]
          integrable measurable_restrict_space1 U_pos)
        auto
    also have "... = ln (?F a) - ln (?F x)"
      by(subst set_integral_inverse)
        (auto intro!: set_integral_subset set_integrable_subset[OF integrable]
          less_imp_le[OF U_pos])
    finally show ?thesis
      by (simp add: set_integral_uminus)
  qed
  define r where "r \<equiv> \<lambda>x. g x - 1"
  define c where "c \<equiv> \<lambda>x. - g x * ?F a / a"
  define C where "C \<equiv> - (\<rho> + 1) * ?F a / a"
  have 1:"\<forall>x\<ge>a. U x = c x * exp (\<integral>t\<in>{a<..x}. r t / t \<partial>lborel)"
  proof safe
    fix x
    assume x[arith]:"a \<le> x"
    have [arith]:"0 < ?F x"
      by simp
    have "U x = - g x * ?F x / x"
      by(simp add: g_def)
    also have "... = - g x * exp (- ln x) * exp (ln (?F x))"
      by(simp add: ln_inverse[symmetric] divide_real_def)
    thm ln_inverse[symmetric]
    also have "... = - g x * exp (ln (1 / a) - (\<integral>t\<in>{a<..x}. 1 / t \<partial>lborel))
                           * exp (ln (?F a) + (\<integral>t\<in>{a<..x}. g t / t \<partial>lborel))"
      by(simp add: set_integral_inverse lnF_eq ln_divide_pos)
    also have "... = c x * exp ((\<integral>t\<in>{a<..x}. g t / t \<partial>lborel) - (\<integral>t\<in>{a<..x}. 1 / t \<partial>lborel))"
      by(simp add: c_def exp_diff exp_add)
    also have "... = c x * exp (\<integral>t\<in>{a<..x}. r t / t \<partial>lborel)"
      using g_integ[OF x] set_integrable_inverse'
      by(auto simp: r_def diff_divide_distrib)
    finally show "U x = c x * exp (\<integral>t\<in>{a<..x}. r t / t \<partial>lborel)" .
  qed
  have 2:"\<forall>x\<ge>a. set_integrable lborel {a<..x} (\<lambda>t. r t / t)"
    unfolding r_def diff_divide_distrib
    by(intro allI impI set_integral_diff set_integrable_inverse' g_integ) auto
  have 3:"(r \<longlongrightarrow> \<rho>) at_top"
    using tendsto_diff[OF lim tendsto_const[where k="- 1"]]
    by(simp add: r_def g_def tendsto_minus_cancel_left)
  have 4:"(c \<longlongrightarrow> C) at_top"
    unfolding c_def C_def times_divide_eq_right[symmetric] using lim
    by(intro tendsto_mult)
      (auto simp: g_def )
  have 5:"0 < C"
    using rho by(simp add: C_def)
  show "regularly_varying U \<rho>"
    using 1 2 3 4 5
    by(subst Karamata_representation_iff[OF U_meas U_pos])
      (auto intro!:  exI[where x=a,OF conjI[OF _ exI[where x=c,
              OF exI[where x=r,OF exI[where x=C]]]]]
        simp del: ex_simps)
qed

subsection \<open>Properties Related to Derivative\<close>
text \<open>Proposition~2.5 (a)~\<^cite>\<open>Resnick\<close>.\<close>
lemma deriv_ratio_regularly_varying_uniform:
  fixes U U' :: "real \<Rightarrow> real" and \<rho> a b :: real
  assumes t0: "0 < t0"
    and deriv: "\<And>t. t0 < t \<Longrightarrow> (U has_real_derivative U' t) (at t)"
    and U'cont: "continuous_on {t0<..} U'"
    and Upos: "\<And>t. t0 < t \<Longrightarrow> 0 < U t"
    and lim: "((\<lambda>t. t * U' t / U t) \<longlongrightarrow> \<rho>) at_top"
    and a: "0 < a"
  shows "uniform_limit {a..b} (\<lambda>t x. U (t * x) / U t) (\<lambda>x. x powr \<rho>) at_top"
proof -
  have Ucont:"continuous_on {t0<..} U"
    by(auto intro!: has_real_derivative_imp_continuous_on[where f'=U'] deriv)
  define V where "V \<equiv> \<lambda>x. if x \<in> {t0<..} then U x else 1"
  have V_eq_U:"\<And>x. t0 < x \<Longrightarrow> V x = U x"
    by(simp add: V_def)
  have cong:"\<forall>\<^sub>F t in at_top. \<forall>x\<in>{a..b}. V (t * x) / V t = U (t * x) / U t"
  proof(safe intro!: eventually_at_top_linorderI[where c="max (t0 + 1) ((t0 + 1) / a)"])
    fix t x
    assume "max (t0 + 1) ((t0 + 1) / a) \<le> t" "x \<in> {a..b}"
    then have "t0 < t" "t0 < t * x"
      using a t0 by(auto intro!: order.strict_trans2[of t0 "t0 + 1" "t * x"]
          order.trans[of "t0 + 1" "t * a" "t * x"] simp: pos_divide_le_eq )
    thus "V (t * x) / V t = U (t * x) / U t"
      by(simp add: V_eq_U)
  qed
  have rv:"regularly_varying V \<rho>"
  proof(subst Karamata_representation_iff)
    show "V \<in> borel_measurable (restrict_space borel {0<..})"
      unfolding V_def
      by(intro measurable_restrict_space1 borel_measurable_continuous_on_if Ucont) auto
    show V_pos:"\<And>x. 0 < V x"
      by(auto simp: V_def Upos)
    define A where "A \<equiv> t0 + 1"
    have A_pos[arith]:"0 < A" and t0A[arith]:"t0 < A"
      using t0 by(simp_all add: A_def)
    define r where "r \<equiv> \<lambda>x. x * U' x / U x"
    have r_lim:"(r \<longlongrightarrow> \<rho>) at_top"
      unfolding r_def by fact
    have deriv':"A \<le> x \<Longrightarrow> ((\<lambda>x. ln (U x)) has_real_derivative r x / x) (at x)" for x
      by(intro DERIV_cong[where X="1 / U x * U' x" and Y="r x / x"] derivative_intros deriv)
        (auto simp: r_def Upos)
    have rcont:"continuous_on {t0<..} (\<lambda>x. r x / x)"
      unfolding r_def using Upos A_pos t0A t0
      by(intro continuous_intros continuous_on_subset[OF U'cont]
          continuous_on_subset[OF Ucont] ballI dual_order.strict_implies_not_eq) auto
    have "(\<integral>t\<in>{A<..x}. r t / t \<partial>lborel) = ln (V x) - ln (V A)" if x:"A \<le> x" for x
    proof -
      have "(\<integral>t\<in>{A<..x}. r t / t \<partial>lborel) = (\<integral>t. r t / t * indicator {A..x} t \<partial>lborel)"
        unfolding LBINT_Ioc_eq_Icc by(simp add: set_lebesgue_integral_def mult.commute)
      also have "... = ln (U x) - ln (U A)"
        using x
        by(intro integral_FTC_Icc_real deriv' continuous_on_interior[OF rcont])
          (auto simp: interior_open)
      finally show ?thesis
        using x by(simp add: V_eq_U)
    qed
    hence eq:"A \<le> x \<Longrightarrow> V x = V A * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel)" for x
      using V_pos[of A] by(auto simp add: exp_diff V_pos[of x])
    have integ:"set_integrable lborel {A<..x} (\<lambda>t. r t / t)" if "A \<le> x" for x
      by(auto intro!: set_integrable_subset[OF borel_integrable_atLeastAtMost'[of A x]]
          continuous_on_subset[OF rcont])
    show "\<exists>A>0. \<exists>c r C.
              (\<forall>x \<ge> A. V x = c x * exp (\<integral>t\<in>{A<..x}. r t / t \<partial>lborel))
            \<and> (\<forall>x \<ge> A. set_integrable lborel {A<..x} (\<lambda>t. r t / t))
            \<and> (r \<longlongrightarrow> \<rho>) at_top
            \<and> (c \<longlongrightarrow> C) at_top
            \<and> 0 < C"
      using eq integ r_lim V_pos[of A] tendsto_const[of "V A"] A_pos
      by fast
  qed
  hence "uniform_limit {a..b} (\<lambda>t x. V (t * x) / V t) (\<lambda>x. x powr \<rho>) at_top"
    by(simp add: a regularly_varying_UCT_interval)
  with cong show ?thesis
    using uniform_limit_cong by fast
qed

corollary deriv_ratio_regularly_varying:
  fixes U U' :: "real \<Rightarrow> real" and \<gamma> x :: real
  assumes "0 < t0"
    and "\<And>t. t0 < t \<Longrightarrow> (U has_real_derivative U' t) (at t)"
    and "continuous_on {t0<..} U'"
    and "\<And>t. t0 < t \<Longrightarrow> 0 < U t"
    and "((\<lambda>t. t * U' t / U t) \<longlongrightarrow> \<gamma>) at_top"
    and "0 < x"
  shows "((\<lambda>t. U (t * x) / U t) \<longlongrightarrow> x powr \<gamma>) at_top"
  by(auto intro!: tendsto_uniform_limitI[OF
        deriv_ratio_regularly_varying_uniform[where a=x and b=x,OF assms]])

lemma deriv_ratio_regularly_varying_uminus:
  fixes U u :: "real \<Rightarrow> real" and \<gamma> L x :: real
  assumes t0: "0 < t0"
    and Uderiv: "\<And>t. t0 < t \<Longrightarrow> (U has_real_derivative u t) (at t)"
    and ucont: "continuous_on {t0<..} u"
    and Ult: "\<And>t. t0 < t \<Longrightarrow> U t < L"
    and lim: "((\<lambda>t. t * u t / (L - U t)) \<longlongrightarrow> - \<gamma>) at_top"
    and x: "0 < x"
  shows "((\<lambda>t. (L - U (t * x)) / (L - U t)) \<longlongrightarrow> x powr \<gamma>) at_top"
  using DERIV_diff[OF DERIV_const[of L] Uderiv] ucont tendsto_minus[OF lim]
  by(auto intro!: deriv_ratio_regularly_varying[where U'="\<lambda>x. - u x",OF t0] continuous_minus
                  Ult x simp: continuous_on_eq_continuous_within)

text \<open>Corollary~1.1.10~\<^cite>\<open>deHaanFerreira\<close>.\<close>
lemma deriv_diff_ratio_regularly_varying:
  fixes U u u' :: "real \<Rightarrow> real" and \<gamma> x :: real
  assumes t0: "0 < t0"
    and U_deriv: "\<And>t. t0 < t \<Longrightarrow> (U has_real_derivative u t) (at t)"
    and u_deriv: "\<And>t. t0 < t \<Longrightarrow> (u has_real_derivative u' t) (at t)"
    and u'_cont: "continuous_on {t0<..} u'"
    and u_pos: "\<And>t. t0 < t \<Longrightarrow> 0 < u t"
    and lim: "((\<lambda>t. t * u' t / u t) \<longlongrightarrow> \<gamma> - 1) at_top"
    and x: "0 < x"
  shows "((\<lambda>t. (U (t * x) - U t) / (t * u t))
           \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
proof -
  have u_cont:"continuous_on {t0<..} u"
    by(intro has_real_derivative_imp_continuous_on[where f'=u'] u_deriv) auto
  define v where "v \<equiv> \<lambda>x. (if x \<in> {t0<..} then u x else 1)"
  have v_eq:"\<And>t. t0 < t \<Longrightarrow> v t = u t"
    by(simp add: v_def)
  have v_pos:"\<And>t. 0 < v t"
    using u_pos by(simp add: v_def)
  have [measurable]:"v \<in> borel_measurable borel"
    unfolding v_def
    by(intro measurable_restrict_space1 borel_measurable_continuous_on_if u_cont) auto
  have rv:"regularly_varying v (\<gamma> - 1)"
  proof(safe intro!: regularly_varyingI_total)
    fix y::real
    assume "0 < y"
    then show "((\<lambda>t. v (t * y) / v t) \<longlongrightarrow> y powr (\<gamma> - 1)) at_top"
      by(intro Lim_transform_eventually
          [OF deriv_ratio_regularly_varying[OF t0 u_deriv u'_cont u_pos lim]]
          eventually_at_top_linorderI[where c="max (t0 + 1) (t0 / y + 1)"]
          arg_cong2[where f=divide,OF v_eq[symmetric] v_eq[symmetric]])
        (auto simp: field_simps)
  qed (use v_pos in auto)
  obtain t' where t':"\<And>x y. t' \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> v y / v x \<le> 2 * (y / x) powr \<gamma>"
    using Potter_bounds1[where A=2 and d=1,OF rv] by auto
  obtain t'' where t'':"\<And>x y. t'' \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> v y / v x \<le> 2 * (y / x) powr (\<gamma> - 2)"
    using Potter_bounds2[where A=2 and d=1,OF rv] by auto
  define T where "T \<equiv> max (max (t0 + 1) (t0 / x + 1)) (max t' (t'' / x + 1))"
  have T:"t0 < T" "\<And>t. T \<le> t \<Longrightarrow> t0 < t" "\<And>t. T \<le> t \<Longrightarrow> t0 < t * x" "t' \<le> T"
    "\<And>t. T \<le> t \<Longrightarrow> t'' \<le> t * x"
    and T_pos:"0 < T"
    using x t0 by(auto simp: T_def field_simps)
  have div_eq1:"T \<le> t \<Longrightarrow> 1 \<le> s \<Longrightarrow> v (t * s)/ v t = u (t * s) / u t" for t s
    using T_pos T
    by(intro arg_cong2[where f=divide,OF v_eq v_eq] order.strict_trans2[of t0 t "t * s"])
       auto
  have div_eq2:"T \<le> t \<Longrightarrow> x \<le> s \<Longrightarrow> v (t * s)/ v t = u (t * s) / u t" for t s
    using T_pos T x
    by(intro arg_cong2[where f=divide,OF v_eq v_eq] order.strict_trans2[of t0 "t * x" "t * s"])
       auto
  have leq1:"T \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> v y / v x \<le> 2 * (y / x) powr \<gamma>" for x y
    using t' t'' T by simp_all
  consider "x < 1" | "1 < x" | "x = 1"
    by linarith
  thus ?thesis
  proof cases
    assume x1:"1 < x"
    have "\<forall>\<^sub>F t in at_top. (U (t * x) - U t) / (t * u t) = (\<integral>s\<in>{1..x}. v (t * s) / v t \<partial>lborel)"
    proof(safe intro!: eventually_at_top_linorderI[where c=T])
      fix t
      assume t:"T \<le> t"
      hence t_pos:"0 < t" and t0t:"t0 < t"
        using T_pos T by simp_all
      have "(U (t * x) - U t) / (t * u t)
             = (\<integral>s. v s / (t * v t) * indicat_real {t..t * x} s \<partial>lborel)"
        using U_deriv x1 t_pos v_pos t0t
        by(subst integral_FTC_Icc_nonneg[where F="\<lambda>x. U x / (t * v t)"])
          (auto simp: v_eq[symmetric] diff_divide_distrib
              intro!: divide_nonneg_pos less_imp_le DERIV_cdivide)
      also have "... = (\<integral>s\<in>{1..x}. v (t * s) / v t \<partial>lborel)"
        using t_pos v_pos
        by(subst lborel_integral_real_affine
            [of t "\<lambda>s. v s / (t * v t) * indicat_real {t..t * x} s" 0])
          (auto simp: set_lebesgue_integral_def indicator_def
            intro!: Bochner_Integration.integral_cong)
      finally show "(U (t * x) - U t) / (t * u t) = (\<integral>s\<in>{1..x}. v (t * s) / v t \<partial>lborel)" .
    qed
    moreover have "((\<lambda>t. (\<integral>s\<in>{1..x}. v (t * s) / v t  \<partial>lborel))
                     \<longlongrightarrow> (\<integral>s\<in>{1..x}. s powr (\<gamma> - 1) \<partial>lborel)) at_top"
      unfolding set_lebesgue_integral_def
    proof(rule integral_dominated_convergence_real[OF _ _ _ AE_I2 AE_I2])
      fix t s
      assume "T \<le> t"
      thus "norm (indicat_real {1..x} s *\<^sub>R (v (t * s) / v t))
             \<le> 2 * (indicator {1..x} s *\<^sub>R s powr \<gamma>)"
        using v_pos leq1[of t "t * s"] T_pos
        by(auto simp: indicator_def abs_of_pos)
    next
      fix y
      show "((\<lambda>t. indicat_real {1..x} y *\<^sub>R (v (t * y) / v t))
             \<longlongrightarrow> indicat_real {1..x} y *\<^sub>R y powr (\<gamma> - 1)) at_top"
        using regularly_varying_lim[OF rv,of y] by(auto simp: indicator_def)
    qed(auto intro!: borel_integrable_compact continuous_on_powr continuous_on_mult
           simp del: real_scaleR_def)
    ultimately have lim':"((\<lambda>t. (U (t * x) - U t) / (t * u t))
                     \<longlongrightarrow> (\<integral>s\<in>{1..x}. s powr (\<gamma> - 1) \<partial>lborel)) at_top"
      using tendsto_cong by fast
    have "(\<integral>s\<in>{1..x}. s powr (\<gamma> - 1) \<partial>lborel) = (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
    proof(cases "\<gamma> = 0")
      assume gamma:"\<gamma> = 0"
      then have "(\<integral>s\<in>{1..x}. s powr (\<gamma> - 1) \<partial>lborel) = (\<integral>s\<in>{1<..x}. 1 / s \<partial>lborel)"
        by(auto intro!: set_integral_cong simp: LBINT_Ioc_eq_Icc )
      also have "... = ln x"
        using x1 by(simp add: set_integral_inverse)
      finally show ?thesis
        using gamma by simp
    qed(use x1 in "auto simp: set_integral_powr_Icc diff_divide_distrib")
    with lim' show ?thesis
      by simp
  next
    assume x1:"x < 1"
    have "\<forall>\<^sub>F t in at_top. (U (t * x) - U t) / (t * u t) = - (\<integral>s\<in>{x..1}. v (t * s) / v t \<partial>lborel)"
    proof(safe intro!: eventually_at_top_linorderI[where c=T])
      fix t
      assume t:"T \<le> t"
      hence t_pos:"0 < t" and t0t:"t0 < t * x" "t0 < t"
        using T_pos T by simp_all
      have "(U (t * x) - U t) / (t * u t)
             = - (\<integral>s. v s / (t * v t) * indicat_real {t * x..t} s \<partial>lborel)"
        using  x1 t_pos v_pos t0t U_deriv
        by(subst integral_FTC_Icc_nonneg[where F="\<lambda>x. U x / (t * v t)"])
          (auto simp: v_eq[symmetric] diff_divide_distrib
              intro!: divide_nonneg_pos less_imp_le DERIV_cdivide)
      also have "... = - (\<integral>s\<in>{x..1}. v (t * s) / v t \<partial>lborel)"
        using t_pos v_pos
        by(subst lborel_integral_real_affine
            [of t "\<lambda>s. v s / (t * v t) * indicat_real {t * x..t} s" 0])
          (auto simp: set_lebesgue_integral_def indicator_def
            intro!: Bochner_Integration.integral_cong)
      finally show "(U (t * x) - U t) / (t * u t) = - (\<integral>s\<in>{x..1}. v (t * s) / v t \<partial>lborel)" .
    qed
    moreover have "((\<lambda>t. (\<integral>s\<in>{x..1}. v (t * s) / v t  \<partial>lborel))
                     \<longlongrightarrow> (\<integral>s\<in>{x..1}. s powr (\<gamma> - 1) \<partial>lborel)) at_top"
      unfolding set_lebesgue_integral_def
    proof(rule integral_dominated_convergence_real[OF _ _ _ AE_I2 AE_I2])
      fix t s
      assume t:"T \<le> t"
      hence "x \<le> s \<Longrightarrow> t'' \<le> t * s"
        using T_pos t x by(auto intro!: order.trans[OF T(5)[OF t]] mult_mono)
      thus "norm (indicat_real {x..1} s *\<^sub>R (v (t * s) / v t))
            \<le> 2 * (indicator {x..1} s *\<^sub>R s powr (\<gamma> - 2))"
        using v_pos t''[of "t * s" t] T_pos t
        by(auto simp: indicator_def abs_of_pos)
    next
      fix y
      show "((\<lambda>t. indicat_real {x..1} y *\<^sub>R (v (t * y) / v t))
             \<longlongrightarrow> indicat_real {x..1} y *\<^sub>R y powr (\<gamma> - 1)) at_top"
        using regularly_varying_lim[OF rv,of y] x by(auto simp: indicator_def)
    qed(use x in "auto intro!: borel_integrable_compact continuous_on_powr continuous_on_mult
           simp del: real_scaleR_def")
    ultimately have lim':"((\<lambda>t. (U (t * x) - U t) / (t * u t))
                     \<longlongrightarrow> - (\<integral>s\<in>{x..1}. s powr (\<gamma> - 1) \<partial>lborel)) at_top"
      using tendsto_cong tendsto_minus by fast
    have "(\<integral>s\<in>{x..1}. s powr (\<gamma> - 1) \<partial>lborel) = - (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
    proof(cases "\<gamma> = 0")
      assume gamma:"\<gamma> = 0"
      then have "(\<integral>s\<in>{x..1}. s powr (\<gamma> - 1) \<partial>lborel) = (\<integral>s\<in>{x<..1}. 1 / s \<partial>lborel)"
        using x by(auto intro!: set_integral_cong simp: LBINT_Ioc_eq_Icc)
      also have "... = - ln x"
        using x x1 by(simp add: set_integral_inverse)
      finally show ?thesis
        using gamma by simp
    qed(use x1 x in "auto simp: set_integral_powr_Icc diff_divide_distrib")
    with lim' show ?thesis
      by simp
  qed simp
qed

end