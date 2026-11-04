(*  Title:   Pareto_Distribution.thy
    Author:  Michikazu Hirata
*)

subsection \<open>Generalized Pareto Distribution\<close>
theory Pareto_Distribution
imports
   Lemmas_EVT
   Extreme_Value_Distribution
begin

text \<open>We define the generalized Pareto distribution (GPD) density and cdf.\<close>
definition GPD_density :: "[real, real, real, real] \<Rightarrow> real" where
"GPD_density \<xi> \<mu> \<sigma> x \<equiv> if \<xi> = 0 then
                        if \<mu> \<le> x then exp (- (x - \<mu>) / \<sigma>) / \<sigma> else 0
                     else if \<xi> > 0 then
                        if \<mu> \<le> x then ((1 + \<xi> * (x - \<mu>) / \<sigma>) powr (- 1 - 1 / \<xi>)) / \<sigma>
                         else 0
                     else
                        if \<mu> \<le> x \<and> x \<le> \<mu> - \<sigma> / \<xi> then
                         ((1 + \<xi> * (x - \<mu>) / \<sigma>) powr (- 1 - 1 / \<xi>)) / \<sigma>
                        else 0"

lemma GPD_density_nonneg[simp]:"0 \<le> \<sigma> \<Longrightarrow> 0 \<le> GPD_density \<xi> \<mu> \<sigma> x"
  by(simp add: GPD_density_def)

lemma GPD_density_measurable[measurable]:
  "GPD_density \<xi> \<mu> \<sigma> \<in> borel_measurable borel"
  unfolding GPD_density_def by measurable

lemma GPD_density_eq_exponential_density:
  "GPD_density 0 \<mu> \<sigma> = (\<lambda>x. exponential_density (1 / \<sigma>) (x - \<mu>))"
  by(auto simp: exponential_density_def GPD_density_def)

lemma GPD_density_xi_pos:
  "0 < \<xi> \<Longrightarrow> \<mu> \<le> x
   \<Longrightarrow> GPD_density \<xi> \<mu> \<sigma> x = (1 + \<xi> * (x - \<mu>) / \<sigma>) powr (- 1 - 1 / \<xi>) / \<sigma>"
  by(simp add: GPD_density_def)

lemma GPD_density_xi_neg:
  "\<xi> < 0 \<Longrightarrow> \<mu> \<le> x \<Longrightarrow> x \<le> \<mu> - \<sigma> / \<xi>
   \<Longrightarrow> GPD_density \<xi> \<mu> \<sigma> x = (1 + \<xi> * (x - \<mu>) / \<sigma>) powr (- 1 - 1 / \<xi>) / \<sigma>"
  by(simp add: GPD_density_def)

lemma GPD_density_eq_0:
  "x < \<mu> \<Longrightarrow> GPD_density \<xi> \<mu> \<sigma> x = 0"
  by(simp add: GPD_density_def)

lemma GPD_density_xi_neg_eq_0:
  "\<xi> < 0 \<Longrightarrow> \<mu> - \<sigma> / \<xi> < x \<Longrightarrow> GPD_density \<xi> \<mu> \<sigma> x = 0"
  by(simp add: GPD_density_def)

lemma
  fixes a \<mu> \<sigma> :: real
  assumes sigma[arith]:"0 < \<sigma>"
  shows GPD_density_set_integrable0:"set_integrable lborel {..a} (GPD_density 0 \<mu> \<sigma>)"
    and GPD_density_set_integral0:
    "(\<integral>x\<in>{..a}. GPD_density 0 \<mu> \<sigma> x \<partial>lborel) = (if a < \<mu> then 0 else 1 - exp (- (a - \<mu>) / \<sigma>))"
    and GPD_density_set_nn_integral0:
    "(\<integral>\<^sup>+x\<in>{..a}. GPD_density 0 \<mu> \<sigma> x \<partial>lborel)
      = ennreal (if a < \<mu> then 0 else 1 - exp (- (a - \<mu>) / \<sigma>))"
proof -
  have *:" indicator {..a} (\<mu> + x) =  indicator {..a-\<mu>} x" for x
    by(auto simp: indicator_def)
  have "(\<integral>\<^sup>+x\<in>{..a}. GPD_density 0 \<mu> \<sigma> x \<partial>lborel)
        = (\<integral>\<^sup>+x\<in>{..a - \<mu>}. exponential_density (1 / \<sigma>) x \<partial>lborel)"
    by(subst nn_integral_real_affine
        [where t=\<mu> and c=1 and f="\<lambda>x. ennreal (GPD_density 0 \<mu> \<sigma> x) * indicator {..a} x"])
      (auto simp add: GPD_density_eq_exponential_density *)
  also have "... = ennreal (if a < \<mu> then 0 else 1 - exp (- (a - \<mu>) / \<sigma>))"
    by(simp add: nn_integral_erlang_density erlang_CDF_def minus_divide_left
        del: minus_divide_left[symmetric])
  finally show nn_eq: "(\<integral>\<^sup>+x\<in>{..a}. GPD_density 0 \<mu> \<sigma> x \<partial>lborel)
                        = ennreal (if a < \<mu> then 0 else 1 - exp (- (a - \<mu>) / \<sigma>))" .

  show integ0: "set_integrable lborel {..a} (GPD_density 0 \<mu> \<sigma>)"
    unfolding set_integrable_def
    using nn_eq
    by(auto intro!: integrableI_nn_integral_finite
        [where x="if a < \<mu> then 0 else 1 - exp (- (a - \<mu>) / \<sigma>)"]
        simp: ennreal_indicator ennreal_mult' mult.commute)
  have nonneg: "0 \<le> (\<integral>x\<in>{..a}. GPD_density 0 \<mu> \<sigma> x \<partial>lborel)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_nonneg) (auto simp: indicator_def)
  have "ennreal (\<integral>x\<in>{..a}. GPD_density 0 \<mu> \<sigma> x \<partial>lborel)
            = (\<integral>\<^sup>+x. ennreal (indicat_real {..a} x *\<^sub>R GPD_density 0 \<mu> \<sigma> x) \<partial>lborel)"
    unfolding set_lebesgue_integral_def
    by (rule nn_integral_eq_integral[symmetric])
      (use integ0[unfolded set_integrable_def] in \<open>auto simp: indicator_def\<close>)
  also have "... = (\<integral>\<^sup>+x\<in>{..a}. GPD_density 0 \<mu> \<sigma> x \<partial>lborel)"
    by (simp add: ennreal_indicator ennreal_mult' mult.commute)
  also have "... = ennreal (if a < \<mu> then 0 else 1 - exp (- (a - \<mu>) / \<sigma>))"
    using nn_eq .
  finally have eq: "ennreal (\<integral>x\<in>{..a}. GPD_density 0 \<mu> \<sigma> x \<partial>lborel)
                       = ennreal (if a < \<mu> then 0 else 1 - exp (- (a - \<mu>) / \<sigma>))" .
  show "(\<integral>x\<in>{..a}. GPD_density 0 \<mu> \<sigma> x \<partial>lborel)
         = (if a < \<mu> then 0 else 1 - exp (- (a - \<mu>) / \<sigma>))"
    by(intro ennreal_inj[THEN iffD1,OF _ _ eq] nonneg)
      (auto simp: divide_nonpos_pos)
qed

lemma
  fixes a \<mu> \<sigma> :: real
  defines "y \<equiv> (a - \<mu>) / \<sigma>"
  assumes sigma[arith]:"0 < \<sigma>"
    and amu:"a \<le> \<mu>"
  shows GPD_density_set_integrable2:"set_integrable lborel {..a} (GPD_density \<xi> \<mu> \<sigma>)"
    and GPD_density_set_integral2:"(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    and GPD_density_set_nn_integral2:"(\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
proof -
  have ae: "AE x in lborel. x \<in> {..a} \<longrightarrow> GPD_density \<xi> \<mu> \<sigma> x = 0"
    using amu by(intro AE_I[where N="{\<mu>}"]) (auto intro!: GPD_density_eq_0)
  show "set_integrable lborel {..a} (GPD_density \<xi> \<mu> \<sigma>)"
    unfolding set_integrable_def
    by(rule integrable_cong_AE[where g="\<lambda>x. 0", THEN iffD2])
      (use ae in \<open>auto elim!: eventually_mono simp: indicator_def\<close>)
  show "(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    unfolding set_lebesgue_integral_def
    by(subst integral_cong_AE[where g="\<lambda>x. 0"])
      (use ae in \<open>auto elim!: eventually_mono simp: indicator_def\<close>)
  show "(\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    by(intro nn_integral_zero')
      (use ae in \<open>auto elim!: eventually_mono simp: indicator_def\<close>)
qed

lemma
  fixes a \<mu> \<sigma> :: real
  defines "y \<equiv> (a - \<mu>) / \<sigma>"
  assumes sigma[arith]:"0 < \<sigma>"
    and xi:"\<xi> \<noteq> 0"
    and mua:"\<mu> \<le> a"
    and xiy:"- 1 \<le> \<xi> * y"
  shows GPD_density_set_integrable1:"set_integrable lborel {..a} (GPD_density \<xi> \<mu> \<sigma>)"
    and GPD_density_set_integral1:
    "(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1 - (1 + \<xi> * y) powr (- 1 / \<xi>)"
    and GPD_density_set_nn_integral1:
    "(\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = ennreal (1 - (1 + \<xi> * y) powr (- 1 / \<xi>))"
proof -
  have main: "set_integrable lborel {..a} (GPD_density \<xi> \<mu> \<sigma>) \<and>
              (\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1 - (1 + \<xi> * y) powr (- 1 / \<xi>) \<and>
              (\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
               = ennreal (1 - (1 + \<xi> * y) powr (- 1 / \<xi>))"
  proof(cases "\<mu> < a")
    assume "\<not> \<mu> < a"
    with mua
    have y0: "y = 0" and amu:"a \<le> \<mu>"
      by (simp_all add: y_def)
    from GPD_density_set_integrable2[OF sigma amu] GPD_density_set_integral2[OF sigma amu]
      GPD_density_set_nn_integral2[OF sigma amu]
    show ?thesis
      by (simp add: y0)
  next
    assume mua': "\<mu> < a"
    define g where "g \<equiv> \<lambda>t. (1 + \<xi> * (t - \<mu>) / \<sigma>) powr (- 1 - 1 / \<xi>) / \<sigma>"
    define F where "F \<equiv> \<lambda>t. - ((1 + \<xi> * (t - \<mu>) / \<sigma>) powr (- 1 / \<xi>))"
    have g_nonneg: "0 \<le> g t" for t
      by (simp add: g_def)
    have g_meas[measurable]: "g \<in> borel_measurable borel"
      unfolding g_def by measurable
    have Fmu: "F \<mu> = - 1"
      by (simp add: F_def)
    have Fa: "F a = - ((1 + \<xi> * y) powr (- 1 / \<xi>))"
      by (simp add: F_def y_def)
    have pos: "0 < 1 + \<xi> * (t - \<mu>) / \<sigma>" if t: "\<mu> < t" "t < a" for t
    proof(cases "0 < \<xi>")
      case True
      have "0 < \<xi> * (t - \<mu>) / \<sigma>"
        using t True by (intro divide_pos_pos mult_pos_pos) auto
      thus ?thesis
        by linarith
    next
      case False
      with xi have xi_neg: "\<xi> < 0"
        by simp
      have "- \<sigma> \<le> \<xi> * (a - \<mu>)"
        using xiy sigma unfolding y_def by (simp add: pos_le_divide_eq)
      moreover have "\<xi> * (a - \<mu>) < \<xi> * (t - \<mu>)"
        using t xi_neg by (intro mult_strict_left_mono_neg) auto
      ultimately have "- \<sigma> < \<xi> * (t - \<mu>)"
        by linarith
      hence "- 1 < \<xi> * (t - \<mu>) / \<sigma>"
        using sigma by (simp add: pos_less_divide_eq)
      thus ?thesis
        by linarith
    qed
    have deriv: "(F has_real_derivative g t) (at t)" if t: "\<mu> < t" "t < a" for t
      using pos[OF t] xi sigma unfolding F_def g_def
      by(auto intro!: derivative_eq_intros simp: field_simps) argo
    have isCont_g: "isCont g t" if t: "\<mu> < t" "t < a" for t
      using pos[OF t] sigma unfolding g_def
      by(intro continuous_intros) auto
    have A: "(F \<longlongrightarrow> - 1) (at_right \<mu>)"
    proof -
      have "isCont F \<mu>"
        unfolding F_def by(intro continuous_intros) auto
      from continuous_at_imp_continuous_at_within[OF this]
      show ?thesis
        by (simp add: continuous_within Fmu)
    qed
    have B: "(F \<longlongrightarrow> F a) (at_left a)"
    proof(cases "\<xi> * y = - 1")
      case False
      with xiy have "- 1 < \<xi> * ((a - \<mu>) / \<sigma>)"
        unfolding y_def by (auto simp: le_less)
      hence pos_a: "0 < 1 + \<xi> * (a - \<mu>) / \<sigma>"
        by simp
      have "isCont F a"
        unfolding F_def using pos_a by(intro continuous_intros) auto
      from continuous_at_imp_continuous_at_within[OF this]
      show ?thesis
        by (simp add: continuous_within)
    next
      case True
      have xi_neg: "\<xi> < 0"
      proof(rule ccontr)
        assume "\<not> \<xi> < 0"
        with xi have "0 < \<xi>"
          by simp
        hence "0 \<le> \<xi> * y"
          using mua by (auto intro: mult_nonneg_nonneg simp: y_def)
        with True show False
          by simp
      qed
      have p_pos: "0 < - 1 / \<xi>"
        using xi_neg by (simp add: divide_pos_neg)
      have base_a: "1 + \<xi> * (a - \<mu>) / \<sigma> = 0"
        using True by (simp add: y_def)
      have Fa0: "F a = 0"
        using xi by (simp add: F_def base_a)
      have base0: "((\<lambda>t. 1 + \<xi> * (t - \<mu>) / \<sigma>) \<longlongrightarrow> 0) (at_left a)"
        unfolding base_a[symmetric]
        by (intro tendsto_intros) auto
      have ev_nonneg: "\<forall>\<^sub>F t in at_left a. 0 \<le> 1 + \<xi> * (t - \<mu>) / \<sigma>"
        by (intro eventually_at_leftI[of \<mu>]) (use pos[THEN less_imp_le] mua' in auto)
      have "((\<lambda>t. (1 + \<xi> * (t - \<mu>) / \<sigma>) powr (- 1 / \<xi>)) \<longlongrightarrow> 0) (at_left a)"
        by (rule tendsto_zero_powrI[OF base0 tendsto_const ev_nonneg p_pos])
      hence "(F \<longlongrightarrow> - 0) (at_left a)"
        unfolding F_def by (rule tendsto_minus)
      thus ?thesis
        by (simp add: Fa0)
    qed
    have FTC1: "set_integrable lborel (einterval (ereal \<mu>) (ereal a)) g"
      by (rule interval_integral_FTC_nonneg[where F=F and A="- 1" and B="F a"])
         (use mua' deriv isCont_g g_nonneg A B in
          \<open>auto simp: ereal_tendsto_simps\<close>)
    have FTC2: "interval_lebesgue_integral lborel (ereal \<mu>) (ereal a) g = F a - (- 1)"
      by (rule interval_integral_FTC_nonneg[where F=F])
         (use mua' deriv isCont_g g_nonneg A B in
          \<open>auto simp: ereal_tendsto_simps\<close>)
    have intg_oo: "set_integrable lborel {\<mu><..<a} g"
      using FTC1 by simp
    have int_oo: "(\<integral>x\<in>{\<mu><..<a}. g x \<partial>lborel) = 1 - (1 + \<xi> * y) powr (- 1 / \<xi>)"
      using FTC2 mua' by (simp add: interval_lebesgue_integral_def Fa)
    have dens_eq: "GPD_density \<xi> \<mu> \<sigma> t = g t" if t: "\<mu> < t" "t < a" for t
    proof(cases "0 < \<xi>")
      case True
      thus ?thesis
        using t by (simp add: GPD_density_xi_pos g_def)
    next
      case False
      with xi have xi_neg: "\<xi> < 0"
        by simp
      have "- \<sigma> \<le> \<xi> * (a - \<mu>)"
        using xiy sigma unfolding y_def by (simp add: pos_le_divide_eq)
      moreover have "\<xi> * (a - \<mu>) \<le> \<xi> * (t - \<mu>)"
        using t xi_neg by (intro mult_left_mono_neg) auto
      ultimately have "- \<sigma> \<le> \<xi> * (t - \<mu>)"
        by linarith
      from divide_right_mono_neg[OF this, of \<xi>] xi_neg xi
      have "t - \<mu> \<le> - \<sigma> / \<xi>"
        by simp
      thus ?thesis
        using t xi_neg by (simp add: GPD_density_xi_neg g_def)
    qed
    have ae_eq: "AE x in lborel. indicat_real {..a} x *\<^sub>R GPD_density \<xi> \<mu> \<sigma> x
                                 = indicat_real {\<mu><..<a} x *\<^sub>R g x"
      using AE_lborel_singleton[of \<mu>] AE_lborel_singleton[of a]
    proof eventually_elim
      case (elim x)
      consider "x < \<mu>" | "\<mu> < x" "x < a" | "a < x"
        using elim mua' by argo
      thus ?case
        by cases (simp_all add: indicator_def GPD_density_eq_0 mua' less_le_not_le dens_eq)
    qed
    have intg: "set_integrable lborel {..a} (GPD_density \<xi> \<mu> \<sigma>)"
    proof -
      have "integrable lborel (\<lambda>x. indicat_real {..a} x *\<^sub>R GPD_density \<xi> \<mu> \<sigma> x)
             \<longleftrightarrow> integrable lborel (\<lambda>x. indicat_real {\<mu><..<a} x *\<^sub>R g x)"
        using ae_eq by (intro integrable_cong_AE) auto
      thus ?thesis
        using intg_oo by (simp add: set_integrable_def)
    qed
    have integral_eq: "(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1 - (1 + \<xi> * y) powr (- 1 / \<xi>)"
    proof -
      have "(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
             = (\<integral>x. indicat_real {\<mu><..<a} x *\<^sub>R g x \<partial>lborel)"
        unfolding set_lebesgue_integral_def
        using ae_eq by (intro integral_cong_AE) auto
      also have "... = 1 - (1 + \<xi> * y) powr (- 1 / \<xi>)"
        using int_oo by (simp add: set_lebesgue_integral_def)
      finally show ?thesis .
    qed
    have nn_eq: "(\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
                  = ennreal (1 - (1 + \<xi> * y) powr (- 1 / \<xi>))"
    proof -
      have "(\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
             = (\<integral>\<^sup>+x. ennreal (indicat_real {\<mu><..<a} x *\<^sub>R g x) \<partial>lborel)"
        using ae_eq by (intro nn_integral_cong_AE)
                       (auto elim!: eventually_mono simp: indicator_def)
      also have "... = ennreal (\<integral>x. indicat_real {\<mu><..<a} x *\<^sub>R g x \<partial>lborel)"
        by (intro nn_integral_eq_integral)
           (use intg_oo g_nonneg in \<open>auto simp: set_integrable_def indicator_def\<close>)
      also have "... = ennreal (1 - (1 + \<xi> * y) powr (- 1 / \<xi>))"
        using int_oo by (simp add: set_lebesgue_integral_def)
      finally show ?thesis .
    qed
    show ?thesis
      using intg integral_eq nn_eq by blast
  qed
  from main show "set_integrable lborel {..a} (GPD_density \<xi> \<mu> \<sigma>)"
    and "(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1 - (1 + \<xi> * y) powr (- 1 / \<xi>)"
    and "(\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
          = ennreal (1 - (1 + \<xi> * y) powr (- 1 / \<xi>))"
    by blast+
qed

lemma
  fixes a \<mu> \<sigma> :: real
  defines "y \<equiv> (a - \<mu>) / \<sigma>"
  assumes sigma[arith]:"0 < \<sigma>"
    and xi:"\<xi> < 0"
    and xiy:"\<xi> * y \<le> - 1"
  shows GPD_density_set_integrable3:"set_integrable lborel {..a} (GPD_density \<xi> \<mu> \<sigma>)"
    and GPD_density_set_integral3:"(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    and GPD_density_set_nn_integral3:"(\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
proof -
  define b where "b \<equiv> \<mu> - \<sigma> / \<xi>"
  have ba: "b \<le> a"
    using xiy xi sigma unfolding b_def y_def by (simp add: field_simps)
  have yb1: "(b - \<mu>) / \<sigma> = - 1 / \<xi>"
    using xi sigma by (simp add: b_def field_simps)
  have mub:"\<mu> \<le> b"
    using xi by(simp add: b_def divide_nonneg_neg)
  have yb3: "- 1 \<le> \<xi> * ((b - \<mu>) / \<sigma>)"
    using xi by (simp add: yb1)
  have base0: "1 + \<xi> * (b - \<mu>) / \<sigma> = 0"
    using xi sigma by (simp add: b_def field_simps)
  have dens_b: "GPD_density \<xi> \<mu> \<sigma> x = 0" if "b \<le> x" for x
  proof(cases "x = b")
    case True
    have "b \<le> \<mu> - \<sigma> / \<xi>"
      by (simp add: b_def)
    hence "GPD_density \<xi> \<mu> \<sigma> b = (1 + \<xi> * (b - \<mu>) / \<sigma>) powr (- 1 - 1 / \<xi>) / \<sigma>"
      by (intro GPD_density_xi_neg[OF xi mub])
    thus ?thesis
      by (simp add: True base0)
  next
    case False
    with that
    have "b < x"
      by simp
    hence "\<mu> - \<sigma> / \<xi> < x"
      unfolding b_def by argo
    thus ?thesis
      by (intro GPD_density_xi_neg_eq_0[OF xi])
  qed
  have h1[simp]: "set_integrable lborel {..b} (GPD_density \<xi> \<mu> \<sigma>)"
    and h2: "(\<integral>x\<in>{..b}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    and h3: "(\<integral>\<^sup>+x\<in>{..b}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    using GPD_density_set_integrable1[OF sigma less_imp_neq[OF xi] mub yb3]
      GPD_density_set_integral1[OF sigma less_imp_neq[OF xi] mub yb3]
      GPD_density_set_nn_integral1[OF sigma less_imp_neq[OF xi] mub yb3] xi
    by (simp_all add: yb1)
  have i2[simp]: "set_integrable lborel {b<..a} (GPD_density \<xi> \<mu> \<sigma>)"
    by(subst set_integrable_cong[where f'="\<lambda>x. 0", OF refl refl]) (simp_all add: dens_b)
  have eq0: "(\<integral>x\<in>{b<..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    by(subst set_integral_cong[where g="\<lambda>x. 0"]) (auto simp: dens_b)
  have eq0': "(\<integral>\<^sup>+x\<in>{b<..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    by(subst set_nn_integral_cong[where g="\<lambda>x. 0", OF refl refl]) (auto simp: dens_b)
  show "set_integrable lborel {..a} (GPD_density \<xi> \<mu> \<sigma>)"
    using ba
    by(subst set_integrable_cong[where A'="{..b} \<union> {b<..a}"])
      (auto intro!: set_integrable_Un)
  have "(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) =
       (\<integral>x\<in>{..b}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) + (\<integral>x\<in>{b<..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel)"
    using ba
    by(subst set_integral_Un[symmetric])
      (auto intro!: arg_cong[where f="\<lambda>B. set_lebesgue_integral lborel B _"])
  also have "... = 1"
    by (auto simp: h2 eq0)
  finally show "(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1" .
  have "(\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) =
        (\<integral>\<^sup>+x. ennreal (GPD_density \<xi> \<mu> \<sigma> x) * indicator {..b} x
         + ennreal (GPD_density \<xi> \<mu> \<sigma> x) * indicator {b<..a} x \<partial>lborel)"
    using ba by(auto intro!: nn_integral_cong simp: indicator_def)
  also have "... = (\<integral>\<^sup>+x\<in>{..b}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel)"
    using ba by(auto intro!: nn_integral_cong simp: indicator_def dens_b)
  finally show "(\<integral>\<^sup>+x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    by(simp add: h3)
qed

lemma GPD_density_set_integrable:
  assumes sigma[arith]:"0 < \<sigma>"
  shows "set_integrable lborel {..a} (GPD_density \<xi> \<mu> \<sigma>)"
proof -
  consider "\<xi> = 0"
    | "\<not> \<xi> = 0" "a \<le> \<mu>"
    |  "\<not> \<xi> = 0" "\<mu> \<le> a" "- 1 \<le> \<xi> * ((a - \<mu>) / \<sigma>)"
    |  "\<not> \<xi> = 0" "\<mu> \<le> a" "\<xi> * ((a - \<mu>) / \<sigma>) < - 1"
    by argo
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      using GPD_density_set_integrable0
      by simp
  next
    case 2
    thus ?thesis
      by (intro GPD_density_set_integrable2[OF sigma])
    thm GPD_density_set_integrable2[OF sigma]
  next
    case 3
    thus ?thesis
      by (intro GPD_density_set_integrable1[OF sigma])
  next
    case 4
    hence xi_neg: "\<xi> < 0"
      by (smt (verit, best) assms divide_nonneg_pos mult_nonneg_nonneg)
    show ?thesis
      by (intro GPD_density_set_integrable3[OF sigma xi_neg] less_imp_le 4)
  qed
qed

abbreviation GPD_cdf where "GPD_cdf \<equiv> \<lambda>\<xi> \<mu> \<sigma> x. cdf (density lborel (GPD_density \<xi> \<mu> \<sigma>)) x"

lemma GPD_cdf_set_integral:
  assumes sigma[arith]:"0 < \<sigma>"
  shows "GPD_cdf \<xi> \<mu> \<sigma> x = (\<integral>t\<in>{..x}. GPD_density \<xi> \<mu> \<sigma> t \<partial>lborel)"
  unfolding cdf_def
  by (intro measure_density_on GPD_density_set_integrable[OF sigma])
     (auto simp: less_imp_le)

corollary GPD_cdf_def:
  assumes sigma[arith]:"0 < \<sigma>"
  shows "GPD_cdf \<xi> \<mu> \<sigma> x =
                    (let y = (x - \<mu>) / \<sigma> in
                     if \<xi> = 0 then
                        if x < \<mu> then 0 else 1 - exp (- y)
                     else
                     if x < \<mu> then 0
                     else if - 1 \<le> \<xi> * y then 1 - (1 + \<xi> * y) powr (- 1 / \<xi>)
                     else 1)"
proof -
  consider "\<xi> = 0"
    | "\<xi> \<noteq> 0" "x < \<mu>"
    | "\<xi> \<noteq> 0" "\<mu> \<le> x" "- 1 \<le> \<xi> * ((x - \<mu>) / \<sigma>)"
    | "\<xi> \<noteq> 0" "\<mu> \<le> x" "\<xi> * ((x - \<mu>) / \<sigma>) < - 1"
    by argo
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      unfolding GPD_cdf_set_integral[OF sigma]
      by(simp add: GPD_density_set_integral0 del: minus_diff_eq)
  next
    case 2
    thus ?thesis
      using GPD_density_set_integral2[OF sigma less_imp_le]
      by (auto simp add: GPD_cdf_set_integral Let_def)
  next
    case 3
    thus ?thesis
      using GPD_density_set_integral1[OF sigma]
      by (simp add: GPD_cdf_set_integral Let_def)
  next
    case 4
    hence xi_neg: "\<xi> < 0"
      by (smt (verit, best) assms mult_nonneg_nonneg zero_le_divide_iff)
    show ?thesis
      using GPD_density_set_integral3[OF sigma xi_neg less_imp_le] 4
      by (simp add: GPD_cdf_set_integral Let_def)
  qed
qed

lemma GPD_cdf_location_scale:
  assumes sigma: "0 < \<sigma>"
  shows "GPD_cdf \<gamma> 0 \<sigma> x = GPD_cdf \<gamma> 0 1 (x / \<sigma>)"
  using sigma
  by (simp add: GPD_cdf_def[OF sigma] GPD_cdf_def[OF zero_less_one] Let_def divide_less_0_iff)

lemma EVD_tail_eq_GPD_cdf:
  assumes supp: "1 + \<gamma> * x > 0" and x: "0 \<le> x"
  shows "- ln (EVD_cdf \<gamma> 0 1 x) = 1 - GPD_cdf \<gamma> 0 1 x"
  using x supp
  by (simp add: EVD_cdf_def[of 1] GPD_cdf_def[OF zero_less_one] Let_def)

lemma GPD_cdf_eq0:
  assumes "x \<le> \<mu>"
  shows "GPD_cdf \<xi> \<mu> \<sigma> x = 0"
proof -
  have "GPD_cdf \<xi> \<mu> \<sigma> x = enn2real (set_nn_integral lborel {..x} (GPD_density \<xi> \<mu> \<sigma>))"
    by(simp add: emeasure_density cdf_def measure_def)
  also have "... = enn2real (set_nn_integral lborel {..x} (\<lambda>y. 0))"
    using assms
    by(intro arg_cong[where f=enn2real] nn_integral_cong_AE AE_I'[where N="{x}"])
      (auto simp: GPD_density_def indicator_def)
  finally show ?thesis
    by simp
qed

lemma GPD_cdf_at_bot_0: "(GPD_cdf \<xi> \<mu> \<sigma> \<longlongrightarrow> 0) at_bot"
proof -
  have "\<forall>\<^sub>F x in at_bot. GPD_cdf \<xi> \<mu> \<sigma> x = 0"
    using eventually_le_at_bot[of \<mu>]
    by eventually_elim (intro GPD_cdf_eq0)
  thus ?thesis
    by (rule tendsto_eventually)
qed

lemma GPD_cdf_at_top_1:
  assumes sigma:"0 < \<sigma>"
  shows "(GPD_cdf \<xi> \<mu> \<sigma> \<longlongrightarrow> 1) at_top"
proof (cases "\<xi> = 0")
  case True
  have ev: "\<forall>\<^sub>F x in at_top. 1 - exp (- (x - \<mu>) / \<sigma>) = GPD_cdf \<xi> \<mu> \<sigma> x"
    using eventually_ge_at_top[of \<mu>]
    by eventually_elim
      (use True in "simp add: GPD_cdf_def[OF sigma] Let_def field_simps minus_divide_left")
  have lim: "((\<lambda>x. 1 - exp (- (x - \<mu>) / \<sigma>)) \<longlongrightarrow> 1) at_top"
  proof -
    have "((\<lambda>x. exp (- (x - \<mu>) / \<sigma>)) \<longlongrightarrow> 0) at_top"
      using sigma by real_asymp
    from tendsto_diff[OF tendsto_const this]
    show ?thesis
      by simp
  qed
  show ?thesis
    by (rule Lim_transform_eventually[OF lim ev])
next
  case False
  show ?thesis
  proof(cases "0 < \<xi>")
    case True
    have ev: "\<forall>\<^sub>F x in at_top. 1 - (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)
                                   = GPD_cdf \<xi> \<mu> \<sigma> x"
      using eventually_ge_at_top[of \<mu>]
    proof eventually_elim
      case (elim x)
      hence y0: "0 \<le> (x - \<mu>) / \<sigma>"
        using sigma by (intro divide_nonneg_pos) auto
      have "- 1 \<le> \<xi> * ((x - \<mu>) / \<sigma>)"
        using mult_nonneg_nonneg[OF less_imp_le[OF True] y0] by linarith
      thus ?case
        using True elim by (simp add: GPD_cdf_def[OF sigma] Let_def)
    qed
    have lim: "((\<lambda>x. 1 - (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)) \<longlongrightarrow> 1) at_top"
    proof -
      have 1: "LIM x at_top. 1 + \<xi> * ((x - \<mu>) / \<sigma>) :> at_top"
      proof -
        have "LIM x at_top. (x - \<mu>) / \<sigma> :> at_top"
          using sigma by real_asymp
        hence "LIM x at_top. \<xi> * ((x - \<mu>) / \<sigma>) :> at_top"
          by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const True])
        thus ?thesis
          by (intro filterlim_tendsto_add_at_top[OF tendsto_const])
      qed
      have "((\<lambda>x. (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)) \<longlongrightarrow> 0) at_top"
        by (intro tendsto_neg_powr[OF _ 1]) (use True in \<open>auto simp: divide_neg_pos\<close>)
      from tendsto_diff[OF tendsto_const this]
      show ?thesis
        by simp
    qed
    show ?thesis
      by (rule Lim_transform_eventually[OF lim ev])
next
  case False
  with \<open>\<xi> \<noteq> 0\<close> have xi_neg: "\<xi> < 0"
    by simp
  have ev: "\<forall>\<^sub>F x in at_top. GPD_cdf \<xi> \<mu> \<sigma> x = 1"
    using eventually_ge_at_top[of "\<mu> - \<sigma> / \<xi>"]
  proof eventually_elim
    case (elim x)
    note neg = divide_pos_neg[OF sigma xi_neg]
    hence mux:"\<mu> \<le> x"
      using elim neg by linarith
    have eq: "(- \<sigma> / \<xi>) / \<sigma> = - 1 / \<xi>"
      using xi_neg sigma by (simp add: field_simps)
    have "(- \<sigma> / \<xi>) / \<sigma> \<le> (x - \<mu>) / \<sigma>"
      using elim sigma by (intro divide_right_mono) auto
    hence zb: "- 1 / \<xi> \<le> (x - \<mu>) / \<sigma>"
      using sigma by (simp add: eq)
    have "\<xi> * ((x - \<mu>) / \<sigma>) \<le> \<xi> * (- 1 / \<xi>)"
      by (rule mult_left_mono_neg[OF zb less_imp_le[OF xi_neg]])
    hence xiy_le: "\<xi> * ((x - \<mu>) / \<sigma>) \<le> - 1"
      using xi_neg by simp
    consider "\<xi> * ((x - \<mu>) / \<sigma>) = - 1" | "\<xi> * ((x - \<mu>) / \<sigma>) < - 1"
      using xiy_le by argo
    thus ?case
    proof cases
      case 1
      thus ?thesis
        using mux xi_neg by (simp add: GPD_cdf_def[OF sigma] Let_def)
    next
      case 2
      thus ?thesis
        using mux xi_neg by (auto simp: GPD_cdf_def[OF sigma] Let_def)
    qed
  qed
  thus ?thesis
    by (rule tendsto_eventually)
  qed
qed

lemma
  assumes sigma[arith]:"0 < \<sigma>"
  shows GPD_density_integrable:"integrable lborel (GPD_density \<xi> \<mu> \<sigma>)"
    and GPD_density_integral:"(\<integral>x. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    and GPD_density_nn_integral:"(\<integral>\<^sup>+x. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
proof -
  have lim: "((\<lambda>a. (\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel)) \<longlongrightarrow> 1) at_top"
  proof -
    have *: "(\<integral>x\<in>{..a}. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = GPD_cdf \<xi> \<mu> \<sigma> a" for a
      unfolding cdf_def
      by(subst measure_density_on)
        (auto simp: GPD_density_set_integrable[OF sigma])
    show ?thesis
      unfolding * by(rule GPD_cdf_at_top_1[OF sigma])
  qed
  show integ: "integrable lborel (GPD_density \<xi> \<mu> \<sigma>)"
    and eq2: "(\<integral>x. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    using lim GPD_density_set_integrable[OF sigma]
      integrable_monotone_convergence_at_top[where f="GPD_density \<xi> \<mu> \<sigma>" and x=1,
        OF _ AE_I2[OF GPD_density_nonneg[OF less_imp_le[OF sigma]]]]
      integral_monotone_convergence_at_top[where f="GPD_density \<xi> \<mu> \<sigma>" and x=1,
        OF _ AE_I2[OF GPD_density_nonneg[OF less_imp_le[OF sigma]]]]
    by(auto simp: set_integrable_def set_lebesgue_integral_def mult.commute)
  thus "(\<integral>\<^sup>+x. GPD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    by(subst nn_integral_eq_integral) auto
qed

lemma prob_space_GPD:
  assumes sigma[arith]:"0 < \<sigma>"
  shows "prob_space (density lborel (GPD_density \<xi> \<mu> \<sigma>))"
  by(auto intro!: prob_spaceI simp: emeasure_density GPD_density_nn_integral[OF sigma])

corollary real_distribution_GPD:
  "0 < \<sigma> \<Longrightarrow> real_distribution (density lborel (GPD_density \<xi> \<mu> \<sigma>))"
  by(simp add: real_distribution_def real_distribution_axioms_def prob_space_GPD)

lemma isCont_GPD_cdf:
  assumes sigma[arith]: "0 < \<sigma>"
  shows "isCont (GPD_cdf \<xi> \<mu> \<sigma>) x"
  using continuous_on_LBINT_com[OF GPD_density_integrable[OF sigma]]
    GPD_cdf_set_integral[OF sigma]
  by simp

lemma right_continuous_mono_GPD_cdf:
  assumes sigma[arith]: "0 < \<sigma>"
  shows "right_continuous_mono (GPD_cdf \<xi> \<mu> \<sigma>) 0 1"
  by(auto intro!: right_continuous_mono_cdf real_distribution_GPD)

corollary GPD_cdf_nonneg:"0 < \<sigma> \<Longrightarrow> 0 \<le> GPD_cdf \<xi> \<mu> \<sigma> x"
  and GPD_cdf_le_1:"0 < \<sigma> \<Longrightarrow> GPD_cdf \<xi> \<mu> \<sigma> x \<le> 1"
  using right_continuous_mono_GPD_cdf right_continuous_mono.a_le_f[of _ 0 1]
    right_continuous_mono.f_le_b[of _ 0 1]
  by fastforce+

lemma GPD_normalization:
  fixes \<gamma> \<mu> \<sigma> x :: real
  assumes sigma[arith]: "0 < \<sigma>"
  defines "a \<equiv> (\<lambda>n. \<sigma> * (if \<gamma> = 0 then 1 else real n powr \<gamma>))"
  defines "b \<equiv> (\<lambda>n. \<mu> + \<sigma> * (if \<gamma> = 0 then ln (real n) else (real n powr \<gamma> - 1) / \<gamma>))"
  shows "(\<lambda>n. GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n) ^ n)  \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 x"
proof(cases "\<gamma> = 0")
  assume 0:"\<gamma> = 0"
  have "\<forall>\<^sub>F n in sequentially. \<bar>x\<bar> < ln (real n)"
    using filterlim_compose[OF ln_at_top filterlim_real_sequentially]
    by(auto simp: filterlim_at_top_dense)
  hence pos: "\<forall>\<^sub>F n in sequentially. \<sigma> * x + \<sigma> * ln (real n) > 0"
    by eventually_elim (smt (verit, ccfv_SIG) sigma distrib_left mult_pos_pos)
  moreover have "\<forall>\<^sub>F n in sequentially. \<mu> \<le> a n * x + b n"
    using pos by eventually_elim (simp add: 0 a_def b_def)
  moreover have "\<forall>\<^sub>F n in sequentially. 0 < real n"
    by simp
  ultimately have "\<forall>\<^sub>F n in sequentially. (GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n))^n
                                         = (1 - exp (- x) / real n)^n"
    unfolding GPD_cdf_def[OF sigma]
    by eventually_elim (auto simp: 0 b_def a_def add_divide_distrib exp_diff)
  moreover have "(\<lambda>n. (1 - exp (- x) / real n)^n) \<longlonglongrightarrow> exp (- exp (- x))"
    using tendsto_exp_limit_sequentially[of "- exp (- x)"]
    by simp
  ultimately show ?thesis
    using tendsto_cong by(fastforce simp: EVD_cdf_def 0)
next
  assume 0:"\<gamma> \<noteq> 0"
  define y where "y \<equiv> (\<lambda>n::nat. (real n powr \<gamma> * (1 + \<gamma> * x) - 1) / \<gamma>)"
  have arg: "a n * x + b n = \<mu> + \<sigma> * y n" for n
    using 0 by(simp add: a_def b_def y_def field_simps)
  have gy: "\<gamma> * y n = real n powr \<gamma> * (1 + \<gamma> * x) - 1" for n
    using 0 by(simp add: y_def)
  have cdf_eq: "GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n)
                  = (if y n < 0 then 0
                     else if - 1 \<le> \<gamma> * y n then 1 - (1 + \<gamma> * y n) powr (- 1 / \<gamma>) else 1)" for n
    unfolding arg using 0 by(simp add: GPD_cdf_def[OF sigma] Let_def mult_less_0_iff)
  show ?thesis
  proof(cases "0 < 1 + \<gamma> * x")
    case c_pos: True
    have ge: "- 1 \<le> \<gamma> * y n" for n
      using c_pos by(simp add: gy)
    have ev0: "\<forall>\<^sub>F n in sequentially. 0 \<le> y n"
    proof(cases "0 < \<gamma>")
      case True
      have "filterlim (\<lambda>n. real n powr \<gamma>) at_top sequentially"
        by(rule filterlim_compose[OF real_powr_at_top[OF True] filterlim_real_sequentially])
      hence "\<forall>\<^sub>F n in sequentially. 1 / (1 + \<gamma> * x) \<le> real n powr \<gamma>"
        by(simp add: filterlim_at_top)
      thus ?thesis
      proof eventually_elim
        case (elim n)
        hence "1 \<le> real n powr \<gamma> * (1 + \<gamma> * x)"
          using c_pos by(simp add: pos_divide_le_eq)
        thus "0 \<le> y n"
          unfolding y_def using True by(intro divide_nonneg_pos) auto
      qed
    next
      case False
      with 0 have neg: "\<gamma> < 0"
        by simp
      have "(\<lambda>n. real n powr \<gamma>) \<longlonglongrightarrow> 0"
        by(rule tendsto_neg_powr[OF neg filterlim_real_sequentially])
      hence "\<forall>\<^sub>F n in sequentially. real n powr \<gamma> < 1 / (1 + \<gamma> * x)"
        using c_pos by(intro order_tendstoD) auto
      thus ?thesis
      proof eventually_elim
        case (elim n)
        hence "real n powr \<gamma> * (1 + \<gamma> * x) \<le> 1"
          using c_pos by(simp add: pos_less_divide_eq)
        thus "0 \<le> y n"
          unfolding y_def using neg by(intro divide_nonpos_neg) auto
      qed
    qed
    have ev: "\<forall>\<^sub>F n in sequentially.
                GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n) = 1 - (1 + \<gamma> * x) powr (- 1 / \<gamma>) / real n"
    proof(safe intro!: eventually_mp[OF eventually_sequentiallyI[of 1] ev0])
      fix n :: nat
      assume n: "1 \<le> n" and yn: "0 \<le> y n"
      have n0: "0 < real n"
        using n by simp
      have "(1 + \<gamma> * y n) powr (- 1 / \<gamma>) = (real n powr \<gamma> * (1 + \<gamma> * x)) powr (- 1 / \<gamma>)"
        by(simp add: gy)
      also have "... = (real n powr \<gamma>) powr (- 1 / \<gamma>) * (1 + \<gamma> * x) powr (- 1 / \<gamma>)"
        using c_pos by(simp add: powr_mult)
      also have "... = (1 + \<gamma> * x) powr (- 1 / \<gamma>) / real n"
        using 0 n0 by(simp add: powr_powr powr_minus_divide)
      finally show "GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n)
                      = 1 - (1 + \<gamma> * x) powr (- 1 / \<gamma>) / real n"
        using yn ge by(simp add: cdf_eq)
    qed
    have ev2: "\<forall>\<^sub>F n in sequentially. GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n) ^ n
                    = (1 - (1 + \<gamma> * x) powr (- 1 / \<gamma>) / real n) ^ n"
      using ev by eventually_elim simp
    have lim: "(\<lambda>n. (1 - (1 + \<gamma> * x) powr (- 1 / \<gamma>) / real n) ^ n)
                 \<longlonglongrightarrow> exp (- ((1 + \<gamma> * x) powr (- 1 / \<gamma>)))"
      using tendsto_exp_limit_sequentially[of "- ((1 + \<gamma> * x) powr (- 1 / \<gamma>))"]
      by simp
    have EVD: "EVD_cdf \<gamma> 0 1 x = exp (- ((1 + \<gamma> * x) powr (- 1 / \<gamma>)))"
      using c_pos 0 by(simp add: EVD_cdf_def)
    show ?thesis
      unfolding EVD by(subst tendsto_cong[OF ev2]) (rule lim)
  next
    case c_nonpos: False
    have ev: "\<forall>\<^sub>F n in sequentially.
                GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n) ^ n = EVD_cdf \<gamma> 0 1 x"
    proof(intro eventually_sequentiallyI[of 1])
      fix n :: nat
      assume n: "1 \<le> n"
      hence "0 < real n powr \<gamma>"
        by simp
      hence le: "\<gamma> * y n \<le> - 1"
        using c_nonpos by(simp add: gy mult_nonneg_nonpos)
      show "GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n) ^ n = EVD_cdf \<gamma> 0 1 x"
      proof(cases "0 < \<gamma>")
        case True
        hence "y n < 0"
          using le by (smt (verit, best) mult_nonneg_nonneg)
        hence "GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n) = 0"
          by(simp add: cdf_eq)
        thus ?thesis
          using n True c_nonpos by(simp add: EVD_cdf_def)
      next
        case False
        with 0 have neg: "\<gamma> < 0"
          by simp
        hence yn: "\<not> y n < 0"
          using le by (smt (verit, best) mult_less_0_iff)
        have "GPD_cdf \<gamma> \<mu> \<sigma> (a n * x + b n) = 1"
        proof(cases "\<gamma> * y n = - 1")
          case True
          thus ?thesis
            using yn 0 neg by(simp add: cdf_eq)
        next
          case False
          with le have "\<gamma> * y n < - 1"
            by simp
          thus ?thesis
            using yn by(simp add: cdf_eq)
        qed
        thus ?thesis
          using neg c_nonpos by(simp add: EVD_cdf_def)
      qed
    qed
    show ?thesis
      using ev by(simp add: tendsto_eventually)
  qed
qed

end