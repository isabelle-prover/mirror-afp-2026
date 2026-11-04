(*  Title:   Extreme_Value_Distribution.thy
    Author:  Michikazu Hirata
*)

section \<open>Distributions\<close>
subsection \<open>Generalized Extreme Value Distribution\<close>
theory Extreme_Value_Distribution
imports
   Lemmas_EVT
begin

text \<open>We define the generalized extreme value (GEV) density and cdf.
      Our definition includes a location parameter $\mu$ and
      a scale parameter $\sigma$.\<close>
definition EVD_density :: "[real, real, real, real] \<Rightarrow> real" where
"EVD_density \<xi> \<mu> \<sigma> x \<equiv> let y = (x - \<mu>) / \<sigma> in
                       if \<xi> = 0 then
                          exp (- y) * exp (- exp (- y)) / \<sigma>
                       else
                          if \<xi> * y > - 1 then
                          (1 + \<xi> * y) powr (- 1 / \<xi> - 1)
                           * exp (- ((1 + \<xi> * y) powr (- 1 / \<xi>))) / \<sigma>
                          else 0"

lemma EVD_density_nonneg[simp]:
 "0 \<le> \<sigma> \<Longrightarrow> 0 \<le> EVD_density \<xi> \<mu> \<sigma> x"
  by(simp add: EVD_density_def Let_def)

lemma EVD_density_xi_0:
 "EVD_density 0 \<mu> \<sigma> x = exp (- ((x - \<mu>) / \<sigma>)) * exp (- exp (- ((x - \<mu>) / \<sigma>))) / \<sigma>"
  by(simp add: EVD_density_def Let_def)

lemma
  assumes "\<xi> \<noteq> 0"
  shows EVD_density_xi_non0_1:
   "\<xi> * (x - \<mu>) / \<sigma> \<ge> - 1
     \<Longrightarrow> EVD_density \<xi> \<mu> \<sigma> x = (1 + \<xi> * (x - \<mu>) / \<sigma>) powr (- 1 / \<xi> - 1)
                                  * exp (- ((1 + \<xi> * (x - \<mu>) / \<sigma>) powr (- 1 / \<xi>))) / \<sigma>"
   and EVD_density_xi_non0_2:
   "\<xi> * (x - \<mu>) / \<sigma> \<le> - 1 \<Longrightarrow> EVD_density \<xi> \<mu> \<sigma> x = 0"
  using assms by(auto simp: EVD_density_def order.order_iff_strict)

lemma EVD_density_measurable[measurable]:
  "EVD_density \<xi> \<mu> \<sigma> \<in> borel_measurable borel"
  unfolding EVD_density_def Let_def by simp

lemma
  assumes sigma[arith]:"0 < \<sigma>"
  shows EVD_density_set_integrable0:"set_integrable lborel {..a} (EVD_density 0 \<mu> \<sigma>)"
    and EVD_density_set_integral0:
    "(\<integral>x\<in>{..a}. EVD_density 0 \<mu> \<sigma> x \<partial>lborel) = exp (- exp (- (a - \<mu>) / \<sigma>))"
    and EVD_density_set_nn_integral0:
    "(\<integral>\<^sup>+x\<in>{..a}. EVD_density 0 \<mu> \<sigma> x \<partial>lborel) = ennreal (exp (- exp (- (a - \<mu>) / \<sigma>)))"
proof -
  define G where "G = (\<lambda>x::real. exp (- exp (- (x - \<mu>) / \<sigma>)))"
  have deriv: "(G has_real_derivative EVD_density 0 \<mu> \<sigma> x) (at x)" for x
    unfolding G_def EVD_density_def Let_def
    using sigma by (auto intro!: derivative_eq_intros
                           simp: field_simps simp del: minus_diff_eq)
  have tendsto_bot: "(G \<longlongrightarrow> 0) at_bot"
    unfolding G_def using sigma
    by(intro filterlim_compose[OF exp_at_bot filterlim_compose
          [OF filterlim_uminus_at_bot_at_top]]
                filterlim_compose[OF exp_at_top])
      real_asymp
  have cont: "continuous (at_left a) G"
    using continuous_at_imp_continuous_at_within[OF DERIV_isCont[OF deriv]] by simp
  show "set_integrable lborel {..a} (EVD_density 0 \<mu> \<sigma>)"
    and "(\<integral>x\<in>{..a}. EVD_density 0 \<mu> \<sigma> x \<partial>lborel) = exp (- exp (- (a - \<mu>) / \<sigma>))"
    and "(\<integral>\<^sup>+x\<in>{..a}. EVD_density 0 \<mu> \<sigma> x \<partial>lborel) = ennreal (exp (- exp (- (a - \<mu>) / \<sigma>)))"
    using set_integrable_FTC_atMost[OF _ cont deriv _ tendsto_bot]
      set_integral_FTC_atMost[OF _ cont deriv _ tendsto_bot]
      nn_integral_FTC_lessThan[OF _ cont deriv _ tendsto_bot]
    by(simp_all add: G_def set_nn_integral_atMost_eq)
qed

lemma
  fixes a \<mu> \<sigma>
  defines "y \<equiv> (a - \<mu>) / \<sigma>"
  assumes sigma[arith]:"0 < \<sigma>"
    and xi:"\<xi> \<noteq> 0"
    and xiy:"\<xi> * y \<ge> - 1"
    and xiy_pos:"0 < \<xi> \<Longrightarrow> - 1 < \<xi> * y"
  shows EVD_density_set_integrable1:"set_integrable lborel {..a} (EVD_density \<xi> \<mu> \<sigma>)"
    and EVD_density_set_integral1:
    "(\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = exp (- ((1 + \<xi> * y) powr (- 1 / \<xi>)))"
    and EVD_density_set_nn_integral1:
    "(\<integral>\<^sup>+x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = ennreal (exp (- ((1 + \<xi> * y) powr (- 1 / \<xi>))))"
proof -
  have deriv_raw: "((\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) has_real_derivative
                     EVD_density \<xi> \<mu> \<sigma> x) (at x)"
    if pos: "0 < 1 + \<xi> * ((x - \<mu>) / \<sigma>)" for x
  proof -
    have cond: "- 1 < \<xi> * ((x - \<mu>) / \<sigma>)"
      using pos by linarith
    have dens: "EVD_density \<xi> \<mu> \<sigma> x
        = (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi> - 1)
            * exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>))) / \<sigma>"
      using cond xi by(simp add: EVD_density_def Let_def)
    show ?thesis
      unfolding dens
      using pos xi by(auto intro!: derivative_eq_intros simp: field_simps)
  qed
  show nn: "(\<integral>\<^sup>+x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
             = ennreal (exp (- ((1 + \<xi> * y) powr (- 1 / \<xi>))))"
  proof(cases "0 < \<xi>")
    case False
    with xi have xi_neg: "\<xi> < 0"
      by simp
    have p_pos: "0 < - 1 / \<xi>"
      using xi_neg by (simp add: divide_pos_neg)
    define F where "F \<equiv> \<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))"
    have pos: "0 < 1 + \<xi> * ((x - \<mu>) / \<sigma>)" if "x < a" for x
    proof -
      have "(x - \<mu>) / \<sigma> < (a - \<mu>) / \<sigma>"
        using that sigma by (intro divide_strict_right_mono) auto
      hence "\<xi> * ((a - \<mu>) / \<sigma>) < \<xi> * ((x - \<mu>) / \<sigma>)"
        by (rule mult_strict_left_mono_neg[OF _ xi_neg])
      with xiy show ?thesis
        unfolding y_def by linarith
    qed
    have deriv: "(F has_real_derivative EVD_density \<xi> \<mu> \<sigma> x) (at x)" if "x < a" for x
      unfolding F_def by (rule deriv_raw[OF pos[OF that]])
    have nonneg: "0 \<le> EVD_density \<xi> \<mu> \<sigma> x" for x
      by simp
    have cont: "continuous (at_left a) F"
    proof (cases "\<xi> * y = - 1")
      case False
      with xiy have pos_a: "0 < 1 + \<xi> * y"
        by linarith
      have "isCont F a"
        unfolding F_def using pos_a
        by (intro continuous_intros) (simp_all add: y_def)
      thus ?thesis
        using continuous_at_imp_continuous_at_within by blast
    next
      case True
      have Fa: "F a = 1"
        using True unfolding F_def y_def by simp
      have "((\<lambda>x. 1 + \<xi> * ((x - \<mu>) / \<sigma>)) \<longlongrightarrow> 1 + \<xi> * ((a - \<mu>) / \<sigma>)) (at_left a)"
        by (intro tendsto_intros) arith
      with True have base0: "((\<lambda>x. 1 + \<xi> * ((x - \<mu>) / \<sigma>)) \<longlongrightarrow> 0) (at_left a)"
        by (simp add: y_def)
      have ev_pos: "\<forall>\<^sub>F x in at_left a. 0 \<le> 1 + \<xi> * ((x - \<mu>) / \<sigma>)"
        by (intro eventually_at_leftI[of "a - 1"]) (use pos[THEN less_imp_le] in auto)
      have "((\<lambda>x. (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)) \<longlongrightarrow> 0) (at_left a)"
        by (rule tendsto_zero_powrI[OF base0 tendsto_const ev_pos p_pos])
      hence "(F \<longlongrightarrow> exp (- 0)) (at_left a)"
        unfolding F_def by (intro tendsto_intros)
      thus ?thesis
        by (simp add: continuous_within Fa)
    qed
    have lim: "(F \<longlongrightarrow> 0) at_bot"
      unfolding F_def
      using filterlim_compose[OF real_powr_at_top[OF p_pos]
              filterlim_shift_scale_at_bot[OF sigma xi_neg]]
      by (intro filterlim_compose[OF exp_at_bot
            filterlim_compose[OF filterlim_uminus_at_bot_at_top]])
    have "(\<integral>\<^sup>+x\<in>{..<a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
           = ennreal (exp (- ((1 + \<xi> * y) powr (- 1 / \<xi>))))"
      using nn_integral_FTC_lessThan[OF EVD_density_measurable cont deriv nonneg lim]
      by (simp add: F_def y_def)
    thus ?thesis
      by (simp add: set_nn_integral_atMost_eq[symmetric])
  next
    case True
    have p_neg: "- 1 / \<xi> < 0"
      using True by (simp add: divide_neg_pos)
    define c where "c \<equiv> \<mu> - \<sigma> / \<xi>"
    define F where "F \<equiv> \<lambda>x. if - 1 < \<xi> * ((x - \<mu>) / \<sigma>)
                            then exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>))) else 0"
    have cond_iff: "(- 1 < \<xi> * ((x - \<mu>) / \<sigma>)) \<longleftrightarrow> c < x" for x
      using True sigma unfolding c_def by (auto simp: field_simps)
    have ca: "c < a"
      using xiy_pos[OF True] cond_iff[of a] by (simp add: y_def)
    have dens0: "EVD_density \<xi> \<mu> \<sigma> x = 0" if "\<not> c < x" for x
      using cond_iff[of x] that xi by (auto simp: EVD_density_def Let_def)
    have pos: "0 < 1 + \<xi> * ((x - \<mu>) / \<sigma>)" if "c < x" for x
      using cond_iff[THEN iffD2, OF that] by linarith
    have F_eq: "F x = exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))" if "c < x" for x
      using cond_iff that by (simp add: F_def)
    have deriv: "(F has_real_derivative EVD_density \<xi> \<mu> \<sigma> x) (at x)" if "c < x" for x
    proof -
      have "((\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) has_real_derivative
              EVD_density \<xi> \<mu> \<sigma> x) (at x)"
        by (rule deriv_raw[OF pos[OF that]])
      thus ?thesis
        by (rule has_field_derivative_transform_within_open[where S="{c<..}"])
           (auto simp: F_eq that)
    qed
    have deriv': "(F has_real_derivative EVD_density \<xi> \<mu> \<sigma> x) (at x)" if "a < x" for x
      by (rule deriv[OF less_trans[OF ca that]])
    have nonneg: "0 \<le> EVD_density \<xi> \<mu> \<sigma> x" for x
      by simp
    have Fc: "F c = 0"
      using cond_iff[of c] by (simp add: F_def)
    have contc: "continuous (at_right c) F"
    proof -
      have "((\<lambda>x. 1 + \<xi> * ((x - \<mu>) / \<sigma>)) \<longlongrightarrow> 1 + \<xi> * ((c - \<mu>) / \<sigma>)) (at_right c)"
        by (intro tendsto_intros) arith
      moreover have "1 + \<xi> * ((c - \<mu>) / \<sigma>) = 0"
        using True sigma by (simp add: c_def)
      ultimately have base0: "((\<lambda>x. 1 + \<xi> * ((x - \<mu>) / \<sigma>)) \<longlongrightarrow> 0) (at_right c)"
        by simp
      have ev_pos: "\<forall>\<^sub>F x in at_right c. 0 < 1 + \<xi> * ((x - \<mu>) / \<sigma>)"
        by (intro eventually_at_rightI[of c "c + 1"]) (use pos in auto)
      have small: "((\<lambda>x. (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (1 / \<xi>)) \<longlongrightarrow> 0) (at_right c)"
        by (rule tendsto_zero_powrI[OF base0 tendsto_const])
           (use ev_pos True in \<open>auto elim: eventually_mono\<close>)
      have ev_pos': "\<forall>\<^sub>F x in at_right c. 0 < (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (1 / \<xi>)"
        using ev_pos by (auto elim!: eventually_mono)
      have top: "LIM x (at_right c). (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>) :> at_top"
        using filterlim_inverse_at_top[OF small ev_pos'] by (simp add: powr_minus)
      have *: "((\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) \<longlongrightarrow> 0) (at_right c)"
        by (rule filterlim_compose[OF exp_at_bot
              filterlim_compose[OF filterlim_uminus_at_bot_at_top top]])
      have "(F \<longlongrightarrow> 0) (at_right c)"
        by (rule Lim_transform_eventually[OF *])
           (auto intro!: eventually_at_rightI[of c "c + 1"] simp: F_eq)
      thus ?thesis
        by (simp add: continuous_within Fc)
    qed
    have conta: "continuous (at_right a) F"
    proof -
      have "isCont (\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) a"
        using pos[OF ca] by (intro continuous_intros) auto
      hence "continuous (at_right a) (\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>))))"
        by (rule continuous_at_imp_continuous_at_within)
      hence "((\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>))))
               \<longlongrightarrow> exp (- ((1 + \<xi> * ((a - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) (at_right a)"
        by (simp add: continuous_within)
      hence "(F \<longlongrightarrow> exp (- ((1 + \<xi> * ((a - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) (at_right a)"
        by (rule Lim_transform_eventually)
           (auto intro!: eventually_at_rightI[of a "a + 1"] simp: F_eq less_trans[OF ca])
      thus ?thesis
        by (simp add: continuous_within F_eq[OF ca])
    qed
    have limtop: "(F \<longlongrightarrow> 1) at_top"
    proof -
      have powr0: "((\<lambda>x. (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)) \<longlongrightarrow> 0) at_top"
        by (rule tendsto_neg_powr[OF p_neg filterlim_shift_scale_at_top[OF sigma True]])
      have "((\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) \<longlongrightarrow> exp (- 0)) at_top"
        by (intro tendsto_intros powr0)
      hence *: "((\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) \<longlongrightarrow> 1) at_top"
        by simp
      have ev: "\<forall>\<^sub>F x in at_top. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>))) = F x"
        using eventually_gt_at_top[of c] by eventually_elim (simp add: F_eq)
      show ?thesis
        by (rule Lim_transform_eventually[OF * ev])
    qed
    have Fa: "F a = exp (- ((1 + \<xi> * y) powr (- 1 / \<xi>)))"
      by (simp add: F_eq[OF ca] y_def)
    have Fa01: "0 \<le> F a" "F a \<le> 1"
      by (auto simp: Fa)
    have I1: "(\<integral>\<^sup>+x\<in>{c<..}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
      using nn_integral_FTC_greaterThan[OF EVD_density_measurable contc deriv nonneg limtop]
      by (simp add: Fc)
    have I2: "(\<integral>\<^sup>+x\<in>{a<..}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1 - ennreal (F a)"
      using nn_integral_FTC_greaterThan[OF EVD_density_measurable conta deriv' nonneg limtop]
      by (metis ennreal_1 ennreal_minus Fa01(1))
    have "(\<integral>\<^sup>+x\<in>{c<..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) + (\<integral>\<^sup>+x\<in>{a<..}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
          = (\<integral>\<^sup>+x. ennreal (EVD_density \<xi> \<mu> \<sigma> x) * indicator {c<..a} x
                 + ennreal (EVD_density \<xi> \<mu> \<sigma> x) * indicator {a<..} x \<partial>lborel)"
      by (rule nn_integral_add[symmetric]) auto
    also have "... = (\<integral>\<^sup>+x\<in>{c<..}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)"
      using ca by (auto intro!: nn_integral_cong simp: indicator_def)
    finally have split: "(\<integral>\<^sup>+x\<in>{c<..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) + (1 - ennreal (F a)) = 1"
      by (simp add: I1 I2)
    have X: "(\<integral>\<^sup>+x\<in>{c<..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = ennreal (F a)"
    proof -
      have le1: "ennreal (F a) \<le> 1"
        using Fa01 by (simp add: ennreal_leI)
      have c_ne: "1 - ennreal (F a) \<noteq> \<top>"
        by simp
      have "(\<integral>\<^sup>+x\<in>{c<..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
            = ((\<integral>\<^sup>+x\<in>{c<..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) + (1 - ennreal (F a)))
              - (1 - ennreal (F a))"
        by (simp add: c_ne)
      also have "... = 1 - (1 - ennreal (F a))"
        by (simp add: split)
      also have "... = ennreal (F a)"
        using le1 diff_diff_ennreal'' by auto
      finally show ?thesis .
    qed
    have "(\<integral>\<^sup>+x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = (\<integral>\<^sup>+x\<in>{c<..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)"
      by (auto intro!: nn_integral_cong simp: indicator_def dens0)
    thus ?thesis
      by (simp add: X Fa)
  qed
  have 1: "(\<integral>\<^sup>+x\<in>{..a}. ennreal (EVD_density \<xi> \<mu> \<sigma> x) \<partial>lborel)
           = (\<integral>\<^sup>+ x. ennreal \<bar>indicat_real {..a} x * EVD_density \<xi> \<mu> \<sigma> x\<bar> \<partial>lborel)"
    by(auto intro!: nn_integral_cong simp: indicator_def)
  show "set_integrable lborel {..a} (EVD_density \<xi> \<mu> \<sigma>)"
    using nn by(simp add: set_integrable_def integrable_iff_bounded 1)
  have "(\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)
          = enn2real (\<integral>\<^sup>+x\<in>{..a}. ennreal (EVD_density \<xi> \<mu> \<sigma> x) \<partial>lborel)"
    unfolding set_lebesgue_integral_def
    by(subst integral_eq_nn_integral)
      (auto simp: indicator_def intro!: arg_cong[where f=enn2real] nn_integral_cong)
  thus "(\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = exp (- ((1 + \<xi> * y) powr (- 1 / \<xi>)))"
    by(simp add: nn)
qed

lemma
  fixes a \<mu> \<sigma>
  defines "y \<equiv> (a - \<mu>) / \<sigma>"
  assumes sigma[arith]:"0 < \<sigma>"
    and xiy:"\<xi> * y \<le> - 1"
    and xi:"\<xi> > 0"
  shows EVD_density_set_integrable2: "set_integrable lborel {..a} (EVD_density \<xi> \<mu> \<sigma>)"
    and EVD_density_set_integral2:
    "(\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    and EVD_density_set_nn_integral2:
    "(\<integral>\<^sup>+x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
proof -
  have eq0[simp]:"\<And>x. x \<le> a \<Longrightarrow> EVD_density \<xi> \<mu> \<sigma> x = 0"
    by (smt (verit, ccfv_SIG) EVD_density_def y_def sigma
        xi xiy divide_right_mono mult_le_cancel_left_pos)
  show "set_integrable lborel {..a} (EVD_density \<xi> \<mu> \<sigma>)"
    by(subst set_integrable_cong[where f'="\<lambda>x. 0",OF refl refl]) simp_all
  show "(\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    by(subst set_integral_cong[where g="\<lambda>x. 0"]) simp_all
  show "(\<integral>\<^sup>+x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    by(subst set_nn_integral_cong[where g="\<lambda>x. 0"]) simp_all
qed

lemma
  fixes a \<mu> \<sigma>
  defines "y \<equiv> (a - \<mu>) / \<sigma>"
  assumes sigma[arith]:"0 < \<sigma>"
    and xiy:"\<xi> * y \<le> - 1"
    and xi:"\<xi> < 0"
  shows EVD_density_set_integrable3: "set_integrable lborel {..a} (EVD_density \<xi> \<mu> \<sigma>)"
    and EVD_density_set_integral3:
    "(\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    and EVD_density_set_nn_integral3:
    "(\<integral>\<^sup>+x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
proof -
  define b where "b \<equiv> \<mu> - \<sigma> / \<xi>"
  have ba:"b \<le> a"
    using xiy xi unfolding b_def y_def by (simp add: field_simps)
  have [simp]:"\<And>x. b \<le> x \<Longrightarrow> EVD_density \<xi> \<mu> \<sigma> x = 0"
    by (smt (verit, ccfv_SIG) EVD_density_def sigma xi b_def divide_le_eq
        le_divide_eq_1 minus_divide_left mult.commute
        times_divide_eq_right)
  have b:"\<xi> * ((b - \<mu>) / \<sigma>) \<ge> - 1"
    using xi by(simp add: b_def)
  have b':"0 < \<xi> \<Longrightarrow> - 1 < \<xi> * ((b - \<mu>) / \<sigma>)"
    using xi by linarith
  have h1[simp]:"set_integrable lborel {..b} (EVD_density \<xi> \<mu> \<sigma>)"
    and h2:"(\<integral>x\<in>{..b}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    and h3:"(\<integral>\<^sup>+x\<in>{..b}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    using EVD_density_set_integrable1[OF sigma less_imp_neq[OF xi] b b']
      EVD_density_set_integral1[OF sigma less_imp_neq[OF xi] b b']
      EVD_density_set_nn_integral1[OF sigma less_imp_neq[OF xi] b b'] xi
    by(simp_all add: b_def)
  have [simp]:"set_integrable lborel {b<..a} (EVD_density \<xi> \<mu> \<sigma>)"
    by(subst set_integrable_cong[where f'="\<lambda>x. 0",OF refl refl]) simp_all
  have eq0:"(\<integral>x\<in>{b<..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    by(subst set_integral_cong[where g="\<lambda>x. 0"]) auto
  have eq0':"(\<integral>\<^sup>+x\<in>{b<..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 0"
    by(subst set_nn_integral_cong[where g="\<lambda>x. 0",OF refl refl]) auto
  show "set_integrable lborel {..a} (EVD_density \<xi> \<mu> \<sigma>)"
    using ba
    by(subst set_integrable_cong[where A'="{..b} \<union> {b<..a}"])
      (auto intro!: set_integrable_Un h1)
  have "(\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) =
       (\<integral>x\<in>{..b}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) + (\<integral>x\<in>{b<..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)"
    using ba
    by(subst set_integral_Un[symmetric])
      (auto intro!: arg_cong[where f="\<lambda>B. set_lebesgue_integral lborel B _"])
  also have "... = 1"
    by (auto simp: h2 eq0)
  finally show "(\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1" .
  have "(\<integral>\<^sup>+x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) =
        (\<integral>\<^sup>+x. ennreal (EVD_density \<xi> \<mu> \<sigma> x) * indicator {..b} x
         + ennreal (EVD_density \<xi> \<mu> \<sigma> x) * indicator {b<..a} x \<partial>lborel)"
    using ba by(auto intro!: nn_integral_cong simp: indicator_def)
  also have "... = (\<integral>\<^sup>+x\<in>{..b}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)"
    using ba by(auto intro!: nn_integral_cong simp: indicator_def)
  finally show "(\<integral>\<^sup>+x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    by(simp add: h3)
qed

lemma EVD_density_set_integrable:
  assumes sigma[arith]:"0 < \<sigma>"
  shows "set_integrable lborel {..a} (EVD_density \<xi> \<mu> \<sigma>)"
proof -
  consider "\<xi> = 0" | "\<xi> \<noteq> 0" "- 1 < \<xi> * ((a - \<mu>) / \<sigma>)"
    | "\<xi> * ((a - \<mu>) / \<sigma>) \<le> -1" "\<xi> > 0" | "\<xi> * ((a - \<mu>) / \<sigma>) \<le> -1" "\<xi> < 0"
    by argo
  thus ?thesis
    by cases
    (use EVD_density_set_integrable0[OF sigma]
      EVD_density_set_integrable1[OF sigma _ less_imp_le]
      EVD_density_set_integrable2[OF sigma]
      EVD_density_set_integrable3[OF sigma] in auto)
qed

abbreviation EVD_cdf where "EVD_cdf \<equiv> \<lambda>\<xi> \<mu> \<sigma> x. cdf (density lborel (EVD_density \<xi> \<mu> \<sigma>)) x"

lemma EVD_cdf_set_integral:
  assumes sigma[arith]:"0 < \<sigma>"
  shows "EVD_cdf \<xi> \<mu> \<sigma> a = (\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)"
proof -
  consider "\<xi> = 0" | "\<xi> \<noteq> 0" "- 1 < \<xi> * ((a - \<mu>) / \<sigma>)"
    | "\<xi> > 0" "\<xi> * ((a - \<mu>) / \<sigma>) \<le> - 1"
    | "\<xi> < 0" "\<xi> * ((a - \<mu>) / \<sigma>) \<le> - 1"
    by linarith
  thus ?thesis
    unfolding cdf_def
    using EVD_density_set_integrable3[OF sigma]
      EVD_density_set_integrable2[OF sigma]
      EVD_density_set_integrable1[OF sigma]
      EVD_density_set_integrable0[OF sigma]
    by (cases; subst measure_density_on) auto
qed

corollary EVD_cdf_def:
  assumes sigma[arith]:"0 < \<sigma>"
  shows "EVD_cdf \<xi> \<mu> \<sigma> x =
                    (let y = (x - \<mu>) / \<sigma> in
                     if \<xi> = 0 then exp (- exp (- y))
                     else if \<xi> * y > - 1 then exp (- ((1 + \<xi> * y) powr (- 1 / \<xi>)))
                     else if \<xi> > 0 then 0 else 1)"
proof -
  note cdf_simps = cdf_def measure_def emeasure_density
  consider "\<xi> = 0" | "\<xi> \<noteq> 0" "- 1 < \<xi> * ((x - \<mu>) / \<sigma>)"
    | "\<xi> * ((x - \<mu>) / \<sigma>) \<le> -1" "\<xi> > 0" | "\<xi> * ((x - \<mu>) / \<sigma>) \<le> -1" "\<xi> < 0"
    by argo
  thus ?thesis
  proof cases
    assume 2:"\<xi> \<noteq> 0" "- 1 < \<xi> * ((x - \<mu>) / \<sigma>)"
    thus ?thesis
      by(simp add: cdf_simps
          EVD_density_set_nn_integral1[OF sigma 2(1) less_imp_le[OF 2(2)] 2(2)])
  qed(simp_all add: cdf_simps minus_divide_left
      EVD_density_set_nn_integral0
      EVD_density_set_nn_integral2
      EVD_density_set_nn_integral3)
qed

lemma EVD_cdf_supp_bounds:
  fixes x \<gamma> :: real
  assumes [arith]:"1 + \<gamma> * (x - \<mu>) / \<sigma> > 0" "0 < \<sigma>"
  shows "0 < EVD_cdf \<gamma> \<mu> \<sigma> x" "EVD_cdf \<gamma> \<mu> \<sigma> x \<le> 1"
  using assms by (auto simp add: EVD_cdf_def Let_def)

lemma EVD_cdf_supp_bounds01:
  fixes x \<gamma> :: real
  assumes [arith]:"1 + \<gamma> * x > 0"
  shows "0 < EVD_cdf \<gamma> 0 1 x" "EVD_cdf \<gamma> 0 1 x \<le> 1"
  by(auto intro!: EVD_cdf_supp_bounds)

lemma ln_EVD_cdf_0:
  assumes "0 < \<sigma>"
  shows "- ln (EVD_cdf 0 \<mu> \<sigma> x) = exp (- ((x - \<mu>) / \<sigma>))"
  using assms by(simp add: EVD_cdf_def[of \<sigma>])

lemma ln_EVD_cdf_1:
  assumes "0 < \<sigma>" "1 + \<gamma> * (x - \<mu>) / \<sigma> > 0" "\<gamma> \<noteq> 0"
  shows "- ln (EVD_cdf \<gamma> \<mu> \<sigma> x) = (1 + \<gamma> * (x - \<mu>) / \<sigma>) powr (- 1 / \<gamma>)"
  using assms by(auto simp add: EVD_cdf_def[of \<sigma>])

lemma EVD_cdf_location_scale:
  assumes [arith]:"0 < \<sigma>"
  shows "EVD_cdf \<xi> 0 1 ((x - \<mu>) / \<sigma>) = EVD_cdf \<xi> \<mu> \<sigma> x"
  by(simp add: EVD_cdf_def)

lemma EVD_cdf_at_bot_0:
  assumes sigma:"0 < \<sigma>"
  shows "(EVD_cdf \<xi> \<mu> \<sigma> \<longlongrightarrow> 0) at_bot"
proof -
  consider "\<xi> = 0" | "\<xi> > 0" | "\<xi> < 0"
    by linarith
  thus ?thesis
  proof cases
    assume xi:"\<xi> = 0"
    have *: "((\<lambda>x. exp (- exp (- ((x - \<mu>) / \<sigma>)))) \<longlongrightarrow> 0) at_bot"
      using sigma
      by(intro filterlim_compose[OF exp_at_bot
                 filterlim_compose[OF filterlim_uminus_at_bot_at_top]]
               filterlim_compose[OF exp_at_top])
        real_asymp
    show ?thesis
      by(rule Lim_transform_eventually[OF *])
        (use xi in \<open>simp add: EVD_cdf_def[OF sigma] Let_def\<close>)
  next
    assume xi:"\<xi> > 0"
    have ev: "\<forall>\<^sub>F x in at_bot. EVD_cdf \<xi> \<mu> \<sigma> x = 0"
      using xi sigma
      by (auto intro!: eventually_mono[OF eventually_le_at_bot[of "\<mu> - \<sigma> / \<xi>"]]
          simp: EVD_cdf_def[OF sigma] Let_def field_simps)
    thus ?thesis
      by (rule tendsto_eventually)
  next
    assume xi:"\<xi> < 0"
    have p_pos: "0 < - 1 / \<xi>"
      using xi by (simp add: divide_pos_neg)
    note base = filterlim_shift_scale_at_bot[OF sigma xi]
    have *: "((\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) \<longlongrightarrow> 0) at_bot"
      by (rule filterlim_compose[OF exp_at_bot
            filterlim_compose[OF filterlim_uminus_at_bot_at_top
              filterlim_compose[OF real_powr_at_top[OF p_pos] base]]])
    have evlt: "\<forall>\<^sub>F x in at_bot. x < \<mu> - \<sigma> / \<xi>"
      using eventually_le_at_bot[of "\<mu> - \<sigma> / \<xi> - 1"] by eventually_elim simp
    have ev:
      "\<forall>\<^sub>F x in at_bot. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>))) = EVD_cdf \<xi> \<mu> \<sigma> x"
      using evlt
    proof eventually_elim
      case (elim x)
      have "(x - \<mu>) / \<sigma> < ((\<mu> - \<sigma> / \<xi>) - \<mu>) / \<sigma>"
        using elim sigma by (intro divide_strict_right_mono) auto
      hence "\<xi> * (((\<mu> - \<sigma> / \<xi>) - \<mu>) / \<sigma>) < \<xi> * ((x - \<mu>) / \<sigma>)"
        by (rule mult_strict_left_mono_neg[OF _ xi])
      moreover have "\<xi> * (((\<mu> - \<sigma> / \<xi>) - \<mu>) / \<sigma>) = - 1"
        using xi sigma by (simp add: field_simps)
      ultimately have "- 1 < \<xi> * ((x - \<mu>) / \<sigma>)"
        by simp
      thus ?case
        using xi by (simp add: EVD_cdf_def[OF sigma] Let_def)
    qed
    show ?thesis
      by (rule Lim_transform_eventually[OF * ev])
  qed
qed

lemma EVD_cdf_at_top_1:
  assumes sigma:"0 < \<sigma>"
  shows "(EVD_cdf \<xi> \<mu> \<sigma> \<longlongrightarrow> 1) at_top"
proof -
  consider "\<xi> = 0" | "\<xi> > 0" | "\<xi> < 0"
    by linarith
  thus ?thesis
  proof cases
    assume xi:"\<xi> = 0"
    have 1: "((\<lambda>x. exp (- ((x - \<mu>) / \<sigma>))) \<longlongrightarrow> 0) at_top"
      using sigma
      by (intro filterlim_compose[OF exp_at_bot]) real_asymp
    have "((\<lambda>x. exp (- exp (- ((x - \<mu>) / \<sigma>)))) \<longlongrightarrow> exp (- 0)) at_top"
      by (intro tendsto_intros 1)
    hence *: "((\<lambda>x. exp (- exp (- ((x - \<mu>) / \<sigma>)))) \<longlongrightarrow> 1) at_top"
      by simp
    show ?thesis
      by(rule Lim_transform_eventually[OF *])
        (use xi in \<open>simp add: EVD_cdf_def[OF sigma] Let_def\<close>)
  next
    assume xi:"\<xi> > 0"
    have p_neg: "- 1 / \<xi> < 0"
      using xi by (simp add: divide_neg_pos)
    have powr0: "((\<lambda>x. (1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)) \<longlongrightarrow> 0) at_top"
      by (rule tendsto_neg_powr[OF p_neg filterlim_shift_scale_at_top[OF sigma xi]])
    have "((\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) \<longlongrightarrow> exp (- 0)) at_top"
      by (intro tendsto_intros powr0)
    hence *: "((\<lambda>x. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>)))) \<longlongrightarrow> 1) at_top"
      by simp
    have ev:
      "\<forall>\<^sub>F x in at_top. exp (- ((1 + \<xi> * ((x - \<mu>) / \<sigma>)) powr (- 1 / \<xi>))) = EVD_cdf \<xi> \<mu> \<sigma> x"
      using eventually_gt_at_top[of "\<mu> - \<sigma> / \<xi>"]
    proof eventually_elim
      case (elim x)
      have "((\<mu> - \<sigma> / \<xi>) - \<mu>) / \<sigma> < (x - \<mu>) / \<sigma>"
        using elim sigma by (intro divide_strict_right_mono) auto
      hence "\<xi> * (((\<mu> - \<sigma> / \<xi>) - \<mu>) / \<sigma>) < \<xi> * ((x - \<mu>) / \<sigma>)"
        by (rule mult_strict_left_mono[OF _ xi])
      moreover have "\<xi> * (((\<mu> - \<sigma> / \<xi>) - \<mu>) / \<sigma>) = - 1"
        using xi sigma by (simp add: field_simps)
      ultimately have "- 1 < \<xi> * ((x - \<mu>) / \<sigma>)"
        by simp
      thus ?case
        using xi by (simp add: EVD_cdf_def[OF sigma] Let_def)
    qed
    show ?thesis
      by (rule Lim_transform_eventually[OF * ev])
  next
    assume xi:"\<xi> < 0"
    have ev: "\<forall>\<^sub>F x in at_top. EVD_cdf \<xi> \<mu> \<sigma> x = 1"
      using eventually_ge_at_top[of "\<mu> - \<sigma> / \<xi>"]
    proof eventually_elim
      case (elim x)
      have "((\<mu> - \<sigma> / \<xi>) - \<mu>) / \<sigma> \<le> (x - \<mu>) / \<sigma>"
        using elim sigma by (intro divide_right_mono) auto
      hence "\<xi> * ((x - \<mu>) / \<sigma>) \<le> \<xi> * (((\<mu> - \<sigma> / \<xi>) - \<mu>) / \<sigma>)"
        by (rule mult_left_mono_neg[OF _ less_imp_le[OF xi]])
      moreover have "\<xi> * (((\<mu> - \<sigma> / \<xi>) - \<mu>) / \<sigma>) = - 1"
        using xi sigma by (simp add: field_simps)
      ultimately have "\<xi> * ((x - \<mu>) / \<sigma>) \<le> - 1"
        by simp
      thus ?case
        using xi by (simp add: EVD_cdf_def[OF sigma] Let_def)
    qed
    thus ?thesis
      by (rule tendsto_eventually)
  qed
qed

lemma
  assumes sigma[arith]:"0 < \<sigma>"
  shows EVD_density_integrable:"integrable lborel (EVD_density \<xi> \<mu> \<sigma>)"
    and EVD_density_integral:"(\<integral>x. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    and EVD_density_nn_integral:"(\<integral>\<^sup>+x. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
proof -
  have lim:"((\<lambda>a. (\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel)) \<longlongrightarrow> 1) at_top"
  proof -
    have *:"(\<integral>x\<in>{..a}. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = EVD_cdf \<xi> \<mu> \<sigma> a" for a
      unfolding cdf_def
      by(subst measure_density_on)
        (auto simp: EVD_density_set_integrable)
    show ?thesis
      unfolding * by(rule EVD_cdf_at_top_1[OF sigma])
  qed
  show integ:"integrable lborel (EVD_density \<xi> \<mu> \<sigma>)"
    and eq2:"(\<integral>x. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    using lim EVD_density_set_integrable[OF sigma]
      integrable_monotone_convergence_at_top[where f="EVD_density \<xi> \<mu> \<sigma>" and x=1,
        OF _ AE_I2[OF EVD_density_nonneg[OF less_imp_le[OF sigma]]]]
      integral_monotone_convergence_at_top[where f="EVD_density \<xi> \<mu> \<sigma>" and x=1,
        OF _ AE_I2[OF EVD_density_nonneg[OF less_imp_le[OF sigma]]]]
    by(auto simp: set_integrable_def set_lebesgue_integral_def mult.commute)
  thus "(\<integral>\<^sup>+x. EVD_density \<xi> \<mu> \<sigma> x \<partial>lborel) = 1"
    by(subst nn_integral_eq_integral) auto
qed

lemma prob_space_EVD:
  assumes sigma[arith]:"0 < \<sigma>"
  shows "prob_space (density lborel (EVD_density \<xi> \<mu> \<sigma>))"
  by(auto intro!: prob_spaceI simp: emeasure_density EVD_density_nn_integral)

corollary real_distribution_EVD:
  "0 < \<sigma> \<Longrightarrow> real_distribution (density lborel (EVD_density \<xi> \<mu> \<sigma>))"
  by(simp add: real_distribution_def real_distribution_axioms_def prob_space_EVD)

corollary right_continuous_mono_EVD_cdf:
  "0 < \<sigma> \<Longrightarrow> right_continuous_mono (EVD_cdf \<xi> \<mu> \<sigma>) 0 1"
  by(auto intro!: right_continuous_mono_cdf real_distribution_EVD)

corollary EVD_cdf_nonneg:"0 < \<sigma> \<Longrightarrow> 0 \<le> EVD_cdf \<xi> \<mu> \<sigma> x"
  and EVD_cdf_le_1:"0 < \<sigma> \<Longrightarrow> EVD_cdf \<xi> \<mu> \<sigma> x \<le> 1"
  using right_continuous_mono_EVD_cdf right_continuous_mono.a_le_f[of _ 0 1]
    right_continuous_mono.f_le_b[of _ 0 1]
  by fastforce+

lemma isCont_EVD_cdf:
  assumes sigma[arith]: "0 < \<sigma>"
  shows "isCont (EVD_cdf \<xi> \<mu> \<sigma>) x"
  using continuous_on_LBINT_com[OF EVD_density_integrable[OF sigma]]
    EVD_cdf_set_integral[OF sigma]
  by simp

corollary weak_conv_EVD_cdf_iff:
  assumes sigma:"0 < \<sigma>"
  shows "weak_conv F (EVD_cdf \<xi> \<mu> \<sigma>) \<longleftrightarrow> (\<forall>x. (\<lambda>n. F n x) \<longlonglongrightarrow> EVD_cdf \<xi> \<mu> \<sigma> x)"
  using isCont_EVD_cdf[OF sigma] by(simp add: weak_conv_def)

text \<open>Max-stability of the GEV distribution (Exercise~1.2 of the book~\<^cite>\<open>deHaanFerreira\<close>).
      The book's argument is
      $G_\xi^n(a_n x + b_n) = G_\xi(x)$ for $a_n = n^\xi$ and $b_n = (n^\xi - 1)/\xi$,
      whereas we state the equivalent solved form
      $G_\xi^n(x) = G_\xi((x - b_n)/a_n)$, in which
      $(x - b_n)/a_n = n^{-\xi}x + (n^{-\xi} - 1)/\xi$.\<close>
lemma EVD_cdf_max_stable:
  assumes "0 < n"
  shows "EVD_cdf \<xi> 0 1 x ^ n
          = EVD_cdf \<xi> 0 1 (if \<xi> = 0 then x - ln n
                            else n powr (- \<xi>) * x + (real n powr (- \<xi>) - 1) / \<xi>)"
proof -
  have [arith]: "(0::real) < 1"
    by simp
  consider "\<xi> = 0" | "\<xi> \<noteq> 0" "- 1 < \<xi> * x" | "\<xi> \<noteq> 0" "\<xi> * x \<le> - 1" by argo
  thus ?thesis
  proof cases
    case 1
    have "EVD_cdf \<xi> 0 1 x ^ n = exp (real n * (- exp (- x)))"
      by (simp add: EVD_cdf_def Let_def 1 exp_of_nat_mult[symmetric])
    also have "real n * (- exp (- x)) = - exp (- (x - ln (real n)))"
      using assms by (simp add: exp_diff exp_minus field_simps)
    finally show ?thesis
      using 1 by (simp add: EVD_cdf_def Let_def)
  next
    case 2
    define c where "c = real n powr (- \<xi>)"
    have c_pos: "0 < c"
      using assms by (simp add: c_def)
    have arg: "1 + \<xi> * (c * x + (c - 1) / \<xi>) = c * (1 + \<xi> * x)"
      using 2(1) by (simp add: field_simps)
    have p1: "0 < c * (1 + \<xi> * x)"
      using c_pos 2(2) by (intro mult_pos_pos) auto
    have argpos: "- 1 < \<xi> * (c * x + (c - 1) / \<xi>)"
      using arg p1 by linarith
    have "(c * (1 + \<xi> * x)) powr (- 1 / \<xi>) = c powr (- 1 / \<xi>) * (1 + \<xi> * x) powr (- 1 / \<xi>)"
      by (rule powr_mult)
    also have "c powr (- 1 / \<xi>) = real n powr ((- \<xi>) * (- 1 / \<xi>))"
      by (simp add: c_def powr_powr)
    also have "(- \<xi>) * (- 1 / \<xi>) = 1"
      using 2(1) by simp
    also have "real n powr 1 = real n"
      by simp
    finally have *: "(c * (1 + \<xi> * x)) powr (- 1 / \<xi>) = real n * (1 + \<xi> * x) powr (- 1 / \<xi>)" .
    have "EVD_cdf \<xi> 0 1 x ^ n = exp (real n * (- ((1 + \<xi> * x) powr (- 1 / \<xi>))))"
      using 2 by (simp add: EVD_cdf_def Let_def exp_of_nat_mult[symmetric])
    also have "\<dots> = exp (- ((c * (1 + \<xi> * x)) powr (- 1 / \<xi>)))"
      using * by simp
    also have "\<dots> = EVD_cdf \<xi> 0 1 (c * x + (c - 1) / \<xi>)"
      using 2(1) argpos by (simp add: EVD_cdf_def Let_def arg)
    finally show ?thesis
      using 2(1) by (simp add: c_def)
  next
    case 3
    define c where "c = real n powr (- \<xi>)"
    have c_pos: "0 < c"
      using assms by (simp add: c_def)
    have le0: "c * (1 + \<xi> * x) \<le> 0"
      using 3(2) by (intro mult_nonneg_nonpos) (use c_pos in auto)
    have arg: "\<xi> * (c * x + (c - 1) / \<xi>) = c * (1 + \<xi> * x) - 1"
      using 3(1) by (simp add: field_simps)
    have argneg: "\<xi> * (c * x + (c - 1) / \<xi>) \<le> - 1"
      using le0 by (simp add: arg)
    consider "0 < \<xi>" | "\<xi> < 0" using 3(1) by argo
    thus ?thesis
    proof cases
      case pos: 1
      hence "EVD_cdf \<xi> 0 1 x = 0"
        using 3 by (simp add: EVD_cdf_def Let_def)
      moreover have "EVD_cdf \<xi> 0 1 (c * x + (c - 1) / \<xi>) = 0"
        using pos argneg by (simp add: EVD_cdf_def Let_def not_less)
      ultimately show ?thesis
        using assms 3(1) by (simp add: c_def)
    next
      case neg: 2
      hence "EVD_cdf \<xi> 0 1 x = 1"
        using 3 by (simp add: EVD_cdf_def Let_def)
      moreover have "EVD_cdf \<xi> 0 1 (c * x + (c - 1) / \<xi>) = 1"
        using neg argneg by (simp add: EVD_cdf_def Let_def not_less)
      ultimately show ?thesis
        using 3(1) by (simp add: c_def)
    qed
  qed
qed

end