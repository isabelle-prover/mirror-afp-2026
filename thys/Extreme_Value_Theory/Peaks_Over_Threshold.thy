(*  Title:   Peaks_Over_Threshold.thy
    Author:  Michikazu Hirata
*)
section \<open>Peaks Over Threshold\<close>
theory Peaks_Over_Threshold
imports
   "Domain_of_Attraction"
begin

text \<open>In this section, we formalize the Pickands--Balkema--de Haan theorem.
      Our formalization is stated in the form of Theorem~3.4.13(b)
      in the book by Embrechts et al.~\<^cite>\<open>EmbrechtsKluppelbergMikosch\<close>.
      The original sources of the theorem are Theorems~3 and~4 in the paper
      by Balkema and de Haan~\<^cite>\<open>BalkemaDeHaan1974\<close> and
      Theorem~7 in the paper by Pickands~\<^cite>\<open>Pickands1975\<close>.\<close>

subsection \<open>Excess (Peaks-Over-Threshold) Distribution Function\<close>
definition excess_cdf :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"excess_cdf F u x = 1 - (1 - F (u + x)) / (1 - F u)"

lemma excess_cdf_def2:"F u < 1 \<Longrightarrow> excess_cdf F u x = (F (u + x) - F u) / (1 - F u)"
  by (smt (verit, ccfv_threshold) add_divide_distrib divide_self_if excess_cdf_def)

lemma excess_cdf_0[simp]: "F u < 1 \<Longrightarrow> excess_cdf F u 0 = 0"
  by (simp add: excess_cdf_def)

lemma excess_cdf_eq_1_of_F_eq_1:
  assumes "F u = 1"
  shows "excess_cdf F u x = 1"
  using assms by (simp add: excess_cdf_def)

lemma excess_cdf_mono:
  assumes F: "right_continuous_mono F 0 1" and xy: "x \<le> y"
  shows "excess_cdf F u x \<le> excess_cdf F u y"
proof (cases "F u < 1")
  assume Fu: "F u < 1"
  have mono: "F (u + x) \<le> F (u + y)"
    using xy by (intro monoD[OF right_continuous_mono.mono[OF F]]) simp
  have "(1 - F (u + y)) / (1 - F u) \<le> (1 - F (u + x)) / (1 - F u)"
    using mono Fu by (intro divide_right_mono) auto
  thus ?thesis
    by (simp add: excess_cdf_def)
next
  case False
  hence "F u = 1"
    using right_continuous_mono.f_le_b[OF F, of u] by linarith
  thus ?thesis
    by (simp add: excess_cdf_eq_1_of_F_eq_1)
qed

lemma excess_cdf_bounds:
  assumes F: "right_continuous_mono F 0 1" and x: "0 \<le> x"
  shows "0 \<le> excess_cdf F u x" "excess_cdf F u x \<le> 1"
proof -
  have "0 \<le> excess_cdf F u x \<and> excess_cdf F u x \<le> 1"
  proof (cases "F u < 1")
    case Fu: True
    have le1: "F (u + x) \<le> 1"
      using right_continuous_mono.f_le_b[OF F] .
    have ge: "F u \<le> F (u + x)"
      using x by (intro monoD[OF right_continuous_mono.mono[OF F]]) simp
    have "(1 - F (u + x)) / (1 - F u) \<le> 1"
      using ge Fu by (simp add: divide_le_eq)
    moreover have "0 \<le> (1 - F (u + x)) / (1 - F u)"
      using le1 Fu by (simp add: divide_nonneg_pos)
    ultimately show ?thesis
      by (simp add: excess_cdf_def)
  next
    case False
    hence "F u = 1"
      using right_continuous_mono.f_le_b[OF F, of u] by linarith
    thus ?thesis
      by (simp add: excess_cdf_eq_1_of_F_eq_1)
  qed
  thus "0 \<le> excess_cdf F u x" "excess_cdf F u x \<le> 1"
    by auto
qed

lemma excess_cdf_eq_1_beyond_support:
  assumes F: "right_continuous_mono F 0 1" and bdd: "bdd_support F"
    and xu: "x_star F \<le> u + x"
  shows "excess_cdf F u x = 1"
proof -
  have "F (x_star F) = 1"
    by (intro F_x_star_eq_1 F bdd)
  moreover have "F (x_star F) \<le> F (u + x)"
    using xu by (intro monoD[OF right_continuous_mono.mono[OF F]])
  ultimately have "F (u + x) = 1"
    using right_continuous_mono.f_le_b[OF F, of "u + x"] by linarith
  thus ?thesis
    by (simp add: excess_cdf_def)
qed

lemma excess_tendsto_of_divide_tail:
  fixes F f :: "real \<Rightarrow> real" and \<gamma> x :: real
  assumes F: "right_continuous_mono F 0 1"
    and fpos: "\<And>t. 0 < f t"
    and lim: "\<And>x. 1 + \<gamma> * x > 0 \<Longrightarrow>
                  ((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
                     \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F)"
    and x: "0 \<le> x"
  shows "((\<lambda>t. excess_cdf F t (f t * x)) \<longlongrightarrow> GPD_cdf \<gamma> 0 1 x) (endpoint_filter F)"
proof -
  have main: "((\<lambda>t. excess_cdf F t (f t * y)) \<longlongrightarrow> GPD_cdf \<gamma> 0 1 y) (endpoint_filter F)"
    if y: "0 \<le> y" and supp: "1 + \<gamma> * y > 0" for y
  proof -
    have ratio_lim: "((\<lambda>t. (1 - F (t + y * f t)) / (1 - F t))
                        \<longlongrightarrow> 1 - GPD_cdf \<gamma> 0 1 y) (endpoint_filter F)"
      using lim[OF supp] EVD_tail_eq_GPD_cdf[OF supp y] by simp
    have "((\<lambda>t. 1 - (1 - F (t + y * f t)) / (1 - F t))
             \<longlongrightarrow> 1 - (1 - GPD_cdf \<gamma> 0 1 y)) (endpoint_filter F)"
      by (intro tendsto_diff tendsto_const ratio_lim)
    thus ?thesis
      by (simp add: excess_cdf_def mult.commute)
  qed
  show ?thesis
  proof (cases "1 + \<gamma> * x > 0")
    case True
    show ?thesis
      by (rule main[OF x True])
  next
    case False
    hence notsupp: "1 + \<gamma> * x \<le> 0"
      by simp
    have gneg: "\<gamma> < 0"
    proof (rule ccontr)
      assume "\<not> \<gamma> < 0"
      hence "0 \<le> \<gamma> * x"
        using x by (intro mult_nonneg_nonneg) auto
      with notsupp show False
        by simp
    qed
    have gpdx1: "GPD_cdf \<gamma> 0 1 x = 1"
      using x gneg notsupp by (auto simp: GPD_cdf_def[OF zero_less_one] Let_def)
    have gpdbdry: "GPD_cdf \<gamma> 0 1 (- 1 / \<gamma>) = 1"
      using gneg by (simp add: GPD_cdf_def[OF zero_less_one] Let_def)
    have gpd_cont: "(GPD_cdf \<gamma> 0 1 \<longlongrightarrow> 1) (at (- 1 / \<gamma>))"
      using isCont_GPD_cdf[OF zero_less_one, where \<xi> = \<gamma> and \<mu> = 0 and x = "- 1 / \<gamma>"] gpdbdry
      by (simp add: isCont_def)
    have gpd_cont_left: "(GPD_cdf \<gamma> 0 1 \<longlongrightarrow> 1) (at_left (- 1 / \<gamma>))"
      using gpd_cont by (simp add: filterlim_at_split)
    have le1: "excess_cdf F t (f t * x) \<le> 1" for t
      using fpos[of t] x by (intro excess_cdf_bounds(2)[OF F]) simp
    have "((\<lambda>t. excess_cdf F t (f t * x)) \<longlongrightarrow> 1) (endpoint_filter F)"
      unfolding tendsto_iff dist_real_def
    proof safe
      fix e :: real
      assume e: "0 < e"
      have "\<forall>\<^sub>F y in at_left (- 1 / \<gamma>). 1 - e < GPD_cdf \<gamma> 0 1 y"
        using order_tendstoD(1)[OF gpd_cont_left, of "1 - e"] e by simp
      moreover have "\<forall>\<^sub>F y in at_left (- 1 / \<gamma>). y < - 1 / \<gamma> \<and> 0 \<le> y"
        using gneg by (intro eventually_at_leftI[of 0]) auto
      ultimately obtain x0 where x0: "1 - e < GPD_cdf \<gamma> 0 1 x0" "x0 < - 1 / \<gamma>" "0 \<le> x0"
        using eventually_happens'[OF trivial_limit_at_left_real eventually_conj] by blast
      have supp0: "1 + \<gamma> * x0 > 0"
        using mult_strict_left_mono_neg[OF x0(2) gneg] gneg by simp
      have x0x: "x0 < x"
      proof (rule ccontr)
        assume "\<not> x0 < x"
        hence "1 + \<gamma> * x0 \<le> 1 + \<gamma> * x"
          using gneg by (intro add_left_mono mult_left_mono_neg) auto
        with supp0 notsupp show False
          by simp
      qed
      have "\<forall>\<^sub>F t in endpoint_filter F. 1 - e < excess_cdf F t (f t * x0)"
        using order_tendstoD(1)[OF main[OF x0(3) supp0] x0(1)] .
      thus "\<forall>\<^sub>F t in endpoint_filter F. \<bar>excess_cdf F t (f t * x) - 1\<bar> < e"
      proof eventually_elim
        case (elim t)
        have "excess_cdf F t (f t * x0) \<le> excess_cdf F t (f t * x)"
          using fpos[of t] x0x
          by (intro excess_cdf_mono[OF F] mult_left_mono less_imp_le) auto
        with elim le1[of t] show ?case
          by (simp add: abs_less_iff)
      qed
    qed
    thus ?thesis
      using gpdx1 by simp
  qed
qed

lemma tail_probability_u_form:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  shows "\<exists>\<beta>. (\<forall>u. 0 < \<beta> u) \<and>
             (\<forall>x\<ge>0. ((\<lambda>u. excess_cdf F u (\<beta> u * x) - GPD_cdf \<gamma> 0 1 x)
                       \<longlongrightarrow> 0) (endpoint_filter F))"
proof -
  obtain f where fpos: "\<And>t. 0 < f t"
    and lim: "\<And>x. 1 + \<gamma> * x > 0 \<Longrightarrow>
                  ((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
                     \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F)"
    using MDA_iff_divide_tail[OF F] dom by blast
  show ?thesis
  proof (safe intro!: exI[of _ f])
    show "\<And>u. 0 < f u"
      using fpos by blast
  next
    fix x :: real
    assume x: "0 \<le> x"
    from tendsto_diff[OF excess_tendsto_of_divide_tail[OF F fpos lim x] tendsto_const,
                      of "GPD_cdf \<gamma> 0 1 x"]
    show "((\<lambda>u. excess_cdf F u (f u * x) - GPD_cdf \<gamma> 0 1 x) \<longlongrightarrow> 0) (endpoint_filter F)"
      by simp
  qed
qed

lemma excess_pointwise_imp_uniform:
  fixes F :: "real \<Rightarrow> real" and \<beta> :: "real \<Rightarrow> real" and FF :: "real filter"
  assumes F: "right_continuous_mono F 0 1" and \<beta>pos: "\<And>u. 0 < \<beta> u"
    and pconv: "\<And>x. 0 \<le> x \<Longrightarrow> ((\<lambda>u. excess_cdf F u (\<beta> u * x)) \<longlongrightarrow> GPD_cdf \<gamma> 0 1 x) FF"
  shows "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1) FF"
proof -
  interpret GPD: right_continuous_mono "GPD_cdf \<gamma> 0 1" 0 1
    by (intro right_continuous_mono_GPD_cdf zero_less_one)
  interpret F: right_continuous_mono F 0 1
    by fact
  show ?thesis
  proof (rule mono_on_UCT_atLeast[OF eventuallyI[OF mono_onI] eventuallyI mono_onI])
    fix u :: real and x y :: real
    assume "x \<in>{0..}" "x \<le> y"
    thus "excess_cdf F u (\<beta> u * x) \<le> excess_cdf F u (\<beta> u * y)"
      using \<beta>pos[of u] by (intro excess_cdf_mono[OF F] mult_left_mono) auto
  next
    fix u :: real
    show "\<forall>x\<ge>0. excess_cdf F u (\<beta> u * x) \<le> 1"
      using \<beta>pos[of u] excess_cdf_bounds[OF F] by simp
  next
    fix x y :: real
    assume "x \<in>{0..}" "x \<le> y"
    thus "GPD_cdf \<gamma> 0 1 x \<le> GPD_cdf \<gamma> 0 1 y"
      by (intro monoD[OF GPD.mono])
  next
    show "continuous_on {0..} (GPD_cdf \<gamma> 0 1)"
      using isCont_GPD_cdf by(auto intro!: continuous_at_imp_continuous_on)
  next
    show "(GPD_cdf \<gamma> 0 1 \<longlongrightarrow> 1) at_top"
      by (intro GPD_cdf_at_top_1 zero_less_one)
  qed fact
qed

lemma tail_probability_u_form_uniform:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  shows "\<exists>\<beta>. (\<forall>u. 0 < \<beta> u) \<and>
             uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
               (endpoint_filter F)"
proof -
  obtain \<beta> where \<beta>pos: "\<And>u. 0 < \<beta> u"
    and pconv0: "\<And>x. 0 \<le> x \<Longrightarrow>
               ((\<lambda>u. excess_cdf F u (\<beta> u * x) - GPD_cdf \<gamma> 0 1 x) \<longlongrightarrow> 0) (endpoint_filter F)"
    using tail_probability_u_form[OF F dom] by blast
  have pconv: "((\<lambda>u. excess_cdf F u (\<beta> u * x)) \<longlongrightarrow> GPD_cdf \<gamma> 0 1 x) (endpoint_filter F)"
    if x: "0 \<le> x" for x
    using tendsto_add[OF pconv0[OF x] tendsto_const, of "GPD_cdf \<gamma> 0 1 x"] by simp
  have "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1) (endpoint_filter F)"
    by (intro excess_pointwise_imp_uniform[OF F \<beta>pos] pconv)
  thus ?thesis
    using \<beta>pos by blast
qed
subsection \<open>Pickands--Balkema--de Haan Theorem\<close>
text \<open>The proof of the direct half follows the proof of Theorem~3.4.13(b) in the
      same book: the pointwise statement is Theorem~1.1.6(4) of the book by
      de Haan and Ferreira~\<^cite>\<open>deHaanFerreira\<close>, and uniformity follows since the
      limit is continuous.
      The converse half follows the route sketched in the proof
      of Theorem~3.4.5 of Embrechts et al.~\<^cite>\<open>EmbrechtsKluppelbergMikosch\<close>.\<close>
subsubsection \<open>Direct Half\<close>
theorem Pickands_Balkema_de_Haan_forward:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  shows "\<exists>\<beta>. (\<forall>u. 0 < \<beta> u) \<and>
             uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x)
               (\<lambda>x. 0) (endpoint_filter F)"
proof -
  obtain \<beta> where \<beta>pos: "\<And>u. 0 < \<beta> u"
    and ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
               (endpoint_filter F)"
    using tail_probability_u_form_uniform[OF F dom] by blast
  have "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0)
          (endpoint_filter F)"
  proof (rule uniform_limitI)
    fix \<epsilon> :: real
    assume \<epsilon>: "0 < \<epsilon>"
    show "\<forall>\<^sub>F u in endpoint_filter F.
            \<forall>x\<in>{0..}. dist (excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) 0 < \<epsilon>"
      using uniform_limitD[OF ul \<epsilon>]
    proof eventually_elim
      case (elim u)
      show ?case
      proof
        fix x :: real
        assume "x \<in> {0..}"
        hence x: "0 \<le> x"
          by simp
        have y: "x / \<beta> u \<in> {0..}"
          using x \<beta>pos[of u] by simp
        have dist_lt: "dist (excess_cdf F u (\<beta> u * (x / \<beta> u))) (GPD_cdf \<gamma> 0 1 (x / \<beta> u)) < \<epsilon>"
          using elim y by blast
        have rescale: "\<beta> u * (x / \<beta> u) = x"
          using \<beta>pos[of u] by simp
        have target: "GPD_cdf \<gamma> 0 1 (x / \<beta> u) = GPD_cdf \<gamma> 0 (\<beta> u) x"
          using GPD_cdf_location_scale[OF \<beta>pos[of u], of \<gamma> x] by simp
        show "dist (excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) 0 < \<epsilon>"
          using dist_lt unfolding rescale target by (simp add: dist_real_def)
      qed
    qed
  qed
  thus ?thesis
    using \<beta>pos by blast
qed

subsubsection \<open>Converse Half\<close>
lemma GPD_level_nonneg:
  fixes \<gamma> x :: real
  assumes "1 \<le> x"
  shows "0 \<le> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
  by (smt (verit) assms ge_one_powr_ge_zero ln_ge_zero nle_le powr_less_one
      powr_one_eq_one zero_le_divide_iff)

lemma GPD_level_pos:
  fixes \<gamma> x :: real
  assumes "1 < x"
  shows "0 < (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
  by (smt (verit, ccfv_SIG) assms divide_neg_neg divide_pos_pos
      gr_one_powr ln_one ln_strict_mono powr_less_one)

lemma GPD_level_supp:
  fixes \<gamma> x :: real
  assumes "1 \<le> x"
  shows "1 + \<gamma> * (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>) = (if \<gamma> = 0 then 1 else x powr \<gamma>)"
  using assms by simp

lemma GPD_tail_eq:
  assumes x: "0 \<le> x"
  shows "1 - GPD_cdf \<gamma> 0 1 x
           = (if \<gamma> = 0 then exp (- x)
              else if 0 \<le> 1 + \<gamma> * x then (1 + \<gamma> * x) powr (- 1 / \<gamma>) else 0)"
  using x by (simp add: GPD_cdf_def[OF zero_less_one] Let_def)

lemma GPD_tail_level:
  assumes x: "1 \<le> x"
  shows "1 - GPD_cdf \<gamma> 0 1 ((if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) = 1 / x"
proof (cases "\<gamma> = 0")
  case True
  thus ?thesis
    using x by (simp add: GPD_tail_eq GPD_level_nonneg exp_minus inverse_eq_divide)
next
  case False
  have x0: "0 < x"
    using x by simp
  have supp: "1 + \<gamma> * (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>) = x powr \<gamma>"
    using GPD_level_supp[OF x, of \<gamma>] False by simp
  have "0 < x powr \<gamma>"
    using x0 by simp
  hence "1 - GPD_cdf \<gamma> 0 1 (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)
           = (x powr \<gamma>) powr (- 1 / \<gamma>)"
    using GPD_level_nonneg[OF x, of \<gamma>] False supp by (simp add: GPD_tail_eq)
  also have "... = x powr (\<gamma> * (- 1 / \<gamma>))"
    using x0 by (simp add: powr_powr)
  also have "... = 1 / x"
    using False x0 by (simp add: powr_minus_divide field_simps)
  finally show ?thesis .
qed

lemma GPD_tail_strict_antimono:
  assumes y: "0 \<le> y" and yz: "y < z" and supp: "0 < 1 + \<gamma> * y"
  shows "1 - GPD_cdf \<gamma> 0 1 z < 1 - GPD_cdf \<gamma> 0 1 y"
proof -
  have z: "0 \<le> z"
    using y yz by simp
  show ?thesis
  proof (cases "\<gamma> = 0")
    case True
    thus ?thesis
      using y z yz by (simp add: GPD_tail_eq)
  next
    case nonzero: False
    show ?thesis
    proof (cases "0 < 1 + \<gamma> * z")
      case True
      show ?thesis
      proof (cases "0 < \<gamma>")
        case gpos: True
        have "1 + \<gamma> * y < 1 + \<gamma> * z"
          using yz gpos by simp
        hence "(1 + \<gamma> * z) powr (- 1 / \<gamma>) < (1 + \<gamma> * y) powr (- 1 / \<gamma>)"
          using supp gpos by (intro powr_less_mono2_neg) auto
        thus ?thesis
          using y z supp True nonzero by (simp add: GPD_tail_eq)
      next
        case False
        hence gneg: "\<gamma> < 0"
          using nonzero by simp
        have "1 + \<gamma> * z < 1 + \<gamma> * y"
          using yz gneg by simp
        hence "(1 + \<gamma> * z) powr (- 1 / \<gamma>) < (1 + \<gamma> * y) powr (- 1 / \<gamma>)"
          using True gneg by (intro powr_less_mono2) auto
        thus ?thesis
          using y z supp True nonzero by (simp add: GPD_tail_eq)
      qed
    next
      case False
      hence "1 - GPD_cdf \<gamma> 0 1 z \<le> 0"
        using z nonzero by (auto simp: GPD_tail_eq)
      moreover have "0 < 1 - GPD_cdf \<gamma> 0 1 y"
        using y supp by (simp add: GPD_tail_eq)
      ultimately show ?thesis
        by simp
    qed
  qed
qed

lemma GPD_tail_gt_level:
  assumes x: "1 < x" and y: "0 \<le> y" and lt: "y < (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
  shows "1 / x < 1 - GPD_cdf \<gamma> 0 1 y"
proof -
  have x1: "1 \<le> x"
    using x by simp
  have supp: "0 < 1 + \<gamma> * y"
  proof (cases "\<gamma> = 0")
    case True
    thus ?thesis
      by simp
  next
    case False
    hence sup': "1 + \<gamma> * (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>) = x powr \<gamma>"
      using GPD_level_supp[OF x1, of \<gamma>] by simp
    have pos: "0 < x powr \<gamma>"
      using x by simp
    show ?thesis
    proof (cases "0 < \<gamma>")
      case True
      hence "0 \<le> \<gamma> * y"
        using y by simp
      thus ?thesis
        by simp
    next
      case False
      hence gneg: "\<gamma> < 0"
        using \<open>\<gamma> \<noteq> 0\<close> by simp
      have "\<gamma> * (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>) < \<gamma> * y"
        by (rule mult_strict_left_mono_neg[OF lt gneg])
      thus ?thesis
        using sup' pos by linarith
    qed
  qed
  have "1 - GPD_cdf \<gamma> 0 1 ((if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) < 1 - GPD_cdf \<gamma> 0 1 y"
    by (intro GPD_tail_strict_antimono y lt supp)
  thus ?thesis
    using GPD_tail_level[OF x1, of \<gamma>] by simp
qed

lemma GPD_tail_lt_level:
  assumes x: "1 < x" and gt: "(if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>) < y"
  shows "1 - GPD_cdf \<gamma> 0 1 y < 1 / x"
proof -
  have x1: "1 \<le> x"
    using x by simp
  note L0 = GPD_level_nonneg[OF x1]
  have supp: "0 < 1 + \<gamma> * (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
    using GPD_level_supp[OF x1, of \<gamma>] x by (cases "\<gamma> = 0") auto
  have "1 - GPD_cdf \<gamma> 0 1 y < 1 - GPD_cdf \<gamma> 0 1 ((if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>))"
    by (intro GPD_tail_strict_antimono L0 gt supp)
  thus ?thesis
    using GPD_tail_level[OF x1, of \<gamma>] by simp
qed
lemma endpoint_filter_eventually_at_left:
  fixes F :: "real \<Rightarrow> real"
  assumes ev: "eventually P (endpoint_filter F)"
  shows "\<forall>\<^sub>F t in endpoint_filter F. eventually P (at_left t)"
proof (cases "bdd_support F")
  case True
  hence eq: "endpoint_filter F = at_left (x_star F)"
    by (simp add: endpoint_filter)
  obtain c where c: "c < x_star F"
    and P: "\<And>z. c < z \<Longrightarrow> z < x_star F \<Longrightarrow> P z"
    by (metis assms eq eventually_at_left_field)
  show ?thesis
    unfolding eq
  proof (rule eventually_at_leftI[where a = c])
    fix t :: real
    assume "t \<in> {c<..<x_star F}"
    hence t: "c < t" "t < x_star F"
      by auto
    show "eventually P (at_left t)"
    proof (rule eventually_at_leftI[where a = c])
      fix z :: real
      assume "z \<in> {c<..<t}"
      thus "P z"
        using t by (auto intro!: P)
    next
      show "c < t"
        using t by simp
    qed
  next
    show "c < x_star F"
      by (rule c)
  qed
next
  case False
  hence eq: "endpoint_filter F = at_top"
    by (simp add: endpoint_filter)
  obtain d where d: "\<And>z. d \<le> z \<Longrightarrow> P z"
    using ev[unfolded eq] by (auto simp: eventually_at_top_linorder)
  show ?thesis
    unfolding eq
  proof (rule eventually_at_top_linorderI[where c = "d + 1"])
    fix t :: real
    assume t: "d + 1 \<le> t"
    show "eventually P (at_left t)"
    proof (rule eventually_at_leftI[where a = d])
      fix z :: real
      assume "z \<in> {d<..<t}"
      thus "P z"
        by (auto intro!: d)
    next
      show "d < t"
        using t by simp
    qed
  qed
qed

lemma excess_uniform_scaled_iff:
  fixes F :: "real \<Rightarrow> real" and \<beta> :: "real \<Rightarrow> real" and FF :: "real filter"
  assumes \<beta>pos: "\<And>u. 0 < \<beta> u"
  shows "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0) FF
         \<longleftrightarrow> uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1) FF"
proof
  assume ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0) FF"
  show "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1) FF"
  proof (rule uniform_limitI)
    fix \<epsilon> :: real
    assume \<epsilon>: "0 < \<epsilon>"
    show "\<forall>\<^sub>F u in FF. \<forall>y\<in>{0..}. dist (excess_cdf F u (\<beta> u * y)) (GPD_cdf \<gamma> 0 1 y) < \<epsilon>"
    proof(safe intro!: eventually_mono[OF uniform_limitD[OF ul \<epsilon>]])
      fix u y :: real
      assume h:"\<forall>z\<in>{0..}. dist (excess_cdf F u z - GPD_cdf \<gamma> 0 (\<beta> u) z) 0 < \<epsilon>"
        and y:"0 \<le> y"
      have mem: "\<beta> u * y \<in> {0..}"
        using \<beta>pos[of u] y by simp
      have target: "GPD_cdf \<gamma> 0 (\<beta> u) (\<beta> u * y) = GPD_cdf \<gamma> 0 1 y"
        using GPD_cdf_location_scale[OF \<beta>pos[of u], of \<gamma> "\<beta> u * y"] \<beta>pos[of u] by simp
      have "\<bar>excess_cdf F u (\<beta> u * y) - GPD_cdf \<gamma> 0 (\<beta> u) (\<beta> u * y)\<bar> < \<epsilon>"
        using h mem by (simp add: dist_real_def)
      thus "dist (excess_cdf F u (\<beta> u * y)) (GPD_cdf \<gamma> 0 1 y) < \<epsilon>"
        using target by (simp add: dist_real_def)
    qed
  qed
next
  assume ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1) FF"
  show "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0) FF"
  proof (rule uniform_limitI)
    fix \<epsilon> :: real
    assume \<epsilon>: "0 < \<epsilon>"
    show "\<forall>\<^sub>F u in FF. \<forall>x\<in>{0..}. dist (excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) 0 < \<epsilon>"
    proof(safe intro!: eventually_mono[OF uniform_limitD[OF ul \<epsilon>]])
      fix u x :: real
      assume h:"\<forall>y\<in>{0..}. dist (excess_cdf F u (\<beta> u * y)) (GPD_cdf \<gamma> 0 1 y) < \<epsilon>"
        and x:"0 \<le> x"
      hence x: "0 \<le> x"
        by simp
      have mem: "x / \<beta> u \<in> {0..}"
        using \<beta>pos[of u] x by simp
      have rescale: "excess_cdf F u (\<beta> u * (x / \<beta> u)) = excess_cdf F u x"
        using \<beta>pos[of u] by simp
      have target: "GPD_cdf \<gamma> 0 1 (x / \<beta> u) = GPD_cdf \<gamma> 0 (\<beta> u) x"
        using GPD_cdf_location_scale[OF \<beta>pos[of u], of \<gamma> x] by simp
      have "dist (excess_cdf F u (\<beta> u * (x / \<beta> u))) (GPD_cdf \<gamma> 0 1 (x / \<beta> u)) < \<epsilon>"
        using h mem by blast
      hence "\<bar>excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x\<bar> < \<epsilon>"
        using rescale target by (simp add: dist_real_def)
      thus "dist (excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) 0 < \<epsilon>"
        by (simp add: dist_real_def)
    qed
  qed
qed

lemma excess_uniform_eventually:
  fixes F :: "real \<Rightarrow> real" and \<beta> :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1"
    and ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
               (endpoint_filter F)"
    and \<delta>: "0 < \<delta>"
  shows "\<forall>\<^sub>F t in endpoint_filter F. F t < 1 \<and>
                              (\<forall>x\<ge>0. \<bar>excess_cdf F t (\<beta> t * x) - GPD_cdf \<gamma> 0 1 x\<bar> < \<delta>)"
  by(auto intro!: eventually_mono[OF eventually_conj
        [OF F_lt_1_endpoint[OF F] uniform_limitD[OF ul \<delta>]]] simp: dist_real_def)

lemma excess_iterate_tail_small:
  fixes F :: "real \<Rightarrow> real" and \<beta> :: "real \<Rightarrow> real"
  assumes \<beta>pos: "\<And>u. 0 < \<beta> u"
    and Y0: "0 < Y0" and KY0: "1 / 2 \<le> GPD_cdf \<gamma> 0 1 Y0"
    and cT: "c < T"
    and lt1: "\<And>z. c < z \<Longrightarrow> z < T \<Longrightarrow> F z < 1"
    and near: "\<And>z. c < z \<Longrightarrow> z < T \<Longrightarrow>
                 \<bar>excess_cdf F z (\<beta> z * Y0) - GPD_cdf \<gamma> 0 1 Y0\<bar> < 1 / 4"
    and step: "\<And>z. c < z \<Longrightarrow> z < T \<Longrightarrow> z + \<beta> z * Y0 < T"
    and \<delta>: "0 < \<delta>"
  shows "\<exists>z. c < z \<and> z < T \<and> 1 - F z < \<delta>"
proof -
  define w :: "nat \<Rightarrow> real" where "w = rec_nat ((c + T) / 2) (\<lambda>n wn. wn + \<beta> wn * Y0)"
  have w0: "w 0 = (c + T) / 2"
    by (simp add: w_def)
  have wSuc: "w (Suc n) = w n + \<beta> (w n) * Y0" for n
    by (simp add: w_def)
  have inv: "c < w n \<and> w n < T" for n
  proof (induction n)
    case 0
    thus ?case
      using cT by (simp add: w0)
  next
    case (Suc n)
    have bY: "0 < \<beta> (w n) * Y0"
      using \<beta>pos[of "w n"] Y0 by simp
    have lo: "c < w n + \<beta> (w n) * Y0"
      using Suc[THEN conjunct1] bY by linarith
    have hi: "w n + \<beta> (w n) * Y0 < T"
      using Suc by (intro step) auto
    show ?case
      using lo hi by (simp add: wSuc)
  qed
  have wlo: "c < w n" and whi: "w n < T" for n
    using inv by blast+
  have pos: "0 < 1 - F (w n)" for n
    using lt1[OF wlo whi] by simp
  have decay: "1 - F (w (Suc n)) \<le> 3 / 4 * (1 - F (w n))" for n
  proof -
    have "\<bar>excess_cdf F (w n) (\<beta> (w n) * Y0) - GPD_cdf \<gamma> 0 1 Y0\<bar> < 1 / 4"
      by (intro near wlo whi)
    hence e: "1 - excess_cdf F (w n) (\<beta> (w n) * Y0) \<le> 3 / 4"
      using KY0 by linarith
    have "1 - F (w n + \<beta> (w n) * Y0)
            = (1 - excess_cdf F (w n) (\<beta> (w n) * Y0)) * (1 - F (w n))"
      using lt1[OF wlo whi, of n] by (simp add: excess_cdf_def)
    also have "... \<le> 3 / 4 * (1 - F (w n))"
      using e pos[of n] by (intro mult_right_mono) auto
    finally show ?thesis
      by (simp add: wSuc)
  qed
  have geom: "1 - F (w n) \<le> (3 / 4) ^ n * (1 - F (w 0))" for n
  proof (induction n)
    case 0
    thus ?case
      by simp
  next
    case (Suc n)
    have "1 - F (w (Suc n)) \<le> 3 / 4 * (1 - F (w n))"
      by (rule decay)
    also have "... \<le> 3 / 4 * ((3 / 4) ^ n * (1 - F (w 0)))"
      using Suc by simp
    finally show ?case
      by simp
  qed
  have pow0: "(\<lambda>n. (3 / 4:: real) ^ n) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_realpow_zero) auto
  have "(\<lambda>n. (3 / 4:: real) ^ n * (1 - F (w 0))) \<longlonglongrightarrow> 0"
    using tendsto_mult[OF pow0 tendsto_const[of "1 - F (w 0)"]] by simp
  from order_tendstoD(2)[OF this \<delta>] obtain n
    where "(3 / 4 :: real) ^ n * (1 - F (w 0)) < \<delta>"
    by (auto simp: eventually_sequentially)
  hence "1 - F (w n) < \<delta>"
    using geom[of n] by simp
  thus ?thesis
    using wlo whi by blast
qed

lemma excess_tail_small_below_x_star:
  fixes F :: "real \<Rightarrow> real" and \<beta> :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and \<beta>pos: "\<And>u. 0 < \<beta> u"
    and ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
               (endpoint_filter F)"
    and bdd: "bdd_support F" and \<delta>: "0 < \<delta>"
  shows "\<exists>z. z < x_star F \<and> 1 - F z < \<delta>"
proof -
  define Y0 where "Y0 = (if \<gamma> = 0 then ln 2 else (2 powr \<gamma> - 1) / \<gamma>)"
  have Y0pos: "0 < Y0"
    unfolding Y0_def by (intro GPD_level_pos) simp
  have KY0: "GPD_cdf \<gamma> 0 1 Y0 = 1 / 2"
    unfolding Y0_def using GPD_tail_level[of 2 \<gamma>] by simp
  have eq: "endpoint_filter F = at_left (x_star F)"
    using bdd by (simp add: endpoint_filter)
  have "\<exists>c<x_star F. \<forall>z>c. z < x_star F \<longrightarrow>
          F z < 1 \<and> (\<forall>x\<ge>0. \<bar>excess_cdf F z (\<beta> z * x) - GPD_cdf \<gamma> 0 1 x\<bar> < 1 / 4)"
    using excess_uniform_eventually[OF F ul, of "1 / 4"]
    unfolding eq eventually_at_left_field by simp
  then obtain c where c: "c < x_star F"
    and P: "\<And>z. c < z \<Longrightarrow> z < x_star F \<Longrightarrow>
             F z < 1 \<and> (\<forall>x\<ge>0. \<bar>excess_cdf F z (\<beta> z * x) - GPD_cdf \<gamma> 0 1 x\<bar> < 1 / 4)"
    by blast
  have near: "\<bar>excess_cdf F z (\<beta> z * Y0) - GPD_cdf \<gamma> 0 1 Y0\<bar> < 1 / 4"
    if z: "c < z" "z < x_star F" for z
    using P[OF z] Y0pos by simp
  have step: "z + \<beta> z * Y0 < x_star F" if z: "c < z" "z < x_star F" for z
  proof (rule ccontr)
    assume "\<not> z + \<beta> z * Y0 < x_star F"
    hence ge: "x_star F \<le> z + \<beta> z * Y0"
      by simp
    have "excess_cdf F z (\<beta> z * Y0) = 1"
      by (rule excess_cdf_eq_1_beyond_support[OF F bdd ge])
    hence "(1::real) / 2 < 1 / 4"
      using near[OF z] KY0 by simp
    thus False
      by simp
  qed
  have "\<exists>z. c < z \<and> z < x_star F \<and> 1 - F z < \<delta>"
  proof (rule excess_iterate_tail_small[OF \<beta>pos Y0pos])
    show "1 / 2 \<le> GPD_cdf \<gamma> 0 1 Y0"
      by (simp add: KY0)
    show "c < x_star F"
      by (rule c)
    show "\<And>z. c < z \<Longrightarrow> z < x_star F \<Longrightarrow> F z < 1"
      using P by blast
    show "\<And>z. c < z \<Longrightarrow> z < x_star F \<Longrightarrow> \<bar>excess_cdf F z (\<beta> z * Y0) - GPD_cdf \<gamma> 0 1 Y0\<bar> < 1 / 4"
      by (rule near)
    show "\<And>z. c < z \<Longrightarrow> z < x_star F \<Longrightarrow> z + \<beta> z * Y0 < x_star F"
      by (rule step)
    show "0 < \<delta>"
      by (rule \<delta>)
  qed
  thus ?thesis
    by blast
qed

lemma F_tendsto_1_endpoint_of_excess:
  fixes F :: "real \<Rightarrow> real" and \<beta> :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and \<beta>pos: "\<And>u. 0 < \<beta> u"
    and ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
               (endpoint_filter F)"
  shows "(F \<longlongrightarrow> 1) (endpoint_filter F)"
proof (cases "bdd_support F")
  case False
  thus ?thesis
    using right_continuous_mono.top[OF F] by (simp add: endpoint_filter)
next
  case bdd: True
  interpret right_continuous_mono F 0 1
    by fact
  show ?thesis
    unfolding endpoint_filter(1)[OF bdd] order_tendsto_iff
  proof safe
    fix a :: real
    assume a: "a < 1"
    obtain z where z: "z < x_star F" "1 - F z < 1 - a"
      using excess_tail_small_below_x_star[OF F \<beta>pos ul bdd, of "1 - a"] a by auto
    show "\<forall>\<^sub>F t in at_left (x_star F). a < F t"
    proof (intro eventually_at_leftI[OF _ z(1)])
      fix t
      assume "t \<in> {z<..<x_star F}"
      hence "F z \<le> F t"
        by (intro monoD[OF mono]) simp
      thus "a < F t"
        using z(2) by simp
    qed
  next
    fix a :: real
    assume "1 < a"
    thus "\<forall>\<^sub>F t in at_left (x_star F). F t < a"
      using f_le_b[THEN order_le_less_trans]
      by (auto intro!: eventually_at_leftI[of "x_star F - 1"])
  qed
qed

lemma tail_quantile_asymp_inverse_of_excess:
  fixes F :: "real \<Rightarrow> real" and \<beta> :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and \<beta>pos: "\<And>u. 0 < \<beta> u"
    and ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
               (endpoint_filter F)"
  shows "((\<lambda>s. s * (1 - F (tail_quantile F s))) \<longlongrightarrow> 1) at_top"
proof -
  define Y0 where "Y0 = (if \<gamma> = 0 then ln 2 else (2 powr \<gamma> - 1) / \<gamma>)"
  have Y0pos: "0 < Y0"
    unfolding Y0_def by (intro GPD_level_pos) simp
  have KY0: "GPD_cdf \<gamma> 0 1 Y0 = 1 / 2"
    unfolding Y0_def using GPD_tail_level[of 2 \<gamma>] by simp
  note Flim = F_tendsto_1_endpoint_of_excess[OF F \<beta>pos ul]
  note Uendpoint = tail_quantile_tendsto_endpoint[OF F Flim]
  show ?thesis
    unfolding tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    define \<delta> where "\<delta> = min (e / 16) (1 / 8)"
    define \<eta> where "\<eta> = min (e / 8) (1 / 8)"
    have \<delta>pos: "0 < \<delta>" and \<delta>le: "\<delta> \<le> 1 / 8" and \<delta>e: "\<delta> \<le> e / 16"
      using e by (simp_all add: \<delta>_def)
    have \<eta>pos: "0 < \<eta>" and \<eta>le: "\<eta> \<le> 1 / 8" and \<eta>e: "\<eta> \<le> e / 8"
      using e by (simp_all add: \<eta>_def)
    define Q where
      "Q = (\<lambda>z. F z < 1 \<and> (\<forall>x\<ge>0. \<bar>excess_cdf F z (\<beta> z * x) - GPD_cdf \<gamma> 0 1 x\<bar> < \<delta>))"
    have evP: "\<forall>\<^sub>F t in endpoint_filter F. eventually Q (at_left t)"
      unfolding Q_def
      by (intro endpoint_filter_eventually_at_left excess_uniform_eventually[OF F ul \<delta>pos])
    note evU = eventually_compose_filterlim[OF evP Uendpoint]
    show "\<forall>\<^sub>F s in at_top. \<bar>s * (1 - F (tail_quantile F s)) - 1\<bar> < e"
      using evU eventually_gt_at_top[of 1]
    proof eventually_elim
      case (elim s)
      define t0 where "t0 = tail_quantile F s"
      have s1: "1 < s"
        using elim(2) .
      have spos: "0 < s"
        using s1 by simp
      have fA: "1 - F t0 \<le> 1 / s"
        using lt_tail_quantile_iff[OF F s1, of t0] by (simp add: t0_def)
      have fB: "1 / s < 1 - F w" if "w < t0" for w
        using lt_tail_quantile_iff[OF F s1] that by (simp add: t0_def)
      obtain c where c: "c < t0" and Q: "\<And>z. c < z \<Longrightarrow> z < t0 \<Longrightarrow> Q z"
        using elim(1) eventually_at_left_field t0_def by blast
      have Qlt1: "F z < 1" if "c < z" "z < t0" for z
        using Q[OF that] by (simp add: Q_def)
      have Qnear: "\<bar>excess_cdf F z (\<beta> z * x) - GPD_cdf \<gamma> 0 1 x\<bar> < \<delta>"
        if z: "c < z" "z < t0" and x: "0 \<le> x" for z x
        using Q[OF z] x by (simp add: Q_def)
      have "\<exists>z. c < z \<and> z < t0 \<and> t0 \<le> z + \<beta> z * Y0"
      proof (rule ccontr)
        assume "\<not> (\<exists>z. c < z \<and> z < t0 \<and> t0 \<le> z + \<beta> z * Y0)"
        hence step: "\<And>z. c < z \<Longrightarrow> z < t0 \<Longrightarrow> z + \<beta> z * Y0 < t0"
          by (auto simp: not_le)
        have "\<exists>z. c < z \<and> z < t0 \<and> 1 - F z < 1 / s"
        proof (rule excess_iterate_tail_small[OF \<beta>pos Y0pos])
          show "\<bar>excess_cdf F z' (\<beta> z' * Y0) - GPD_cdf \<gamma> 0 1 Y0\<bar> < 1 / 4"
            if "c < z'" "z' < t0" for z'
            using Qnear[OF that less_imp_le[OF Y0pos]] \<delta>le by simp
        qed(simp_all add: KY0 c Qlt1 step spos)
        then obtain z where z: "c < z" "z < t0" "1 - F z < 1 / s"
          by blast
        show False
          using fB[OF z(2)] z(3) by simp
      qed
      then obtain z where z: "c < z" "z < t0" and zA: "t0 \<le> z + \<beta> z * Y0"
        by blast
      define y0 where "y0 = (t0 - z) / \<beta> z"
      have \<beta>z: "0 < \<beta> z"
        by (rule \<beta>pos)
      have y0pos: "0 < y0"
        using z(2) \<beta>z by (simp add: y0_def)
      have y0_le: "y0 \<le> Y0"
        using zA \<beta>z by (simp add: y0_def field_simps)
      have y0_eq: "z + \<beta> z * y0 = t0"
        using \<beta>z by (simp add: y0_def)
      define B where "B = 1 - GPD_cdf \<gamma> 0 1 y0"
      have Bge: "1 / 2 \<le> B"
        using monoD[OF right_continuous_mono.mono[OF right_continuous_mono_GPD_cdf[of 1]]
            y0_le,of \<gamma> 0] KY0
        by(simp add: B_def)
      have Bpos: "0 < B"
        using Bge by simp
      have Fzpos: "0 < 1 - F z"
        using Qlt1[OF z(1,2)] by simp
      have factor: "1 - F (z + h) = (1 - excess_cdf F z h) * (1 - F z)" for h
        using Qlt1[OF z(1,2)] by (simp add: excess_cdf_def)
      have lower1: "(B - \<delta>) * (1 - F z) < 1 - F t0"
      proof -
        have "\<bar>excess_cdf F z (\<beta> z * y0) - GPD_cdf \<gamma> 0 1 y0\<bar> < \<delta>"
          using Qnear[OF z(1,2) less_imp_le[OF y0pos]] .
        hence "B - \<delta> < 1 - excess_cdf F z (\<beta> z * y0)"
          by (simp add: B_def)
        moreover have "1 - F t0 = (1 - excess_cdf F z (\<beta> z * y0)) * (1 - F z)"
          using factor[of "\<beta> z * y0"] y0_eq by simp
        ultimately show ?thesis
          using Fzpos by (simp add: mult_strict_right_mono)
      qed
      have upper1: "1 / s < (B + \<eta> + \<delta>) * (1 - F z)"
      proof -
        have cont: "isCont (GPD_cdf \<gamma> 0 1) y0"
          by (intro isCont_GPD_cdf zero_less_one)
        obtain \<rho> where \<rho>: "0 < \<rho>"
          and \<rho>near0: "\<And>y. y \<noteq> y0 \<Longrightarrow> \<bar>y - y0\<bar> < \<rho> \<Longrightarrow>
                          \<bar>GPD_cdf \<gamma> 0 1 y - GPD_cdf \<gamma> 0 1 y0\<bar> < \<eta>"
          using LIM_D[OF cont[unfolded isCont_def] \<eta>pos] by auto
        have \<rho>near: "\<bar>GPD_cdf \<gamma> 0 1 y - GPD_cdf \<gamma> 0 1 y0\<bar> < \<eta>" if "\<bar>y - y0\<bar> < \<rho>" for y
          using \<rho>near0[of y] that \<eta>pos by (cases "y = y0") auto
        define \<theta> where "\<theta> = min (\<beta> z * \<rho> / 2) ((t0 - z) / 2)"
        have \<theta>pos: "0 < \<theta>"
          using \<beta>z \<rho> z(2) by (simp add: \<theta>_def)
        have \<theta>1: "\<theta> \<le> \<beta> z * \<rho> / 2"
          unfolding \<theta>_def by (rule min.cobounded1)
        have \<theta>2: "\<theta> \<le> (t0 - z) / 2"
          unfolding \<theta>_def by (rule min.cobounded2)
        define w where "w = t0 - \<theta>"
        have wlt: "w < t0"
          using \<theta>pos by (simp add: w_def)
        have wgt: "z < w"
          using \<theta>2 z(2) by (simp add: w_def)
        define yw where "yw = (w - z) / \<beta> z"
        have yw_eq: "z + \<beta> z * yw = w"
          using \<beta>z by (simp add: yw_def)
        have yw0: "0 \<le> yw"
          using wgt \<beta>z by (simp add: yw_def)
        have yw_diff: "yw - y0 = - (\<theta> / \<beta> z)"
          using \<beta>z by (simp add: yw_def y0_def w_def field_simps)
        have "\<bar>yw - y0\<bar> < \<rho>"
          using \<theta>1 \<beta>z \<rho> \<theta>pos by (simp add: yw_diff field_simps)
        hence "\<bar>GPD_cdf \<gamma> 0 1 yw - GPD_cdf \<gamma> 0 1 y0\<bar> < \<eta>"
          by (rule \<rho>near)
        hence Byw: "1 - GPD_cdf \<gamma> 0 1 yw < B + \<eta>"
          by (simp add: B_def)
        have "\<bar>excess_cdf F z (\<beta> z * yw) - GPD_cdf \<gamma> 0 1 yw\<bar> < \<delta>"
          using Qnear[OF z(1,2) yw0] .
        hence "1 - excess_cdf F z (\<beta> z * yw) < B + \<eta> + \<delta>"
          using Byw by simp
        moreover have "1 - F w = (1 - excess_cdf F z (\<beta> z * yw)) * (1 - F z)"
          using factor[of "\<beta> z * yw"] yw_eq by simp
        ultimately have "1 - F w < (B + \<eta> + \<delta>) * (1 - F z)"
          using Fzpos by (simp add: mult_strict_right_mono)
        thus ?thesis
          using fB[OF wlt] by simp
      qed
      have Bden: "0 < B + \<eta> + \<delta>"
        using Bpos \<eta>pos \<delta>pos by simp
      have Bnum: "0 < B - \<delta>"
        using Bge \<delta>le by simp
      have "(B - \<delta>) / (B + \<eta> + \<delta>) < s * (1 - F t0)"
      proof -
        have "1 / s < (B + \<eta> + \<delta>) * (1 - F z)"
          by (rule upper1)
        hence "(B - \<delta>) * (1 / s) < (B - \<delta>) * ((B + \<eta> + \<delta>) * (1 - F z))"
          using Bnum by (intro mult_strict_left_mono) auto
        also have "... = (B + \<eta> + \<delta>) * ((B - \<delta>) * (1 - F z))"
          by (simp add: algebra_simps)
        also have "... < (B + \<eta> + \<delta>) * (1 - F t0)"
          using lower1 Bden by (simp add: mult_strict_left_mono)
        finally have "(B - \<delta>) * (1 / s) < (B + \<eta> + \<delta>) * (1 - F t0)" .
        hence "(B - \<delta>) / (B + \<eta> + \<delta>) < s * (1 - F t0)"
          using Bden spos by (simp add: field_simps)
        thus ?thesis .
      qed
      moreover have "1 - 2 * (\<eta> + 2 * \<delta>) \<le> (B - \<delta>) / (B + \<eta> + \<delta>)"
      proof -
        have "(B - \<delta>) / (B + \<eta> + \<delta>) = 1 - (\<eta> + 2 * \<delta>) / (B + \<eta> + \<delta>)"
          using Bden by (simp add: field_simps)
        moreover have "(\<eta> + 2 * \<delta>) / (B + \<eta> + \<delta>) \<le> 2 * (\<eta> + 2 * \<delta>)"
        proof -
          have "1 / 2 \<le> B + \<eta> + \<delta>"
            using Bge \<eta>pos \<delta>pos by simp
          hence "(\<eta> + 2 * \<delta>) / (B + \<eta> + \<delta>) \<le> (\<eta> + 2 * \<delta>) / (1 / 2)"
            using \<eta>pos \<delta>pos Bden by (intro divide_left_mono) auto
          thus ?thesis
            by simp
        qed
        ultimately show ?thesis
          by simp
      qed
      moreover have "s * (1 - F t0) \<le> 1"
        using fA spos by (simp add: field_simps)
      ultimately show ?case
        using \<eta>e \<delta>e e by (simp add: t0_def abs_real_def)
    qed
  qed
qed

lemma tail_quantile_gap_of_excess:
  fixes F :: "real \<Rightarrow> real" and \<beta> :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and \<beta>pos: "\<And>u. 0 < \<beta> u"
    and ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
               (endpoint_filter F)"
    and x: "1 < x"
  shows "((\<lambda>s. (tail_quantile F (s * x) - tail_quantile F s) / \<beta> (tail_quantile F s))
            \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
proof -
  note Flim = F_tendsto_1_endpoint_of_excess[OF F \<beta>pos ul]
  note Uendpoint = tail_quantile_tendsto_endpoint[OF F Flim]
  note P1 = tail_quantile_asymp_inverse_of_excess[OF F \<beta>pos ul]
  have xpos: "0 < x"
    using x by simp
  define q where "q = 1 / x"
  have qpos: "0 < q"
    using xpos by (simp add: q_def)
  show ?thesis
    unfolding tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    define L where "L = (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
    have Lpos: "0 < L"
      unfolding L_def by (intro GPD_level_pos x)
    define \<epsilon> where "\<epsilon> = min (e / 2) (L / 2)"
    have \<epsilon>pos: "0 < \<epsilon>" and \<epsilon>e: "\<epsilon> < e" and \<epsilon>L: "\<epsilon> < L"
      using e Lpos by (simp_all add: \<epsilon>_def)
    define ym yp where "ym = L - \<epsilon>" and "yp = L + \<epsilon>"
    have ym0: "0 < ym"
      using \<epsilon>L by (simp add: ym_def)
    have ymL: "ym < L"
      using \<epsilon>pos by (simp add: ym_def)
    have Lyp: "L < yp"
      using \<epsilon>pos by (simp add: yp_def)
    define Km Kp where "Km = 1 - GPD_cdf \<gamma> 0 1 ym" and "Kp = 1 - GPD_cdf \<gamma> 0 1 yp"
    have Km_gt: "q < Km"
      unfolding Km_def q_def
      using ym0 ymL by (intro GPD_tail_gt_level[OF x]) (auto simp: L_def)
    have Kp_lt: "Kp < q"
      unfolding Kp_def q_def
      using Lyp by (intro GPD_tail_lt_level[OF x]) (simp add: L_def)
    have Kp0: "0 \<le> Kp"
      using GPD_cdf_le_1
      unfolding Kp_def by simp
    define \<delta> where "\<delta> = min ((q - Kp) / 2) ((Km - q) / 2)"
    have \<delta>1: "\<delta> \<le> (q - Kp) / 2"
      unfolding \<delta>_def by (rule min.cobounded1)
    have \<delta>2: "\<delta> \<le> (Km - q) / 2"
      unfolding \<delta>_def by (rule min.cobounded2)
    have \<delta>pos: "0 < \<delta>"
      using Kp_lt Km_gt by (simp add: \<delta>_def)
    have Kp\<delta>: "Kp + \<delta> \<le> q"
    proof -
      have "2 * (Kp + \<delta>) \<le> 2 * Kp + (q - Kp)"
        using \<delta>1 by simp
      also have "... \<le> 2 * q"
        using Kp_lt by simp
      finally show ?thesis
        by simp
    qed
    have Km\<delta>: "q < Km - \<delta>"
    proof -
      have "2 * \<delta> \<le> Km - q"
        using \<delta>2 by simp
      hence "2 * q < 2 * (Km - \<delta>)"
        using Km_gt by simp
      thus ?thesis
        by simp
    qed
    have Km\<delta>pos: "0 < Km - \<delta>"
      using Km\<delta> qpos by linarith
    define r where "r = q / (Km - \<delta>)"
    have r_lt1: "r < 1"
      unfolding r_def using Km\<delta> Km\<delta>pos by simp
    define \<zeta> where "\<zeta> = (1 - r) / 2"
    have \<zeta>pos: "0 < \<zeta>"
      using r_lt1 by (simp add: \<zeta>_def)
    have r\<zeta>: "r < 1 - \<zeta>"
    proof -
      have "1 - \<zeta> = (1 + r) / 2"
        by (simp add: \<zeta>_def field_simps)
      moreover have "r < (1 + r) / 2"
        using r_lt1 by simp
      ultimately show ?thesis
        by simp
    qed
    have key: "q < (Km - \<delta>) * (1 - \<zeta>)"
    proof -
      have "(Km - \<delta>) * r = q"
        using Km\<delta>pos by (simp add: r_def)
      moreover have "(Km - \<delta>) * r < (Km - \<delta>) * (1 - \<zeta>)"
        using r\<zeta> Km\<delta>pos by (intro mult_strict_left_mono) auto
      ultimately show ?thesis
        by simp
    qed
    define Q where
      "Q = (\<lambda>t. F t < 1 \<and> (\<forall>y\<ge>0. \<bar>excess_cdf F t (\<beta> t * y) - GPD_cdf \<gamma> 0 1 y\<bar> < \<delta>))"
    have evQ: "\<forall>\<^sub>F s in at_top. Q (tail_quantile F s)"
      unfolding Q_def
      by (intro eventually_compose_filterlim[OF excess_uniform_eventually[OF F ul \<delta>pos]]
          Uendpoint)
    have evP1: "\<forall>\<^sub>F s in at_top. 1 - \<zeta> < s * (1 - F (tail_quantile F s))"
      using order_tendstoD(1)[OF P1, of "1 - \<zeta>"] \<zeta>pos by simp
    have evx: "\<forall>\<^sub>F s::real in at_top. 1 < s * x"
      using x by real_asymp
    show "\<forall>\<^sub>F s in at_top. \<bar>(tail_quantile F (s * x) - tail_quantile F s)
                                   / \<beta> (tail_quantile F s)
                                 - (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)\<bar> < e"
      using evQ evP1 evx eventually_gt_at_top[of 1]
    proof eventually_elim
      case (elim s)
      define t0 where "t0 = tail_quantile F s"
      have s1: "1 < s" and sx1: "1 < s * x"
        using elim(3,4) by simp_all
      have spos: "0 < s"
        using s1 by simp
      have qs: "q / s = 1 / (s * x)"
        using xpos spos by (simp add: q_def field_simps)
      have \<beta>t: "0 < \<beta> t0"
        by (rule \<beta>pos)
      have Ft0: "F t0 < 1"
        using elim(1) by (simp add: Q_def t0_def)
      have Ft0pos: "0 < 1 - F t0"
        using Ft0 by simp
      have near: "\<bar>excess_cdf F t0 (\<beta> t0 * y) - GPD_cdf \<gamma> 0 1 y\<bar> < \<delta>" if "0 \<le> y" for y
        using elim(1) that by (simp add: Q_def t0_def)
      have factor: "1 - F (t0 + h) = (1 - excess_cdf F t0 h) * (1 - F t0)" for h
        using Ft0 by (simp add: excess_cdf_def)
      have upper_tail: "1 - F t0 \<le> 1 / s"
        using lt_tail_quantile_iff[OF F s1, of "tail_quantile F s"] by (simp add: t0_def)
      have lower_tail: "1 - \<zeta> < s * (1 - F t0)"
        using elim(2) by (simp add: t0_def)
      have p_bounds: "0 < 1 - 1 / (s * x)" "1 - 1 / (s * x) < 1"
        using sx1 by simp_all
      have Uup: "tail_quantile F (s * x) \<le> t0 + \<beta> t0 * yp"
      proof -
        have "\<bar>excess_cdf F t0 (\<beta> t0 * yp) - GPD_cdf \<gamma> 0 1 yp\<bar> < \<delta>"
          using ym0 \<epsilon>pos by (intro near) (simp add: yp_def ym_def)
        hence "1 - excess_cdf F t0 (\<beta> t0 * yp) < Kp + \<delta>"
          by (simp add: Kp_def)
        hence step1: "1 - F (t0 + \<beta> t0 * yp) < (Kp + \<delta>) * (1 - F t0)"
          using Ft0pos factor[of "\<beta> t0 * yp"] by (simp add: mult_strict_right_mono)
        have step2: "(Kp + \<delta>) * (1 - F t0) \<le> q * (1 / s)"
          using Kp\<delta> upper_tail Ft0pos qpos by (intro mult_mono) auto
        have step3: "q * (1 / s) = 1 / (s * x)"
          using qs by simp
        have "1 - F (t0 + \<beta> t0 * yp) \<le> 1 / (s * x)"
          using step1 step2 step3 by simp
        hence "1 - 1 / (s * x) \<le> F (t0 + \<beta> t0 * yp)"
          by simp
        thus ?thesis
          using right_continuous_mono.ginv_le_iff[OF F p_bounds, of "t0 + \<beta> t0 * yp"] by simp
      qed
      have Ulo: "t0 + \<beta> t0 * ym < tail_quantile F (s * x)"
      proof -
        have "\<bar>excess_cdf F t0 (\<beta> t0 * ym) - GPD_cdf \<gamma> 0 1 ym\<bar> < \<delta>"
          using ym0 by (intro near) simp
        hence "Km - \<delta> < 1 - excess_cdf F t0 (\<beta> t0 * ym)"
          by (simp add: Km_def)
        hence "(Km - \<delta>) * (1 - F t0) < 1 - F (t0 + \<beta> t0 * ym)"
          using Ft0pos factor[of "\<beta> t0 * ym"] by (simp add: mult_strict_right_mono)
        hence "s * ((Km - \<delta>) * (1 - F t0)) < s * (1 - F (t0 + \<beta> t0 * ym))"
          using spos by (intro mult_strict_left_mono) auto
        moreover have "q < s * ((Km - \<delta>) * (1 - F t0))"
          using key mult_strict_left_mono[OF lower_tail Km\<delta>pos] by (simp add: algebra_simps)
        ultimately have "q < s * (1 - F (t0 + \<beta> t0 * ym))"
          by simp
        hence "q / s < 1 - F (t0 + \<beta> t0 * ym)"
          using spos by (simp add: divide_less_eq mult.commute)
        hence "1 / (s * x) < 1 - F (t0 + \<beta> t0 * ym)"
          using qs by simp
        thus ?thesis
          using right_continuous_mono.ginv_le_iff[OF F p_bounds, of "t0 + \<beta> t0 * ym"]
          by linarith
      qed
      have "ym < (tail_quantile F (s * x) - t0) / \<beta> t0"
        using Ulo \<beta>t by (simp add: field_simps)
      moreover have "(tail_quantile F (s * x) - t0) / \<beta> t0 \<le> yp"
        using Uup \<beta>t by (simp add: field_simps)
      ultimately show ?case
        using \<epsilon>e by (simp add: t0_def ym_def yp_def L_def abs_real_def)
    qed
  qed
qed

lemma GPD_level_mult:
  fixes \<gamma> y :: real
  assumes y: "0 < y"
  shows "(if \<gamma> = 0 then ln (2 * y) else ((2 * y) powr \<gamma> - 1) / \<gamma>)
           - (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)
         = y powr \<gamma> * (if \<gamma> = 0 then ln 2 else (2 powr \<gamma> - 1) / \<gamma>)"
proof (cases "\<gamma> = 0")
next
  case False
  have "(2 * y) powr \<gamma> = 2 powr \<gamma> * y powr \<gamma>"
    using y by (simp add: powr_mult)
  thus ?thesis
    using False by (simp add: field_simps)
qed(use y in "simp add: ln_mult")

lemma GPD_level_inverse:
  fixes \<gamma> x :: real
  assumes x: "0 < x"
  shows "- ((if \<gamma> = 0 then ln (1 / x) else ((1 / x) powr \<gamma> - 1) / \<gamma>) * x powr \<gamma>)
         = (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
proof (cases "\<gamma> = 0")
  case True
  thus ?thesis
    using x by (simp add: ln_div)
next
  case False
  have xpowr: "0 < x powr \<gamma>"
    using x by simp
  have "- ((if \<gamma> = 0 then ln (1 / x) else ((1 / x) powr \<gamma> - 1) / \<gamma>) * x powr \<gamma>)
          = - ((1 / x powr \<gamma> - 1) / \<gamma> * x powr \<gamma>)"
    using False by (simp add: divide_inverse inverse_powr)
  also have "... = - ((1 - x powr \<gamma>) / \<gamma>)"
    using xpowr False by (simp add: field_simps)
  also have "... = (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
    using False by (simp add: field_simps)
  finally show ?thesis .
qed

lemma tail_quantile_gap_of_excess_all:
  fixes F :: "real \<Rightarrow> real" and \<beta> :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and \<beta>pos: "\<And>u. 0 < \<beta> u"
    and ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
               (endpoint_filter F)"
    and x: "0 < x"
  shows "((\<lambda>s. (tail_quantile F (s * x) - tail_quantile F s) / \<beta> (tail_quantile F s))
            \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
proof -
  define U where "U = tail_quantile F"
  define a where "a = (\<lambda>s. \<beta> (tail_quantile F s))"
  have apos: "0 < a s" for s
    by (simp add: a_def \<beta>pos)
  have anz: "a s \<noteq> 0" for s
    using apos[of s] by simp
  have Q: "((\<lambda>s. (U (s * y) - U s) / a s)
              \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top" if "1 < y" for y
    using tail_quantile_gap_of_excess[OF F \<beta>pos ul that] by (simp add: U_def a_def)
  have L2pos: "0 < (if \<gamma> = 0 then ln 2 else (2 powr \<gamma> - 1) / \<gamma>)"
    by (intro GPD_level_pos) simp
  have shift: "filterlim (\<lambda>s::real. s * y) at_top at_top" if "0 < y" for y
    using that by real_asymp
  have RV: "((\<lambda>s. a (s * y) / a s) \<longlongrightarrow> y powr \<gamma>) at_top" if y: "1 < y" for y
  proof -
    have ypos: "0 < y"
      using y by simp
    have Q2y: "((\<lambda>s. (U (s * (2 * y)) - U s) / a s)
                  \<longlongrightarrow> (if \<gamma> = 0 then ln (2 * y) else ((2 * y) powr \<gamma> - 1) / \<gamma>)) at_top"
      using y by (intro Q) simp
    have eq: "(U (s * (2 * y)) - U s) / a s - (U (s * y) - U s) / a s
                = (U (s * y * 2) - U (s * y)) / a s" for s
    proof -
      have arg: "s * (2 * y) = s * y * 2"
        by (simp add: algebra_simps)
      have "(U (s * (2 * y)) - U s) / a s - (U (s * y) - U s) / a s
              = ((U (s * (2 * y)) - U s) - (U (s * y) - U s)) / a s"
        by (simp add: diff_divide_distrib)
      also have "... = (U (s * (2 * y)) - U (s * y)) / a s"
        by simp
      finally show ?thesis
        by (simp add: arg)
    qed
    have Ndiff: "((\<lambda>s. (U (s * y * 2) - U (s * y)) / a s)
                    \<longlongrightarrow> (if \<gamma> = 0 then ln (2 * y) else ((2 * y) powr \<gamma> - 1) / \<gamma>)
                        - (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
    proof -
      have "((\<lambda>s. (U (s * (2 * y)) - U s) / a s - (U (s * y) - U s) / a s)
              \<longlongrightarrow> (if \<gamma> = 0 then ln (2 * y) else ((2 * y) powr \<gamma> - 1) / \<gamma>)
                  - (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
        by (intro tendsto_diff Q2y Q y)
      thus ?thesis
        by (simp add: eq)
    qed
    have D: "((\<lambda>s. (U (s * y * 2) - U (s * y)) / a (s * y))
              \<longlongrightarrow> (if \<gamma> = 0 then ln 2 else (2 powr \<gamma> - 1) / \<gamma>)) at_top"
    proof -
      have "((\<lambda>r. (U (r * 2) - U r) / a r)
              \<longlongrightarrow> (if \<gamma> = 0 then ln 2 else (2 powr \<gamma> - 1) / \<gamma>)) at_top"
        by (intro Q) simp
      from filterlim_compose[OF this shift[OF ypos]] show ?thesis
        by (simp add: comp_def)
    qed
    have Dpos: "\<forall>\<^sub>F s in at_top. 0 < (U (s * y * 2) - U (s * y)) / a (s * y)"
      by (rule order_tendstoD(1)[OF D L2pos])
    have "((\<lambda>s. ((U (s * y * 2) - U (s * y)) / a s)
                  / ((U (s * y * 2) - U (s * y)) / a (s * y)))
             \<longlongrightarrow> ((if \<gamma> = 0 then ln (2 * y) else ((2 * y) powr \<gamma> - 1) / \<gamma>)
                     - (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>))
                   / (if \<gamma> = 0 then ln 2 else (2 powr \<gamma> - 1) / \<gamma>)) at_top"
      using L2pos by (intro tendsto_divide Ndiff D) simp
    moreover have "\<forall>\<^sub>F s in at_top. ((U (s * y * 2) - U (s * y)) / a s)
                              / ((U (s * y * 2) - U (s * y)) / a (s * y)) = a (s * y) / a s"
      using apos anz
      by (auto intro!: eventually_mono[OF Dpos] simp: zero_less_divide_iff field_simps)
    ultimately have "((\<lambda>s. a (s * y) / a s)
                       \<longlongrightarrow> ((if \<gamma> = 0 then ln (2 * y) else ((2 * y) powr \<gamma> - 1) / \<gamma>)
                               - (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>))
                             / (if \<gamma> = 0 then ln 2 else (2 powr \<gamma> - 1) / \<gamma>)) at_top"
      by (rule Lim_transform_eventually)
    thus ?thesis
      using GPD_level_mult[OF ypos, of \<gamma>] L2pos by simp
  qed
  have RVall: "((\<lambda>s. a (s * y) / a s) \<longlongrightarrow> y powr \<gamma>) at_top" if y: "0 < y" for y
  proof (cases "1 < y")
    case True
    thus ?thesis
      by (rule RV)
  next
    case notgt: False
    show ?thesis
    proof (cases "y = 1")
      case True
      thus ?thesis
        using anz by simp
    next
      case ne: False
      have ylt: "y < 1"
        using notgt ne by simp
      define \<mu> where "\<mu> = 1 / y"
      have \<mu>1: "1 < \<mu>"
        using y ylt by (simp add: \<mu>_def)
      have "((\<lambda>r. a (r * \<mu>) / a r) \<longlongrightarrow> \<mu> powr \<gamma>) at_top"
        by (rule RV[OF \<mu>1])
      from filterlim_compose[OF this shift[OF y]]
      have "((\<lambda>s. a (s * y * \<mu>) / a (s * y)) \<longlongrightarrow> \<mu> powr \<gamma>) at_top"
        by (simp add: comp_def)
      moreover have "s * y * \<mu> = s" for s
        using y by (simp add: \<mu>_def)
      ultimately have inv: "((\<lambda>s. a s / a (s * y)) \<longlongrightarrow> \<mu> powr \<gamma>) at_top"
        by simp
      have ypowr: "0 < y powr \<gamma>"
        using y by simp
      have \<mu>powr: "\<mu> powr \<gamma> = 1 / y powr \<gamma>"
        using y by (simp add: \<mu>_def divide_inverse inverse_powr)
      have \<mu>nz: "\<mu> powr \<gamma> \<noteq> 0"
        using \<mu>1 by simp
      from tendsto_inverse[OF inv \<mu>nz]
      have "((\<lambda>s. inverse (a s / a (s * y))) \<longlongrightarrow> inverse (\<mu> powr \<gamma>)) at_top" .
      moreover have "inverse (a s / a (s * y)) = a (s * y) / a s" for s
        by (simp add: inverse_eq_divide)
      moreover have "inverse (\<mu> powr \<gamma>) = y powr \<gamma>"
        using ypowr by (simp add: \<mu>powr)
      ultimately show ?thesis
        by simp
    qed
  qed
  have res: "((\<lambda>s. (U (s * x) - U s) / a s)
              \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
  proof (cases "1 < x")
    case True
    thus ?thesis
      by (rule Q)
  next
    case notgt: False
    show ?thesis
    proof (cases "x = 1")
      case True
      thus ?thesis
        by simp
    next
      case ne: False
      have xlt: "x < 1"
        using notgt ne by simp
      define \<mu> where "\<mu> = 1 / x"
      have \<mu>1: "1 < \<mu>"
        using x xlt by (simp add: \<mu>_def)
      have "((\<lambda>r. (U (r * \<mu>) - U r) / a r)
              \<longlongrightarrow> (if \<gamma> = 0 then ln \<mu> else (\<mu> powr \<gamma> - 1) / \<gamma>)) at_top"
        by (rule Q[OF \<mu>1])
      from filterlim_compose[OF this shift[OF x]]
      have "((\<lambda>s. (U (s * x * \<mu>) - U (s * x)) / a (s * x))
               \<longlongrightarrow> (if \<gamma> = 0 then ln \<mu> else (\<mu> powr \<gamma> - 1) / \<gamma>)) at_top"
        by (simp add: comp_def)
      moreover have "s * x * \<mu> = s" for s
        using x by (simp add: \<mu>_def)
      ultimately have A: "((\<lambda>s. (U s - U (s * x)) / a (s * x))
                            \<longlongrightarrow> (if \<gamma> = 0 then ln \<mu> else (\<mu> powr \<gamma> - 1) / \<gamma>)) at_top"
        by simp
      note B = RVall[OF x]
      from tendsto_mult[OF A B]
      have "((\<lambda>s. ((U s - U (s * x)) / a (s * x)) * (a (s * x) / a s))
               \<longlongrightarrow> (if \<gamma> = 0 then ln \<mu> else (\<mu> powr \<gamma> - 1) / \<gamma>) * x powr \<gamma>) at_top" .
      moreover have "((U s - U (s * x)) / a (s * x)) * (a (s * x) / a s)
                       = - ((U (s * x) - U s) / a s)" for s
        using anz by (simp add: field_simps)
      ultimately have "((\<lambda>s. - ((U (s * x) - U s) / a s))
                          \<longlongrightarrow> (if \<gamma> = 0 then ln \<mu> else (\<mu> powr \<gamma> - 1) / \<gamma>) * x powr \<gamma>) at_top"
        by simp
      from tendsto_minus[OF this]
      have "((\<lambda>s. (U (s * x) - U s) / a s)
               \<longlongrightarrow> - ((if \<gamma> = 0 then ln \<mu> else (\<mu> powr \<gamma> - 1) / \<gamma>) * x powr \<gamma>)) at_top"
        by simp
      moreover have "- ((if \<gamma> = 0 then ln \<mu> else (\<mu> powr \<gamma> - 1) / \<gamma>) * x powr \<gamma>)
                       = (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)"
        unfolding \<mu>_def by (rule GPD_level_inverse[OF x])
      ultimately show ?thesis
        by simp
    qed
  qed
  thus ?thesis
    by (simp add: U_def a_def)
qed

theorem Pickands_Balkema_de_Haan_converse:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and hyp: "\<exists>\<beta>. (\<forall>u. 0 < \<beta> u) \<and>
             uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x)
               (\<lambda>x. 0) (endpoint_filter F)"
  shows "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
proof -
  obtain \<beta> where \<beta>pos: "\<And>u. 0 < \<beta> u"
    and ul0: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0)
                (endpoint_filter F)"
    using hyp by blast
  have iff: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0)
               (endpoint_filter F)
             \<longleftrightarrow> uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
                 (endpoint_filter F)"
    by (intro excess_uniform_scaled_iff \<beta>pos)
  have ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
              (endpoint_filter F)"
    using iff ul0 by simp
  have "\<exists>a. (\<forall>t. 0 < a t) \<and>
            (\<forall>x>0. ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
                      \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top)"
  proof (intro exI[of _ "\<lambda>s. \<beta> (tail_quantile F s)"] conjI allI impI)
    show "\<And>t. 0 < \<beta> (tail_quantile F t)"
      by (rule \<beta>pos)
  next
    fix x :: real
    assume xpos: "0 < x"
    show "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / \<beta> (tail_quantile F t))
             \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
      by (rule tail_quantile_gap_of_excess_all[OF F \<beta>pos ul xpos])
  qed
  thus ?thesis
    using MDA_iff_tail_quantile'[OF F, of \<gamma>] by simp
qed

theorem Pickands_Balkema_de_Haan:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
  shows "domain_of_attraction F (EVD_cdf \<gamma> 0 1)
          \<longleftrightarrow> (\<exists>\<beta>. (\<forall>u. 0 < \<beta> u) \<and>
                  uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x)
                    (\<lambda>x. 0) (endpoint_filter F))"
  using Pickands_Balkema_de_Haan_forward[OF F] Pickands_Balkema_de_Haan_converse[OF F]
  by blast

subsubsection \<open>Explicit Choice of $\beta$\<close>
lemma excess_uniform_beta_cong:
  fixes F :: "real \<Rightarrow> real" and \<beta> \<beta>' :: "real \<Rightarrow> real" and FF :: "real filter"
  assumes ul: "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0) FF"
    and ev: "\<forall>\<^sub>F u in FF. \<beta>' u = \<beta> u"
  shows "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta>' u) x) (\<lambda>x. 0) FF"
proof (rule uniform_limitI)
  fix \<epsilon> :: real
  assume \<epsilon>: "0 < \<epsilon>"
  show "\<forall>\<^sub>F u in FF. \<forall>x\<in>{0..}. dist (excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta>' u) x) 0 < \<epsilon>"
    using uniform_limitD[OF ul \<epsilon>] ev by eventually_elim simp
qed

text \<open>Case: $\gamma > 0$\<close>
theorem Pickands_Balkema_de_Haan_pos:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and \<gamma>: "0 < \<gamma>"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  shows "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<gamma> * u) x) (\<lambda>x. 0)
           (endpoint_filter F)"
proof -
  have unbdd: "\<forall>x. F x < 1" and rv: "regularly_varying (\<lambda>x. 1 - F x) (- 1 / \<gamma>)"
    using MDA_regularly_varying_pos[OF F \<gamma>] dom by auto
  have nbdd: "\<not> bdd_support F"
    by (rule not_bdd_supportI') (use unbdd in simp)
  note ef = endpoint_filter(2)[OF nbdd]
  define \<beta> where "\<beta> = (\<lambda>u::real. \<gamma> * max u 1)"
  have \<beta>pos: "0 < \<beta> u" for u
    using \<gamma> by (simp add: \<beta>_def)
  have \<beta>eq: "\<forall>\<^sub>F u in at_top. \<beta> u = \<gamma> * u"
    using eventually_ge_at_top[of "1::real"] by eventually_elim (simp add: \<beta>_def)
  have pconv: "((\<lambda>u. excess_cdf F u (\<beta> u * x)) \<longlongrightarrow> GPD_cdf \<gamma> 0 1 x) at_top" if x: "0 \<le> x" for x
  proof -
    have xnn: "0 \<le> \<gamma> * x"
      using \<gamma> x by simp
    have cpos: "0 < 1 + \<gamma> * x"
      using xnn by simp
    have "((\<lambda>u. (1 - F (u * (1 + \<gamma> * x))) / (1 - F u)) \<longlongrightarrow> (1 + \<gamma> * x) powr (- 1 / \<gamma>)) at_top"
      by (rule regularly_varying_lim[OF rv cpos])
    from tendsto_diff[OF tendsto_const[of 1] this]
    have lim: "((\<lambda>u. 1 - (1 - F (u * (1 + \<gamma> * x))) / (1 - F u))
                 \<longlongrightarrow> 1 - (1 + \<gamma> * x) powr (- 1 / \<gamma>)) at_top" .
    have eq: "\<forall>\<^sub>F u in at_top. 1 - (1 - F (u * (1 + \<gamma> * x))) / (1 - F u)
                                = excess_cdf F u (\<beta> u * x)"
      using \<beta>eq by eventually_elim (simp add: excess_cdf_def field_simps)
    have m1: "- 1 \<le> \<gamma> * x"
      using xnn by simp
    have target: "GPD_cdf \<gamma> 0 1 x = 1 - (1 + \<gamma> * x) powr (- 1 / \<gamma>)"
      using x \<gamma> m1 by (simp add: GPD_cdf_def)
    show ?thesis
      using Lim_transform_eventually[OF lim eq] target by simp
  qed
  have "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1) at_top"
    by (intro excess_pointwise_imp_uniform[OF F \<beta>pos] pconv)
  hence "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0) at_top"
    using excess_uniform_scaled_iff[OF \<beta>pos] by simp
  moreover have \<beta>eq': "\<forall>\<^sub>F u in at_top. \<gamma> * u = \<beta> u"
    using \<beta>eq by eventually_elim simp
  ultimately show ?thesis
    using excess_uniform_beta_cong by (simp add: ef)
qed

text \<open>Case: $\gamma < 0$\<close>
theorem Pickands_Balkema_de_Haan_neg:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and \<gamma>: "\<gamma> < 0"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  shows "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (- \<gamma> * (x_star F - u)) x)
           (\<lambda>x. 0) (endpoint_filter F)"
proof -
  have bdd: "bdd_support F" and rv: "regularly_varying (\<lambda>s. 1 - F (x_star F - 1 / s)) (1 / \<gamma>)"
    using MDA_regularly_varying_neg[OF F \<gamma>] dom by auto
  note ef = endpoint_filter(1)[OF bdd]
  have evlt: "\<forall>\<^sub>F u in at_left (x_star F). u < x_star F"
    by (auto simp: eventually_at_filter)
  define \<beta> where "\<beta> = (\<lambda>u::real. if u < x_star F then - \<gamma> * (x_star F - u) else 1)"
  have \<beta>pos: "0 < \<beta> u" for u
    using \<gamma> by (auto simp: \<beta>_def intro!: mult_neg_pos)
  have \<beta>eq: "\<forall>\<^sub>F u in at_left (x_star F). \<beta> u = - \<gamma> * (x_star F - u)"
    using evlt by eventually_elim (simp add: \<beta>_def)
  have stop: "filterlim (\<lambda>u. 1 / (x_star F - u)) at_top (at_left (x_star F))"
  proof -
    have tend: "((\<lambda>u::real. x_star F - u) \<longlongrightarrow> 0) (at_left (x_star F))"
      by (auto intro!: tendsto_eq_intros)
    have "filterlim (\<lambda>u. inverse (x_star F - u)) at_top (at_left (x_star F))"
      by (intro filterlim_inverse_at_top[OF tend] eventually_mono[OF evlt]) simp
    thus ?thesis
      by (simp add: inverse_eq_divide)
  qed
  have pconv: "((\<lambda>u. excess_cdf F u (\<beta> u * x)) \<longlongrightarrow> GPD_cdf \<gamma> 0 1 x) (at_left (x_star F))"
    if x: "0 \<le> x" for x
  proof (cases "0 < 1 + \<gamma> * x")
    case supp: True
    hence m1: "- 1 \<le> \<gamma> * x"
      by simp
    have cpos: "0 < 1 / (1 + \<gamma> * x)"
      using supp by simp
    have "((\<lambda>s. (1 - F (x_star F - 1 / (s * (1 / (1 + \<gamma> * x)))))
                  / (1 - F (x_star F - 1 / s))) \<longlongrightarrow> (1 / (1 + \<gamma> * x)) powr (1 / \<gamma>)) at_top"
      by (rule regularly_varying_lim[OF rv cpos])
    from filterlim_compose[OF this stop]
    have lim0: "((\<lambda>u. (1 - F (x_star F - 1 / (1 / (x_star F - u) * (1 / (1 + \<gamma> * x)))))
                  / (1 - F (x_star F - 1 / (1 / (x_star F - u)))))
                  \<longlongrightarrow> (1 / (1 + \<gamma> * x)) powr (1 / \<gamma>)) (at_left (x_star F))"
      by simp
    have eq0: "\<forall>\<^sub>F u in at_left (x_star F).
        (1 - F (x_star F - 1 / (1 / (x_star F - u) * (1 / (1 + \<gamma> * x)))))
          / (1 - F (x_star F - 1 / (1 / (x_star F - u))))
        = (1 - F (u + \<beta> u * x)) / (1 - F u)"
      using evlt \<beta>eq
    proof eventually_elim
      case (elim u)
      hence gap: "0 < x_star F - u"
        by simp
      have "1 / (1 / (x_star F - u) * (1 / (1 + \<gamma> * x))) = (x_star F - u) * (1 + \<gamma> * x)"
        using gap supp by (simp add: field_simps)
      moreover have "x_star F - (x_star F - u) * (1 + \<gamma> * x) = u + \<beta> u * x"
        unfolding elim(2) by (simp add: algebra_simps)
      moreover have "x_star F - 1 / (1 / (x_star F - u)) = u"
        using gap by simp
      ultimately show ?case
        by simp
    qed
    have lim: "((\<lambda>u. (1 - F (u + \<beta> u * x)) / (1 - F u))
                 \<longlongrightarrow> (1 / (1 + \<gamma> * x)) powr (1 / \<gamma>)) (at_left (x_star F))"
      by (rule Lim_transform_eventually[OF lim0 eq0])
    have powr_eq: "(1 / (1 + \<gamma> * x)) powr (1 / \<gamma>) = (1 + \<gamma> * x) powr (- 1 / \<gamma>)"
      using supp by (simp add: powr_divide powr_minus divide_inverse inverse_powr)
    from tendsto_diff[OF tendsto_const[of 1] lim]
    have "((\<lambda>u. 1 - (1 - F (u + \<beta> u * x)) / (1 - F u))
            \<longlongrightarrow> 1 - (1 + \<gamma> * x) powr (- 1 / \<gamma>)) (at_left (x_star F))"
      by (simp add: powr_eq)
    moreover have "GPD_cdf \<gamma> 0 1 x = 1 - (1 + \<gamma> * x) powr (- 1 / \<gamma>)"
      using x \<gamma> m1 by (simp add: GPD_cdf_def)
    ultimately show ?thesis
      by (simp add: excess_cdf_def)
  next
    case False
    hence supp: "1 + \<gamma> * x \<le> 0"
      by simp
    have "\<forall>\<^sub>F u in at_left (x_star F). excess_cdf F u (\<beta> u * x) = 1"
      using evlt \<beta>eq
    proof eventually_elim
      case (elim u)
      hence gap: "0 < x_star F - u"
        by simp
      have "(x_star F - u) * (1 + \<gamma> * x) \<le> 0"
        using gap supp by (simp add: mult_nonneg_nonpos less_imp_le)
      hence "x_star F \<le> u + - \<gamma> * (x_star F - u) * x"
        by (simp add: algebra_simps)
      hence "x_star F \<le> u + \<beta> u * x"
        unfolding elim(2) by simp
      thus ?case
        by (rule excess_cdf_eq_1_beyond_support[OF F bdd])
    qed
    moreover have "GPD_cdf \<gamma> 0 1 x = 1"
      using x \<gamma> supp by (auto simp: GPD_cdf_def)
    ultimately show ?thesis
      by (simp add: tendsto_eventually)
  qed
  have "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1)
          (at_left (x_star F))"
    by (intro excess_pointwise_imp_uniform[OF F \<beta>pos] pconv)
  hence "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0)
           (at_left (x_star F))"
    using excess_uniform_scaled_iff[OF \<beta>pos] by simp
  moreover have "\<forall>\<^sub>F u in at_left (x_star F). - \<gamma> * (x_star F - u) = \<beta> u"
    using \<beta>eq by eventually_elim simp
  ultimately show ?thesis
    using excess_uniform_beta_cong by (simp add: ef)
qed


text \<open>Case: arbitrary $\gamma$\<close>
lemma isCont_GPD_level:
  fixes \<gamma> y :: real
  assumes y: "0 < y"
  shows "isCont (\<lambda>z. if \<gamma> = 0 then ln z else (z powr \<gamma> - 1) / \<gamma>) y"
  using y by (cases "\<gamma> = 0") (auto intro!: isCont_ln isCont_divide isCont_diff continuous_powr)

lemma tail_quantile_witness_of_gap:
  fixes F a :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and apos: "\<And>t. 0 < a t"
    and quant: "\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
                    \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
  shows "(\<lambda>n. F (a (real n) * x + tail_quantile F (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 x"
proof (rule MDA_tail_quantile_witness[where b = "tail_quantile F", OF F apos zero_less_one])
  fix y :: real
  assume y: "0 < y"
  show "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
          \<longlongrightarrow> (if \<gamma> = 0 then 1 * ln y + 0 else 1 * (y powr \<gamma> - 1) / \<gamma> + 0)) at_top"
    using quant[OF y] by (cases "\<gamma> = 0") simp_all
qed

lemma t_div_a_tendsto_zero_endpoint:
  fixes F a :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and apos: "\<And>t. 0 < a t"
    and quant: "\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
                    \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
  shows "((\<lambda>t. (t - tail_quantile F (1 / (1 - F t))) / a (1 / (1 - F t))) \<longlongrightarrow> 0)
           (endpoint_filter F)"
proof -
  define s where "s = (\<lambda>t::real. 1 / (1 - F t))"
  have goal_eq: "(\<lambda>t. (t - tail_quantile F (1 / (1 - F t))) / a (1 / (1 - F t)))
                   = (\<lambda>t. (t - tail_quantile F (s t)) / a (s t))"
    by (simp add: s_def)
  have stop: "filterlim s at_top (endpoint_filter F)"
    unfolding s_def
    by (rule s_tendsto_at_top_endpoint[where a = "\<lambda>n. a (real n)"
          and b = "\<lambda>n. tail_quantile F (real n)", OF F _ zero_less_one
          tail_quantile_witness_of_gap[OF F apos quant]])
       (use apos in simp)
  note Flt1 = F_lt_1_endpoint[OF F]
  have spos: "\<forall>\<^sub>F t in endpoint_filter F. 0 < s t"
    using stop[unfolded filterlim_at_top_dense, rule_format, of 0] by simp
  have conv: "((\<lambda>t. (tail_quantile F (s t * y') - tail_quantile F (s t)) / a (s t))
                 \<longlongrightarrow> (if \<gamma> = 0 then ln y' else (y' powr \<gamma> - 1) / \<gamma>))
                (endpoint_filter F)" if y': "\<bar>y' - 1\<bar> < 1" for y'
    by (rule filterlim_compose[OF quant stop]) (use y' in simp)
  have low: "\<forall>\<^sub>F t in endpoint_filter F.
               (tail_quantile F (s t * y') - tail_quantile F (s t)) / a (s t)
                 \<le> (t - tail_quantile F (s t)) / a (s t)"
    if y': "(1::real) - 1 < y'" "y' < 1" for y'
    using stop[unfolded filterlim_at_top_dense, rule_format, of "1 / y'"] spos Flt1
  proof eventually_elim
    case (elim t)
    hence s_gt: "1 / y' < s t" and s_pos: "0 < s t" and Ft: "F t < 1"
      by auto
    have u1: "1 < s t * y'"
      using mult_strict_right_mono[OF s_gt] y' by force
    have u2: "s t * y' < 1 / (1 - F t)"
      using mult_strict_left_mono[OF y'(2) s_pos] by (simp add: s_def)
    show ?case
      using apos[of "s t"] Ft u1 u2
      by (auto intro!: divide_right_mono tail_quantile_le_of_lt_inv[OF F])
  qed
  have up: "\<forall>\<^sub>F t in endpoint_filter F. (t - tail_quantile F (s t)) / a (s t)
                  \<le> (tail_quantile F (s t * y') - tail_quantile F (s t)) / a (s t)"
    if y': "(1::real) < y'" "y' < 1 + 1" for y'
    using spos Flt1
  proof eventually_elim
    case (elim t)
    hence s_pos: "0 < s t" and Ft: "F t < 1"
      by auto
    have u: "1 / (1 - F t) < s t * y'"
      using mult_strict_left_mono[OF _ s_pos] y' by (simp add: s_def)
    show ?case
      using apos[of "s t"]
      by (auto intro!: divide_right_mono
          less_imp_le[OF t_lt_tail_quantile_of_gt_inv[OF F Ft u]])
  qed
  have one: "(if \<gamma> = 0 then ln 1 else (1 powr \<gamma> - 1) / \<gamma>) = 0"
    by simp
  show ?thesis
    using squeeze_tendsto_local[OF zero_less_one isCont_GPD_level[OF zero_less_one] conv low up]
    unfolding goal_eq one .
qed

lemma divide_tail_of_gap:
  fixes F a :: "real \<Rightarrow> real" and \<gamma> x :: real
  assumes F: "right_continuous_mono F 0 1"
    and apos: "\<And>t. 0 < a t"
    and quant: "\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
                    \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
    and x: "0 < 1 + \<gamma> * x"
  shows "((\<lambda>t. (1 - F (t + x * a (1 / (1 - F t)))) / (1 - F t))
           \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F)"
proof -
  define s where "s = (\<lambda>t::real. 1 / (1 - F t))"
  define U where "U = tail_quantile F"
  have goal_eq: "(\<lambda>t. (1 - F (t + x * a (1 / (1 - F t)))) / (1 - F t))
                   = (\<lambda>t. (1 - F (t + x * a (s t))) / (1 - F t))"
    by (simp add: s_def)
  have stop: "filterlim s at_top (endpoint_filter F)"
    unfolding s_def
    by (rule s_tendsto_at_top_endpoint[where a = "\<lambda>n. a (real n)"
          and b = "\<lambda>n. tail_quantile F (real n)", OF F _ zero_less_one
          tail_quantile_witness_of_gap[OF F apos quant]])
       (use apos in simp)
  note Flt1 = F_lt_1_endpoint[OF F]
  have delta_tendsto: "((\<lambda>t. (t - U (s t)) / a (s t)) \<longlongrightarrow> 0) (endpoint_filter F)"
    using t_div_a_tendsto_zero_endpoint[OF F apos quant] by (simp add: s_def U_def)
  have op: "open {x'. 0 < 1 + \<gamma> * x'}"
    by (auto intro!: open_Collect_less continuous_on_add continuous_on_mult)
  have "\<forall>\<^sub>F x' in nhds x. x' \<in> {x'. 0 < 1 + \<gamma> * x'}"
    using x op by (intro eventually_nhds_in_open) auto
  hence ev: "\<forall>\<^sub>F x' in nhds x. 0 < 1 + \<gamma> * x'"
    by eventually_elim simp
  then obtain \<eta> where eta: "0 < \<eta>"
    and eta_supp: "\<And>x'. \<bar>x' - x\<bar> < \<eta> \<Longrightarrow> 0 < 1 + \<gamma> * x'"
    using eventually_nhds_metric[of "\<lambda>x'. 0 < 1 + \<gamma> * x'" x] by (auto simp: dist_real_def)
  have Dcont: "isCont (\<lambda>x'. ln (EVD_cdf \<gamma> 0 1 x')) x"
    using EVD_cdf_supp_bounds[OF _ zero_less_one, of \<gamma> x 0] x
    by (auto intro!: isCont_ln' isCont_EVD_cdf)
  have conv: "((\<lambda>t. - ((1 - F (a (s t) * x' + U (s t))) / (1 - F t)))
                \<longlongrightarrow> ln (EVD_cdf \<gamma> 0 1 x')) (endpoint_filter F)"
    if x': "\<bar>x' - x\<bar> < \<eta>" for x'
  proof -
    have supp': "0 < 1 + \<gamma> * x'"
      using x' eta_supp by simp
    have quant': "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
                     \<longlongrightarrow> (if \<gamma> = 0 then 1 * ln y + 0 else 1 * (y powr \<gamma> - 1) / \<gamma> + 0)) at_top"
      if y: "0 < y" for y
      using quant[OF y] by (cases "\<gamma> = 0") simp_all
    have base: "((\<lambda>t. t * (1 - F (a t * x' + U t))) \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x')) at_top"
      unfolding U_def
      by (intro MDA_tail_quantile_to_tail_probability[where b = "tail_quantile F",
            OF F apos zero_less_one quant']) (use supp' in auto)
    show ?thesis
      using tendsto_minus[OF filterlim_compose[OF base stop]] by (simp add: s_def)
  qed
  have low: "\<forall>\<^sub>F t in endpoint_filter F. - ((1 - F (a (s t) * x' + U (s t))) / (1 - F t))
                                       \<le> - ((1 - F (t + x * a (s t))) / (1 - F t))"
    if x': "x - \<eta> < x'" "x' < x" for x'
  proof -
    have dlt: "x' - x < 0"
      using x' by simp
    have ev1: "\<forall>\<^sub>F t in endpoint_filter F. x' - x < (t - U (s t)) / a (s t)"
      using order_tendstoD(1)[OF delta_tendsto dlt] .
    show ?thesis
      using ev1 Flt1
    proof eventually_elim
      case (elim t)
      hence d: "x' - x < (t - U (s t)) / a (s t)" and Ft: "F t < 1"
        by auto
      have apos': "0 < a (s t)"
        using apos by simp
      have "(x' - x) * a (s t) < ((t - U (s t)) / a (s t)) * a (s t)"
        using mult_strict_right_mono[OF d apos'] .
      also have "\<dots> = t - U (s t)"
        using apos' by simp
      finally have ineq: "(x' - x) * a (s t) < t - U (s t)" .
      have "a (s t) * x' + U (s t) < t + x * a (s t)"
        using ineq by (simp add: field_simps)
      hence fmono: "F (a (s t) * x' + U (s t)) \<le> F (t + x * a (s t))"
        by (intro monoD[OF right_continuous_mono.mono[OF F]]) simp
      have "(1 - F (t + x * a (s t))) / (1 - F t)
              \<le> (1 - F (a (s t) * x' + U (s t))) / (1 - F t)"
        using fmono Ft by (intro divide_right_mono) auto
      thus ?case
        by simp
    qed
  qed
  have up: "\<forall>\<^sub>F t in endpoint_filter F. - ((1 - F (t + x * a (s t))) / (1 - F t))
                                       \<le> - ((1 - F (a (s t) * x' + U (s t))) / (1 - F t))"
    if x': "x < x'" "x' < x + \<eta>" for x'
  proof -
    have dpos: "0 < x' - x"
      using x' by simp
    have ev1: "\<forall>\<^sub>F t in endpoint_filter F. (t - U (s t)) / a (s t) < x' - x"
      using order_tendstoD(2)[OF delta_tendsto dpos] .
    show ?thesis
      using ev1 Flt1
    proof eventually_elim
      case (elim t)
      hence d: "(t - U (s t)) / a (s t) < x' - x" and Ft: "F t < 1"
        by auto
      have apos': "0 < a (s t)"
        using apos by simp
      have "((t - U (s t)) / a (s t)) * a (s t) < (x' - x) * a (s t)"
        using mult_strict_right_mono[OF d apos'] .
      moreover have "((t - U (s t)) / a (s t)) * a (s t) = t - U (s t)"
        using apos' by simp
      ultimately have ineq: "t - U (s t) < (x' - x) * a (s t)"
        by simp
      have "t + x * a (s t) < a (s t) * x' + U (s t)"
        using ineq by (simp add: field_simps)
      hence fmono: "F (t + x * a (s t)) \<le> F (a (s t) * x' + U (s t))"
        by (intro monoD[OF right_continuous_mono.mono[OF F]]) simp
      have "(1 - F (a (s t) * x' + U (s t))) / (1 - F t)
              \<le> (1 - F (t + x * a (s t))) / (1 - F t)"
        using fmono Ft by (intro divide_right_mono) auto
      thus ?case
        by simp
    qed
  qed
  show ?thesis
    unfolding goal_eq
    using tendsto_minus[OF squeeze_tendsto_local[OF eta Dcont conv low up]] by simp
qed

theorem Pickands_Balkema_de_Haan_normalization:
  fixes F a :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and apos: "\<And>t. 0 < a t"
    and quant: "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
                    \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
  shows "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (a (1 / (1 - F u))) x)
           (\<lambda>x. 0) (endpoint_filter F)"
proof -
  define \<beta> where "\<beta> = (\<lambda>u. a (1 / (1 - F u)))"
  have \<beta>pos: "0 < \<beta> u" for u
    using apos by (simp add: \<beta>_def)
  have pconv: "((\<lambda>u. excess_cdf F u (\<beta> u * x)) \<longlongrightarrow> GPD_cdf \<gamma> 0 1 x) (endpoint_filter F)"
    if x: "0 \<le> x" for x
    by (rule excess_tendsto_of_divide_tail[OF F \<beta>pos _ x])
       (use divide_tail_of_gap[OF F apos quant] in "simp add: \<beta>_def")
  have "uniform_limit {0..} (\<lambda>u x. excess_cdf F u (\<beta> u * x)) (GPD_cdf \<gamma> 0 1) (endpoint_filter F)"
    by (intro excess_pointwise_imp_uniform[OF F \<beta>pos] pconv)
  thus ?thesis
    using excess_uniform_scaled_iff[OF \<beta>pos] by (simp add: \<beta>_def)
qed

corollary Pickands_Balkema_de_Haan_normalization':
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  obtains a :: "real \<Rightarrow> real"
  where "\<And>t. 0 < a t"
    and "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
                          \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
    and "\<And>x. (\<lambda>n. F (a (real n) * x + tail_quantile F (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 x"
    and "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (a (1 / (1 - F u))) x)
           (\<lambda>x. 0) (endpoint_filter F)"
proof -
  obtain a where apos: "\<And>t. 0 < a t"
    and quant0: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
           \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of \<gamma>] by auto
  have quant: "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
                                \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
    using quant0 by simp
  show thesis
    by (rule that[of a])
       (use apos quant tail_quantile_witness_of_gap[OF F apos quant]
            Pickands_Balkema_de_Haan_normalization[OF F apos quant] in blast)+
qed

end