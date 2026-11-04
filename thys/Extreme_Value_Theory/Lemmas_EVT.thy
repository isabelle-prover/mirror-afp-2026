(*  Title:   Lemmas_EVT.thy
    Author:  Michikazu Hirata
*)

section \<open>Lemmas\<close>
theory Lemmas_EVT
imports
   "HOL-Probability.Probability"
   "Regular_Variation.Regular_Variation"
begin

lemma power_of_nat_log_less_Suc:
  fixes Z t :: real
  assumes Z: "1 < Z"
  shows "t < Z ^ (nat \<lfloor>log Z t\<rfloor> + 1)"
  using assms le_nat_floor[OF le_log_of_power, of Z _ t]
  by (meson less_add_one not_less)

subsection \<open>Lemmas for Measure Theory\<close>
lemma measure_density_on:
  assumes integ:"set_integrable M A f"
    and [measurable]: "f \<in> borel_measurable M"
    and [measurable]:"A \<in> sets M"
    and f_nonneg:"AE x \<in>A in M. 0 \<le> f x"
  shows "measure (density M f) A = (\<integral>x\<in>A. f x \<partial>M)"
proof -
  have "measure (density M f) A = enn2real (\<integral>\<^sup>+x\<in>A. ennreal (f x)\<partial>M)"
    by(simp add: measure_def emeasure_density)
  also have "... = enn2real (\<integral>\<^sup>+x. ennreal (f x)\<partial>(restrict_space M A))"
    by(simp add: nn_integral_restrict_space)
  also have "... = enn2real (ennreal (\<integral>x. f x \<partial>(restrict_space M A)))"
    using f_nonneg integ
    by(subst nn_integral_eq_integral)
      (auto simp: set_integrable_eq AE_restrict_space_iff)
  also have "... = enn2real (ennreal (\<integral>x\<in>A. f x \<partial>M))"
    by(simp add: integral_restrict_space set_lebesgue_integral_def)
  also have "... = (\<integral>x\<in>A. f x \<partial>M)"
    using f_nonneg
    by(intro enn2real_ennreal)
      (auto intro!: integral_nonneg_AE simp: set_lebesgue_integral_def)
  finally show ?thesis .
qed

corollary measure_density:
  assumes integ[measurable]:"integrable M f"
    and [measurable]:"A \<in> sets M"
    and f_nonneg:"AE x in M. 0 \<le> f x"
  shows "measure (density M f) A = (\<integral>x\<in>A. f x \<partial>M)"
  using f_nonneg integrable_mult_indicator[OF _ integ]
  by(auto intro!: measure_density_on simp: set_integrable_def)

lemma nn_integral_FTC_greaterThan:
  fixes f :: "real \<Rightarrow> real" and F :: "real \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable borel"
    and cont: "continuous (at_right a) F"
    and f: "\<And>x. a < x \<Longrightarrow> DERIV F x :> f x"
    and nonneg: "\<And>x. a < x \<Longrightarrow> 0 \<le> f x"
    and lim: "(F \<longlongrightarrow> T) at_top"
  shows "(\<integral>\<^sup>+x. ennreal (f x) * indicator {a <..} x \<partial>lborel) = T - F a"
proof -
  define lo where "lo n = a + 1 / (real n + 1)" for n :: nat
  define hi where "hi n = a + (real n + 1)" for n :: nat
  define g where "g n = (\<lambda>x. ennreal (f x) * indicator {lo n .. hi n} x)" for n :: nat
  have lo_gt: "\<And>n. a < lo n" and lo_le_hi: "\<And>n. lo n \<le> hi n"
    by (auto simp: lo_def hi_def field_simps)
  have g_eq: "integral\<^sup>N lborel (g n) = ennreal (F (hi n) - F (lo n))" for n
    unfolding g_def
    by (rule nn_integral_FTC_Icc[OF f_borel]) (use f nonneg lo_gt[of n] lo_le_hi[of n] in auto)
  have incseq_g: "incseq g"
    unfolding incseq_def le_fun_def g_def
  proof (intro allI impI)
    fix m n :: nat and x :: real
    assume "m \<le> n"
    hence "lo n \<le> lo m" "hi m \<le> hi n"
      by (auto simp: lo_def hi_def field_simps)
    thus "ennreal (f x) * indicator {lo m..hi m} x \<le> ennreal (f x) * indicator {lo n..hi n} x"
      using nonneg[of x] lo_gt[of m]
      by (auto split: split_indicator)
  qed
  have lo_tendsto: "lo \<longlonglongrightarrow> a"
    unfolding lo_def by real_asymp
  have hi_tendsto: "filterlim hi at_top sequentially"
    unfolding hi_def by real_asymp
  have lo_at_right: "filterlim lo (at_right a) sequentially"
    using lo_tendsto lo_gt by (rule tendsto_imp_filterlim_at_right[OF _ eventuallyI])
  have pointwise: "(\<lambda>n. g n x) \<longlonglongrightarrow> ennreal (f x) * indicator {a <..} x" for x
  proof (cases "a < x")
    case True
    have "\<forall>\<^sub>F n in sequentially. lo n \<le> x"
      using order_tendstoD(2)[OF lo_tendsto True] by (auto elim: eventually_mono)
    moreover have "\<forall>\<^sub>F n in sequentially. x \<le> hi n"
      using hi_tendsto[unfolded filterlim_at_top] by simp
    ultimately have "\<forall>\<^sub>F n in sequentially. g n x = ennreal (f x) * indicator {a<..} x"
      by eventually_elim (use True in \<open>auto simp: g_def split: split_indicator\<close>)
    thus ?thesis
      by (rule tendsto_eventually)
  next
    case False
    hence "g n x = 0" for n
      using lo_gt[of n] by (auto simp: g_def split: split_indicator)
    thus ?thesis
      using False by simp
  qed
  have limseq1: "(\<lambda>n. integral\<^sup>N lborel (g n)) \<longlonglongrightarrow> (\<integral>\<^sup>+x\<in>{a<..}. ennreal (f x)\<partial>lborel)"
    using f_borel pointwise
    by (intro nn_integral_LIMSEQ incseq_g) (auto simp: g_def)
  have limseq2: "(\<lambda>n. integral\<^sup>N lborel (g n)) \<longlonglongrightarrow> ennreal (T - F a)"
  proof -
    have "(\<lambda>n. F (hi n) - F (lo n)) \<longlonglongrightarrow> T - F a"
      using cont
      by (auto intro!: tendsto_diff filterlim_compose[OF _ hi_tendsto]
          filterlim_compose[OF _ lo_at_right] lim
          simp: continuous_within)
    from tendsto_ennrealI[OF this]
    show ?thesis
      by (simp add: g_eq)
  qed
  from LIMSEQ_unique[OF limseq1 limseq2]
  show ?thesis .
qed

lemma nn_integral_FTC_lessThan:
  fixes f :: "real \<Rightarrow> real" and F :: "real \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable borel"
    and cont: "continuous (at_left b) F"
    and f: "\<And>x. x < b \<Longrightarrow> DERIV F x :> f x"
    and nonneg: "\<And>x. x < b \<Longrightarrow> 0 \<le> f x"
    and lim: "(F \<longlongrightarrow> S) at_bot"
  shows "(\<integral>\<^sup>+x. ennreal (f x) * indicator {..< b} x \<partial>lborel) = F b - S"
proof -
  define g where "g x = f (- x)" for x :: real
  define G where "G x = - F (- x)" for x :: real
  note f_borel[measurable]
  have g_borel: "g \<in> borel_measurable borel"
    unfolding g_def by (rule measurable_compose[OF _ f_borel]) simp
  have G_deriv: "DERIV G x :> g x" if "-b < x" for x
  proof -
    have hx: "- x < b"
      using that by simp
    have Fd: "(F has_real_derivative f (- x)) (at (- x))"
      using f[OF hx] .
    have "DERIV (\<lambda>z. F (- z)) x :> f (- x) * (- 1)"
      by (rule DERIV_chain2[where g=uminus, OF Fd]) (auto intro!: derivative_eq_intros)
    with DERIV_minus[OF this]
    show ?thesis
      unfolding G_def g_def by simp
  qed
  have G_nonneg: "0 \<le> g x" if "-b < x" for x
    unfolding g_def using nonneg[of "-x"] that by simp
  have G_cont: "continuous (at_right (-b)) G"
    using cont[unfolded continuous_within]
    unfolding G_def continuous_within
    by (simp add: at_right_minus[of "-b"] filterlim_filtermap comp_def tendsto_minus)
  have G_lim: "(G \<longlongrightarrow> - S) at_top"
    unfolding G_def
    using filterlim_compose[OF lim filterlim_uminus_at_bot_at_top]
    by (intro tendsto_minus) simp
  have eq: "(\<integral>\<^sup>+x. ennreal (g x) * indicator {-b <..} x \<partial>lborel) = F b - S"
    using nn_integral_FTC_greaterThan[OF g_borel G_cont G_deriv G_nonneg G_lim]
    by (simp add: G_def)
  have "(\<integral>\<^sup>+x. ennreal (f x) * indicator {..< b} x \<partial>lborel)
      = (\<integral>\<^sup>+x. ennreal (f (0 + (-1) * x)) * indicator {..< b} (0 + (-1) * x) \<partial>lborel)"
    by (subst nn_integral_real_affine[where c="-1" and t=0
          and f="\<lambda>x. ennreal (f x) * indicator {..<b} x"]) auto
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (g x) * indicator {-b <..} x \<partial>lborel)"
    by (intro nn_integral_cong) (auto simp: g_def split: split_indicator)
  finally show ?thesis
    using eq by simp
qed

lemma
  fixes f :: "real \<Rightarrow> real" and F :: "real \<Rightarrow> real"
  assumes f_borel[measurable]: "f \<in> borel_measurable borel"
    and cont: "continuous (at_right a) F"
    and f: "\<And>x. a < x \<Longrightarrow> DERIV F x :> f x"
    and nonneg: "\<And>x. a < x \<Longrightarrow> 0 \<le> f x"
    and lim: "(F \<longlongrightarrow> T) at_top"
  shows set_integral_FTC_atLeast:"(\<integral>x\<in>{a..}. f x \<partial>lborel) = T - F a"
    and set_integrable_FTC_atLeast:"set_integrable lborel {a..} f"
proof -
  have mono:"F x \<le> F y" if ax:"a < x" and xy:"x \<le> y" for x y
    by(intro DERIV_nonneg_imp_nondecreasing[OF xy])
      (meson ax f nonneg order.strict_trans2)
  have le_T:"F x \<le> T" if "a < x" for x
    using mono[OF that] by(intro tendsto_lowerbound[OF lim])
      (auto intro!: eventually_at_top_linorderI[where c=x])
  have T_le:"F a \<le> T"
    using cont le_T eventually_at_right_less[of a]
    by(intro tendsto_upperbound[where F="at_right a"])
      (auto simp: continuous_within elim!: eventually_mono)
  have 1:"(\<integral>\<^sup>+x\<in>{a<..}. ennreal (f x)\<partial>lborel)
           = (\<integral>\<^sup>+ x. ennreal \<bar>indicat_real {a<..} x * f x\<bar> \<partial>lborel)"
    using nonneg by(auto intro!: nn_integral_cong simp: indicator_def)
  show "set_integrable lborel {a..} f"
    unfolding set_integrable_atLeast_eq[symmetric]
    using nn_integral_FTC_greaterThan[OF f_borel cont f nonneg lim]
    by(simp add: set_integrable_def integrable_iff_bounded 1)
  have "(\<integral>x\<in>{a..}. f x \<partial>lborel) = (\<integral>x\<in>{a<..}. f x \<partial>lborel)"
    by (simp add: set_integral_atLeast_eq)
  also have "... = enn2real (\<integral>\<^sup>+x\<in>{a<..}. ennreal (f x)\<partial>lborel)"
    unfolding set_lebesgue_integral_def using nonneg
    by(subst integral_eq_nn_integral)
      (auto simp: indicator_def intro!: arg_cong[where f=enn2real] nn_integral_cong)
  also have "... = enn2real (ennreal (T - F a))"
    by(simp add: nn_integral_FTC_greaterThan[OF f_borel cont f nonneg lim])
  also have "... = T - F a"
    by(simp add: T_le)
  finally show "(\<integral>x\<in>{a..}. f x \<partial>lborel) = T - F a" .
qed

lemma
  fixes f :: "real \<Rightarrow> real" and F :: "real \<Rightarrow> real"
  assumes f_borel[measurable]: "f \<in> borel_measurable borel"
  assumes cont: "continuous (at_left b) F"
  assumes f: "\<And>x. x < b \<Longrightarrow> DERIV F x :> f x"
  assumes nonneg: "\<And>x. x < b \<Longrightarrow> 0 \<le> f x"
  assumes lim: "(F \<longlongrightarrow> S) at_bot"
  shows set_integral_FTC_atMost:"(\<integral>x\<in>{..b}. f x \<partial>lborel) = F b - S"
    and set_integrable_FTC_atMost:"set_integrable lborel {..b} f"
proof -
  have mono:"F x \<le> F y" if xy:"x \<le> y" and yb:"y < b" for x y
    by(intro DERIV_nonneg_imp_nondecreasing[OF xy])
      (meson yb f nonneg order.strict_trans1)
  have S_ge:"S \<le> F x" if "x < b" for x
    using mono[OF _ that] by(intro tendsto_upperbound[OF lim])
      (auto intro!: eventually_at_bot_linorderI[where c=x])
  have b_left:"\<forall>\<^sub>F x in at_left b. x < b"
    by(simp add: eventually_at_filter)
  have S_le:"S \<le> F b"
    using cont S_ge b_left
    by(intro tendsto_lowerbound[where F="at_left b"])
      (auto simp: continuous_within elim!: eventually_mono)
  have 1:"(\<integral>\<^sup>+x\<in>{..<b}. ennreal (f x)\<partial>lborel)
           = (\<integral>\<^sup>+ x. ennreal \<bar>indicat_real {..<b} x * f x\<bar> \<partial>lborel)"
    using nonneg by(auto intro!: nn_integral_cong simp: indicator_def)
  show "set_integrable lborel {..b} f"
    unfolding set_integrable_atMost_eq[symmetric]
    using nn_integral_FTC_lessThan[OF f_borel cont f nonneg lim]
    by(simp add: set_integrable_def integrable_iff_bounded 1)
  have "(\<integral>x\<in>{..b}. f x \<partial>lborel) = (\<integral>x\<in>{..<b}. f x \<partial>lborel)"
    by (simp add: set_integral_atMost_eq)
  also have "... = enn2real (\<integral>\<^sup>+x\<in>{..<b}. ennreal (f x)\<partial>lborel)"
    unfolding set_lebesgue_integral_def using nonneg
    by(subst integral_eq_nn_integral)
      (auto simp: indicator_def intro!: arg_cong[where f=enn2real] nn_integral_cong)
  also have "... = enn2real (ennreal (F b - S))"
    by(simp add: nn_integral_FTC_lessThan[OF f_borel cont f nonneg lim])
  also have "... = F b - S"
    by(simp add: S_le)
  finally show "(\<integral>x\<in>{..b}. f x \<partial>lborel) = F b - S" .
qed

subsection \<open>Lemmas for Limits\<close>
lemma filterlim_log_at_top_gt_1:
  fixes a :: real
  assumes a:"1 < a"
  shows "filterlim (log a) at_top at_top"
  unfolding filterlim_at_top
proof safe
  fix Z
  show "\<forall>\<^sub>F x in at_top. Z \<le> log a x"
    by(auto intro!: eventually_at_top_linorderI[where c="max (a powr Z) 1"]
        le_log_iff[THEN iffD2] assms)
qed

lemma LIMSEQ_power_at_top:
  fixes c :: real
  assumes "1 < c"
  shows "filterlim (\<lambda>n. c ^ n) at_top sequentially"
  using Archimedean_eventually_pow assms filterlim_at_top_dense by blast

lemma floor_log_at_top:
  fixes Z :: real
  assumes Z: "1 < Z"
  shows "filterlim (\<lambda>t. nat \<lfloor>log Z t\<rfloor>) at_top at_top"
  by(intro filterlim_compose[OF filterlim_nat_sequentially]
      filterlim_compose[OF filterlim_floor_sequentially] filterlim_log_at_top_gt_1 Z)

lemma squeeze_tendsto_cont_points:
  fixes f :: "real \<Rightarrow> real" and h :: "'a \<Rightarrow> real" and gr :: "real \<Rightarrow> 'a \<Rightarrow> real"
    and F :: "'a filter" and y :: real
    and A :: "real set"
  assumes mono: "mono_on A f"
    and y:"y \<in> interior A"
    and cont: "isCont f y"
    and conv: "\<And>y'. y' \<in> A \<Longrightarrow> isCont f y' \<Longrightarrow> ((gr y') \<longlongrightarrow> f y') F"
    and low: "\<And>y'. y' < y \<Longrightarrow> y' \<in> A \<Longrightarrow> \<forall>\<^sub>F t in F. gr y' t \<le> h t"
    and up: "\<And>y'. y < y' \<Longrightarrow> y' \<in> A \<Longrightarrow> \<forall>\<^sub>F t in F. h t \<le> gr y' t"
  shows "(h \<longlongrightarrow> f y) F"
proof -
  obtain A' where A':"open A'" "y \<in> A'" "A' \<subseteq> A"
    using y interiorE by blast
  have cd: "countable {s \<in> A'. \<not> isCont f s}"
    by (intro mono_on_ctble_discont_open) (auto intro!: mono_onI mono_on_subset[OF mono] A')
  obtain \<delta>1 where \<delta>1: "0 < \<delta>1" "\<And>x. dist x y < \<delta>1 \<Longrightarrow> x \<in> A'"
    using A'(1,2) open_dist by blast
  show ?thesis
    unfolding tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    obtain \<delta>0 where \<delta>0: "0 < \<delta>0"
      "\<And>y''. y'' \<noteq> y \<and> \<bar>y'' - y\<bar> < \<delta>0 \<Longrightarrow> \<bar>f y'' - f y\<bar> < e"
      using LIM_D[OF cont[unfolded isCont_def], of e] e by auto
    define \<delta> where "\<delta> = min \<delta>0 \<delta>1 / 2"
    have \<delta>pos: "0 < \<delta>" and \<delta>lt: "\<delta> < \<delta>0" "\<delta> < \<delta>1"
      using \<delta>0(1) \<delta>1(1) by (auto simp: \<delta>_def)
    obtain ylo where ylo: "ylo \<in> {y - \<delta><..<y}" "ylo \<notin> {s \<in> A'. \<not> isCont f s}"
      using real_interval_avoid_countable_set[OF _ cd, of "y - \<delta>" y] \<delta>pos by auto
    obtain yhi where yhi: "yhi \<in> {y<..<y + \<delta>}" "yhi \<notin> {s \<in> A'. \<not> isCont f s}"
      using real_interval_avoid_countable_set[OF _ cd, of y "y + \<delta>"] \<delta>pos by auto
    have ylo_lt: "ylo < y" and yhi_gt: "y < yhi"
      using ylo(1) yhi(1) by auto
    have ylo_A': "ylo \<in> A'" and yhi_A': "yhi \<in> A'"
      using \<delta>1(2) ylo(1) yhi(1) \<delta>lt(2) by (auto simp: dist_real_def)
    have ylo_A: "ylo \<in> A" and yhi_A: "yhi \<in> A"
      using ylo_A' yhi_A' A'(3) by auto
    have ylo_cont: "isCont f ylo" and yhi_cont: "isCont f yhi"
      using ylo(2) yhi(2) ylo_A' yhi_A' by auto
    have "f y - e < f ylo"
      using \<delta>0(2)[of ylo] ylo(1) \<delta>lt(1) by auto
    hence lo: "\<forall>\<^sub>F t in F. f y - e < gr ylo t"
      by (intro order_tendstoD(1)[OF conv[OF ylo_A ylo_cont]])
    have "f yhi < f y + e"
      using \<delta>0(2)[of yhi] yhi(1) \<delta>lt(1) by auto
    hence hi: "\<forall>\<^sub>F t in F. gr yhi t < f y + e"
      by (intro order_tendstoD(2)[OF conv[OF yhi_A yhi_cont]])
    show "\<forall>\<^sub>F t in F. \<bar>h t - f y\<bar> < e"
      using lo hi low[OF ylo_lt ylo_A] up[OF yhi_gt yhi_A]
      by eventually_elim (simp add: abs_less_iff)
  qed
qed

lemma squeeze_tendsto_local:
  fixes f :: "real \<Rightarrow> real" and h :: "'a \<Rightarrow> real" and gr :: "real \<Rightarrow> 'a \<Rightarrow> real"
    and F :: "'a filter" and y \<eta> :: real
  assumes eta: "0 < \<eta>"
    and cont: "isCont f y"
    and conv: "\<And>y'. \<bar>y' - y\<bar> < \<eta> \<Longrightarrow> ((gr y') \<longlongrightarrow> f y') F"
    and low: "\<And>y'. y - \<eta> < y' \<Longrightarrow> y' < y \<Longrightarrow> \<forall>\<^sub>F t in F. gr y' t \<le> h t"
    and up: "\<And>y'. y < y' \<Longrightarrow> y' < y + \<eta> \<Longrightarrow> \<forall>\<^sub>F t in F. h t \<le> gr y' t"
  shows "(h \<longlongrightarrow> f y) F"
  unfolding tendsto_iff dist_real_def
proof safe
  fix e :: real
  assume e: "0 < e"
  obtain \<delta>0 where \<delta>0: "0 < \<delta>0"
    "\<And>y''. y'' \<noteq> y \<and> \<bar>y'' - y\<bar> < \<delta>0 \<Longrightarrow> \<bar>f y'' - f y\<bar> < e"
    using LIM_D[OF cont[unfolded isCont_def], of e] e by auto
  define \<delta> where "\<delta> = min \<delta>0 \<eta> / 2"
  have \<delta>pos: "0 < \<delta>" and \<delta>lt: "\<delta> < \<eta>" "\<delta> < \<delta>0"
    using \<delta>0(1) eta by (auto simp: \<delta>_def)
  define ylo yhi where "ylo = y - \<delta>" and "yhi = y + \<delta>"
  have ylo1: "y - \<eta> < ylo" "ylo < y" "ylo \<noteq> y" "\<bar>ylo - y\<bar> < \<delta>0" "\<bar>ylo - y\<bar> < \<eta>"
    using \<delta>pos \<delta>lt by (auto simp: ylo_def)
  have yhi1: "y < yhi" "yhi < y + \<eta>" "yhi \<noteq> y" "\<bar>yhi - y\<bar> < \<delta>0" "\<bar>yhi - y\<bar> < \<eta>"
    using \<delta>pos \<delta>lt by (auto simp: yhi_def)
  have "f y - e < f ylo"
    using \<delta>0(2)[of ylo] ylo1(3,4) by auto
  hence lo: "\<forall>\<^sub>F t in F. f y - e < gr ylo t"
    by (intro order_tendstoD(1)[OF conv[OF ylo1(5)]])
  have "f yhi < f y + e"
    using \<delta>0(2)[of yhi] yhi1(3,4) by auto
  hence hi: "\<forall>\<^sub>F t in F. gr yhi t < f y + e"
    by (intro order_tendstoD(2)[OF conv[OF yhi1(5)]])
  show "\<forall>\<^sub>F t in F. \<bar>h t - f y\<bar> < e"
    using lo hi low[OF ylo1(1,2)] up[OF yhi1(1,2)]
    by eventually_elim (simp add: abs_less_iff)
qed

corollary squeeze_tendsto_cont_points_pos:
  fixes f :: "real \<Rightarrow> real" and h :: "'a \<Rightarrow> real" and gr :: "real \<Rightarrow> 'a \<Rightarrow> real"
    and F :: "'a filter" and y :: real
  assumes mono: "mono_on {0<..} f"
    and y: "0 < y" and cont: "isCont f y"
    and conv: "\<And>r. 0 < r \<Longrightarrow> isCont f r \<Longrightarrow> ((gr r) \<longlongrightarrow> f r) F"
    and low: "\<And>r. 0 < r \<Longrightarrow> r < y \<Longrightarrow> \<forall>\<^sub>F t in F. gr r t \<le> h t"
    and up: "\<And>r. y < r \<Longrightarrow> \<forall>\<^sub>F t in F. h t \<le> gr r t"
  shows "(h \<longlongrightarrow> f y) F"
  using assms
  by(auto intro!: squeeze_tendsto_cont_points
      [where f=f and F=F and h=h and gr=gr and A="{0<..}"] simp: interior_open)

corollary squeeze_tendsto_cont_points_UNIV:
  fixes f :: "real \<Rightarrow> real" and h :: "'a \<Rightarrow> real" and gr :: "real \<Rightarrow> 'a \<Rightarrow> real"
    and F :: "'a filter" and y :: real
  assumes mono: "mono f"
    and cont: "isCont f y"
    and conv: "\<And>y'. isCont f y' \<Longrightarrow> ((gr y') \<longlongrightarrow> f y') F"
    and low: "\<And>y'. y' < y \<Longrightarrow> \<forall>\<^sub>F t in F. gr y' t \<le> h t"
    and up: "\<And>y'. y < y' \<Longrightarrow> \<forall>\<^sub>F t in F. h t \<le> gr y' t"
  shows "(h \<longlongrightarrow> f y) F"
  using assms
  by(auto intro!: squeeze_tendsto_cont_points
      [where f=f and F=F and h=h and gr=gr and A=UNIV] simp: interior_open)

lemma left_cont_agree_cocountable_eq:
  fixes f h :: "real \<Rightarrow> real" and N :: "real set" and y :: real
  assumes N: "countable N" and y: "0 < y"
    and left_cont: "(f \<longlongrightarrow> f y) (at_left y)"
    and left_cont_h: "(h \<longlongrightarrow> h y) (at_left y)"
    and eq: "\<And>x. 0 < x \<Longrightarrow> x < y \<Longrightarrow> x \<notin> N \<Longrightarrow> f x = h x"
  shows "f y = h y"
proof -
  define P where "P = (\<lambda>n z. z \<in> {max 0 (y - 1 / (real n + 1))<..<y} \<and> z \<notin> N)"
  have exP: "\<exists>z. P n z" for n
    unfolding P_def
    using real_interval_avoid_countable_set[OF _ N, of "max 0 (y - 1 / (real n + 1))" y]
      y by auto
  define zseq where "zseq = (\<lambda>n. SOME z. P n z)"
  have zseqP: "P n (zseq n)" for n
    unfolding zseq_def using exP by (rule someI_ex)
  have z_pos: "0 < zseq n" and z_lt: "zseq n < y" and z_notin: "zseq n \<notin> N" for n
    using zseqP by (auto simp: P_def)
  have z_gt: "y - 1 / (real n + 1) < zseq n" for n
    using zseqP by (auto simp: P_def)
  have diff_bound: "y - zseq n < 1 / (real n + 1)" for n
    using z_gt by (simp add: cross3_simps)
  have diff_pos: "0 \<le> y - zseq n" for n
    using z_lt less_eq_real_def by auto
  have "(\<lambda>n. y - zseq n) \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich)
    show "\<forall>\<^sub>F n in sequentially. 0 \<le> y - zseq n"
      using diff_pos by simp
    show "\<forall>\<^sub>F n in sequentially. y - zseq n \<le> 1 / (real n + 1)"
      using diff_bound by (simp add: less_le_not_le)
    show "(\<lambda>n. 1 / (real n + 1)) \<longlonglongrightarrow> (0::real)"
      using LIMSEQ_inverse_real_of_nat by (simp add: inverse_eq_divide add.commute)
  qed simp
  from tendsto_diff[OF tendsto_const this, of y]
  have z_tendsto: "(\<lambda>n. zseq n) \<longlonglongrightarrow> y"
    by simp
  have z_at_left: "filterlim zseq (at_left y) sequentially"
    by (rule tendsto_imp_filterlim_at_left[OF z_tendsto]) (simp add: z_lt)
  have f_lim: "(\<lambda>n. f (zseq n)) \<longlonglongrightarrow> f y"
    using filterlim_compose[OF left_cont z_at_left] by (simp add: comp_def)
  have h_lim: "(\<lambda>n. h (zseq n)) \<longlonglongrightarrow> h y"
    using filterlim_compose[OF left_cont_h z_at_left] by (simp add: comp_def)
  have "f (zseq n) = h (zseq n)" for n
    using eq[OF z_pos z_lt z_notin] .
  with h_lim have "(\<lambda>n. f (zseq n)) \<longlonglongrightarrow> h y"
    by simp
  from LIMSEQ_unique[OF f_lim this] show ?thesis .
qed

lemma power_tendsto_iff_tendsto_tail:
  fixes p :: "nat \<Rightarrow> real" and q :: real
  assumes p_nonneg: "\<And>n. 0 \<le> p n" and p_le1: "\<And>n. p n \<le> 1"
    and q_pos: "0 < q" and q_le1: "q \<le> 1"
  shows "(\<lambda>n. p n ^ n) \<longlonglongrightarrow> q \<longleftrightarrow> (\<lambda>n. real n * (1 - p n)) \<longlonglongrightarrow> - ln q"
proof -
  have lb: "1 - p n \<le> - ln (p n)" if "0 < p n" for n
    using ln_le_minus_one[OF that] by simp
  have ub: "p n * (- ln (p n)) \<le> 1 - p n" if "0 < p n" for n
  proof -
    have "ln (1 / p n) \<le> 1 / p n - 1"
      using that by (intro ln_le_minus_one) simp
    hence "- ln (p n) \<le> (1 - p n) / p n"
      using that by (simp add: ln_div field_simps)
    thus ?thesis
      using that by (simp add: field_simps)
  qed
  show ?thesis
  proof
    assume T: "(\<lambda>n. real n * (1 - p n)) \<longlonglongrightarrow> - ln q"
    have p_to_1: "(\<lambda>n. p n) \<longlonglongrightarrow> 1"
    proof -
      have "(\<lambda>n. (real n * (1 - p n)) * (1 / real n)) \<longlonglongrightarrow> 0"
        using tendsto_mult[OF T lim_1_over_n] by simp
      moreover have "\<forall>\<^sub>F n in sequentially. (real n * (1 - p n)) * (1 / real n) = 1 - p n"
        using eventually_gt_at_top[of 0] by eventually_elim auto
      ultimately have "(\<lambda>n. 1 - p n) \<longlonglongrightarrow> 0"
        by (rule Lim_transform_eventually)
      hence "(\<lambda>n. 1 - (1 - p n)) \<longlonglongrightarrow> 1 - 0"
        by (intro tendsto_diff tendsto_const)
      thus ?thesis
        by simp
    qed
    have ev_pos: "\<forall>\<^sub>F n in sequentially. 1 / 2 < p n"
      by (rule order_tendstoD(1)[OF p_to_1]) simp
    have nlnp: "(\<lambda>n. real n * (- ln (p n))) \<longlonglongrightarrow> - ln q"
    proof (rule tendsto_sandwich)
      show "\<forall>\<^sub>F n in sequentially. real n * (1 - p n) \<le> real n * (- ln (p n))"
        using ev_pos by eventually_elim (fastforce intro!: mult_left_mono lb)
      show "\<forall>\<^sub>F n in sequentially. real n * (- ln (p n)) \<le> real n * (1 - p n) / p n"
        using ev_pos
        by eventually_elim
           (use mult_left_mono[OF ub, of _ "real n" for n] in \<open>simp add: field_simps\<close>)
      show "(\<lambda>n. real n * (1 - p n)) \<longlonglongrightarrow> - ln q"
        by fact
      show "(\<lambda>n. real n * (1 - p n) / p n) \<longlonglongrightarrow> - ln q"
        using tendsto_divide[OF T p_to_1] by simp
    qed
    have "\<forall>\<^sub>F n in sequentially. exp (real n * ln (p n)) = p n ^ n"
      using ev_pos by eventually_elim (simp add: exp_of_nat_mult)
    moreover have "(\<lambda>n. exp (real n * ln (p n))) \<longlonglongrightarrow> exp (ln q)"
      using tendsto_minus[OF nlnp] by (intro tendsto_exp) simp
    ultimately show "(\<lambda>n. p n ^ n) \<longlonglongrightarrow> q"
      using q_pos by (auto intro: Lim_transform_eventually)
  next
    assume P: "(\<lambda>n. p n ^ n) \<longlonglongrightarrow> q"
    have p_to_1: "(\<lambda>n. p n) \<longlonglongrightarrow> 1"
    proof (rule tendsto_sandwich)
      have ev1: "\<forall>\<^sub>F n in sequentially. q / 2 < p n ^ n"
        by (rule order_tendstoD(1)[OF P]) (use q_pos q_le1 in simp)
      hence ev2: "\<forall>\<^sub>F n in sequentially. q / 2 < p n ^ n \<and> 0 < n"
        using eventually_gt_at_top[of 0] by (auto intro: eventually_conj)
      show "\<forall>\<^sub>F n in sequentially. (q / 2) powr (1 / real n) \<le> p n"
        using ev2
      proof eventually_elim
        case (elim n)
        hence pn_pos: "0 < p n"
          using q_pos p_nonneg[of n] by (cases "p n = 0") (auto simp: zero_power)
        have "(q / 2) powr (1 / real n) \<le> (p n ^ n) powr (1 / real n)"
          using elim q_pos by (intro powr_mono2) auto
        also have "(p n ^ n) powr (1 / real n) = (p n powr real n) powr (1 / real n)"
          using pn_pos by (simp add: powr_realpow)
        also have "\<dots> = p n"
          using elim pn_pos by (simp add: powr_powr)
        finally show ?case .
      qed
      show "\<forall>\<^sub>F n in sequentially. p n \<le> 1"
        using p_le1 by simp
      have "(\<lambda>n. (q / 2) powr (1 / real n)) \<longlonglongrightarrow> (q / 2) powr 0"
        using q_pos by (intro tendsto_powr tendsto_const lim_1_over_n) auto
      thus "(\<lambda>n. (q / 2) powr (1 / real n)) \<longlonglongrightarrow> 1"
        using q_pos q_le1 by simp
      show "(\<lambda>n. 1::real) \<longlonglongrightarrow> 1"
        by simp
    qed
    have ev_pos: "\<forall>\<^sub>F n in sequentially. 1 / 2 < p n"
      by (rule order_tendstoD(1)[OF p_to_1]) simp
    have nlnp: "(\<lambda>n. real n * (- ln (p n))) \<longlonglongrightarrow> - ln q"
    proof -
      have "(\<lambda>n. ln (p n ^ n)) \<longlonglongrightarrow> ln q"
        using q_pos by (intro isCont_tendsto_compose[OF _ P] isCont_ln) simp
      moreover have "\<forall>\<^sub>F n in sequentially. ln (p n ^ n) = real n * ln (p n)"
        using ev_pos by eventually_elim (simp add: ln_realpow)
      ultimately have "(\<lambda>n. real n * ln (p n)) \<longlonglongrightarrow> ln q"
        by (simp add: filterlim_cong)
      thus ?thesis
        by(auto dest: tendsto_minus)
    qed
    show "(\<lambda>n. real n * (1 - p n)) \<longlonglongrightarrow> - ln q"
    proof (rule tendsto_sandwich)
      show "\<forall>\<^sub>F n in sequentially. p n * (real n * (- ln (p n))) \<le> real n * (1 - p n)"
        using ev_pos
        by eventually_elim
           (use mult_left_mono[OF ub, of _ "real n" for n] in \<open>simp add: field_simps\<close>)
      show "\<forall>\<^sub>F n in sequentially. real n * (1 - p n) \<le> real n * (- ln (p n))"
        using ev_pos by eventually_elim (fastforce intro!: mult_left_mono lb)
    qed(use tendsto_mult[OF p_to_1 nlnp] nlnp in auto)
  qed
qed

lemma filterlim_shift_scale_at_top:
  fixes \<mu> \<sigma> \<xi> :: real
  assumes [arith]:"0 < \<sigma>" "0 < \<xi>"
  shows "LIM x at_top. 1 + \<xi> * ((x - \<mu>) / \<sigma>) :> at_top"
  using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of "1 / \<sigma>"]
      _ filterlim_tendsto_add_at_top[OF tendsto_const[of "- \<mu>" at_top],of "\<lambda>x. x"]]
  by(intro filterlim_tendsto_add_at_top[OF tendsto_const]
      filterlim_tendsto_pos_mult_at_top[OF tendsto_const])
    (auto simp: filterlim_ident)

lemma filterlim_shift_scale_at_bot:
  fixes \<mu> \<sigma> \<xi> :: real
  assumes sigma: "0 < \<sigma>" and xi_neg: "\<xi> < 0"
  shows "LIM x at_bot. 1 + \<xi> * ((x - \<mu>) / \<sigma>) :> at_top"
proof -
  have eq: "(\<lambda>x. 1 + \<xi> * ((x - \<mu>) / \<sigma>)) = (\<lambda>x. 1 + (- \<xi> / \<sigma>) * (\<mu> - x))"
    by (rule ext) (use sigma in \<open>simp add: field_simps\<close>)
  have "LIM x at_bot. \<mu> - x :> at_top"
    by real_asymp
  hence "LIM x at_bot. (- \<xi> / \<sigma>) * (\<mu> - x) :> at_top"
    by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const])
       (use assms in \<open>auto intro: divide_neg_pos\<close>)
  hence "LIM x at_bot. 1 + (- \<xi> / \<sigma>) * (\<mu> - x) :> at_top"
    by (intro filterlim_tendsto_add_at_top[OF tendsto_const])
  thus ?thesis
    unfolding eq .
qed

subsection \<open>Lemmas for Weak Convergence\<close>
lemma weak_conv_ignore_initial_segment:
  assumes "weak_conv a A"
  shows "weak_conv (\<lambda>n. a (n + k)) A"
  using assms by(auto simp: weak_conv_def intro!: LIMSEQ_ignore_initial_segment)

lemma weak_conv_offset:
  assumes "weak_conv (\<lambda>n. a (n + k)) A"
  shows "weak_conv a A"
  using assms LIMSEQ_offset by(fastforce simp: weak_conv_def)

lemma weak_conv_cong:
  assumes ev:"\<And>x. isCont A x \<Longrightarrow> \<forall>\<^sub>F n in sequentially. a n x = b n x"
  shows "weak_conv a A \<longleftrightarrow> weak_conv b A"
  using tendsto_cong[OF ev] by(simp add: weak_conv_def)

lemma LIMSEQ_imp_weak_conv:
  "(\<And>x. (\<lambda>n. a n x) \<longlonglongrightarrow> A x) \<Longrightarrow> weak_conv a A"
  by(simp add: weak_conv_def)

subsection \<open>Generalized Inverses\<close>
definition ginv :: "('a :: conditionally_complete_linorder \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<^sup>\<leftarrow>" [81]) where
"ginv F y = Inf {x. y \<le> F x}"

text \<open> The constant @{term ginv} is the same as @{const right_continuous_mono.I}.
       We define @{term ginv} because @{const right_continuous_mono.I} is defined inside
       the locale @{locale right_continuous_mono},
       which makes it inconvenient to use.\<close>

lemma bdd_below_ginv_set:
  assumes mono:"mono F" and Fw:"F w < y"
  shows "bdd_below {x::_ :: linorder. y \<le> F x}"
proof (intro bdd_belowI[of _ w])
  fix x
  assume x:"x \<in> {x. y \<le> F x}"
  show "w \<le> x"
    using x monoD[OF mono, of x w] Fw by force
qed

lemma ginv_le_iff1:
  fixes y :: "'a::{linorder_topology,conditionally_complete_linorder}"
  assumes mono: "mono F" and cont: "\<And>x. continuous (at_right x) F"
    and yFz: "y \<le> F z" and Fwy: "F w < y"
  shows "F\<^sup>\<leftarrow> y \<le> x \<longleftrightarrow> y \<le> F x"
proof
  have ne: "{x. y \<le> F x} \<noteq> {}"
    using yFz by auto
  show "y \<le> F x \<Longrightarrow> ginv F y \<le> x"
    unfolding ginv_def by (auto intro!: cInf_lower bdd_below_ginv_set[OF mono Fwy])
  assume *: "ginv F y \<le> x"
  have "y \<le> (INF s\<in>{x. y \<le> F x}. F s)"
    by (rule cINF_greatest[OF ne]) auto
  also have "\<dots> = F (Inf {x. y \<le> F x})"
    using continuous_at_Inf_mono[OF mono cont ne bdd_below_ginv_set[OF mono Fwy]] ..
  also have "\<dots> \<le> F x"
    using * monoD[OF mono] by (simp add: ginv_def)
  finally show "y \<le> F x" .
qed

lemma ginv_mono:
  assumes mono: "mono F" and y12: "y1 \<le> y2"
    and ex_z: "\<exists>z. y2 \<le> F z" and ex_w: "\<exists>w. F w < y1"
  shows "ginv F y1 \<le> ginv F y2"
proof -
  obtain z w where z: "y2 \<le> F z" and w: "F w < y1"
    using ex_z ex_w by auto
  have ne: "{x. y2 \<le> F x} \<noteq> {}"
    using z by auto
  have sub: "{x. y2 \<le> F x} \<subseteq> {x. y1 \<le> F x}"
    using y12 by auto
  show ?thesis
    unfolding ginv_def by (rule cInf_superset_mono[OF ne bdd_below_ginv_set[OF mono w] sub])
qed

lemma ginv_compose_mono:
  assumes mono: "mono F" and monog:"mono_on A g"
    and ex:"\<forall>s\<in>A. \<exists>z. g s \<le> F z" "\<forall>r\<in>A. \<exists>w. F w < g r"
  shows "mono_on A (\<lambda>x. ginv F (g x))"
  using ex
  by(intro ginv_mono mono_onI mono_onD[OF monog] monoD[OF mono])
     auto

lemma ginv_attained1:
  fixes y :: "'a::{linorder_topology,conditionally_complete_linorder}"
  assumes mono: "mono F" and cont: "\<And>z. continuous (at_right z) F"
    and ex_z: "\<exists>z. y \<le> F z" and ex_w: "\<exists>w. F w < y"
  shows "y \<le> F (ginv F y)"
proof -
  obtain z w where "y \<le> F z" "F w < y"
    using ex_z ex_w by auto
  thus ?thesis
    using ginv_le_iff1[OF mono cont, of y z w "ginv F y"]
    by simp
qed

text \<open>Convergence of generalized inverses (Lemma~1.1.1 of the book by de Haan and
      Ferreira~\<^cite>\<open>deHaanFerreira\<close>).\<close>
lemma tendsto_ginv:
  fixes Fn :: "nat \<Rightarrow> real \<Rightarrow> real" and g :: "real \<Rightarrow> real" and y :: real
  assumes mono_Fn: "\<And>n. mono (Fn n)" and mono_g: "mono g"
    and wc':"weak_conv Fn g"
    and cont_ginv: "isCont (ginv g) y"
    and yz: "y < g z" and wy: "g w < y"
  shows "(\<lambda>n. (Fn n)\<^sup>\<leftarrow> y) \<longlonglongrightarrow> g\<^sup>\<leftarrow> y"
proof (rule metric_LIMSEQ_I)
  have wc:"\<And>x. isCont g x \<Longrightarrow> (\<lambda>n. Fn n x) \<longlonglongrightarrow> g x"
    using wc' by(simp add: weak_conv_def)
  fix \<epsilon> :: real
  assume eps: "0 < \<epsilon>"
  define x0 where "x0 = ginv g y"
  note cd = mono_ctble_discont[OF mono_g]
  have bdd: "bdd_below {x. y \<le> g x}"
    using wy by (intro bdd_below_ginv_set[OF mono_g])
  have ne: "{x. y \<le> g x} \<noteq> {}"
    using yz by (auto intro!: exI[of _ z] less_imp_le)
  obtain x1 where x1: "x1 \<in> {x0 - \<epsilon><..<x0}" "isCont g x1"
    using real_interval_avoid_countable_set[OF _ cd, of "x0 - \<epsilon>" x0] eps by auto
  have gx1: "g x1 < y"
  proof (rule ccontr)
    assume "\<not> g x1 < y"
    hence "x0 \<le> x1"
      unfolding x0_def ginv_def by (auto intro!: cInf_lower bdd)
    with x1(1) show False
      by auto
  qed
  obtain s where s: "0 < s"
    "\<And>y'. y' \<noteq> y \<and> \<bar>y' - y\<bar> < s \<Longrightarrow> \<bar>ginv g y' - ginv g y\<bar> < \<epsilon> / 2"
    using LIM_D[OF cont_ginv[unfolded isCont_def], of "\<epsilon> / 2"] eps by auto
  define y' where "y' = min (y + s / 2) ((y + g z) / 2)"
  have y'1: "y < y'"
    using s(1) yz by (simp add: y'_def)
  have y'2: "y' \<le> g z"
    using yz by (auto simp: y'_def min_le_iff_disj)
  have y'3: "\<bar>y' - y\<bar> < s"
    using s(1) yz unfolding y'_def by (auto simp: min_def)
  have upper': "ginv g y' < x0 + \<epsilon> / 2"
    using s(2)[of y'] y'1 y'3 unfolding x0_def
    by (auto simp: abs_real_def split: if_split_asm)
  obtain x2 where x2: "x2 \<in> {ginv g y'<..<x0 + \<epsilon>}" "isCont g x2"
    using real_interval_avoid_countable_set[OF _ cd, of "ginv g y'" "x0 + \<epsilon>"] upper' eps by auto
  have gx2: "y < g x2"
  proof -
    have ne': "{x. y' \<le> g x} \<noteq> {}"
      using y'2 by auto
    have "Inf {x. y' \<le> g x} < x2"
      using x2(1) by (auto simp: ginv_def)
    from cInf_lessD[OF ne' this] obtain x' where x': "y' \<le> g x'" "x' < x2"
      by auto
    hence "y' \<le> g x2"
      using monoD[OF mono_g, of x' x2] by auto
    with y'1 show ?thesis
      by auto
  qed
  have ev1: "\<forall>\<^sub>F n in sequentially. Fn n x1 < y"
    by (rule order_tendstoD(2)[OF wc[OF x1(2)] gx1])
  have ev2: "\<forall>\<^sub>F n in sequentially. y < Fn n x2"
    by (rule order_tendstoD(1)[OF wc[OF x2(2)] gx2])
  have "\<forall>\<^sub>F n in sequentially. dist (ginv (Fn n) y) x0 < \<epsilon>"
    using ev1 ev2
  proof eventually_elim
    case (elim n)
    have ne_n: "{x. y \<le> Fn n x} \<noteq> {}"
      using elim(2) by (auto intro!: exI[of _ x2] less_imp_le)
    have up: "ginv (Fn n) y \<le> x2"
      unfolding ginv_def
      by (intro cInf_lower bdd_below_ginv_set[OF mono_Fn elim(1)]) (use elim(2) in auto)
    have low: "x1 \<le> ginv (Fn n) y"
      unfolding ginv_def
      by (intro cInf_greatest[OF ne_n])
         (metis mono_Fn elim(1) leI mem_Collect_eq monoD order_less_le_trans less_le_not_le)
    show ?case
      using up low x1(1) x2(1) unfolding dist_real_def by auto
  qed
  thus"\<exists>no. \<forall>n\<ge>no. dist (ginv (Fn n) y) (ginv g y) < \<epsilon>"
    unfolding eventually_sequentially x0_def by blast
qed

context right_continuous_mono
begin

lemma ex_gt_b:
  assumes "p < b"
  shows "\<exists>z. p < f z"
  using order_tendstoD[OF top,of p] assms
  by (auto dest!: eventually_happens'[OF trivial_limit_at_top_linorder])

lemma ex_ge_b:
  assumes "p < b"
  shows "\<exists>z. p \<le> f z"
  using ex_gt_b[OF assms] by(auto intro!: less_imp_le)

lemma ex_less_a:
  assumes "a < p"
  shows "\<exists>w. f w < p"
  using order_tendstoD[OF bot,of p] assms
  by (auto dest!: eventually_happens'[OF trivial_limit_at_bot_linorder])

lemma ex_le_a:
  assumes "a < p"
  shows "\<exists>w. f w \<le> p"
  using ex_less_a[OF assms] by(auto intro!: less_imp_le)

lemma a_le_b:"a \<le> b"
proof -
  have "\<forall>\<^sub>F w in at_bot. f w \<le> f 0"
    by (auto intro!: eventually_mono[OF eventually_le_at_bot[of 0]] monoD[OF mono])
  from tendsto_upperbound[OF bot this]
  have "a \<le> f 0"
    by simp
  moreover
  have "\<forall>\<^sub>F w in at_top. f 0 \<le> f w"
    by (auto intro!: eventually_mono[OF eventually_ge_at_top[of 0]] monoD[OF mono])
  from tendsto_lowerbound[OF top this]
  have "f 0 \<le> b"
    by simp
  ultimately show ?thesis
    by linarith
qed

lemma ginv_le_iff:
  assumes "a < p" "p < b"
  shows "ginv f p \<le> x \<longleftrightarrow> p \<le> f x"
  unfolding ginv_def
  by(intro pseudoinverse[symmetric] assms)

lemma ginv_attained:
  assumes "a < p" "p < b"
  shows "p \<le> f (ginv f p)"
  using ginv_le_iff[OF assms, of "ginv f p"] by simp

lemma
  shows a_le_f: "a \<le> f x"
    and f_le_b: "f x \<le> b"
proof -
  have "\<forall>\<^sub>F w in at_bot. f w \<le> f x"
    by (auto intro!: eventually_mono[OF eventually_le_at_bot[of x]] monoD[OF mono])
  from tendsto_upperbound[OF bot this]
  show "a \<le> f x"
    by simp
  have "\<forall>\<^sub>F w in at_top. f x \<le> f w"
    by (auto intro!: eventually_mono[OF eventually_ge_at_top[of x]] monoD[OF mono])
  from tendsto_lowerbound[OF top this]
  show "f x \<le> b"
    by simp
qed

lemma ginv_left_cont:
  assumes  ap: "a < p" and pb:"p < b"
  shows "(ginv f \<longlongrightarrow> ginv f p) (at_left p)"
proof (rule order_tendstoI)
  fix c
  assume c: "c < ginv f p"
  hence fc_less: "f c < p"
    using ginv_le_iff[OF assms, of c] by simp
  define p0 where "p0 = (f c + p) / 2"
  have p0_pos: "a < p0" and p0_lt_p: "p0 < p" and Fc_lt_p0: "f c < p0"
    using a_le_f[of c] ap fc_less by(auto simp: p0_def)
  have p0_lt_1: "p0 < b"
    using p0_lt_p pb by simp
  have c_lt_p0: "c < ginv f p0"
    using ginv_le_iff[OF p0_pos p0_lt_1, of c] Fc_lt_p0 by force
  have "\<forall>\<^sub>F x in at_left p. p0 < x \<and> x < p"
    using eventually_at_left_field[where x = p] p0_lt_p by auto
  thus "\<forall>\<^sub>F x in at_left p. c < ginv f x"
    by eventually_elim
      (metis c_lt_p0 pb dual_order.strict_trans ginv_le_iff linorder_not_less p0_pos)
next
  fix c
  assume c: "ginv f p < c"
  have "\<forall>\<^sub>F x in at_left p. a < x \<and> x < p"
    using eventually_at_left_field[where x = p] ap by auto
  thus "\<forall>\<^sub>F x in at_left p. ginv f x < c"
    by eventually_elim (smt (verit) c pb ginv_le_iff)
qed

lemma f_eq_b:
  assumes "f y = b"
    and "y \<le> x"
  shows "f x = b"
  using assms f_le_b mono monoD order_antisym by blast

lemma f_eq_a:
  assumes "f y = a"
    and "x \<le> y"
  shows "f x = a"
  by (metis a_le_f assms dual_order.eq_iff mono monoD)

corollary regularly_varying_less_b:
  assumes "regularly_varying (\<lambda>x. b - f x) \<rho>"
  shows "f x < b"
proof(rule ccontr)
  assume "\<not> f x < b"
  hence eq:"\<And>y. x \<le> y \<Longrightarrow> f y = b"
    by (metis f_eq_b f_le_b not_le order_antisym)
  show False
    using regularly_varying_pos[OF assms,of "max 1 x"]
    by(cases "1 \<le> x") (auto simp: eq)
qed

lemma ex_gt_less:
  assumes z: "f z < c"
  shows "\<exists>w>z. f w < c"
proof -
  have "\<forall>\<^sub>F y in at_right z. f y < c \<and> z < y"
    using order_tendstoD(2)[OF cont[of z, unfolded continuous_within] z]
      eventually_at_right_less by eventually_elim simp
  from eventually_happens'[OF trivial_limit_at_right_real this]
  show ?thesis
    by blast
qed

lemma upper_semicontinuous: "upper_semicontinuous_map euclidean f"
proof -
  have "open {x. f x < c}" for c
  proof -
    have *:"(\<Union>w\<in>{w. f w < c}. {..<w}) = {x. f x < c}"
    proof (intro set_eqI iffI)
      fix x
      assume "x \<in> (\<Union>w\<in>{w. f w < c}. {..<w})"
      then obtain w where "f w < c" "x < w"
        by auto
      thus "x \<in> {x. f x < c}"
        using monoD[OF mono, of x w] by simp
    next
      fix x
      assume "x \<in> {x. f x < c}"
      thus "x \<in> (\<Union>w\<in>{w. f w < c}. {..<w})"
        using ex_gt_less[of x c] by auto
    qed
    have "open (\<Union>w\<in>{w. f w < c}. {..<w})"
      by fastforce
    thus ?thesis
      unfolding * .
  qed
  thus ?thesis
    by(auto simp: upper_semicontinuous_map_def)
qed

corollary open_less: "open {x. f x < c}"
  using upper_semicontinuous by(simp add: upper_semicontinuous_map_def)

lemma strict_mono_of_deriv:
  assumes deriv: "\<And>z. x0 < z \<Longrightarrow> f z < c \<Longrightarrow> (f has_real_derivative f' z) (at z)"
    and pos: "\<And>z. x0 < z \<Longrightarrow> f z < c \<Longrightarrow> 0 < f' z"
    and x: "x0 < x" and xy: "x < y" and fy: "f y < c"
  shows "f x < f y"
proof (rule DERIV_pos_imp_increasing[OF xy])
  fix z
  assume z: "x \<le> z" "z \<le> y"
  hence "x0 < z" "f z < c"
    using x fy monoD[OF mono, of z y] by auto
  thus "\<exists>w. (f has_real_derivative w) (at z) \<and> 0 < w"
    using deriv pos by blast
qed

lemma ginv_f_eq:
  assumes fmono: "\<And>x y. x0 < x \<Longrightarrow> x < y \<Longrightarrow> f y < b \<Longrightarrow> f x < f y"
    and z: "x0 < z" and fz: "f z < b"
  shows "ginv f (f z) = z"
proof -
  have w: "x0 < (x0 + z) / 2" "(x0 + z) / 2 < z"
    using z by simp_all
  have "f ((x0 + z) / 2) < f z"
    by (rule fmono[OF w fz])
  hence p: "a < f z"
    using a_le_f[of "(x0 + z) / 2"] by simp
  have "z \<le> ginv f (f z)"
  proof (rule ccontr)
    assume "\<not> z \<le> ginv f (f z)"
    hence lt: "ginv f (f z) < z"
      by simp
    define v where "v = (max x0 (ginv f (f z)) + z) / 2"
    have vx0: "x0 < v" and vginv: "ginv f (f z) < v" and vz: "v < z"
      using lt z by (auto simp: v_def)
    have "f z \<le> f v"
      using ginv_le_iff[OF p fz, of v] vginv by simp
    moreover have "f v < f z"
      by (rule fmono[OF vx0 vz fz])
    ultimately show False
      by simp
  qed
  moreover have "ginv f (f z) \<le> z"
    using ginv_le_iff[OF p fz, of z] by simp
  ultimately show ?thesis
    by simp
qed

end

sublocale real_distribution \<subseteq> right_continuous_mono "cdf M" 0 1
  by standard
     (auto intro!: monoI cdf_nondecreasing cdf_is_right_cont cdf_lim_at_bot cdf_lim_at_top_prob)

corollary right_continuous_mono_cdf:
  assumes "real_distribution M"
  shows "right_continuous_mono (cdf M) 0 1"
proof -
  interpret real_distribution M by fact
  show ?thesis
    by unfold_locales
qed

lemma one_less_of_inverse_tail_less:
  fixes F :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and x0: "F x0 < 1"
    and t: "1 / (1 - F x0) < t"
  shows "1 < t"
proof -
  have "1 \<le> 1 / (1 - F x0)"
    using x0 right_continuous_mono.a_le_f[OF F, of x0] by simp
  thus ?thesis
    using t by linarith
qed

subsection \<open>Lemmas for Infinite Sums\<close>
text \<open> The following are used to prove relation~(1.2.21) of \<^cite>\<open>deHaanFerreira\<close>. \<close>
lemma geometric_ratio_chain_ge:
  fixes d :: "nat \<Rightarrow> real"
  assumes pos: "\<And>n. 0 < d n"
    and r: "0 < r"
    and bound: "\<And>j. M \<le> j \<Longrightarrow> r \<le> d (Suc j) / d j"
    and k: "M \<le> k"
  shows "d k * r ^ m \<le> d (k + m)"
proof (induction m)
  case (Suc m)
  hence "d k * r ^ Suc m \<le> r * d (k + m)"
    using r by (auto intro!: mult_left_mono)
  also have "\<dots> \<le> d (Suc (k + m))"
    using bound[of "k + m"] k pos[of "k + m"] by (simp add: field_simps)
  finally show ?case
    by simp
qed simp

lemma geometric_ratio_chain_le:
  fixes d :: "nat \<Rightarrow> real"
  assumes pos: "\<And>n. 0 < d n"
    and r: "0 < r"
    and bound: "\<And>j. M \<le> j \<Longrightarrow> d (Suc j) / d j \<le> r"
    and k: "M \<le> k"
  shows "d (k + m) \<le> d k * r ^ m"
proof (induction m)
  case (Suc m)
  have "d (Suc (k + m)) \<le> r * d (k + m)"
    using bound[of "k + m"] k pos[of "k + m"] by (simp add: field_simps)
  also have "\<dots> \<le> d k * r ^ Suc m"
    using Suc r by (auto intro!: mult_left_mono)
  finally show ?case
    by simp
qed simp

lemma geometric_ratio_tailsum_tendsto:
  fixes d :: "nat \<Rightarrow> real" and L :: real
  assumes pos: "\<And>n. 0 < d n"
    and L: "0 < L" "L < 1"
    and ratio: "(\<lambda>n. d (Suc n) / d n) \<longlonglongrightarrow> L"
  shows geometric_ratio_tailsum_summable: "summable d"
    and geometric_ratio_tailsum_div: "(\<lambda>n. (\<Sum>k. d (k + n)) / d n) \<longlonglongrightarrow> 1 / (1 - L)"
    and geometric_ratio_tailsum_ratio: "(\<lambda>n. (\<Sum>k. d (k + Suc n)) / (\<Sum>k. d (k + n))) \<longlonglongrightarrow> L"
proof -
  define cs where "cs = (1 + L) / 2"
  have cs_bounds: "L < cs" "cs < 1" "0 < cs"
    using L by (simp_all add: cs_def)
  obtain N0 where N0: "\<And>n. N0 \<le> n \<Longrightarrow> d (Suc n) / d n < cs"
    using order_tendstoD(2)[OF ratio cs_bounds(1)] unfolding eventually_sequentially by blast
  have step_le0: "d (Suc n) \<le> cs * d n" if "N0 \<le> n" for n
    using N0[OF that] pos[of n] by (simp add: field_simps)
  show summable: "summable d"
    using cs_bounds step_le0 pos
    by(auto intro!: summable_ratio_test[of cs N0 d] simp: abs_of_pos)
  note chain_ge = geometric_ratio_chain_ge[where d=d, OF pos]
  note chain_le = geometric_ratio_chain_le[where d=d, OF pos]
  define T where "T = (\<lambda>n. \<Sum>k. d (k + n))"
  have shift_summable: "summable (\<lambda>k. d (k + n))" for n
    using summable by simp
  have T_eq: "T n = suminf d - (\<Sum>i<n. d i)" for n
    unfolding T_def using suminf_minus_initial_segment[OF summable, of n] by simp
  have partial_tendsto: "(\<lambda>n. \<Sum>i<n. d i) \<longlonglongrightarrow> suminf d"
    using summable by (rule summable_LIMSEQ)
  have T_fun_eq: "T = (\<lambda>n. suminf d - (\<Sum>i<n. d i))"
    using T_eq by (intro ext) simp
  have T_tendsto0: "T \<longlonglongrightarrow> 0"
    unfolding T_fun_eq
    using tendsto_diff[OF tendsto_const partial_tendsto, of "suminf d"] by simp
  have T_pos: "0 < T n" for n
  proof -
    have I: "finite {0::nat}" "\<And>k. k \<in> - {0::nat} \<Longrightarrow> 0 \<le> d (k + n)"
      using pos by (auto simp: less_eq_real_def)
    have "(0::real) < d (0 + n)"
      using pos by simp
    also have "d (0 + n) = sum (\<lambda>k. d (k + n)) {0}"
      by simp
    also have "\<dots> \<le> suminf (\<lambda>k. d (k + n))"
      by (rule sum_le_suminf[OF shift_summable[of n] I(1) I(2)])
    finally show ?thesis
      by (simp add: T_def)
  qed
  have T_diff: "T n - T (Suc n) = d n" for n
    using T_eq[of n] T_eq[of "Suc n"] by simp
  have geom_sum: "(\<Sum>k. d n * r ^ k) = d n / (1 - r)" if r: "0 < r" "r < 1" for n r
    using suminf_geometric[of r] r by (simp add: suminf_mult)
  have geom_summable: "summable (\<lambda>k. d n * r ^ k)" if r: "0 < r" "r < 1" for n r
    using summable_geometric[of r] r by (intro summable_mult) simp
  have div_tendsto: "(\<lambda>n. T n / d n) \<longlonglongrightarrow> 1 / (1 - L)"
  proof (rule order_tendstoI)
    fix c :: real
    assume c: "1 / (1 - L) < c"
    have c_pos: "0 < c"
      using L c by (smt (verit) divide_pos_pos zero_less_divide_1_iff)
    define r where "r = (L + (1 - 1 / c)) / 2"
    have Lc: "L < 1 - 1 / c"
      using c c_pos L by (simp add: divide_less_eq field_simps)
    have r_bounds: "L < r" "r < 1 - 1 / c"
      using Lc by (simp_all add: r_def)
    have r_pos: "0 < r"
      using L r_bounds(1) by simp
    have r_lt1: "r < 1"
      using r_bounds(2) c_pos by (smt (verit) zero_less_divide_1_iff)
    have r_val: "1 / (1 - r) < c"
      using r_bounds(2) c_pos r_lt1 by (simp add: field_simps)
    obtain N where N: "\<And>j. N \<le> j \<Longrightarrow> d (Suc j) / d j < r"
      using order_tendstoD(2)[OF ratio r_bounds(1)]
      unfolding eventually_sequentially by blast
    have bound_le: "\<And>j. N \<le> j \<Longrightarrow> d (Suc j) / d j \<le> r"
      using N by (intro less_imp_le) simp
    show "\<forall>\<^sub>F n in sequentially. T n / d n < c"
      using eventually_ge_at_top[of N]
    proof eventually_elim
      case (elim n)
      have term_le: "d (n + m) \<le> d n * r ^ m" for m
        by (rule chain_le[OF r_pos bound_le]) (use elim in auto)
      have term_le': "d (k + n) \<le> d n * r ^ k" for k
        using term_le[of k] by (simp add: add.commute)
      have "T n \<le> (\<Sum>k. d n * r ^ k)"
        unfolding T_def
        by (rule suminf_le[OF term_le' shift_summable[of n] geom_summable[OF r_pos r_lt1]])
      also have "\<dots> = d n / (1 - r)"
        by (rule geom_sum[OF r_pos r_lt1])
      finally have "T n \<le> d n / (1 - r)" .
      hence "T n / d n \<le> 1 / (1 - r)"
        using pos[of n] by (simp add: field_simps)
      thus ?case
        using r_val by simp
    qed
  next
    fix c :: real
    assume c: "c < 1 / (1 - L)"
    show "\<forall>\<^sub>F n in sequentially. c < T n / d n"
    proof (cases "c \<le> 0")
      case True
      have "\<forall>x. c < T x / d x"
        using T_pos pos True by (auto intro: divide_pos_pos order_le_less_trans)
      thus ?thesis
        by (rule always_eventually)
    next
      case False
      hence c_pos: "0 < c"
        by simp
      have Lc: "1 - 1 / c < L"
        using c c_pos L by (simp add: divide_less_eq field_simps)
      define \<epsilon> where "\<epsilon> = min ((L - (1 - 1 / c)) / 2) (L / 2)"
      have \<epsilon>_le1: "\<epsilon> \<le> (L - (1 - 1 / c)) / 2"
        unfolding \<epsilon>_def by (rule min.cobounded1)
      have \<epsilon>_le2: "\<epsilon> \<le> L / 2"
        unfolding \<epsilon>_def by (rule min.cobounded2)
      have \<epsilon>_pos: "0 < \<epsilon>"
        using Lc L by (simp add: \<epsilon>_def)
      define r where "r = L - \<epsilon>"
      have r_pos: "0 < r"
        unfolding r_def using \<epsilon>_le2 L by linarith
      have r_lt_L: "r < L"
        unfolding r_def using \<epsilon>_pos by simp
      have r_lt1: "r < 1"
        using r_lt_L L by simp
      have r_gt: "1 - 1 / c < r"
        using \<epsilon>_le1 Lc unfolding r_def by argo
      have r_val: "c < 1 / (1 - r)"
        using r_gt c_pos r_lt_L L by (simp add: field_simps)
      have ev_le: "\<forall>\<^sub>F n in sequentially. r \<le> d (Suc n) / d n"
        using order_tendstoD(1)[OF ratio r_lt_L] by eventually_elim simp
      obtain N where N: "\<And>j. N \<le> j \<Longrightarrow> r \<le> d (Suc j) / d j"
        using ev_le unfolding eventually_sequentially by blast
      show "\<forall>\<^sub>F n in sequentially. c < T n / d n"
        using eventually_ge_at_top[of N]
      proof eventually_elim
        case (elim n)
        have term_ge: "d n * r ^ m \<le> d (n + m)" for m
          by (rule chain_ge[OF r_pos N]) (use elim in auto)
        have term_ge': "d n * r ^ k \<le> d (k + n)" for k
          using term_ge[of k] by (simp add: add.commute)
        have "d n / (1 - r) = (\<Sum>k. d n * r ^ k)"
          by (rule geom_sum[OF r_pos r_lt1, symmetric])
        also have "\<dots> \<le> T n"
          unfolding T_def
          by (rule suminf_le[OF term_ge' geom_summable[OF r_pos r_lt1] shift_summable[of n]])
        finally have "d n / (1 - r) \<le> T n" .
        hence "1 / (1 - r) \<le> T n / d n"
          using pos[of n] by (simp add: field_simps)
        thus ?case
          using r_val by simp
      qed
    qed
  qed
  show div_goal: "(\<lambda>n. (\<Sum>k. d (k + n)) / d n) \<longlonglongrightarrow> 1 / (1 - L)"
    using div_tendsto by (simp add: T_def)
  have d_over_T: "(\<lambda>n. d n / T n) \<longlonglongrightarrow> (1 - L)"
  proof -
    have inv: "(\<lambda>n. inverse (T n / d n)) \<longlonglongrightarrow> inverse (1 / (1 - L))"
      by (rule tendsto_inverse[OF div_tendsto]) (use L in simp)
    have eq1: "inverse (1 / (1 - L)) = 1 - L"
      by simp
    have eq2: "\<And>n. inverse (T n / d n) = d n / T n"
      using pos T_pos by (simp add: field_simps)
    show ?thesis
      using inv by (simp add: eq1 eq2)
  qed
  have T_ratio: "(\<lambda>n. T (Suc n) / T n) \<longlonglongrightarrow> L"
  proof -
    have eqn: "T (Suc n) / T n = 1 - d n / T n" for n
      using T_diff[of n] T_pos[of n] by (simp add: field_simps)
    have "(\<lambda>n. 1 - d n / T n) \<longlonglongrightarrow> 1 - (1 - L)"
      by (intro tendsto_diff[OF tendsto_const d_over_T])
    thus ?thesis
      using eqn by simp
  qed
  show "(\<lambda>n. (\<Sum>k. d (k + Suc n)) / (\<Sum>k. d (k + n))) \<longlonglongrightarrow> L"
    using T_ratio by (simp add: T_def)
qed

lemma geometric_ratio_sum_tendsto:
  fixes d :: "nat \<Rightarrow> real" and L :: real
  assumes pos: "\<And>n. 0 < d n"
    and L: "1 < L"
    and ratio: "(\<lambda>n. d (Suc n) / d n) \<longlonglongrightarrow> L"
  shows geometric_ratio_sum_div_last: "(\<lambda>n. (\<Sum>k\<le>n. d k) / d n) \<longlonglongrightarrow> L / (L - 1)"
    and geometric_ratio_sum_ratio: "(\<lambda>n. (\<Sum>k\<le>Suc n. d k) / (\<Sum>k\<le>n. d k)) \<longlonglongrightarrow> L"
proof -
  have d_at_top: "filterlim d at_top sequentially"
  proof -
    define r0 :: real where "r0 = (1 + L) / 2"
    have r0_bounds: "1 < r0" "r0 < L"
      using L by (simp_all add: r0_def)
    obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> r0 < d (Suc n) / d n"
      using order_tendstoD(1)[OF ratio r0_bounds(2)]
      unfolding eventually_sequentially by blast
    have grow: "r0 ^ k * d N \<le> d (N + k)" for k
    proof (induction k)
      case 0
      show ?case
        by simp
    next
      case (Suc k)
      have step: "r0 * d (N + k) < d (N + Suc k)"
        using N[of "N + k"] pos[of "N + k"] by (simp add: field_simps)
      have "r0 ^ Suc k * d N = r0 * (r0 ^ k * d N)"
        by simp
      also have "\<dots> \<le> r0 * d (N + k)"
        using Suc r0_bounds by (intro mult_left_mono) auto
      also have "\<dots> < d (N + Suc k)"
        by (rule step)
      finally show ?case
        by simp
    qed
    have r0k_at_top: "filterlim (\<lambda>k. r0 ^ k) at_top sequentially"
    proof -
      have inv0: "(\<lambda>k. inverse (r0 ^ k)) \<longlonglongrightarrow> 0"
        using r0_bounds(1) by (rule LIMSEQ_inverse_realpow_zero)
      have posr: "\<forall>\<^sub>F k in sequentially. 0 < inverse (r0 ^ k)"
        using r0_bounds(1) by (auto intro!: always_eventually)
      from filterlim_inverse_at_top[OF inv0 posr] show ?thesis
        by simp
    qed
    have shifted: "filterlim (\<lambda>k. d (N + k)) at_top sequentially"
    proof (rule filterlim_at_top_mono)
      have "((\<lambda>k::nat. d N) \<longlonglongrightarrow> d N)"
        by (rule tendsto_const)
      from filterlim_tendsto_pos_mult_at_top[OF this pos[of N] r0k_at_top]
      show "filterlim (\<lambda>k. d N * r0 ^ k) at_top sequentially" .
      show "\<forall>\<^sub>F k in sequentially. d N * r0 ^ k \<le> d (N + k)"
        using grow by (intro always_eventually) (simp add: mult.commute)
    qed
    show ?thesis
      unfolding filterlim_at_top
    proof
      fix Z :: real
      obtain M where M: "\<And>k. M \<le> k \<Longrightarrow> Z \<le> d (N + k)"
        using shifted unfolding filterlim_at_top eventually_sequentially by blast
      show "\<forall>\<^sub>F n in sequentially. Z \<le> d n"
        unfolding eventually_sequentially
      proof (intro exI[of _ "N + M"] allI impI)
        fix n
        assume "N + M \<le> n"
        hence "M \<le> n - N" "N \<le> n"
          by simp_all
        with M[of "n - N"] show "Z \<le> d n"
          by simp
      qed
    qed
  qed
  define S where "S = (\<lambda>n. sum d {..n})"
  have S_pos: "0 < S n" for n
    unfolding S_def by (rule sum_pos) (auto simp: pos)
  have S_split: "S n = sum d {..<N} + sum d {N..n}" if "N \<le> n" for N n
    using that
    by(subst sum.union_disjoint[symmetric])
      (auto simp: S_def intro!: arg_cong[where f="sum d"])
  note chain_ge = geometric_ratio_chain_ge[where d=d, OF pos]
  note chain_le = geometric_ratio_chain_le[where d=d, OF pos]
  have div_last: "(\<lambda>n. S n / d n) \<longlonglongrightarrow> L / (L - 1)"
  proof (rule order_tendstoI)
    fix c :: real
    assume c: "L / (L - 1) < c"
    have c_gt1: "1 < c"
      using L c by (smt (verit) divide_le_eq_1 le_divide_eq_1_pos)
    have Lc: "c / (c - 1) < L"
      using c c_gt1 L by (simp add: divide_less_eq field_simps)
    define \<epsilon> where "\<epsilon> = (L - c / (c - 1)) / 2"
    have \<epsilon>_pos: "0 < \<epsilon>"
      using Lc by (simp add: \<epsilon>_def)
    define r where "r = L - \<epsilon>"
    have cc1_gt1: "1 < c / (c - 1)"
      using c_gt1 by simp
    have r_bounds: "1 < r" "r < L"
    proof -
      have h: "(2::real) < L + c / (c - 1)"
        using L cc1_gt1 by linarith
      show "1 < r"
        unfolding r_def \<epsilon>_def using h by argo
      show "r < L"
        using \<epsilon>_pos by (simp add: r_def)
    qed
    have r_gt: "c / (c - 1) < r"
      using Lc \<epsilon>_def r_def by auto
    have r_c: "r / (r - 1) < c"
      using r_bounds(1) r_gt c_gt1 by (simp add: field_simps)
    obtain N where N: "\<And>j. N \<le> j \<Longrightarrow> r < d (Suc j) / d j"
      using order_tendstoD(1)[OF ratio r_bounds(2)]
      unfolding eventually_sequentially by blast
    have N_ge: "\<And>j. N \<le> j \<Longrightarrow> r \<le> d (Suc j) / d j"
      using N by (intro less_imp_le) simp
    have geo_bound: "(\<Sum>j\<le>m. (1 / r) ^ j) < r / (r - 1)" for m
    proof -
      have ne1: "(1::real) / r \<noteq> 1"
        using r_bounds(1) by simp
      have "(\<Sum>j\<le>m. (1 / r) ^ j) = (\<Sum>j<Suc m. (1 / r) ^ j)"
        by (simp add: lessThan_Suc_atMost)
      also have "\<dots> = (1 - (1 / r) ^ Suc m) / (1 - 1 / r)"
        using sum_gp_strict[of "1 / r" "Suc m"] ne1 by simp
      also have "\<dots> < 1 / (1 - 1 / r)"
      proof -
        have "0 < (1 / r) ^ Suc m"
          using r_bounds(1) by simp
        hence "1 - (1 / r) ^ Suc m < 1"
          by simp
        thus ?thesis
          using r_bounds(1) by (intro divide_strict_right_mono) auto
      qed
      also have "\<dots> = r / (r - 1)"
        using r_bounds(1) by (simp add: field_simps)
      finally show ?thesis .
    qed
    have sum_bound_upper: "sum d {N..n} \<le> d n * (\<Sum>j\<le>n - N. (1 / r) ^ j)"
      if n: "N \<le> n" for n
    proof -
      have term_bound: "d k \<le> d n * (1 / r) ^ (n - k)" if k: "k \<in> {N..n}" for k
      proof -
        have "d k * r ^ (n - k) \<le> d (k + (n - k))"
          by (rule chain_ge[OF _ N_ge]) (use k r_bounds in auto)
        also have "k + (n - k) = n"
          using k by simp
        finally have "d k * r ^ (n - k) \<le> d n" .
        thus ?thesis
          using r_bounds(1) by (simp add: field_simps)
      qed
      have "sum d {N..n} \<le> sum (\<lambda>k. d n * (1 / r) ^ (n - k)) {N..n}"
        by (rule sum_mono) (use term_bound in auto)
      also have "\<dots> = d n * sum (\<lambda>k. (1 / r) ^ (n - k)) {N..n}"
        by (simp add: sum_distrib_left)
      also have "sum (\<lambda>k. (1 / r) ^ (n - k)) {N..n} = sum (\<lambda>j. (1 / r) ^ j) {..n - N}"
        by (rule sum.reindex_bij_witness[where i = "\<lambda>k. n - k" and j = "\<lambda>j. n - j"])
          (use n in auto)
      finally show ?thesis
        by simp
    qed
    have S_bound: "S n \<le> sum d {..<N} + d n * (r / (r - 1))" if n: "N \<le> n" for n
    proof -
      have "S n = sum d {..<N} + sum d {N..n}"
        by (rule S_split[OF n])
      also have "\<dots> \<le> sum d {..<N} + d n * (\<Sum>j\<le>n - N. (1 / r) ^ j)"
        using sum_bound_upper[OF n] by simp
      also have "\<dots> < sum d {..<N} + d n * (r / (r - 1))"
        using geo_bound[of "n - N"] pos[of n]
        by (intro add_strict_left_mono mult_strict_left_mono) auto
      finally show ?thesis
        by simp
    qed
    have const_over_d: "(\<lambda>n. sum d {..<N} / d n) \<longlonglongrightarrow> 0"
    proof -
      have "(\<lambda>n. inverse (d n)) \<longlonglongrightarrow> 0"
        using d_at_top by (rule tendsto_inverse_0_at_top)
      hence "(\<lambda>n. sum d {..<N} * inverse (d n)) \<longlonglongrightarrow> sum d {..<N} * 0"
        by (intro tendsto_mult tendsto_const)
      thus ?thesis
        by (simp add: inverse_eq_divide)
    qed
    have gap_pos: "0 < c - r / (r - 1)"
      using r_c by simp
    have ev_small: "\<forall>\<^sub>F n in sequentially. sum d {..<N} / d n < c - r / (r - 1)"
      using order_tendstoD(2)[OF const_over_d gap_pos] .
    show "\<forall>\<^sub>F n in sequentially. S n / d n < c"
      using eventually_ge_at_top[of N] ev_small
    proof eventually_elim
      case (elim n)
      have "S n / d n \<le> sum d {..<N} / d n + r / (r - 1)"
        using S_bound[OF elim(1)] pos[of n] by (simp add: field_simps)
      also have "\<dots> < c"
        using elim(2) by simp
      finally show ?case .
    qed
  next
    fix c :: real
    assume c: "c < L / (L - 1)"
    show "\<forall>\<^sub>F n in sequentially. c < S n / d n"
    proof (cases "c \<le> 1")
      case True
      show ?thesis
        using eventually_ge_at_top[of 1]
      proof eventually_elim
        case (elim n)
        have "S n = sum d {..<n} + d n"
          unfolding S_def by (simp add: lessThan_Suc_atMost[symmetric])
        moreover have "0 < sum d {..<n}"
          using pos elim by(auto intro!: sum_pos simp: lessThan_empty_iff)
        ultimately have "d n < S n"
          by simp
        hence "1 < S n / d n"
          using pos[of n] by (simp add: field_simps)
        with True show ?case
          by simp
      qed
    next
      case False
      hence c_gt1: "1 < c"
        by simp
      have cc1: "L < c / (c - 1)"
      proof -
        have "c * (L - 1) < L / (L - 1) * (L - 1)"
          using c L by (intro mult_strict_right_mono) auto
        hence step1: "c * (L - 1) < L"
          using L by simp
        have step2: "L * (c - 1) < c"
          using step1 by argo
        show ?thesis
          using step2 c_gt1 by (simp add: pos_less_divide_eq)
      qed
      define \<epsilon> where "\<epsilon> = (c / (c - 1) - L) / 2"
      have \<epsilon>_pos: "0 < \<epsilon>"
        using cc1 by (simp add: \<epsilon>_def)
      define r where "r = L + \<epsilon>"
      have r_bounds: "1 < r"
        using L \<epsilon>_pos by (simp add: r_def)
      have r_lt: "r < c / (c - 1)"
        unfolding r_def \<epsilon>_def using cc1 by argo
      have r_c: "c < r / (r - 1)"
      proof -
        have "r * (c - 1) < c / (c - 1) * (c - 1)"
          using r_lt c_gt1 by (intro mult_strict_right_mono) auto
        hence step1: "r * (c - 1) < c"
          using c_gt1 by simp
        have step2: "c * (r - 1) < r"
          using step1 by argo
        show ?thesis
          using step2 r_bounds by (simp add: pos_less_divide_eq)
      qed
      have L_lt_r: "L < r"
        using \<epsilon>_pos by (simp add: r_def)
      obtain N where N: "\<And>j. N \<le> j \<Longrightarrow> d (Suc j) / d j < r"
        using order_tendstoD(2)[OF ratio L_lt_r]
        unfolding eventually_sequentially by blast
      have N_le: "\<And>j. N \<le> j \<Longrightarrow> d (Suc j) / d j \<le> r"
        using N by (intro less_imp_le) simp
      have sum_bound_lower: "d n * (\<Sum>j\<le>n - N. (1 / r) ^ j) \<le> sum d {N..n}"
        if n: "N \<le> n" for n
      proof -
        have term_bound: "d n * (1 / r) ^ (n - k) \<le> d k" if k: "k \<in> {N..n}" for k
        proof -
          have "d (k + (n - k)) \<le> d k * r ^ (n - k)"
            by (rule chain_le[OF _ N_le]) (use k r_bounds in auto)
          also have "k + (n - k) = n"
            using k by simp
          finally have "d n \<le> d k * r ^ (n - k)" .
          thus ?thesis
            using r_bounds by (simp add: field_simps)
        qed
        have "d n * sum (\<lambda>k. (1 / r) ^ (n - k)) {N..n} \<le> sum d {N..n}"
          unfolding sum_distrib_left by (rule sum_mono) (use term_bound in auto)
        moreover have "sum (\<lambda>k. (1 / r) ^ (n - k)) {N..n} = sum (\<lambda>j. (1 / r) ^ j) {..n - N}"
          by (rule sum.reindex_bij_witness[where i = "\<lambda>k. n - k" and j = "\<lambda>j. n - j"])
            (use n in auto)
        ultimately show ?thesis
          by simp
      qed
      have S_bound: "d n * (\<Sum>j\<le>n - N. (1 / r) ^ j) \<le> S n" if n: "N \<le> n" for n
      proof -
        have "d n * (\<Sum>j\<le>n - N. (1 / r) ^ j) \<le> sum d {N..n}"
          by (rule sum_bound_lower[OF n])
        also have "\<dots> \<le> sum d {..<N} + sum d {N..n}"
          using sum_nonneg[of "{..<N}" d] pos by (simp add: less_imp_le)
        also have "\<dots> = S n"
          using S_split[OF n] by simp
        finally show ?thesis .
      qed
      have geo_tendsto: "(\<lambda>m. \<Sum>j\<le>m. (1 / r) ^ j) \<longlonglongrightarrow> r / (r - 1)"
      proof -
        have "norm (1 / r) < 1"
          using r_bounds by simp
        from geometric_sums[OF this]
        have "(\<lambda>n. \<Sum>i<n. (1 / r) ^ i) \<longlonglongrightarrow> 1 / (1 - 1 / r)"
          unfolding sums_def by simp
        from LIMSEQ_Suc[OF this]
        show ?thesis
          using r_bounds by (simp add: lessThan_Suc_atMost field_simps)
      qed
      have ev_close: "\<forall>\<^sub>F m in sequentially. r / (r - 1) - (r / (r - 1) - c)
                                                   < (\<Sum>j\<le>m. (1 / r) ^ j)"
        using order_tendstoD(1)[OF geo_tendsto, of "r / (r - 1) - (r / (r - 1) - c)"]
          r_c by simp
      obtain M where M: "\<And>m. M \<le> m \<Longrightarrow>
          r / (r - 1) - (r / (r - 1) - c) < (\<Sum>j\<le>m. (1 / r) ^ j)"
        using ev_close unfolding eventually_sequentially by blast
      show ?thesis
        unfolding eventually_sequentially
      proof (intro exI[of _ "N + M"] allI impI)
        fix n
        assume "N + M \<le> n"
        hence nN: "N \<le> n" and Mn: "M \<le> n - N"
          by simp_all
        have "d n * (r / (r - 1) - (r / (r - 1) - c)) < d n * (\<Sum>j\<le>n - N. (1 / r) ^ j)"
          using M[OF Mn] pos[of n] by (intro mult_strict_left_mono) auto
        also have "\<dots> \<le> S n"
          by (rule S_bound[OF nN])
        finally have "d n * c < S n"
          by simp
        thus "c < S n / d n"
          using pos[of n] by (simp add: field_simps)
      qed
    qed
  qed
  show geometric_ratio_sum_div_last: "(\<lambda>n. (\<Sum>k\<le>n. d k) / d n) \<longlonglongrightarrow> L / (L - 1)"
    using div_last by (simp add: S_def)
  show geometric_ratio_sum_ratio: "(\<lambda>n. (\<Sum>k\<le>Suc n. d k) / (\<Sum>k\<le>n. d k)) \<longlonglongrightarrow> L"
  proof -
    have L1ne0: "L / (L - 1) \<noteq> 0"
      using L by simp
    have d_div_S: "(\<lambda>n. d n / S n) \<longlonglongrightarrow> (L - 1) / L"
    proof -
      have "(\<lambda>n. inverse (S n / d n)) \<longlonglongrightarrow> inverse (L / (L - 1))"
        by (rule tendsto_inverse[OF div_last L1ne0])
      moreover have "\<And>n. inverse (S n / d n) = d n / S n"
        using pos S_pos by (simp add: inverse_eq_divide)
      moreover have "inverse (L / (L - 1)) = (L - 1) / L"
        using L by (simp add: field_simps)
      ultimately show ?thesis
        by simp
    qed
    note prod_lim = tendsto_mult[OF ratio d_div_S]
    have step: "(\<lambda>n. 1 + (d (Suc n) / d n) * (d n / S n)) \<longlonglongrightarrow> 1 + L * ((L - 1) / L)"
      by (intro tendsto_add tendsto_const prod_lim)
    have eq: "1 + (d (Suc n) / d n) * (d n / S n) = S (Suc n) / S n" for n
    proof -
      have "(d (Suc n) / d n) * (d n / S n) = d (Suc n) / S n"
        using pos[of n] by (simp add: field_simps)
      hence "1 + (d (Suc n) / d n) * (d n / S n) = (S n + d (Suc n)) / S n"
        using S_pos[of n] by (simp add: field_simps)
      also have "S n + d (Suc n) = S (Suc n)"
        unfolding S_def by simp
      finally show ?thesis .
    qed
    have val_eq: "1 + L * ((L - 1) / L) = L"
      using L by (simp add: field_simps)
    have "(\<lambda>n. S (Suc n) / S n) \<longlonglongrightarrow> L"
      using step unfolding eq val_eq .
    thus ?thesis
      by (simp add: S_def)
  qed
qed

lemma geometric_ratio_forward_telescope:
  fixes g :: "real \<Rightarrow> real" and Z c :: real
  assumes power_ratio: "\<And>t0. 0 < t0 \<Longrightarrow> (\<lambda>n. g (t0 * Z ^ Suc n) / g (t0 * Z ^ n)) \<longlonglongrightarrow> c"
    and Z: "1 < Z" and c: "c \<noteq> 0"
  shows "(\<lambda>n. g (Z ^ (n + j)) / g (Z ^ n)) \<longlonglongrightarrow> c ^ j"
proof (induction j)
  case 0
  have ratio0: "(\<lambda>n. g (Z ^ Suc n) / g (Z ^ n)) \<longlonglongrightarrow> c"
    using power_ratio[OF zero_less_one] by simp
  have ev_ne0: "\<forall>\<^sub>F n in sequentially. g (Z ^ n) \<noteq> 0"
    using tendsto_imp_eventually_ne[OF ratio0 c] by eventually_elim force
  have eq0: "\<forall>\<^sub>F n in sequentially. (1::real) = g (Z ^ (n + 0)) / g (Z ^ n)"
    using ev_ne0 by eventually_elim simp
  show ?case
    using Lim_transform_eventually[OF tendsto_const eq0] by simp
next
  case (Suc j)
  have Zjpos: "0 < Z ^ j"
    using Z by simp
  have step: "(\<lambda>n. g (Z ^ (Suc n + j)) / g (Z ^ (n + j))) \<longlonglongrightarrow> c"
    using power_ratio[OF Zjpos] by (simp add: algebra_simps power_add)
  have ev_ne: "\<forall>\<^sub>F n in sequentially. g (Z ^ (n + j)) \<noteq> 0"
    using tendsto_imp_eventually_ne[OF step c] by eventually_elim force
  have eq: "\<forall>\<^sub>F n in sequentially.
      g (Z ^ (Suc n + j)) / g (Z ^ (n + j)) * (g (Z ^ (n + j)) / g (Z ^ n))
        = g (Z ^ (Suc n + j)) / g (Z ^ n)"
    by(auto intro!: eventually_mono[OF ev_ne])
  show ?case
    using Lim_transform_eventually[OF tendsto_mult[OF step Suc.IH] eq] by simp
qed

lemma monotone_geometric_ratio_imp_ratio:
  fixes g :: "real \<Rightarrow> real" and \<rho> y :: real
  assumes gmono: "\<And>s t. 1 < s \<Longrightarrow> s \<le> t \<Longrightarrow> g s \<le> g t"
    and gpos: "\<forall>\<^sub>F t in at_top. 0 < g t"
    and rho: "0 < \<rho>"
    and power_ratio: "\<And>Z t0. 1 < Z \<Longrightarrow> 0 < t0 \<Longrightarrow>
        (\<lambda>n. g (t0 * Z ^ Suc n) / g (t0 * Z ^ n)) \<longlonglongrightarrow> Z powr \<rho>"
    and y: "0 < y"
  shows "((\<lambda>t. g (t * y) / g t) \<longlongrightarrow> y powr \<rho>) at_top"
proof -
  have Zseq_at_top: "filterlim (\<lambda>n. Z ^ n) at_top sequentially"
    if Z: "1 < Z" for Z :: real
    by (rule LIMSEQ_power_at_top[OF Z])
  have n_at_top: "filterlim (\<lambda>t::real. nat \<lfloor>log Z t\<rfloor>) at_top at_top"
    if Z: "1 < Z" for Z :: real
    using Z by (rule floor_log_at_top)
  have Zn_cont_at_top: "filterlim (\<lambda>t::real. Z ^ nat \<lfloor>log Z t\<rfloor>) at_top at_top"
    if Z: "1 < Z" for Z :: real
    by (rule filterlim_compose[OF Zseq_at_top[OF Z] n_at_top[OF Z]])
  have Un_pos_ev: "\<forall>\<^sub>F t in at_top. 0 < g (Z ^ nat \<lfloor>log Z t\<rfloor>)" if Z: "1 < Z"
    for Z :: real
    using eventually_compose_filterlim[OF gpos Zn_cont_at_top[OF Z]] .
  have Zpowr_ne: "Z powr \<rho> \<noteq> 0" if Z: "1 < Z" for Z :: real
    using Z by simp
  have telescope: "(\<lambda>n. g (Z ^ (n + j)) / g (Z ^ n))
                    \<longlonglongrightarrow> (Z powr \<rho>) ^ j"
    if Z: "1 < Z" for Z :: real and j :: nat
    by (rule geometric_ratio_forward_telescope[OF power_ratio[OF Z] Z Zpowr_ne[OF Z]])
  have telescope_cont: "((\<lambda>t. g (Z ^ (nat \<lfloor>log Z t\<rfloor> + j))
                                / g (Z ^ nat \<lfloor>log Z t\<rfloor>))
                         \<longlongrightarrow> (Z powr \<rho>) ^ j) at_top"
    if Z: "1 < Z" for Z :: real and j :: nat
    by (rule filterlim_compose[OF telescope[OF Z] n_at_top[OF Z]])
  have t_bracket: "\<forall>\<^sub>F t in at_top. Z ^ nat \<lfloor>log Z t\<rfloor> \<le> t \<and> t < Z ^ (nat \<lfloor>log Z t\<rfloor> + 1)"
    if Z: "1 < Z" for Z :: real
    using eventually_ge_at_top[of "1::real"]
    by eventually_elim (use power_of_nat_log_le power_of_nat_log_less_Suc Z in auto)
  have n_ge1: "\<forall>\<^sub>F t in at_top. 1 \<le> nat \<lfloor>log Z t\<rfloor>" if Z: "1 < Z" for Z :: real
    using n_at_top[OF Z, unfolded filterlim_at_top, rule_format, of 1]
    by eventually_elim simp

  have sandwich_upper: "\<forall>\<^sub>F t in at_top. g (t * y) / g t
               \<le> g (Z ^ (nat \<lfloor>log Z t\<rfloor> + m + 2)) / g (Z ^ nat \<lfloor>log Z t\<rfloor>)"
    if y1: "1 \<le> y" and Z1: "1 < Z" and mlo: "Z ^ m \<le> y" and mhi: "y < Z ^ (m + 1)"
    for Z :: real and m :: nat and y :: real
    using t_bracket[OF Z1] n_ge1[OF Z1] Un_pos_ev[OF Z1]
  proof eventually_elim
    case (elim t)
    define n where "n = nat \<lfloor>log Z t\<rfloor>"
    have tb1: "Z ^ n \<le> t" and tb2: "t < Z ^ (n + 1)"
      using elim unfolding n_def by auto
    have n1: "1 \<le> n"
      using elim unfolding n_def by simp
    have Zn_gt1: "1 < Z ^ n"
      using Z1 n1 by simp
    have Un_pos: "0 < g (Z ^ n)"
      using elim unfolding n_def by simp
    have tpos: "0 < t"
      using Zn_gt1 tb1 by simp
    have ypos: "0 < y"
      using y1 by simp
    have ty_lt: "t * y < Z ^ (n + m + 2)"
    proof -
      have "t * y < Z ^ (n + 1) * Z ^ (m + 1)"
        using tb2 mhi tpos ypos by (intro mult_strict_mono') auto
      also have "\<dots> = Z ^ (n + m + 2)"
        by (simp add: power_add)
      finally show ?thesis .
    qed
    have t_gt1: "1 < t"
      using Zn_gt1 tb1 by simp
    have ty_gt1: "1 < t * y"
      using y1 t_gt1 mult_left_mono[of 1 y t] by linarith
    have Uty_le: "g (t * y) \<le> g (Z ^ (n + m + 2))"
      using gmono[OF ty_gt1] ty_lt by simp
    have Ut_ge: "g (Z ^ n) \<le> g t"
      using gmono[OF Zn_gt1 tb1] .
    have Ut_pos: "0 < g t"
      using Un_pos Ut_ge by simp
    have Unm2_ge: "Z ^ n \<le> Z ^ (n + m + 2)"
      using Z1 by (intro power_increasing) auto
    have Unm2_gt1: "1 < Z ^ (n + m + 2)"
      using Unm2_ge Zn_gt1 by simp
    have Utym2_pos: "0 < g (Z ^ (n + m + 2))"
      using gmono[OF Zn_gt1 Unm2_ge] Un_pos by simp
    show ?case
      unfolding n_def[symmetric]
      using frac_le[OF Utym2_pos[THEN less_imp_le] Uty_le Un_pos Ut_ge] .
  qed
  have sandwich_lower:
    "\<forall>\<^sub>F t in at_top. g (Z ^ (nat \<lfloor>log Z t\<rfloor> + m)) / g (Z ^ (nat \<lfloor>log Z t\<rfloor> + 1))
       \<le> g (t * y) / g t"
    if y1: "1 \<le> y" and Z1: "1 < Z" and mlo: "Z ^ m \<le> y"
    for Z :: real and m :: nat and y :: real
    using t_bracket[OF Z1] n_ge1[OF Z1] Un_pos_ev[OF Z1]
  proof eventually_elim
    case (elim t)
    define n where "n = nat \<lfloor>log Z t\<rfloor>"
    have tb1: "Z ^ n \<le> t" and tb2: "t < Z ^ (n + 1)"
      using elim unfolding n_def by auto
    have n1: "1 \<le> n"
      using elim unfolding n_def by simp
    have Zn_gt1: "1 < Z ^ n"
      using Z1 n1 by simp
    have Un_pos: "0 < g (Z ^ n)"
      using elim unfolding n_def by simp
    have Znm_ge: "Z ^ n \<le> Z ^ (n + m)"
      using Z1 by (intro power_increasing) auto
    have Znm_gt1: "1 < Z ^ (n + m)"
      using Znm_ge Zn_gt1 by simp
    have ty_ge: "Z ^ (n + m) \<le> t * y"
      using tb1 mlo Z1 Zn_gt1 by(auto intro!: mult_mono simp: power_add)
    have Unm_pos: "0 < g (Z ^ (n + m))"
      using gmono[OF Zn_gt1 Znm_ge] Un_pos by simp
    have t_gt1: "1 < t"
      using Zn_gt1 tb1 by simp
    show ?case
      unfolding n_def[symmetric]
      by(intro frac_le[OF less_imp_le] gmono Znm_gt1 ty_ge
          t_gt1 tb2[THEN less_imp_le]
          order.strict_trans2[OF Un_pos gmono[OF Zn_gt1 tb1]]
          order.strict_trans2[OF Unm_pos gmono[OF Znm_gt1 ty_ge]])
  qed

  have main: "((\<lambda>t. g (t * y) / g t) \<longlongrightarrow> y powr \<rho>) at_top"
    if y1: "1 \<le> y" for y
  proof -
    have Z_of_ratio: "\<exists>Z. 1 < Z \<and> Z ^ 2 < R" if Rgt1: "1 < R" for R :: real
    proof -
      define B where "B = sqrt R"
      define Z where "Z = (1 + B) / 2"
      have B1: "1 < B"
        unfolding B_def using real_sqrt_less_mono[OF Rgt1] by simp
      have Zbounds1: "1 < Z"
        unfolding Z_def using B1 by argo
      have Zbounds2: "Z < B"
        unfolding Z_def using B1 by argo
      have ZltB2: "Z ^ 2 < B ^ 2"
        using Zbounds1 Zbounds2 by (simp add: power_strict_mono)
      have B2: "B ^ 2 = R"
        unfolding B_def using Rgt1 by simp
      show ?thesis
        using Zbounds1 ZltB2 B2 by (intro exI[of _ Z]) simp
    qed
    show ?thesis
    proof (rule order_tendstoI)
      fix a :: real
      assume a: "a < y powr \<rho>"
      show "\<forall>\<^sub>F t in at_top. a < g (t * y) / g t"
      proof (cases "a \<le> 0")
        case True
        have ypos: "0 < y"
          using y1 by simp
        have y_at_top: "filterlim (\<lambda>t::real. t * y) at_top at_top"
          using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of y] ypos filterlim_ident]
          by (simp add: mult.commute)
        have ev_pos: "\<forall>\<^sub>F t in at_top. 0 < g (t * y) / g t"
          using eventually_compose_filterlim[OF gpos y_at_top] gpos
          by eventually_elim simp
        show ?thesis
          using ev_pos
          by eventually_elim (use True in linarith)
      next
        case False
        hence apos: "0 < a"
          by simp
        have alt: "a powr (1 / \<rho>) < y"
          using powr_less_mono2[OF _ _ a, of "1 / \<rho>"] apos rho y1
          by (simp add: powr_powr)
        have ratio_gt1: "1 < y / a powr (1 / \<rho>)"
          using alt apos by (simp add: field_simps)
        obtain Z where Zbounds1: "1 < Z" and ZltR: "Z ^ 2 < y / a powr (1 / \<rho>)"
          using Z_of_ratio[OF ratio_gt1] by auto
        have Zpos: "0 < Z"
          using Zbounds1 by simp
        have key: "a < (y / Z ^ 2) powr \<rho>"
        proof -
          have "a powr (1 / \<rho>) < y / Z ^ 2"
            using ZltR Zpos apos by (simp add: field_simps)
          hence "(a powr (1 / \<rho>)) powr \<rho> < (y / Z ^ 2) powr \<rho>"
            using rho apos Zpos y1 by (intro powr_less_mono2) auto
          also have "(a powr (1 / \<rho>)) powr \<rho> = a"
            using rho apos by (simp add: powr_powr)
          finally show ?thesis .
        qed
        define m where "m = nat \<lfloor>log Z y\<rfloor>"
        have ybracket: "Z ^ m \<le> y" "y < Z ^ (m + 1)"
          using  power_of_nat_log_le power_of_nat_log_less_Suc Zbounds1 y1
          unfolding m_def by auto
        have tel_m: "((\<lambda>t. g (Z ^ (nat \<lfloor>log Z t\<rfloor> + m))
                            / g (Z ^ nat \<lfloor>log Z t\<rfloor>)) \<longlongrightarrow> (Z powr \<rho>) ^ m) at_top"
          using telescope_cont[OF Zbounds1, of m] .
        have tel_1: "((\<lambda>t. g (Z ^ (nat \<lfloor>log Z t\<rfloor> + 1))
                            / g (Z ^ nat \<lfloor>log Z t\<rfloor>)) \<longlongrightarrow> Z powr \<rho>) at_top"
          using telescope_cont[OF Zbounds1, of 1] by simp
        have Z\<rho>ne: "Z powr \<rho> \<noteq> 0"
          using Zpos by simp
        have div_lim: "((\<lambda>t. (g (Z ^ (nat \<lfloor>log Z t\<rfloor> + m))
                              / g (Z ^ nat \<lfloor>log Z t\<rfloor>))
                            / (g (Z ^ (nat \<lfloor>log Z t\<rfloor> + 1))
                              / g (Z ^ nat \<lfloor>log Z t\<rfloor>)))
                       \<longlongrightarrow> (Z powr \<rho>) ^ m / Z powr \<rho>) at_top"
          by (intro tendsto_divide[OF tel_m tel_1 Z\<rho>ne])
        have eq_ev: "\<forall>\<^sub>F t in at_top. (g (Z ^ (nat \<lfloor>log Z t\<rfloor> + m)) / g (Z ^ nat \<lfloor>log Z t\<rfloor>))
                   / (g (Z ^ (nat \<lfloor>log Z t\<rfloor> + 1)) / g (Z ^ nat \<lfloor>log Z t\<rfloor>))
                 = g (Z ^ (nat \<lfloor>log Z t\<rfloor> + m)) / g (Z ^ (nat \<lfloor>log Z t\<rfloor> + 1))"
          using Un_pos_ev[OF Zbounds1]
          by eventually_elim (simp add: field_simps)
        have ratio_lim: "((\<lambda>t. g (Z ^ (nat \<lfloor>log Z t\<rfloor> + m))
                                / g (Z ^ (nat \<lfloor>log Z t\<rfloor> + 1)))
                          \<longlongrightarrow> (Z powr \<rho>) ^ m / Z powr \<rho>) at_top"
          using Lim_transform_eventually[OF div_lim eq_ev] .
        have val_gt: "a < (Z powr \<rho>) ^ m / Z powr \<rho>"
        proof -
          have "y / Z ^ 2 < Z ^ m / Z"
            using ybracket(2) Zpos by (simp add: field_simps power2_eq_square)
          moreover have "0 \<le> y / Z ^ 2"
            using y1 Zpos by simp
          ultimately have "(y / Z ^ 2) powr \<rho> < (Z ^ m / Z) powr \<rho>"
            using rho by (intro powr_less_mono2)
          also have "(Z ^ m / Z) powr \<rho> = (Z ^ m) powr \<rho> / Z powr \<rho>"
            by (simp add: powr_divide)
          also have "(Z ^ m) powr \<rho> = (Z powr \<rho>) ^ m"
            by (metis Zpos less_eq_real_def linorder_not_less powr_power powr_powr powr_realpow)
          finally show ?thesis
            using key by simp
        qed
        have ev_val: "\<forall>\<^sub>F t in at_top. a <
                 g (Z ^ (nat \<lfloor>log Z t\<rfloor> + m)) / g (Z ^ (nat \<lfloor>log Z t\<rfloor> + 1))"
          using order_tendstoD(1)[OF ratio_lim val_gt] .
        show ?thesis
          using ev_val sandwich_lower[OF y1 Zbounds1 ybracket(1)]
          by eventually_elim linarith
      qed
    next
      fix c :: real
      assume c: "y powr \<rho> < c"
      have cpos: "0 < c"
        by(auto intro!: order.strict_trans1[OF _ c])
      have alt: "y < c powr (1 / \<rho>)"
        using powr_less_mono2[OF _ _ c, of "1 / \<rho>"] rho y1
        by (simp add: powr_powr)
      have ratio_gt1: "1 < c powr (1 / \<rho>) / y"
        using alt y1 by (simp add: field_simps)
      obtain Z where Zbounds1: "1 < Z" and ZltR: "Z ^ 2 < c powr (1 / \<rho>) / y"
        using Z_of_ratio[OF ratio_gt1] by auto
      have Zpos: "0 < Z"
        using Zbounds1 by simp
      have key: "(y * Z ^ 2) powr \<rho> < c"
      proof -
        have "y * Z ^ 2 < c powr (1 / \<rho>)"
          using ZltR y1 by (simp add: field_simps)
        hence "(y * Z ^ 2) powr \<rho> < (c powr (1 / \<rho>)) powr \<rho>"
          using rho y1 Zpos by (intro powr_less_mono2) auto
        also have "(c powr (1 / \<rho>)) powr \<rho> = c"
          using rho cpos by (simp add: powr_powr)
        finally show ?thesis .
      qed
      define m where "m = nat \<lfloor>log Z y\<rfloor>"
      have ybracket: "Z ^ m \<le> y" "y < Z ^ (m + 1)"
        using  power_of_nat_log_le power_of_nat_log_less_Suc Zbounds1 y1
        unfolding m_def by auto
      have tel_m2: "((\<lambda>t. g (Z ^ (nat \<lfloor>log Z t\<rfloor> + (m + 2)))
                          / g (Z ^ nat \<lfloor>log Z t\<rfloor>)) \<longlongrightarrow> (Z powr \<rho>) ^ (m + 2)) at_top"
        using telescope_cont[OF Zbounds1, of "m + 2"] .
      have val_lt: "(Z powr \<rho>) ^ (m + 2) < c"
      proof -
        have step1: "Z ^ (m + 2) = Z ^ m * Z ^ 2"
          by (rule power_add)
        have step2: "Z ^ m * Z ^ 2 \<le> y * Z ^ 2"
          using ybracket(1) Zpos by (intro mult_right_mono) auto
        have step3: "Z ^ (m + 2) \<le> y * Z ^ 2"
          unfolding step1 by (rule step2)
        have step3pos: "0 \<le> Z ^ (m + 2)"
          using Zpos by simp
        have step4: "(Z ^ (m + 2)) powr \<rho> \<le> (y * Z ^ 2) powr \<rho>"
          by (rule powr_mono2[OF less_imp_le[OF rho] step3pos step3])
        have step5: "(Z ^ (m + 2)) powr \<rho> < c"
          using step4 key by linarith
        have step6: "(Z ^ (m + 2)) powr \<rho> = (Z powr \<rho>) ^ (m + 2)"
          by (metis Zpos less_eq_real_def linorder_not_less powr_power powr_powr powr_realpow)
        show ?thesis
          using step5 step6 by simp
      qed
      have ev_val:
        "\<forall>\<^sub>F t in at_top. g (Z ^ (nat \<lfloor>log Z t\<rfloor> + (m + 2))) / g (Z ^ nat \<lfloor>log Z t\<rfloor>) < c"
        using order_tendstoD(2)[OF tel_m2 val_lt] .
      have ev_val':
        "\<forall>\<^sub>F t in at_top. g (Z ^ (nat \<lfloor>log Z t\<rfloor> + m + 2)) / g (Z ^ nat \<lfloor>log Z t\<rfloor>) < c"
        using ev_val by (simp add: add.assoc)
      show "\<forall>\<^sub>F t in at_top. g (t * y) / g t < c"
        using ev_val' sandwich_upper[OF y1 Zbounds1 ybracket(1) ybracket(2)]
        by eventually_elim linarith
    qed
  qed
  show ?thesis
  proof (cases "1 \<le> y")
    case False
    hence y01: "0 < y" "y < 1"
      using y by auto
    have yinv1: "1 \<le> 1 / y"
      using y01 by (simp add: field_simps)
    have base: "((\<lambda>t. g (t * (1 / y)) / g t)
                \<longlongrightarrow> (1 / y) powr \<rho>) at_top"
      using main[OF yinv1] .
    have ty_at_top: "filterlim (\<lambda>s::real. s * y) at_top at_top"
      using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of y] y01(1) filterlim_ident]
      by (simp add: mult.commute)
    have comp: "((\<lambda>s. g (s * y * (1 / y)) / g (s * y))
                   \<longlongrightarrow> (1 / y) powr \<rho>) at_top"
      by (rule filterlim_compose[OF base ty_at_top])
    have simp1: "s * y * (1 / y) = s" for s :: real
      using y01 by simp
    have base2: "((\<lambda>s. g s / g (s * y)) \<longlongrightarrow> (1 / y) powr \<rho>) at_top"
      using comp y01 by (simp add: simp1)
    have nz: "(1 / y) powr \<rho> \<noteq> 0"
      using y01 by simp
    have recip: "((\<lambda>s. inverse (g s / g (s * y)))
                    \<longlongrightarrow> inverse ((1 / y) powr \<rho>)) at_top"
      by (rule tendsto_inverse[OF base2 nz])
    note ev_ne = tendsto_imp_eventually_ne[OF base2 nz]
    have eq: "\<forall>\<^sub>F s in at_top. inverse (g s / g (s * y))
                       = g (s * y) / g s"
      using ev_ne by eventually_elim (simp add: field_simps)
    have final: "((\<lambda>s. g (s * y) / g s)
                    \<longlongrightarrow> inverse ((1 / y) powr \<rho>)) at_top"
      using Lim_transform_eventually[OF recip eq] .
    have val: "inverse ((1 / y) powr \<rho>) = y powr \<rho>"
      by (simp add: powr_divide)
    show ?thesis
      using final val by simp
  qed(simp add: main)
qed

lemma galois_inverse_ratio_tendsto:
  fixes W s :: "real \<Rightarrow> real" and \<rho> x :: real
  assumes W: "filterlim W at_top at_top"
    and s: "filterlim s at_top at_top"
    and s_pos: "\<And>w. 0 < w \<Longrightarrow> 0 < s w"
    and le_iff: "\<And>t w. 1 < t \<Longrightarrow> (W t \<le> w) = (t \<le> s w)"
    and rho[arith]: "0 < \<rho>"
    and lim: "\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. W (t * y) / W t) \<longlongrightarrow> y powr \<rho>) at_top"
    and x[arith]: "0 < x"
  shows "((\<lambda>u. s (u * x) / s u) \<longlongrightarrow> x powr (1 / \<rho>)) at_top"
proof -
  have galois_strict: "(w < W t) = (s w < t)" if t1: "1 < t" for t w
    using le_iff[OF t1, of w] by linarith
  have s_gt1: "\<forall>\<^sub>F u in at_top. 1 < s u"
    using s unfolding filterlim_at_top_dense by blast
  have Ws_pos: "\<forall>\<^sub>F u in at_top. 0 < W (s u)"
    using filterlim_compose[OF W s] unfolding filterlim_at_top_dense by blast
  have s_gt1_mult: "\<forall>\<^sub>F u in at_top. 1 < s u * c" if c: "0 < c" for c
  proof -
    have "\<forall>\<^sub>F u in at_top. 1 / c < s u"
      using s unfolding filterlim_at_top_dense by blast
    thus ?thesis
      by eventually_elim (use c in "simp add: field_simps")
  qed
  have u_pos: "\<forall>\<^sub>F u in at_top. (0::real) < u"
    by (rule eventually_gt_at_top)
  have upper: "\<forall>\<^sub>F u in at_top. W (s u) \<le> u"
    using s_gt1 by eventually_elim (use le_iff in auto)
  have near_inv: "((\<lambda>u. W (s u) / u) \<longlongrightarrow> 1) at_top"
    unfolding tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    define e' where "e' = min (1 / 2) e"
    have e'_pos[arith]: "0 < e'" and e'_le: "e' \<le> e" and e'_lt1: "e' < 1"
      using e by (simp_all add: e'_def)
    have cpos[arith]: "0 < 1 - e'"
      using e'_lt1 by simp
    have c_lt1: "1 - e' < 1"
      using e'_pos by simp
    define K where "K = (1 / (1 - e')) powr (1 / \<rho>)"
    have K_gt1[arith]: "1 < K"
      using rho cpos c_lt1 by (simp add: K_def)
    define \<delta> where "\<delta> = (K - 1) / 2"
    have \<delta>_pos[arith]: "0 < \<delta>"
      using K_gt1 by (simp add: \<delta>_def)
    have \<delta>1_pos: "0 < 1 + \<delta>"
      using \<delta>_pos by simp
    have \<delta>_lt_K: "1 + \<delta> < K"
      using K_gt1 by (simp add: \<delta>_def field_simps)
    have \<delta>_lt: "(1 + \<delta>) powr \<rho> < 1 / (1 - e')"
      using powr_less_mono2[OF rho _ \<delta>_lt_K] \<delta>_pos rho cpos
      by (simp add: K_def powr_powr)
    have ev_ratio: "\<forall>\<^sub>F u in at_top. W (s u * (1 + \<delta>)) / W (s u) < 1 / (1 - e')"
      using order_tendstoD(2)[OF filterlim_compose[OF lim[OF \<delta>1_pos] s] \<delta>_lt] .
    have ev_lower: "\<forall>\<^sub>F u in at_top. u < W (s u * (1 + \<delta>))"
      using s_gt1_mult[OF \<delta>1_pos] s_gt1
    proof eventually_elim
      case (elim u)
      hence "s u < s u * (1 + \<delta>)"
        using \<delta>_pos by simp
      thus ?case
        using galois_strict[OF elim(1), of u] by simp
    qed
    have lower: "\<forall>\<^sub>F u in at_top. 1 - e' < W (s u) / u"
      using ev_ratio ev_lower upper Ws_pos u_pos
    proof eventually_elim
      case (elim u)
      have "u / W (s u) < W (s u * (1 + \<delta>)) / W (s u)"
        using elim(2,4) by (rule divide_strict_right_mono)
      also have "\<dots> < 1 / (1 - e')"
        using elim(1) .
      finally have lt: "u / W (s u) < 1 / (1 - e')" .
      have "u * (1 - e') < W (s u)"
        using lt elim(4,5) cpos by (simp add: field_simps)
      thus ?case
        using elim(5) cpos by (simp add: field_simps)
    qed
    have e'1: "1 < 1 + e'"
      using e'_pos by simp
    have upperb: "\<forall>\<^sub>F u in at_top. W (s u) / u < 1 + e'"
      using upper u_pos
    proof eventually_elim
      case (elim u)
      have "W (s u) < u * (1 + e')"
        using elim(1) mult_strict_left_mono[OF e'1 elim(2)] by simp
      thus ?case
        using elim(2) by (simp add: divide_less_eq mult.commute)
    qed
    show "\<forall>\<^sub>F u in at_top. \<bar>W (s u) / u - 1\<bar> < e"
      using lower upperb
      by eventually_elim (use e'_le in linarith)
  qed
  have Winv_ratio: "((\<lambda>u. W (s u * y) / u) \<longlongrightarrow> y powr \<rho>) at_top" if y: "0 < y" for y
  proof -
    have eq: "\<forall>\<^sub>F u in at_top.
        (W (s u * y) / W (s u)) * (W (s u) / u) = W (s u * y) / u"
      using Ws_pos by eventually_elim (simp add: field_simps)
    from Lim_transform_eventually[OF
        tendsto_mult[OF filterlim_compose[OF lim[OF y] s] near_inv] eq]
    show ?thesis
      by simp
  qed
  define L where "L = x powr (1 / \<rho>)"
  have L_pos: "0 < L"
    using x by (simp add: L_def)
  show ?thesis
    unfolding L_def[symmetric] tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    define e' where "e' = min (L / 2) e"
    have e'_pos: "0 < e'" and e'_le: "e' \<le> e" and e'_lt: "e' < L"
      using e L_pos by (simp_all add: e'_def)
    have cpos: "0 < L - e'"
      using e'_lt by simp
    define ylo where "ylo = (L - e' + L) / 2"
    have ylo_pos: "0 < ylo"
      using cpos L_pos by (simp add: ylo_def)
    have c_lt_ylo: "L - e' < ylo"
      using e'_pos by (simp add: ylo_def)
    have ylo_lt_L: "ylo < L"
      using e'_pos by (simp add: ylo_def)
    have ylo_powr_lt_x: "ylo powr \<rho> < x"
      using powr_less_mono2[OF rho less_imp_le[OF ylo_pos] ylo_lt_L] x rho
      by (simp add: L_def powr_powr)
    have ev_lt: "\<forall>\<^sub>F u in at_top. W (s u * ylo) < u * x"
      using order_tendstoD(2)[OF Winv_ratio[OF ylo_pos] ylo_powr_lt_x] u_pos
      by eventually_elim (simp add: field_simps)
    have lower: "\<forall>\<^sub>F u in at_top. L - e' < s (u * x) / s u"
      using ev_lt s_gt1_mult[OF ylo_pos] u_pos
    proof eventually_elim
      case (elim u)
      have le: "s u * ylo \<le> s (u * x)"
        using le_iff[OF elim(2), of "u * x"] elim(1) by simp
      have "(L - e') * s u < ylo * s u"
        using c_lt_ylo s_pos[OF elim(3)] by (intro mult_strict_right_mono) auto
      also have "\<dots> \<le> s (u * x)"
        using le by (simp add: mult.commute)
      finally have "(L - e') * s u < s (u * x)" .
      thus ?case
        using s_pos[OF elim(3)] by (simp add: field_simps)
    qed
    define yhi where "yhi = (L + (L + e')) / 2"
    have yhi_pos: "0 < yhi"
      using L_pos e'_pos by (simp add: yhi_def)
    have yhi_lt_c: "yhi < L + e'"
      using e'_pos by (simp add: yhi_def)
    have L_lt_yhi: "L < yhi"
      using e'_pos by (simp add: yhi_def)
    have x_lt_yhi_powr: "x < yhi powr \<rho>"
      using powr_less_mono2[OF rho less_imp_le[OF L_pos] L_lt_yhi] x rho
      by (simp add: L_def powr_powr)
    have ev_gt: "\<forall>\<^sub>F u in at_top. u * x < W (s u * yhi)"
      using order_tendstoD(1)[OF Winv_ratio[OF yhi_pos] x_lt_yhi_powr] u_pos
      by eventually_elim (simp add: field_simps)
    have upperb: "\<forall>\<^sub>F u in at_top. s (u * x) / s u < L + e'"
      using ev_gt s_gt1_mult[OF yhi_pos] u_pos
    proof eventually_elim
      case (elim u)
      have "s (u * x) < s u * yhi"
        using galois_strict[OF elim(2)] elim(1) by simp
      also have "s u * yhi < s u * (L + e')"
        using yhi_lt_c s_pos[OF elim(3)] by (intro mult_strict_left_mono) auto
      finally have "s (u * x) < s u * (L + e')" .
      thus ?case
        using s_pos[OF elim(3)] by (simp add: field_simps)
    qed
    show "\<forall>\<^sub>F u in at_top. \<bar>s (u * x) / s u - L\<bar> < e"
      using lower upperb
      by eventually_elim (use e'_le in linarith)
  qed
qed

end