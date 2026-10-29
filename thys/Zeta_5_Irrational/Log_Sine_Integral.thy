(*  Title:   Log_Sine_Integral.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Log_Sine_Integral
  imports Interval_Integral_Substitutions "HOL-Complex_Analysis.Complex_Analysis"
begin

section \<open>The log-sine integral and circle averages of \<open>ln |z - a|\<close>\<close>

text \<open>Jordan's inequality \<open>sin \<theta> \<ge>
  2\<theta>/\<pi>\<close> on \<open>[0, \<pi>/2]\<close>,
  integrability of \<open>ln\<close> near \<open>0\<close>, the classical
  \<open>\<integral>\<^sub>0\<^sup>\<pi> ln (sin \<theta>) d\<theta> =
    -\<pi> ln 2\<close>, and the circle average \<open>\<integral>\<^sub>0\<^sup>2\<^sup>\<pi> ln
    |e\<^sup>i\<^sup>\<theta> - a| d\<theta> = 2\<pi> ln (max 1 |a|)\<close>
  for every complex \<open>a\<close>, including the singular case \<open>|a| = 1\<close>; the same
    for the normalised
  arclength measure @{text circ} on a circle of radius \<open>\<epsilon>\<close> about
    \<open>c\<close>.  This is the layer of
  Jensen's formula that HOL-Complex\_Analysis lacks.\<close>

text \<open>Jordan's inequality @{text "sin \<theta> \<ge> 2\<theta>/\<pi>"} on
  @{text "[0, \<pi>/2]"}: @{text "sin"} is concave there
  (@{text "sin'' = - sin \<le> 0"}) and the chord through @{text "(0, 0)"} and
    @{text "(\<pi>/2, 1)"} lies below it.\<close>
lemma sin_ge_two_over_pi:
  assumes "0 \<le> \<theta>" "\<theta> \<le> pi / 2"
  shows "2 * \<theta> / pi \<le> sin \<theta>"
proof -
  have c1: "convex {0..pi / 2 :: real}"
    by blast
  have c2: "\<And>x. DERIV sin x :> cos x"
    by (blast intro: DERIV_sin)
  have c3: "\<And>x. DERIV cos x :> - sin x"
    by (fast intro: DERIV_cos)
  have c4: "\<And>x. x \<in> {0..pi / 2} \<Longrightarrow> - sin x \<le> 0"
    using sin_ge_zero by simp
  have conc: "concave_on {0..pi / 2} sin"
    using f''_le0_imp_concave[OF c1 c2 c3 c4] by fastforce
  show ?thesis
    using concave_onD_Icc'[OF conc, of \<theta>] assms
    by (simp add: field_simps)
qed

text \<open>@{text "ln"} is integrable near @{text 0}:
  @{text "\<integral>_0^c (- ln u) du = c - c ln c < \<infinity>"}.\<close>
lemma ln_integrable_near_zero:
  assumes "0 < c"
  shows "set_integrable lborel {0<..<c} (\<lambda>u :: real. ln u)"
proof -
  define F where "F u = u * ln c - u * ln u + u" for u :: real
  define f where "f u = ln c - ln u" for u :: real
  have D: "DERIV F x :> f x" if "0 < x" for x
    unfolding F_def[abs_def] f_def using that
    by (intro derivative_eq_intros) auto
  have contf: "isCont f x" if "0 < x" for x
    unfolding f_def using that
    by (fastforce intro: continuous_intros)
  have nonneg: "AE x in lborel. ereal 0 < ereal x \<longrightarrow>
    ereal x < ereal c \<longrightarrow> 0 \<le> f x"
    unfolding f_def
    by fastforce
  have lim0: "((F \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_right (ereal 0))"
    unfolding ereal_tendsto_simps F_def
    by real_asymp
  have limc: "((F \<circ> real_of_ereal) \<longlongrightarrow> F c) (at_left (ereal c))"
    unfolding ereal_tendsto_simps F_def using assms
    by (fast intro: tendsto_intros)
  note FTC = interval_integral_FTC_nonneg[of "ereal 0" "ereal c" F f, OF _ _ _ nonneg lim0 limc]
  have "set_integrable lborel {0<..<c} (\<lambda>u :: real. ln c)"
    using interval_integral_const(1)[of 0 c "ln c"] assms
    unfolding interval_lebesgue_integrable_def
    by auto
  moreover have "set_integrable lborel {0<..<c} f"
    using FTC(1) assms D contf
    by auto
  ultimately have "set_integrable lborel {0<..<c} (\<lambda>u. ln c - f u)"
    by (rule set_integral_diff(1))
  thus ?thesis unfolding f_def
    by simp
qed

text \<open>The classical @{text "\<integral>_0^\<pi> log sin \<theta> d\<theta> = -\<pi> log 2"};
  first the integrability.\<close>
lemma ln_sin_integrable: "interval_lebesgue_integrable lborel (ereal 0) (ereal pi)
  (\<lambda>\<theta>. ln (sin \<theta>))"
proof -
  have meas: "(\<lambda>\<theta> :: real. ln (sin \<theta>)) \<in> borel_measurable borel"
    by simp
  have lower: "ln (2 * \<theta> / pi) \<le> ln (sin \<theta>)" if "\<theta> \<in> {0<..<pi / 2}"
    for \<theta>
    using sin_ge_two_over_pi[of \<theta>] sin_gt_zero[of \<theta>] pi_gt_zero ln_le_cancel_iff[of "2
      * \<theta> / pi" "sin \<theta>"]
    using that
    by simp
  have upper: "ln (sin \<theta>) \<le> 0" if "\<theta> \<in> {0<..<pi}" for \<theta>
    using sin_le_one[of \<theta>] sin_gt_zero[of \<theta>]
    using that
    by (simp add: ln_le_zero_iff)
  have bound: "norm (ln (sin \<theta>)) \<le> norm (ln \<theta>) + norm (ln (2 / pi))"
    if th: "\<theta> \<in> {0<..<pi / 2}" for \<theta>
  proof -
    have e0: "2 * \<theta> / pi = \<theta> * (2 / pi)"
      by simp
    have "ln (2 * \<theta> / pi) = ln \<theta> + ln (2 / pi)"
      using th pi_gt_zero ln_mult[of \<theta> "2 / pi"] unfolding e0
      by simp
    moreover have "ln (2 * \<theta> / pi) \<le> ln (sin \<theta>)" using lower th by blast
    moreover have "ln (sin \<theta>) \<le> 0" using upper th pi_gt_zero by auto
    ultimately show ?thesis unfolding real_norm_def
      by linarith
  qed
  have i1: "set_integrable lborel {0<..<pi / 2} (\<lambda>\<theta>. norm (ln \<theta>))"
    using set_integrable_abs[OF ln_integrable_near_zero[OF pi_half_gt_zero]] unfolding real_norm_def
    by simp
  have i2: "set_integrable lborel {0<..<pi / 2} (\<lambda>\<theta> :: real. norm (ln (2 / pi)))"
    using interval_integral_const(1)[of 0 "pi / 2" "norm (ln (2 / pi))"] pi_gt_zero
    unfolding interval_lebesgue_integrable_def
    by simp
  have int_ln: "set_integrable lborel {0<..<pi / 2} (\<lambda>\<theta>. norm (ln \<theta>) +
    norm (ln (2 / pi)))"
    using set_integral_add(1)[OF i1 i2] by simp
  have sb: "set_borel_measurable lborel {0<..<pi / 2} (\<lambda>\<theta>. ln (sin \<theta>))"
    unfolding set_borel_measurable_def using meas
    by simp
  have ae: "AE x in lborel. x \<in> {0<..<pi / 2} \<longrightarrow>
    norm (ln (sin x)) \<le> norm (norm (ln x) + norm (ln (2 / pi)))" using bound
    by (auto intro: AE_I2)
  have int_half: "set_integrable lborel {0<..<pi / 2} (\<lambda>\<theta>. ln (sin \<theta>))"
    using set_integrable_bound[OF int_ln sb ae] by simp
  have "interval_lebesgue_integrable lborel (ereal 0) (ereal (pi /
    2)) (\<lambda>\<theta>. ln (sin \<theta>))" using int_half
    unfolding interval_lebesgue_integrable_def
    by simp
  hence "interval_lebesgue_integrable lborel (ereal (pi - pi / 2)) (ereal (pi -
    0)) (\<lambda>x. ln (sin (pi - x)))"
    using LBINT_reflect_int[of 0 "pi / 2" "(\<lambda>\<theta>. ln (sin \<theta>))" pi]
    by simp
  hence int_upper: "set_integrable lborel {pi / 2<..<pi} (\<lambda>\<theta>. ln (sin \<theta>))"
    unfolding interval_lebesgue_integrable_def
    by simp
  have split: "einterval (ereal 0) (ereal pi) =
    {0<..<pi / 2} \<union> {pi / 2<..<pi} \<union> {pi / 2}"
    using pi_gt_zero
    by auto
  have m1a: "{0<..<pi / 2} \<in> sets lborel"
    by simp
  have m1b: "{pi / 2<..<pi} \<in> sets lborel"
    by simp
  note m1 = m1a m1b
  have u1: "set_integrable lborel ({0<..<pi / 2} \<union> {pi /
    2<..<pi}) (\<lambda>\<theta>. ln (sin \<theta>))" using set_integrable_Un[OF int_half int_upper]
    using m1
    by blast
  have "set_integrable lborel ({0<..<pi / 2} \<union> {pi / 2<..<pi} \<union> {pi /
    2}) (\<lambda>\<theta>. ln (sin \<theta>))"
    using set_integrable_discrete_difference[where X="{pi / 2}" and A="{0<..<pi / 2} \<union> {pi /
      2<..<pi}" and B="{0<..<pi / 2} \<union> {pi / 2<..<pi} \<union> {pi /
      2}" and M=lborel and f="(\<lambda>\<theta>. ln (sin \<theta>))"] u1
    by auto
  moreover have "ereal 0 \<le> ereal pi" using pi_gt_zero by simp
  ultimately show ?thesis unfolding interval_lebesgue_integrable_def unfolding split[symmetric]
    by simp
qed

lemma ln_sin_integrable_half: "interval_lebesgue_integrable lborel (ereal 0) (ereal (pi /
  2)) (\<lambda>\<theta>. ln (sin \<theta>))"
proof -
  have a: "set_integrable lborel {0<..<pi} (\<lambda>\<theta>. ln (sin \<theta>))"
    using ln_sin_integrable pi_gt_zero unfolding interval_lebesgue_integrable_def
    by simp
  have "set_integrable lborel {0<..<pi / 2} (\<lambda>\<theta>. ln (sin \<theta>))"
    using set_integrable_subset[OF a, of "{0<..<pi / 2}"]
    by fastforce
  thus ?thesis unfolding interval_lebesgue_integrable_def
    by simp
qed

lemma ln_cos_integrable_half: "interval_lebesgue_integrable lborel (ereal 0) (ereal (pi /
  2)) (\<lambda>u. ln (cos u))"
proof -
  have e: "(\<lambda>x. ln (sin (pi / 2 - x))) = (\<lambda>x. ln (cos x))"
    by (simp add: cos_sin_eq)
  show ?thesis using LBINT_reflect_int[of 0 "pi / 2" "\<lambda>\<theta>. ln (sin \<theta>)" "pi /
    2"] ln_sin_integrable_half unfolding e
    by simp
qed

lemma ln_sin_integral: "interval_lebesgue_integral lborel (ereal 0) (ereal pi) (\<lambda>\<theta>.
  ln (sin \<theta>)) = - pi * ln 2"
proof -
  define I where "I = interval_lebesgue_integral lborel (ereal 0) (ereal pi) (\<lambda>\<theta>. ln
    (sin \<theta>))"
  have "interval_lebesgue_integral lborel (ereal (0)) (ereal (pi /
    2)) (\<lambda>\<theta>. ln (sin \<theta>)) + interval_lebesgue_integral lborel (ereal (pi /
    2)) (ereal (pi)) (\<lambda>\<theta>. ln (sin \<theta>)) = I" unfolding I_def
    using interval_integral_sum[of "ereal 0" "ereal (pi /
    2)" "ereal pi" "(\<lambda>\<theta>. ln (sin \<theta>))"] ln_sin_integrable
    by simp
  moreover have "interval_lebesgue_integral lborel (ereal (pi /
    2)) (ereal (pi)) (\<lambda>\<theta>. ln (sin \<theta>)) =
    interval_lebesgue_integral lborel (ereal (0)) (ereal (pi /
    2)) (\<lambda>\<theta>. ln (sin \<theta>))"
    using LBINT_reflect[of "pi / 2" pi "(\<lambda>\<theta>. ln (sin \<theta>))" pi]
    by simp
  ultimately have half: "I = 2 * interval_lebesgue_integral lborel (ereal 0) (ereal (pi /
    2)) (\<lambda>\<theta>. ln (sin \<theta>))"
    by linarith
  have p: "0 \<le> pi" using pi_gt_zero by simp
  have pw: "ln (sin (0 + 2 * x)) = ln 2 + ln (sin x) + ln (cos x)" if x: "0 < x" "x < pi / 2" for x
  proof -
    have sx: "0 < sin x" using x sin_gt_zero[of x]
      by simp
    have cx: "0 < cos x" using x cos_gt_zero_pi[of x]
      by simp
    have e2: "sin (0 + 2 * x) = 2 * (sin x * cos x)" using sin_double[of x]
      by simp
    show ?thesis unfolding e2 using sx cx ln_mult[of 2 "sin x * cos x"] ln_mult[of "sin x" "cos x"]
      by simp
  qed
  have "I = 2 * interval_lebesgue_integral lborel (ereal (0)) (ereal (pi /
    2)) (\<lambda>x. ln (sin (0 + 2 * x)))"
    using LBINT_affine[of 2 0 pi "\<lambda>\<theta>. ln (sin \<theta>)" 0, OF _ p] unfolding I_def
    by simp
  moreover have "interval_lebesgue_integral lborel (ereal (0)) (ereal (pi /
    2)) (\<lambda>x. ln (sin (0 + 2 * x))) =
    interval_lebesgue_integral lborel (ereal (0)) (ereal (pi / 2)) (\<lambda>x. ln 2 + ln (sin x) +
    ln (cos x))" using pw pi_gt_zero
    by (auto intro: interval_integral_cong)
  moreover have "interval_lebesgue_integral lborel (ereal (0)) (ereal (pi / 2)) (\<lambda>x. ln 2 +
    ln (sin x) + ln (cos x)) = pi / 2 * ln 2 +
    interval_lebesgue_integral lborel (ereal (0)) (ereal (pi / 2)) (\<lambda>u. ln (sin u)) +
    interval_lebesgue_integral lborel (ereal (0)) (ereal (pi / 2)) (\<lambda>u. ln (cos u))"
    using ln_sin_integrable_half ln_cos_integrable_half
    by simp
  ultimately have doubling: "I = pi * ln 2 + 2 *
    interval_lebesgue_integral lborel (ereal 0) (ereal (pi / 2)) (\<lambda>u. ln (sin u))
                      + 2 * interval_lebesgue_integral lborel (ereal 0) (ereal (pi /
                        2)) (\<lambda>u. ln (cos u))"
    by linarith
  have e: "(\<lambda>x. ln (cos (pi / 2 - x))) = (\<lambda>x. ln (sin x))"
    by (simp add: cos_diff)
  have cos_eq: "interval_lebesgue_integral lborel (ereal 0) (ereal (pi /
    2)) (\<lambda>u. ln (cos u)) = interval_lebesgue_integral lborel (ereal 0) (ereal (pi /
    2)) (\<lambda>u. ln (sin u))"
    using LBINT_reflect[of 0 "pi / 2" "\<lambda>u. ln (cos u)" "pi / 2"] pi_gt_zero unfolding e
    by simp
  show ?thesis using half doubling cos_eq unfolding I_def[symmetric] by linarith
qed

lemma norm_1_minus_cis: "norm (1 - cis \<theta>) ^ 2 = (2 * sin (\<theta> / 2)) ^ 2"
proof -
  have a: "norm (1 - cis \<theta>) ^ 2 = (1 - cos \<theta>) ^ 2 + (sin \<theta>) ^ 2"
    by (simp add: cmod_power2)
  have b: "cos \<theta> = 1 - 2 * sin (\<theta> / 2) ^ 2" using cos_double_sin[of "\<theta> / 2"]
    by simp
  have c: "sin \<theta> = 2 * sin (\<theta> / 2) * cos (\<theta> / 2)"
    using sin_double[of "\<theta> / 2"]
    by simp
  have d: "sin (\<theta> / 2) ^ 2 + cos (\<theta> / 2) ^ 2 = 1" by (rule sin_cos_squared_add)
  have e: "(1 - (1 - 2 * sin (\<theta> / 2) ^ 2)) ^ 2 + (2 * sin (\<theta> / 2) * cos (\<theta> /
    2)) ^ 2 = (2 * sin (\<theta> / 2)) ^ 2 * (sin (\<theta> / 2) ^ 2 + cos (\<theta> / 2) ^ 2)"
    using sin_cos_squared_add[of "\<theta> / 2"]
    unfolding power2_eq_square
    by argo
  show ?thesis unfolding a b c e d
    by simp
qed

lemma ln_norm_one_minus_cis:
  assumes th: "0 < \<theta>" "\<theta> < 2 * pi"
  shows "ln (norm (1 - cis \<theta>)) = ln 2 + ln (sin (\<theta> / 2))"
proof -
  have s: "0 < sin (\<theta> / 2)" using th sin_gt_zero[of "\<theta> / 2"]
    by simp
  have n: "norm (1 - cis \<theta>) = 2 * sin (\<theta> / 2)" using norm_1_minus_cis[of \<theta>] s
    using power2_eq_iff_nonneg[of "norm (1 - cis \<theta>)" "2 * sin (\<theta> / 2)"]
    by simp
  show ?thesis unfolding n using s ln_mult[of 2 "sin (\<theta> / 2)"]
    by simp
qed

text \<open>@{text "\<integral>_0^{2\<pi>} log|1 - e^{i\<theta>}| d\<theta> = 0"}: the singular case
  of the circle average.\<close>
lemma circle_log_one: "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
  pi)) (\<lambda>\<theta>. ln (norm (1 - cis \<theta>))) = 0"
proof -
  have c1: "interval_lebesgue_integral lborel (ereal (0)) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (1 - cis \<theta>))) =
    interval_lebesgue_integral lborel (ereal (0)) (ereal (2 * pi)) (\<lambda>\<theta>. ln 2 +
    ln (sin (\<theta> / 2)))" using ln_norm_one_minus_cis pi_gt_zero
    by (auto intro: interval_integral_cong)
  have p: "0 \<le> 2 * pi" using pi_gt_zero by simp
  have gi: "interval_lebesgue_integrable lborel (ereal (0)) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (sin (\<theta> / 2)))"
    using LBINT_affine_int[of 2 0 "2 * pi" "\<lambda>\<theta>. ln (sin (\<theta> / 2))" 0,
    OF _ p] ln_sin_integrable
    by simp
  have gv: "interval_lebesgue_integral lborel (ereal (0)) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (sin (\<theta> / 2))) = 2 * (- pi * ln 2)"
    using LBINT_affine[of 2 0 "2 * pi" "\<lambda>\<theta>. ln (sin (\<theta> / 2))" 0,
    OF _ p] ln_sin_integral
    by simp
  have c2: "interval_lebesgue_integral lborel (ereal (0)) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln 2 + ln (sin (\<theta> / 2))) =
    ln 2 * (2 * pi - 0) + interval_lebesgue_integral lborel (ereal (0)) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (sin (\<theta> / 2)))" using gi
    by simp
  show ?thesis using c1 c2 gv
    by argo
qed

lemma circle_log_one_integrable: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 *
  pi)) (\<lambda>\<theta>. ln (norm (1 - cis \<theta>)))"
proof -
  have p: "0 \<le> 2 * pi" using pi_gt_zero by simp
  have "interval_lebesgue_integrable lborel (ereal (0)) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (sin (\<theta> / 2)))"
    using LBINT_affine_int[of 2 0 "2 * pi" "\<lambda>\<theta>. ln (sin (\<theta> / 2))" 0,
    OF _ p] ln_sin_integrable
    by simp
  hence "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 * pi)) (\<lambda>\<theta>. ln 2 +
    ln (sin (\<theta> / 2)))"
    by simp
  hence s2: "set_integrable lborel {0<..<2 * pi} (\<lambda>\<theta>. ln 2 + ln (sin (\<theta> /
    2)))" using pi_gt_zero unfolding interval_lebesgue_integrable_def
    by simp
  have "set_integrable lborel {0<..<2 * pi} (\<lambda>\<theta>. ln (norm (1 - cis \<theta>)))"
    using set_integrable_cong[of lborel lborel "{0<..<2 * pi}" "{0<..<2 *
      pi}" "\<lambda>\<theta>. ln (norm (1 - cis \<theta>))" "\<lambda>\<theta>. ln 2 +
      ln (sin (\<theta> / 2))"] ln_norm_one_minus_cis s2
    by simp
  thus ?thesis using pi_gt_zero unfolding interval_lebesgue_integrable_def
    by simp
qed

text \<open>Mean value of the holomorphic @{text "Ln (1 - z/a)"} on the unit circle,
  @{text "|a| > 1"}.\<close>
lemma circle_log_gt:
  assumes "1 < norm a"
  shows "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - a))) = 2 * pi * ln (norm a)"
proof -
  define f where "f = (\<lambda>z. Ln (1 - z / a))"
  have a0: "a \<noteq> 0" using assms by auto
  have nr: "1 - z / a \<notin> \<real>\<^sub>\<le>\<^sub>0" if "norm z < norm a" for z
  proof -
    have "norm (z / a) < 1" using that a0
      by (simp add: norm_divide field_simps)
    hence "Re (z / a) < 1" using complex_Re_le_cmod[of "z / a"] by linarith
    thus ?thesis
      by (simp add: complex_nonpos_Reals_iff)
  qed
  have hol: "f holomorphic_on ball 0 (norm a)" unfolding f_def using nr a0
    by (fastforce intro: holomorphic_intros)
  have sb: "cball 0 1 \<subseteq> ball (0 :: complex) (norm a)" using assms
    by auto
  have sb2: "ball 0 1 \<subseteq> ball (0 :: complex) (norm a)" using sb ball_subset_cball
    by blast
  have cont: "continuous_on (cball 0 1) f" using holomorphic_on_imp_continuous_on[OF hol] sb
    by (blast intro: continuous_on_subset)
  have cauchy: "((\<lambda>u. f u / (u - 0)) has_contour_integral (2 * of_real pi * \<i> *
    f 0)) (circlepath 0 1)"
    using Cauchy_integral_circlepath [OF cont holomorphic_on_subset [OF hol sb2], of 0]
    by simp
  have f0: "f 0 = 0" by (simp add: f_def)
  have mean: "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. Re (f (cis \<theta>))) = 0"
  proof -
    have cx: "circlepath 0 1 x = cis (2 * pi * x)" for x
      by (simp add: circlepath cis_conv_exp mult_ac)
    have m1: "((\<lambda>x. f (circlepath 0 1 x) / (circlepath 0 1 x - 0) *
      vector_derivative (circlepath 0 1) (at x within {0..1})) has_integral 0) {0..1}"
      using cauchy f0 unfolding has_contour_integral_def
      by simp
    have m2: "f (circlepath 0 1 x) / (circlepath 0 1 x - 0) *
      vector_derivative (circlepath 0 1) (at x within {0..1}) =
      2 * pi * \<i> * f (cis (2 * pi * x))" if "x \<in> {0..1}" for x
      using vector_derivative_circlepath01[of x 0 1] that unfolding cx
      by (simp add: cis_conv_exp field_simps)
    have m3: "((\<lambda>x. 2 * pi * \<i> * f (cis (2 * pi * x))) has_integral 0) {0..1}"
      using m1 has_integral_cong[of "{0..1}", OF m2]
      by fast
    have cnz: "complex_of_real (2 * pi) * \<i> \<noteq> 0"
      by simp
    have m4: "((\<lambda>x. f (cis (2 * pi * x))) has_integral 0) {0..1}"
      using m3 has_integral_mult_right_iff[of "2 * pi * \<i>" "\<lambda>x. f (cis (2 * pi *
        x))" 0 "{0..1}"] cnz
      by simp
    have m5: "((\<lambda>x. Re (f (cis (2 * pi * x)))) has_integral 0) {0..1}"
      using has_integral_linear[OF m4 bounded_linear_Re]
      by (simp add: o_def)
    have g1: "continuous_on UNIV (\<lambda>\<theta>. Re (f (cis \<theta>)))"
      using continuous_on_compose2[OF cont, of UNIV cis]
      by (fastforce intro: continuous_intros)
    have g2: "continuous_on {0..1} (\<lambda>x. Re (f (cis (0 + 2 * pi * x))))"
      using continuous_on_compose2[OF g1, of "{0..1}" "\<lambda>x. 0 + 2 * pi * x"]
      by (fast intro: continuous_intros)
    have si: "set_integrable lborel {0..1} (\<lambda>x. Re (f (cis (0 + 2 * pi * x))))"
      using borel_integrable_compact[OF compact_Icc g2] unfolding set_integrable_def
      by fastforce
    have ie: "interval_lebesgue_integral lborel (ereal 0) (ereal 1) (\<lambda>x. Re (f (cis (0 + 2 *
      pi * x)))) = integral {0..1} (\<lambda>x. Re (f (cis (0 + 2 * pi * x))))"
      using interval_integral_eq_integral[OF _ si]
      by argo
    have iz: "integral {0..1} (\<lambda>x. Re (f (cis (0 + 2 * pi * x)))) = 0" using m5
      by (auto intro: integral_unique)
    have af: "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
      pi)) (\<lambda>\<theta>. Re (f (cis \<theta>))) =
      2 * pi * interval_lebesgue_integral lborel (ereal 0) (ereal 1) (\<lambda>x. Re (f (cis (0 +
      2 * pi * x))))"
      using LBINT_affine[of "2 * pi" 0 "2 *
        pi" "\<lambda>\<theta>. Re (f (cis \<theta>))" 0] pi_gt_zero
      by simp
    show ?thesis using af ie iz
      by simp
  qed
  have pt: "ln (norm (cis \<theta> - a)) = ln (norm a) + Re (f (cis \<theta>))" for \<theta>
  proof -
    have nz: "1 - cis \<theta> / a \<noteq> 0"
    proof
      assume "1 - cis \<theta> / a = 0"
      hence "cis \<theta> = a" using a0
        by (simp add: field_simps)
      thus False using assms
        by auto
    qed
    have eq: "norm (cis \<theta> - a) = norm a * norm (1 - cis \<theta> / a)"
    proof -
      have "cis \<theta> - a = - (a * (1 - cis \<theta> / a))" using a0
        by (simp add: field_simps)
      thus ?thesis
        by (simp add: norm_mult)
    qed
    show ?thesis unfolding eq f_def using nz a0 ln_mult[of "norm a" "norm (1 - cis \<theta> / a)"]
      by simp
  qed
  have c1: "continuous_on UNIV (\<lambda>\<theta>. f (cis \<theta>))"
    using continuous_on_compose2[OF cont, of UNIV cis]
    by (fastforce intro: continuous_intros)
  have c2: "continuous_on {0..2 * pi} (\<lambda>\<theta>. Re (f (cis \<theta>)))"
    using continuous_on_Re[OF c1]
    by (blast intro: continuous_on_subset)
  have ii: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. Re (f (cis \<theta>)))"
    using interval_integrable_continuous_on[OF _ c2] pi_gt_zero
    by simp
  show ?thesis unfolding pt using ii mean
    by simp
qed

lemma circle_log_lt:
  assumes "norm a < 1"
  shows "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - a))) = 0"
proof (cases "a = 0")
  case True
  thus ?thesis by simp
next
  case False
  define b where "b = 1 / cnj a"
  have nb: "norm b = 1 / norm a" and b1: "1 < norm b" using False assms
    by (auto simp: b_def norm_divide)
  have pt: "ln (norm (cis \<theta> - a)) = ln (norm a) + ln (norm (cis \<theta> - b))" for \<theta>
  proof -
    have c1: "cnj (cnj a * cis \<theta> - 1) = cis (- \<theta>) * (a - cis \<theta>)"
      by (simp add: cis_cnj algebra_simps cis_mult)
    have "norm (cnj a * cis \<theta> - 1) = norm (a - cis \<theta>)"
      using arg_cong[where f = norm, OF c1] unfolding complex_mod_cnj norm_mult
      by auto
    hence e1: "norm (cis \<theta> - a) = norm (cnj a * cis \<theta> - 1)"
      using norm_minus_commute[of a "cis \<theta>"]
      by simp
    have e2: "norm (cnj a * cis \<theta> - 1) = norm a * norm (cis \<theta> - b)"
    proof -
      have "cnj a * cis \<theta> - 1 = cnj a * (cis \<theta> - b)" using False unfolding b_def
        by (simp add: field_simps)
      thus ?thesis by (simp add: norm_mult)
    qed
    have nz: "cis \<theta> - b \<noteq> 0" using b1
      by auto
    show ?thesis unfolding e1 e2 using False nz ln_mult[of "norm a" "norm (cis \<theta> - b)"]
      by simp
  qed
  have nzb: "norm (cis \<theta> - b) \<noteq> 0" for \<theta> using b1
    by auto
  have cb: "continuous_on {0..2 * pi} (\<lambda>\<theta>. ln (norm (cis \<theta> - b)))" using nzb
    by (fast intro: continuous_intros)
  have ib: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - b)))"
    using interval_integrable_continuous_on[OF _ cb] pi_gt_zero
    by simp
  show ?thesis unfolding pt using ib circle_log_gt[OF b1] nb False
    by (simp add: ln_div)
qed


text \<open>A point of the unit circle as @{text "cis \<phi>"} with
  @{text "\<phi> \<in> [0, 2\<pi>]"}.\<close>
lemma cis_of_norm_one:
  assumes "norm a = 1"
  obtains \<phi> where "a = cis \<phi>" "0 \<le> \<phi>" "\<phi> \<le> 2 * pi"
proof -
  have c: "a = cis (Arg a)" using rcis_cmod_Arg[of a] assms
    by (simp add: rcis_def)
  show ?thesis
  proof (cases "0 \<le> Arg a")
    case True
    thus ?thesis using that[of "Arg a"] c Arg_bounded[of a]
      by linarith
  next
    case False
    have "cis (Arg a + 2 * pi) = cis (Arg a)"
      by (simp add: cis_mult[symmetric])
    thus ?thesis using that[of "Arg a + 2 * pi"] c Arg_bounded[of a] False
      by simp
  qed
qed

lemma norm_cis_minus_cis: "norm (cis \<theta> - cis \<phi>) = norm (1 - cis (\<theta> - \<phi>))"
proof -
  have q: "cis \<theta> - cis \<phi> = cis \<phi> * (cis (\<theta> - \<phi>) - 1)"
    by (simp add: cis_mult algebra_simps)
  show ?thesis unfolding q norm_mult
    using norm_minus_commute[of "cis (\<theta> - \<phi>)" 1]
    by simp
qed

lemma circle_log_eq:
  assumes "norm a = 1"
  shows "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - a))) = 0"
proof -
  obtain \<phi> where phi: "a = cis \<phi>" and p0: "0 \<le> \<phi>" "\<phi> \<le> 2 * pi"
    by (rule cis_of_norm_one[OF assms])
  define h where "h u = ln (norm (1 - cis u))" for u
  have per: "h (x + 2 * pi) = h x" for x unfolding h_def
    by (simp add: cis_mult[symmetric])
  have ih: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 * pi)) h"
    using circle_log_one_integrable unfolding h_def[abs_def] .
  have pt: "ln (norm (cis \<theta> - a)) = h (\<theta> - \<phi>)" for \<theta>
    using norm_cis_minus_cis[of \<theta> \<phi>] unfolding phi h_def by simp
  show ?thesis unfolding pt using periodic_shift_eq[of h \<phi>, OF per ih p0] circle_log_one
    unfolding h_def[abs_def]
    by simp
qed

lemma circle_log_eq_integrable:
  assumes "norm a = 1"
  shows "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - a)))"
proof -
  obtain \<phi> where phi: "a = cis \<phi>" and p0: "0 \<le> \<phi>" "\<phi> \<le> 2 * pi"
    by (rule cis_of_norm_one[OF assms])
  define h where "h u = ln (norm (1 - cis u))" for u
  have per: "h (x + 2 * pi) = h x" for x unfolding h_def
    by (simp add: cis_mult[symmetric])
  have ih: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 * pi)) h"
    using circle_log_one_integrable unfolding h_def[abs_def] .
  have pt: "ln (norm (cis \<theta> - a)) = h (\<theta> - \<phi>)" for \<theta>
    using norm_cis_minus_cis[of \<theta> \<phi>] unfolding phi h_def by simp
  show ?thesis unfolding pt using periodic_shift_int[of h \<phi>, OF per ih p0]
    unfolding h_def[abs_def]
    by simp
qed

theorem circle_avg_log:
  "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - a))) = 2 * pi * ln (max 1 (norm a))"
proof (cases "norm a" "1 :: real" rule: linorder_cases)
  case less thus ?thesis using circle_log_lt[OF less] by (simp add: max_def)
next
  case equal thus ?thesis using circle_log_eq[OF equal] by (simp add: max_def)
next
  case greater thus ?thesis using circle_log_gt[OF greater] by (simp add: max_def)
qed

lemma circle_log_integrable:
  "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - a)))"
proof (cases "norm a = 1")
  case True
  thus ?thesis by (rule circle_log_eq_integrable)
next
  case False
  have nz: "norm (cis \<theta> - a) \<noteq> 0" for \<theta> using False
    by auto
  have cb: "continuous_on {0..2 * pi} (\<lambda>\<theta>. ln (norm (cis \<theta> - a)))" using nz
    by (fast intro: continuous_intros)
  show ?thesis using interval_integrable_continuous_on[OF _ cb] pi_gt_zero
    by simp
qed


text \<open>Normalised arclength on the circle of radius @{text \<epsilon>} about @{text c}.\<close>
definition circ :: "complex \<Rightarrow> real \<Rightarrow> complex measure" where
  "circ c \<epsilon> = distr (density lborel (\<lambda>\<theta>. ennreal (indicator {0..2 *
    pi} \<theta> / (2 * pi)))) borel
                    (\<lambda>\<theta>. c + of_real \<epsilon> * cis \<theta>)"

text \<open>The circle average of @{text "log|z - a|"} over the circle of radius @{text \<epsilon>}
  about @{text c}: @{text "log max(\<epsilon>, |c - a|)"}.\<close>
lemma circ_log:
  assumes "0 < \<epsilon>"
  shows "integral\<^sup>L (circ c \<epsilon>) (\<lambda>z. ln (norm (z - a))) =
    ln (max \<epsilon> (norm (c - a)))"
proof -
  have "integral\<^sup>L (circ c \<epsilon>) (\<lambda>z. ln (norm (z - a)))
        = (1 / (2 * pi)) * interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
          pi)) (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a)))"
  proof -
    have mg0: "(\<lambda>\<theta>. c + of_real \<epsilon> * cis \<theta>) \<in>
      borel_measurable borel"
      by (fast intro: borel_measurable_continuous_onI continuous_intros)
    have mF: "(\<lambda>z. ln (norm (z - a))) \<in> borel_measurable borel"
      by simp
    have i1: "integral\<^sup>L (distr (density lborel (\<lambda>\<theta>. ennreal (indicator {0..2 *
      pi} \<theta> / (2 * pi)))) borel (\<lambda>\<theta>. c + of_real \<epsilon> *
      cis \<theta>)) (\<lambda>z. ln (norm (z - a))) =
      integral\<^sup>L (density lborel (\<lambda>\<theta>. ennreal (indicator {0..2 * pi} \<theta> /
      (2 * pi)))) (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a)))"
      using integral_distr[of "\<lambda>\<theta>. c + of_real \<epsilon> *
        cis \<theta>" "(density lborel (\<lambda>\<theta>. ennreal (indicator {0..2 * pi} \<theta> /
        (2 * pi))))" borel "\<lambda>z. ln (norm (z - a))"] mg0 mF
      by fastforce
    have mG: "(\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a))) \<in>
      borel_measurable borel" using measurable_compose[OF mg0 mF]
      by simp
    have i2: "integral\<^sup>L (density lborel (\<lambda>\<theta>. ennreal (indicator {0..2 *
      pi} \<theta> / (2 * pi)))) (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> *
      cis \<theta> - a))) = (\<integral>\<theta>. (indicator {0..2 * pi} \<theta> / (2 *
      pi)) *\<^sub>R (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> -
      a))) \<theta> \<partial>lborel)"
      using integral_density[of "(\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> *
        cis \<theta> - a)))" lborel "\<lambda>\<theta>. indicator {0..2 * pi} \<theta> / (2 *
        pi)"] mG
      by fastforce
    have i3a: "(\<lambda>\<theta>. (indicator {0..2 * pi} \<theta> / (2 *
      pi)) *\<^sub>R (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> -
      a))) \<theta>) = (\<lambda>\<theta>. (1 / (2 * pi)) * (indicator {0..2 *
      pi} \<theta> *\<^sub>R (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> -
      a))) \<theta>))"
      by (simp add: fun_eq_iff)
    have i3b: "(\<integral>\<theta>. (1 / (2 * pi)) * (indicator {0..2 *
      pi} \<theta> *\<^sub>R (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> -
      a))) \<theta>) \<partial>lborel) =
      (1 / (2 * pi)) * (\<integral>\<theta>. indicator {0..2 *
      pi} \<theta> *\<^sub>R (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> -
      a))) \<theta> \<partial>lborel)"
      by (fast intro: integral_mult_right_zero)
    have i3c: "(\<integral>\<theta>. indicator {0..2 *
      pi} \<theta> *\<^sub>R (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> -
      a))) \<theta> \<partial>lborel) = interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
      pi)) (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a)))"
      using interval_integral_Icc[of 0 "2 * pi" "(\<lambda>\<theta>. ln (norm (c +
        of_real \<epsilon> * cis \<theta> - a)))"] pi_gt_zero unfolding set_lebesgue_integral_def
      by linarith
    show ?thesis unfolding circ_def using i1 i2 i3a i3b i3c
      by presburger
  qed
  also have "\<dots> = (1 / (2 * pi)) * interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln \<epsilon> + ln (norm (cis \<theta> - (a - c) /
    of_real \<epsilon>)))"
  proof -
    define w where "w = (a - c) / of_real \<epsilon>"
    have bad: "{\<theta>. cis \<theta> = w} \<subseteq>
      range (\<lambda>n::int. Arg w + 2 * pi * of_int n)"
    proof
      fix \<theta> assume th: "\<theta> \<in> {\<theta>. cis \<theta> = w}"
      have w0: "w \<noteq> 0" using th
        by auto
      have cw: "cis (Arg w) = w" using cis_Arg[OF w0] th
        by (force simp: sgn_div_norm)
      have "sin \<theta> = sin (Arg w) \<and> cos \<theta> = cos (Arg w)" using th cw
        by (simp add: complex_eq_iff)
      then obtain n :: int where "\<theta> = Arg w + 2 * pi * n" using sin_cos_eq_iff by blast
      thus "\<theta> \<in> range (\<lambda>n::int. Arg w + 2 * pi * of_int n)" by auto
    qed
    have null: "{\<theta>. cis \<theta> = w} \<in> null_sets lborel"
      using countable_imp_null_set_lborel countable_subset[OF bad]
      by fast
    have pw: "ln (norm (c + of_real \<epsilon> * cis \<theta> - a)) =
      ln \<epsilon> + ln (norm (cis \<theta> - w))" if nw: "cis \<theta> \<noteq> w" for \<theta>
    proof -
      have e: "c + of_real \<epsilon> * cis \<theta> - a = of_real \<epsilon> * (cis \<theta> - w)"
        using assms unfolding w_def
        by (simp add: field_simps)
      show ?thesis unfolding e norm_mult
        using assms nw ln_mult[of \<epsilon> "norm (cis \<theta> - w)"]
        by simp
    qed
    have n1: "(\<lambda>\<theta>. norm (c + of_real \<epsilon> * cis \<theta> - a)) \<in>
      borel_measurable borel"
      by (fast intro: borel_measurable_continuous_onI continuous_intros)
    have n2: "(\<lambda>\<theta>. norm (cis \<theta> - w)) \<in> borel_measurable borel"
      by (fast intro: borel_measurable_continuous_onI continuous_intros)
    have m3: "(\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a))) \<in>
      borel_measurable borel" using borel_measurable_ln[OF n1]
      by simp
    have m4: "(\<lambda>\<theta>. ln \<epsilon> + ln (norm (cis \<theta> - w))) \<in>
      borel_measurable borel" using borel_measurable_ln[OF n2]
      by (auto intro: borel_measurable_add)
    have ae: "AE \<theta> in lborel. \<theta> \<in>
      einterval (min (ereal 0) (ereal (2 * pi))) (max (ereal 0) (ereal (2 * pi))) \<longrightarrow>
      (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a))) \<theta> =
      (\<lambda>\<theta>. ln \<epsilon> + ln (norm (cis \<theta> - w))) \<theta>"
      using AE_I'[OF null, of "\<lambda>\<theta>. \<theta> \<in>
        einterval (min (ereal 0) (ereal (2 * pi))) (max (ereal 0) (ereal (2 *
        pi))) \<longrightarrow> (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> *
        cis \<theta> - a))) \<theta> = (\<lambda>\<theta>. ln \<epsilon> + ln (norm (cis \<theta> -
        w))) \<theta>"] pw
      by blast
    have eqI: "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
      pi)) (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a))) =
      interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
      pi)) (\<lambda>\<theta>. ln \<epsilon> + ln (norm (cis \<theta> - w)))"
      using interval_integral_cong_AE[OF m3 m4 ae]
      by fastforce
    show ?thesis unfolding w_def[symmetric] using eqI
      by simp
  qed
  also have "\<dots> = (1 / (2 * pi)) * (2 * pi * ln \<epsilon> + 2 * pi * ln (max 1 (norm ((a -
    c) / of_real \<epsilon>))))"
    using circle_log_integrable[of "(a - c) / of_real \<epsilon>"] circle_avg_log[of "(a - c) /
      of_real \<epsilon>"]
    by simp
  also have "\<dots> = ln (max \<epsilon> (norm (c - a)))"
  proof -
    have nd: "norm ((a - c) / of_real \<epsilon>) = norm (c - a) / \<epsilon>" using assms
      by (simp add: norm_divide norm_minus_commute)
    have k: "ln \<epsilon> + ln (max 1 (norm (c - a) / \<epsilon>)) =
      ln (max \<epsilon> (norm (c - a)))"
    proof (cases "norm (c - a) \<le> \<epsilon>")
      case True
      thus ?thesis using assms
        by (simp add: max_def)
    next
      case False
      thus ?thesis using assms ln_div[of "norm (c - a)" \<epsilon>]
        by (auto simp: max_def)
    qed
    have e: "(1 / (2 * pi)) * (2 * pi * ln \<epsilon> + 2 * pi * ln (max 1 (norm (c - a) /
      \<epsilon>)))
        = ln \<epsilon> + ln (max 1 (norm (c - a) / \<epsilon>))"
      by (simp add: field_simps)
    show ?thesis unfolding nd e k ..
  qed
  finally show ?thesis .
qed

end
