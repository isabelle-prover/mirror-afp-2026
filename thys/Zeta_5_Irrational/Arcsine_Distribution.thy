(*  Title:   Arcsine_Distribution.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Arcsine_Distribution
  imports Log_Sine_Integral
begin

section \<open>The arcsine distribution and its logarithmic potential\<close>

text \<open>The arcsine law on \<open>(a,
  b)\<close> with density \<open>1 / (\<pi> \<surd>((t - a)(b - t)))\<close>,
  as the pushforward of the
  uniform distribution on \<open>(0, \<pi>)\<close> under \<open>\<theta> \<mapsto> (a+b)/2 -
    (b-a)/2 \<cdot> cos \<theta>\<close>; its logarithmic potential
  \<open>U(t) = \<integral> ln |t - u| d\<omega>(u)\<close>,
    which equals \<open>ln ((b - a)/4)\<close> on \<open>[a,
    b]\<close> and has an explicit (Joukowski)
  form outside; and the bound \<open>\<omega>[x - r, x + r] \<le>
    8 \<surd>r / (\<pi> \<surd>(b - a))\<close> on the mass of short intervals.\<close>

text \<open>The arcsine probability density on @{text "(a, b)"}, and the measure.\<close>
definition arcsine_dens :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "arcsine_dens a b t = (if a < t \<and> t < b then 1 / (pi * sqrt ((t - a) * (b - t))) else 0)"

definition arcsine :: "real \<Rightarrow> real \<Rightarrow> real measure" where
  "arcsine a b = density lborel (\<lambda>t. ennreal (arcsine_dens a b t))"

text \<open>The logarithmic potential @{text "U^\<mu>(t) = \<integral> log|t - u| d\<mu>(u)"} of a
  measure on the line.\<close>
definition logPot :: "real measure \<Rightarrow> real \<Rightarrow> real" where
  "logPot \<mu> t = integral\<^sup>L \<mu> (\<lambda>u. ln \<bar>t - u\<bar>)"

subsection \<open>The arcsine measure\<close>

lemma arcsine_distr:
  assumes "a < b"
  shows "arcsine a b = distr (density lborel (\<lambda>\<theta>. ennreal (indicator {0<..<pi}
    \<theta> / pi))) borel (\<lambda>\<theta>. (a + b) / 2 - (b - a) / 2 * cos \<theta>)"
proof -
  define m where "m = (a + b) / 2"
  define r where "r = (b - a) / 2"
  define g where "g = (\<lambda>\<theta>. m - r * cos \<theta>)"
  have r0: "0 < r" using assms unfolding r_def by simp
  have g_deriv: "\<And>\<theta>. (g has_real_derivative (r * sin \<theta>)) (at \<theta>)"
    unfolding g_def by (auto intro!: derivative_eq_intros)
  have g0: "g 0 = a" unfolding g_def m_def r_def
    by (simp add: field_simps)
  have gpi: "g pi = b" unfolding g_def m_def r_def
    by (simp add: field_simps)
  note g_ends = g0 gpi
  have g_pos: "\<And>\<theta>. \<theta> \<in> {0..pi} \<Longrightarrow> 0 \<le> r * sin \<theta>"
    using r0 by (simp add: sin_ge_zero)
  have dens: "\<And>\<theta>. \<theta> \<in> {0<..<pi} \<Longrightarrow>
    arcsine_dens a b (g \<theta>) * (r * sin \<theta>) = 1 / pi"
  proof -
    fix \<theta> :: real assume th: "\<theta> \<in> {0<..<pi}"
    have s0: "0 < sin \<theta>" using th by (simp add: sin_gt_zero)
    hence "0 < sin \<theta> ^ 2" by simp
    hence "cos \<theta> ^ 2 < 1" using sin_cos_squared_add[of \<theta>] by linarith
    hence c1: "\<bar>cos \<theta>\<bar> < 1" using abs_square_less_1[of "cos \<theta>"]
      by simp
    have ab: "a = m - r" "b = m + r" unfolding m_def r_def by (simp_all add: field_simps)
    have "r * cos \<theta> < r" using c1 r0
      by (simp add: abs_less_iff)
    moreover have "- r < r * cos \<theta>" using c1 r0
      using mult_strict_left_mono[of "- 1" "cos \<theta>" r] c1 r0 abs_less_iff[of "cos \<theta>" 1]
      by linarith
    ultimately have ga: "a < g \<theta> \<and> g \<theta> < b" unfolding g_def ab
      by auto
    have pr0: "(g \<theta> - a) * (b - g \<theta>) = r ^ 2 * (1 - cos \<theta> ^ 2)"
      unfolding g_def ab
      by (simp add: power2_eq_square algebra_simps)
    have sc: "1 - cos \<theta> ^ 2 = sin \<theta> ^ 2" using sin_cos_squared_add[of \<theta>]
      by linarith
    have pr: "(g \<theta> - a) * (b - g \<theta>) = (r * sin \<theta>) ^ 2" unfolding pr0 sc
      by (simp add: power_mult_distrib)
    have sq: "sqrt ((g \<theta> - a) * (b - g \<theta>)) = r * sin \<theta>" unfolding pr
      using r0 s0 by simp
    show "arcsine_dens a b (g \<theta>) * (r * sin \<theta>) = 1 / pi" unfolding arcsine_dens_def
      using ga sq r0 s0
      by simp
  qed
  define U where "U = density lborel (\<lambda>\<theta>. ennreal (indicator {0<..<pi} \<theta> /
    pi))"
  have mg: "g \<in> borel_measurable borel" unfolding g_def
    by (fast intro: borel_measurable_continuous_onI continuous_intros)
  have meq: "arcsine a b = distr U borel g"
  proof (rule measure_eqI)
    show "sets (arcsine a b) = sets (distr U borel g)" unfolding arcsine_def U_def
      by simp
    fix A assume "A \<in> sets (arcsine a b)"
    hence A: "A \<in> sets borel" unfolding arcsine_def by simp
    define F where "F t = arcsine_dens a b t * indicator A t" for t
    have md: "(\<lambda>t. arcsine_dens a b t) \<in> borel_measurable borel"
      unfolding arcsine_dens_def by measurable
    have mF: "F \<in> borel_measurable borel" unfolding F_def using A md
      by (blast intro: borel_measurable_times borel_measurable_indicator)
    have l0: "emeasure (arcsine a b) A =
      (\<integral>\<^sup>+ t. ennreal (arcsine_dens a b t) * indicator A t \<partial>lborel)"
      unfolding arcsine_def using A
      using md
      by (auto simp: emeasure_density)
    have pw1: "ennreal (arcsine_dens a b t) * indicator A t =
      ennreal (F t * indicator {g 0..g pi} t)" for t
      unfolding F_def g_ends arcsine_dens_def
      by (simp add: indicator_def)
    have l1: "emeasure (arcsine a b) A =
      (\<integral>\<^sup>+ t. ennreal (F t * indicator {g 0..g pi} t) \<partial>lborel)"
      unfolding l0 pw1 ..
    have sbF: "set_borel_measurable borel {g 0..g pi} F" using mF unfolding set_borel_measurable_def
      by simp
    have cg: "continuous_on {0..pi} (\<lambda>x. r * sin x)"
      by (fast intro: continuous_intros)
    have l2: "(\<integral>\<^sup>+ t. ennreal (F t * indicator {g 0..g pi} t) \<partial>lborel) =
      (\<integral>\<^sup>+ \<theta>. ennreal (F (g \<theta>) * (r * sin \<theta>) *
      indicator {0..pi} \<theta>) \<partial>lborel)"
      using nn_integral_substitution[where f=F and g=g and a=0 and b=pi and g'="\<lambda>x. r *
        sin x", OF sbF _ cg] g_deriv g_pos pi_gt_zero
      by simp
    have pw3: "ennreal (F (g \<theta>) * (r * sin \<theta>) * indicator {0..pi} \<theta>) =
      ennreal (indicator {0<..<pi} \<theta> / pi) * indicator (g -` A) \<theta>" for \<theta>
    proof (cases "\<theta> \<in> {0<..<pi}")
      case True
      thus ?thesis using dens[OF True] unfolding F_def
        by (simp add: indicator_def)
    next
      case False
      hence "\<theta> \<notin> {0..pi} \<or> \<theta> = 0 \<or> \<theta> = pi" by auto
      thus ?thesis
        by (auto simp: indicator_def)
    qed
    have mgU: "g \<in> measurable U borel" using mg unfolding U_def by simp
    have l4: "emeasure (distr U borel g) A =
      (\<integral>\<^sup>+ \<theta>. ennreal (indicator {0<..<pi} \<theta> / pi) *
      indicator (g -` A) \<theta> \<partial>lborel)"
      using emeasure_distr[OF mgU A] measurable_sets[OF mg A] unfolding U_def
      by (simp add: emeasure_density)
    show "emeasure (arcsine a b) A = emeasure (distr U borel g) A" unfolding l1 l2 l4 pw3 ..
  qed
  show ?thesis using meq unfolding U_def g_def m_def r_def
    by blast
qed

text \<open>Integration against the arcsine measure:
  @{text "\<integral> f d\<omega> = \<pi>^-^1 \<integral>_{(0,\<pi>)} f(m -
    r cos \<theta>) d\<theta>"}
  (substitution @{text "t = m - r cos \<theta>"}: @{text "has_integral_substitution"}).\<close>
theorem integral_arcsine:
  assumes "a < b" "f \<in> borel_measurable borel"
  shows "integral\<^sup>L (arcsine a b) f =
         1 / pi * set_lebesgue_integral lborel {0<..<pi} (\<lambda>\<theta>. f ((a + b) / 2 - (b -
           a) / 2 * cos \<theta>))"
proof -
  define g where "g = (\<lambda>\<theta> :: real. (a + b) / 2 - (b - a) / 2 * cos \<theta>)"
  define U where "U = density lborel (\<lambda>\<theta>. ennreal (indicator {0<..<pi} \<theta> /
    pi))"
  have meq: "arcsine a b = distr U borel g" unfolding U_def g_def
    by (rule arcsine_distr[OF assms(1)])
  have mg: "g \<in> borel_measurable borel" unfolding g_def
    by (fast intro: borel_measurable_continuous_onI continuous_intros)
  have mgU: "g \<in> measurable U borel" using mg unfolding U_def by simp
  have mfg: "(\<lambda>\<theta>. f (g \<theta>)) \<in> borel_measurable borel"
    using measurable_compose[OF mg assms(2)]
    by simp
  have "integral\<^sup>L (arcsine a b) f = integral\<^sup>L U (\<lambda>\<theta>. f (g \<theta>))"
    unfolding meq
    using integral_distr[OF mgU assms(2)]
    by fast
  moreover have "integral\<^sup>L U (\<lambda>\<theta>. f (g \<theta>)) =
    (\<integral>\<theta>. (indicator {0<..<pi} \<theta> /
    pi) *\<^sub>R f (g \<theta>) \<partial>lborel)"
    unfolding U_def using integral_density[of "\<lambda>\<theta>. f (g \<theta>)" lborel
      "\<lambda>\<theta>. indicator {0<..<pi} \<theta> / pi"] mfg
    by simp
  moreover have "(\<integral>\<theta>. (indicator {0<..<pi} \<theta> /
    pi) *\<^sub>R f (g \<theta>) \<partial>lborel) =
    1 / pi * set_lebesgue_integral lborel {0<..<pi} (\<lambda>\<theta>. f (g \<theta>))"
    unfolding set_lebesgue_integral_def
    by (simp add: integral_mult_right_zero[symmetric])
  ultimately show ?thesis unfolding g_def
    by linarith
qed

lemma arcsine_sqrt_identity:
  assumes "a < t" "t < b"
  shows "sqrt (1 - ((2 * t - a - b) / (b - a))\<^sup>2) = 2 * sqrt ((t - a) * (b - t)) / (b - a)"
proof -
  define X where "X = (t - a) * (b - t)"
  have X0: "0 \<le> X" using assms by (simp add: X_def)
  have ba: "0 < b - a" using assms by simp
  have num: "(b - a)\<^sup>2 - (2 * t - a - b)\<^sup>2 = 4 * X"
    by (simp add: X_def algebra_simps power2_eq_square)
  have "1 - ((2 * t - a - b) / (b - a))\<^sup>2 =
    ((b - a)\<^sup>2 - (2 * t - a - b)\<^sup>2) / (b - a)\<^sup>2"
  proof -
    have g: "1 - (c / d)\<^sup>2 = (d\<^sup>2 - c\<^sup>2) / d\<^sup>2" if "d \<noteq> 0"
      for c d :: real
      using that by (simp add: power_divide field_simps)
    show ?thesis by (rule g) (use ba in simp)
  qed
  also have "\<dots> = 4 * X / (b - a)\<^sup>2" unfolding num ..
  also have "\<dots> = (2 * sqrt X / (b - a))\<^sup>2"
    using X0 by (simp add: power_divide power_mult_distrib)
  finally have "sqrt (1 - ((2 * t - a - b) / (b - a))\<^sup>2) = \<bar>2 * sqrt X / (b - a)\<bar>"
    by simp
  also have "\<dots> = 2 * sqrt X / (b - a)" using ba X0 by simp
  finally show ?thesis by (simp add: X_def)
qed

lemma arcsine_dens_integral:
  assumes ab: "a < b"
  shows "(\<integral>\<^sup>+ t. ennreal (arcsine_dens a b t) \<partial>lborel) = 1"
proof -
  define u where "u t = (2 * t - a - b) / (b - a)" for t
  define F where "F t = arcsin (u t) / pi" for t
  define f where "f t = 1 / (pi * sqrt ((t - a) * (b - t)))" for t
  have ba: "0 < b - a" using ab by simp
  have u_rng: "- 1 < u t \<and> u t < 1" if "a < t" "t < b" for t
    using that ba by (auto simp: u_def field_simps)
  have u_rng': "- 1 \<le> u t \<and> u t \<le> 1" if "a \<le> t" "t \<le> b" for t
    using that ba by (auto simp: u_def field_simps)
  have deriv: "(F has_real_derivative f t) (at t)" if t: "a < t" "t < b" for t
  proof -
    have ue: "u = (\<lambda>t. (2 / (b - a)) * t - (a + b) / (b - a))"
      by (rule ext) (simp add: u_def diff_divide_distrib add_divide_distrib)
    have lin: "((\<lambda>t. c * t - e) has_real_derivative c) (at t)" for c e :: real
      by (auto intro!: derivative_eq_intros)
    have du: "(u has_real_derivative 2 / (b - a)) (at t)"
      unfolding ue by (rule lin)
    have "((\<lambda>t. arcsin (u t)) has_real_derivative inverse (sqrt (1 - (u t)\<^sup>2)) * (2 /
      (b - a))) (at t)"
      using DERIV_arcsin[of "u t"] u_rng[OF t] du by (intro DERIV_chain2) auto
    hence "(F has_real_derivative inverse (sqrt (1 - (u t)\<^sup>2)) * (2 / (b - a)) / pi) (at t)"
      unfolding F_def[abs_def] by (rule DERIV_cdivide)
    moreover have "inverse (sqrt (1 - (u t)\<^sup>2)) * (2 / (b - a)) / pi = f t"
    proof -
      have pos: "0 < (t - a) * (b - t)" using t by simp
      show ?thesis unfolding u_def arcsine_sqrt_identity[OF t] f_def
        using ba pos by (simp add: field_simps)
    qed
    ultimately show ?thesis by simp
  qed
  have contf: "isCont f t" if t: "a < t" "t < b" for t
  proof -
    have "0 < (t - a) * (b - t)" using t by simp
    thus ?thesis unfolding f_def by (auto intro!: continuous_intros)
  qed
  have contF: "continuous_on {a..b} F"
    unfolding F_def[abs_def] u_def
    by (intro continuous_intros continuous_on_arcsin) (use u_rng' ab in \<open>auto simp:
      u_def\<close>)
  have lima: "((F \<circ> real_of_ereal) \<longlongrightarrow> F a) (at_right (ereal a))"
    unfolding ereal_tendsto_simps by (rule continuous_on_Icc_at_rightD[OF contF ab])
  have limb: "((F \<circ> real_of_ereal) \<longlongrightarrow> F b) (at_left (ereal b))"
    unfolding ereal_tendsto_simps by (rule continuous_on_Icc_at_leftD[OF contF ab])
  have nonneg: "AE x in lborel. ereal a < ereal x \<longrightarrow>
    ereal x < ereal b \<longrightarrow> 0 \<le> f x"
    by (auto simp: f_def)
  note FTC = interval_integral_FTC_nonneg[of "ereal a" "ereal b" F f, OF _ _ _ nonneg lima limb]
  have si: "set_integrable lborel {a<..<b} f"
    using FTC(1) ab deriv contf by (simp add: einterval_eq_Icc)
  have ua: "u a = - 1" and ub: "u b = 1" using ba by (simp_all add: u_def field_simps)
  have Fab: "F b - F a = 1" by (simp add: F_def ua ub arcsin_minus_1)
  have int: "interval_lebesgue_integral lborel (ereal a) (ereal b) f = 1"
    using FTC(2) ab deriv contf Fab by simp
  have eq: "arcsine_dens a b t = indicator {a<..<b} t *\<^sub>R f t" for t
    by (simp add: arcsine_dens_def f_def indicator_def)
  have "(\<integral>\<^sup>+ t. ennreal (arcsine_dens a b t) \<partial>lborel) =
    ennreal (\<integral> t. indicator {a<..<b} t *\<^sub>R f t \<partial>lborel)"
    unfolding eq
    by (rule nn_integral_eq_integral) (use si in \<open>auto simp: set_integrable_def f_def
      indicator_def\<close>)
  also have "(\<integral> t. indicator {a<..<b} t *\<^sub>R f t \<partial>lborel) = 1"
    using int ab by (simp add: interval_lebesgue_integral_def einterval_eq_Icc
      set_lebesgue_integral_def)
  finally show ?thesis by simp
qed

lemma arcsine_dens_measurable [measurable]: "(\<lambda>t. arcsine_dens a b t) \<in>
  borel_measurable borel"
  unfolding arcsine_dens_def by measurable

theorem arcsine_univ: "a < b \<Longrightarrow> emeasure (arcsine a b) UNIV = 1"
  unfolding arcsine_def by (subst emeasure_density) (auto simp: arcsine_dens_integral)

text \<open>(A.1): the potential of the unit arcsine measure (Joukowski parameter, the integral of
  @{text "log|x - cos \<theta>|"} over a period;
    alternatively via @{text "Cauchy_integral_circlepath"}).\<close>
text \<open>The Joukowski radius @{text "|w|"} with @{text "w^2 + 1 = 2 x w"}: @{text "1"}
  for @{text "|x| \<le> 1"}, else @{text "|x| + \<surd>(x^2 - 1)"}.\<close>
definition jouk :: "real \<Rightarrow> real" where
  "jouk x = (if \<bar>x\<bar> \<le> 1 then 1 else \<bar>x\<bar> + sqrt (x ^ 2 - 1))"

lemma jouk_ge_1: "1 \<le> jouk x"
  unfolding jouk_def using real_sqrt_ge_zero[of "x ^ 2 - 1"]
      using abs_square_le_1[of x]
      by argo

lemma exists_w: "\<exists>w :: complex. w ^ 2 + 1 = 2 * of_real x * w \<and> norm w = jouk x"
proof (cases "\<bar>x\<bar> \<le> 1")
  case True
  define s where "s = sqrt (1 - x ^ 2)"
  have x2: "x ^ 2 \<le> 1" using True abs_square_le_1
    by blast
  have s2: "s ^ 2 = 1 - x ^ 2" unfolding s_def using x2
    by simp
  define w where "w = Complex x s"
  have e: "w ^ 2 + 1 = 2 * of_real x * w" unfolding w_def using s2
    by (simp add: complex_eq_iff power2_eq_square algebra_simps)
  have n: "norm w = 1" unfolding w_def cmod_def using s2
    by simp
  show ?thesis using e n True unfolding jouk_def
    by meson
next
  case False
  define s where "s = sqrt (x ^ 2 - 1)"
  have x2: "1 \<le> x ^ 2" using False abs_square_le_1[of x]
    by linarith
  have s2: "s ^ 2 = x ^ 2 - 1" unfolding s_def using x2
    by simp
  have s0: "0 \<le> s" unfolding s_def using x2
    by simp
  have sg: "sgn x * sgn x = 1" using False
    by (auto simp: sgn_if)
  define w where "w = complex_of_real (x + sgn x * s)"
  have e0: "(x + sgn x * s) ^ 2 + 1 = 2 * x * (x + sgn x * s)" using s2 sg
    by (simp add: power2_eq_square algebra_simps)
  have e: "w ^ 2 + 1 = 2 * of_real x * w" unfolding w_def
    using arg_cong[where f = complex_of_real, OF e0]
    by simp
  have n0: "\<bar>x + sgn x * s\<bar> = \<bar>x\<bar> + s" using s0 False
    by (force simp: sgn_if abs_if)
  have n: "norm w = \<bar>x\<bar> + s" unfolding w_def using n0
    unfolding norm_of_real
    by meson
  show ?thesis using e n False unfolding jouk_def s_def
    by metis
qed

lemma joukowski:
  assumes "w ^ 2 + 1 = 2 * of_real x * w"
  shows "norm (cis \<theta> - w) * norm (cis \<theta> - cnj w) =
    2 * norm w * \<bar>x - cos \<theta>\<bar>"
proof -
  define u where "u = Re w"
  define v where "v = Im w"
  define c where "c = cos \<theta>"
  define s where "s = sin \<theta>"
  have re: "u ^ 2 - v ^ 2 + 1 = 2 * x * u" using arg_cong[where f = Re, OF assms]
    unfolding u_def v_def
    by (simp add: power2_eq_square)
  have im: "2 * u * v = 2 * x * v" using arg_cong[where f = Im, OF assms] unfolding u_def v_def
    by (simp add: power2_eq_square)
  have cs: "c ^ 2 + s ^ 2 = 1" unfolding c_def s_def by simp
  have n1: "norm (cis \<theta> - w) ^ 2 = (c - u) ^ 2 + (s - v) ^ 2"
    unfolding c_def s_def u_def v_def
    by (simp add: cmod_power2)
  have n2: "norm (cis \<theta> - cnj w) ^ 2 = (c - u) ^ 2 + (s + v) ^ 2"
    unfolding c_def s_def u_def v_def
    by (simp add: cmod_power2)
  have nw: "norm w ^ 2 = u ^ 2 + v ^ 2" unfolding u_def v_def by (simp add: cmod_power2)
  have vu: "v = 0 \<or> u = x" using im by auto
  have sq0: "((c - u) ^ 2 + (s - v) ^ 2) * ((c - u) ^ 2 + (s + v) ^ 2) =
    4 * (u ^ 2 + v ^ 2) * (x - c) ^ 2"
  proof (cases "v = 0")
    case True
    have h: "(c - u) ^ 2 + s ^ 2 = 2 * u * (x - c)" using cs re True
      by (simp add: power2_eq_square algebra_simps)
    show ?thesis using h True
      by (simp add: power2_eq_square algebra_simps)
  next
    case False
    hence ux: "u = x" using vu by simp
    have v2: "v ^ 2 = 1 - x ^ 2" using re ux by (simp add: power2_eq_square)
    have s2: "s ^ 2 = 1 - c ^ 2" using cs by simp
    have fac: "((c - x) ^ 2 + (s - v) ^ 2) * ((c - x) ^ 2 + (s + v) ^ 2) =
      ((c - x) ^ 2 + s ^ 2 + v ^ 2) ^ 2 - 4 * s ^ 2 * v ^ 2"
      by (simp add: power2_eq_square algebra_simps)
    have fin: "((c - x) ^ 2 + (1 - c ^ 2) + (1 - x ^ 2)) ^ 2 - 4 * (1 - c ^ 2) * (1 - x ^ 2) =
      4 * (x ^ 2 + (1 - x ^ 2)) * (x - c) ^ 2"
      by (simp add: power2_eq_square algebra_simps)
    show ?thesis unfolding ux fac s2 v2 using fin
      by blast
  qed
  have sq: "(norm (cis \<theta> - w) * norm (cis \<theta> - cnj w)) ^ 2 =
    (2 * norm w * \<bar>x - cos \<theta>\<bar>) ^ 2"
    unfolding power_mult_distrib n1 n2 nw power2_abs c_def[symmetric] using sq0
    by simp
  show ?thesis using sq power2_eq_iff_nonneg[of "norm (cis \<theta> - w) * norm (cis \<theta> -
    cnj w)" "2 * norm w * \<bar>x - cos \<theta>\<bar>"]
    by simp
qed

lemma cos_level_null: "{\<theta> :: real. cos \<theta> = x} \<in> null_sets lborel"
proof (cases "\<bar>x\<bar> \<le> 1")
  case True
  have sub: "{\<theta> :: real. cos \<theta> = x} \<subseteq>
    range (\<lambda>n::int. arccos x + 2 * of_int n * pi) \<union> range (\<lambda>n::int. -
    arccos x + 2 * of_int n * pi)"
  proof
    fix \<theta> :: real assume th: "\<theta> \<in> {\<theta>. cos \<theta> = x}"
    have "cos \<theta> = cos (arccos x)" using th True
      by (simp add: cos_arccos_abs)
    then obtain n where n: "n \<in> \<int>" "\<theta> = arccos x + 2 * n * pi \<or>
      \<theta> = - arccos x + 2 * n * pi" using cos_eq by blast
    then obtain k :: int where "n = of_int k" using Ints_cases by blast
    thus "\<theta> \<in> range (\<lambda>n::int. arccos x + 2 * of_int n *
      pi) \<union> range (\<lambda>n::int. - arccos x + 2 * of_int n * pi)" using n(2)
      by fast
  qed
  show ?thesis using countable_imp_null_set_lborel countable_subset[OF sub]
    by fast
next
  case False
  hence "{\<theta> :: real. cos \<theta> = x} = {}" using abs_cos_le_one
    by blast
  thus ?thesis by simp
qed

lemma log_cos_pt:
  assumes w: "w ^ 2 + 1 = 2 * of_real x * w" and w1: "1 \<le> norm w" and th: "cos \<theta> \<noteq>
    x"
  shows "ln \<bar>x - cos \<theta>\<bar> =
    ln (norm (cis \<theta> - w)) + ln (norm (cis \<theta> - cnj w)) - ln 2 - ln (norm w)"
proof -
  have j: "norm (cis \<theta> - w) * norm (cis \<theta> - cnj w) =
    2 * norm w * \<bar>x - cos \<theta>\<bar>" by (rule joukowski[OF w])
  have p: "0 < 2 * norm w * \<bar>x - cos \<theta>\<bar>" using w1 th
    by (force intro: mult_pos_pos)
  have n1: "norm (cis \<theta> - w) \<noteq> 0" and n2: "norm (cis \<theta> - cnj w) \<noteq> 0"
    using j p by auto
  have "ln (norm (cis \<theta> - w) * norm (cis \<theta> - cnj w)) =
    ln (norm (cis \<theta> - w)) + ln (norm (cis \<theta> - cnj w))"
    using n1 n2 ln_mult by simp
  moreover have "ln (2 * norm w * \<bar>x - cos \<theta>\<bar>) =
    ln 2 + ln (norm w) + ln \<bar>x - cos \<theta>\<bar>"
    using w1 th ln_mult[of "2 * norm w" "\<bar>x - cos \<theta>\<bar>"] ln_mult[of 2 "norm w"]
    by fastforce
  ultimately show ?thesis unfolding j
    by linarith
qed

lemma log_cos_ae:
  assumes w: "w ^ 2 + 1 = 2 * of_real x * w" and w1: "1 \<le> norm w"
  shows "AE \<theta> in lborel. P \<theta> \<longrightarrow>
    ln \<bar>x - cos \<theta>\<bar> = (\<lambda>\<theta>. ln (norm (cis \<theta> - w)) +
    ln (norm (cis \<theta> - cnj w)) - ln 2 - ln (norm w)) \<theta>"
  using AE_I'[OF cos_level_null[of x], of "\<lambda>\<theta>. P \<theta> \<longrightarrow>
    ln \<bar>x - cos \<theta>\<bar> = (\<lambda>\<theta>. ln (norm (cis \<theta> - w)) +
    ln (norm (cis \<theta> - cnj w)) - ln 2 - ln (norm w)) \<theta>"] log_cos_pt[OF w w1]
  by blast

lemma log_cos_meas: "(\<lambda>\<theta> :: real. ln \<bar>x - cos \<theta>\<bar>) \<in>
  borel_measurable borel"
proof -
  have h: "(\<lambda>\<theta> :: real. \<bar>x - cos \<theta>\<bar>) \<in> borel_measurable borel"
    by (force intro: borel_measurable_continuous_onI continuous_intros)
  show ?thesis using borel_measurable_ln[OF h]
    by simp
qed

lemma log_cos_rhs_meas: "(\<lambda>\<theta>. ln (norm (cis \<theta> - w)) + ln (norm (cis \<theta> -
  cnj w)) - ln 2 - ln (norm w)) \<in> borel_measurable borel"
proof -
  have "(\<lambda>\<theta>. norm (cis \<theta> - w)) \<in>
    borel_measurable borel" "(\<lambda>\<theta>. norm (cis \<theta> - cnj w)) \<in>
    borel_measurable borel"
    by (fast intro: borel_measurable_continuous_onI continuous_intros)+
  thus ?thesis
    by (fastforce intro: borel_measurable_ln borel_measurable_add borel_measurable_diff)
qed

lemma log_cos_integrable: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 *
  pi)) (\<lambda>\<theta>. ln \<bar>x - cos \<theta>\<bar>)"
proof -
  obtain w :: complex where w: "w ^ 2 + 1 = 2 * of_real x * w" "norm w = jouk x" using exists_w
    by blast
  have w1: "1 \<le> norm w" using w(2) jouk_ge_1 by simp
  have ig: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - w)) + ln (norm (cis \<theta> - cnj w)) -
    ln 2 - ln (norm w))"
    using circle_log_integrable[of w] circle_log_integrable[of "cnj w"]
    by simp
  have ae: "AE \<theta> \<in> einterval (min (ereal 0) (ereal (2 * pi))) (max (ereal 0) (ereal (2 *
    pi))) in lborel. ln \<bar>x - cos \<theta>\<bar> =
    (\<lambda>\<theta>. ln (norm (cis \<theta> - w)) + ln (norm (cis \<theta> - cnj w)) - ln 2 -
    ln (norm w)) \<theta>"
    by (rule log_cos_ae[OF w(1) w1])
  show ?thesis using interval_lebesgue_integrable_cong_AE[OF _ _ ae] log_cos_meas[of x]
    log_cos_rhs_meas[of w] ig
    by simp
qed

text \<open>@{text "\<integral>_0^{2\<pi>} log|x - cos \<theta>| d\<theta> =
  2\<pi>(log jouk(x) - log 2)"}.\<close>
lemma log_cos_integral:
  "interval_lebesgue_integral lborel (ereal 0) (ereal (2 * pi)) (\<lambda>\<theta>. ln \<bar>x -
    cos \<theta>\<bar>) = 2 * pi * (ln (jouk x) - ln 2)"
proof -
  obtain w :: complex where w: "w ^ 2 + 1 = 2 * of_real x * w" "norm w = jouk x" using exists_w
    by blast
  have w1: "1 \<le> norm w" using w(2) jouk_ge_1 by simp
  have ae: "AE \<theta> \<in> einterval (min (ereal 0) (ereal (2 * pi))) (max (ereal 0) (ereal (2 *
    pi))) in lborel. ln \<bar>x - cos \<theta>\<bar> =
    (\<lambda>\<theta>. ln (norm (cis \<theta> - w)) + ln (norm (cis \<theta> - cnj w)) - ln 2 -
    ln (norm w)) \<theta>"
    by (rule log_cos_ae[OF w(1) w1])
  have "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln \<bar>x - cos \<theta>\<bar>) =
    interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - w)) + ln (norm (cis \<theta> - cnj w)) -
    ln 2 - ln (norm w))"
    using interval_integral_cong_AE[OF log_cos_meas[of x] log_cos_rhs_meas[of w] ae]
    by fast
  moreover have "interval_lebesgue_integral lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (cis \<theta> - w)) + ln (norm (cis \<theta> - cnj w)) -
    ln 2 - ln (norm w)) = 2 * pi * ln (norm w) + 2 * pi * ln (norm w) - ln 2 * (2 * pi) -
    ln (norm w) * (2 * pi)"
    using circle_log_integrable[of w] circle_log_integrable[of "cnj w"] circle_avg_log[of w]
      circle_avg_log[of "cnj w"] w1
    by (simp add: max_absorb2)
  ultimately show ?thesis unfolding w(2)[symmetric]
    by (simp add: algebra_simps)
qed

lemma log_cos_half:
  "interval_lebesgue_integral lborel (ereal 0) (ereal pi) (\<lambda>\<theta>. ln \<bar>x -
    cos \<theta>\<bar>) = pi * (ln (jouk x) - ln 2)"
proof -
  have s: "interval_lebesgue_integral lborel (ereal (0)) (ereal (pi)) (\<lambda>\<theta>. ln \<bar>x
    - cos \<theta>\<bar>) + interval_lebesgue_integral lborel (ereal (pi)) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln \<bar>x - cos \<theta>\<bar>) =
    interval_lebesgue_integral lborel (ereal (0)) (ereal (2 * pi)) (\<lambda>\<theta>. ln \<bar>x -
    cos \<theta>\<bar>)"
    using interval_integral_sum[of "ereal 0" "ereal pi" "ereal (2 *
      pi)" "(\<lambda>\<theta>. ln \<bar>x -
      cos \<theta>\<bar>)"] log_cos_integrable[of x] pi_gt_zero
    by simp
  have e: "(\<lambda>t. ln \<bar>x - cos (2 * pi - t)\<bar>) =
    (\<lambda>\<theta>. ln \<bar>x - cos \<theta>\<bar>)"
    by (simp add: cos_diff)
  have r: "interval_lebesgue_integral lborel (ereal (pi)) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln \<bar>x - cos \<theta>\<bar>) =
    interval_lebesgue_integral lborel (ereal (0)) (ereal (pi)) (\<lambda>\<theta>. ln \<bar>x -
    cos \<theta>\<bar>)"
    using LBINT_reflect[of pi "2 * pi" "(\<lambda>\<theta>. ln \<bar>x - cos \<theta>\<bar>)" "2 *
      pi"] pi_gt_zero unfolding e
    by simp
  show ?thesis using s r log_cos_integral[of x]
    by linarith
qed

lemma arcsine_integrable_ln:
  assumes ab: "a < b"
  shows "integrable (arcsine a b) (\<lambda>u. ln \<bar>t - u\<bar>)"
proof -
  define m where "m = (a + b) / 2"
  define r where "r = (b - a) / 2"
  define y where "y = (m - t) / r"
  define g where "g = (\<lambda>\<theta>. (a + b) / 2 - (b - a) / 2 * cos \<theta>)"
  define U where "U = density lborel (\<lambda>\<theta>. ennreal (indicator {0<..<pi} \<theta> /
    pi))"
  have r0: "0 < r" using ab unfolding r_def by simp
  have mg: "g \<in> borel_measurable borel" unfolding g_def
    by (fast intro: borel_measurable_continuous_onI continuous_intros)
  have mgU: "g \<in> measurable U borel" using mg unfolding U_def by simp
  have h: "(\<lambda>u :: real. \<bar>t - u\<bar>) \<in> borel_measurable borel"
    by (force intro: borel_measurable_continuous_onI continuous_intros)
  have mF: "(\<lambda>u :: real. ln \<bar>t - u\<bar>) \<in> borel_measurable borel"
    using borel_measurable_ln[OF h] by simp
  have mFg: "(\<lambda>\<theta>. ln \<bar>t - g \<theta>\<bar>) \<in> borel_measurable borel"
    using measurable_compose[OF mg mF] by (simp add: o_def)
  have e1: "integrable (arcsine a b) (\<lambda>u. ln \<bar>t - u\<bar>) =
    integrable U (\<lambda>\<theta>. ln \<bar>t - g \<theta>\<bar>)"
    unfolding arcsine_distr[OF ab] g_def[symmetric] U_def[symmetric]
      using integrable_distr_eq[OF mgU mF]
    by blast
  have e2: "integrable U (\<lambda>\<theta>. ln \<bar>t - g \<theta>\<bar>) =
    integrable lborel (\<lambda>\<theta>. (indicator {0<..<pi} \<theta> / pi) *\<^sub>R ln \<bar>t -
    g \<theta>\<bar>)"
    unfolding U_def using integrable_density[of "\<lambda>\<theta>. ln \<bar>t -
      g \<theta>\<bar>" lborel "\<lambda>\<theta>. indicator {0<..<pi} \<theta> / pi"] mFg
    by simp
  have fe: "(\<lambda>\<theta>. (indicator {0<..<pi} \<theta> / pi) *\<^sub>R ln \<bar>t -
    g \<theta>\<bar>) = (\<lambda>\<theta>. 1 / pi *
    (indicator {0<..<pi} \<theta> *\<^sub>R ln \<bar>t - g \<theta>\<bar>))"
    by (simp add: fun_eq_iff)
  have e3: "integrable lborel (\<lambda>\<theta>. (indicator {0<..<pi} \<theta> /
    pi) *\<^sub>R ln \<bar>t - g \<theta>\<bar>) =
    set_integrable lborel {0<..<pi} (\<lambda>\<theta>. ln \<bar>t - g \<theta>\<bar>)"
    unfolding set_integrable_def fe
    using integrable_mult_left_iff[of lborel "1 /
      pi" "\<lambda>\<theta>. indicator {0<..<pi} \<theta> *\<^sub>R ln \<bar>t -
      g \<theta>\<bar>"] pi_gt_zero
    by (simp add: divide_inverse mult.commute)
  have pw: "ln \<bar>t - g \<theta>\<bar> = ln r + ln \<bar>y - cos \<theta>\<bar>"
    if nc: "cos \<theta> \<noteq> y" for \<theta>
  proof -
    have e0: "t - g \<theta> = r * (cos \<theta> - y)" using r0 unfolding y_def g_def m_def r_def
      by (simp add: field_simps)
    have e: "\<bar>t - g \<theta>\<bar> = r * \<bar>y - cos \<theta>\<bar>" unfolding e0 using r0
      by (simp add: abs_mult abs_minus_commute)
    show ?thesis unfolding e using r0 nc ln_mult[of r "\<bar>y - cos \<theta>\<bar>"] by simp
  qed
  have ae: "AE \<theta> \<in> {0<..<pi} in lborel. (\<lambda>\<theta>. ln \<bar>t -
    g \<theta>\<bar>) \<theta> = (\<lambda>\<theta> :: real. ln r + ln \<bar>y -
    cos \<theta>\<bar>) \<theta>"
    using AE_I'[OF cos_level_null[of y], of "\<lambda>\<theta>. \<theta> \<in>
      {0<..<pi} \<longrightarrow> (\<lambda>\<theta>. ln \<bar>t - g \<theta>\<bar>) \<theta> =
      (\<lambda>\<theta> :: real. ln r + ln \<bar>y - cos \<theta>\<bar>) \<theta>"] pw by fast
  have mG: "(\<lambda>\<theta> :: real. ln r + ln \<bar>y - cos \<theta>\<bar>) \<in>
    borel_measurable borel" using log_cos_meas[of y] by (auto intro: borel_measurable_add)
  have "interval_lebesgue_integrable lborel (ereal 0) (ereal pi) (\<lambda>\<theta>. ln \<bar>y -
    cos \<theta>\<bar>)"
    using interval_integrable_sub[OF _ _ _ log_cos_integrable[of y], of 0 pi] pi_gt_zero by simp
  hence i1: "set_integrable lborel {0<..<pi} (\<lambda>\<theta>. ln \<bar>y - cos \<theta>\<bar>)"
    using pi_gt_zero unfolding interval_lebesgue_integrable_def by simp
  have c1: "set_integrable lborel {0<..<pi} (\<lambda>\<theta>::real. ln r)"
    using interval_integral_const(1)[of 0 pi "ln r"] pi_gt_zero
      unfolding interval_lebesgue_integrable_def by simp
  have sG: "set_integrable lborel {0<..<pi} (\<lambda>\<theta> :: real. ln r + ln \<bar>y -
    cos \<theta>\<bar>)" using set_integral_add(1)[OF c1 i1] .
  have si: "set_integrable lborel {0<..<pi} (\<lambda>\<theta>. ln \<bar>t - g \<theta>\<bar>)"
    using set_integrable_cong_AE[of "\<lambda>\<theta>. ln \<bar>t -
      g \<theta>\<bar>" lborel "\<lambda>\<theta>. ln r + ln \<bar>y -
      cos \<theta>\<bar>" "{0<..<pi}"] mFg mG ae sG
    by simp
  show ?thesis using e1 e2 e3 si by simp
qed

lemma dens_ln_meas: "(\<lambda>u :: real. ln \<bar>t - u\<bar>) \<in> borel_measurable borel"
proof -
  have h: "(\<lambda>u :: real. \<bar>t - u\<bar>) \<in> borel_measurable borel"
    by (force intro: borel_measurable_continuous_onI continuous_intros)
  show ?thesis using borel_measurable_ln[OF h] by simp
qed

lemma dens_ln_integrable:
  assumes ab: "a < b"
  shows "integrable lborel (\<lambda>u. arcsine_dens a b u * ln \<bar>t - u\<bar>)"
proof -
  have md: "(\<lambda>u. arcsine_dens a b u) \<in> borel_measurable borel"
    unfolding arcsine_dens_def by measurable
  have nn: "AE u in lborel. 0 \<le> arcsine_dens a b u" by (simp add: arcsine_dens_def)
  show ?thesis using arcsine_integrable_ln[OF ab,
    of t] integrable_density[of "\<lambda>u. ln \<bar>t -
    u\<bar>" lborel "arcsine_dens a b"] dens_ln_meas[of t] md nn
    unfolding arcsine_def
    by simp
qed

lemma dens_ln_integral:
  shows "(\<integral> u. arcsine_dens a b u * ln \<bar>t - u\<bar> \<partial>lborel) =
    logPot (arcsine a b) t"
proof -
  have md: "(\<lambda>u. arcsine_dens a b u) \<in> borel_measurable borel"
    unfolding arcsine_dens_def by measurable
  have nn: "AE u in lborel. 0 \<le> arcsine_dens a b u" by (simp add: arcsine_dens_def)
  show ?thesis unfolding logPot_def arcsine_def
    using integral_density[of "\<lambda>u. ln \<bar>t -
    u\<bar>" lborel "arcsine_dens a b"] dens_ln_meas[of t] md nn
    by simp
qed

text \<open>(A.1): the potential of the unit arcsine measure.\<close>
theorem arcsine_potential:
  assumes "a < b"
  shows "logPot (arcsine a b) t =
         (if a \<le> t \<and> t \<le> b then ln ((b - a) / 4)
          else ln ((\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2))"
proof -
  define m where "m = (a + b) / 2"
  define r where "r = (b - a) / 2"
  define y where "y = (m - t) / r"
  have r0: "0 < r" using assms unfolding r_def by simp
  have "logPot (arcsine a b) t = 1 / pi *
    set_lebesgue_integral lborel {0<..<pi} (\<lambda>\<theta>. ln \<bar>t - (m - r *
    cos \<theta>)\<bar>)"
    unfolding logPot_def m_def r_def by (rule integral_arcsine[OF assms]) measurable
  also have "\<dots> = 1 / pi * set_lebesgue_integral lborel {0<..<pi} (\<lambda>\<theta>. ln r +
    ln \<bar>y - cos \<theta>\<bar>)"
  proof -
    have pw: "ln \<bar>t - (m - r * cos \<theta>)\<bar> = ln r + ln \<bar>y - cos \<theta>\<bar>"
      if nc: "cos \<theta> \<noteq> y" for \<theta>
    proof -
      have e: "\<bar>t - (m - r * cos \<theta>)\<bar> = r * \<bar>y - cos \<theta>\<bar>" using r0
        unfolding y_def
        by (simp add: field_simps abs_mult abs_minus_commute)
      show ?thesis unfolding e using r0 nc ln_mult[of r "\<bar>y - cos \<theta>\<bar>"] by simp
    qed
    have ae: "AE \<theta> \<in> {0<..<pi} in lborel. (\<lambda>\<theta> :: real. ln \<bar>t - (m -
      r * cos \<theta>)\<bar>) \<theta> =
      (\<lambda>\<theta> :: real. ln r + ln \<bar>y - cos \<theta>\<bar>) \<theta>"
      using AE_I'[OF cos_level_null[of y], of "\<lambda>\<theta>. \<theta> \<in>
        {0<..<pi} \<longrightarrow> (\<lambda>\<theta> :: real. ln \<bar>t - (m - r *
        cos \<theta>)\<bar>) \<theta> = (\<lambda>\<theta> :: real. ln r + ln \<bar>y -
        cos \<theta>\<bar>) \<theta>"] pw
      by fast
    have mf: "(\<lambda>\<theta> :: real. ln \<bar>t - (m - r * cos \<theta>)\<bar>) \<in>
      borel_measurable lborel"
    proof -
      have h: "(\<lambda>\<theta> :: real. \<bar>t - (m - r * cos \<theta>)\<bar>) \<in>
        borel_measurable borel"
        by (force intro: borel_measurable_continuous_onI continuous_intros)
      show ?thesis using borel_measurable_ln[OF h] by simp
    qed
    have mg: "(\<lambda>\<theta> :: real. ln r + ln \<bar>y - cos \<theta>\<bar>) \<in>
      borel_measurable lborel" using log_cos_meas[of y]
      by (auto intro: borel_measurable_add)
    show ?thesis using set_lebesgue_integral_cong_AE[OF _ mf mg ae]
      by simp
  qed
  also have "\<dots> = 1 / pi * (pi * ln r + pi * (ln (jouk y) - ln 2))"
  proof -
    have "interval_lebesgue_integrable lborel (ereal 0) (ereal pi) (\<lambda>\<theta>. ln \<bar>y -
      cos \<theta>\<bar>)"
      using interval_integrable_sub[OF _ _ _ log_cos_integrable[of y], of 0 pi] pi_gt_zero
      by simp
    hence i1: "set_integrable lborel {0<..<pi} (\<lambda>\<theta>. ln \<bar>y -
      cos \<theta>\<bar>)" using pi_gt_zero unfolding interval_lebesgue_integrable_def
      by simp
    have v1: "set_lebesgue_integral lborel {0<..<pi} (\<lambda>\<theta>. ln \<bar>y -
      cos \<theta>\<bar>) = pi * (ln (jouk y) - ln 2)"
      using log_cos_half[of y] interval_lebesgue_integral_le_eq[of "ereal 0" "ereal pi" lborel
        "(\<lambda>\<theta>. ln \<bar>y - cos \<theta>\<bar>)"] pi_gt_zero
      by simp
    have c1: "set_integrable lborel {0<..<pi} (\<lambda>\<theta>::real. ln r)"
      using interval_integral_const(1)[of 0 pi "ln r"] pi_gt_zero
        unfolding interval_lebesgue_integrable_def
      by simp
    have c2: "set_lebesgue_integral lborel {0<..<pi} (\<lambda>\<theta>::real. ln r) = pi * ln r"
      using interval_integral_const(2)[of 0 pi "ln r"] pi_gt_zero
        unfolding interval_lebesgue_integral_def
      by auto
    show ?thesis using set_integral_add(2)[OF c1 i1] c2 v1
      by simp
  qed
  also have "\<dots> = (if a \<le> t \<and>
    t \<le> b then ln ((b - a) / 4) else ln ((\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t -
    b))) / 2))"
  proof -
    have iff: "\<bar>y\<bar> \<le> 1 \<longleftrightarrow> a \<le> t \<and> t \<le> b" using r0
      unfolding y_def m_def r_def
      by (auto simp: abs_le_iff field_simps)
    have e0: "1 / pi * (pi * ln r + pi * (ln (jouk y) - ln 2)) = ln r + ln (jouk y) - ln 2"
      by (simp add: field_simps)
    have bm: "(b - a) / 4 = r / 2" unfolding r_def by simp
    have p0: "0 < jouk y" using jouk_ge_1[of y] by simp
    show ?thesis
    proof (cases "a \<le> t \<and> t \<le> b")
      case True
      hence "jouk y = 1" using iff unfolding jouk_def by simp
      thus ?thesis unfolding e0 bm using True r0 ln_div[of r 2]
        by simp
    next
      case False
      have y1: "1 < \<bar>y\<bar>" using iff False by linarith
      have j: "jouk y = \<bar>y\<bar> + sqrt (y ^ 2 - 1)" using y1 unfolding jouk_def by simp
      have q1: "r * \<bar>y\<bar> = \<bar>t - (a + b) / 2\<bar>" using r0 unfolding y_def m_def
        by (simp add: abs_divide abs_minus_commute)
      have q2b: "r ^ 2 * (y ^ 2 - 1) = (m - t) ^ 2 - r ^ 2" using r0 unfolding y_def
        by (simp add: field_simps power2_eq_square)
      have q2c: "(m - t) ^ 2 - r ^ 2 = (t - a) * (t - b)" unfolding m_def r_def
        by (simp add: power2_eq_square algebra_simps field_simps)
      have q2a: "r ^ 2 * (y ^ 2 - 1) = (t - a) * (t - b)" using q2b q2c
        by simp
      have q2: "r * sqrt (y ^ 2 - 1) = sqrt ((t - a) * (t - b))"
        using q2a r0 real_sqrt_mult[of "r ^ 2" "y ^ 2 - 1"]
        by simp
      have q3: "(\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2 = r * jouk y / 2"
        using q1 q2 j
        by (metis distrib_left)
      have fin: "ln r + ln (jouk y) - ln 2 =
        ln ((\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2)"
        unfolding q3 using r0 p0 ln_div[of "r * jouk y" 2] ln_mult[of r "jouk y"]
        by simp
      show ?thesis unfolding e0 using False fin
        by presburger
    qed
  qed
  finally show ?thesis .
qed

lemma arcsine_dens_nonneg: "0 \<le> arcsine_dens a b t"
  by (simp add: arcsine_dens_def)

lemma arcsine_finite: "a < b \<Longrightarrow> finite_measure (arcsine a b)"
  using arcsine_univ[of a b] unfolding arcsine_def
  by (fastforce intro: finite_measureI)

lemma arcsine_AE: "AE x in arcsine a b. a < x \<and> x < b"
proof -
  have md: "(\<lambda>t. ennreal (arcsine_dens a b t)) \<in> borel_measurable lborel"
    unfolding arcsine_dens_def by measurable
  show ?thesis unfolding arcsine_def using AE_density[OF md]
    by (simp add: arcsine_dens_def)
qed


lemma abs_ln_bound:
  fixes z :: real
  assumes "0 \<le> z" "z < 2"
  shows "\<bar>ln z\<bar> \<le> 2 * ln 2 - ln z"
proof (cases "z = 0")
  case True
  thus ?thesis
    by simp
next
  case False
  hence z0: "0 < z" using assms by simp
  have "ln z \<le> ln 2" using z0 assms
    by simp
  thus ?thesis using ln_gt_zero[of "2::real"]
    by linarith
qed

lemma arcsine_swap:
  fixes a b c d L :: real
  assumes ab: "a < b" "0 < a" "b < 2" and cd: "c < d" "0 < c" "d < 2"
    and bnd: "\<And>x. 0 < x \<Longrightarrow> x < 2 \<Longrightarrow>
      L \<le> logPot (arcsine c d) x"
  shows "integral\<^sup>L (arcsine a b) (logPot (arcsine c d)) =
    integral\<^sup>L (arcsine c d) (logPot (arcsine a b))"
proof -
  have fm1: "finite_measure (arcsine a b)" by (rule arcsine_finite[OF ab(1)])
  have fm2: "finite_measure (arcsine c d)" by (rule arcsine_finite[OF cd(1)])
  have ps: "pair_sigma_finite (arcsine a b) (arcsine c d)" using fm1 fm2
    by (simp add: pair_sigma_finite_def finite_measure_def)
  have sf2: "sigma_finite_measure (arcsine c d)" using fm2 unfolding finite_measure_def by simp
  have sets1: "sets (arcsine a b) = sets borel" and sets2: "sets (arcsine c d) = sets borel"
    unfolding arcsine_def by simp_all
  have meas: "(\<lambda>p. ln \<bar>fst p - snd p\<bar>) \<in>
    borel_measurable (arcsine a b \<Otimes>\<^sub>M arcsine c d)"
    unfolding measurable_cong_sets[OF sets_pair_measure_cong[OF sets1 sets2] refl] by measurable
  have inner: "(\<integral>\<^sup>+ y. ennreal (norm (ln \<bar>x -
    y\<bar>)) \<partial>arcsine c d) \<le> ennreal (2 * ln 2 - L)" if x: "0 < x" "x < 2" for x
  proof -
    have i1: "(\<integral>\<^sup>+ y. ennreal (norm (ln \<bar>x -
      y\<bar>)) \<partial>arcsine c d) \<le>
      (\<integral>\<^sup>+ y. ennreal (2 * ln 2 - ln \<bar>x - y\<bar>) \<partial>arcsine c d)"
    proof (rule nn_integral_mono_AE)
      have "\<bar>ln \<bar>x - y\<bar>\<bar> \<le> 2 * ln 2 - ln \<bar>x - y\<bar>"
        if "c < y \<and> y < d" for y
        using abs_ln_bound[of "\<bar>x - y\<bar>"] that x cd
        by linarith
      thus "AE y in arcsine c d. ennreal (norm (ln \<bar>x - y\<bar>)) \<le>
        ennreal (2 * ln 2 - ln \<bar>x - y\<bar>)"
        using arcsine_AE[of c d]
        by (auto intro: ennreal_leI elim: AE_mp)
    qed
    have ig: "integrable (arcsine c d) (\<lambda>y. 2 * ln 2 - ln \<bar>x - y\<bar>)"
      using arcsine_integrable_ln[OF cd(1), of x] fm2
      by (fast intro: Bochner_Integration.integrable_diff finite_measure.integrable_const)
    have nn0: "0 \<le> 2 * ln 2 - ln \<bar>x - y\<bar>" if "c < y \<and> y < d" for y
      using abs_ln_bound[of "\<bar>x - y\<bar>"] that x cd
      by linarith
    have nn: "AE y in arcsine c d. 0 \<le> 2 * ln 2 - ln \<bar>x - y\<bar>"
      using arcsine_AE[of c d] nn0
      by (fast elim: AE_mp)
    have i2: "(\<integral>\<^sup>+ y. ennreal (2 * ln 2 - ln \<bar>x -
      y\<bar>) \<partial>arcsine c d) = ennreal (\<integral> y. 2 * ln 2 - ln \<bar>x -
      y\<bar> \<partial>arcsine c d)"
      using nn_integral_eq_integral[OF ig nn] .
    have mu: "measure (arcsine c d) (space (arcsine c d)) = 1" using arcsine_univ[OF cd(1)]
      unfolding arcsine_def
      by (simp add: measure_def)
    have i3: "(\<integral> y. 2 * ln 2 - ln \<bar>x - y\<bar> \<partial>arcsine c d) =
      2 * ln 2 - logPot (arcsine c d) x"
      using Bochner_Integration.integral_diff[of "arcsine c d" "\<lambda>y. 2 *
        ln 2" "\<lambda>y. ln \<bar>x - y\<bar>"] arcsine_integrable_ln[OF cd(1),
        of x] finite_measure.integrable_const[OF fm2] mu
      unfolding logPot_def
      by fastforce
    show ?thesis using i1 i2 i3 bnd[OF x]
      by (fastforce intro: order_trans ennreal_leI)
  qed
  have outer: "(\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. ennreal (norm (ln \<bar>x -
    y\<bar>)) \<partial>arcsine c d) \<partial>arcsine a b) \<le>
    (\<integral>\<^sup>+ x. ennreal (2 * ln 2 - L) \<partial>arcsine a b)"
    using arcsine_AE[of a b] inner ab
    by (fastforce intro: nn_integral_mono_AE elim: AE_mp)
  have fin: "(\<integral>\<^sup>+ x. ennreal (2 * ln 2 - L) \<partial>arcsine a b) < \<infinity>"
    using arcsine_univ[OF ab(1)] unfolding arcsine_def
    by simp
  have pr: "(\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. ennreal (norm (ln \<bar>x -
    y\<bar>)) \<partial>arcsine c d) \<partial>arcsine a b) =
    (\<integral>\<^sup>+ p. ennreal (norm (ln \<bar>fst p -
    snd p\<bar>)) \<partial>(arcsine a b \<Otimes>\<^sub>M arcsine c d))"
    using sigma_finite_measure.nn_integral_fst[OF sf2,
      of "\<lambda>p. ennreal (norm (ln \<bar>fst p - snd p\<bar>))" "arcsine a b"] meas
    by simp
  have intg: "integrable (arcsine a b \<Otimes>\<^sub>M arcsine c d) (\<lambda>(x,
    y). ln \<bar>x - y\<bar>)"
    using integrable_iff_bounded[of "arcsine a b \<Otimes>\<^sub>M arcsine c d" "\<lambda>p. ln
      \<bar>fst p - snd p\<bar>"] meas outer fin pr
    by (simp add: case_prod_beta')
  have F: "(\<integral>y. (\<integral>x. ln \<bar>x -
    y\<bar> \<partial>arcsine a b) \<partial>arcsine c d) =
    (\<integral>x. (\<integral>y. ln \<bar>x -
    y\<bar> \<partial>arcsine c d) \<partial>arcsine a b)"
    using pair_sigma_finite.Fubini_integral[OF ps, of "\<lambda>x y. ln \<bar>x - y\<bar>"] intg
      by simp
  show ?thesis unfolding logPot_def using F
    by (simp add: abs_minus_commute)
qed

text \<open>@{text "\<omega>_{[a,b]}([x - r, x + r]) \<le> 8\<surd>r/(\<pi>\<surd>(b - a))"}: the
  density is dominated by @{text "(\<pi>\<surd>((b-a)/2))^-^1 ((u - a)^{-1/2} + (b -
    u)^{-1/2})"}.\<close>
lemma cos_gap:
  fixes s t :: real
  assumes st: "0 \<le> s" "s \<le> t" "t \<le> pi"
  shows "2 * ((t - s) / pi) ^ 2 \<le> cos s - cos t"
proof -
  define d where "d = (t - s) / 2"
  define y where "y = (s + t) / 2"
  have cd: "cos s - cos t = 2 * sin y * sin d" unfolding y_def d_def by (rule cos_diff_cos)
  have d0: "0 \<le> d" "d \<le> pi / 2" using st unfolding d_def by auto
  have sd: "2 * d / pi \<le> sin d" by (rule sin_ge_two_over_pi[OF d0])
  have p2: "0 \<le> 2 * d / pi" using d0 by simp
  have sy: "sin d \<le> sin y"
  proof (cases "y \<le> pi / 2")
    case True
    thus ?thesis using sin_monotone_2pi_le[of d y] d0 st unfolding y_def d_def
      by simp
  next
    case False
    have "sin d \<le> sin (pi - y)"
    proof (rule sin_monotone_2pi_le)
      show "- (pi / 2) \<le> d" using d0 pi_gt_zero by linarith
      show "d \<le> pi - y" using st unfolding y_def d_def by argo
      show "pi - y \<le> pi / 2" using False unfolding y_def by linarith
    qed
    thus ?thesis by simp
  qed
  have "(2 * d / pi) * (2 * d / pi) \<le> sin d * sin y" using sd sy p2
    by (fastforce intro: mult_mono)
  thus ?thesis unfolding cd d_def
    by (simp add: power2_eq_square field_simps)
qed

lemma diam_measure:
  fixes S :: "real set" and D :: real
  assumes ne: "S \<noteq> {}" and bdd: "\<forall>x\<in>S. 0 \<le> x" and dm: "\<And>x y. x \<in>
    S \<Longrightarrow> y \<in> S \<Longrightarrow> y - x \<le> D"
  shows "emeasure lborel S \<le> ennreal D"
proof -
  define c where "c = Inf S"
  have b: "bdd_below S" using bdd
    by (fast intro: bdd_belowI)
  have sub: "S \<subseteq> {c..c + D}"
  proof
    fix x assume x: "x \<in> S"
    have "c \<le> x" unfolding c_def using cInf_lower[OF x b] .
    moreover have lb: "x - D \<le> y" if "y \<in> S" for y using dm[OF that x]
      by force
    moreover have "x - D \<le> c" unfolding c_def using cInf_greatest[OF ne lb]
      by blast
    ultimately show "x \<in> {c..c + D}" by simp
  qed
  obtain x0 where "x0 \<in> S" using ne by blast
  hence D0: "0 \<le> D" using dm[of x0 x0] by simp
  have "emeasure lborel S \<le> emeasure lborel {c..c + D}" by (rule emeasure_mono[OF sub]) simp
  also have "\<dots> = ennreal D" using D0
    by simp
  finally show ?thesis .
qed

lemma arcsine_Icc_le:
  assumes "a < b" "0 \<le> r"
  shows "emeasure (arcsine a b) {x - r..x + r} \<le> ennreal (8 * sqrt r / (pi * sqrt (b - a)))"
proof -
  define R where "R = (b - a) / 2"
  define g where "g = (\<lambda>\<theta>. (a + b) / 2 - (b - a) / 2 * cos \<theta>)"
  define U where "U = density lborel (\<lambda>\<theta>. ennreal (indicator {0<..<pi} \<theta> /
    pi))"
  define S where "S = {\<theta> \<in> {0<..<pi}. g \<theta> \<in> {x - r..x + r}}"
  define l where "l = 2 * r / R"
  have R0: "0 < R" using assms unfolding R_def by simp
  have mg: "g \<in> borel_measurable borel" unfolding g_def
    by (fast intro: borel_measurable_continuous_onI continuous_intros)
  have mgU: "g \<in> measurable U borel" using mg unfolding U_def by simp
  have Se: "S = {0<..<pi} \<inter> (g -` {x - r..x + r} \<inter> space borel)" unfolding S_def
    by auto
  have Sm: "S \<in> sets lborel" unfolding Se using measurable_sets[OF mg, of "{x - r..x + r}"]
    by (force intro: sets.Int)
  have e1: "emeasure (arcsine a b) {x - r..x + r} =
    (\<integral>\<^sup>+ \<theta>. ennreal (indicator {0<..<pi} \<theta> / pi) *
    indicator (g -` {x - r..x + r}) \<theta> \<partial>lborel)"
    unfolding arcsine_distr[OF assms(1)] g_def[symmetric] U_def[symmetric]
      using emeasure_distr[OF mgU, of "{x - r..x + r}"] measurable_sets[OF mg, of "{x - r..x + r}"]
      unfolding U_def
    by (force simp: emeasure_density)
  have e2: "(\<integral>\<^sup>+ \<theta>. ennreal (indicator {0<..<pi} \<theta> / pi) *
    indicator (g -` {x - r..x + r}) \<theta> \<partial>lborel) =
    ennreal (1 / pi) * emeasure lborel S"
  proof -
    have "(\<lambda>\<theta>. ennreal (indicator {0<..<pi} \<theta> / pi) * indicator (g -` {x -
      r..x + r}) \<theta>) = (\<lambda>\<theta>. ennreal (1 / pi) * indicator S \<theta>)"
      unfolding S_def
      by (simp add: indicator_def fun_eq_iff)
    thus ?thesis using nn_integral_cmult_indicator[OF Sm, of "ennreal (1 / pi)"] by simp
  qed
  have e3: "emeasure lborel S \<le> ennreal (pi * sqrt (l / 2))"
  proof (cases "S = {}")
    case True
    thus ?thesis by simp
  next
    case False
    have bdd: "\<forall>\<theta>\<in>S. 0 \<le> \<theta>" unfolding S_def by auto
    have lp: "0 \<le> pi * sqrt (l / 2)" unfolding l_def using R0 assms by simp
    have dm: "\<theta>2 - \<theta>1 \<le> pi * sqrt (l / 2)"
      if th: "\<theta>1 \<in> S" "\<theta>2 \<in> S" for \<theta>1 \<theta>2
    proof (cases "\<theta>2 \<le> \<theta>1")
      case True
      thus ?thesis using lp by linarith
    next
      case False
      have t: "0 \<le> \<theta>1" "\<theta>1 \<le> \<theta>2" "\<theta>2 \<le> pi" using th False
        unfolding S_def by auto
      have cg: "2 * ((\<theta>2 - \<theta>1) / pi) ^ 2 \<le> cos \<theta>1 - cos \<theta>2"
        by (rule cos_gap[OF t])
      have gi: "g \<theta>2 - g \<theta>1 \<le> 2 * r" using th unfolding S_def by auto
      have gc: "g \<theta>2 - g \<theta>1 = R * (cos \<theta>1 - cos \<theta>2)"
        unfolding g_def R_def
        by (simp add: field_simps)
      have cl: "cos \<theta>1 - cos \<theta>2 \<le> l" using gi gc R0 unfolding l_def
        by (auto simp: pos_le_divide_eq mult.commute)
      have sq: "((\<theta>2 - \<theta>1) / pi) ^ 2 \<le> l / 2" using cg cl by linarith
      have "(\<theta>2 - \<theta>1) / pi \<le> sqrt (l / 2)" using real_le_rsqrt[OF sq] .
      thus ?thesis using pi_gt_zero
        by (fastforce simp: field_simps)
    qed
    show ?thesis by (rule diam_measure[OF False bdd dm])
  qed
  have e4: "ennreal (1 / pi) * ennreal (pi * sqrt (l / 2)) \<le>
    ennreal (8 * sqrt r / (pi * sqrt (b - a)))"
  proof -
    have l0: "0 \<le> sqrt (l / 2)" unfolding l_def using R0 assms by simp
    have q0: "ennreal (1 / pi) * ennreal (pi * sqrt (l / 2)) = ennreal (sqrt (l / 2))"
      using ennreal_mult[of "1 / pi" "pi * sqrt (l / 2)"] pi_gt_zero l0
      by force
    have q1: "l / 2 = 2 * r / (b - a)" unfolding l_def R_def using assms by (simp add: field_simps)
    have q2: "sqrt (2 * r / (b - a)) = sqrt 2 * sqrt r / sqrt (b - a)"
      by (simp add: real_sqrt_mult real_sqrt_divide)
    have q3: "sqrt 2 < 3 / 2" using real_less_lsqrt[of "3 / 2" 2]
      by (simp add: power2_eq_square)
    have q4a: "sqrt 2 * pi \<le> 3 / 2 * 4" using q3 pi_less_4 pi_gt_zero
      by (fastforce intro: mult_mono)
    have q4: "sqrt 2 * pi \<le> 8" using q4a
      by linarith
    have k5: "sqrt 2 * pi * sqrt r \<le> 8 * sqrt r" using q4 real_sqrt_ge_zero[OF assms(2)]
      by (fast intro: mult_right_mono)
    have ba: "0 < sqrt (b - a)" using assms by simp
    have q5: "sqrt 2 * sqrt r / sqrt (b - a) \<le> 8 * sqrt r / (pi * sqrt (b - a))"
      using k5 ba pi_gt_zero
      by (simp add: field_simps)
    show ?thesis unfolding q0 unfolding q1 q2 using q5
      by (blast intro: ennreal_leI)
  qed
  have e5: "ennreal (1 / pi) * emeasure lborel S \<le>
    ennreal (1 / pi) * ennreal (pi * sqrt (l / 2))"
    using e3
    by (force intro: mult_left_mono)
  show ?thesis unfolding e1 e2 using e5 e4
    by (fast intro: order_trans)
qed

lemma arcsine_Icc_le40:
  assumes "a < b" "1 / 225 < b - a" "0 \<le> r"
  shows "emeasure (arcsine a b) {x - r..x + r} \<le> ennreal (40 * sqrt r)"
proof -
  have s1: "1 / 15 < sqrt (b - a)" using real_less_rsqrt[of "1 / 15" "b - a"] assms(2)
    by (simp add: power2_eq_square)
  have p0: "3 * (1 / 15) \<le> pi * sqrt (b - a)" using s1 pi_gt3
    by (fastforce intro: mult_mono)
  have p: "1 / 5 \<le> pi * sqrt (b - a)" using p0
    by simp
  have q: "8 \<le> 40 * (pi * sqrt (b - a))" using p by linarith
  have k: "8 * sqrt r \<le> 40 * sqrt r * (pi * sqrt (b - a))"
    using mult_left_mono[OF q real_sqrt_ge_zero[OF assms(3)]]
    by (auto simp: algebra_simps)
  have pp: "0 < pi * sqrt (b - a)" using p by linarith
  have "8 * sqrt r / (pi * sqrt (b - a)) \<le> 40 * sqrt r" using k pp
    using pos_divide_le_eq by blast
  thus ?thesis using arcsine_Icc_le[OF assms(1) assms(3), of x] by (meson ennreal_leI order_trans)
qed
end
