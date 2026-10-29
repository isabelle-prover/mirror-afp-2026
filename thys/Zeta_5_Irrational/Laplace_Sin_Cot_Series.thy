(*  Title:   Laplace_Sin_Cot_Series.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Laplace_Sin_Cot_Series
  imports "HOL-Analysis.Analysis" "Cotangent_PFD_Formula.Cotangent_PFD_Formula"
begin

section \<open>Gamma-type integrals, the Laplace transform of \<open>sin\<close> and the
  \<open>coth\<close> series\<close>

text \<open>Integrals \<open>\<integral>\<^sub>0\<^sup>\<infinity> y\<^sup>k
  e\<^sup>-\<^sup>c\<^sup>y dy\<close> on the open half-line by the fundamental theorem of calculus,
  the interchange of \<open>\<integral>\<close> and \<open>\<Sum>\<close>
    for non-negative series, the Mittag-Leffler expansion of \<open>coth\<close>
  (from the AFP's cotangent partial-fraction formula),
    the series \<open>\<Sum>\<^sub>l u / (u\<^sup>2 + (2\<pi>l)\<^sup>2)\<close>, the
  Laplace transform \<open>\<integral>\<^sub>0\<^sup>\<infinity> e\<^sup>-\<^sup>c\<^sup>y sin(ay)
    dy\<close>, and the integrals
  \<open>\<Psi>(a, c) = \<integral>\<^sub>0\<^sup>\<infinity> e\<^sup>-\<^sup>c\<^sup>y y/(y\<^sup>2
    + a\<^sup>2) dy\<close>, \<open>\<Phi>(a, c) =
    \<integral>\<^sub>0\<^sup>\<infinity> y\<^sup>5 e\<^sup>-\<^sup>c\<^sup>y/(y\<^sup>2 +
    a\<^sup>2) dy\<close> and the geometric
  pole sums.\<close>

subsection \<open>Gamma integrals and the interchange of @{text \<integral>} and
  @{text \<Sum>}\<close>

lemma set_bm_cont: "continuous_on UNIV f \<Longrightarrow>
  set_borel_measurable lborel {0<..} (f :: real \<Rightarrow> real)"
  unfolding set_borel_measurable_def
  by (intro borel_measurable_scaleR borel_measurable_indicator) (simp_all add:
    borel_measurable_continuous_onI)

lemma ftc_Ioi_nonneg:
  fixes f F :: "real \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel"
    and D: "\<And>x. 0 \<le> x \<Longrightarrow> (F has_real_derivative f x) (at x)"
    and nn: "\<And>x. 0 \<le> x \<Longrightarrow> 0 \<le> f x"
    and T: "(F \<longlongrightarrow> T) at_top"
  shows "set_integrable lborel {0<..} f \<and> set_lebesgue_integral lborel {0<..} f = T - F 0"
proof -
  have mono: "F 0 \<le> F x" if x: "0 \<le> x" for x
    by (rule DERIV_nonneg_imp_nondecreasing[OF x]) (use D nn in blast)
  have ev: "eventually (\<lambda>x. F 0 \<le> F x) at_top"
    using eventually_ge_at_top[of "0::real"] by eventually_elim (rule mono)
  have T0: "F 0 \<le> T" by (rule tendsto_lowerbound[OF T ev]) simp
  define g where "g = (\<lambda>x. indicator {0..} x * f x :: real)"
  have nnI: "(\<integral>\<^sup>+x\<in>{0..}. ennreal (f x) \<partial>lborel) = ennreal (T - F 0)"
    by (rule nn_integral_FTC_atLeast[OF f D nn T])
  have e: "(\<integral>\<^sup>+x. ennreal (g x) \<partial>lborel) = ennreal (T - F 0)"
    unfolding nnI[symmetric] g_def by (intro nn_integral_cong) (simp split: split_indicator)
  have gm: "g \<in> borel_measurable lborel" unfolding g_def using f by measurable
  have hb: "has_bochner_integral lborel g (T - F 0)"
    by (rule has_bochner_integral_nn_integral[OF gm _ _ e]) (auto intro!: AE_I2 simp: g_def nn T0
      split: split_indicator)
  have gs: "(\<lambda>x. indicator {0..} x *\<^sub>R f x) = g" by (simp add: g_def fun_eq_iff)
  have i0: "set_integrable lborel {0..} f"
    unfolding set_integrable_def gs by (rule integrable.intros[OF hb])
  have v0: "set_lebesgue_integral lborel {0..} f = T - F 0"
    unfolding set_lebesgue_integral_def gs by (rule has_bochner_integral_integral_eq[OF hb])
  have i1: "set_integrable lborel {0<..} f" by (rule set_integrable_subset[OF i0]) auto
  have v1: "set_lebesgue_integral lborel {0<..} f = set_lebesgue_integral lborel {0..} f"
  proof (rule set_integral_cong_set)
    show "set_borel_measurable lborel {0..} f" "set_borel_measurable lborel {0<..} f"
      using i0 i1 unfolding set_integrable_def set_borel_measurable_def
        by (auto dest: borel_measurable_integrable)
    show "AE x in lborel. ((x::real) \<in> {0..}) = (x \<in> {0<..})"
      using AE_lborel_singleton[of 0] by eventually_elim (auto simp: le_less)
  qed
  show ?thesis using i1 v1 v0 by simp
qed

lemma gam_deriv:
  fixes c :: real
  shows "((\<lambda>y. exp (- (c * y)) * (\<Sum> k \<le>
    n. (c * y) ^ k / fact k)) has_real_derivative
          - c * exp (- (c * y)) * ((c * y) ^ n / fact n)) (at y)"
proof (induction n)
  case 0
  show ?case by (auto intro!: derivative_eq_intros)
next
  case (Suc n)
  have e': "((\<lambda>y. exp (- (c * y))) has_real_derivative - c * exp (- (c * y))) (at y)"
    by (auto intro!: derivative_eq_intros)
  have p0: "((\<lambda>y. y ^ Suc n) has_real_derivative of_nat (Suc n) * y ^ n) (at y)"
    using DERIV_pow[of "Suc n" y] by simp
  have p: "((\<lambda>y. (c * y) ^ Suc n / fact (Suc n)) has_real_derivative c * ((c * y) ^ n /
    fact n)) (at y)"
  proof -
    have h1: "((\<lambda>y. (c ^ Suc n / fact (Suc n)) * y ^ Suc n) has_real_derivative (c ^ Suc n /
      fact (Suc n)) * (of_nat (Suc n) * y ^ n)) (at y)"
      by (rule DERIV_cmult[OF p0])
    have h2: "(\<lambda>y. (c ^ Suc n / fact (Suc n)) * y ^ Suc n) =
      (\<lambda>y. (c * y) ^ Suc n / fact (Suc n))"
      by (simp add: fun_eq_iff power_mult_distrib)
    have f: "fact (Suc n) = (of_nat (Suc n) * fact n :: real)" by (rule fact_Suc)
    have h3: "(c ^ Suc n / fact (Suc n)) * (of_nat (Suc n) * y ^ n) = c * ((c * y) ^ n / fact n)"
      unfolding f by (simp add: power_mult_distrib field_simps del: of_nat_Suc)
    show ?thesis using h1 unfolding h2 h3 .
  qed
  have d: "((\<lambda>y. exp (- (c * y)) * ((c * y) ^ Suc n / fact (Suc n))) has_real_derivative
     (- c * exp (- (c * y)) * ((c * y) ^ Suc n / fact (Suc n)) + c * exp (- (c * y)) * ((c *
       y) ^ n / fact n))) (at y)"
    by (rule DERIV_cong[OF DERIV_mult[OF e' p]]) (simp add: algebra_simps)
  show ?case unfolding sum.atMost_Suc distrib_left
    by (rule DERIV_cong[OF DERIV_add[OF Suc.IH d]]) (simp add: algebra_simps)
qed

lemma gam_lim:
  fixes c :: real
  assumes c: "0 < c"
  shows "((\<lambda>y. exp (- (c * y)) * (\<Sum> k \<le>
    n. (c * y) ^ k / fact k)) \<longlongrightarrow> 0) at_top"
proof -
  have cy: "filterlim (\<lambda>y. c * y) at_top at_top"
    by (rule filterlim_tendsto_pos_mult_at_top[OF tendsto_const c filterlim_ident])
  have "((\<lambda>y. \<Sum> k \<le> n. (c * y) ^ k / exp (c * y) /
    fact k) \<longlongrightarrow> 0) at_top"
  proof (rule tendsto_null_sum)
    fix k :: nat assume "k \<in> {..n}"
    have "((\<lambda>y. (c * y) ^ k / exp (c * y)) \<longlongrightarrow> 0) at_top"
      using filterlim_compose[OF tendsto_power_div_exp_0 cy] by (simp add: o_def)
    thus "((\<lambda>y. (c * y) ^ k / exp (c * y) / fact k) \<longlongrightarrow> 0) at_top"
      by (rule tendsto_divide_zero)
  qed
  moreover have "(\<lambda>y. \<Sum> k \<le> n. (c * y) ^ k / exp (c * y) / fact k) =
    (\<lambda>y. exp (- (c * y)) * (\<Sum> k \<le> n. (c * y) ^ k / fact k))"
    by (simp add: fun_eq_iff sum_distrib_left exp_minus field_simps)
  ultimately show ?thesis by simp
qed

lemma exp_neg_lim: "0 < (c :: real) \<Longrightarrow>
  ((\<lambda>y. exp (- (c * y))) \<longlongrightarrow> 0) at_top"
  using gam_lim[of c 0] by simp

lemma gam_both:
  fixes c :: real
  assumes c: "0 < c"
  shows "set_integrable lborel {0<..} (\<lambda>y. y ^ n * exp (- (c * y))) \<and>
         set_lebesgue_integral lborel {0<..} (\<lambda>y. y ^ n * exp (- (c * y))) =
           fact n / c ^ (n + 1)"
proof -
  define F where "F = (\<lambda>y. - (fact n / c ^ (n + 1)) * (exp (- (c * y)) * (\<Sum> k \<le>
    n. (c * y) ^ k / fact k)))"
  have D: "(F has_real_derivative y ^ n * exp (- (c * y))) (at y)" for y
  proof -
    have "(F has_real_derivative - (fact n / c ^ (n + 1)) * (- c * exp (- (c * y)) * ((c * y) ^ n /
      fact n))) (at y)"
      unfolding F_def by (intro DERIV_cmult gam_deriv)
    moreover have "- (fact n / c ^ (n + 1)) * (- c * exp (- (c * y)) * ((c * y) ^ n / fact n)) =
      y ^ n * exp (- (c * y))"
      using c by (simp add: power_mult_distrib field_simps)
    ultimately show ?thesis by simp
  qed
  have F0: "F 0 = - (fact n / c ^ (n + 1))"
    by (simp add: F_def atMost_atLeast0 sum.atLeast_Suc_atMost[of 0 n] power_0_left)
  have T: "(F \<longlongrightarrow> 0) at_top" unfolding F_def
    by (rule tendsto_mult_right_zero[OF gam_lim[OF c]])
  have m: "(\<lambda>y. y ^ n * exp (- (c * y))) \<in> borel_measurable borel" by measurable
  have "set_integrable lborel {0<..} (\<lambda>y. y ^ n * exp (- (c * y))) \<and>
        set_lebesgue_integral lborel {0<..} (\<lambda>y. y ^ n * exp (- (c * y))) = 0 - F 0"
    by (rule ftc_Ioi_nonneg[OF m D _ T]) simp
  thus ?thesis unfolding F0 by simp
qed

lemma gam_integrable: "0 < (c::real) \<Longrightarrow>
  set_integrable lborel {0<..} (\<lambda>y. y ^ n * exp (- (c * y)))"
  by (rule gam_both[THEN conjunct1])

lemma gam: "0 < (c::real) \<Longrightarrow>
  set_lebesgue_integral lborel {0<..} (\<lambda>y. y ^ n * exp (- (c * y))) = fact n / c ^ (n + 1)"
  by (rule gam_both[THEN conjunct2])

text \<open>Interchange of @{text \<integral>} and @{text \<Sum>}
  for nonnegative integrable terms with summable integrals.\<close>
lemma set_integral_sum_fin:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes "\<And>i. i \<in> I \<Longrightarrow> set_integrable lborel A (f i)"
  shows "set_integrable lborel A (\<lambda>x. \<Sum> i \<in> I. f i x) \<and>
         set_lebesgue_integral lborel A (\<lambda>x. \<Sum> i \<in> I. f i x) = (\<Sum> i \<in>
           I. set_lebesgue_integral lborel A (f i))"
proof -
  have i: "\<And>i. i \<in> I \<Longrightarrow>
    integrable lborel (\<lambda>x. indicator A x *\<^sub>R f i x)" using assms
    unfolding set_integrable_def .
  have e: "(\<lambda>x. indicator A x *\<^sub>R (\<Sum> i \<in> I. f i x)) =
    (\<lambda>x. \<Sum> i \<in> I. indicator A x *\<^sub>R f i x)"
    by (simp add: sum_distrib_left)
  show ?thesis unfolding set_integrable_def set_lebesgue_integral_def e
    using Bochner_Integration.integrable_sum[OF i] Bochner_Integration.integral_sum[OF i]
      by (rule conjI)
qed

lemma set_integrable_cong_Ioi:
  "set_integrable lborel {0<..} f \<Longrightarrow> (\<And>x. 0 < x \<Longrightarrow>
    f x = g x) \<Longrightarrow> set_integrable lborel {0<..} (g :: real \<Rightarrow> real)"
  using set_integrable_cong[of lborel lborel "{0<..}" "{0<..}" f g] by simp

lemma set_integral_cong_Ioi:
  "(\<And>x. 0 < x \<Longrightarrow> f x = g x) \<Longrightarrow>
    set_lebesgue_integral lborel {0<..} f =
    set_lebesgue_integral lborel {0<..} (g :: real \<Rightarrow> real)"
  by (rule set_lebesgue_integral_cong) auto

lemma integral_suminf_nn:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes "\<And>n. set_integrable lborel {0<..} (f n)" "\<And>n y. 0 < y \<Longrightarrow>
    0 \<le> f n y"
    and "\<And>y. 0 < y \<Longrightarrow>
      summable (\<lambda>n. f n y)" "summable (\<lambda>n. set_lebesgue_integral lborel {0<..} (f
      n))"
  shows "set_integrable lborel {0<..} (\<lambda>y. \<Sum> n. f n y) \<and>
         set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> n. f n y) =
           (\<Sum> n. set_lebesgue_integral lborel {0<..} (f n))"
proof -
  define g where "g = (\<lambda>n x. indicator {0<..} x *\<^sub>R f n x)"
  have gi: "integrable lborel (g n)" for n using assms(1)[of n] unfolding set_integrable_def g_def .
  have gnn: "0 \<le> g n x" for n x using assms(2)[of x n] by (simp add: g_def indicator_def)
  have gnn': "norm (g n x) = g n x" for n x using gnn[of n x] by simp
  have gs: "summable (\<lambda>n. g n x)" for x
    using assms(3)[of x] by (cases "0 < x") (simp_all add: g_def indicator_def)
  have AE: "AE x in lborel. summable (\<lambda>n. norm (g n x))" unfolding gnn' using gs by simp
  have S: "summable (\<lambda>n. LINT x|lborel. norm (g n x))"
  proof -
    have "(\<lambda>n. LINT x|lborel. norm (g n x)) =
      (\<lambda>n. set_lebesgue_integral lborel {0<..} (f n))"
      unfolding gnn' by (simp add: set_lebesgue_integral_def g_def)
    thus ?thesis using assms(4) by simp
  qed
  have i: "integrable lborel (\<lambda>x. \<Sum> n. g n x)" by (rule integrable_suminf[OF gi AE S])
  have v: "lebesgue_integral lborel (\<lambda>x. \<Sum> n. g n x) =
    (\<Sum> n. lebesgue_integral lborel (g n))" by (rule integral_suminf[OF gi AE S])
  have sumg: "(\<lambda>x. indicator {0<..} x *\<^sub>R (\<Sum> n. f n x)) =
    (\<lambda>x. \<Sum> n. g n x)"
  proof (rule ext)
    fix x :: real
    show "indicator {0<..} x *\<^sub>R (\<Sum> n. f n x) = (\<Sum> n. g n x)"
    proof (cases "0 < x")
      case True thus ?thesis by (simp add: g_def)
    next
      case False thus ?thesis by (simp add: g_def)
    qed
  qed
  show ?thesis using i v unfolding set_integrable_def set_lebesgue_integral_def sumg g_def
    by (rule conjI)
qed

text \<open>Converse interchange: if the pointwise sum is integrable,
  the integrals sum to its integral.\<close>
lemma suminf_integral_nn:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes "\<And>n. set_integrable lborel {0<..} (f n)" "\<And>n y. 0 < y \<Longrightarrow>
    0 \<le> f n y"
    and "\<And>y. 0 < y \<Longrightarrow>
      summable (\<lambda>n. f n y)" "set_integrable lborel {0<..} (\<lambda>y. \<Sum> n. f n y)"
  shows "(\<lambda>n. set_lebesgue_integral lborel {0<..} (f n)) sums set_lebesgue_integral lborel
    {0<..} (\<lambda>y. \<Sum> n. f n y)"
proof -
  have nn_int: "0 \<le> set_lebesgue_integral lborel {0<..} (f n)" for n
    using set_integral_mono[of lborel "{0<..}" "\<lambda>x. 0" "f n"] assms(1,2)
      by (simp add: set_integrable_def)
  have bd: "(\<Sum> n < N. set_lebesgue_integral lborel {0<..} (f n)) \<le>
    set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> n. f n y)" for N
  proof -
    have fs: "set_integrable lborel {0<..} (\<lambda>x. \<Sum> n < N. f n x) \<and>
        set_lebesgue_integral lborel {0<..} (\<lambda>x. \<Sum> n < N. f n x) = (\<Sum> n <
          N. set_lebesgue_integral lborel {0<..} (f n))"
      by (rule set_integral_sum_fin) (rule assms(1))
    have "set_lebesgue_integral lborel {0<..} (\<lambda>x. \<Sum> n < N. f n x) \<le>
      set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> n. f n y)"
    proof (rule set_integral_mono[OF conjunct1[OF fs] assms(4)])
      fix x :: real assume "x \<in> {0<..}"
      thus "(\<Sum> n < N. f n x) \<le> (\<Sum> n. f n x)" using assms(2,3)
        by (intro sum_le_suminf) auto
    qed
    thus ?thesis using fs by simp
  qed
  have sm: "summable (\<lambda>n. set_lebesgue_integral lborel {0<..} (f n))"
    by (rule summableI_nonneg_bounded[OF nn_int bd])
  have "(\<Sum> n. set_lebesgue_integral lborel {0<..} (f n)) =
    set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> n. f n y)"
    using integral_suminf_nn[OF assms(1-3) sm] by simp
  thus ?thesis using summable_sums[OF sm] by simp
qed


text \<open>Mittag-Leffler for @{text coth} (from
  @{text "Cotangent_PFD_Formula.cot_pfd_formula_real"}).\<close>
lemma coth_series:
  "0 < v \<Longrightarrow> (\<lambda>n. 2 * v / (v ^ 2 + (real n + 1) ^ 2)) sums (pi * cosh (pi *
    v) / sinh (pi * v) - 1 / v)"
proof -
  assume v: "0 < v"
  define z where "z = \<i> * complex_of_real v"
  define x where "x = pi * v"
  have zI: "z \<notin> \<int>"
  proof
    assume "z \<in> \<int>"
    then obtain m where "z = of_int m" by (elim Ints_cases)
    hence "Im z = 0" by simp
    thus False using v by (simp add: z_def)
  qed
  have sh0: "sinh x \<noteq> 0" using v by (simp add: x_def)
  have cosr: "cos (\<i> * complex_of_real x) = complex_of_real (cosh x)"
    using cosh_real[of x] by (simp add: cosh_def exp_minus)
  have sinr: "sin (\<i> * complex_of_real x) = \<i> * complex_of_real (sinh x)"
  proof -
    have "complex_of_real (sinh x) = - \<i> * sin (\<i> * complex_of_real x)"
      using sinh_real[of x] by (simp add: sinh_def exp_minus)
    hence "\<i> * complex_of_real (sinh x) = sin (\<i> * complex_of_real x)" by simp
    thus ?thesis by simp
  qed
  have piz: "complex_of_real pi * z = \<i> * complex_of_real x" by (simp add: z_def x_def)
  have "complex_of_real pi * cot (complex_of_real pi * z) = 1 / z + cot_pfd z"
    by (rule cot_pfd_formula_complex[OF zI])
  hence "cot_pfd z = complex_of_real pi * (complex_of_real (cosh x) / (\<i> *
    complex_of_real (sinh x))) - 1 / z"
    unfolding piz cot_def cosr sinr by (simp add: algebra_simps)
  hence c: "\<i> * cot_pfd z = complex_of_real (pi * cosh x / sinh x - 1 / v)"
    using v sh0 by (simp add: z_def field_simps)
  have t: "\<i> * (2 * z / (z\<^sup>2 - (complex_of_nat (Suc n))\<^sup>2)) =
    complex_of_real (2 * v / (v ^ 2 + (real n + 1) ^ 2))" for n
  proof -
    have d: "z\<^sup>2 - (complex_of_nat (Suc n))\<^sup>2 =
      - complex_of_real (v ^ 2 + (real n + 1) ^ 2)"
      by (simp add: z_def power2_eq_square algebra_simps)
    have d0: "complex_of_real (v ^ 2 + (real n + 1) ^ 2) \<noteq> 0"
      by (metis add_pos_nonneg of_real_eq_0_iff less_irrefl zero_less_power v zero_le_power2)
    have g: "\<i> * (2 * (\<i> * c) / - D) = 2 * c / D" if "D \<noteq> 0" for c D :: complex
      using that by (simp add: field_simps)
    show ?thesis unfolding d unfolding z_def g[OF d0]
      by (simp only: of_real_divide of_real_mult of_real_numeral)
  qed
  have "(\<lambda>n. \<i> * (2 * z / (z\<^sup>2 - (complex_of_nat (Suc n))\<^sup>2))) sums (\<i> *
    cot_pfd z)"
    by (rule sums_mult[OF sums_cot_pfd_complex])
  hence "(\<lambda>n. complex_of_real (2 * v / (v ^ 2 + (real n +
    1) ^ 2))) sums complex_of_real (pi * cosh x / sinh x - 1 / v)"
    unfolding t c .
  thus ?thesis unfolding sums_of_real_iff x_def .
qed

subsection \<open>The @{text S}-series and the Laplace transform of @{text sin}\<close>

lemma S_series:
  "0 < u \<Longrightarrow> (\<lambda>l. u / (u ^ 2 + (2 * pi * (real l + 1)) ^ 2)) sums (1 / 4 + 1 /
    (2 * (exp u - 1)) - 1 / (2 * u))"
proof -
  assume u: "0 < u"
  define v where "v = u / (2 * pi)"
  have v: "0 < v" using u by (simp add: v_def)
  have cs: "(\<lambda>n. 1 / (4 * pi) * (2 * v / (v ^ 2 + (real n + 1) ^ 2))) sums (1 / (4 * pi) *
    (pi * cosh (pi * v) / sinh (pi * v) - 1 / v))"
    by (rule sums_mult[OF coth_series[OF v]])
  have t: "1 / (4 * pi) * (2 * v / (v ^ 2 + (real n + 1) ^ 2)) =
    u / (u ^ 2 + (2 * pi * (real n + 1)) ^ 2)" for n
  proof -
    have d2: "0 < u ^ 2 + (2 * pi * (real n + 1)) ^ 2" using u by (simp add: add_pos_pos)
    have "1 / (4 * pi) * (2 * v / (v ^ 2 + (real n + 1) ^ 2)) =
      v / (2 * pi * (v ^ 2 + (real n + 1) ^ 2))"
      by (simp add: field_simps)
    also have "2 * pi * (v ^ 2 + (real n + 1) ^ 2) =
      (u ^ 2 + (2 * pi * (real n + 1)) ^ 2) / (2 * pi)"
      by (simp add: v_def field_simps power2_eq_square)
    also have "v / ((u ^ 2 + (2 * pi * (real n + 1)) ^ 2) / (2 * pi)) =
      u / (u ^ 2 + (2 * pi * (real n + 1)) ^ 2)"
      using d2 by (simp add: v_def field_simps)
    finally show ?thesis .
  qed
  define w where "w = exp (u / 2)"
  have w1: "1 < w" using u by (simp add: w_def)
  have ww: "exp u = w ^ 2" unfolding w_def using exp_double[of "u / 2"] by simp
  have pv: "pi * v = u / 2" by (simp add: v_def)
  have ch: "cosh (u / 2) / sinh (u / 2) = (w ^ 2 + 1) / (w ^ 2 - 1)"
  proof -
    have w0: "w \<noteq> 0" using w1 by simp
    have c1: "cosh (u / 2) = (w + inverse w) / 2" by (simp add: cosh_def exp_minus w_def)
    have s1: "sinh (u / 2) = (w - inverse w) / 2" by (simp add: sinh_def exp_minus w_def)
    have "cosh (u / 2) / sinh (u / 2) = (w + inverse w) / (w - inverse w)"
      unfolding c1 s1 divide_divide_times_eq mult.commute[of _ 2]
      by (rule nonzero_mult_divide_mult_cancel_left) simp
    also have "\<dots> = (w * (w + inverse w)) / (w * (w - inverse w))" using w0 by simp
    also have "w * (w + inverse w) = w * w + 1" using w0 by (simp add: distrib_left)
    also have "w * (w - inverse w) = w * w - 1" using w0 by (simp add: right_diff_distrib)
    finally show ?thesis by (simp add: power2_eq_square)
  qed
  have val: "1 / (4 * pi) * (pi * cosh (pi * v) / sinh (pi * v) - 1 / v) =
    1 / 4 + 1 / (2 * (exp u - 1)) - 1 / (2 * u)"
  proof -
    have w2: "w ^ 2 - 1 \<noteq> 0" using one_less_power[OF w1, of 2] by simp
    have ch': "pi * cosh (u / 2) / sinh (u / 2) = pi * ((w ^ 2 + 1) / (w ^ 2 - 1))"
      using ch by (metis times_divide_eq_right)
    show ?thesis unfolding pv ww ch' using u w2 by (simp add: v_def field_simps)
  qed
  show ?thesis using cs unfolding t val .
qed

lemma exp_integrable: "0 < (a::real) \<Longrightarrow>
  set_integrable lborel {0<..} (\<lambda>u. exp (- (a * u)))"
  using gam_integrable[of a 0] by simp

lemma laplace_sin_integrable: "0 < (a::real) \<Longrightarrow>
  set_integrable lborel {0<..} (\<lambda>u. exp (- (a * u)) * sin (y * u))"
proof -
  assume a: "0 < a"
  show ?thesis
  proof (rule set_integrable_bound[OF exp_integrable[OF a]])
    show "set_borel_measurable lborel {0<..} (\<lambda>u. exp (- (a * u)) * sin (y * u))"
      by (rule set_bm_cont) (intro continuous_intros)
    show "AE x\<in>{0<..} in lborel. norm (exp (- (a * x)) * sin (y * x)) \<le>
      norm (exp (- (a * x)))"
      by (intro AE_I2 impI) (auto simp: abs_mult intro!: mult_left_le abs_sin_le_one)
  qed
qed

text \<open>@{text "\<integral>_0^\<infinity> e^{-au} sin(yu) du = y / (y^2 + a^2)"}.\<close>
lemma laplace_sin: "0 < (a::real) \<Longrightarrow>
  set_lebesgue_integral lborel {0<..} (\<lambda>u. exp (- (a * u)) * sin (y * u)) =
  y / (y ^ 2 + a ^ 2)"
proof -
  assume a: "0 < a"
  have D: "a ^ 2 + y ^ 2 \<noteq> 0" using a by (simp add: add_pos_nonneg)
  have Dp: "0 < a ^ 2 + y ^ 2" using a by (simp add: add_pos_nonneg)
  define G where "G = (\<lambda>u. (- exp (- (a * u)) * (a * sin (y * u) + y * cos (y * u))) *
    inverse (a ^ 2 + y ^ 2) - exp (- (a * u)) * inverse a)"
  have dG: "(G has_real_derivative exp (- (a * u)) * (sin (y * u) + 1)) (at u)" for u
    unfolding G_def
    by (rule DERIV_cong, (rule derivative_eq_intros refl)+) (use a D in \<open>simp add: field_simps
      power2_eq_square\<close>)
  define K where "K = (a + \<bar>y\<bar>) * inverse (a ^ 2 + y ^ 2) + inverse a"
  have bnd: "norm (G u) \<le> exp (- (a * u)) * K" for u
  proof -
    have X: "\<bar>a * sin (y * u) + y * cos (y * u)\<bar> \<le> a + \<bar>y\<bar>"
    proof -
      have "\<bar>a * sin (y * u) + y * cos (y * u)\<bar> \<le>
        \<bar>a\<bar> * \<bar>sin (y * u)\<bar> + \<bar>y\<bar> * \<bar>cos (y * u)\<bar>"
        using abs_triangle_ineq[of "a * sin (y * u)" "y * cos (y * u)"] by (simp add: abs_mult)
      also have "\<dots> \<le> a + \<bar>y\<bar>"
        using a by (intro add_mono) (auto intro!: mult_left_le)
      finally show ?thesis .
    qed
    have "norm (G u) \<le> exp (- (a * u)) * \<bar>a * sin (y * u) + y * cos (y * u)\<bar> *
      inverse (a ^ 2 + y ^ 2) + exp (- (a * u)) * inverse a"
    proof -
      have "norm (G u) \<le> \<bar>(- exp (- (a * u)) * (a * sin (y * u) + y * cos (y * u))) *
        inverse (a ^ 2 + y ^ 2)\<bar> + \<bar>exp (- (a * u)) * inverse a\<bar>"
        unfolding G_def real_norm_def by (rule abs_triangle_ineq4)
      also have "\<bar>(- exp (- (a * u)) * (a * sin (y * u) + y * cos (y * u))) * inverse (a ^ 2 +
        y ^ 2)\<bar> =
          exp (- (a * u)) * \<bar>a * sin (y * u) + y * cos (y * u)\<bar> * inverse (a ^ 2 + y ^ 2)"
        using Dp by (simp add: abs_mult)
      also have "\<bar>exp (- (a * u)) * inverse a\<bar> = exp (- (a * u)) * inverse a" using a
        by (simp add: abs_mult)
      finally show ?thesis .
    qed
    also have "\<dots> \<le> exp (- (a * u)) * (a + \<bar>y\<bar>) * inverse (a ^ 2 + y ^ 2) +
      exp (- (a * u)) * inverse a"
      using X Dp by (intro add_mono mult_right_mono mult_left_mono) auto
    also have "\<dots> = exp (- (a * u)) * K" by (simp add: K_def algebra_simps)
    finally show ?thesis .
  qed
  have T: "(G \<longlongrightarrow> 0) at_top"
    by (rule Lim_null_comparison[OF always_eventually[OF allI[OF bnd]] tendsto_mult_left_zero[OF
      exp_neg_lim[OF a]]])
  have m: "(\<lambda>u. exp (- (a * u)) * (sin (y * u) + 1)) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have nn: "0 \<le> exp (- (a * u)) * (sin (y * u) + 1)" for u
  proof -
    have "0 \<le> sin (y * u) + 1" using sin_ge_minus_one[of "y * u"] by linarith
    thus ?thesis by simp
  qed
  have I1: "set_integrable lborel {0<..} (\<lambda>u. exp (- (a * u)) * (sin (y * u) + 1)) \<and>
      set_lebesgue_integral lborel {0<..} (\<lambda>u. exp (- (a * u)) * (sin (y * u) + 1)) =
        0 - G 0"
    by (rule ftc_Ioi_nonneg[OF m dG nn T])
  have G0: "G 0 = - y * inverse (a ^ 2 + y ^ 2) - inverse a" by (simp add: G_def)
  have I2: "set_lebesgue_integral lborel {0<..} (\<lambda>u. exp (- (a * u))) = inverse a"
    using gam[OF a, of 0] by (simp add: inverse_eq_divide)
  have f: "(\<lambda>u. exp (- (a * u)) * sin (y * u)) =
    (\<lambda>u. exp (- (a * u)) * (sin (y * u) + 1) - exp (- (a * u)))"
    by (simp add: fun_eq_iff algebra_simps)
  have "set_lebesgue_integral lborel {0<..} (\<lambda>u. exp (- (a * u)) * sin (y * u)) =
    (0 - G 0) - inverse a"
    unfolding f set_integral_diff(2)[OF conjunct1[OF I1] exp_integrable[OF a]] I2 conjunct2[OF I1]
      ..
  also have "\<dots> = y / (y ^ 2 + a ^ 2)" unfolding G0 by (simp add: field_simps add.commute)
  finally show ?thesis .
qed

text \<open>@{text "\<Psi>(a, c) = \<integral>_0^\<infinity> e^{-cy} y/(y^2 + a^2) dy"}.\<close>
definition Psi :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Psi a c = set_lebesgue_integral lborel {0<..} (\<lambda>y. exp (- (c * y)) * (y / (y ^ 2 +
    a ^ 2)))"

lemma psi_integrable: "0 < (a::real) \<Longrightarrow> 0 < c \<Longrightarrow>
  set_integrable lborel {0<..} (\<lambda>y. exp (- (c * y)) * (y / (y ^ 2 + a ^ 2)))"
proof -
  assume a: "0 < a" and c: "0 < c"
  have Dp: "0 < y ^ 2 + a ^ 2" for y using a by (simp add: add_nonneg_pos)
  have b: "y / (y ^ 2 + a ^ 2) \<le> 1 / (2 * a)" if y: "0 < y" for y
  proof -
    have "0 \<le> (y - a) ^ 2" by simp
    hence "2 * a * y \<le> y ^ 2 + a ^ 2" by (simp add: power2_diff algebra_simps)
    thus ?thesis using a Dp[of y] by (simp add: field_simps)
  qed
  show ?thesis
  proof (rule set_integrable_bound)
    show "set_integrable lborel {0<..} (\<lambda>y. exp (- (c * y)) * (1 / (2 * a)))"
      by (rule set_integrable_mult_left[OF exp_integrable[OF c]])
    show "set_borel_measurable lborel {0<..} (\<lambda>y. exp (- (c * y)) * (y / (y ^ 2 + a ^ 2)))"
      by (rule set_bm_cont) (intro continuous_intros, metis Dp less_irrefl)
    show "AE x\<in>{0<..} in lborel. norm (exp (- (c * x)) * (x / (x ^ 2 + a ^ 2))) \<le>
      norm (exp (- (c * x)) * (1 / (2 * a)))"
    proof (rule AE_I2, rule impI)
      fix x :: real assume "x \<in> {0<..}"
      hence x: "0 < x" by simp
      have le: "exp (- (c * x)) * (x / (x ^ 2 + a ^ 2)) \<le> exp (- (c * x)) * (1 / (2 * a))"
        by (rule mult_left_mono[OF b[OF x]]) simp
      have n1: "norm (exp (- (c * x)) * (x / (x ^ 2 + a ^ 2))) =
        exp (- (c * x)) * (x / (x ^ 2 + a ^ 2))"
        using x Dp[of x] by (simp add: abs_mult)
      have n2: "norm (exp (- (c * x)) * (1 / (2 * a))) = exp (- (c * x)) * (1 / (2 * a))"
        using a by (simp add: abs_mult)
      show "norm (exp (- (c * x)) * (x / (x ^ 2 + a ^ 2))) \<le>
        norm (exp (- (c * x)) * (1 / (2 * a)))"
        unfolding n1 n2 by (rule le)
    qed
  qed
qed

text \<open>The symmetry @{text "\<Psi>(a, c) = \<Psi>(c, a)"},
  by Fubini on @{text "e^{-cy} e^{-au} sin(yu)"}.\<close>
lemma psi_symm: "0 < a \<Longrightarrow> 0 < c \<Longrightarrow> Psi a c = Psi c a"
proof -
  assume a: "0 < a" and c: "0 < c"
  define K where "K = (\<lambda>y u :: real.
    if 0 < y \<and> 0 < u then exp (- (c * y)) * (exp (- (a * u)) * sin (y * u)) else 0)"
  have Km: "(\<lambda>(y, u). K y u) \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding K_def by measurable
  have Kslice: "(\<lambda>u. K y u) = (\<lambda>u. indicator {0<..} u *\<^sub>R (exp (- (c * y)) *
    (exp (- (a * u)) * sin (y * u))))" if y: "0 < y" for y
    using y by (auto simp: K_def fun_eq_iff indicator_def)
  have Kslice2: "(\<lambda>y. K y u) = (\<lambda>y. indicator {0<..} y *\<^sub>R (exp (- (a * u)) *
    (exp (- (c * y)) * sin (u * y))))" if u: "0 < u" for u
    using u by (auto simp: K_def fun_eq_iff indicator_def mult_ac)
  have Kz: "(\<lambda>u. K y u) = (\<lambda>u. 0)" if "\<not> 0 < y" for y using that
    by (auto simp: K_def fun_eq_iff)
  have Kz2: "(\<lambda>y. K y u) = (\<lambda>y. 0)" if "\<not> 0 < u" for u using that
    by (auto simp: K_def fun_eq_iff)
  have Ki: "integrable lborel (\<lambda>u. K y u)" for y
  proof (cases "0 < y")
    case True
    have "set_integrable lborel {0<..} (\<lambda>u. exp (- (c * y)) * (exp (- (a * u)) * sin (y *
      u)))"
      by (intro set_integrable_mult_right laplace_sin_integrable[OF a])
    thus ?thesis unfolding Kslice[OF True] set_integrable_def .
  qed (simp add: Kz)
  have Kn: "(\<integral>u. norm (K y u) \<partial>lborel) \<le> exp (- (c * y)) * (1 / a)"
    if y: "0 < y" for y
  proof -
    have "(\<integral>u. norm (K y u) \<partial>lborel) \<le>
      (\<integral>u. indicator {0<..} u *\<^sub>R (exp (- (c * y)) * exp (- (a *
      u))) \<partial>lborel)"
    proof (rule integral_mono)
      show "integrable lborel (\<lambda>u. norm (K y u))" by (rule integrable_norm[OF Ki])
      show "integrable lborel (\<lambda>u. indicator {0<..} u *\<^sub>R (exp (- (c * y)) *
        exp (- (a * u))))"
        using set_integrable_mult_right[OF exp_integrable[OF a], of "exp (- (c * y))"]
          unfolding set_integrable_def .
      fix u :: real
      show "norm (K y u) \<le> indicator {0<..} u *\<^sub>R (exp (- (c * y)) * exp (- (a * u)))"
        using y by (auto simp: K_def abs_mult indicator_def intro!: mult_left_le)
    qed
    also have "\<dots> = set_lebesgue_integral lborel {0<..} (\<lambda>u. exp (- (c * y)) *
      exp (- (a * u)))"
      unfolding set_lebesgue_integral_def ..
    also have "\<dots> = exp (- (c * y)) *
      set_lebesgue_integral lborel {0<..} (\<lambda>u. exp (- (a * u)))"
      by (rule set_integral_mult_right)
    also have "set_lebesgue_integral lborel {0<..} (\<lambda>u. exp (- (a * u))) = 1 / a"
      using gam[OF a, of 0] by simp
    finally show ?thesis .
  qed
  have Kint: "integrable (lborel \<Otimes>\<^sub>M lborel) (\<lambda>(y, u). K y u)"
  proof (rule lborel_pair.Fubini_integrable[OF Km])
    show "AE y in lborel. integrable lborel (\<lambda>u. case (y, u) of (y,
      u) \<Rightarrow> K y u)" using Ki by simp
    show "integrable lborel (\<lambda>y. \<integral>u. norm (case (y, u) of (y,
      u) \<Rightarrow> K y u) \<partial>lborel)"
    proof (rule Bochner_Integration.integrable_bound)
      show "integrable lborel (\<lambda>y. indicator {0<..} y *\<^sub>R (exp (- (c * y)) * (1 /
        a)))"
        using set_integrable_mult_left[OF exp_integrable[OF c], of "1 / a"]
          unfolding set_integrable_def .
      show "(\<lambda>y. \<integral>u. norm (case (y, u) of (y,
        u) \<Rightarrow> K y u) \<partial>lborel) \<in> borel_measurable lborel"
        using Km by measurable
      show "AE y in lborel. norm (\<integral>u. norm (case (y, u) of (y,
        u) \<Rightarrow> K y u) \<partial>lborel) \<le>
        norm (indicator {0<..} y *\<^sub>R (exp (- (c * y)) * (1 / a)))"
      proof (rule AE_I2)
        fix y :: real
        show "norm (\<integral>u. norm (case (y, u) of (y,
          u) \<Rightarrow> K y u) \<partial>lborel) \<le>
          norm (indicator {0<..} y *\<^sub>R (exp (- (c * y)) * (1 / a)))"
        proof (cases "0 < y")
          case True
          have "0 \<le> (\<integral>u. norm (K y u) \<partial>lborel)"
            by (rule integral_nonneg_AE) simp
          thus ?thesis using Kn[OF True] True a by simp
        qed (simp add: Kz)
      qed
    qed
  qed
  have L: "Psi a c = (\<integral>y. (\<integral>u. K y u \<partial>lborel) \<partial>lborel)"
  proof -
    have "(\<lambda>y. indicator {0<..} y *\<^sub>R (exp (- (c * y)) * (y / (y ^ 2 + a ^ 2)))) =
      (\<lambda>y. \<integral>u. K y u \<partial>lborel)"
    proof (rule ext)
      fix y :: real
      show "indicator {0<..} y *\<^sub>R (exp (- (c * y)) * (y / (y ^ 2 + a ^ 2))) =
        (\<integral>u. K y u \<partial>lborel)"
      proof (cases "0 < y")
        case True
        have "(\<integral>u. K y u \<partial>lborel) =
          set_lebesgue_integral lborel {0<..} (\<lambda>u. exp (- (c * y)) * (exp (- (a * u)) *
          sin (y * u)))"
          unfolding Kslice[OF True] set_lebesgue_integral_def ..
        also have "\<dots> = exp (- (c * y)) * (y / (y ^ 2 + a ^ 2))"
          unfolding set_integral_mult_right laplace_sin[OF a] ..
        finally have "(\<integral>u. K y u \<partial>lborel) =
          exp (- (c * y)) * (y / (y ^ 2 + a ^ 2))" .
        thus ?thesis using True by simp
      next
        case False
        have "(\<integral>u. K y u \<partial>lborel) = 0" unfolding Kz[OF False]
          by (rule integral_zero)
        thus ?thesis using False by simp
      qed
    qed
    thus ?thesis unfolding Psi_def set_lebesgue_integral_def by simp
  qed
  have R: "Psi c a = (\<integral>u. (\<integral>y. K y u \<partial>lborel) \<partial>lborel)"
  proof -
    have "(\<lambda>u. indicator {0<..} u *\<^sub>R (exp (- (a * u)) * (u / (u ^ 2 + c ^ 2)))) =
      (\<lambda>u. \<integral>y. K y u \<partial>lborel)"
    proof (rule ext)
      fix u :: real
      show "indicator {0<..} u *\<^sub>R (exp (- (a * u)) * (u / (u ^ 2 + c ^ 2))) =
        (\<integral>y. K y u \<partial>lborel)"
      proof (cases "0 < u")
        case True
        have "(\<integral>y. K y u \<partial>lborel) =
          set_lebesgue_integral lborel {0<..} (\<lambda>y. exp (- (a * u)) * (exp (- (c * y)) *
          sin (u * y)))"
          unfolding Kslice2[OF True] set_lebesgue_integral_def ..
        also have "\<dots> = exp (- (a * u)) * (u / (u ^ 2 + c ^ 2))"
          unfolding set_integral_mult_right laplace_sin[OF c] ..
        finally have "(\<integral>y. K y u \<partial>lborel) =
          exp (- (a * u)) * (u / (u ^ 2 + c ^ 2))" .
        thus ?thesis using True by simp
      next
        case False
        have "(\<integral>y. K y u \<partial>lborel) = 0" unfolding Kz2[OF False]
          by (rule integral_zero)
        thus ?thesis using False by simp
      qed
    qed
    thus ?thesis unfolding Psi_def set_lebesgue_integral_def by simp
  qed
  show ?thesis unfolding L R using lborel_pair.Fubini_integral[OF Kint] by simp
qed

text \<open>@{text "\<Phi>(a, c) = \<integral>_0^\<infinity> y^5 e^{-cy}/(y^2 + a^2) dy"}.\<close>
definition Phi :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Phi a c = set_lebesgue_integral lborel {0<..} (\<lambda>y. y ^ 5 * exp (- (c * y)) / (y ^ 2 +
    a ^ 2))"

lemma phi_split:
  fixes a y :: real assumes a: "0 < a"
  shows "y ^ 5 * exp (- (c * y)) / (y ^ 2 + a ^ 2) =
         y ^ 3 * exp (- (c * y)) - a ^ 2 * (y ^ 1 * exp (- (c * y))) + a ^ 4 * (exp (- (c * y)) *
           (y / (y ^ 2 + a ^ 2)))"
proof -
  have D: "y ^ 2 + a ^ 2 \<noteq> 0" using a by (simp add: add_nonneg_pos)
  have "y ^ 5 = (y ^ 3 - a ^ 2 * y) * (y ^ 2 + a ^ 2) + a ^ 4 * y"
    by (simp add: algebra_simps eval_nat_numeral)
  hence "y ^ 5 * exp (- (c * y)) / (y ^ 2 + a ^ 2) =
    ((y ^ 3 - a ^ 2 * y) * (y ^ 2 + a ^ 2) + a ^ 4 * y) * exp (- (c * y)) / (y ^ 2 + a ^ 2)"
    by simp
  also have "\<dots> = (y ^ 3 - a ^ 2 * y) * exp (- (c * y)) + a ^ 4 * (exp (- (c * y)) * (y /
    (y ^ 2 + a ^ 2)))"
    using D by (simp add: field_simps)
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma phi_integrable: "0 < (a::real) \<Longrightarrow> 0 < c \<Longrightarrow>
  set_integrable lborel {0<..} (\<lambda>y. y ^ 5 * exp (- (c * y)) / (y ^ 2 + a ^ 2))"
proof -
  assume a: "0 < a" and c: "0 < c"
  have E: "(\<lambda>y. y ^ 5 * exp (- (c * y)) / (y ^ 2 + a ^ 2)) =
           (\<lambda>y. y ^ 3 * exp (- (c * y)) - a ^ 2 * (y ^ 1 * exp (- (c * y))) + a ^ 4 *
             (exp (- (c * y)) * (y / (y ^ 2 + a ^ 2))))"
    by (rule ext) (rule phi_split[OF a])
  show ?thesis unfolding E
    by (intro set_integral_add(1) set_integral_diff(1) set_integrable_mult_right gam_integrable
      psi_integrable a c)
qed

lemma phi_eq: "0 < a \<Longrightarrow> 0 < c \<Longrightarrow>
  Phi a c = 6 / c ^ 4 - a ^ 2 / c ^ 2 + a ^ 4 * Psi a c"
proof -
  assume a: "0 < a" and c: "0 < c"
  have E: "(\<lambda>y. y ^ 5 * exp (- (c * y)) / (y ^ 2 + a ^ 2)) =
           (\<lambda>y. y ^ 3 * exp (- (c * y)) - a ^ 2 * (y ^ 1 * exp (- (c * y))) + a ^ 4 *
             (exp (- (c * y)) * (y / (y ^ 2 + a ^ 2))))"
    by (rule ext) (rule phi_split[OF a])
  have i3: "set_integrable lborel {0<..} (\<lambda>y. y ^ 3 * exp (- (c * y)))"
    by (rule gam_integrable[OF c])
  have i1: "set_integrable lborel {0<..} (\<lambda>y. a ^ 2 * (y ^ 1 * exp (- (c * y))))"
    by (intro set_integrable_mult_right gam_integrable[OF c])
  have ip: "set_integrable lborel {0<..} (\<lambda>y. a ^ 4 * (exp (- (c * y)) * (y / (y ^ 2 +
    a ^ 2))))"
    by (intro set_integrable_mult_right psi_integrable[OF a c])
  have "Phi a c = set_lebesgue_integral lborel {0<..} (\<lambda>y. y ^ 3 * exp (- (c * y)))
      - a ^ 2 * set_lebesgue_integral lborel {0<..} (\<lambda>y. y ^ 1 * exp (- (c * y))) + a ^ 4 *
        Psi a c"
    unfolding Phi_def E set_integral_add(2)[OF set_integral_diff(1)[OF i3 i1] ip]
      set_integral_diff(2)[OF i3 i1]
      set_integral_mult_right Psi_def ..
  also have "\<dots> = 6 / c ^ 4 - a ^ 2 / c ^ 2 + a ^ 4 * Psi a c"
    unfolding gam[OF c] by (simp add: fact_numeral power2_eq_square)
  finally show ?thesis .
qed

lemma phi_symm: "0 < a \<Longrightarrow> 0 < c \<Longrightarrow> c ^ 4 * Phi a c = a ^ 4 * Phi c a"
proof -
  assume a: "0 < a" and c: "0 < c"
  have "c ^ 4 * Phi a c = 6 - a ^ 2 * c ^ 2 + a ^ 4 * c ^ 4 * Psi a c"
    unfolding phi_eq[OF a c] using c by (simp add: field_simps eval_nat_numeral)
  also have "\<dots> = a ^ 4 * Phi c a"
    unfolding phi_eq[OF c a] psi_symm[OF a c] using a by (simp add: field_simps eval_nat_numeral)
  finally show ?thesis .
qed

subsection \<open>The pole integral\<close>

lemma geom_pt: "0 < u \<Longrightarrow> (\<lambda>n. u ^ 4 * exp (- ((a + (real n + 1)) *
  u))) sums (u ^ 4 * exp (- (a * u)) / (exp u - 1))"
proof -
  assume u: "0 < u"
  define x where "x = exp (- u)"
  have x0: "0 < x" "x < 1" using u by (simp_all add: x_def)
  have g: "(\<lambda>n. x ^ n) sums (1 / (1 - x))" by (rule geometric_sums) (use x0 in simp)
  have s: "(\<lambda>n. (u ^ 4 * exp (- (a * u)) * x) * x ^ n) sums ((u ^ 4 * exp (- (a * u)) * x) *
    (1 / (1 - x)))"
    by (rule sums_mult[OF g])
  have e1: "(\<lambda>n. (u ^ 4 * exp (- (a * u)) * x) * x ^ n) =
    (\<lambda>n. u ^ 4 * exp (- ((a + (real n + 1)) * u)))"
  proof (rule ext)
    fix n :: nat
    have "x ^ n = exp (real n * (- u))" unfolding x_def by (rule exp_of_nat_mult[symmetric])
    hence "(u ^ 4 * exp (- (a * u)) * x) * x ^ n =
      u ^ 4 * (exp (- (a * u)) * exp (- u) * exp (real n * (- u)))"
      by (simp add: x_def mult_ac)
    also have "exp (- (a * u)) * exp (- u) * exp (real n * (- u)) =
      exp (- ((a + (real n + 1)) * u))"
      by (simp add: exp_add[symmetric] algebra_simps)
    finally show "(u ^ 4 * exp (- (a * u)) * x) * x ^ n =
      u ^ 4 * exp (- ((a + (real n + 1)) * u))" .
  qed
  have e2: "(u ^ 4 * exp (- (a * u)) * x) * (1 / (1 - x)) = u ^ 4 * exp (- (a * u)) / (exp u - 1)"
  proof -
    have "x * (1 / (1 - x)) = 1 / (exp u - 1)"
      unfolding x_def exp_minus using u by (simp add: field_simps)
    moreover have "(u ^ 4 * exp (- (a * u)) * x) * (1 / (1 - x)) =
      u ^ 4 * exp (- (a * u)) * (x * (1 / (1 - x)))"
      by (simp only: mult.assoc)
    ultimately show ?thesis by simp
  qed
  show ?thesis using s unfolding e1 e2 .
qed

lemma u_integral:
  assumes "0 < a" "(\<lambda>n. 1 / (a + (real n + 1)) ^ 5) sums Z"
  shows "set_integrable lborel {0<..} (\<lambda>u. u ^ 4 * exp (- (a * u)) * (1 / 4 + 1 / (2 *
    (exp u - 1)) - 1 / (2 * u))) \<and>
         set_lebesgue_integral lborel {0<..} (\<lambda>u. u ^ 4 * exp (- (a * u)) * (1 / 4 + 1 /
           (2 * (exp u - 1)) - 1 / (2 * u)))
           = 6 / a ^ 5 - 3 / a ^ 4 + 12 * Z"
proof -
  note a = assms(1) and Z = assms(2)
  define f where "f = (\<lambda>n u. u ^ 4 * exp (- ((a + (real n + 1)) * u)))"
  have an: "0 < a + (real n + 1)" for n using a by simp
  have fi: "set_integrable lborel {0<..} (f n)" for n unfolding f_def
    by (rule gam_integrable[OF an])
  have fv: "set_lebesgue_integral lborel {0<..} (f n) = 24 * (1 / (a + (real n + 1)) ^ 5)" for n
    unfolding f_def gam[OF an] by (simp add: fact_numeral)
  have fnn: "0 \<le> f n u" if "0 < u" for n u using that by (simp add: f_def)
  have fs: "summable (\<lambda>n. f n u)" if "0 < u" for u
    using geom_pt[OF that, of a] unfolding f_def by (rule sums_summable)
  have fsum: "(\<lambda>n. set_lebesgue_integral lborel {0<..} (f n)) sums (24 * Z)"
    unfolding fv by (rule sums_mult[OF Z])
  have IG: "set_integrable lborel {0<..} (\<lambda>u. \<Sum> n. f n u) \<and>
      set_lebesgue_integral lborel {0<..} (\<lambda>u. \<Sum> n. f n u) =
        (\<Sum> n. set_lebesgue_integral lborel {0<..} (f n))"
    by (rule integral_suminf_nn[OF fi fnn fs sums_summable[OF fsum]])
  have G: "(\<Sum> n. f n u) = u ^ 4 * exp (- (a * u)) / (exp u - 1)" if "0 < u" for u
    using sums_unique[OF geom_pt[OF that, of a]] unfolding f_def by simp
  have GI: "set_integrable lborel {0<..} (\<lambda>u. u ^ 4 * exp (- (a * u)) / (exp u - 1))"
    by (rule set_integrable_cong_Ioi[OF conjunct1[OF IG]]) (rule G)
  have GV: "set_lebesgue_integral lborel {0<..} (\<lambda>u. u ^ 4 * exp (- (a * u)) / (exp u -
    1)) = 24 * Z"
  proof -
    have "set_lebesgue_integral lborel {0<..} (\<lambda>u. u ^ 4 * exp (- (a * u)) / (exp u - 1)) =
          set_lebesgue_integral lborel {0<..} (\<lambda>u. \<Sum> n. f n u)"
      by (rule set_integral_cong_Ioi) (rule G[symmetric])
    also have "\<dots> = 24 * Z" using conjunct2[OF IG] sums_unique[OF fsum] by simp
    finally show ?thesis .
  qed
  have i4: "set_integrable lborel {0<..} (\<lambda>u. 1 / 4 * (u ^ 4 * exp (- (a * u))))"
    by (intro set_integrable_mult_right gam_integrable[OF a])
  have iG: "set_integrable lborel {0<..} (\<lambda>u. 1 / 2 * (u ^ 4 * exp (- (a * u)) / (exp u -
    1)))"
    by (intro set_integrable_mult_right GI)
  have i3: "set_integrable lborel {0<..} (\<lambda>u. 1 / 2 * (u ^ 3 * exp (- (a * u))))"
    by (intro set_integrable_mult_right gam_integrable[OF a])
  have H: "u ^ 4 * exp (- (a * u)) * (1 / 4 + 1 / (2 * (exp u - 1)) - 1 / (2 * u)) =
           1 / 4 * (u ^ 4 * exp (- (a * u))) + 1 / 2 * (u ^ 4 * exp (- (a * u)) / (exp u - 1)) - 1 /
             2 * (u ^ 3 * exp (- (a * u)))"
    if u: "0 < u" for u
  proof -
    have "exp u - 1 \<noteq> 0" using u by simp
    thus ?thesis using u by (simp add: field_simps eval_nat_numeral)
  qed
  have HI: "set_integrable lborel {0<..} (\<lambda>u. 1 / 4 * (u ^ 4 * exp (- (a * u))) + 1 / 2 *
    (u ^ 4 * exp (- (a * u)) / (exp u - 1)) - 1 / 2 * (u ^ 3 * exp (- (a * u))))"
    by (intro set_integral_diff(1) set_integral_add(1) i4 iG i3)
  have HV: "set_lebesgue_integral lborel {0<..} (\<lambda>u. 1 / 4 * (u ^ 4 * exp (- (a * u))) + 1 /
    2 * (u ^ 4 * exp (- (a * u)) / (exp u - 1)) - 1 / 2 * (u ^ 3 * exp (- (a * u))))
      = 6 / a ^ 5 - 3 / a ^ 4 + 12 * Z"
    unfolding set_integral_diff(2)[OF set_integral_add(1)[OF i4 iG] i3] set_integral_add(2)[OF i4
      iG] set_integral_mult_right
      GV gam[OF a] by (simp add: fact_numeral)
  show ?thesis
  proof
    show "set_integrable lborel {0<..} (\<lambda>u. u ^ 4 * exp (- (a * u)) * (1 / 4 + 1 / (2 *
      (exp u - 1)) - 1 / (2 * u)))"
      by (rule set_integrable_cong_Ioi[OF HI]) (rule H[symmetric])
    have "set_lebesgue_integral lborel {0<..} (\<lambda>u. u ^ 4 * exp (- (a * u)) * (1 / 4 + 1 /
      (2 * (exp u - 1)) - 1 / (2 * u))) =
          set_lebesgue_integral lborel {0<..} (\<lambda>u. 1 / 4 * (u ^ 4 * exp (- (a * u))) + 1 /
            2 * (u ^ 4 * exp (- (a * u)) / (exp u - 1)) - 1 / 2 * (u ^ 3 * exp (- (a * u))))"
      by (rule set_integral_cong_Ioi) (rule H)
    thus "set_lebesgue_integral lborel {0<..} (\<lambda>u. u ^ 4 * exp (- (a * u)) * (1 / 4 + 1 /
      (2 * (exp u - 1)) - 1 / (2 * u))) = 6 / a ^ 5 - 3 / a ^ 4 + 12 * Z"
      using HV by simp
  qed
qed

end
