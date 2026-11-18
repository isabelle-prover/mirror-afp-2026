section \<open>Isoperimetric theorem for convex curves\<close>

theory Isoperimetric
  imports Green_Variant

begin

text \<open>
  Formalisation of the isoperimetric inequality, following John Harrison's
  HOL Light proof in @{text "100/isoperimetric.ml"}.

  The proof has six parts:
  \<^enum> Convex curve lemmas (switching between views of a convex simple closed curve)
  \<^enum> The Wirtinger inequality
  \<^enum> A special case of Green's theorem for convex area
  \<^enum> The isoperimetric theorem for convex curves
  \<^enum> Convexification of an arbitrary rectifiable simple closed curve
  \<^enum> The full isoperimetric theorem

  Infrastructure is provided by the prerequisite theories:
  \<^item> @{text Bounded_Variation}: bounded variation and vector variation
  \<^item> @{text Absolute_Continuity}: absolute continuity and FTC
  \<^item> @{text Rectifiable_Path}: rectifiable paths and path length
  \<^item> @{text Green_Variant}: a form of the Green Area Theorem

  AFP dependencies:
  \<^item> @{text Fourier}: trigonometric orthonormal system, Bessel inequality,
    L2 Fourier convergence (useful for Wirtinger inequality)
  \<^item> @{text Lp} (via Fourier): Hölder inequality, Minkowski inequality
\<close>

text \<open>The kernel lemma: the isoperimetric inequality for a convex curve that has been
  normalized to arc-length parametrization with zero-mean imaginary part and
  diameter along the real axis starting at a point with $Re = 0$.
  This is where the Wirtinger inequality is applied.\<close>

lemma isoperimetric_kernel:
  fixes g :: "real \<Rightarrow> complex" and L :: real and a b :: complex
  assumes "0 < L"
    and conv_in: "convex (inside (path_image g))"
    and ab: "a \<in> path_image g" "b \<in> path_image g"
    and dist_ab: "dist a b = diameter (path_image g)"
    and bma: "b - a = of_real (dist a b)"
    and ga: "pathstart g = a" "pathfinish g = a"
    and g: "rectifiable_path g" "simple_path g"
    and L: "path_length g = L"
    and arc_length: "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g) = L * t"
    and lipschitz: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
    and "Re a = 0"
    and "(Im \<circ> g has_integral 0) {0..1}"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>c r. path_image g = sphere c r"
proof -
  have "a\<noteq>b"
    using ab(1) dist_ab bounded_simple_path_image diameter_eq_0 g(2) nonempty_simple_path_endless
    by fastforce
  have acont_g: "absolutely_continuous_on {0..1} g"
    by (metis Lipschitz_imp_absolutely_continuous dist_norm lipschitz real_norm_def)
  define S where "S = {x \<in> {0..1}. \<not> g differentiable (at x)}"
  have negS: "negligible S"
    unfolding S_def using Lebesgue_differentiation_thm_compact
    by (metis (full_types) absolutely_continuous_on_imp_has_bounded_variation_on
        acont_g cbox_interval compact_Icc compact_imp_bounded)
  define g' where "g' \<equiv> (\<lambda>x. vector_derivative g (at x))"
  have g'_deriv: "\<And>x. x \<in> {0..1} - S \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
    by (simp add: S_def g'_def vector_derivative_works)
  have g'_int: "g' absolutely_integrable_on {0..t} \<and> integral {0..t} g' = g t - a" 
    if "t \<in> {0..1::real}" for t
  proof -
    have lhs: "g' absolutely_integrable_on {0..1} \<and> (\<forall>x\<in>{0..1}. (g' has_integral g x - g 0) {0..x})"
      unfolding absolute_integral_absolutely_continuous_derivative_eq
      by (metis has_vector_derivative_at_within acont_g negS g'_deriv)
    have abs_int_t: "g' absolutely_integrable_on {0..t}"
      using absolutely_integrable_on_subinterval[OF conjunct1[OF lhs]] that by auto
    moreover have "integral {0..t} g' = g t - a"
      using ga by (metis integral_unique lhs pathstart_def that)
    ultimately show ?thesis
      by auto
  qed
  have norm_g'_int: "(\<lambda>x. norm (g' x)) absolutely_integrable_on {0..t} \<and> integral {0..t} (\<lambda>x. norm (g' x)) = L * t"
    if "t \<in> {0..1}" for t
  proof -
    have acont_gt: "absolutely_continuous_on {0..t} g"
      using absolutely_continuous_on_subset[OF acont_g] that by auto
    have g'_deriv_t: "\<And>x. x \<in> {0..t} - S \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
      using g'_deriv that by auto
    have "vector_variation {0..t} g = integral {0..t} (\<lambda>u. norm (g' u))"
      using vector_variation_integral_norm_derivative[OF negS _ acont_gt g'_deriv_t] that
      by presburger
    moreover have "vector_variation {0..t} g = L * t"
      using that \<open>rectifiable_path g\<close> path_length_subpath_eq [of 0 t, symmetric] arc_length
      by (fastforce simp: closed_segment_eq_real_ivl1)
    moreover have "(\<lambda>x. norm (g' x)) absolutely_integrable_on {0..t}"
      using g'_int set_integrable_norm that by blast
    ultimately show ?thesis
      using that by auto
  qed
  have norm_g'_le: "norm (g' x) \<le> L" if "x \<in> {0..1} - S" for x
  proof -
    have ev: "\<forall>\<^sub>F y in at x within {0..1}. norm (g y - g x) \<le> norm (L * y - L * x)"
      unfolding eventually_at_filter
    proof (intro always_eventually allI impI)
      fix y assume "y \<noteq> x" "y \<in> {0..1}"
      have "norm (g y - g x) \<le> \<bar>L * (y - x)\<bar>"
        using lipschitz \<open>y \<in> {0..1}\<close> that by (fastforce simp: dist_norm)
      also have "\<dots> = norm (L * y - L * x)"
        by (simp add: right_diff_distrib)
      finally show "norm (g y - g x) \<le> norm (L * y - L * x)" .
    qed
    have gd: "(g has_vector_derivative g' x) (at x)" using g'_deriv that by auto
    have xlimpt: "x islimpt {0..1::real}"
      using limpt_of_convex[of "{0..1::real}" x] that by auto
    have Ld: "((\<lambda>t. L * t) has_vector_derivative L) (at x within {0..1})"
      using has_vector_derivative_mult_right[OF has_vector_derivative_id] by simp
    show "norm (g' x) \<le> L"
      using \<open>0 < L\<close> norm_vector_derivatives_le_within [OF _ Ld ev] xlimpt gd has_vector_derivative_at_within
      by (force simp add: trivial_limit_within)
  qed

  have norm_g'_sq_int: "(\<lambda>x. (norm (g' x))\<^sup>2) absolutely_integrable_on {0..1}"
  proof (rule measurable_bounded_by_integrable_imp_absolutely_integrable_ae)
    show "(\<lambda>x. (norm (g' x))\<^sup>2) \<in> borel_measurable (lebesgue_on {0..1})"
      by (simp add: absolutely_integrable_imp_borel_measurable borel_measurable_power norm_g'_int)
    fix x assume "x \<in> {0..1} - S"
    then show "norm ((norm (g' x))\<^sup>2) \<le> L\<^sup>2"
      using norm_g'_le by (simp add: power_mono)
  qed (use negS in auto)

  have integral_norm_g'_sq: "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x. (norm (g' x))\<^sup>2) = L\<^sup>2"
  proof -
    let ?int01 = "{0..1::real}"
    have meas01: "?int01 \<in> sets lebesgue" by simp
    have norm_g'_leb: "integrable (lebesgue_on {0..1}) (\<lambda>x. norm (g' x))"
      using norm_g'_int[of 1] absolutely_integrable_imp_integrable 
      using absolutely_integrable_imp_integrable[OF _ meas01] by auto
    have int_norm_g': "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x. norm (g' x)) = L"
      by (simp add: lebesgue_integral_eq_integral norm_g'_int norm_g'_leb)
    have const_leb: "integrable (lebesgue_on {0..1}) (\<lambda>x::real. L)"
      by (simp add: integrable_const_ivl)
    have int_const: "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x::real. L) = L"
      using lebesgue_integral_const[of "lebesgue_on {0..1}" L]
      by (simp add: measure_restrict_space)
    have ae_le: "AE x in lebesgue_on {0..1}. norm (g' x) \<le> L"
    proof -
      have "S \<inter> {0..1} \<in> null_sets (lebesgue_on {0..1})"
        using negS negligible_iff_null_sets null_sets_restrict_space
        by (metis inf_le2 meas01 null_set_Int2)
      then have "AE x in lebesgue_on {0..1}. x \<notin> S"
        by (metis AE_not_in Collect_subset S_def inf.orderE)
      then show ?thesis
        using norm_g'_le by (auto elim: eventually_mono)
    qed
    \<comment> \<open>Therefore $\mathit{norm}\,(g'\,x) = L$ a.e.\<close>
    have ae_eq: "AE x in lebesgue_on {0..1}. norm (g' x) = L"
      using integral_ineq_eq_0_then_AE[OF ae_le norm_g'_leb const_leb] int_norm_g' int_const
      by simp
    \<comment> \<open>Therefore $(\mathit{norm}\,(g'\,x))^2 = L^2$ a.e.\<close>
    have ae_sq: "AE x in lebesgue_on {0..1}. (norm (g' x))\<^sup>2 = L\<^sup>2"
      using ae_eq by (rule AE_mp) auto
    \<comment> \<open>Conclude by \<open>integral_cong_AE\<close>\<close>
    have meas_sq: "(\<lambda>x. (norm (g' x))\<^sup>2) \<in> borel_measurable (lebesgue_on {0..1})"
      using absolutely_integrable_imp_borel_measurable meas01 norm_g'_sq_int by blast
    have "integral\<^sup>L (lebesgue_on ?int01) (\<lambda>x. (norm (g' x))\<^sup>2) =
          integral\<^sup>L (lebesgue_on ?int01) (\<lambda>x. L\<^sup>2)"
      by (rule integral_cong_AE[OF meas_sq _ ae_sq]) simp
    also have "\<dots> = L\<^sup>2"
      using lebesgue_integral_const by (simp add: measure_restrict_space)
    finally show ?thesis .
  qed
  let ?G = "\<lambda>t. Re (g' t) * Im (g t)"
  text \<open>Use the Green formula for the area inside the curve.\<close>
  have green_ai: "?G absolutely_integrable_on {0..1}"
    and green_area: "\<bar>integral {0..1} ?G\<bar> = measure lebesgue (inside (path_image g))"
  proof -
    interpret G: Green g g' S a b
    proof (intro Green.intro g ga negS g'_deriv ab dist_ab conv_in acont_g)
      show "Re a < Re b"
        by (metis \<open>a\<noteq>b\<close> Re_complex_of_real \<open>Re a = 0\<close> bma diff_zero dist_nz minus_complex.sel(1))
      show "Im a = Im b"
        using bma by (simp add: complex_of_real_def complex_eq_iff)
    qed auto
    from G.area_theorem show "?G absolutely_integrable_on {0..1}"
      and "\<bar>integral {0..1} ?G\<bar> = measure lebesgue (inside (path_image g))"
      by (metis (full_types))+
  qed

  have integrable: "?G integrable_on {0..1}"
    using green_ai absolutely_integrable_on_def by blast
  obtain sgn :: real where sgn2: "sgn\<^sup>2 = 1"
    and has_int_green: "(?G has_integral (sgn * measure lebesgue (inside (path_image g)))) {0..1}"
  proof (cases "integral {0..1} ?G \<ge> 0")
    case True
    then show thesis
      using that[of 1] integrable green_area by (simp add: has_integral_integrable_integral)
  next
    case False
    then show thesis using that[of "-1"]
      using integrable green_area by (simp add: has_integral_iff)
  qed

  have has_int_norm_sq: "((\<lambda>x. (norm (g' x))\<^sup>2) has_integral L\<^sup>2) {0..1}"
    using lebesgue_integral_eq_integral[of "{0..1}" "\<lambda>x. (norm (g' x))\<^sup>2"]
          absolutely_integrable_imp_integrable[OF norm_g'_sq_int]
    using integral_norm_g'_sq norm_g'_sq_int
    by (auto simp: absolutely_integrable_on_def)

  have has_int_key: "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 +
    (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral
    (L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi)) {0..1}"
  proof -
    have integrand_eq: "\<And>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 + (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2 =
      (norm (g' x))\<^sup>2 - 4 * pi * sgn * Re (g' x) * Im (g x)"
      using sgn2 cmod_power2 by (simp add: power2_eq_square algebra_simps)
    have val: "4 * pi * sgn * (sgn * measure lebesgue (inside (path_image g))) =
      measure lebesgue (inside (path_image g)) * 4 * pi"
      using sgn2 by (simp add: power2_eq_square algebra_simps)
    have "((\<lambda>t. 4 * pi * sgn * Re (g' t) * Im (g t)) has_integral
      (measure lebesgue (inside (path_image g)) * 4 * pi)) {0..1}"
      using has_integral_mult_right[OF has_int_green, of "4 * pi * sgn"]
      unfolding val by (simp add: algebra_simps)
    then show ?thesis
      using has_integral_diff[OF has_int_norm_sq] integrand_eq by presburger
  qed

  have key: "0 \<le> L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi \<and>
             (L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi = 0 \<longrightarrow>
             (\<exists>c r. path_image g = sphere c r))"
  proof (cases "inside(path_image g) = {}")
    case False
    have Im_g'_has_int: "((\<lambda>t. Im (g' t)) has_integral (Im (g x) - Im (g 0))) {0..x}"
      if "x \<in> {0..1}" for x
      using ga has_integral_Im g'_int has_integral_iff set_lebesgue_integral_eq_integral(1) that
      by (metis pathstart_def minus_complex.simps(2))
    have Im_g_periodic: "Im (g 1) = Im (g 0)"
      using ga by (simp add: pathstart_def pathfinish_def)
    have Im_g_zero_mean: "((\<lambda>x. Im (g x)) has_integral 0) {0..1}"
      using assms by (simp add: o_def)

    have "(\<lambda>x. (Im (g' x))\<^sup>2) absolutely_integrable_on {0..1}"
    proof (rule measurable_bounded_by_integrable_imp_absolutely_integrable_ae)
      show "(\<lambda>x. (Im (g' x))\<^sup>2) \<in> borel_measurable (lebesgue_on {0..1})"
        by (simp add: Im_absolutely_integrable_on absolutely_integrable_imp_borel_measurable
            borel_measurable_power g'_int sets_completionI_sets)
      fix x assume "x \<in> {0..1} - S"
      then have "norm (g' x) \<le> L" using norm_g'_le by auto
      then show "norm ((Im (g' x))\<^sup>2) \<le> L\<^sup>2"
        by (metis abs_Im_le_cmod order.trans norm_ge_zero norm_power power_mono real_norm_def)
    qed (use negS in auto)
    then have Im_g'_sq_int: "(\<lambda>x. (Im (g' x))\<^sup>2) integrable_on {0..1}"
      using absolutely_integrable_on_def by blast
    have wirt1: "(\<lambda>x. (Im (g x))\<^sup>2) integrable_on {0..1}"
      and wirt2: "integral {0..1} (\<lambda>x. (2*pi * Im (g x))\<^sup>2) \<le> integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2)"
      and wirt3: "integral {0..1} (\<lambda>x. (2*pi * Im (g x))\<^sup>2) = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2) \<Longrightarrow>
        \<exists>c a. \<forall>x \<in> {0..1}. Im (g x) = c * sin (2*pi*x - a)"
      using scaled_Wirtinger_inequality[OF Im_g'_has_int Im_g_periodic Im_g_zero_mean Im_g'_sq_int]
      by auto
    have sq: "(\<lambda>x. (2 * pi * Im (g x))\<^sup>2) integrable_on {0..1}"
      using integrable_cmul[OF wirt1, of "(2*pi)\<^sup>2"]
      by (simp add: power_mult_distrib mult.commute)
    then obtain w where w: "((\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral w) {0..1}"
      using integrable_diff[OF Im_g'_sq_int sq] by force
    then have "w = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2)"
      by (simp add: integral_unique)
    also have w_eq: "\<dots> = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2) - integral {0..1} (\<lambda>x. (2 * pi * Im (g x))\<^sup>2)"
      using sq integral_diff[OF Im_g'_sq_int]
      by (simp add: power_mult_distrib mult.commute)
    finally have w_nonneg: "0 \<le> w"
            and w_zero: "w = 0 \<Longrightarrow> \<exists>c a. \<forall>x \<in> {0..1}. Im (g x) = c * sin (2*pi*x - a)"
      using wirt2 wirt3 by argo+
    define d where "d = L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi - w"
    have key_eq: "L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi = d + w"
      unfolding d_def by linarith

    have sq_has_int: "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) has_integral d) {0..1}"
      using has_integral_diff[OF has_int_key w] d_def by auto
    have d_nonneg: "0 \<le> d"
      using integral_nonneg [OF has_integral_integrable[OF sq_has_int]] integral_unique[OF sq_has_int]
      by simp
    have "\<exists>c r. path_image g = sphere c r" if "d + w = 0"
    proof -
      have d0: "d = 0" and w0: "w = 0"
        using that d_nonneg w_nonneg by linarith+
      obtain C A where CA: "\<And>x. x \<in> {0..1} \<Longrightarrow> Im (g x) = C * sin (2*pi*x - A)"
        using w_zero[OF w0] by blast
      have sq_zero: "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) has_integral 0) {0..1}"
        using sq_has_int d0 by simp
      have neg_Re: "negligible {x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0}"
      proof -
        have sq_abs: "(\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) absolutely_integrable_on {0..1}"
          using nonnegative_absolutely_integrable_1[OF has_integral_integrable[OF sq_zero]]
          by (simp add: zero_le_power2)
        have sq_leb: "integrable (lebesgue_on {0..1}) (\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2)"
          by (rule absolutely_integrable_imp_integrable[OF sq_abs]) simp
        have leb_zero: "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) = 0"
          using lebesgue_integral_eq_integral[OF sq_leb] integral_unique[OF sq_zero] by simp
        have "AE x in lebesgue_on {0..1}. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 = 0"
          using integral_nonneg_eq_0_iff_AE[OF sq_leb] leb_zero
          by (simp add: zero_le_power2)
        then have ae: "AE x in lebesgue_on {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) = 0"
          by (rule AE_mp) (auto simp: power2_eq_square)
        then obtain N0 where N0: "N0 \<in> null_sets (lebesgue_on {0..1})"
          and sub: "{x \<in> space (lebesgue_on {0..1}). Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0} \<subseteq> N0"
          by (auto simp: eventually_ae_filter[of _ "lebesgue_on {0..1}"])
        have "negligible N0"
          by (meson N0 fmeasurableD lmeasurable_interval(1) negligible_iff_null_sets null_sets_restrict_space)
        moreover have "{x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0} \<subseteq> N0"
          using sub by (auto simp: space_lebesgue_on)
        ultimately show ?thesis
          by (meson negligible_subset)
      qed
      have neg_Re': "negligible {x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * C * sin (2*pi*x - A) \<noteq> 0}"
        using neg_Re by (simp add: CA mult.assoc cong: conj_cong)
      have Re_g: "Re (g x) = - sgn * C * (cos (2*pi*x - A) - cos A)"
        if x: "x \<in> {0..1}" for x
      proof -
        have "((\<lambda>t. Re (g' t)) has_integral Re (g x - a)) {0..x}"
          by (metis has_integral_Re g'_int integrable_integral set_lebesgue_integral_eq_integral(1) that)
        then have Re_g'_int: "((\<lambda>t. Re (g' t)) has_integral Re (g x)) {0..x}"
          using \<open>Re a = 0\<close> by simp
        have \<section>: "((\<lambda>t. - sgn * C * cos (2 * pi * t - A)) has_vector_derivative
            2 * pi * sgn * C * sin (2 * pi * t - A)) (at t within {0..x})" for t
          unfolding has_real_derivative_iff_has_vector_derivative [symmetric]
          by (intro derivative_eq_intros) (auto simp: algebra_simps)
        have sin_int: "((\<lambda>t. 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral
          (- sgn * C * (cos (2 * pi * x - A) - cos A))) {0..x}"
          using fundamental_theorem_of_calculus[OF _ \<section>] x by (simp add: algebra_simps)
        \<comment> \<open>the integrand is $0$ a.e., so the integral is $0$\<close>
        have neg_sub: "negligible {t \<in> {0..x}. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A) \<noteq> 0}"
          by (rule negligible_subset[OF neg_Re']) (use x in auto)
        have "((\<lambda>t. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral 0) {0..x}"
          by (rule has_integral_spike[OF neg_sub _ has_integral_0]) auto
        then show ?thesis
          using has_integral_unique has_integral_diff[OF Re_g'_int sin_int]
          using right_minus_eq by blast
      qed
      \<comment> \<open>Final step: @{term "path_image g = sphere c \<bar>C\<bar>"}\<close>
      define c where "c = Complex (sgn * C * cos A) 0"
      have subset: "path_image g \<subseteq> sphere c \<bar>C\<bar>"
      proof -
        have "cmod (g t - c) = \<bar>C\<bar>" if "t \<in> {0..1}" for t
        proof -
          have eq_gt: "g t - c = Complex (- sgn * C * cos (2*pi*t - A)) (C * sin (2*pi*t - A))"
            unfolding c_def using Re_g[OF that] CA[OF that] by (simp add: complex_eqI algebra_simps)
          have "(cmod (g t - c))\<^sup>2 = (sgn * C * cos (2*pi*t - A))\<^sup>2 + (C * sin (2*pi*t - A))\<^sup>2"
            using eq_gt by (simp add: complex_norm power2_eq_square)
          also have "\<dots> = C\<^sup>2 * (sgn\<^sup>2 * (cos (2*pi*t - A))\<^sup>2 + (sin (2*pi*t - A))\<^sup>2)"
            using eq_gt by (simp add: complex_norm power2_eq_square algebra_simps power2_eq_square)
          also have "\<dots> = C\<^sup>2 * ((cos (2*pi*t - A))\<^sup>2 + (sin (2*pi*t - A))\<^sup>2)"
            using sgn2 by (simp add: algebra_simps power2_eq_square)
          also have "\<dots> = \<bar>C\<bar>\<^sup>2"
            by (simp add: power2_abs sin_cos_squared_add3)
          finally show "cmod (g t - c) = \<bar>C\<bar>"
            by (simp add: cmod_def)
        qed
        then show ?thesis
          by (auto simp: path_image_def sphere_def dist_norm norm_minus_commute)
      qed
      have supset: "sphere c \<bar>C\<bar> \<subseteq> path_image g"
      proof (cases "C = 0")
        case True
        have "g 0 = c"
          using Re_g[of 0] CA[of 0] by (simp add: c_def True complex_eqI)
        moreover have "g 0 \<in> path_image g"
          by (simp add: path_image_def)
        ultimately show ?thesis by (simp add: True sphere_def dist_self)
      next
        case Cne: False
        show ?thesis
        proof (rule subsetI)
          fix z assume z: "z \<in> sphere c \<bar>C\<bar>"
          then have zc_norm: "cmod (z - c) = \<bar>C\<bar>"
            by (simp add: sphere_def dist_norm norm_minus_commute)
          \<comment> \<open>Find the angle for $(z-c)$ scaled to the unit circle\<close>
          have unit: "cmod (Complex (- Re (z - c) / (sgn * C)) (Im (z - c) / C)) = 1"
          proof -
            have "(cmod (Complex (- Re (z - c) / (sgn * C)) (Im (z - c) / C)))\<^sup>2
                = (Re (z - c))\<^sup>2 / (sgn\<^sup>2 * C\<^sup>2) + (Im (z - c))\<^sup>2 / C\<^sup>2"
              by (metis (no_types, lifting) cmod_power2 complex.sel power2_minus power_divide
                  power_mult_distrib)
            also have "\<dots> = \<bar>C\<bar>\<^sup>2 / C\<^sup>2"
              by (metis zc_norm add_divide_distrib cmod_power2 mult_cancel_right2 sgn2)
            also have "\<dots> = 1"
              using Cne by (simp add: power2_abs)
            finally show ?thesis
              using norm_ge_zero by (simp add: abs_square_eq_1)
          qed
          obtain \<theta> where \<theta>_bounds: "0 \<le> \<theta>" "\<theta> < 2*pi"
            and \<theta>_eq: "Complex (- Re (z - c) / (sgn * C)) (Im (z - c) / C) = Complex (cos \<theta>) (sin \<theta>)"
            using complex_unimodular_polar[OF unit] by auto
          have \<theta>_Re: "- Re (z - c) / (sgn * C) = cos \<theta>"
            and \<theta>_Im: "Im (z - c) / C = sin \<theta>"
            using \<theta>_eq by (simp_all add: complex.expand)
              \<comment> \<open>Find $t \in [0,1]$ with $2\pi t - A \equiv \theta \pmod{2\pi}$\<close>
          define t where "t = frac ((\<theta> + A) / (2 * pi))"
          have t01: "t \<in> {0..1}"
            using Multiseries_Expansion_Bounds.trivial_bounds_frac t_def by blast
          have *: "2*pi*t = (\<theta> + A) - of_int \<lfloor>(\<theta> + A) / (2*pi)\<rfloor> * (2*pi)"
            using pi_gt_zero by (simp add: t_def frac_def field_simps)
          have cos_eq: "cos (2*pi*t - A) = cos \<theta>"
            unfolding * by (simp add: cos_diff mult_of_int_commute)
          have sin_eq: "sin (2*pi*t - A) = sin \<theta>"
            unfolding * by (simp add: mult_of_int_commute sin_diff)
          have "g t = z"
          proof (rule complex_eqI)
            have "sgn \<noteq> 0" using sgn2 by fastforce
            have "Re (g t) = - sgn * C * cos \<theta> + sgn * C * cos A"
              using cos_eq by (simp add: Re_g[OF t01] algebra_simps)
            also have "\<dots> = Re (z - c) + Re c"
              using \<open>sgn \<noteq> 0\<close> sgn2 \<theta>_Re Cne by (simp add: c_def field_simps)
            finally show "Re (g t) = Re z" by simp
          next
            show "Im (g t) = Im z"
              using CA Cne \<theta>_Im sin_eq c_def nonzero_divide_eq_eq t01 by fastforce
          qed
          moreover have "g t \<in> path_image g"
            using t01 by (auto simp: path_image_def)
          ultimately show "z \<in> path_image g" by simp
        qed
      qed
      show ?thesis
        using subset supset by (auto intro!: exI[of _ c] exI[of _ "\<bar>C\<bar>"])
    qed
    then show ?thesis
      using d_nonneg w_nonneg key_eq by argo
  qed (use \<open>L>0\<close> in auto)
  show "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
        "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
    \<exists>c r. path_image g = sphere c r"
    using key by (simp_all add: field_simps)
qed

text \<open>Reduction lemmas for the reparametrization steps.\<close>


lemma isoperimetric_reduce_shift:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
    "a \<in> path_image g"
  obtains h where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = a"
    "convex (inside (path_image h))"
    "path_length h = L"
    "path_image h = path_image g"
proof -
  obtain t where t: "t \<in> {0..1}" "g t = a"
    using assms(6) by (auto simp: path_image_def)
  let ?h = "shiftpath t g"
  show thesis
  proof
    show "rectifiable_path ?h"
      using assms rectifiable_path_shiftpath t(1) by blast
    show "simple_path ?h"
      using assms(2,3) simple_path_shiftpath t(1) by auto
    show "pathfinish ?h = pathstart ?h"
      using assms(3) closed_shiftpath t(1) by blast
    show "pathstart ?h = a"
      using pathstart_shiftpath t by auto
    show "path_image ?h = path_image g"
      using assms(3) path_image_shiftpath t(1) by blast
    then show "convex (inside (path_image ?h))"
      by (simp add: assms(4))
    show "path_length ?h = L"
      using assms path_length_shiftpath t(1) by blast
  qed
qed

lemma isoperimetric_reduce_rotate_translate:
  fixes g :: "real \<Rightarrow> complex" and a b :: complex
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g" "pathstart g = a"
    "convex (inside (path_image g))"
    "path_length g = L"
    "b \<in> path_image g" "dist a b = diameter (path_image g)"
    "a \<noteq> b"
  obtains h a' b' where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = a'"
    "convex (inside (path_image h))"
    "path_length h = L"
    "b' \<in> path_image h" "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "Re a' = 0"
    "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    "\<And>c r. path_image h = sphere c r \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
proof -
  define r where "r = cis (- Arg (b - a))"
  define h where "h = (*) r \<circ> (+) (-a) \<circ> g"
  define b' where "b' = r * (b - a)"
  have r_norm: "norm r = 1" unfolding r_def by simp
  have r_ne: "r \<noteq> 0" using r_norm by auto
  have lin_r: "linear ((*) r)" by (intro linearI) (auto simp: algebra_simps scaleR_conv_of_real)
  have inj_r: "inj ((*) r)" using r_ne by (simp add: inj_def)
  have norm_r: "\<And>x. norm (r * x) = norm x" using r_norm
    by (simp add: norm_mult)
  have dist_r: "\<And>x y. dist (r * x) (r * y) = dist x y"
    by (simp add: dist_mult_left r_norm)
  \<comment> \<open>Translation step: @{term "g1 = (+) (-a) \<circ> g"}\<close>
  define g1 where "g1 = (+) (-a) \<circ> g"
  have rect_g1: "rectifiable_path g1"
    unfolding g1_def using assms(1) rectifiable_path_translation_eq by blast
  have sp_g1: "simple_path g1"
    unfolding g1_def using assms(2) simple_path_translation_eq by blast
  have pi_g1: "path_image g1 = (+) (-a) ` path_image g"
    unfolding g1_def by (simp add: path_image_compose image_comp)
  have ps_g1: "pathstart g1 = 0"
    unfolding g1_def using assms(4) by (simp add: pathstart_compose)
  have pf_g1: "pathfinish g1 = 0"
    unfolding g1_def using assms(3,4) by (simp add: pathstart_compose pathfinish_compose)
  have pl_g1: "path_length g1 = L"
    unfolding g1_def using assms(6) path_length_translation by blast
  \<comment> \<open>Rotation step: @{term "h = (*) r \<circ> g1"}\<close>
  have h_eq: "h = (*) r \<circ> g1" unfolding h_def g1_def by (simp add: comp_assoc)
  have pi_h: "path_image h = (*) r ` path_image g1"
    unfolding h_eq by (simp add: path_image_compose image_comp)
  \<comment> \<open>Key: $r \cdot (b-a)$ is a positive real\<close>
  have "r * (b - a) = cis (- Arg (b-a)) * (b-a)"
    unfolding r_def by simp
  also have "\<dots> = of_real (cmod (b-a))"
    by (subst (2) rcis_cmod_Arg[symmetric, of "b - a"]) (simp add: rcis_def cis_mult)
  finally have rb_real: "b' = of_real (cmod (b-a))" unfolding b'_def by simp
  show ?thesis
  proof 
    show "rectifiable_path h"
      unfolding h_eq using rect_g1 rectifiable_path_linear_image_eq[OF lin_r inj_r] by simp
    show "simple_path h"
      unfolding h_eq using sp_g1 simple_path_linear_image_eq[OF lin_r inj_r] by simp
    show "pathfinish h = pathstart h"
      unfolding h_eq using pf_g1 ps_g1 by (simp add: pathstart_compose pathfinish_compose)
    show "pathstart h = 0"
      unfolding h_eq using ps_g1 by (simp add: pathstart_compose)
    show "path_length h = L"
      unfolding h_eq using pl_g1 path_length_linear_image[OF lin_r norm_r] by simp
    show "b' \<in> path_image h"
      unfolding pi_h b'_def g1_def using assms(7)
      by (auto simp: path_image_compose image_comp image_iff)
    show "dist 0 b' = diameter (path_image h)"
    proof -
      have "diameter (path_image h) = diameter ((*) r ` path_image g1)"
        unfolding pi_h by simp
      also have "\<dots> = diameter (path_image g1)"
      proof -
        have "(\<lambda>(x,y). dist x y) ` ((*) r ` path_image g1 \<times> (*) r ` path_image g1) =
              (\<lambda>(x,y). dist x y) ` (path_image g1 \<times> path_image g1)"
          by (force simp: image_iff dist_r)
        then show ?thesis by (simp add: diameter_def)
      qed
      also have "\<dots> = diameter (path_image g)"
        unfolding pi_g1 by (metis diameter_translation)
      finally have diam_eq: "diameter (path_image h) = diameter (path_image g)" .
      have "dist 0 b' = dist a b"
        unfolding b'_def by (simp add: dist_norm norm_r norm_minus_commute)
      then show ?thesis using diam_eq assms(8) by simp
    qed
    have "inside ((*) r ` path_image g1) = (*) r ` inside (path_image g1)"
    proof (rule set_eqI)
      fix x
      define y where "y = inverse r * x"
      then have xy: "x = r * y" using r_ne by simp
      have bij_r: "bij ((*) r)"
        unfolding bij_def using lin_r inj_r eucl.linear_inj_imp_surj[OF lin_r inj_r] by blast
      have compl_img: "(*) r ` (- path_image g1) = - ((*) r ` path_image g1)"
        using bij_image_Compl_eq[OF bij_r] .
      have homeo: "homeomorphism (- path_image g1) ((*) r ` (- path_image g1)) ((*) r) ((*) (inverse r))"
      proof (rule homeomorphismI)
        show "continuous_on (- path_image g1) ((*) r)"
          "continuous_on ((*) r ` (- path_image g1)) ((*) (inverse r))"
          by (intro continuous_intros)+
        show "(*) (inverse r) ` ((*) r ` (- path_image g1)) \<subseteq> - path_image g1"
          using r_ne 
          by (clarsimp simp: image_iff) (metis divide_inverse_commute nonzero_mult_div_cancel_left)
      qed (use r_ne in auto)
      have cc: "connected_component_set (- ((*) r ` path_image g1)) x =
                    (*) r ` connected_component_set (- path_image g1) y"
      proof (cases "y \<in> path_image g1")
        case True
        then show ?thesis
          using xy connected_component_eq_empty by blast
      next
        case False
        then show ?thesis 
          using compl_img xy connected_component_set_homeomorphism[OF homeo] by simp
      qed
      have "bounded ((*) r ` connected_component_set (- path_image g1) y) =
            bounded (connected_component_set (- path_image g1) y)"
        by (simp add: bounded_iff norm_r image_iff)
      then show "(x \<in> inside ((*) r ` path_image g1)) = (x \<in> (*) r ` inside (path_image g1))"
        using xy cc by (simp add: inj_image_mem_iff [OF inj_r] inside_def)
    qed
    then have "inside (path_image h) = (*) r ` inside (path_image g1)"
      unfolding pi_h .
    also have "inside (path_image g1) = (+) (-a) ` inside (path_image g)"
      unfolding pi_g1 using inside_translation[of "-a" "path_image g"] by simp
    finally have inside_h: "inside (path_image h) = (*) r ` (+) (-a) ` inside (path_image g)"
      .
    show "convex (inside (path_image h))"
      using inside_h assms(5) by (metis convex_linear_image convex_translation_eq lin_r)
    show "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    proof -
      have meas_g: "inside (path_image g) \<in> lmeasurable"
        by (simp add: Jordan_inside_outside assms lmeasurable_open)
      have "measure lebesgue ((*) r ` (+) (-a) ` inside (path_image g)) =
            measure lebesgue ((+) (-a) ` inside (path_image g))"
      proof -
        have meas_t: "(+) (-a) ` inside (path_image g) \<in> lmeasurable"
          using meas_g measurable_translation by blast
        have "\<bar>eucl.det ((*) r)\<bar> = 1"
          unfolding det_complex r_def by simp
        then show ?thesis
          using measure_linear_image[OF lin_r meas_t] by simp
      qed
      also have "\<dots> = measure lebesgue (inside (path_image g))"
        using measure_translation[of "-a" "inside (path_image g)"] by simp
      finally show ?thesis using inside_h by simp
    qed
    show "\<exists>c' r'. path_image g = sphere c' r'" 
      if sph: "path_image h = sphere c0 r0" for c0 r0
    proof -
      have "(+) (-a) ` path_image g = (*) (inverse r) ` sphere c0 r0"
      proof -
        have *: "\<And>z. inverse r * (r * z) = z"
          using r_ne by (metis left_inverse mult.assoc mult_1)
        have "(*) (inverse r) ` ((*) r ` (+) (-a) ` path_image g) = (+) (-a) ` path_image g"
          by (auto simp: image_iff *)
        then show ?thesis
          using pi_g1 pi_h sph by argo
      qed
      then have "path_image g = (+) a ` (*) (inverse r) ` sphere c0 r0"
        by (metis translation_galois)
      moreover have "(*) (inverse r) ` sphere c0 r0 = sphere (inverse r * c0) r0"
        by (auto simp: nonzero_norm_inverse r_ne r_norm sphere_cscale)
      moreover have "(+) a ` sphere (inverse r * c0) r0 = sphere (a + inverse r * c0) r0"
        using sphere_translation[of a "inverse r * c0" r0] by simp
      ultimately show "\<exists>c' r'. path_image g = sphere c' r'" by auto
    qed
  qed (auto simp: rb_real dist_norm)
qed


lemma isoperimetric_reduce_arc_length:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L" "0 < L"
  obtains h where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = pathstart g"
    "convex (inside (path_image h))"
    "path_length h = L"
    "path_image h = path_image g"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    using arc_length_reparametrization assms by metis

lemma isoperimetric_reduce_zero_mean:
  fixes g :: "real \<Rightarrow> complex" and b :: complex
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
    "b \<in> path_image g"
    "dist (pathstart g) b = diameter (path_image g)"
    "b - pathstart g = of_real (dist (pathstart g) b)"
    "Re (pathstart g) = 0"
    and subp: "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g) = L * t"
    and dist: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
  obtains h a' b' where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h"
    "convex (inside (path_image h))"
    "path_length h = L"
    "a' \<in> path_image h" "b' \<in> path_image h"
    "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "pathstart h = a'" "pathfinish h = a'"
    "Re a' = 0"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    "(Im \<circ> h has_integral 0) {0..1}"
    "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    "\<And>c r. path_image h = sphere c r \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
proof -
  define c where "c = integral {0..1} (Im \<circ> g)"
  define d where "d = -(\<i> * (of_real c :: complex))"
  define h where "h = (+) d \<circ> g"
  define a' where "a' = pathstart g + d"
  define b' where "b' = b + d"
  have h_eq: "\<And>t. h t = g t + d" unfolding h_def comp_def by simp
  have pi_h: "path_image h = (+) d ` path_image g"
    unfolding h_def image_comp [symmetric] path_image_compose by simp
  show ?thesis
  proof 
    show "rectifiable_path h"
      unfolding h_def using assms(1) rectifiable_path_translation_eq[of d g] by simp
    show "simple_path h"
      unfolding h_def using assms(2) simple_path_translation_eq[of d g] by simp
    show "pathfinish h = pathstart h"
      unfolding h_def using assms(3) by (simp add: pathstart_compose pathfinish_compose)
    show "path_length h = L"
      unfolding h_def using assms(5) path_length_translation[of d g] by simp
    show "pathstart h = a'" unfolding h_def a'_def by (simp add: pathstart_compose)
    show "pathfinish h = a'" unfolding h_def a'_def
      using assms(3) by (simp add: pathstart_compose pathfinish_compose)
    show "a' \<in> path_image h"
      unfolding a'_def using pi_h path_image_def pathstart_def by fastforce
    show "b' \<in> path_image h"
      unfolding b'_def using pi_h assms(6) by auto
    show "b' - a' = of_real (dist a' b')"
      unfolding a'_def b'_def using assms(8) by (simp add: dist_norm)
    show "dist a' b' = diameter (path_image h)"
      by (simp add: a'_def assms(7) b'_def diameter_translation pi_h)
    show "Re a' = 0" unfolding a'_def d_def using assms(9) by simp
    show "convex (inside (path_image h))"
      by (simp add: assms(4) inside_translation pi_h)
    show "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
      by (simp add: assms(10) h_def path_length_translation subpath_image)
    show "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
      by (simp add: dist h_eq)
    show "(Im \<circ> h has_integral 0) {0..1}"
    proof -
      have cont_g: "continuous_on {0..1} g"
        using rectifiable_path_imp_path[OF assms(1)] unfolding path_def .
      have int_Im_g: "(\<lambda>t. Im (g t)) integrable_on {0..1}"
        using integrable_continuous_real[OF continuous_on_Im[OF cont_g]] .
      have Im_h: "\<And>t. Im (h t) = Im (g t) - c"
        unfolding h_def comp_def d_def by simp
      have eq: "\<And>t. (Im \<circ> h) t = (\<lambda>t. Im (g t) - c) t"
        using Im_h unfolding comp_def by simp
      have int_sub: "(\<lambda>t. Im (g t) - c) integrable_on {0..1}"
        by (rule integrable_diff[OF int_Im_g integrable_const_ivl])
      have int_h: "(Im \<circ> h) integrable_on {0..1}"
        using integrable_spike_finite[OF finite.emptyI _ int_sub] eq by simp
      have "integral {0..1} (Im \<circ> h) = integral {0..1} (\<lambda>t. Im (g t) - c)"
        using eq by presburger
      also have "\<dots> = integral {0..1} (\<lambda>t. Im (g t)) - integral {0..1} (\<lambda>_::real. c::real)"
        using Henstock_Kurzweil_Integration.integral_diff int_Im_g by blast
      also have "\<dots> = 0" unfolding c_def comp_def by simp
      finally show ?thesis using int_h has_integral_iff by blast
    qed
    show "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
      by (metis inside_translation measure_translation pi_h)
    show "\<exists>c' r'. path_image g = sphere c' r'" if "path_image h = sphere c0 r" for c0 r
      by (metis pi_h sphere_translation that translation_galois)
  qed
qed

theorem isoperimetric_theorem_convex:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
proof -
  have Lpos: "0 < L"
    using simple_path_length_pos_lt[OF assms(1,2)] assms(5) by simp
  text \<open>Step 1: obtain diameter endpoints\<close>
  have compact_pi: "compact (path_image g)"
    using compact_simple_path_image[OF assms(2)] .
  have nonempty_pi: "path_image g \<noteq> {}"
    using path_image_nonempty .
  obtain a b where ab: "a \<in> path_image g" "b \<in> path_image g"
    "dist a b = diameter (path_image g)"
    using diameter_compact_attained[OF compact_pi nonempty_pi] by auto
  text \<open>Step 2: shift start to diameter endpoint a\<close>
  obtain g1 where g1: "rectifiable_path g1" "simple_path g1"
    "pathfinish g1 = pathstart g1" "pathstart g1 = a"
    "convex (inside (path_image g1))"
    "path_length g1 = L" "path_image g1 = path_image g"
    using isoperimetric_reduce_shift[OF assms(1,2,3,4,5) ab(1)] by metis
  have ab1: "a \<in> path_image g1" "b \<in> path_image g1"
    "dist a b = diameter (path_image g1)"
    using ab g1(7) by auto
  have a_ne_b: "a \<noteq> b"
  proof
    assume "a = b"
    then have "diameter (path_image g) = 0" using ab(3) by simp
    then have "path_image g = {a}"
      by (metis ab(1) compact_eq_bounded_closed compact_pi diameter_eq_0 equals0D
          insertE)
    then show False using simple_path_image_uncountable[OF assms(2)]
      by (simp add: countable_finite)
  qed
  text \<open>Step 3: rotate and translate to normalize diameter direction\<close>
  obtain g2 a2 b2 where g2: "rectifiable_path g2" "simple_path g2"
    "pathfinish g2 = pathstart g2" "pathstart g2 = a2"
    "convex (inside (path_image g2))"
    "path_length g2 = L"
    "b2 \<in> path_image g2" "dist a2 b2 = diameter (path_image g2)"
    "b2 - a2 = of_real (dist a2 b2)"
    "Re a2 = 0"
    "measure lebesgue (inside (path_image g2)) = measure lebesgue (inside (path_image g))"
    and sphere_back2: "\<And>c r. path_image g2 = sphere c r \<Longrightarrow>
      \<exists>c' r'. path_image g = sphere c' r'"
    using isoperimetric_reduce_rotate_translate g1 ab1 a_ne_b by (metis (no_types, lifting))
  text \<open>Step 4: arc-length reparametrization\<close>
  obtain g3 where g3: "rectifiable_path g3" "simple_path g3"
    "pathfinish g3 = pathstart g3" "pathstart g3 = pathstart g2"
    "convex (inside (path_image g3))"
    "path_length g3 = L"
    "path_image g3 = path_image g2"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g3) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g3 x) (g3 y) \<le> L * dist x y"
    using isoperimetric_reduce_arc_length[OF g2(1,2,3,5,6) Lpos] by metis
  have g3_facts: "b2 \<in> path_image g3" "dist (pathstart g3) b2 = diameter (path_image g3)"
    "b2 - pathstart g3 = of_real (dist (pathstart g3) b2)" "Re (pathstart g3) = 0"
    using g2 g3 by auto
  text \<open>Step 5: vertical translation for zero-mean imaginary part\<close>
  obtain h a' b' where h: "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h"
    "convex (inside (path_image h))"
    "path_length h = L"
    "a' \<in> path_image h" "b' \<in> path_image h"
    "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "pathstart h = a'" "pathfinish h = a'"
    "Re a' = 0"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    "(Im \<circ> h has_integral 0) {0..1}"
    and meas_eq5: "measure lebesgue (inside (path_image h)) =
      measure lebesgue (inside (path_image g3))"
    and sphere_back5: "\<And>c r. path_image h = sphere c r \<Longrightarrow>
      \<exists>c' r'. path_image g3 = sphere c' r'"
    using isoperimetric_reduce_zero_mean g3 g3_facts by blast
  have meas_eq: "measure lebesgue (inside (path_image g)) =
    measure lebesgue (inside (path_image h))"
    using meas_eq5 g3(5,7) g2(11) by simp
  have sphere_back: "\<And>c r. path_image h = sphere c r \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
    by (metis g3(7) sphere_back2 sphere_back5)
  text \<open>Step 6: apply the kernel lemma\<close>
  have kernel_hyps: "0 < L" "convex (inside (path_image h))"
    "a' \<in> path_image h" "b' \<in> path_image h"
    "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "pathstart h = a'" "pathfinish h = a'"
    "rectifiable_path h" "simple_path h"
    "path_length h = L"
    "Re a' = 0"
    "(Im \<circ> h has_integral 0) {0..1}"
    using Lpos h by auto
  have ineq_h: "measure lebesgue (inside (path_image h)) \<le> L\<^sup>2 / (4 * pi)"
    using h isoperimetric_kernel(1) kernel_hyps by blast
  show "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    using ineq_h meas_eq by simp
  show "\<exists>a r. path_image g = sphere a r"
    if "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi)"
    using that h isoperimetric_kernel simple_path_length_pos_lt sphere_back
    by (metis meas_eq)
qed

subsection \<open>Convexification\<close>

text \<open>A connected subset of a segment that contains both endpoints is the whole segment.
  (HOL Light: CONNECTED\_SUBSET\_SEGMENT.)\<close>

lemma connected_subset_segment:
  fixes a b :: "'a::euclidean_space"
  assumes "connected S" "S \<subseteq> closed_segment a b" "a \<in> S" "b \<in> S"
  shows "S = closed_segment a b"
proof (cases "a = b")
  case True
  then show ?thesis using assms by auto
next
  case False
  define f where "f = (\<lambda>x::'a. (b - a) \<bullet> x)"
  define K where "K = (b - a) \<bullet> (b - a)"
  have contf: "continuous_on S f" by (auto simp: f_def continuous_intros)
  have conn_fS: "connected (f ` S)" using assms(1) contf connected_continuous_image by blast
  have nz: "K > 0" using False by (simp add: K_def inner_gt_zero_iff)
  have fseg: "\<And>u. f ((1-u) *\<^sub>R a + u *\<^sub>R b) = (b - a) \<bullet> a + u * K"
    by (simp add: f_def K_def inner_diff_right algebra_simps inner_diff_left inner_commute)
  show ?thesis
  proof (intro subset_antisym assms)
    show "closed_segment a b \<subseteq> S"
    proof
      fix x assume "x \<in> closed_segment a b"
      then obtain u where u: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1"
        by (auto simp: in_segment)
      have fx: "f x = (b - a) \<bullet> a + u * K" using u(1) fseg by simp
      have mem: "f x \<in> closed_segment (f a) (f b)"
        unfolding closed_segment_eq_real_ivl using nz u(2,3) f_def fseg[of 1] fx
        by (auto simp: mult_left_le_one_le)
      have "closed_segment (f a) (f b) \<subseteq> f ` S"
        using conn_fS assms(3,4) connected_contains_Icc
        by (metis closed_segment_eq_real_ivl image_eqI)
      then obtain s where s: "s \<in> S" "f s = f x" "s \<in> closed_segment a b"
        using mem assms by (metis image_iff subsetD)
      then obtain v where v: "s = (1 - v) *\<^sub>R a + v *\<^sub>R b" "0 \<le> v" "v \<le> 1"
        by (auto simp: in_segment)
      have "(b - a) \<bullet> a + v * K = (b - a) \<bullet> a + u * K"
        using s(2) v(1) fseg fx by simp
      then show "x \<in> S" using nz s(1) v(1) u(1) by simp
    qed
  qed
qed

text \<open>A connected subset of two arcs joined only at their common endpoints, containing both
  endpoints, must contain one of the two arcs in full. (HOL Light: CONNECTED\_SUBSET\_ARC\_PAIR.)\<close>

lemma connected_subset_arc_pair:
  fixes g h :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc g" "arc h"
    "pathstart g = pathstart h" "pathfinish g = pathfinish h"
    and pai_eq: "path_image g \<inter> path_image h = {pathstart g, pathfinish g}"
    "connected S" and Ssub: "S \<subseteq> path_image g \<union> path_image h"
    and "pathstart g \<in> S" "pathfinish g \<in> S"
  shows "path_image g \<subseteq> S \<or> path_image h \<subseteq> S"
proof (rule ccontr)
  assume "\<not> (path_image g \<subseteq> S \<or> path_image h \<subseteq> S)"
  then have ng: "\<not> path_image g \<subseteq> S" and nh: "\<not> path_image h \<subseteq> S" by auto
  from ng obtain pg where pg: "pg \<in> path_image g" "pg \<notin> S" by blast
  then obtain p where p: "p \<in> {0..1}" "g p = pg" by (auto simp: path_image_def)
  from nh obtain ph where ph: "ph \<in> path_image h" "ph \<notin> S" by blast
  then obtain q where q: "q \<in> {0..1}" "h q = ph" by (auto simp: path_image_def)
  have gp: "g p \<notin> S" using p(2) pg(2) by simp
  have hq: "h q \<notin> S" using q(2) ph(2) by simp
  have pathg: "path g" and pathh: "path h" using assms(1,2) arc_imp_path by auto
  have img_g0p: "path_image (subpath 0 p g) = g ` {0..p}" using p(1) by (simp add: path_image_subpath)
  have img_gp1: "path_image (subpath p 1 g) = g ` {p..1}" using p(1) by (simp add: path_image_subpath)
  have img_h0q: "path_image (subpath 0 q h) = h ` {0..q}" using q(1) by (simp add: path_image_subpath)
  have img_hq1: "path_image (subpath q 1 h) = h ` {q..1}" using q(1) by (simp add: path_image_subpath)
  have comb_g: "g ` {0..p} \<union> g ` {p..1} = path_image g"
    using p(1) by (simp add: path_image_def image_Un [symmetric]) (metis ivl_disj_un_two_touch(4))
  have comb_h: "h ` {0..q} \<union> h ` {q..1} = path_image h"
    using q(1) by (simp add: path_image_def image_Un [symmetric]) (metis ivl_disj_un_two_touch(4))
  define E1 where "E1 = S - (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h))"
  define E2 where "E2 = S - (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h))"
  have openE1: "openin (top_of_set S) E1"
  proof -
    have "E1 = S \<inter> (- (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h)))"
      unfolding E1_def by blast
    moreover have "closed (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h))"
      using p q pathg pathh by (force intro: closed_path_image)
    ultimately show ?thesis by blast
  qed
  have openE2: "openin (top_of_set S) E2"
  proof -
    have "E2 = S \<inter> (- (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h)))"
      unfolding E2_def by blast
    moreover have "closed (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h))"
      using p q pathg pathh by (force intro: closed_path_image)
    ultimately show ?thesis by blast
  qed
  have injg: "inj_on g {0..1}" and injh: "inj_on h {0..1}" using assms by (simp_all add: arc_def)
  have "p > 0"
    using assms pg p by (force simp: pathstart_def)
  have "q > 0"
    using assms ph q by (force simp: pathstart_def)
  have "p < 1"
    using assms pg p by (force simp: pathfinish_def)
  have "q < 1"
    using assms ph q by (force simp: pathfinish_def)
  have ne_E1: "pathstart g \<in> E1"
  proof -
    have "g 0 \<notin> g ` {p..1}"
      using injg p(1) \<open>p > 0\<close> by (force simp: inj_on_def)
    moreover have "g 0 \<notin> h ` {q..1}"
      using injh q(1) \<open>q > 0\<close> assms(3) by (fastforce simp: pathstart_def inj_on_def)
    ultimately show ?thesis
      using \<open>pathstart g \<in> S\<close> img_gp1 img_hq1 by (simp add: E1_def pathstart_def)
  qed
  have ne_E2: "pathfinish g \<in> E2"
  proof -
    have "g 1 \<notin> g ` {0..p}"
      using injg \<open>p < 1\<close> p(1) by (force simp: inj_on_def)
    moreover have "g 1 \<notin> h ` {0..q}"
      by (smt (verit) arcD assms(2,4) atLeastAtMost_iff imageE pathfinish_def \<open>q < 1\<close>)
    ultimately show ?thesis
      using \<open>pathfinish g \<in> S\<close> img_g0p img_h0q by (simp add: E2_def pathfinish_def)
  qed
  have ps_g: "pathstart g = g 0" by (simp add: pathstart_def)
  have pf_g: "pathfinish g = g 1" by (simp add: pathfinish_def)
  have cross_gh: "g s = g 0 \<or> g s = g 1" 
    if "s \<in> {0..1}" "t \<in> {0..1}" "g s = h t" for s t
    using that pf_g ps_g assms(5) by (force simp: path_image_def)
  have gh11: "g 1 = h 1" using assms(4) by (simp add: pathfinish_def)
  have gh00: "g 0 = h 0" using assms(3) by (simp add: pathstart_def)
  have cover_False: False 
    if xS: "x \<in> S" and inR1: "x \<in> g ` {p..1} \<union> h ` {q..1}" and inR2: "x \<in> g ` {0..p} \<union> h ` {0..q}" for x 
  proof -
    from inR1 consider (g1) "x \<in> g ` {p..1}" | (h1) "x \<in> h ` {q..1}" by auto
    then show False
    proof cases
      case g1
      then obtain s where s: "s \<in> {p..1}" "x = g s" by auto
      from inR2 consider (a) "x \<in> g ` {0..p}" | (b) "x \<in> h ` {0..q}" by auto
      then show False
      proof cases
        case a
        then obtain t where t: "t \<in> {0..p}" "x = g t" by auto
        have "s = t" using injg s t p s(2) t(2) by (force simp: inj_on_def)
        then have "s = p" using s(1) t(1) by simp
        then show False using gp xS s(2) by simp
      next
        case b
        then obtain t where t: "t \<in> {0..q}" "x = h t" by auto
        have eq: "g s = h t" using s(2) t(2) by simp
        have "g s = g 0 \<or> g s = g 1" using cross_gh s(1) p q t(1) eq by (auto intro: order.trans)
        then show False
        proof
          assume "g s = g 0"
          then have "s = 0" using injg s(1) p by (force simp: inj_on_def)
          then show False using s(1) \<open>p > 0\<close> by simp
        next
          assume "g s = g 1"
          then have "t = 1" using eq gh11 injh t(1) q by (force simp: inj_on_def)
          then show False using t(1) \<open>q < 1\<close> by simp
        qed
      qed
    next
      case h1
      then obtain s where s: "s \<in> {q..1}" "x = h s" by auto
      from inR2 consider (a) "x \<in> g ` {0..p}" | (b) "x \<in> h ` {0..q}" by auto
      then show False
      proof cases
        case a
        then obtain t where t: "t \<in> {0..p}" "x = g t" by auto
        have eq: "g t = h s" using s(2) t(2) by simp
        have "g t = g 0 \<or> g t = g 1" using cross_gh t(1) p s(1) q eq by (auto intro: order.trans)
        then show False
        proof
          assume "g t = g 1"
          then have "t = 1" using injg t(1) p by (force simp: inj_on_def)
          then show False using t(1) \<open>p < 1\<close> by simp
        next
          assume "g t = g 0"
          then have "s = 0" using injh eq gh00 s(1) q by (force simp: inj_on_def)
          then show False using s(1) \<open>q > 0\<close> by simp
        qed
      next
        case b then show False
          using arcD assms(2) ph(2) q(2) s xS by fastforce
      qed
    qed
  qed
  have cover: "S \<subseteq> E1 \<union> E2"
    using arcD assms(1) gp cover_False
    unfolding E1_def E2_def img_gp1 img_hq1 img_g0p img_h0q by blast
  have "(g ` {p..1} \<union> h ` {q..1}) \<union> (g ` {0..p} \<union> h ` {0..q}) = path_image g \<union> path_image h"
    using comb_g comb_h by blast
  with assms(7)  have disjoint: "E1 \<inter> E2 = {}"
    unfolding E1_def E2_def img_gp1 img_hq1 img_g0p img_h0q by blast
  have "openin (top_of_set S) E1 \<and> openin (top_of_set S) E2 \<and> S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {}"
    using openE1 openE2 cover disjoint ne_E1 ne_E2 by auto
  with \<open>connected S\<close> show False
    using connected_openin by blast
qed

text \<open>If two frontier points of a bounded convex $2$-dimensional set are joined by a frontier arc whose
  interior (the arc minus the two points) stays connected and whose convex hull is the whole set,
  then the straight segment between the two points also lies on the frontier. The connectedness of
  the arc-minus-endpoints is what rules out the spurious ``chord through the interior'' case.\<close>

lemma seg_frontier_aux:
  fixes S :: "complex set"
  assumes cvx: "convex S" and cpt: "compact S" and intne: "interior S \<noteq> {}"
    and ga_fr: "ga \<in> frontier S" and gb_fr: "gb \<in> frontier S" and ne: "ga \<noteq> gb"
    and D1fr: "path_image D1 \<subseteq> frontier S"
    and D1con: "connected (path_image D1 - {ga, gb})"
    and gaD1: "ga \<in> path_image D1" and gbD1: "gb \<in> path_image D1"
    and hullD1: "convex hull (path_image D1) = S"
  shows "closed_segment ga gb \<subseteq> frontier S"
proof -
  have relfr: "rel_frontier S = frontier S" using intne by (rule rel_frontier_nonempty_interior)
  have ga_cl: "ga \<in> closure S" and gb_cl: "gb \<in> closure S"
    using ga_fr gb_fr by (auto simp: frontier_def)
  have dich: "open_segment ga gb \<subseteq> frontier S \<or> open_segment ga gb \<subseteq> interior S"
    using convex_open_segment_cases_alt[OF cvx ga_cl gb_cl] .
  define A where "A = \<i> * (gb - ga)"
  have A_nz: "A \<noteq> 0" using ne by (simp add: A_def)
  define e where "e = inner A ga"
  have eb: "inner A gb = e"
    by (auto simp: A_def inner_complex_def e_def algebra_simps)
  have opfr: "open_segment ga gb \<subseteq> frontier S"
  proof (rule ccontr)
    assume "\<not> open_segment ga gb \<subseteq> frontier S"
    then have segint: "open_segment ga gb \<subseteq> interior S" using dich by blast
    have mid_int: "midpoint ga gb \<in> interior S"
      using segint ne by (simp add: midpoint_in_open_segment subsetD)
    have mid_e: "inner A (midpoint ga gb) = e"
      using e_def eb by (simp add: midpoint_def inner_add_right inner_diff_right field_simps)
    have not_le: False if "path_image D1 \<subseteq> {x. inner A x \<le> e}"
    proof -
      have "S \<subseteq> {x. inner A x \<le> e}" 
        by (metis convex_halfspace_le hullD1 hull_minimal that)
      then have "inner A (midpoint ga gb) < e" using mid_int
        by (metis (mono_tags, lifting) A_nz interior_halfspace_le interior_mono 
            mem_Collect_eq subsetD)
      then show False using mid_e by simp
    qed
    have not_ge: False if "path_image D1 \<subseteq> {x. e \<le> inner A x}"
    proof -
      have "S \<subseteq> {x. e \<le> inner A x}"
        by (metis convex_halfspace_ge hullD1 hull_minimal that)
      then have "e < inner A (midpoint ga gb)" using mid_int
        by (metis A_nz interior_halfspace_ge interior_mono mem_Collect_eq subsetD)
      then show False using mid_e by simp
    qed
    from not_le obtain x1 where x1: "x1 \<in> path_image D1" "inner A x1 > e" by force
    from not_ge obtain x2 where x2: "x2 \<in> path_image D1" "inner A x2 < e" by force
    have x1ne: "x1 \<notin> {ga, gb}" using x1(2) e_def eb by auto
    have x2ne: "x2 \<notin> {ga, gb}" using x2(2) e_def eb by auto
    have x1D: "x1 \<in> path_image D1 - {ga,gb}" using x1(1) x1ne by simp
    have x2D: "x2 \<in> path_image D1 - {ga,gb}" using x2(1) x2ne by simp
    obtain w where w: "w \<in> path_image D1 - {ga,gb}" "inner A w = e"
      using connected_ivt_hyperplane[OF D1con x2D x1D, where a=A and b=e] x1(2) x2(2) by force
    have w_fr: "w \<in> rel_frontier S" using w(1) D1fr relfr by auto
    have ga_rf: "ga \<in> rel_frontier S" using ga_fr relfr by simp
    have gb_rf: "gb \<in> rel_frontier S" using gb_fr relfr by simp
    have wne: "w \<noteq> ga" "w \<noteq> gb" using w(1) by auto
    have triple: "S \<subseteq> {x. inner A x \<le> e} \<or> S \<subseteq> {x. e \<le> inner A x}"
      using assms(1,6) convex_triple_rel_frontier e_def eb ga_rf gb_rf w(2) w_fr wne(1,2) by blast
    have D1S: "path_image D1 \<subseteq> S"
      by (metis hullD1 hull_subset) 
    from triple show False
      using D1S local.not_le not_ge by blast
  qed
  have "{ga, gb} \<subseteq> frontier S" using ga_fr gb_fr by simp
  then show ?thesis using opfr by (simp add: closed_segment_eq_open)
qed

text \<open>The step lemma: replacing an arc that deviates from the convex hull frontier
  with a straight segment shortens the path while preserving the convex hull.\<close>

lemma step_lemma:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    and cont: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
    and "a < b"
    and ab01: "a \<in> {0..1}" "b \<in> {0..1}"
    and ga: "g a \<in> frontier (convex hull (path_image g))"
    and gb: "g b \<in> frontier (convex hull (path_image g))"
    and disj: "g ` {a<..<b} \<inter> frontier (convex hull (path_image g)) = {}"
  obtains h where "simple_path h"
    and "pathstart h = pathstart g" and "pathfinish h = pathstart g"
    and "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    and "path_length h < path_length g"
    and "convex hull (path_image h) = convex hull (path_image g)"
    and "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x"
    and "h ` {a..b} \<subseteq> frontier (convex hull (path_image g))"
proof (cases "box a b = {}")
  case True
  with \<open>a<b\<close> show ?thesis by auto
next
  case False
  have sub: "g ` {a<..<b} \<subseteq> convex hull (path_image g)"
    using ab01(1,2) hull_subset path_defs(4) by fastforce
  moreover have closed: "closed (convex hull (path_image g))"
    by (simp add: \<open>simple_path g\<close> compact_convex_hull compact_imp_closed compact_simple_path_image)
  ultimately
  have interior_subset: "g ` {a<..<b} \<subseteq> interior (convex hull (path_image g))"
    using disj frontier_def by fastforce
  have interior_ne: "interior (convex hull (path_image g)) \<noteq> {}"
    using interior_subset \<open>a<b\<close> by fastforce
  show ?thesis
  proof (cases "g a = g b")
    case True
    have ab_eq: "a = 0" "b = 1"
      using True \<open>simple_path g\<close> ab01  \<open>a < b\<close>
      by (force simp: simple_path_def loop_free_def)+
    have g01: "g 0 = g 1"
      using assms(2) by (simp add: pathfinish_def pathstart_def)
    have pi_eq: "path_image g = {g 0} \<union> g ` {0<..<1}"
      using g01 by (fastforce simp: path_image_def image_iff)
    have int_sub: "g ` {0<..<1} \<subseteq> interior (convex hull (path_image g))"
      using interior_subset ab_eq by simp
        \<comment> \<open>Every extreme point of the convex hull lies in @{term "path_image g"} but not in the interior\<close>
    have ext_sub: "{x. x extreme_point_of (convex hull (path_image g))} \<subseteq> {g 0}"
      using extreme_point_of_convex_hull extreme_point_not_in_interior int_sub by (fastforce simp: pi_eq)
        \<comment> \<open>By Krein--Milman, the convex hull collapses to a single point\<close>
    have compact_hull: "compact (convex hull (path_image g))"
      by (rule compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]])
    have "convex hull (path_image g) = convex hull {x. x extreme_point_of (convex hull (path_image g))}"
      using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull] by simp
    also have "\<dots> \<subseteq> convex hull {g 0}"
      using ext_sub by (intro hull_mono)
    also have "\<dots> = {g 0}" by (simp add: convex_hull_singleton)
    finally have "convex hull (path_image g) \<subseteq> {g 0}" .
    with interior_ne show ?thesis
      by (simp add: subset_singleton_iff)
  next
    case False
    have hull_eq: "convex hull (g ` ({0..1} - {a<..<b})) = convex hull (path_image g)"
    proof
      show "convex hull (g ` ({0..1} - {a<..<b})) \<subseteq> convex hull (path_image g)"
        by (intro hull_mono image_mono) (auto simp: path_image_def)
          \<comment> \<open>For $\supseteq$, use extreme points: they lie in @{term "path_image g"} but not in the interior\<close>
      have compact_hull: "compact (convex hull (path_image g))"
        by (rule compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]])
      have ext_in_rest: "{x. x extreme_point_of (convex hull (path_image g))} \<subseteq> g ` ({0..1} - {a<..<b})"
        using extreme_point_of_convex_hull extreme_point_not_in_interior interior_subset
        unfolding path_image_def by blast
      show "convex hull (path_image g) \<subseteq> convex hull (g ` ({0..1} - {a<..<b}))"
        using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull]
        using ext_in_rest hull_mono by blast
    qed
    have hull_seg_eq: "convex hull (closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})) = convex hull (path_image g)"
    proof
      have "g a \<in> g ` ({0..1} - {a<..<b})" "g b \<in> g ` ({0..1} - {a<..<b})"
        using ab01 \<open>a < b\<close> by auto
      then have seg_sub: "closed_segment (g a) (g b) \<subseteq> convex hull (g ` ({0..1} - {a<..<b}))"
        by (meson closed_segment_subset convex_convex_hull hull_inc)
      show "convex hull (closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})) \<subseteq> convex hull (path_image g)"
        by (metis hull_eq convex_convex_hull hull_subset le_supI seg_sub subset_hull)
      show "convex hull (path_image g) \<subseteq> convex hull (closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b}))"
        by (metis Un_commute Un_upper1 hull_eq hull_mono)
    qed
  \<comment> \<open>Step 1: double arc decomposition of @{term g}\<close>
    obtain g0 g1 where arcs:
      "arc g0" "arc g1"
      "pathstart g0 = g a" "pathfinish g0 = g b"
      "pathstart g1 = g b" "pathfinish g1 = g a"
      "path_image g0 = g ` {a..b}"
      "path_image g1 = g ` ({0..1} - {a<..<b})"
      "(path_image g0) \<inter> (path_image g1) = {g a, g b}"
      "(path_image g0) \<union> (path_image g1) = path_image g"
      using exists_double_arc_explicit[OF \<open>simple_path g\<close> \<open>pathfinish g = pathstart g\<close>
          ab01(1) ab01(2) less_imp_le[OF \<open>a < b\<close>] False] by blast

    \<comment> \<open>Step 2: the frontier of the convex hull admits a rectifiable simple loop parametrization
       (this corresponds to HOL Light's \<open>RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX\<close>)\<close>
    obtain d where d_props:
      "simple_path d" "pathfinish d = pathstart d" "rectifiable_path d"
      "path_image d = frontier (convex hull (path_image g))"
      by (metis assms(1) bounded_convex_hull bounded_simple_path_image convex_convex_hull interior_ne
          rectifiable_loop_frontier_convex)

\<comment> \<open>Step 4: double arc decomposition of the frontier loop @{term d}, with inside decomposition\<close>
    have ga_ne_gb: "g a \<noteq> g b" using False .
    obtain d0 d1 where d_split:
      "arc d0" "arc d1"
      "pathstart d0 = g a" "pathfinish d0 = g b"
      "pathstart d1 = g b" "pathfinish d1 = g a"
      "path_image d0 \<inter> path_image d1 = {g a, g b}"
      "path_image d0 \<union> path_image d1 = path_image d"
      "inside (path_image d0 \<union> path_image g0) \<inter> inside (path_image d1 \<union> path_image g0) = {}"
      "inside (path_image d0 \<union> path_image g0) \<union> inside (path_image d1 \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) =
       interior (convex hull (path_image g))"
      "(path_image g1 - {g b, g a}) \<inter> path_image d0 = {}"
    proof -
      have ga_d: "g a \<in> path_image d" and gb_d: "g b \<in> path_image d"
        using d_props(4) assms(7,8) by simp_all
      obtain d0 d1 where da:
        "arc d0" "arc d1"
        "pathstart d0 = g a" "pathfinish d0 = g b"
        "pathstart d1 = g b" "pathfinish d1 = g a"
        "path_image d0 \<inter> path_image d1 = {g a, g b}"
        "path_image d0 \<union> path_image d1 = path_image d"
        using exists_double_arc[OF d_props(1) d_props(2) ga_d gb_d ga_ne_gb] by metis
      \<comment> \<open>Endpoints and basic simple-path facts for the frontier arcs @{term d0}, @{term d1}\<close>
      have sp_d0: "simple_path d0" and sp_d1: "simple_path d1"
        using da(1,2) arc_imp_simple_path by blast+
      have rev_ends: "pathstart (reversepath d1) = g a" "pathfinish (reversepath d1) = g b"
        using da(5,6) by (simp_all add: pathstart_reversepath pathfinish_reversepath)
      have sp_rev_d1: "simple_path (reversepath d1)"
        using sp_d1 by (simp add: simple_path_reversepath)
      have sp_g0: "simple_path g0" using arcs(1) arc_imp_simple_path by blast
      note g0_ends = arcs(3,4)
      have gab_d1: "g a \<in> path_image d1" "g b \<in> path_image d1"
        using da(5,6) by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have d0_sub: "path_image d0 \<subseteq> path_image d" and d1_sub: "path_image d1 \<subseteq> path_image d"
        using da(8) by blast+
      \<comment> \<open>The open part of @{term g0} lies in the interior, hence @{term g0} meets the frontier only at $g\,a$, $g\,b$\<close>
      have g0_decomp: "path_image g0 = g ` {a<..<b} \<union> {g a, g b}"
        using \<open>a < b\<close> by (force simp:  arcs(7) image_iff)
      have g0_d_int: "path_image g0 \<inter> path_image d = {g a, g b}"
        using assms(9) d_props(4) ga_d gb_d g0_decomp by auto
      have d0_g0_int: "path_image d0 \<inter> path_image g0 = {g a, g b}"
        using da(7,8) g0_d_int by auto
      have d1_g0_int: "path_image d1 \<inter> path_image g0 = {g a, g b}"
        using d1_sub da(7) g0_d_int by auto
      \<comment> \<open>Split the inside via \<open>SPLIT_INSIDE_SIMPLE_CLOSED_CURVE\<close> on @{term d0}, @{term "reversepath d1"}, @{term g0}\<close>
      have inside_eq: "inside (path_image d0 \<union> path_image (reversepath d1)) = interior (convex hull path_image g)"
        by (simp add: assms(1) bounded_convex_hull bounded_simple_path_image d_props(4) da(8)
            inside_frontier_eq_interior)
      have "g ` {a<..<b} \<noteq> {}"
        using \<open>a < b\<close> by auto
      then have g0_inside_ne: "path_image g0 \<inter> inside (path_image d0 \<union> path_image (reversepath d1)) \<noteq> {}"
        using \<open>a < b\<close> g0_decomp interior_subset inside_eq by blast
      have d0_rev_int: "path_image d0 \<inter> path_image (reversepath d1) = {g a, g b}"
        using da(7) path_image_reversepath by simp
      have split:
        "inside (path_image d0 \<union> path_image g0) \<inter> inside (path_image (reversepath d1) \<union> path_image g0) = {}"
        "inside (path_image d0 \<union> path_image g0) \<union> inside (path_image (reversepath d1) \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) = inside (path_image d0 \<union> path_image (reversepath d1))"
        using split_inside_simple_closed_curve[OF sp_d0 da(3,4) sp_rev_d1 rev_ends sp_g0 g0_ends ga_ne_gb
            d0_rev_int d0_g0_int _ g0_inside_ne]
        by (simp_all add: path_image_reversepath d1_g0_int)
      have split1: "inside (path_image d0 \<union> path_image g0) \<inter> inside (path_image d1 \<union> path_image g0) = {}"
        using split(1) path_image_reversepath by simp
      have split2: "inside (path_image d0 \<union> path_image g0) \<union> inside (path_image d1 \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) = interior (convex hull path_image g)"
        using split(2) path_image_reversepath inside_eq by simp
      \<comment> \<open>Step 4 (cont.): orient the split so that @{term g1}'s interior avoids @{term d0}.
          This is a connectedness argument on @{term "path_image g1 - {g a, g b}"}.\<close>
      have arc_rev_g0: "arc (reversepath g0)" using arcs(1) by (simp add: arc_reversepath)
      have J0_loop: "simple_path (d0 +++ reversepath g0)"
      proof (intro simple_path_join_loop da arc_rev_g0)
      qed (use da g0_ends d0_g0_int in auto)
      have J0_close: "pathfinish (d0 +++ reversepath g0) = pathstart (d0 +++ reversepath g0)"
        using da(3) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
      have J0_pi: "path_image (d0 +++ reversepath g0) = path_image d0 \<union> path_image g0"
        using da(4) g0_ends by (simp add: path_image_join pathstart_reversepath path_image_reversepath)
      have J1_loop: "simple_path (reversepath d1 +++ reversepath g0)"
      proof (intro simple_path_join_loop arc_rev_g0)
        show "arc (reversepath d1)" using da(2) by (simp add: arc_reversepath)
      qed (use da g0_ends d1_g0_int in auto)
      have J1_close: "pathfinish (reversepath d1 +++ reversepath g0) = pathstart (reversepath d1 +++ reversepath g0)"
        using da(6) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
      have J1_pi: "path_image (reversepath d1 +++ reversepath g0) = path_image d1 \<union> path_image g0"
        using da(5) g0_ends by (simp add: path_image_join pathstart_reversepath pathfinish_reversepath path_image_reversepath)
      have J0_jio: "frontier (inside (path_image d0 \<union> path_image g0)) = path_image d0 \<union> path_image g0"
        using Jordan_inside_outside[OF J0_loop J0_close] J0_pi by simp
      have J1_jio: "frontier (inside (path_image d1 \<union> path_image g0)) = path_image d1 \<union> path_image g0"
        using Jordan_inside_outside[OF J1_loop J1_close] J1_pi by simp
      have cl_J0: "closure (inside (path_image d0 \<union> path_image g0)) = inside (path_image d0 \<union> path_image g0) \<union> path_image d0 \<union> path_image g0"
        by (simp add: J0_jio Un_ac(1) closure_Un_frontier)
      have cl_J1: "closure (inside (path_image d1 \<union> path_image g0)) = inside (path_image d1 \<union> path_image g0) \<union> path_image d1 \<union> path_image g0"
        by (simp add: J1_jio Un_assoc closure_Un_frontier)
      have sp_g1: "simple_path g1" using arcs(2) arc_imp_simple_path by blast
      define S where "S = path_image g1 - {g b, g a}"
      have S_conn: "connected S"
        using connected_simple_path_endless[OF sp_g1] arcs(5,6) unfolding S_def
        by (simp add: insert_commute)
      have g1_g0_int: "path_image g1 \<inter> path_image g0 = {g a, g b}"
        using arcs(9) by (simp add: Int_commute)
      have S_g0: "S \<inter> path_image g0 = {}"
        using g1_g0_int unfolding S_def by blast
      have cldd0: "closed (path_image d0 \<union> path_image g0)"
        using da(1) arcs(1) by (simp add: closed_path_image arc_imp_path closed_Un)
      have cldd1: "closed (path_image d1 \<union> path_image g0)"
        using da(2) arcs(1) by (simp add: closed_path_image arc_imp_path closed_Un)
      have g1_in_hull: "path_image g1 \<subseteq> convex hull path_image g"
        by (metis arcs(8) hull_subset local.hull_eq)
      have hull_closed: "closed (convex hull path_image g)"
        by (simp add: compact_imp_closed compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
      have g1_cover: "path_image g1 \<subseteq> interior (convex hull path_image g) \<union> frontier (convex hull path_image g)"
        using g1_in_hull hull_closed by (simp add: frontier_def closure_closed) blast
      \<comment> \<open>@{term S} (which is @{term g1} minus its endpoints) is covered by the two \<open>inside\<close>-plus-arc regions ...\<close>
      have cover: "\<And>z. z \<in> S \<Longrightarrow> z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<union> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
        using IntE IntI S_def S_g0 Un_iff d_props(4) da(8) g1_cover split2 by fastforce
      have ic0: "inside (path_image d1 \<union> path_image g0) \<inter> closure (inside (path_image d0 \<union> path_image g0)) = {}"
        using open_Int_closure_eq_empty cldd1 split1 by (metis Int_commute open_inside)
      have ic1: "inside (path_image d0 \<union> path_image g0) \<inter> closure (inside (path_image d1 \<union> path_image g0)) = {}"
        using open_Int_closure_eq_empty cldd0 split1 by (metis open_inside)
      have d0_cl: "path_image d0 \<subseteq> closure (inside (path_image d0 \<union> path_image g0))"
        using cl_J0 by blast
      have d1_cl: "path_image d1 \<subseteq> closure (inside (path_image d1 \<union> path_image g0))"
        using cl_J1 by blast
      have in1_d0: "inside (path_image d1 \<union> path_image g0) \<inter> path_image d0 = {}"
        using ic0 d0_cl by blast
      have d1_in0: "path_image d1 \<inter> inside (path_image d0 \<union> path_image g0) = {}"
        using ic1 d1_cl by blast
      have in1_in0: "inside (path_image d1 \<union> path_image g0) \<inter> inside (path_image d0 \<union> path_image g0) = {}"
        using split1 by (simp add: Int_commute)
      have d1_d0_S: "\<And>z. z \<in> S \<Longrightarrow> \<not>(z \<in> path_image d1 \<and> z \<in> path_image d0)"
        using da(7) unfolding S_def by blast
      \<comment> \<open>... and the two regions are disjoint on @{term S}, so @{term S} splits into two relatively clopen pieces\<close>
      have disj: "\<And>z. z \<in> S \<Longrightarrow> \<not>(z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<and> z \<in> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0)))"
        using in1_d0 in1_in0 d1_in0 d1_d0_S by blast
      have eqA: "S - closure (inside (path_image d1 \<union> path_image g0)) = S \<inter> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
        using cl_J1 S_g0 cover disj by blast
      have eqB: "S - closure (inside (path_image d0 \<union> path_image g0)) = S \<inter> (path_image d1 \<union> inside (path_image d1 \<union> path_image g0))"
        using cl_J0 S_g0 cover disj by blast
      have opA: "openin (top_of_set S) (S - closure (inside (path_image d1 \<union> path_image g0)))"
        by (simp add: Diff_eq open_Compl openin_open_Int)
      have opB: "openin (top_of_set S) (S - closure (inside (path_image d0 \<union> path_image g0)))"
        by (metis Diff_eq interior_complement open_interior openin_open_Int)
      have AB_cover: "(S - closure (inside (path_image d1 \<union> path_image g0))) \<union> (S - closure (inside (path_image d0 \<union> path_image g0))) = S"
        using eqA eqB cover by blast
      have AB_disj: "(S - closure (inside (path_image d1 \<union> path_image g0))) \<inter> (S - closure (inside (path_image d0 \<union> path_image g0))) = {}"
        using eqA eqB in1_d0 in1_in0 d1_in0 d1_d0_S split1 by auto
      have one_empty: "(S - closure (inside (path_image d1 \<union> path_image g0))) = {} \<or> (S - closure (inside (path_image d0 \<union> path_image g0))) = {}"
        using S_conn opA opB AB_cover AB_disj connected_openin by blast
      have disjunction: "S \<inter> path_image d0 = {} \<or> S \<inter> path_image d1 = {}"
        using eqA eqB one_empty by auto
          \<comment> \<open>Whichever arc @{term S} avoids becomes @{term d0} (reversing the pair in the second case)\<close>
      show thesis
      proof (cases "S \<inter> path_image d0 = {}")
        case True then show thesis
          using S_def da split1 split2 that by auto
      next
        case False
        then have d1e: "(path_image g1 - {g b, g a}) \<inter> path_image d1 = {}"
          using disjunction unfolding S_def by blast
        then show thesis
          using da arc_reversepath pathstart_reversepath pathfinish_reversepath
          by (metis (no_types, lifting) Int_commute path_image_reversepath split1 split2 sup_commute
              that)
      qed
    qed
    \<comment> \<open>Step 3: $g(a)$ and $g(b)$ are on the @{term "path_image d"}\<close>
    have ga_in_d: "g a \<in> path_image d" and gb_in_d: "g b \<in> path_image d"
      using d_props(4) assms(7,8) by auto
    \<comment> \<open>Step 4: build @{term h} as the straight segment from $g(a)$ to $g(b)$ on $(a,b)$, unchanged elsewhere.
       (\<open>front_arc\<close> is no longer used; see \<open>step_lemma_proof_body.thy\<close> in memory for derivation notes.)\<close>
    show ?thesis
    proof -
      have hull_closed: "closed (convex hull path_image g)"
        by (simp add: compact_imp_closed compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
      have compact_hull: "compact (convex hull path_image g)"
        by (simp add: compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
      have d1_sub_hull: "convex hull (path_image d1) \<subseteq> convex hull (path_image g)"
        using d_props(4) d_split(8) frontier_subset_eq hull_closed
        by (intro hull_minimal) auto
      have km_ext: "convex hull path_image g = convex hull {x. x extreme_point_of (convex hull path_image g)}"
        using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull] by simp
      have test_cl: "\<And>x. x \<in> path_image g \<Longrightarrow> x \<in> closure (convex hull path_image g)"
        using closure_subset hull_subset by (meson subset_iff)
      have test_front: "\<And>x. x \<in> closure (convex hull path_image g) \<Longrightarrow> x \<notin> interior (convex hull path_image g) \<Longrightarrow> x \<in> frontier (convex hull path_image g)"
        by (simp add: frontier_def)
      have ext_in_g_front: "\<And>x. x extreme_point_of (convex hull path_image g) \<Longrightarrow> x \<in> path_image g \<inter> path_image d"
        by (simp add: d_props(4) extreme_point_not_in_interior extreme_point_of_convex_hull test_cl
            test_front)
      have gab_d1: "g a \<in> path_image d1" "g b \<in> path_image d1"
        using d_split(5,6) by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have g0_int_d: "path_image g0 \<inter> path_image d = {g a, g b}"
      proof -
        have "{a..b} = {a<..<b} \<union> {a, b}" using \<open>a < b\<close> by auto
        then have "path_image g0 = g ` {a<..<b} \<union> {g a, g b}"
          using arcs by simp
        moreover have "{g a, g b} \<subseteq> path_image d" using ga_in_d gb_in_d by simp
        ultimately show ?thesis
          using assms(9) d_props(4) by blast
      qed
      have g1_int_d: "path_image g1 \<inter> path_image d \<subseteq> path_image d1"
        using d_split by auto
      have hull_d1_eq: "convex hull (path_image d1) = convex hull (path_image g)"
      proof (intro d1_sub_hull subset_antisym)
        have "path_image g \<inter> path_image d \<subseteq> path_image d1"
        proof -
          have "path_image g \<inter> path_image d = (path_image g0 \<inter> path_image d) \<union> (path_image g1 \<inter> path_image d)"
            using arcs(10) by blast
          also have "\<dots> \<subseteq> path_image d1" using g0_int_d g1_int_d gab_d1 by simp
          finally show ?thesis .
        qed
        then have "{x. x extreme_point_of (convex hull path_image g)} \<subseteq> path_image d1"
          using ext_in_g_front by blast
        then have "convex hull {x. x extreme_point_of (convex hull path_image g)} \<subseteq> convex hull (path_image d1)"
          by (rule hull_mono)
        then show "convex hull (path_image g) \<subseteq> convex hull (path_image d1)" using km_ext by simp
      qed
      \<comment> \<open>The straight segment between $g(a)$ and $g(b)$ lies on the frontier, via \<open>seg_frontier_aux\<close>
         applied to the arc @{term d1} (whose hull is the whole convex hull by \<open>hull_d1_eq\<close>).\<close>
      have seg_in_frontier: "closed_segment (g a) (g b) \<subseteq> frontier (convex hull path_image g)"
      proof (rule seg_frontier_aux[of _ _ _ d1])
        show "path_image d1 \<subseteq> frontier (convex hull path_image g)"
          using d_split(8) d_props(4) by blast
        show "connected (path_image d1 - {g a, g b})"
          using connected_simple_path_endless[OF arc_imp_simple_path[OF d_split(2)]] d_split(5,6)
          by (simp add: insert_commute)
        show "convex hull path_image d1 = convex hull path_image g" by (rule hull_d1_eq)
      qed (use assms gab_d1 ga_ne_gb convex_convex_hull compact_hull interior_ne in auto)
      have rev_d1_arc: "arc (reversepath d1)" using d_split(2) by (simp add: arc_reversepath)
      have rev_d1_start: "pathstart (reversepath d1) = g a" using d_split(6) by (simp add: pathstart_reversepath)
      have rev_d1_finish: "pathfinish (reversepath d1) = g b" using d_split(5) by (simp add: pathfinish_reversepath)
      have rev_d1_pi: "path_image (reversepath d1) = path_image d1" by (simp add: path_image_reversepath)
      have d0d1_pi: "path_image d0 \<union> path_image (reversepath d1) = frontier (convex hull path_image g)"
        using rev_d1_pi d_split(8) d_props(4) by simp
      have int_ends: "path_image d0 \<inter> path_image (reversepath d1) = {pathstart d0, pathfinish d0}"
        using d_split(7) rev_d1_pi d_split(3,4) by simp
      have seg_sub_union: "closed_segment (g a) (g b) \<subseteq> path_image d0 \<union> path_image (reversepath d1)"
        using seg_in_frontier d0d1_pi by simp
      have dich: "path_image d0 \<subseteq> closed_segment (g a) (g b) \<or> path_image (reversepath d1) \<subseteq> closed_segment (g a) (g b)"
      proof (rule connected_subset_arc_pair)
        show "arc d0" by (rule d_split(1))
        show "arc (reversepath d1)" by (rule rev_d1_arc)
        show "pathstart d0 = pathstart (reversepath d1)" using d_split(3) rev_d1_start by simp
        show "pathfinish d0 = pathfinish (reversepath d1)" using d_split(4) rev_d1_finish by simp
        show "path_image d0 \<inter> path_image (reversepath d1) = {pathstart d0, pathfinish d0}" by (rule int_ends)
        show "connected (closed_segment (g a) (g b))" by simp
        show "closed_segment (g a) (g b) \<subseteq> path_image d0 \<union> path_image (reversepath d1)" by (rule seg_sub_union)
        show "pathstart d0 \<in> closed_segment (g a) (g b)" using d_split(3) by simp
        show "pathfinish d0 \<in> closed_segment (g a) (g b)" using d_split(4) by simp
      qed
      have False if "path_image (reversepath d1) \<subseteq> closed_segment (g a) (g b)"
      proof -
        have "convex hull (path_image d1) \<subseteq> convex hull (closed_segment (g a) (g b))"
          using that by (simp add: hull_mono)
        also have "\<dots> = closed_segment (g a) (g b)"
          by (simp add: hull_mono hull_same convex_closed_segment)
        finally have "interior (convex hull (path_image g)) \<subseteq> interior (closed_segment (g a) (g b))"
          by (simp add: hull_d1_eq interior_mono)
        also have "interior (closed_segment (g a) (g b)) = {}"
          by (rule interior_closed_segment_ge2) simp
        finally show False using interior_ne by simp
      qed
      with dich have d0_sub_seg: "path_image d0 \<subseteq> closed_segment (g a) (g b)"
        by blast
      have d0_eq_seg: "path_image d0 = closed_segment (g a) (g b)"
      proof (rule connected_subset_segment)
        show "connected (path_image d0)" using d_split(1) by (simp add: connected_arc_image)
        show "path_image d0 \<subseteq> closed_segment (g a) (g b)" by (rule d0_sub_seg)
        show "g a \<in> path_image d0" using gab_d1 d_split(3) by (metis pathstart_in_path_image)
        show "g b \<in> path_image d0" using d_split(4) by (metis pathfinish_in_path_image)
      qed
      define h where "h \<equiv> \<lambda>t. if t \<in> {a<..<b} then g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a) else g t"
      have interval_img: "(\<lambda>t. (t - a)/(b - a)) ` {a..b} = {0..1}"
      proof -
        have "(\<lambda>t. (t - a)/(b - a)) ` {a..b} = {a/(b-a) - a/(b-a) .. b/(b-a) - a/(b-a)}"
          using \<open>a < b\<close> by (simp add: diff_divide_distrib image_affinity_atLeastAtMost_div_diff)
        also have "\<dots> = {0..1}" using \<open>a < b\<close> by (simp flip: diff_divide_distrib)
        finally show ?thesis .
      qed
      have lin: "(\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b} = closed_segment (g a) (g b)"
      proof -
        have "(\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b}
            = (\<lambda>u. g a + u *\<^sub>R (g b - g a)) ` ((\<lambda>t. (t-a)/(b-a)) ` {a..b})"
          by (simp add: image_image)
        also have "\<dots> = closed_segment (g a) (g b)"
          using interval_img by (simp add: closed_segment_image_interval algebra_simps cong: image_cong)
        finally show ?thesis .
      qed
      have hh_eq_lin: "\<And>t. t \<in> {a..b} \<Longrightarrow> h t = g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)"
        using h_def by fastforce
      have hh_seg: "h ` {a..b} = closed_segment (g a) (g b)"
        by (simp add: hh_eq_lin lin)
      have a_ge0: "0 \<le> a" and b_le1: "b \<le> 1" using ab01 by auto
      have hh_0: "h 0 = g 0" using a_ge0 by (simp add: h_def)
      have hh_1: "h 1 = g 1" using b_le1 by (simp add: h_def)
      have hh_start: "pathstart h = pathstart g" by (simp add: pathstart_def hh_0)
      have hh_finish: "pathfinish h = pathstart g"
        using assms(2) by (simp add: pathstart_def pathfinish_def hh_1)
      have hh_frontier: "h ` {a..b} \<subseteq> frontier (convex hull path_image g)"
        using hh_seg seg_in_frontier by simp
      have hh_out_img: "h ` ({0..1} - {a<..<b}) = g ` ({0..1} - {a<..<b})"
        using h_def by auto
      have "{0..1} = {a..b} \<union> ({0..1} - {a<..<b})"
        using ab01 \<open>a < b\<close> by auto
      then have pi_h: "path_image h = closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})"
        by (metis hh_out_img hh_seg image_Un path_image_def)
      have front_in_hull: "frontier (convex hull path_image g) \<subseteq> convex hull path_image g"
        using hull_closed by (simp add: frontier_def closure_closed)
      have hull_hh: "convex hull (path_image h) = convex hull (path_image g)"
        using hull_seg_eq pi_h by argo
      have "dist (g a) (g b) \<le> L * dist a b" using assms(3) ab01 by blast
      then have L_nonneg: "0 \<le> L"
        by (smt (verit) False dist_le_zero_iff zero_le_mult_iff)
      have dab: "dist (g a) (g b) \<le> L * (b - a)"
        by (smt (verit) assms dist_real_def)
      have lip_mid: "L-lipschitz_on {a..b} h"
      proof (rule lipschitz_onI)
        show "0 \<le> L" by (rule L_nonneg)
        fix x y assume x: "x \<in> {a..b}" and y: "y \<in> {a..b}"
        have factor: "h x - h y = ((x - a)/(b - a) - (y - a)/(b - a)) *\<^sub>R (g b - g a)"
          by (simp add: hh_eq_lin[OF x] hh_eq_lin[OF y] scaleR_left_diff_distrib)
        have e1: "dist (h x) (h y) = \<bar>(x - a)/(b - a) - (y - a)/(b - a)\<bar> * norm (g b - g a)"
          by (simp add: dist_norm factor)
        have e2: "\<bar>(x - a)/(b - a) - (y - a)/(b - a)\<bar> = \<bar>x - y\<bar> / (b - a)"
          using \<open>a < b\<close> by (simp add: divide_simps)
        have e3: "norm (g b - g a) / (b - a) \<le> L"
          by (metis \<open>a < b\<close> dab diff_gt_0_iff_gt dist_commute dist_norm mult_imp_div_pos_le)
        have "dist (h x) (h y) = (norm (g b - g a) / (b - a)) * \<bar>x - y\<bar>"
          using e1 e2 by simp
        also have "\<dots> \<le> L * \<bar>x - y\<bar>"
          using mult_right_mono[OF e3 abs_ge_zero] by simp
        finally show "dist (h x) (h y) \<le> L * dist x y" by (simp add: dist_real_def)
      qed
      have lip_g: "L-lipschitz_on {0..1} g"
        by (rule lipschitz_onI[OF _ L_nonneg]) (rule assms(3))
      have hh_lo: "\<And>x. x \<in> {0..a} \<Longrightarrow> h x = g x"
        by (auto simp: h_def)
      have hh_hi: "\<And>x. x \<in> {b..1} \<Longrightarrow> h x = g x"
        using \<open>a < b\<close> by (auto simp: h_def)
      have lip_lo: "L-lipschitz_on {0..a} h"
        by (smt (verit, ccfv_threshold) ab01(1) atLeastAtMost_iff hh_lo lip_g lipschitz_on_def)
      have lip_hi: "L-lipschitz_on {b..1} h"
        by (smt (verit) ab01(2) atLeastAtMost_iff hh_hi lip_g lipschitz_on_def)
      have lip_lomid: "L-lipschitz_on {0..b} h"
        using lip_lo lip_mid lipschitz_on_concat_max by fastforce
      have lip_hh: "L-lipschitz_on {0..1} h"
        by (smt (verit, ccfv_SIG) lip_hi lip_lomid lipschitz_on_concat lipschitz_on_cong)
      have path_hh: "path h"
        using lip_hh by (simp add: path_def lipschitz_on_continuous_on)
      have g1_img: "g ` ({0..1} - {a<..<b}) = path_image g1" using arcs(8) by simp
      have opse_g1_disj: "open_segment (g a) (g b) \<inter> path_image g1 = {}"
        by (metis Int_Diff Int_commute d0_eq_seg d_split(11) insert_commute open_segment_def)
      have hh_in_opse: "h x \<in> open_segment (g a) (g b)" if "x \<in> {a<..<b}" for x
      proof -
        have "(x - a)/(b - a) \<in> {0<..<1}"
          using that \<open>a < b\<close> by (auto simp: divide_simps)
        then have "g a + ((x-a)/(b-a)) *\<^sub>R (g b - g a) \<in> open_segment (g a) (g b)"
          using ga_ne_gb by (auto simp: in_segment algebra_simps)
        then show "h x \<in> open_segment (g a) (g b)" using that by (simp add: h_def)
      qed
      have hh_inj_mid: "x = y"
        if "x \<in> {a<..<b}" "y \<in> {a<..<b}"  "h x = h y" for x y
        using that False by (simp add: h_def)
      have g_loop_free: "loop_free g" using assms(1) by (simp add: simple_path_def)
      have hh_out_g: "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x" unfolding h_def by presburger
      have hh_out_in_g1: "\<And>x. x \<in> {0..1} \<Longrightarrow> x \<notin> {a<..<b} \<Longrightarrow> h x \<in> path_image g1"
        using hh_out_g g1_img by blast
      have gloopD: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> g x = g y \<Longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
        using g_loop_free unfolding loop_free_def by blast
      have testM1: "\<And>x y. x \<in> {a<..<b} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> y \<notin> {a<..<b} \<Longrightarrow> h x = h y \<Longrightarrow> False"
        by (metis disjoint_iff hh_in_opse hh_out_in_g1 opse_g1_disj)
      have loopfree_hh: "loop_free h"
        unfolding loop_free_def
        by (metis gloopD h_def hh_inj_mid testM1)
      have simple_hh: "simple_path h"
        using path_hh loopfree_hh by (simp add: simple_path_def)
      have lip_imp_bv: "has_bounded_variation_on f {c..d}"
        if lip: "M-lipschitz_on {c..d} f" for f :: "real \<Rightarrow> complex" and M c d
      proof -
        show "has_bounded_variation_on f {c..d}"
          unfolding has_bounded_variation_on_interval
        proof (intro exI[where x="max 0 (M * (d - c))"] allI impI)
          fix D assume D: "D division_of {c..d}"
          have Mnn: "0 \<le> M" using lip by (simp add: lipschitz_on_nonneg)
          have elem: "norm (f (Sup k) - f (Inf k)) \<le> M * content k" if k: "k \<in> D" for k
          proof -
            obtain a' b' where ab': "k = cbox a' b'" and ksub: "k \<subseteq> {c..d}" and kne: "k \<noteq> {}" 
              using division_ofD D k by metis
            then have leab: "a' \<le> b'" using ab' by (simp add: box_ne_empty)
            have infk: "Inf k = a'" and supk: "Sup k = b'" using ab' leab by auto
            have "norm (f b' - f a') = dist (f b') (f a')" by (simp add: dist_norm)
            also have "\<dots> \<le> M * dist b' a'" using lipschitz_onD[OF lip] ksub ab' leab by simp
            also have "dist b' a' = b' - a'" using leab by (simp add: dist_real_def)
            also have "M * (b' - a') = M * content k" using ab' leab by (simp add: content_real)
            finally show "norm (f (Sup k) - f (Inf k)) \<le> M * content k" using infk supk by simp
          qed
          have "(\<Sum>k\<in>D. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>D. M * content k)"
            by (rule sum_mono) (rule elem)
          also have "\<dots> = M * content {c..d}"
            by (metis D box_real(2) sum_content.division sum_distrib_left)
          also have "... \<le> max 0 (M * (d - c))"
            using Mnn by (simp add: content_real_if)
          finally show "(\<Sum>k\<in>D. norm (f (Sup k) - f (Inf k))) \<le> max 0 (M * (d - c))" .
        qed
      qed
      have bv_hh: "has_bounded_variation_on h {0..1}" using lip_imp_bv[OF lip_hh] .
      have bv_g: "has_bounded_variation_on g {0..1}" using lip_imp_bv[OF lip_g] .
      have bv_hh_ab: "has_bounded_variation_on h {a..b}"
        using bv_hh has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff dual_order.refl)
      have bv_g_ab: "has_bounded_variation_on g {a..b}"
        using bv_g has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff dual_order.refl)
      have a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}" using ab01 by auto
      have bv_hh_a1: "has_bounded_variation_on h {a..1}"
        using bv_hh has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff order_refl)
      have bv_g_a1: "has_bounded_variation_on g {a..1}"
        using bv_g has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff order_refl)
      have split_hh: "vector_variation {0..1} h = vector_variation {0..a} h + vector_variation {a..b} h + vector_variation {b..1} h"
        using vector_variation_combine[OF bv_hh a01] vector_variation_combine[OF bv_hh_a1] \<open>a<b\<close> b_le1 
        by simp
      have split_g: "vector_variation {0..1} g = vector_variation {0..a} g + vector_variation {a..b} g + vector_variation {b..1} g"
        using vector_variation_combine[OF bv_g a01] vector_variation_combine[OF bv_g_a1] \<open>a<b\<close> b_le1
        by simp
      have lo_eq: "vector_variation {0..a} h = vector_variation {0..a} g"
        by (rule vector_variation_cong) (simp add: hh_lo)
      have hi_eq: "vector_variation {b..1} h = vector_variation {b..1} g"
        by (rule vector_variation_cong) (simp add: hh_hi)
      have hh_a: "h a = g a" using \<open>a<b\<close> by (simp add: h_def)
      have hh_b: "h b = g b" using \<open>a<b\<close> by (simp add: h_def)
      have mid_hh_ge: "vector_variation {a..b} h \<ge> norm (g b - g a)"
        using vector_variation_ge_norm_function[OF bv_hh_ab, of b a] \<open>a<b\<close> hh_a hh_b 
        by fastforce 
      have mid_hh_le: "vector_variation {a..b} h \<le> norm (g b - g a)"
      proof -
        have key: "(\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) \<le> norm (g b - g a)"
          if D: "D division_of {a..b}" for D
        proof -
          have elem: "norm (h (Sup k) - h (Inf k)) = ((Sup k - Inf k)/(b-a)) * norm (g b - g a)"
            if k: "k \<in> D" for k
          proof -
            obtain a' b' where ab': "k = cbox a' b'"  and ksub: "k \<subseteq> {a..b}" and kne: "k \<noteq> {}" 
              using division_ofD D k by metis
            then have leab: "a' \<le> b'" using ab' by (simp add: box_ne_empty)
            have infk: "Inf k = a'" and supk: "Sup k = b'" using ab' leab by auto
            have a': "a' \<in> {a..b}" and b': "b' \<in> {a..b}" using ksub ab' leab by auto
            have "h b' - h a' = ((b'-a')/(b-a)) *\<^sub>R (g b - g a)"
              by (simp add: hh_eq_lin[OF a'] hh_eq_lin[OF b'] scaleR_left_diff_distrib diff_divide_distrib)
            then have "norm (h b' - h a') = \<bar>(b'-a')/(b-a)\<bar> * norm (g b - g a)" by simp
            also have "\<bar>(b'-a')/(b-a)\<bar> = (b'-a')/(b-a)" using leab \<open>a<b\<close> by simp
            finally show "norm (h (Sup k) - h (Inf k)) = ((Sup k - Inf k)/(b-a)) * norm (g b - g a)"
              using infk supk by simp
          qed
          have content_elem: "(Sup k - Inf k) = content k" if k: "k \<in> D" for k
            using division_ofD(3,4)[OF D k] by (auto simp: content_real)
          then have "(\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) = (\<Sum>k\<in>D. ((Sup k - Inf k)/(b-a)) * norm (g b - g a))"
            using local.elem by auto
          also have "\<dots> = ((\<Sum>k\<in>D. (Sup k - Inf k))/(b-a)) * norm (g b - g a)"
            by (simp add: sum_distrib_right sum_divide_distrib)
          also have "(\<Sum>k\<in>D. (Sup k - Inf k)) = (\<Sum>k\<in>D. content k)"
            using content_elem by force
          also have "(\<Sum>k\<in>D. content k) = content {a..b}"
            by (metis D additive_content_division cbox_interval)
          also have "content {a..b} = b - a" using \<open>a<b\<close> by (simp add: content_real)
          also have "((b-a)/(b-a)) * norm (g b - g a) = norm (g b - g a)" using \<open>a<b\<close> by simp
          finally show "(\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) \<le> norm (g b - g a)" by simp
        qed
        show ?thesis
          using bv_hh_ab key has_bounded_vector_variation_on_interval by blast
      qed
      have mid_hh_eq: "vector_variation {a..b} h = norm (g b - g a)"
        using mid_hh_ge mid_hh_le by simp
      define c where "c = (a + b)/2"
      have c_mem: "c \<in> {a<..<b}" and ac: "a < c" and cb: "c < b"
        using \<open>a<b\<close> by (auto simp: c_def)
      have gc_not_seg: "g c \<notin> closed_segment (g a) (g b)"
        using c_mem frontier_def local.interior_subset seg_in_frontier by fastforce
      have "\<not> between (g a, g b) (g c)" using gc_not_seg by (simp add: between_mem_segment)
      with dist_triangle have strict_tri: "dist (g a) (g b) < dist (g a) (g c) + dist (g c) (g b)"
        using between order_less_le by blast
      have c_in_ab: "c \<in> {a..b}" using ac cb by simp
      have bv_g_ac: "has_bounded_variation_on g {a..c}"
        using bv_g_ab has_bounded_variation_on_subset ac cb by (meson atLeastatMost_subset_iff order_refl less_imp_le)
      have bv_g_cb: "has_bounded_variation_on g {c..b}"
        using bv_g_ab has_bounded_variation_on_subset ac cb by (meson atLeastatMost_subset_iff order_refl less_imp_le)
      have mid_g_gt: "vector_variation {a..b} g > norm (g b - g a)"
      proof -
        have split: "vector_variation {a..b} g = vector_variation {a..c} g + vector_variation {c..b} g"
          using vector_variation_combine[OF bv_g_ab c_in_ab] .
        have ge1: "norm (g c - g a) \<le> vector_variation {a..c} g"
          using vector_variation_ge_norm_function[OF bv_g_ac, of c a] ac cb by (simp add: norm_minus_commute)
        have ge2: "norm (g b - g c) \<le> vector_variation {c..b} g"
          using vector_variation_ge_norm_function[OF bv_g_cb, of b c] ac cb by (simp add: norm_minus_commute)
        have "norm (g b - g a) < norm (g c - g a) + norm (g b - g c)"
          using strict_tri by (simp add: dist_norm norm_minus_commute)
        also have "\<dots> \<le> vector_variation {a..b} g" 
          using split ge1 ge2 by simp
        finally show ?thesis .
      qed
      have path_length_lt: "path_length h < path_length g"
        by (simp add: hi_eq lo_eq mid_g_gt mid_hh_eq path_length_def split_g split_hh)
      have lip_show: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
        using lipschitz_onD[OF lip_hh] .
      have hh_agree: "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x" using hh_out_g .
      show thesis
        using that[OF simple_hh hh_start hh_finish lip_show path_length_lt hull_hh hh_agree hh_frontier] .
    qed
  qed
qed

text \<open>A nonempty bounded open connected subset of the reals is an open interval.\<close>

lemma open_bounded_connected_real_is_interval:
  fixes c :: "real set"
  assumes "open c" "connected c" "c \<noteq> {}" "bounded c"
  shows "c = {Inf c<..<Sup c}"
proof -
  have isiv: "is_interval c" using assms(2) by (simp add: is_interval_connected_1)
  have bb: "bdd_below c" and ba: "bdd_above c" using assms(4) bounded_imp_bdd_below bounded_imp_bdd_above by auto
  have InfnotIn: "Inf c \<notin> c"
  proof
    assume "Inf c \<in> c"
    then obtain b where "b < Inf c" "{b<..Inf c} \<subseteq> c"
      using open_left[OF assms(1) \<open>Inf c \<in> c\<close>, of "Inf c - 1"] by auto
    then have "(Inf c + b)/2 \<in> c" by auto
    moreover have "(Inf c + b)/2 < Inf c" using \<open>b < Inf c\<close> by simp
    ultimately show False using bb cInf_lower leD by blast
  qed
  have SupnotIn: "Sup c \<notin> c"
  proof
    assume "Sup c \<in> c"
    then obtain b where "Sup c < b" "{Sup c..<b} \<subseteq> c" 
      using open_right[OF assms(1) \<open>Sup c \<in> c\<close>, of "Sup c + 1"] by auto
    then have "(Sup c + b)/2 \<in> c" by auto
    moreover have "Sup c < (Sup c + b)/2" using \<open>Sup c < b\<close> by simp
    ultimately show False using ba cSup_upper leD by blast
  qed
  show ?thesis
  proof (intro set_eqI iffI)
    fix x assume "x \<in> c"
    then have "Inf c \<le> x" "x \<le> Sup c" using bb ba cInf_lower cSup_upper by auto
    moreover have "x \<noteq> Inf c" "x \<noteq> Sup c" using \<open>x \<in> c\<close> InfnotIn SupnotIn by auto
    ultimately show "x \<in> {Inf c<..<Sup c}" by auto
  next
    fix x assume x: "x \<in> {Inf c<..<Sup c}"
    obtain u where u: "u \<in> c" "u < x" using x assms(3) bb
      by (metis cInf_lessD greaterThanLessThan_iff)
    obtain v where v: "v \<in> c" "x < v" using x assms(3) ba
      by (metis less_cSupD greaterThanLessThan_iff)
    show "x \<in> c" using isiv u v by (meson is_interval_1 less_imp_le)
  qed
qed

text \<open>The reduced convexification subgoal: a unit-speed (Lipschitz) simple closed rectifiable loop
  starting on the frontier of its convex hull can be replaced by a no-longer loop with the same
  convex hull whose image IS that frontier. The components of the part of the parameter interval
  whose image avoids the frontier are countably many open intervals.\<close>

proposition convexification_unit_speed:
  fixes \<gamma> :: "real \<Rightarrow> complex"
  assumes rect: "rectifiable_path \<gamma>" and simp: "simple_path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
    and frstart: "pathstart \<gamma> \<in> frontier (convex hull (path_image \<gamma>))"
    and lip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (\<gamma> x) (\<gamma> y) \<le> path_length \<gamma> * dist x y"
  shows "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length \<gamma> \<and> convex hull (path_image h) = convex hull (path_image \<gamma>) \<and> path_image h = frontier (convex hull (path_image \<gamma>))"
proof (cases "path_image \<gamma> \<subseteq> frontier (convex hull (path_image \<gamma>))")
  case True
  \<comment> \<open>Already on the frontier: @{term \<gamma>} itself works (its image equals the frontier).\<close>
  have "path_image \<gamma> = frontier (convex hull (path_image \<gamma>))"
    using frontier_convex_hull_subset_path_image[OF simp loop True] True by blast
  then show ?thesis using rect simp loop by (intro exI[of _ \<gamma>]) auto
next
  case False
  have path\<gamma>: "path \<gamma>" using simp by (rule simple_path_imp_path)
  define F where "F = frontier (convex hull (path_image \<gamma>))"
  define s where "s = {t \<in> {0..1}. \<gamma> t \<notin> F}"
  have cont\<gamma>: "continuous_on {0..1} \<gamma>" using path\<gamma> by (simp add: path_def)
  have g0F: "\<gamma> 0 \<in> F" using frstart F_def by (simp add: pathstart_def)
  have g1F: "\<gamma> 1 \<in> F" using frstart loop F_def by (simp add: pathstart_def pathfinish_def)
  \<comment> \<open>Since both endpoints map into @{term F}, the deviating set @{term s} avoids $0$ and $1$, hence is open in $\mathbb{R}$.\<close>
  have s_sub: "s \<subseteq> {0<..<1}"
  proof
    fix t assume "t \<in> s"
    then have bounds: "0 \<le> t" "t \<le> 1" and outside: "\<gamma> t \<notin> F"
      unfolding s_def by auto
    have "t \<noteq> 0" "t \<noteq> 1" using outside g0F g1F by auto
    then show "t \<in> {0<..<1}" using bounds by auto
  qed
  have "openin (top_of_set {0..1}) ({0..1} \<inter> \<gamma> -` (- F))"
    using cont\<gamma> by (intro continuous_openin_preimage_gen) (auto simp: F_def)
  then have s_openin: "openin (top_of_set {0..1}) s"
    by (smt (verit) Collect_cong Compl_iff Int_def s_def vimage_eq)
  then have "openin (top_of_set {0<..<1}) s"
    by (metis interior_atLeastAtMost_real interior_subset openin_subset_trans s_sub)
  then have opens: "open s"
    by (simp add: openin_open_trans)
  have s_ne: "s \<noteq> {}"
    using False by (auto simp: s_def F_def path_image_def)
  \<comment> \<open>Component decomposition: the components of @{term s} are countably many open intervals
     \<open>{a n<..<b n}\<close>, each with both endpoints mapped by @{term \<gamma>} onto the frontier @{term F}.\<close>
  have decomp: "\<exists>a b::nat\<Rightarrow>real. (\<forall>n. a n \<in> {0..1}) \<and> (\<forall>n. b n \<in> {0..1}) \<and> (\<forall>n. a n \<le> b n) \<and> (\<forall>n. \<gamma> (a n) \<in> F) \<and> (\<forall>n. \<gamma> (b n) \<in> F) \<and> components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
  proof -
    have comp_open: "\<And>c. c \<in> components s \<Longrightarrow> open c" using opens by (rule open_components)
    have comp_disj: "disjoint (components s)"
      using pairwise_disjoint_components by (simp add: disjoint_def pairwise_def disjnt_def)
    have comp_count: "countable (components s)"
      using comp_open comp_disj by (rule countable_disjoint_open_subsets)
    have comp_ne: "components s \<noteq> {}" using s_ne by (simp add: components_eq_empty)
    define q where "q = from_nat_into (components s)"
    have q_range: "range q = components s"
      unfolding q_def using comp_ne comp_count by (rule range_from_nat_into)
    have q_comp: "\<And>n. q n \<in> components s" using q_range by auto
    have s_sub01: "s \<subseteq> {0..1}" using s_sub by auto
    have s_bdd: "bounded s" using s_sub01 bounded_closed_interval bounded_subset by blast
    have qsub: "\<And>n. q n \<subseteq> s" using q_comp in_components_subset by blast
    have q_interval: "q n = {Inf (q n)<..<Sup (q n)}" for n
    proof -
      have "bounded (q n)" using qsub s_bdd bounded_subset by blast
      then show "q n = {Inf (q n)<..<Sup (q n)}"
        by (metis comp_open in_components_maximal open_bounded_connected_real_is_interval q_comp)
    qed
    define a where "a = (\<lambda>n. Inf (q n))"
    define b where "b = (\<lambda>n. Sup (q n))"
    have qab: "\<And>n. q n = {a n<..<b n}" using q_interval by (simp add: a_def b_def)
    have ablt: "a n < b n" for n
      by (metis greaterThanLessThan_empty_iff in_components_maximal linorder_not_le q_comp qab)
    have clq: "\<And>n. closure (q n) = {a n..b n}" using qab ablt by (simp add: closure_greaterThanLessThan)
    have cls01: "closure s \<subseteq> {0..1}"
      using s_sub closure_mono[of s "{0<..<1}"] closure_greaterThanLessThan[of "0::real" 1] by simp
    have ab01: "a n \<in> {0..1} \<and> b n \<in> {0..1}" for n
    proof -
      have sub: "{a n..b n} \<subseteq> {0..1}"
        by (metis closure_mono clq cls01 qsub subset_trans) 
      then show "a n \<in> {0..1} \<and> b n \<in> {0..1}"
        by (meson ablt atLeastAtMost_iff less_eq_real_def subset_eq)
    qed
    have a_notin: "\<And>n. a n \<notin> s"
    proof (rule ccontr)
      fix n assume "\<not> a n \<notin> s"
      then have sub: "{a n..<b n} \<subseteq> s"
        using less_eq_real_def qab qsub by fastforce
      then have "{a n..<b n} = q n"
        using q_comp[of n] in_components_maximal 
        by (metis connected_Ico interior_atLeastLessThan interior_subset qab subset_empty)
      then show False using ablt[of n] qab 
        by (metis atLeastLessThan_iff greaterThanLessThan_iff less_irrefl order_refl)
    qed
    have b_notin: "\<And>n. b n \<notin> s"
    proof (rule ccontr)
      fix n assume "\<not> b n \<notin> s"
      then have sub: "{a n<..b n} \<subseteq> s"
        using less_eq_real_def qab qsub by fastforce
      then have "{a n<..b n} = q n"
        using q_comp[of n] in_components_maximal
        by (metis connected_Ioc interior_lessThanAtMost interior_subset qab subset_empty)
      then show False using ablt[of n] qab 
        by (metis greaterThanAtMost_iff greaterThanLessThan_iff less_irrefl order_refl)
    qed
    have gaF: "\<And>n. \<gamma> (a n) \<in> F" and gbF: "\<And>n. \<gamma> (b n) \<in> F"
      using ab01 a_notin b_notin s_def by blast+
    have comp_eq: "components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
      using full_SetCompr_eq q_range qab by force
    show "\<exists>a b::nat\<Rightarrow>real. (\<forall>n. a n \<in> {0..1}) \<and> (\<forall>n. b n \<in> {0..1}) \<and> (\<forall>n. a n \<le> b n) \<and> (\<forall>n. \<gamma> (a n) \<in> F) \<and> (\<forall>n. \<gamma> (b n) \<in> F) \<and> components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
      using ab01 ablt gaF gbF comp_eq by (intro exI[of _ a] exI[of _ b]) (auto simp: less_imp_le)
  qed
  \<comment> \<open>Extract the deviating arcs from the decomposition.\<close>
  from decomp obtain a b :: "nat \<Rightarrow> real" where
    ab01: "\<And>n. a n \<in> {0..1}" "\<And>n. b n \<in> {0..1}" and
    able: "\<And>n. a n \<le> b n" and
    gaF: "\<And>n. \<gamma> (a n) \<in> F" and gbF: "\<And>n. \<gamma> (b n) \<in> F" and
    comps: "components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}" by auto
  \<comment> \<open>@{term "U n"} collects the first @{term n} deviating arcs; @{term "P n h"} is the invariant for the @{term n}-th
     approximation: a Lipschitz simple closed loop with the same convex hull, mapping the
     first @{term n} arcs onto the frontier and equal to @{term \<gamma>} elsewhere.\<close>
  define U where "U = (\<lambda>n::nat. \<Union> {{a m<..<b m} | m. m < n})"
  define P where "P = (\<lambda>n h. simple_path h \<and> rectifiable_path h \<and> pathstart h = pathstart \<gamma> \<and> pathfinish h = pathfinish \<gamma> \<and> convex hull (path_image h) = convex hull (path_image \<gamma>) \<and> (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. dist (h x) (h y) \<le> path_length \<gamma> * dist x y) \<and> (\<forall>x\<in>U n. h x \<in> F) \<and> (\<forall>x. x \<notin> U n \<longrightarrow> h x = \<gamma> x))"
  have arc_comp: "\<And>n. {a n<..<b n} \<in> components s" using comps by auto
  have arc_in_s: "\<And>n. {a n<..<b n} \<subseteq> s" using arc_comp in_components_subset by blast
  have USuc: "\<And>n. U (Suc n) = U n \<union> {a n<..<b n}"
    by (auto simp: U_def less_Suc_eq)
  have U_sub_s: "\<And>n. U n \<subseteq> s"
    using U_def arc_in_s by blast
  have an_notin_U: "\<And>n. a n \<notin> U n" and bn_notin_U: "\<And>n. b n \<notin> U n" 
    using U_sub_s gaF gbF s_def by blast+
  have arc_sub_U: "\<And>i j::nat. i < j \<Longrightarrow> {a i<..<b i} \<subseteq> U j"
    by (auto simp: U_def)
  have U_mem: "\<And>x n. x \<in> U n \<Longrightarrow> \<exists>i<n. x \<in> {a i<..<b i}"
    unfolding U_def by blast
  have arc_disj: "\<And>i j. {a i<..<b i} \<noteq> {a j<..<b j} \<Longrightarrow> {a i<..<b i} \<inter> {a j<..<b j} = {}"
    using arc_comp components_nonoverlap by blast
  have arc_disj_U: "\<And>n. \<not> {a n<..<b n} \<subseteq> U n \<Longrightarrow> {a n<..<b n} \<inter> U n = {}"
    using U_mem arc_disj arc_sub_U by blast
  have F_eq: "F = frontier (convex hull (path_image \<gamma>))" by (simp add: F_def)
  \<comment> \<open>Inductive step: straighten the @{term n}-th arc with \<open>step_lemma\<close> (unless it is empty or already
     handled), preserving the invariant.\<close>
  have step: "\<And>n h. P n h \<Longrightarrow> \<exists>h'. P (Suc n) h' \<and> (\<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x)"
  proof -
    fix n h assume Ph: "P n h"
    have hsimple: "simple_path h" and hrect: "rectifiable_path h"
      and hps: "pathstart h = pathstart \<gamma>" and hpf: "pathfinish h = pathfinish \<gamma>"
      and hhull: "convex hull (path_image h) = convex hull (path_image \<gamma>)"
      and hlip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> path_length \<gamma> * dist x y"
      and hUF: "\<And>x. x \<in> U n \<Longrightarrow> h x \<in> F"
      and hoff: "\<And>x. x \<notin> U n \<Longrightarrow> h x = \<gamma> x"
      using Ph unfolding P_def by auto
    have hloop: "pathfinish h = pathstart h" using hps hpf loop by simp
    have hF: "frontier (convex hull (path_image h)) = F" using hhull F_eq by simp
    show "\<exists>h'. P (Suc n) h' \<and> (\<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x)"
    proof (cases "{a n<..<b n} = {} \<or> {a n<..<b n} \<subseteq> U n")
      case True with USuc Ph show ?thesis 
        by (intro exI[of _ h]) (auto simp: P_def)
    next
      case False
      then have ablt_n: "a n < b n" and arc_disj_Un: "{a n<..<b n} \<inter> U n = {}" 
        using arc_disj_U by auto
      have ha: "h (a n) = \<gamma> (a n)" and hb: "h (b n) = \<gamma> (b n)" 
        using hoff an_notin_U bn_notin_U by auto
      have harc: "\<And>x. x \<in> {a n<..<b n} \<Longrightarrow> h x = \<gamma> x" using hoff arc_disj_Un by blast
      have haF: "h (a n) \<in> frontier (convex hull (path_image h))" using ha gaF hF by simp
      have hbF: "h (b n) \<in> frontier (convex hull (path_image h))" using hb gbF hF by simp
      have harc_offF: "h ` {a n<..<b n} \<inter> frontier (convex hull (path_image h)) = {}"
        using arc_in_s s_def hF harc by fastforce
      obtain h' where h'simple: "simple_path h'"
        and h'p: "pathstart h' = pathstart h" "pathfinish h' = pathstart h"
        and h'lip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h' x) (h' y) \<le> path_length \<gamma> * dist x y"
        and h'hull: "convex hull (path_image h') = convex hull (path_image h)"
        and h'off: "\<And>x. x \<notin> {a n<..<b n} \<Longrightarrow> h' x = h x"
        and h'arcF: "h' ` {a n..b n} \<subseteq> frontier (convex hull (path_image h))"
        using step_lemma[OF hsimple hloop hlip ablt_n ab01(1)[of n] ab01(2)[of n] haF hbF harc_offF]
        by metis
      have h'rect: "rectifiable_path h'"
        by (metis lipschitz_imp_rectifiable_path dist_norm h'lip)
      have h'agree: "\<And>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<Longrightarrow> h' x = h x"
        by (meson arc_disj_Un disjoint_iff h'off)
      have h'UF: "\<And>x. x \<in> U (Suc n) \<Longrightarrow> h' x \<in> F"
        using F_eq USuc h'agree h'arcF hUF hhull by fastforce
      have h'offSuc: "h' x = \<gamma> x" if "x \<notin> U (Suc n)" for x
        using USuc that h'off hoff by force
      have PSuc: "P (Suc n) h'"
        using P_def Ph h'UF h'hull h'lip h'offSuc h'p h'rect h'simple hloop by presburger
      show ?thesis using PSuc h'agree by blast
    qed
  qed
  \<comment> \<open>Dependent choice yields the sequence of approximations @{term f}.\<close>
  have base: "P 0 \<gamma>"
    using simp rect lip by (simp add: P_def U_def)
  obtain f where f: "\<And>n. P n (f n)"
    and fstep: "\<And>n x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<Longrightarrow> f (Suc n) x = f n x"
    using dependent_nat_choice[where P=P and Q="\<lambda>n h h'. \<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x"]
      base step by blast
  have evconst: "\<exists>y. \<forall>\<^sub>F n in sequentially. f n x = y" if x01: "x \<in> {0..1}" for x
  proof (cases "\<exists>n. x \<in> {a n<..<b n}")
    case False
    have stab: "f n x = f 0 x" for n
    by (induct n; use fstep False in presburger)
    then show ?thesis
      by (meson eventually_at_top_dense)
  next
    case True
    define N where "N = (LEAST n. x \<in> {a n<..<b n})"
    have xN: "x \<in> {a N<..<b N}" using True LeastI_ex N_def by (metis (mono_tags, lifting))
    have stab2: "\<And>m. N < m \<Longrightarrow> f (Suc m) x = f m x"
      using arc_sub_U fstep xN by blast
    have "f (Suc N + d) x = f (Suc N) x" for d
      by (induct d; use stab2 in fastforce)
    then have "eventually (\<lambda>n. f n x = f (Suc N) x) sequentially"
      by (metis (mono_tags, lifting) Suc_leI eventually_at_top_dense nat_le_iff_add)
    then show ?thesis by blast
  qed
  \<comment> \<open>Skolemize to obtain the limit path @{term h}: $f\,n\,x = h\,x$ eventually, for each @{term x}.\<close>
  obtain h where h: "\<And>x. x \<in> {0..1} \<Longrightarrow> eventually (\<lambda>n. f n x = h x) sequentially"
    using evconst by (metis (mono_tags))
  \<comment> \<open>Properties of the approximants @{term "f n"}, extracted from the invariant @{term P}.\<close>
  have fsimple: "\<And>n. simple_path (f n)" using f unfolding P_def by blast
  have fps: "\<And>n. pathstart (f n) = pathstart \<gamma>" using f unfolding P_def by blast
  have fpf: "\<And>n. pathfinish (f n) = pathfinish \<gamma>" using f unfolding P_def by blast
  have fhull: "\<And>n. convex hull (path_image (f n)) = convex hull (path_image \<gamma>)" using f unfolding P_def by blast
  have flip: "\<And>n x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (f n x) (f n y) \<le> path_length \<gamma> * dist x y"
    using f unfolding P_def by blast
  have fUF: "\<And>n x. x \<in> U n \<Longrightarrow> f n x \<in> F" using f unfolding P_def by blast
  have foff: "\<And>n x. x \<notin> U n \<Longrightarrow> f n x = \<gamma> x" using f unfolding P_def by blast
  \<comment> \<open>The limit path @{term h} inherits the $L$-Lipschitz bound (pointwise limit of $L$-Lipschitz maps).\<close>
  have hlip: "dist (h x) (h y) \<le> path_length \<gamma> * dist x y"
    if xy: "x \<in> {0..1}" "y \<in> {0..1}" for x y
  proof -
    have ev: "eventually (\<lambda>n. f n x = h x \<and> f n y = h y) sequentially"
      using h[OF xy(1)] h[OF xy(2)] by eventually_elim simp
    then obtain n where n: "f n x = h x" "f n y = h y"
      unfolding eventually_sequentially by auto
    then show "dist (h x) (h y) \<le> path_length \<gamma> * dist x y" 
      using n flip[OF xy] by metis
  qed
  have hrect: "rectifiable_path h"
    by (rule lipschitz_imp_rectifiable_path[where B="path_length \<gamma>"])
       (use hlip in \<open>simp add: dist_norm\<close>)
  have hpath: "path h" using hrect by (rule rectifiable_path_imp_path)
  have hsimple: "simple_path h"
    unfolding simple_path_def loop_free_def
  proof (intro conjI strip)
    show "path h" by (rule hpath)
    fix x y :: real assume xy: "x \<in> {0..1}" "y \<in> {0..1}" and eq: "h x = h y"
    then have ev: "eventually (\<lambda>n. f n x = h x \<and> f n y = h y) sequentially"
      by (metis (full_types) eventually_conj_iff h)
    then obtain n where n: "f n x = h x" "f n y = h y"
      unfolding eventually_sequentially by auto
    then show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
      using n eq fsimple[of n] xy unfolding simple_path_def loop_free_def by presburger 
  qed
  have hloop: "pathfinish h = pathstart h"
  proof -
    have z01: "(0::real) \<in> {0..1}" and o01: "(1::real) \<in> {0..1}" by auto
    then obtain n where n: "f n 0 = h 0" "f n 1 = h 1"
      using h[OF z01] h[OF o01] fpf by (auto simp: path_defs eventually_sequentially)
    have "f n 1 = f n 0" using fps[of n] fpf[of n] loop by (simp add: pathstart_def pathfinish_def)
    with n show ?thesis by (simp add: pathstart_def pathfinish_def)
  qed
  have hlen: "path_length h \<le> path_length \<gamma>"
    by (metis Rectifiable_Path.path_length_lipschitz dist_norm hlip)
  \<comment> \<open>The image of @{term h} lies on the frontier: each parameter either lands in an arc (so eventually
     in @{term F}) or maps via @{term \<gamma>} to a point already on the frontier.\<close>
  have notarc_notin_s: False if noarc: "\<nexists>n. x \<in> {a n<..<b n}" "x \<in> s" for x
  proof -
    from that Union_components 
    obtain c where "c \<in> components s" "x \<in> c" by blast
    then show False using comps noarc \<open>x \<in> c\<close> by blast
  qed
  have hx_in_F: "\<And>x. x \<in> {0..1} \<Longrightarrow> h x \<in> F"
  proof -
    fix x :: real assume x01: "x \<in> {0..1}"
    show "h x \<in> F"
    proof (cases "\<exists>n. x \<in> {a n<..<b n}")
      case True
      then obtain n where xn: "x \<in> {a n<..<b n}" by blast
      obtain N where N: "\<And>m. N \<le> m \<Longrightarrow> f m x = h x" using h[OF x01] unfolding eventually_sequentially by blast
      define m where "m = max N (Suc n)"
      have "N \<le> m" "n < m" by (auto simp: m_def)
      then show "h x \<in> F" using N fUF \<open>N \<le> m\<close>
        using arc_sub_U xn by fastforce
    next
      case False
      obtain n where n: "f n x = h x" using h[OF x01] unfolding eventually_sequentially by blast
      have "x \<notin> U n" using False U_mem by blast
      moreover have "\<gamma> x \<in> F" using x01 s_def
        using False notarc_notin_s by blast
      ultimately show "h x \<in> F" using n
        by (simp add: foff)
    qed
  qed
  have hsub_F: "path_image h \<subseteq> F" using hx_in_F by (auto simp: path_image_def)
  \<comment> \<open>Off the arcs, @{term h} still agrees with @{term \<gamma>}; so @{term \<gamma>}'s image outside the deviating set @{term s} is part of
     the image of @{term h}.\<close>
  have hoff_s: "h x = \<gamma> x" if x01: "x \<in> {0..1}" and xs: "x \<notin> s" for x
    by (metis (mono_tags, lifting) U_sub_s eventually_sequentially foff h le_refl subset_eq
        that)
  have gout_sub_h: "\<gamma> ` ({0..1} - s) \<subseteq> path_image h"
    using hoff_s by (force simp: path_image_def)
  \<comment> \<open>The convex hulls agree.\<close>
  have hhull: "convex hull (path_image h) = convex hull (path_image \<gamma>)"
  proof (rule subset_antisym)
    \<comment> \<open>$\subseteq$: every point $h\,x = f\,n\,x$ for some @{term n} lies in @{term "convex hull (path_image (f n))"} $=$ @{term "convex hull (path_image \<gamma>)"}.\<close>
    have ph_sub: "path_image h \<subseteq> convex hull (path_image \<gamma>)"
    proof
      fix z assume "z \<in> path_image h"
      then obtain x where x: "x \<in> {0..1}" "z = h x" by (auto simp: path_image_def)
      obtain n where n: "f n x = h x" using h[OF x(1)] unfolding eventually_sequentially by blast
      have "h x = f n x" using n by simp
      then have "h x \<in> convex hull (path_image (f n))" using hull_subset
        by (metis hull_inc imageI path_image_def x(1))
      then show "z \<in> convex hull (path_image \<gamma>)"
        by (simp add: fhull x(2))
    qed
    show "convex hull (path_image h) \<subseteq> convex hull (path_image \<gamma>)"
      using ph_sub convex_convex_hull by (rule hull_minimal)
  next
    \<comment> \<open>$\supseteq$: the extreme points of the hull are frontier points, hence images of parameters
       outside @{term s}, which lie in @{term "path_image h"}. (Krein--Milman + redundancy of interior points.)\<close>
    have cpt_g: "compact (convex hull path_image \<gamma>)"
      by (simp add: compact_convex_hull compact_path_image path\<gamma>)
    have km_g: "convex hull path_image \<gamma> = convex hull {x. x extreme_point_of (convex hull path_image \<gamma>)}"
      using Krein_Milman_Minkowski[OF cpt_g convex_convex_hull] by simp
    have ext_in_out: "z \<in> \<gamma> ` ({0..1} - s)" 
      if "z extreme_point_of (convex hull path_image \<gamma>)" for z
    proof -
      have zpig: "z \<in> path_image \<gamma>" using extreme_point_of_convex_hull[OF that] .
      have znotint: "z \<notin> interior (convex hull path_image \<gamma>)" 
        using extreme_point_not_in_interior[OF that] .
      have "z \<in> F"
        using F_def closure_subset frontier_def hull_inc znotint zpig by fastforce
      then show ?thesis using zpig
        by (auto simp: path_image_def s_def)
    qed
    have "{x. x extreme_point_of (convex hull path_image \<gamma>)} \<subseteq> \<gamma> ` ({0..1} - s)"
      using ext_in_out by blast
    then have "convex hull (path_image \<gamma>) \<subseteq> convex hull (\<gamma> ` ({0..1} - s))"
      using hull_mono km_g by blast
    also have "convex hull (\<gamma> ` ({0..1} - s)) \<subseteq> convex hull (path_image h)"
      using gout_sub_h by (rule hull_mono)
    finally show "convex hull (path_image \<gamma>) \<subseteq> convex hull (path_image h)" .
  qed
  \<comment> \<open>The image of @{term h} is exactly the frontier: $\subseteq$ is \<open>hsub_F\<close>; $\supseteq$ because @{term h} is a simple closed
     curve whose image lies on the frontier of its (now equal) convex hull.\<close>
  have hF: "frontier (convex hull (path_image h)) = F" using hhull F_eq by simp
  have h_image_F: "path_image h = F"
    using frontier_convex_hull_subset_path_image hF hloop hsimple hsub_F by blast
  show ?thesis
    using F_def h_image_F hhull hlen hloop hrect hsimple by blast
qed

theorem isoperimetric_convexification:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
  obtains h where "rectifiable_path h" and "simple_path h"
    and "pathfinish h = pathstart h"
    and "path_length h \<le> path_length g"
    and "convex hull (path_image h) = convex hull (path_image g)"
    and "path_image h = frontier (convex hull (path_image g))"
proof -
  \<comment> \<open>Strengthened version, assuming the loop starts on the frontier of its convex hull.
     (Here used to derive the general statement by shifting the basepoint.)\<close>
  have *: "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length G \<and> convex hull (path_image h) = convex hull (path_image G) \<and> path_image h = frontier (convex hull (path_image G))"
    if Grect: "rectifiable_path G" and Gsimple: "simple_path G" and Gloop: "pathfinish G = pathstart G"
      and Gfr: "pathstart G \<in> frontier (convex hull (path_image G))" for G :: "real \<Rightarrow> complex"
      using arc_length_reparametrization[OF Grect] convexification_unit_speed Gsimple Gloop Gfr
      by (metis (no_types, lifting) ext)
  \<comment> \<open>Some point of the loop lies on the frontier (an extreme point of the convex hull).\<close>
  have cpt: "compact (convex hull path_image g)"
    by (simp add: assms(2) compact_convex_hull compact_simple_path_image)
  obtain x where x_ext: "x extreme_point_of (convex hull path_image g)"
    using Krein_Milman_Minkowski cpt by fastforce
  have x_fr: "x \<in> frontier (convex hull path_image g)"
    by (metis Krein_Milman_frontier convex_convex_hull cpt extreme_point_of_convex_hull x_ext)
  obtain t where t: "t \<in> {0..1}" "g t = x" 
    using extreme_point_of_convex_hull[OF x_ext] by (auto simp: path_image_def)
  \<comment> \<open>Shift @{term g} so that it starts at the frontier point $g\,t$; properties are preserved.\<close>
  have sp_rect: "rectifiable_path (shiftpath t g)" using assms(1,3) t(1) by (rule rectifiable_path_shiftpath)
  have sp_simple: "simple_path (shiftpath t g)" using assms(2,3) t(1) by (simp add: simple_path_shiftpath)
  have sp_loop: "pathfinish (shiftpath t g) = pathstart (shiftpath t g)" using assms(3) t(1) by (rule closed_shiftpath)
  have sp_pi: "path_image (shiftpath t g) = path_image g" using t(1) assms(3) by (rule path_image_shiftpath)
  have sp_start: "pathstart (shiftpath t g) = g t" using t(1) by (simp add: pathstart_shiftpath)
  have sp_len: "path_length (shiftpath t g) = path_length g" using assms(1,3) t(1) by (rule path_length_shiftpath)
  have sp_startfr: "pathstart (shiftpath t g) \<in> frontier (convex hull (path_image (shiftpath t g)))"
    using sp_start sp_pi x_fr t(2) by simp
  show ?thesis
    using *[OF sp_rect sp_simple sp_loop sp_startfr] sp_len sp_pi that by force
qed

theorem isoperimetric_convexification_strict:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "\<not> convex (inside (path_image g))"
  obtains h where "rectifiable_path h" and "simple_path h"
    and "pathfinish h = pathstart h"
    and "path_length h \<le> path_length g"
    and "convex hull (path_image h) = convex hull (path_image g)"
    and "path_image h = frontier (convex hull (path_image g))"
    and "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
proof -
  obtain h where h: "rectifiable_path h" "simple_path h" "pathfinish h = pathstart h"
      "path_length h \<le> path_length g" "convex hull (path_image h) = convex hull (path_image g)"
      "path_image h = frontier (convex hull (path_image g))"
    using isoperimetric_convexification[OF assms(1,2,3)] by metis
  have bdd_hull: "bounded (convex hull (path_image g))"
    by (simp add: bounded_convex_hull bounded_simple_path_image assms(2))
  have ins_g_sub: "inside (path_image g) \<subseteq> interior (convex hull (path_image g))"
  proof -
    let ?C = "convex hull (path_image g)"
    have conn: "connected (- ?C)" using bdd_hull by (simp add: connected_complement_bounded_convex)
    have unbdd: "\<not> bounded (- ?C)"
      using bdd_hull cobounded_imp_unbounded by blast
    have un: "(?C - path_image g) \<union> (- ?C) = - path_image g" 
      using hull_subset by fastforce
    then have "inside (path_image g) \<subseteq> ?C" using inside_subset[OF conn unbdd un] by blast
    moreover have "open (inside (path_image g))" using assms(2) by (simp add: open_inside closed_simple_path_image)
    ultimately show ?thesis using interior_maximal by blast
  qed
  \<comment> \<open>Measurability: \<open>inside\<close> is bounded and open, hence Lebesgue measurable (cf. HOL Light's
      \<open>MEASURABLE_INSIDE\<close>, which is just \<open>MEASURABLE_OPEN; BOUNDED_INSIDE; OPEN_INSIDE\<close>).\<close>
  have clg: "closed (path_image g)" using assms(2) by (simp add: closed_simple_path_image)
  have "bounded (inside (path_image g))" 
    using Jordan_inside_outside[OF assms(2,3)] by simp
  then have meas_ins_g: "inside (path_image g) \<in> lmeasurable"
    using clg lmeasurable_open open_inside by blast
  have ins_h: "inside (path_image h) = interior (convex hull (path_image g))"
    using h(6) inside_frontier_eq_interior[OF bdd_hull convex_convex_hull] by simp
  have meas_ins_h: "inside (path_image h) \<in> lmeasurable"
    by (simp add: bdd_hull ins_h lmeasurable_interior)
  \<comment> \<open>The path image is not contained in the frontier of its convex hull (else \<open>inside g\<close>
      would be convex), so it meets the interior of the hull.\<close>
  have not_sub: "\<not> path_image g \<subseteq> frontier (convex hull (path_image g))"
    using assms frontier_convex_hull_subset_path_image h(6) ins_h by fastforce
  have pig_hull: "path_image g \<subseteq> convex hull (path_image g)" by (rule hull_subset)
  have ex_int: "\<exists>x. x \<in> path_image g \<and> x \<in> interior (convex hull (path_image g))"
  proof -
    obtain x where x: "x \<in> path_image g" "x \<notin> frontier (convex hull (path_image g))"
      using not_sub by blast
    then have "x \<in> closure (convex hull (path_image g))" using pig_hull closure_subset by blast
    then show ?thesis using x
      using frontier_def by auto
  qed
  have open_outside: "open (outside (path_image g))" 
    and frontier_outside: "frontier (outside (path_image g)) = path_image g"
    using Jordan_inside_outside[OF assms(2,3)] by blast+
  \<comment> \<open>Find a frontier point \<open>x\<close> of \<open>g\<close> in the hull interior; \<open>frontier_straddle\<close> gives a nearby
      outside point \<open>y\<close>, and a ball about \<open>y\<close> lies in \<open>outside g \<inter> interior(hull)\<close>.\<close>
  obtain x where x_pig: "x \<in> path_image g" and x_int: "x \<in> interior (convex hull (path_image g))"
    using ex_int by blast
  obtain r1 where r1: "r1 > 0" "ball x r1 \<subseteq> interior (convex hull (path_image g))"
    using x_int open_contains_ball[of "interior (convex hull (path_image g))"] by auto
  have x_fro_out: "x \<in> frontier (outside (path_image g))" using x_pig frontier_outside by simp
  obtain y where "y \<in> outside (path_image g)" "dist x y < r1"
    using frontier_straddle r1(1) x_fro_out by blast
  then have"y \<in> outside (path_image g) \<inter> interior (convex hull (path_image g))"
    using r1(2) by fastforce
  moreover have "open (outside (path_image g) \<inter> interior (convex hull (path_image g)))"
    using open_outside open_Int open_interior by blast
  ultimately obtain r2 where r2: "r2 > 0" "ball y r2 \<subseteq> outside (path_image g) \<inter> interior (convex hull (path_image g))"
    by (meson open_contains_ball)
  \<comment> \<open>This ball lies in \<open>inside h - inside g\<close>: it is in \<open>interior(hull) = inside h\<close> and in
      \<open>outside g\<close>, which is disjoint from \<open>inside g\<close>.\<close>
  have ball_sub: "ball y r2 \<subseteq> inside (path_image h) - inside (path_image g)"
  proof
    fix z assume z: "z \<in> ball y r2"
    have "z \<in> outside (path_image g)" "z \<in> interior (convex hull (path_image g))" 
      using z r2(2) by blast+
    then show "z \<in> inside (path_image h) - inside (path_image g)"
      by (metis Diff_iff Diff_triv ins_h inside_Int_outside)
  qed
  \<comment> \<open>A nonempty ball has positive measure, so the difference does too.\<close>
  have ball_pos: "measure lebesgue (ball y r2) > 0"
    by (simp add: r2(1))
  have diff_meas: "inside (path_image h) - inside (path_image g) \<in> lmeasurable"
    using meas_ins_h meas_ins_g by (simp add: fmeasurable.Diff)
  have diff_pos: "measure lebesgue (inside (path_image h) - inside (path_image g)) > 0"
    by (meson ball_pos ball_sub diff_meas negligible_iff_measure negligible_subset
        zero_less_measure_iff)
  have ins_g_sub_h: "inside (path_image g) \<subseteq> inside (path_image h)"
    using ins_g_sub ins_h by simp
  have meas_eq: "measure lebesgue (inside (path_image h) - inside (path_image g)) =
      measure lebesgue (inside (path_image h)) - measure lebesgue (inside (path_image g))"
    using measurable_measure_Diff[OF meas_ins_h _ ins_g_sub_h] meas_ins_g by (simp add: fmeasurableD)
  have "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
    using diff_pos meas_eq by linarith
  with h that show ?thesis by blast
qed

subsection \<open>The isoperimetric theorem\<close>

theorem isoperimetric_theorem:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi) \<and>
         (measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<longrightarrow> (\<exists>a r. path_image g = sphere a r))"
proof (cases "convex (inside (path_image g))")
  case True
  show ?thesis
    using isoperimetric_theorem_convex[OF assms(1-3) True assms(4)]
    by blast 
next
  case False
  obtain h where h: "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h"
    "path_length h \<le> path_length g"
    "convex hull (path_image h) = convex hull (path_image g)"
    "path_image h = frontier (convex hull (path_image g))"
    "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
    by (rule isoperimetric_convexification_strict[OF assms(1-3) False])
  have bounded_hull: "bounded (convex hull (path_image g))"
    by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image assms(2))
  have eq_int: "inside (path_image h) = interior (convex hull (path_image g))"
    using inside_frontier_eq_interior[OF bounded_hull convex_convex_hull] h(6) by simp
  have convex_h: "convex (inside (path_image h))"
    using eq_int convex_interior[OF convex_convex_hull] by simp
  have ineq_h: "measure lebesgue (inside (path_image h)) \<le> (path_length h)\<^sup>2 / (4 * pi)"
    using isoperimetric_theorem_convex(1)[OF h(1-3) convex_h refl] .
  have mono: "(path_length h)\<^sup>2 / (4 * pi) \<le> L\<^sup>2 / (4 * pi)"
    by (intro divide_right_mono power_mono)
      (use h(4) assms(4) path_length_pos_le[OF h(1)] pi_gt_zero in simp_all)
  show ?thesis using h(7) ineq_h mono by linarith
qed

end
