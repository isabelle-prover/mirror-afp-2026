section \<open>Part 1: The Wirtinger inequality\<close>

theory Wirtinger
  imports "HOL-Analysis.Rectifiable_Path" "Fourier.Square_Integrable"

begin

text \<open>Convex curve lemmas: Switching between views of a convex simple closed curve.\<close>

lemma convex_hull_eq_closure_inside:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "simple_path g" "pathfinish g = pathstart g"
    and conv: "convex (inside (path_image g))"
  shows "convex hull (path_image g) = closure (inside (path_image g))"
proof (rule equalityI)
  have bounded_inside: "bounded (inside (path_image g))" 
    and frontier_inside: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast+
  show "convex hull (path_image g) \<subseteq> closure (inside (path_image g))"
    by (metis Diff_subset conv convex_closure frontier_def frontier_inside hull_minimal)
  have "compact (closure (inside (path_image g)))"
    using compact_closure local.bounded_inside by blast
  then show "closure (inside (path_image g)) \<subseteq> convex hull (path_image g)"
    by (metis (no_types, lifting) Krein_Milman_frontier conv closure_closure convex_closure
        convex_interior_closure frontier_def frontier_inside order.refl)
qed


lemma frontier_convex_hull_eq_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g" "convex (inside (path_image g))"
  shows "frontier (convex hull (path_image g)) = path_image g"
  using Jordan_inside_outside
  by (simp add: assms convex_hull_eq_closure_inside convex_interior_closure frontier_def)

lemma frontier_convex_hull_subset_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    "path_image g \<subseteq> frontier (convex hull (path_image g))"
  shows "frontier (convex hull path_image g) \<subseteq> path_image g"
proof -
      \<comment> \<open>The interior of the convex hull is connected, bounded, and disjoint from @{term "path_image g"}\<close>
  have "interior (convex hull (path_image g)) \<inter> path_image g = {}"
    using assms(3) frontier_def by auto
  moreover have "connected (interior (convex hull (path_image g)))"
    by (simp add: convex_connected)
  moreover have "inside (path_image g) \<subseteq> convex hull path_image g"
    by (metis Un_subset_iff compl_le_swap2 convex_convex_hull hull_subset
        outside_subset_convex union_with_inside)
  ultimately have int_inside: "interior (convex hull (path_image g)) \<subseteq> inside (path_image g)"
    using Jordan_inside_outside[OF \<open>simple_path g\<close>] assms
    by (smt (verit) connected_Int_frontier diff_shunt inf.commute interior_Int
        interior_eq le_iff_inf)
  have "- (convex hull (path_image g)) \<subseteq> outside (path_image g)"
    by (simp add: hull_subset outside_subset_convex)
  hence inside_sub: "inside (path_image g) \<subseteq> convex hull (path_image g)"
    by (metis Un_subset_iff compl_le_swap2 union_with_inside)
      \<comment> \<open>Since @{term "inside (path_image g)"} is open and contained in the convex hull, it lies in the interior of the hull\<close>
  have "inside (path_image g) \<subseteq> interior (convex hull (path_image g))"
    by (simp add: Jordan_inside_outside assms inside_sub interior_maximal)
  with assms show ?thesis
    using frontier_convex_hull_eq_path_image int_inside by auto
qed

locale W =
  fixes f f' :: "real \<Rightarrow> real" and a::real
  assumes f'hsd: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and feq: "f (2*pi) = f 0"
    and f0: "(f has_integral 0) {0..2*pi}"
    and f'2: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..2*pi}"
    and a: "0 \<le> a" "a < pi" "f (a + pi) = f a"

begin

definition g where "g \<equiv> \<lambda>x. (f x - f a)\<^sup>2 / tan (x - a)"
definition g' where "g' \<equiv> \<lambda>x. (f' x)\<^sup>2 - (f x - f a)\<^sup>2 - (f' x - (f x - f a) / tan (x - a))\<^sup>2"

lemma f': \<open>f' integrable_on {0..2*pi}\<close>
  using f'hsd [of \<open>2*pi\<close>] by fastforce

lemma f'abs: \<open>f' absolutely_integrable_on {0..2*pi}\<close>
proof (intro f' absolutely_integrable_integrable_bound)
  show \<open>norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close> for x
  proof -
    have \<open>0 \<le> (1 - f' x)\<^sup>2\<close> and \<open>0 \<le> (1 + f' x)\<^sup>2\<close>
      by (auto simp: power2_eq_square)
    then show ?thesis
      by (auto simp: power2_eq_square abs_le_iff algebra_simps)
  qed
  show \<open>(\<lambda>x. 1 + (f' x)\<^sup>2) integrable_on {0..2*pi}\<close>
    using integrable_add [OF integrable_const_ivl f'2] by simp
qed

lemma contf: \<open>continuous_on {0..2*pi} f\<close>
proof (rule continuous_on_eq)
  show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
    by (intro continuous_on_add indefinite_integral_continuous_1 [OF f'] continuous_on_const)
  show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
    using f'hsd by (auto simp: has_integral_integrable_integral)
qed

text \<open>The integral over completely trouble-free intervals.\<close>
lemma trouble_free: "(g' has_integral g d - g c) {c..d}"
  if "c \<le> d"
    and sub_cd: "{c..d} \<subseteq> {0..2*pi}"
    and sin_nz: "\<And>x. x \<in> {c..d} \<Longrightarrow> sin (x - a) \<noteq> 0"
  for c d
proof -
  have f'_int: "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
                   ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
    if xcd: "x \<in> {c..d}" for x
  proof -
    have "c \<le> x" and xd: "x \<le> d" and sub_cx: "{c..x} \<subseteq> {0..2*pi}" 
      using xcd \<open>c \<le> d\<close>  sub_cd by auto
    have ac_f: "absolutely_continuous_on {0..2*pi} f"
      using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
    have ac_sq: "absolutely_continuous_on {c..x} (\<lambda>t. (f t - f a)\<^sup>2)"
      unfolding power2_eq_square using absolutely_continuous_on_subset ac_f sub_cx 
      by(intro continuous_intros) fastforce+
    obtain k where negk: "negligible k"
      and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
          ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
      using f' has_vector_derivative_indefinite_integral by blast
    have deriv_sq: "((\<lambda>t. (f t - f a)\<^sup>2) has_vector_derivative 2 * (f t - f a) * f' t) (at t within {c..x})"
      if "t \<in> {c..x} - k" for t
    proof -
      have hvd_int: "((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
        using derivf that sub_cx by auto
      have "((\<lambda>u. f u - f 0) has_vector_derivative f' t) (at t within {0..2*pi})"
      proof (rule has_vector_derivative_transform_within[OF hvd_int])
        fix u assume "u \<in> {0..2*pi}" "dist u t < 1"
        then show "integral {0..u} f' = f u - f 0"
          using f'hsd by blast
      qed (use that sub_cx in auto)
      then have fderiv: "(f has_vector_derivative f' t) (at t within {c..x})"
        using has_vector_derivative_diff_const has_vector_derivative_within_subset sub_cx by blast
      then show ?thesis
        unfolding power2_eq_square has_vector_derivative_def
        by - (rule derivative_eq_intros | simp add: algebra_simps)+
    qed
    show ?thesis
      using fundamental_theorem_of_calculus_absolutely_continuous [OF negk \<open>c \<le> x\<close> ac_sq deriv_sq] by simp
  qed
  text \<open>Apply integration by parts with
      \<^item> \<open>\<lambda>x. (f x - f a)²\<close> and its derivative \<open>\<lambda>x. 2 * (f x - f a) * f' x\<close>
      \<^item> \<open>\<lambda>x. inverse (tan (x - a))\<close> and its derivative \<open>\<lambda>x. - inverse (sin (x - a))²\<close>\<close>
  have ibp_int: "((\<lambda>x. (f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)))
      has_integral ((f y - f a)\<^sup>2 * inverse (tan (y - a)) -
                    (f c - f a)\<^sup>2 * inverse (tan (c - a)))) {c..y}"
    if "y \<in> {c..d}" for y
  proof (intro f'_int absolute_real_integration_by_parts_sum(2))
    have f'_abs_cd: "f' absolutely_integrable_on {c..d}"
      using absolutely_integrable_on_subinterval[OF f'abs sub_cd] .
    have cont_ffa: "continuous_on {c..d} (\<lambda>x. 2 * (f x - f a))"
      using sub_cd by (intro continuous_intros continuous_on_subset [OF contf]) auto
    have meas: "(\<lambda>x. 2 * (f x - f a)) \<in> borel_measurable (lebesgue_on {c..d})"
      using cont_ffa by (intro continuous_imp_measurable_on_sets_lebesgue) auto
    have bdd: "bounded ((\<lambda>x. 2 * (f x - f a)) ` {c..d})"
      using cont_ffa compact_Icc compact_continuous_image compact_imp_bounded by blast
    show "(\<lambda>x. 2 * (f x - f a) * f' x) absolutely_integrable_on {c..d}"
      using absolutely_integrable_bounded_measurable_product_real bdd f'_abs_cd meas by auto
    show "(\<lambda>x. - inverse ((sin (x - a))\<^sup>2)) absolutely_integrable_on {c..d}"
      by (intro absolutely_integrable_continuous_real continuous_intros) (use sin_nz in auto)
    show "((\<lambda>t. - inverse ((sin (t-a))\<^sup>2)) has_integral
            (inverse (tan (x - a)) - inverse (tan (c - a)))) {c..x}"
      if "x \<in> {c..d}" for x 
    proof -
      have "c \<le> x" and sub_cx: "{c..x} \<subseteq> {c..d}"
        using that by auto
      have inv_tan_eq: "inverse (tan (t-a)) = cos (t-a) / sin (t-a)"
        if "t \<in> {c..x}" for t
        by (simp add: Multiseries_Expansion.tan_conv_sin_cos)
      have deriv: "((\<lambda>t. cos (t-a) / sin (t-a)) has_vector_derivative
                    - inverse ((sin (t-a))\<^sup>2)) (at t within {c..x})"
        if "t \<in> {c..x}" for t
      proof -
        have sin_nz_t: "sin (t-a) \<noteq> 0" using sin_nz that sub_cx by auto
        have "((\<lambda>t. cos (t-a) / sin (t-a)) has_real_derivative
              (- sin (t-a) * sin (t-a) - cos (t-a) * cos (t-a)) / (sin (t-a) * sin (t-a)))
              (at t within {c..x})"
          by (intro derivative_eq_intros | simp add: sin_nz_t)+
        also have "(- sin (t-a) * sin (t-a) - cos (t-a) * cos (t-a)) / (sin (t-a) * sin (t-a))
                 = - inverse ((sin (t-a))\<^sup>2)"
          using sin_cos_squared_add3 [of "t-a"]
          by (simp (no_asm_simp) add: divide_simps power2_eq_square)
        finally show ?thesis
          by (simp add: has_real_derivative_iff_has_vector_derivative)
      qed
        \<comment> \<open>Apply FTC\<close>
      show ?thesis
        using fundamental_theorem_of_calculus[OF _ deriv] inv_tan_eq inv_tan_eq \<open>c \<le> x\<close>
        by simp
    qed
    show "y \<in> {c..d}" using that .
  qed (use \<open>c \<le> d\<close> in auto)
  have integrand_eq: "(f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)) = g' x"
    if "x \<in> {c..d}" for x
  proof -
    have snz: "sin (x - a) \<noteq> 0" "(sin (x - a))\<^sup>2 \<noteq> 0" using sin_nz that by auto
    let ?F = "f x - f a"
    let ?s = "sin (x - a)"
    let ?c = "cos (x - a)"
    have sc1: "?s\<^sup>2 + ?c\<^sup>2 = 1"
      using sin_cos_squared_add[of "x - a"] by simp
    have "((f x - f a)\<^sup>2 * (- inverse (?s\<^sup>2)) + 2 * (f x - f a) * f' x * inverse (tan (x - a))) * ?s\<^sup>2
          = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      using snz by (simp add: tan_def field_simps power2_eq_square)
    moreover have "g' x * ?s\<^sup>2 = ((f' x)\<^sup>2 - ?F\<^sup>2) * ?s\<^sup>2 - (f' x * ?s - ?F * ?c)\<^sup>2"
      using snz by (simp add: g'_def tan_def field_simps)
    moreover have "\<dots>  = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      using sc1 by algebra 
    ultimately show ?thesis using snz
      by (metis mult_right_cancel)
  qed
    \<comment> \<open>Combine using \<open>has_integral_eq\<close>\<close>
  show ?thesis
    using has_integral_eq ibp_int integrand_eq unfolding g_def divide_inverse
    by (metis (no_types, lifting) atLeastAtMost_iff order.refl that(1))
qed

text \<open>Continuity of @{term g}.\<close>
lemma g_cont: "continuous_on {0..2*pi} g"
  unfolding continuous_on_eq_continuous_within
proof
  fix c assume c_in: "c \<in> {0..2*pi}"
  show "continuous (at c within {0..2*pi}) g"
  proof (cases "sin (c - a) = 0")
    case False
      \<comment> \<open>When $\sin(c - a) \neq 0$, @{term g} is a quotient of continuous functions.\<close>
    have g_eq: "g x = (f x - f a)\<^sup>2 * cos (x - a) / sin (x - a)" for x
      unfolding g_def tan_def by (simp add: field_simps)
    have "continuous (at c within {0..2*pi}) f"
      using contf c_in continuous_on_eq_continuous_within by blast
    then show ?thesis unfolding g_eq
      using False by (auto simp: continuous_intros)
  next
    case True
      \<comment> \<open>When $\sin(c - a) = 0$, we have $g(c) = 0$ and need to show $g(x) \to 0$.\<close>
    then obtain n :: int where npi: "c - a = of_int n * pi"
      using sin_zero_iff_int2 by auto
    have "of_int n \<ge> -a / pi" "of_int n \<le> (2 * pi - a) / pi"
      using a npi c_in pi_gt_zero by (simp_all add: field_simps)
    moreover have "-a / pi > -1" using a pi_gt_zero by (simp add: field_simps)
    moreover have "(2 * pi - a) / pi < 3"
      using a pi_gt_zero by (auto simp: divide_simps)
    ultimately have "n = 0 \<or> n = 1 \<or> n = 2"
      by linarith
    then have fca: "f c = f a"
    proof (elim disjE)
      assume "n = 2"
      then have "c = a + 2 * pi" using npi by (simp add: algebra_simps)
      with c_in a pi_gt_zero have "a = 0" by auto
      thus "f c = f a" using \<open>c = a + 2 * pi\<close> feq by simp
    qed (use npi a in \<open>auto simp: algebra_simps\<close>)
    have gc0: "g c = 0"
      unfolding g_def using fca by simp
        \<comment> \<open>Derive $\tan(x - a) = \tan(x - c)$ from $\sin(c - a) = 0$.\<close>
    from True obtain n :: int where npi: "c - a = of_int n * pi"
      using sin_zero_iff_int2 by auto
    have tan_eq: "tan (x - a) = tan (x - c)" for x
      by (metis npi diff_add_cancel diff_diff_eq2 tan_periodic_int)
    have g_eq2: "g x = (f x - f c)\<^sup>2 * cos (x - c) / sin (x - c)" for x
      unfolding g_def by (metis fca divide_divide_eq_right local.tan_eq tan_def)
        \<comment> \<open>Cauchy--Schwarz bound: $(f(x) - f(c))^2 \le |x - c| \cdot \int_c^x (f')^2$.\<close>
    have cs_bound: "(f x - f c)\<^sup>2 \<le> \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
      if xin: "x \<in> {0..2*pi}" for x
    proof -
      have f'_int_sub: "f' integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
        using integrable_subinterval_real[OF set_lebesgue_integral_eq_integral(1)[OF f'abs] that] .
      have f'2_int_sub: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
        using integrable_subinterval_real[OF f'2 that] .
          \<comment> \<open>Helper: the FTC gives $f(b) - f(a) = \int_a^b f'$ for $a, b \in \{0..2\pi\}$\<close>
      have ftc_sub: "f b - f a = integral {a..b} f'"
        if "a \<in> {0..2*pi}" "b \<in> {0..2*pi}" "a \<le> b" for a b
      proof -
        have "integral {0..a} f' + integral {a..b} f' = integral {0..b} f'"
          by (meson Henstock_Kurzweil_Integration.integral_combine atLeastAtMost_iff f'hsd
              has_integral_integrable that)
        moreover have "integral {0..a} f' = f a - f 0" and "integral {0..b} f' = f b - f 0"
          using f'hsd that by (auto simp: has_integral_integrable_integral)
        ultimately show ?thesis by linarith
      qed
        \<comment> \<open>Helper: Cauchy--Schwarz $\left(\int_I f'\right)^2 \le (b-a) \cdot \int_I (f')^2$ for $I = \{a..b\} \subseteq \{0..2\pi\}$\<close>
      have cs_sub: "(integral {a..b} f')\<^sup>2 \<le> (b-a) * integral {a..b} (\<lambda>t. (f' t)\<^sup>2)"
        if sub: "{a..b} \<subseteq> {0..2*pi}" and ab: "a < b" for a b
      proof -
        define \<mu> where "\<mu> \<equiv> integral {a..b} f' / (b-a)"
        have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" by (rule f'2_int_sub[OF sub])
        have int1: "(\<lambda>t. - (2 * \<mu>) * f' t) integrable_on {a..b}"
          using f'_int_sub integrable_on_mult_right sub by blast
        have "0 \<le> integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2)"
          by (metis eq_integralD has_integral_nonneg order_refl zero_le_power2)
        also have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                integral {a..b} (\<lambda>t. (f' t)\<^sup>2) + (- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b-a))"
        proof -
          have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                  integral {a..b} (\<lambda>t. (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2))"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = integral {a..b} (\<lambda>t. (f' t)\<^sup>2) + integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2)"
            by (rule integral_add[OF f'2I integrable_add[OF int1 integrable_const_ivl]])
          also have "integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2) =
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t) + integral {a..b} (\<lambda>t. \<mu>\<^sup>2)"
            by (rule integral_add[OF int1 integrable_const_ivl])
          finally show ?thesis using ab by simp
        qed
        also have "- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b-a) = - (integral {a..b} f')\<^sup>2 / (b-a)"
          using ab unfolding \<mu>_def by (simp add: power2_eq_square divide_simps)
        finally show ?thesis using ab by (simp add: pos_divide_le_eq mult.commute)
      qed
      show ?thesis
      proof (cases "c \<le> x")
        case True
        show ?thesis using cs_sub \<open>c \<le> x\<close> c_in xin ftc_sub by fastforce
      next
        case False
        hence \<section>: "x < c" "{x..c} \<subseteq> {0..2*pi}" using c_in xin by auto
        then show ?thesis
          by (simp add: cs_sub ftc_sub power2_commute)
      qed
    qed
      \<comment> \<open>The integral of $(f')^2$ over a shrinking interval tends to $0$.\<close>
    define F where "F \<equiv> \<lambda>x. integral {0..x} (\<lambda>t. (f' t)\<^sup>2)"
    have F_cont: "continuous_on {0..2*pi} F"
      unfolding F_def by (rule indefinite_integral_continuous_1[OF f'2])
    have F_eq: "integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2) = \<bar>F x - F c\<bar>"
      if "x \<in> {0..2*pi}" for x
    proof (cases "c \<le> x")
      case True
      have sub: "{c..x} \<subseteq> {0..2*pi}" using c_in that True by auto
      have "integral {0..c} (\<lambda>t. (f' t)\<^sup>2) + integral {c..x} (\<lambda>t. (f' t)\<^sup>2) =
                integral {0..x} (\<lambda>t. (f' t)\<^sup>2)"
        by (metis Henstock_Kurzweil_Integration.integral_combine True atLeastatMost_subset_iff f'2
            integrable_on_subinterval order_refl sub)
      hence "integral {c..x} (\<lambda>t. (f' t)\<^sup>2) = F x - F c"
        unfolding F_def by linarith
      moreover have "0 \<le> integral {c..x} (\<lambda>t. (f' t)\<^sup>2)"
        by (metis integral_nonneg not_integrable_integral order.refl zero_le_power2)
      ultimately show ?thesis using True by (simp add: min_def max_def)
    next
      case False
      hence xc: "x \<le> c" by simp
      have sub: "{x..c} \<subseteq> {0..2*pi}" using c_in that xc by auto
      have "integral {0..x} (\<lambda>t. (f' t)\<^sup>2) + integral {x..c} (\<lambda>t. (f' t)\<^sup>2) 
                  = integral {0..c} (\<lambda>t. (f' t)\<^sup>2)"
        by (metis Henstock_Kurzweil_Integration.integral_combine atLeastatMost_subset_iff f'2
            integrable_subinterval_real order.refl sub xc)
      moreover have "0 \<le> integral {x..c} (\<lambda>t. (f' t)\<^sup>2)"
        by (metis integral_nonneg not_integrable_integral order.refl zero_le_power2)
      ultimately show ?thesis using xc by (simp add: F_def min_def max_def)
    qed
    have "((\<lambda>x. \<bar>F x - F c\<bar>) \<longlongrightarrow> 0) (at c within {0..2*pi})"
      by (metis F_cont LIM_zero_iff c_in continuous_on_def tendsto_rabs_zero)
    then have f'2_int_tends_0: "((\<lambda>x. integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
      by (smt (verit, best) F_eq Lim_cong_within)
    have "\<forall>\<^sub>F x in at c. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> < 2"
      by real_asymp
    then have sinc_ratio_bounded:
      "\<forall>\<^sub>F x in at c within {0..2*pi}. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2"
      by (metis (no_types, lifting) UNIV_I eventually_at_topological less_imp_le)
        \<comment> \<open>Now combine everything.\<close>
    show ?thesis 
      unfolding continuous_within gc0
    proof (rule Lim_null_comparison[where g = "\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"])
      have mem: "\<forall>\<^sub>F x in at c within {0..2*pi}. x \<in> {0..2*pi}"
        unfolding at_within_def eventually_inf_principal by simp
      show "\<forall>\<^sub>F x in at c within {0..2*pi}. norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
      proof (rule eventually_mono[OF eventually_conj[OF sinc_ratio_bounded mem]])
        fix x assume H: "\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2 \<and> x \<in> {0..2*pi}"
        have "\<bar>g x\<bar> = (f x - f c)\<^sup>2 * \<bar>cos (x - c)\<bar> / \<bar>sin (x - c)\<bar>"
          using g_eq2 by (simp add: abs_mult)
        also have "\<dots> \<le> (f x - f c)\<^sup>2 * 1 / \<bar>sin (x - c)\<bar>"
          by (meson abs_cos_le_one abs_ge_zero divide_right_mono
              ordered_comm_semiring_class.comm_mult_left_mono zero_le_power2)
        also have "\<dots> = (f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar>" by simp
        also have "\<dots> \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
        proof -
          have sub: "{min c x..max c x} \<subseteq> {0..2*pi}" using c_in H by auto
          have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {min c x..max c x}"
            by (rule integrable_subinterval_real[OF f'2 sub])
          show ?thesis
          proof (cases "sin (x - c) = 0")
            case False
            define I where "I = integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
            have Ige: "I \<ge> 0"
              unfolding I_def by (rule integral_nonneg[OF f'2I]) auto
            have "(f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar> \<le> \<bar>x - c\<bar> * I / \<bar>sin (x - c)\<bar>"
              using H by (simp add: I_def cs_bound divide_right_mono)
            also have "\<dots> = (\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar>) * I"
              by (simp add: field_simps)
            also have "\<dots> \<le> 2 * I"
              by (meson H Ige mult_mono order.refl zero_le_numeral)
            finally show ?thesis unfolding I_def .
          qed (use integral_nonneg[OF f'2I] in auto)
        qed
        finally show "norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)" by simp
      qed
      show "((\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
        using tendsto_mult_right_zero[OF f'2_int_tends_0] by simp
    qed
  qed
qed

text \<open>The integral over mainly trouble-free intervals:
    we only need \<open>sin(x - a) \<noteq> 0\<close> on the open interior, allowing zeros at the endpoints.\<close>
lemma mainly_trouble_free: 
  assumes "c \<le> d" and cd_sub: "{c..d} \<subseteq> {0..2*pi}" and sin_nz: "\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0"
  shows "(g' has_integral g d - g c) {c..d}"
proof -
  have "g' absolutely_integrable_on {c..d}"
  proof -
    have f'2_abs: "(\<lambda>x. (f' x)\<^sup>2) absolutely_integrable_on {0..2*pi}"
      by (simp add: absolutely_integrable_on_def f'2)
    have g'_int_sub: "g' integrable_on {u..v}" if "{u..v} \<subseteq> {c<..<d}" for u v
    proof (cases "u \<le> v")
      case True
      show ?thesis
        using has_integral_integrable[OF trouble_free[OF True]] sin_nz that cd_sub by force
    qed (simp add: not_le integrable_on_empty)
    have g'_int: "g' integrable_on {c'..d'}" if "{c'..d'} \<subseteq> {c<..<d}" for c' d'
      using \<open>{c'..d'} \<subseteq> {c<..<d}\<close> g'_int_sub by blast
    have abs_g_cont: \<open>continuous_on {0..2 * pi} (\<lambda>x. \<bar>g x\<bar>)\<close>
      by (intro continuous_intros g_cont)
    obtain h where h_abs: "h absolutely_integrable_on {c..d}" 
      and h_bounded: "(\<forall>x\<in>{c..d}. g' x \<le> h x) \<or> (\<forall>x\<in>{c..d}. h x \<le> g' x)"
      using absolutely_integrable_on_subinterval[OF f'2_abs cd_sub] by (simp add: g'_def) 
    show ?thesis
    proof (intro g'_int absolutely_integrable_improper [of c d , unfolded box_real])
      obtain w where "0 \<le> w" "w \<le> 2*pi" and w: "\<forall>y. 0\<le>y \<longrightarrow> y \<le> 2*pi \<longrightarrow> \<bar>g y\<bar> \<le> \<bar>g w\<bar>"
        using continuous_attains_sup [of \<open>{0..2*pi}\<close> \<open>\<lambda>x. \<bar>g x\<bar>\<close>]
        by (metis Arg2pi abs_g_cont atLeastAtMost_iff compact_Icc empty_iff less_eq_real_def)
      show "bounded {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
      proof (rule boundedI)
        fix x assume "x \<in> {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
        then obtain c' d' where cd': "{c'..d'} \<subseteq> {c<..<d}" and xeq: "x = integral {c'..d'} g'"
          by auto
        show "norm x \<le> 2 * \<bar>g w\<bar>"
        proof (cases "c' \<le> d'")
          case True
          have sub_2pi: "{c'..d'} \<subseteq> {0..2*pi}"
            using cd' cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
          have "sin (t-a) \<noteq> 0" if "t \<in> {c'..d'}" for t
            using that cd' sin_nz by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
          then have "integral {c'..d'} g' = g d' - g c'"
            using True sub_2pi trouble_free by blast
          then have "\<bar>x\<bar> \<le> \<bar>g d'\<bar> + \<bar>g c'\<bar>"
            using xeq by linarith
          also have "\<dots> \<le> \<bar>g w\<bar> + \<bar>g w\<bar>"
            by (metis True w add_mono atLeastatMost_subset_iff order_trans sub_2pi)
          also have "\<dots> = 2 * \<bar>g w\<bar>" by algebra
          finally show ?thesis by (simp add: xeq)
        qed (simp add: xeq)
      qed
    qed (use h_abs h_bounded in auto)
  qed
  have g'_int: "g' integrable_on {c..d}"
    using \<open>g' absolutely_integrable_on {c..d}\<close> set_lebesgue_integral_eq_integral by blast
  have g_cont_cd: "continuous_on {c..d} g"
    using continuous_on_subset[OF g_cont cd_sub] .
  have "integral {c..d} g' = g d - g c"
  proof (cases "c < d")
    case False with \<open>c \<le> d\<close> show ?thesis by simp
  next
    case True
      \<comment> \<open>Pick sequences $c_n \to c$ and $d_n \to d$ from inside $(c,d)$\<close>
    define c_n where "c_n \<equiv> \<lambda>n. c + (d - c) / (real n + 2)"
    define d_n where "d_n \<equiv> \<lambda>n. d - (d - c) / (real n + 2)"
    have pos: "0 < (d - c) / (real n + 2)" for n
      using True by auto
    have lt_dc: "(d - c) / (real n + 2) < d - c" for n
      using True by (simp add: divide_less_eq)
    have c_n_le_d_n: "c_n n \<le> d_n n" for n
    proof -
      have "c * real n \<le> d * real n"
        using True by (intro mult_right_mono) auto
      then have "2 * ((d - c) / (real n + 2)) \<le> d - c"
        using True by (simp add: field_simps)
      then show ?thesis unfolding c_n_def d_n_def by linarith
    qed
    have frac_lim: "(\<lambda>n. (d - c) / (real n + 2)) \<longlonglongrightarrow> 0"
    proof (rule real_tendsto_sandwich)
      show "\<forall>\<^sub>F n in sequentially. 0 \<le> (d - c) / (real n + 2)"
        using True by (intro always_eventually allI) (auto simp: field_simps)
      show "\<forall>\<^sub>F n in sequentially. (d - c) / (real n + 2) \<le> (d - c) * (1 / real n)"
        using True by (intro eventually_sequentiallyI[of 1]) (auto simp: field_simps)
      show "(\<lambda>_. (0::real)) \<longlonglongrightarrow> 0" by simp
      show "(\<lambda>n. (d - c) * (1 / real n)) \<longlonglongrightarrow> 0"
        using tendsto_mult_right_zero[OF lim_inverse_n'] by simp
    qed
    have c_n_lim: "c_n \<longlonglongrightarrow> c"
      unfolding c_n_def using tendsto_add[OF tendsto_const frac_lim] by simp
    have d_n_lim: "d_n \<longlonglongrightarrow> d"
      unfolding d_n_def using tendsto_diff[OF tendsto_const frac_lim] by simp
        \<comment> \<open>On each $\{c_n..d_n\}$, \<open>trouble_free\<close> applies\<close>
    have c_n_in: "c_n n \<in> {c<..<d}" and d_n_in: "d_n n \<in> {c<..<d}" for n
      using pos[of n] lt_dc[of n] unfolding c_n_def d_n_def by auto
    have sub_n: "{c_n n..d_n n} \<subseteq> {c<..<d}" for n
      using c_n_in[of n] d_n_in[of n] c_n_le_d_n[of n] by auto
    have sub_2pi_n: "{c_n n..d_n n} \<subseteq> {0..2*pi}" for n
      using sub_n[of n] cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
    have sin_nz_n: "sin (x - a) \<noteq> 0" if "x \<in> {c_n n..d_n n}" for n x
      using that sub_n[of n] sin_nz
      by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
    have tf_n: "(g' has_integral g (d_n n) - g (c_n n)) {c_n n..d_n n}" for n
      using trouble_free[OF c_n_le_d_n sub_2pi_n sin_nz_n] .
    have int_n: "integral {c_n n..d_n n} g' = g (d_n n) - g (c_n n)" for n
      using tf_n[of n] by (rule integral_unique)
    have int_lim: "(\<lambda>n. integral {c_n n..d_n n} g') \<longlonglongrightarrow> integral {c..d} g'"
    proof -
      have indef_cont: "continuous_on {c..d} (\<lambda>x. integral {c..x} g')"
        by (rule indefinite_integral_continuous_1[OF g'_int])
      have c_n_cd: "c_n n \<in> {c..d}" for n
        using c_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
      have d_n_cd: "d_n n \<in> {c..d}" for n
        using d_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
      have split: "integral {c_n n..d_n n} g' = integral {c..d_n n} g' - integral {c..c_n n} g'" for n
      proof -
        have cn_le: "c \<le> c_n n" using c_n_in[of n] by auto
        have int_cdn: "g' integrable_on {c..d_n n}"
          by (rule integrable_subinterval_real[OF g'_int]) (use d_n_cd[of n] \<open>c \<le> d\<close> in auto)
        have "integral {c..c_n n} g' + integral {c_n n..d_n n} g' = integral {c..d_n n} g'"
          by (rule Henstock_Kurzweil_Integration.integral_combine[OF cn_le c_n_le_d_n int_cdn])
        then show ?thesis by linarith
      qed
      have "(\<lambda>n. integral {c..d_n n} g') \<longlonglongrightarrow> integral {c..d} g'"
        by (rule continuous_on_tendsto_compose[OF indef_cont d_n_lim])
          (use d_n_cd \<open>c \<le> d\<close> in \<open>auto intro: always_eventually\<close>)
      moreover have "(\<lambda>n. integral {c..c_n n} g') \<longlonglongrightarrow> integral {c..c} g'"
        by (rule continuous_on_tendsto_compose[OF indef_cont c_n_lim])
          (use c_n_cd \<open>c \<le> d\<close> in \<open>auto intro: always_eventually\<close>)
      moreover have "integral {c..c} g' = 0" by simp
      ultimately have "(\<lambda>n. integral {c..d_n n} g' - integral {c..c_n n} g') \<longlonglongrightarrow> integral {c..d} g' - 0"
        by (intro tendsto_diff) simp_all
      then show ?thesis using split by simp
    qed
    moreover have "(\<lambda>n. g (d_n n) - g (c_n n)) \<longlonglongrightarrow> g d - g c"
    proof (intro tendsto_diff)
      obtain d_n_cd: "d_n n \<in> {c..d}" and c_n_cd: "c_n n \<in> {c..d}" for n
        using c_n_in d_n_in less_eq_real_def by force
      show "(\<lambda>n. g (d_n n)) \<longlonglongrightarrow> g d"
        by (rule continuous_on_tendsto_compose[OF g_cont_cd d_n_lim])
          (use d_n_cd \<open>c \<le> d\<close> in \<open>auto intro: always_eventually\<close>)
      show "(\<lambda>n. g (c_n n)) \<longlonglongrightarrow> g c"
        by (rule continuous_on_tendsto_compose[OF g_cont_cd c_n_lim])
          (use c_n_cd \<open>c \<le> d\<close> in \<open>auto intro: always_eventually\<close>)
    qed
    ultimately show ?thesis
      using int_n LIMSEQ_unique by auto
  qed
  then show ?thesis
    using integrable_integral[OF g'_int] by auto
qed

end

theorem Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes f'hsd: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and feq: "f (2*pi) = f 0"
    and f0: "(f has_integral 0) {0..2*pi}"
    and f'2: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..2*pi}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
         \<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
proof -
  obtain a where a: "0 \<le> a" "a < pi" "f (a + pi) = f a"
  proof -
    have contf: \<open>continuous_on {0..2*pi} f\<close>
    proof (rule continuous_on_eq)
      show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
        using f'hsd [of \<open>2*pi\<close>] 
        by (intro continuous_on_add indefinite_integral_continuous_1  continuous_on_const) auto
      show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
        using f'hsd by (auto simp: has_integral_integrable_integral)
    qed
    define h where "h \<equiv> \<lambda>x. f (x + pi) - f x"
    have hcont: "continuous_on {0..pi} h"
      unfolding h_def
      by (intro continuous_intros continuous_on_compose2 [OF contf]) auto
    have heq: "h 0 + h pi = 0"
      unfolding h_def using feq by simp
    have iv: "is_interval (h ` {0..pi})"
      using is_interval_connected_1 connected_continuous_image [OF hcont connected_Icc]
      by blast
    have"h 0 \<in> h ` {0..pi}"  "h pi \<in> h ` {0..pi}"
      using pi_gt_zero by auto
    with heq obtain a where "a \<in> {0..pi}" "h a = 0"
      by (smt (verit, best) imageE is_interval_1 iv)
    show thesis
    proof (cases "a = pi")
      case True
      then have "h 0 = 0" using heq \<open>h a = 0\<close> by auto
      then show thesis using that [of 0] pi_gt_zero by (auto simp: h_def)
    next
      case False
      then show thesis using that [of a] \<open>a \<in> {0..pi}\<close> \<open>h a = 0\<close>
        by (auto simp: h_def)
    qed
  qed

  interpret W f f' a
    using W.intro a assms by blast

  show "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_on_power contf)

\<comment> \<open>Zeros of sine on this interval occur at a and a plus pi.\<close>
  have sin_nz_1: "sin (x - a) \<noteq> 0" if "a + pi < x" "x < 2*pi" for x
    by (smt (verit) \<open>0 \<le> a\<close> sin_lt_zero that)
  have sin_nz_2: "sin (x - a) \<noteq> 0" if "a < x" "x < a + pi" for x
    by (smt (verit, ccfv_threshold) sin_gt_zero that)
  have sin_nz_3: "sin (x - a) \<noteq> 0" if "0 < x" "x < a" for x
    using \<open>a < pi\<close> sin_zero_pi_iff that by auto
      \<comment> \<open>Apply \<open>mainly_trouble_free\<close> on three intervals.\<close>
  have int1: "(g' has_integral g (2*pi) - g (a + pi)) {a + pi..2*pi}"
    by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_1 in auto)
  have int2: "(g' has_integral g (a + pi) - g a) {a..a + pi}"
    by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_2 in auto)
  have int3: "(g' has_integral g a - g 0) {0..a}"
    by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_3 in auto)
  have api_le: "a \<le> a + pi" and api_le2: "a + pi \<le> 2*pi"
    using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
  have a_le_2pi: "a \<le> 2*pi" using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
  have int12: "(g' has_integral (g (a + pi) - g a) + (g (2*pi) - g (a + pi))) {a..2*pi}"
    by (rule has_integral_combine[OF api_le api_le2 int2 int1])
  have "g (2*pi) = g 0"
    unfolding g_def using feq by (simp add: tan_def)
  hence g'_zero: "(g' has_integral 0) {0..2*pi}"
    using has_integral_combine[OF \<open>0 \<le> a\<close> a_le_2pi int3 int12] by (simp add: algebra_simps)
      \<comment> \<open>Extract the inequality from $\int g' = 0$.\<close>
  have ffa_int: "(\<lambda>x. (f x - f a)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_intros contf)
  have diff_int: "((\<lambda>x. (f' x)\<^sup>2 - g' x) has_integral integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) - 0) {0..2*pi}"
    by (rule has_integral_diff[OF integrable_integral[OF f'2] g'_zero])
  have diff_ge: "(f' x)\<^sup>2 - g' x \<ge> (f x - f a)\<^sup>2" for x
     by (simp add: g'_def zero_le_power2)
  have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x)"
    by (rule integral_le[OF ffa_int]) (use diff_int has_integral_integrable_integral in \<open>auto intro: diff_ge\<close>)
  also have int_eq: "\<dots> = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    using diff_int has_integral_integrable_integral by auto
  finally have ineq_ffa: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)" .
      \<comment> \<open>Show $\int f(x)^2 \le \int (f(x)-f(a))^2$ using $\int f = 0$.\<close>
  have "(f x)\<^sup>2 \<le> (f x - f a)\<^sup>2 + 2 * f a * f x - (f a)\<^sup>2" for x
    by (simp add: power2_eq_square algebra_simps)
  have fx2_int: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_intros contf)
  have ffa_2fa_int: "(\<lambda>x. 2 * f a * f x) integrable_on {0..2*pi}"
    using integrable_continuous_interval[OF contf] integrable_on_mult_right by blast
  have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2)"
    by (simp add: power2_eq_square algebra_simps)
  also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) + integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2)"
    by (rule Henstock_Kurzweil_Integration.integral_add)
      (auto intro: integrable_diff fx2_int ffa_2fa_int)
  also have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - integral {0..2*pi} (\<lambda>x. 2 * f a * f x)"
    by (rule Henstock_Kurzweil_Integration.integral_diff[OF fx2_int ffa_2fa_int])
  also have "integral {0..2*pi} (\<lambda>x. 2 * f a * f x) = 0"
    using integral_cmul f0 by (simp add: has_integral_integrable_integral)
  also have "integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2) = (f a)\<^sup>2 * (2*pi)"
    by simp
  finally have ffa_eq: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) 
                      = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) + (f a)\<^sup>2 * (2*pi)"
    by linarith
  then have ffa_ineq': "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2)"
    by auto
  thus "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    using ineq_ffa by linarith
  show "\<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
    if "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    \<comment> \<open>From the equality, all intermediate inequalities are equalities.\<close>
    have fa0: "f a = 0"
      by (smt (verit, best) ffa_ineq' a ffa_eq ineq_ffa mult_eq_0_iff power_eq_0_iff that)
    \<comment> \<open>The "rest" term integrates to 0.\<close>
    define rest where "rest \<equiv> \<lambda>x. f' x - (f x - f a) / tan (x - a)"
    have diff_int: "(\<lambda>x. (f' x)\<^sup>2 - g' x) integrable_on {0..2*pi}"
      using has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
        has_integral_integrable by blast
    have rest_sq_int: "(\<lambda>x. (rest x)\<^sup>2) integrable_on {0..2*pi}"
      using integrable_diff[OF diff_int ffa_int]
      by (simp add: g'_def rest_def)
    have rest_sq_zero: "integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2) = 0"
      using integral_add[OF ffa_int rest_sq_int] that g'_def int_eq 
      by (fastforce simp: rest_def fa0)
    \<comment> \<open>Integral of $c \sin(x - a)$ via the fundamental theorem of calculus.\<close>
    have csin_integral: "integral {u..v} (\<lambda>x. c * sin (x - a)) =
        c * (cos (u - a) - cos (v - a))" if "u \<le> v" for u v c
    proof -
      have "((\<lambda>x. - (c * cos (x - a))) has_real_derivative c * sin (x - a)) (at x)" for x
        by (auto intro!: derivative_eq_intros simp: algebra_simps)
      hence hvd: "((\<lambda>x. - (c * cos (x - a))) has_vector_derivative c * sin (x - a))
        (at x within {u..v})" for x
        by (meson has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
      hence "((\<lambda>x. c * sin (x - a)) has_integral
        (- (c * cos (v - a)) - (- (c * cos (u - a))))) {u..v}"
        using that by (intro fundamental_theorem_of_calculus) auto
      thus ?thesis
        by (simp add: has_integral_integrable_integral algebra_simps)
    qed
    \<comment> \<open>Key fact: on intervals where $\sin(x-a) \neq 0$, @{term f} equals $c \sin(x-a)$.\<close>
    have key_fact: "\<exists>c. \<forall>x\<in>{u..v}. f x = c * sin (x - a)"
      if huv: "0 \<le> u" "u < v" "v \<le> 2*pi"
        and hsin: "\<And>x. x \<in> {u<..<v} \<Longrightarrow> sin (x - a) \<noteq> 0"
      for u v
    proof -
      \<comment> \<open>Open-interval version (to be proved later).\<close>
      \<comment> \<open>Step 1: $\int_u^v \mathit{rest}^2 = 0$ from $\int_0^{2\pi} \mathit{rest}^2 = 0$ and nonnegativity.\<close>
      have rest_sq_sub: "(\<lambda>x. (rest x)\<^sup>2) integrable_on {u..v}"
        using integrable_on_subinterval rest_sq_int that by fastforce
      have "integral {u..v} (\<lambda>x. (rest x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2)"
        by (simp add: huv integral_subset_le rest_sq_int rest_sq_sub)
      moreover have "0 \<le> integral {u..v} (\<lambda>x. (rest x)\<^sup>2)"
        by (simp add: Henstock_Kurzweil_Integration.integral_nonneg rest_sq_sub)
      ultimately have rest_sq_sub_zero: "integral {u..v} (\<lambda>x. (rest x)\<^sup>2) = 0"
        using rest_sq_zero by linarith
          \<comment> \<open>Step 2: $\mathit{rest} = 0$ a.e. on $\{u..v\}$ via Lebesgue theory.\<close>
      have rest_sq_abs: "(\<lambda>x. (rest x)\<^sup>2) absolutely_integrable_on {u..v}"
        by (simp add: absolutely_integrable_on_iff_nonneg rest_sq_sub)
      have rest_sq_leb: "integrable (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2)"
        by (simp add: absolutely_integrable_imp_integrable rest_sq_abs)
      have "integral\<^sup>L (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2) = integral {u..v} (\<lambda>x. (rest x)\<^sup>2)"
        using lebesgue_integral_eq_integral lmeasurable_interval(1) rest_sq_leb by blast 
      hence "integral\<^sup>L (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2) = 0"
        using rest_sq_sub_zero by simp
      hence rest_ae_zero: "AE x in lebesgue_on {u..v}. rest x = 0"
        using integral_nonneg_eq_0_iff_AE[OF rest_sq_leb] by simp
        \<comment> \<open>Step 3: $h(x) = f(x)/\sin(x-a)$ is constant on $(u,v)$.
           For any $\{s..t\} \subseteq (u,v)$, @{term h} is absolutely continuous and $h' = \mathit{rest}/\sin$ a.e.,
           so $h(t) - h(s) = \int_s^t \mathit{rest}/\sin = 0$.\<close>
      have h_const: "f s / sin (s - a) = f t / sin (t-a)"
        if hst: "s \<in> {u<..<v}" "t \<in> {u<..<v}" for s t
      proof (cases "s = t")
        case True thus ?thesis by simp
      next
        case False
          \<comment> \<open>WLOG s < t\<close>
        define s' where "s' = min s t"
        define t' where "t' = max s t"
        have st': "u < s'" "t' < v" "s' < t'"
          using hst False unfolding s'_def t'_def by auto
        have st'_sub: "{s'..t'} \<subseteq> {u<..<v}" and st'_sub2: "{s'..t'} \<subseteq> {0..2*pi}"
          using st' huv by auto
            \<comment> \<open>$\sin(x - a) \neq 0$ on $\{s'..t'\}$\<close>
        have sin_nz_st: "sin (x - a) \<noteq> 0" if "x \<in> {s'..t'}" for x
          using hsin st'_sub that by auto
            \<comment> \<open>$h = f/\sin$ is absolutely continuous on $\{s'..t'\}$\<close>
        define h where "h \<equiv> \<lambda>x. f x / sin (x - a)"
        have ac_f: "absolutely_continuous_on {0..2*pi} f"
          using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
        have ac_f_st: "absolutely_continuous_on {s'..t'} f"
          using absolutely_continuous_on_subset[OF ac_f st'_sub2] .
            \<comment> \<open>$1/\sin(x-a)$ is absolutely continuous on $\{s'..t'\}$ via a Lipschitz bound\<close>
            \<comment> \<open>The derivative $-\cos/\sin^2$ is bounded on $\{s'..t'\}$ since $\sin$ is bounded away from $0$\<close>
        define deriv where "deriv \<equiv> \<lambda>x::real. - cos (x - a) / (sin (x - a))\<^sup>2"
        have cont_deriv: "continuous_on {s'..t'} deriv"
          unfolding deriv_def
          by (intro continuous_intros) (use sin_nz_st in auto)
        have bdd: "bounded (deriv ` {s'..t'})"
          using compact_continuous_image compact_imp_bounded cont_deriv by blast
        then obtain B where B: "\<And>x. x \<in> {s'..t'} \<Longrightarrow> \<bar>deriv x\<bar> \<le> B"
          by (meson bounded_real imageI)
        have lipschitz: "\<bar>inverse (sin (x - a)) - inverse (sin (y - a))\<bar> \<le> B * \<bar>x - y\<bar>"
          if hx: "s' \<le> x" "x \<le> t'" and hy: "s' \<le> y" "y \<le> t'" for x y
        proof -
          have deriv_at: "((\<lambda>x. inverse (sin (x - a))) has_real_derivative deriv z)
                              (at z within {s'..t'})"
            if hz: "z \<in> {s'..t'}" for z
          proof -
            have "((\<lambda>x. sin (x - a)) has_real_derivative cos (z - a)) (at z within {s'..t'})"
              by (intro derivative_eq_intros | simp)+
            moreover have "- (cos (z - a) * inverse (sin (z - a) ^ Suc (Suc 0))) = deriv z"
              unfolding deriv_def power2_eq_square
              by (simp add: field_simps)
            ultimately show ?thesis
              by (metis DERIV_inverse_fun sin_nz_st[OF hz])
          qed
          have "norm (inverse (sin (x - a)) - inverse (sin (y - a))) \<le> B * norm (x - y)"
            using hx hy B deriv_at
            by (intro field_differentiable_bound[OF convex_real_interval(5)]) auto
          then show ?thesis by (simp add: real_norm_def)
        qed
        then have ac_inv_sin: "absolutely_continuous_on {s'..t'} (\<lambda>x. inverse (sin (x - a)))"
          by (intro Lipschitz_imp_absolutely_continuous strip; auto)
            \<comment> \<open>$h = f \cdot (1/\sin)$ is AC on $\{s'..t'\}$\<close>
        have ac_h: "absolutely_continuous_on {s'..t'} h"
          using absolutely_continuous_on_mul[OF ac_f_st ac_inv_sin]
          by (simp add: divide_real_def h_def)
            \<comment> \<open>@{term h} has derivative $\mathit{rest}/\sin$ a.e. on $\{s'..t'\}$\<close>
        obtain k where negk: "negligible k"
          and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
              ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t)
              (at t within {0..2*pi})"
          using f' has_vector_derivative_indefinite_integral by blast
        have f_eq: "f t = f 0 + integral {0..t} f'" if "t \<in> {0..2*pi}" for t
          using f'hsd[OF that] by (auto simp: has_integral_integrable_integral)
        have fderiv: "(f has_vector_derivative f' t) (at t within {s'..t'})"
          if "t \<in> {s'..t'} - k" for t
        proof -
          have t02: "t \<in> {0..2*pi}" and "t \<in> {0..2*pi} - k" 
            using that st'_sub2 by auto
          then have "((\<lambda>u. f u - f 0) has_vector_derivative f' t)
                       (at t within {0..2*pi})"
            using derivf has_vector_derivative_transform_within t02
            by (smt (verit, best) f_eq has_vector_derivative_transform)
          then have "(f has_vector_derivative f' t) (at t within {0..2*pi})"
            using has_vector_derivative_diff_const by blast
          then show ?thesis
            by (rule has_vector_derivative_within_subset) (use st'_sub2 in auto)
        qed
          \<comment> \<open>Derivative of $h = f/\sin$ via the quotient rule\<close>
        have hderiv: "(h has_vector_derivative (f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2)
              (at t within {s'..t'})"
          if "t \<in> {s'..t'} - k" for t
        proof -
          have fd: "(f has_real_derivative f' t) (at t within {s'..t'})"
            using fderiv that by (simp add: has_real_derivative_iff_has_vector_derivative)
          have sd: "((\<lambda>x. sin (x - a)) has_real_derivative cos (t-a))
                      (at t within {s'..t'})"
            by (auto intro!: derivative_eq_intros)
          have "((\<lambda>x. f x / sin (x - a)) has_real_derivative
                   (f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2)
                  (at t within {s'..t'})"
            using DERIV_quotient[OF fd sd] sin_nz_st that
            by (simp add: power2_eq_square algebra_simps)
          then show ?thesis unfolding h_def
            by (simp add: has_real_derivative_iff_has_vector_derivative)
        qed
          \<comment> \<open>The derivative of @{term h} equals $\mathit{rest}/\sin$\<close>
        have hderiv_eq: "(f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2
                          = rest t / sin (t-a)"
          if "t \<in> {s'..t'}" for t
          using that unfolding rest_def fa0
          by (simp add: power2_eq_square divide_simps Multiseries_Expansion.tan_conv_sin_cos)
        have hderiv': "(h has_vector_derivative rest t / sin (t-a)) (at t within {s'..t'})"
          if "t \<in> {s'..t'} - k" for t
          using hderiv[OF that] hderiv_eq[of t] that by auto
            \<comment> \<open>$\mathit{rest} = 0$ a.e. on $\{u..v\}$, so obtain a negligible set @{term N}\<close>
        obtain N where negN: "negligible N" and restN: "\<And>x. x \<in> {u..v} - N \<Longrightarrow> rest x = 0"
        proof -
          from rest_ae_zero[unfolded eventually_ae_filter[of _ "lebesgue_on {u..v}"]]
          obtain N0 where N0: "N0 \<in> null_sets (lebesgue_on {u..v})"
            and sub: "{x \<in> space (lebesgue_on {u..v}). rest x \<noteq> 0} \<subseteq> N0"
            by auto
          have "negligible N0"
            using null_sets_restrict_space[of "{u..v}"] N0 negligible_iff_null_sets 
            by auto
          moreover have "rest x = 0" if "x \<in> {u..v} - N0" for x
            using sub that by (auto simp: space_lebesgue_on)
          ultimately show ?thesis using that by blast
        qed
          \<comment> \<open>@{term h} has derivative $0$ a.e. on $\{s'..t'\}$\<close>
        have hderiv_zero: "(h has_vector_derivative 0) (at t within {s'..t'})"
          if "t \<in> {s'..t'} - (k \<union> N)" for t
          using restN[of t] that st'_sub hderiv' using st'(2) by fastforce
        have neg_kN: "negligible (k \<union> N)"
          using negk negN by (rule negligible_Un)
            \<comment> \<open>By the FTC for AC functions: $h(t') - h(s') = \int 0 = 0$\<close>
        have "h t' - h s' = integral {s'..t'} (\<lambda>x. 0::real)"
          using fundamental_theorem_of_calculus_absolutely_continuous [OF neg_kN _ ac_h hderiv_zero]
          using st' by auto
        then have "h s' = h t'" by simp
            \<comment> \<open>Translate back to $f/\sin$\<close>
        then show ?thesis
          unfolding h_def s'_def t'_def by (auto split: if_splits)
      qed
      obtain x where "x \<in> {u<..<v}"
        using huv(2) dense by (metis greaterThanLessThan_iff)
      with eq_divide_eq hsin h_const that  have open_ver: "\<exists>c. \<forall>x\<in>{u<..<v}. f x = c * sin (x - a)"
        by metis
      then obtain c where hc: "\<forall>x\<in>{u<..<v}. f x = c * sin (x - a)"
        by auto
          \<comment> \<open>Extend to the closed interval by continuity.\<close>
      have "f x = c * sin (x - a)" if "x \<in> {u..v}" for x
      proof -
        have "f x - c * sin (x - a) = 0"
        proof (rule continuous_constant_on_closure[of "{u<..<v}" "\<lambda>x. f x - c * sin (x - a)" 0])
          show "continuous_on (closure {u<..<v}) (\<lambda>x. f x - c * sin (x - a))"
            unfolding closure_greaterThanLessThan[OF huv(2)]
            by (intro continuous_intros continuous_on_subset[OF contf])
              (use huv in auto)
          show "\<And>y. y \<in> {u<..<v} \<Longrightarrow> f y - c * sin (y - a) = 0"
            using hc by simp
          show "x \<in> closure {u<..<v}"
            unfolding closure_greaterThanLessThan[OF huv(2)] using that by auto
        qed
        thus ?thesis by simp
      qed
      thus ?thesis by auto
    qed
    show ?thesis
    proof (cases "a=0")
      case True
      obtain c1 where c1: "\<forall>x\<in>{0..pi}. f x = c1 * sin (x - a)"
        using key_fact[of 0 pi] sin_nz_2 True pi_gt_zero by auto
      obtain c2 where c2: "\<forall>x\<in>{pi..2*pi}. f x = c2 * sin (x - a)"
        using key_fact[of pi "2*pi"] sin_nz_1 True pi_gt_zero by auto
          \<comment> \<open>Use $\int f = 0$ and \<open>csin_integral\<close> to show $c_1 = c_2$.\<close>
      have eq1: "integral {0..pi} f = c1 * (cos (0 - a) - cos (pi - a))"
        by (metis (lifting) integral_cong True add_0 api_le c1 csin_integral)
      have eq2: "integral {pi..2*pi} f = c2 * (cos (pi - a) - cos (2*pi - a))"
        by (metis (lifting) integral_cong True add_0 api_le2 c2 csin_integral)
      have int_split: "integral {0..2*pi} f = integral {0..pi} f + integral {pi..2*pi} f"
        using Henstock_Kurzweil_Integration.integral_combine[OF pi_ge_zero]
        by (metis True add_cancel_left_left api_le2 assms(3) integrable_on_def)
      have "integral {0..2*pi} f = 0"
        using f0 by (simp add: has_integral_integrable_integral)
      hence "c1 * (cos (0 - a) - cos (pi - a)) + c2 * (cos (pi - a) - cos (2*pi - a)) = 0"
        using int_split eq1 eq2 by linarith
      hence "c1 = c2" using True
        by (simp add: cos_two_pi cos_pi)
      then show ?thesis
        by (metis atLeastAtMost_iff c1 c2 nle_le)
    next
      case False
      with \<open>0 \<le> a\<close> have a_pos: "0 < a" by auto
          \<comment> \<open>Three intervals where $\sin(x-a) \neq 0$\<close>
      obtain c1 where c1: "\<forall>x\<in>{0..a}. f x = c1 * sin (x - a)"
        using key_fact[of 0 a] sin_nz_3 a_pos \<open>a < pi\<close> by auto
      obtain c2 where c2: "\<forall>x\<in>{a..a+pi}. f x = c2 * sin (x - a)"
        using key_fact[of a "a+pi"] sin_nz_2 a_pos \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
      obtain c3 where c3: "\<forall>x\<in>{a+pi..2*pi}. f x = c3 * sin (x - a)"
        using key_fact[of "a+pi" "2*pi"] sin_nz_1 \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
          \<comment> \<open>Show $c_1 = c_3$ using $f(2\pi) = f(0)$\<close>
      have sin_a_nz: "sin a \<noteq> 0"
        using sin_gt_zero[OF a_pos \<open>a < pi\<close>] by (simp add: less_imp_le)
      have f0_eq: "f 0 = c1 * sin (0 - a)"
        using c1 \<open>0 \<le> a\<close> by auto
      have f2pi_eq: "f (2*pi) = c3 * sin (2*pi - a)"
        using c3 \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
          \<comment> \<open>Compute integrals on each interval\<close>
      have eq1: "integral {0..a} f = c1 * (cos (0 - a) - cos (a - a))"
        by (metis (no_types, lifting) integral_cong \<open>0 \<le> a\<close> c1 csin_integral)
      have eq2: "integral {a..a+pi} f = c2 * (cos (a - a) - cos ((a+pi) - a))"
        by (metis (no_types, lifting) api_le integral_cong c2 csin_integral)
      have eq3: "integral {a+pi..2*pi} f = c3 * (cos ((a+pi) - a) - cos (2*pi - a))"
        by (metis (mono_tags, lifting) integral_cong api_le2 c3 csin_integral)
          \<comment> \<open>Split the integral into three parts\<close>
      have f_int: "f integrable_on {0..2*pi}"
        using f0 has_integral_integrable by blast
      have a_le: "a \<le> a + pi" using pi_gt_zero by linarith
      have api_le: "a + pi \<le> 2 * pi" using \<open>a < pi\<close> by linarith
      have int_split: "integral {0..2*pi} f =
          integral {0..a} f + integral {a..a+pi} f + integral {a+pi..2*pi} f"
      proof -
        have "integral {0..2*pi} f = integral {0..a+pi} f + integral {a+pi..2*pi} f"
          using Henstock_Kurzweil_Integration.integral_combine [OF _ api_le f_int] 
            a_pos pi_gt_zero by auto
        moreover have "f integrable_on {0..a+pi}"
          using integrable_subinterval_real[OF f_int] a_pos api_le by auto
        ultimately show ?thesis
          by (metis Henstock_Kurzweil_Integration.integral_combine \<open>0 \<le> a\<close> a_le)
      qed
        \<comment> \<open>Use $\int f = 0$ to show $c_1 = c_2$\<close>
      have "integral {0..2*pi} f = 0"
        using f0 by (simp add: has_integral_integrable_integral)
      hence sum_eq: "c1 * (cos (0 - a) - cos (a - a)) + c2 * (cos (a - a) - cos ((a+pi) - a)) +
          c3 * (cos ((a+pi) - a) - cos (2*pi - a)) = 0"
        using int_split eq1 eq2 eq3 by linarith
      have "c1 * (cos a - 1) + 2 * c2 + c1 * (- 1 - cos a) = 0"
        using f0_eq f2pi_eq feq sin_a_nz sum_eq by fastforce
      hence c12_eq: "c1 = c2"
        by (simp add: algebra_simps)
      show ?thesis
        using f0_eq feq sin_a_nz c1 c2 c3 c12_eq by fastforce
    qed
  qed
qed

theorem scaled_Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes f': "\<And>x. x \<in> {0..1} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and "f 1 = f 0"
    and f_int: "(f has_integral 0) {0..1}"
    and f'_int: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..1}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..1}"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
proof -
  define g where "g \<equiv> \<lambda>x. f (x / (2*pi))"
  define g' where "g' \<equiv> \<lambda>x. (1/(2*pi)) * f' (x / (2*pi))"
  have twopi_pos: "2 * pi > 0" and twopi_nz: "2 * pi \<noteq> 0"
    and inv_twopi_pos: "1/(2*pi) > 0" and inv_twopi_nz: "1/(2*pi) \<noteq> (0::real)"
    using pi_gt_zero by auto
  have img: "(\<lambda>x. x / (1/(2*pi))) ` {0..1} = {0..2*pi}"
    using image_divide_atLeastAtMost[OF inv_twopi_pos] by simp
  have prec1: "(g' has_integral (g x - g 0)) {0..x}" if x: "x \<in> {0..2*pi}" for x
  proof -
    have *: "((\<lambda>s. f' (1/(2*pi) * s)) has_integral (2*pi) *\<^sub>R (f (x/(2*pi)) - f 0))
                 ((\<lambda>s. s / (1/(2*pi))) ` {0..x/(2*pi)})"
      using x has_integral_stretch_real[OF f' inv_twopi_nz] inv_twopi_pos by simp
    have **: "((\<lambda>s. f' (s/(2*pi))) has_integral (2*pi) * (f (x/(2*pi)) - f 0)) {0..x}"
      using * image_divide_atLeastAtMost[OF inv_twopi_pos, of 0 "x/(2*pi)"]
      using twopi_pos by (simp add: field_simps)
    have val: "1/(2*pi) * ((2*pi) * (f (x/(2*pi)) - f 0)) = f (x/(2*pi)) - f 0"
      using twopi_nz by simp
    show ?thesis
      using has_integral_mult_right[OF **, of "1/(2*pi)"] twopi_nz 
      unfolding g'_def g_def val by (simp add: field_simps)
  qed
  have prec2: "g (2*pi) = g 0"
    unfolding g_def using assms(2) by simp
  have prec3: "(g has_integral 0) {0..2*pi}"
    using has_integral_stretch_real_iff[OF inv_twopi_nz, of f 0 0 1]  f_int g_def img by auto
  have int: "(\<lambda>x. (f' (x/(2*pi)))\<^sup>2) integrable_on {0..2*pi}"
    using f'_int integrable_stretch_real[OF _ inv_twopi_nz, of "\<lambda>x. (f' x)\<^sup>2" 0 1] img 
    by (simp add: field_simps)
  then have prec4: "(\<lambda>x. (g' x)\<^sup>2) integrable_on {0..2*pi}"
    unfolding g'_def power_mult_distrib
    using integrable_on_cmult_left[OF int, of "(1/(2*pi))\<^sup>2"] by (simp add: algebra_simps)
  text \<open>Apply unscaled Wirtinger inequality\<close>
  have W1: "(\<lambda>x. (g x)\<^sup>2) integrable_on {0..2*pi}"
    and W2: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2)"
    and W3: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) \<Longrightarrow>
         \<exists>c a. \<forall>x \<in> {0..2*pi}. g x = c * sin (x - a)"
    using Wirtinger_inequality[OF prec1 prec2 prec3 prec4] by auto
  text \<open>Transfer conclusions back to scaled domain\<close>
  have g_unfold: "\<And>x. (g x)\<^sup>2 = (f (1/(2*pi) * x))\<^sup>2"
    unfolding g_def by (simp add: field_simps)
  have g'_unfold: "\<And>x. (g' x)\<^sup>2 = (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2"
    unfolding g'_def by (simp add: power_mult_distrib field_simps)
  text \<open>Show 1: integrability of $f(x)^2$ on $\{0..1\}$\<close>
  show int_f2: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..1}"
    using integrable_stretch_real_iff[OF inv_twopi_nz, of "\<lambda>x. (f x)\<^sup>2" 0 1] W1 g_def img by force 
  text \<open>Show 2: the scaled inequality\<close>
  show "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    have lhs_stretch: "integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (f (1/(2*pi) * x))\<^sup>2)
             = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (f x)\<^sup>2"] by simp
    have lhs_val: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using lhs_stretch img inv_twopi_pos by (simp add: g_unfold)
    have rhs_stretch: "integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2)
             = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
      using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2"] by simp
    have factor_out: "integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2) = (1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      by (simp add: integral_mult_right)
    have "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
      using img rhs_stretch by (simp add: g'_unfold)
    also have "\<dots> = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))"
      using inv_twopi_pos factor_out by simp
    finally have  "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))" .
    with W2 lhs_val 
    have "2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2) \<le> (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      by (simp add: power2_eq_square)
    then have "(2*pi)\<^sup>2 * integral {0..1} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using twopi_pos by (simp add: power2_eq_square field_simps)
    then show ?thesis
      by (simp add: power_mult_distrib)
  qed
  text \<open>Show 3: the equality case\<close>
  show "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
  proof -
    assume eq: "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    have "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using img integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (f x)\<^sup>2"] by (simp add: g_unfold)
    also have "\<dots> = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using inv_twopi_pos by simp
    finally have lhs: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)" .
    have rhs: "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
             = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    proof -
      have "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
          = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
        using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2"] img 
        by (simp add: g'_unfold)
      also have "\<dots> = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
        using twopi_pos by (simp add: power2_eq_square field_simps)
      finally show ?thesis .
    qed
    have "(2*pi)\<^sup>2 * integral {0..1} (\<lambda>x. (f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using eq by (simp add: power_mult_distrib)
    then have "2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2) = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using twopi_pos by (simp add: power2_eq_square field_simps)
    then have weq: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2)"
      using lhs rhs by linarith
    from W3[OF weq] obtain c a where ca: "\<forall>x \<in> {0..2*pi}. g x = c * sin (x - a)" by auto
    have "f x = c * sin (2*pi*x - a)" if "x \<in> {0..1}" for x
    proof  -
      have "2*pi*x \<in> {0..2*pi}" using twopi_pos
        using that by auto
      with ca show "f x = c * sin (2*pi*x - a)"
        by (metis g_def nonzero_mult_div_cancel_left twopi_nz)
    qed
    then show "\<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)" by auto
  qed
qed

end
