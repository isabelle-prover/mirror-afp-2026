(*  Title:   Piecewise_Interval_Integrals.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Piecewise_Interval_Integrals
  imports "HOL-Analysis.Analysis"
begin

section \<open>Interval integrals of piecewise polynomial and rational functions\<close>

text \<open>Integrability and the value of @{text interval_lebesgue_integral}
  for functions that agree
  on an open interval with a quadratic polynomial, with \<open>c\<^sub>0 + c\<^sub>1/x\<close>,
    or with a constant, and the
  chaining of adjacent pieces.  Together these give exact integrals of functions defined piecewise
  through \<open>floor\<close> and \<open>frac\<close>.\<close>


subsection \<open>Generic piece lemmas\<close>

text \<open>The integrand may be changed on the open interval.\<close>
lemma interval_integral_cong_Ioo:
  fixes f g :: "real \<Rightarrow> real"
  assumes "a \<le> b" "\<And>x. x \<in> {a<..<b} \<Longrightarrow> f x = g x"
  shows "interval_lebesgue_integral lborel (ereal a) (ereal b) f =
    interval_lebesgue_integral lborel (ereal a) (ereal b) g"
proof -
  have "set_lebesgue_integral lborel {a<..<b} f = set_lebesgue_integral lborel {a<..<b} g"
    using assms(2) set_lebesgue_integral_cong[of "{a<..<b}" lborel f g] by auto
  thus ?thesis unfolding interval_lebesgue_integral_def using assms(1) by auto
qed

lemma interval_integrable_cong_Ioo:
  fixes f g :: "real \<Rightarrow> real"
  assumes "a \<le> b" "\<And>x. x \<in> {a<..<b} \<Longrightarrow>
    f x = g x" "interval_lebesgue_integrable lborel (ereal a) (ereal b) f"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal b) g"
proof -
  have "set_integrable lborel {a<..<b} f = set_integrable lborel {a<..<b} g"
    using assms(2) set_integrable_cong[of lborel lborel "{a<..<b}" "{a<..<b}" f g] by fastforce
  thus ?thesis using assms(1,3) unfolding interval_lebesgue_integrable_def by simp
qed

text \<open>A continuous integrand is integrable on a bounded interval.\<close>
lemma interval_integrable_continuous:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "continuous_on {a..b} f"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal b) f"
  using interval_integrable_continuous_on[OF assms] by meson

text \<open>Quadratic piece: @{text "\<integral>_a^b (c0 + c1 x + c2 x^2) dx"}.\<close>
lemma piece_quad:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "\<And>x. x \<in> {a<..<b} \<Longrightarrow> f x = c0 + c1 * x + c2 * x ^ 2"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal b) f \<and>
         interval_lebesgue_integral lborel (ereal a) (ereal b) f
           = (c0 * b + c1 * b ^ 2 / 2 + c2 * b ^ 3 / 3) - (c0 * a + c1 * a ^ 2 / 2 + c2 * a ^ 3 /
             3)"
proof -
  let ?g = "\<lambda>x. c0 + c1 * x + c2 * x ^ 2"
  let ?F = "\<lambda>x. c0 * x + c1 * x ^ 2 / 2 + c2 * x ^ 3 / 3"
  have cont: "continuous_on {a..b} ?g" by (intro continuous_intros)
  have I: "interval_lebesgue_integrable lborel (ereal a) (ereal b) ?g"
    by (rule interval_integrable_continuous[OF assms(1) cont])
  have D: "\<And>x. x \<in> {a..b} \<Longrightarrow>
    (?F has_vector_derivative ?g x) (at x within {a..b})"
  proof -
    fix x assume x: "x \<in> {a..b}"
    have "((\<lambda>x. c0 * x + c1 * x ^ 2 / 2 + c2 * x ^ 3 / 3) has_real_derivative (c0 + c1 * x +
      c2 * x ^ 2)) (at x within {a..b})"
      using x by (fastforce simp: power2_eq_square intro: derivative_eq_intros)
    thus "(?F has_vector_derivative ?g x) (at x within {a..b})"
      unfolding has_real_derivative_iff_has_vector_derivative .
  qed
  have "interval_lebesgue_integral lborel (ereal a) (ereal b) ?g = ?F b - ?F a"
  proof -
    have mm1: "min a b = a" using assms(1) by simp
    have mm2: "max a b = b" using assms(1) by simp
    show ?thesis using interval_integral_FTC_finite[of a b ?g ?F] cont D unfolding mm1 mm2
      by presburger
  qed
  moreover have "interval_lebesgue_integrable lborel (ereal a) (ereal b) f"
    by (rule interval_integrable_cong_Ioo[OF assms(1) _ I]) (simp add: assms(2))
  moreover have "interval_lebesgue_integral lborel (ereal a) (ereal b) f =
    interval_lebesgue_integral lborel (ereal a) (ereal b) ?g"
    by (rule interval_integral_cong_Ioo[OF assms(1)]) (rule assms(2))
  ultimately show ?thesis by simp
qed

text \<open>Rational piece: @{text "\<integral>_a^b (A x + B)/x^3 dx"} for @{text "0 < a"}.\<close>
lemma piece_rat:
  fixes f :: "real \<Rightarrow> real"
  assumes "0 < a" "a \<le> b" "\<And>x. x \<in> {a<..<b} \<Longrightarrow> f x = A * x + B"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal b) (\<lambda>x. f x / x ^ 3) \<and>
         interval_lebesgue_integral lborel (ereal a) (ereal b) (\<lambda>x. f x / x ^ 3)
           = (- A / b - B / (2 * b ^ 2)) - (- A / a - B / (2 * a ^ 2))"
proof -
  let ?g = "\<lambda>x. (A * x + B) / x ^ 3"
  let ?F = "\<lambda>x. - A / x - B / (2 * x ^ 2)"
  have cont: "continuous_on {a..b} ?g" using assms(1) by (intro continuous_intros) auto
  have I: "interval_lebesgue_integrable lborel (ereal a) (ereal b) ?g"
    by (rule interval_integrable_continuous[OF assms(2) cont])
  have D: "\<And>x. x \<in> {a..b} \<Longrightarrow>
    (?F has_vector_derivative ?g x) (at x within {a..b})"
  proof -
    fix x assume x: "x \<in> {a..b}"
    have "x \<noteq> 0" using assms(1) x by auto
    hence "((\<lambda>x. - A / x - B / (2 * x ^ 2)) has_real_derivative ((A * x + B) /
      x ^ 3)) (at x within {a..b})"
      by (fastforce simp: power2_eq_square power3_eq_cube field_simps intro: derivative_eq_intros)
    thus "(?F has_vector_derivative ?g x) (at x within {a..b})"
      unfolding has_real_derivative_iff_has_vector_derivative .
  qed
  have "interval_lebesgue_integral lborel (ereal a) (ereal b) ?g = ?F b - ?F a"
  proof -
    have mm1: "min a b = a" using assms(2) by simp
    have mm2: "max a b = b" using assms(2) by simp
    show ?thesis using interval_integral_FTC_finite[of a b ?g ?F] cont D unfolding mm1 mm2
      by presburger
  qed
  moreover have "interval_lebesgue_integrable lborel (ereal a) (ereal b) (\<lambda>x. f x / x ^ 3)"
    by (rule interval_integrable_cong_Ioo[OF assms(2) _ I]) (simp add: assms(3))
  moreover have "interval_lebesgue_integral lborel (ereal a) (ereal b) (\<lambda>x. f x / x ^ 3) =
    interval_lebesgue_integral lborel (ereal a) (ereal b) ?g"
    by (rule interval_integral_cong_Ioo[OF assms(2)]) (simp add: assms(3))
  ultimately show ?thesis by simp
qed

text \<open>Adjacent pieces add up.\<close>
lemma chain:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "b \<le> c"
    and "interval_lebesgue_integrable lborel (ereal a) (ereal b) f \<and>
      interval_lebesgue_integral lborel (ereal a) (ereal b) f = v"
    and "interval_lebesgue_integrable lborel (ereal b) (ereal c) f \<and>
      interval_lebesgue_integral lborel (ereal b) (ereal c) f = w"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal c) f \<and>
    interval_lebesgue_integral lborel (ereal a) (ereal c) f = v + w"
proof -
  have I: "interval_lebesgue_integrable lborel (ereal a) (ereal c) f"
  proof -
    have I1: "set_integrable lborel {a<..<b} f" using assms(1,3)
      unfolding interval_lebesgue_integrable_def by force
    have I2: "set_integrable lborel {b<..<c} f" using assms(2,4)
      unfolding interval_lebesgue_integrable_def by force
    have "set_integrable lborel ({a<..<b} \<union> {b<..<c}) f" using set_integrable_Un[OF I1 I2]
      by simp
    moreover have "set_integrable lborel ({a<..<b} \<union> {b<..<c}) f =
      set_integrable lborel {a<..<c} f"
      using set_integrable_discrete_difference[where X = "{b}" and A =
        "{a<..<b} \<union> {b<..<c}" and B = "{a<..<c}" and M = lborel and f = f] assms(1,2)
      by force
    ultimately have "set_integrable lborel {a<..<c} f" by meson
    thus ?thesis unfolding interval_lebesgue_integrable_def using assms(1,2) by force
  qed
  have "interval_lebesgue_integral lborel (ereal a) (ereal c) f
          = interval_lebesgue_integral lborel (ereal a) (ereal b) f +
            interval_lebesgue_integral lborel (ereal b) (ereal c) f"
    using interval_integral_sum[of "ereal a" "ereal b" "ereal c" f] I assms(1,2)
      by (simp add: min_def max_def)
  thus ?thesis using I assms(3,4) by simp
qed

lemma const_piece:
  fixes h :: "real \<Rightarrow> real"
  assumes "a \<le> b" "\<And>z. z \<in> {a<..<b} \<Longrightarrow> h z = c"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal b) h \<and>
         interval_lebesgue_integral lborel (ereal a) (ereal b) h = (b - a) * c"
  using piece_quad[OF assms(1), of h c 0 0] assms(2) by (simp add: algebra_simps)

lemma floor_inv_eq:
  fixes y :: real
  assumes "0 < y" "of_int k * y \<le> 1" "1 < (of_int k + 1) * y"
  shows "floor (1 / y) = k"
  unfolding floor_eq_iff using assms by (auto simp: le_divide_eq divide_less_eq)

lemma frac_nat:
  fixes u :: real
  assumes "real k \<le> u" "u < real k + 1"
  shows "frac u = u - real k"
proof -
  have "floor u = int k" using assms by (auto simp: floor_eq_iff)
  thus ?thesis by (fastforce simp: frac_def)
qed



end
