(*  Title:   Zeta5_Archimedean_Bound.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Archimedean_Bound
  imports Zeta5_Numeric_Enclosures Andreief_Identity
begin

section \<open>The archimedean bound: Proposition 6.3\<close>

text \<open>Section 6 of the paper: the bound (6.11) on the weight, (6.10)
  by Andreief's identity, the
  one-coordinate bound (6.12), the bound (6.9) for every configuration through the logarithmic
  energy of \<open>\<rho>\<close> and the zero-mass energy inequality, and the estimates (6.14),
    (6.15) leading to
  Proposition 6.3 (@{text log_FK_zeta5_bound}): \<open>ln F\<^sub>K(\<zeta>(5)) \<le>
    @{text Ubar} \<cdot> K\<^sup>2 + O(K ln K)\<close>.  Lean theories
  @{text Section6}, @{text Energy6}, @{text Section6b}, @{text Section6c}, @{text Config69}.\<close>

subsection \<open>(6.11) and Lemma 6.2\<close>

text \<open>(6.11): @{text "w(y) \<le> 8192(1+y)^5e^{-2\<pi>y}"}.\<close>
lemma binomial_term_le:
  fixes t :: real
  assumes "0 \<le> t"
  shows "real (n choose k) * t ^ k \<le> (1 + t) ^ n"
proof (cases "k \<le> n")
  case True
  have "(t + 1) ^ n = (\<Sum> i \<le> n. real (n choose i) * t ^ i * 1 ^ (n - i))"
    by (rule binomial_ring)
  also have "\<dots> \<ge> real (n choose k) * t ^ k * 1 ^ (n - k)"
    by (rule member_le_sum) (use assms True in auto)
  finally show ?thesis by (simp add: add.commute)
next
  case False
  hence "n < k" by simp
  thus ?thesis using assms by (simp add: binomial_eq_0)
qed

lemma pow4_exp_bound:
  fixes x :: real
  assumes "0 \<le> x"
  shows "x ^ 4 * exp (- x) \<le> 42"
proof -
  have "exp (x / 12) \<ge> 1 + x / 12" by (rule exp_ge_add_one_self)
  hence "(1 + x / 12) ^ 12 \<le> exp (x / 12) ^ 12" using assms by (intro power_mono) auto
  also have "exp (x / 12) ^ 12 = exp x" by (simp flip: exp_of_nat_mult)
  finally have e: "(1 + x / 12) ^ 12 \<le> exp x" .
  have "real (12 choose 4) * (x / 12) ^ 4 \<le> (1 + x / 12) ^ 12"
    by (rule binomial_term_le) (use assms in simp)
  moreover have "(12 choose 4) = (495 :: nat)"
    using binomial_fact_lemma[of 4 12] by (simp add: fact_numeral)
  ultimately have "495 * (x / 12) ^ 4 \<le> exp x" using e by simp
  hence "x ^ 4 \<le> 20736 / 495 * exp x" by (simp add: power_divide field_simps)
  also have "\<dots> \<le> 42 * exp x" by simp
  finally show ?thesis by (simp add: exp_minus field_simps)
qed

theorem weight_le: "0 < y \<Longrightarrow> weight y \<le> 8192 * (1 + y) ^ 5 * exp (- 2 * pi * y)"
proof -
  assume y: "0 < y"
  define Y where "Y = min y 1"
  define s where "s = pi * Y"
  have Y0: "0 < Y" "Y \<le> y" "Y \<le> 1" using y by (auto simp: Y_def)
  have s0: "0 < s" and spi: "s \<le> pi" using Y0 by (auto simp: s_def)
  define a where "a l = real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) * y)" for l
  define b where "b l = real (l + 1) ^ 4 * exp (- 2 * pi * real l * y)" for l
  define E where "E = exp (- 2 * pi * y)"
  have ab: "a l = E * b l" for l
    by (simp add: a_def b_def E_def algebra_simps flip: exp_add)
  have sa: "summable a" unfolding a_def by (rule weight_summable[OF y])
  have ba: "b l = inverse E * a l" for l using ab[of l] by (simp add: E_def)
  have sb: "summable b" unfolding ba by (rule summable_mult[OF sa])
  define q where "q = exp (- s)"
  have q0: "0 < q" "q < 1" using s0 by (auto simp: q_def)
  define g where "g l = 42 * exp s / s ^ 4 * q ^ l" for l
  have bg: "b l \<le> g l" for l
  proof -
    define x where "x = s * real (l + 1)"
    have x0: "0 \<le> x" using s0 by (simp add: x_def)
    have "Y * real l \<le> y * real l" by (rule mult_right_mono) (use Y0 in auto)
    hence "exp (- 2 * pi * real l * y) \<le> exp (- 2 * s * real l)"
      by (simp add: s_def algebra_simps)
    hence "b l \<le> real (l + 1) ^ 4 * exp (- 2 * s * real l)" by (simp add: b_def mult_left_mono)
    also have "real (l + 1) ^ 4 * exp (- 2 * s * real l) =
      (x ^ 4 * exp (- x)) * exp s * q ^ l / s ^ 4"
    proof -
      have ql: "q ^ l = exp (real l * (- s))" unfolding q_def by (rule exp_of_nat_mult[symmetric])
      have "exp (- x) * exp s * q ^ l = exp (- x + s + real l * (- s))" unfolding ql
        by (simp add: mult_exp_exp algebra_simps)
      also have "- x + s + real l * (- s) = - 2 * s * real l" by (simp add: x_def algebra_simps)
      finally have e: "exp (- x) * exp s * q ^ l = exp (- 2 * s * real l)" .
      have x4: "x ^ 4 = s ^ 4 * real (l + 1) ^ 4" by (simp add: x_def power_mult_distrib)
      have "real (l + 1) ^ 4 * exp (- 2 * s * real l) =
        real (l + 1) ^ 4 * (exp (- x) * exp s * q ^ l)"
        by (simp only: e)
      also have "\<dots> = (x ^ 4 * exp (- x)) * exp s * q ^ l / s ^ 4" unfolding x4 using s0
        by simp
      finally show ?thesis .
    qed
    also have "\<dots> \<le> 42 * exp s * q ^ l / s ^ 4"
      using pow4_exp_bound[OF x0] s0 q0 by (intro divide_right_mono mult_right_mono) auto
    finally show ?thesis by (simp add: g_def)
  qed
  have G: "g sums (42 * exp s / s ^ 4 * (1 / (1 - q)))"
    unfolding g_def by (rule sums_mult) (rule geometric_sums, use q0 in simp)
  have "suminf b \<le> suminf g" by (rule suminf_le[OF bg sb sums_summable[OF G]])
  also have "suminf g = 42 * exp s / s ^ 4 * (1 / (1 - q))" using G by (simp add: sums_iff)
  finally have Sg: "suminf b \<le> 42 * exp s / s ^ 4 * (1 / (1 - q))" .
  have inv: "1 / (1 - q) \<le> (1 + s) / s"
  proof -
    have "1 + s \<le> exp s" by (rule exp_ge_add_one_self)
    hence "q \<le> 1 / (1 + s)" using s0 by (simp add: q_def exp_minus field_simps)
    hence le: "s / (1 + s) \<le> 1 - q" using s0 by (simp add: field_simps)
    have "1 / (1 - q) \<le> 1 / (s / (1 + s))"
      by (rule divide_left_mono[OF le]) (use q0 s0 in \<open>simp_all add:
        zero_less_mult_iff\<close>)
    thus ?thesis by simp
  qed
  have "42 * exp s / s ^ 4 * (1 / (1 - q)) \<le> 42 * exp s / s ^ 4 * ((1 + s) / s)"
    using inv s0 by (intro mult_left_mono) auto
  with Sg have Sb': "suminf b \<le> 42 * exp s / s ^ 4 * ((1 + s) / s)" by linarith
  have s5: "s ^ 5 = s * s ^ 4" by (simp add: eval_nat_numeral)
  have Sb: "suminf b \<le> 42 * exp s * (1 + s) / s ^ 5" using Sb' unfolding s5
    by (simp add: field_simps)
  have W: "weight y = (2 * pi) ^ 4 * y ^ 5 / 12 * E * suminf b"
  proof -
    have "suminf a = E * suminf b" unfolding ab by (rule suminf_mult[OF sb])
    thus ?thesis unfolding weight_def a_def[symmetric] by simp
  qed
  have C0: "0 \<le> (2 * pi) ^ 4 * y ^ 5 / 12 * E" using y by (simp add: E_def)
  have "weight y \<le> (2 * pi) ^ 4 * y ^ 5 / 12 * E * (42 * exp s * (1 + s) / s ^ 5)"
    unfolding W by (rule mult_left_mono[OF Sb C0])
  also have "\<dots> = 56 * pi ^ 4 * (exp s * (1 + s)) * (y / s) ^ 5 * E"
    using s0 by (simp add: power_divide power_mult_distrib field_simps)
  also have "\<dots> \<le> 56 * pi ^ 4 * (exp s * (1 + s)) * ((1 + y) / pi) ^ 5 * E"
  proof -
    have ys: "y / s \<le> (1 + y) / pi"
    proof (cases "y \<le> 1")
      case True
      hence "s = pi * y" by (simp add: s_def Y_def)
      thus ?thesis using y by (simp add: field_simps)
    next
      case False
      hence "s = pi" by (simp add: s_def Y_def)
      thus ?thesis by (simp add: divide_right_mono)
    qed
    have "(y / s) ^ 5 \<le> ((1 + y) / pi) ^ 5" using ys y s0 by (intro power_mono) auto
    thus ?thesis using s0 by (intro mult_right_mono mult_left_mono) (auto simp: E_def)
  qed
  also have "\<dots> = (56 * (exp s * (1 + s)) / pi) * (1 + y) ^ 5 * E"
  proof -
    have p5: "pi ^ 5 = pi * pi ^ 4" by (simp add: eval_nat_numeral)
    have h: "pi ^ 4 * ((1 + y) / pi) ^ 5 = (1 + y) ^ 5 / pi" unfolding power_divide p5 by simp
    have "56 * pi ^ 4 * (exp s * (1 + s)) * ((1 + y) / pi) ^ 5 * E
        = 56 * (exp s * (1 + s)) * (pi ^ 4 * ((1 + y) / pi) ^ 5) * E" by (simp only: mult_ac)
    also have "\<dots> = 56 * (exp s * (1 + s)) * ((1 + y) ^ 5 / pi) * E" by (simp only: h)
    also have "\<dots> = (56 * (exp s * (1 + s)) / pi) * (1 + y) ^ 5 * E" by simp
    finally show ?thesis .
  qed
  also have "\<dots> \<le> 8192 * (1 + y) ^ 5 * E"
  proof -
    have "exp s \<le> exp 4" using spi pi_less_4 by simp
    also have "exp (4 :: real) = exp 1 ^ 4" using exp_of_nat_mult[of 4 "1 :: real"] by simp
    also have "\<dots> \<le> 3 ^ 4" using exp_le by (intro power_mono) auto
    finally have es: "exp s \<le> 81" by simp
    have s5: "1 + s \<le> 5" using spi pi_less_4 by simp
    have "exp s * (1 + s) \<le> 81 * 5" using es s5 s0 by (intro mult_mono) auto
    hence "56 * (exp s * (1 + s)) / pi \<le> 56 * (81 * 5) / 3"
      using pi_gt3 s0 by (intro frac_le) auto
    hence "56 * (exp s * (1 + s)) / pi \<le> 8192" by simp
    thus ?thesis using y by (intro mult_right_mono) (auto simp: E_def)
  qed
  finally show "weight y \<le> 8192 * (1 + y) ^ 5 * exp (- 2 * pi * y)" by (simp add: E_def)
qed

theorem DeltaK_zeta5_integral:
  assumes "40 dvd K"
  shows "real_eval (DeltaK K) zeta5 = 1 / fact (hof K) *
    set_lebesgue_integral (PiM {..<hof K} (\<lambda>_. lborel)) {y. \<forall>i<hof K. 0 < y i}
      (\<lambda>y. (\<Prod> i < hof K. \<Prod> j \<in> {j. i < j \<and>
        j < hof K}. (y i ^ 2 - y j ^ 2) ^ 2) *
           (\<Prod> i < hof K. real_eval (Dm (Nof K)) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) *
             weight (y i)))"
proof -
  text \<open>Instead of the restricted measure on @{text "(0,\<infinity>)"} (whose product would
    need
    @{text "PiM"} of restricted spaces, absent from the library), apply Andreief on @{const lborel}
    with the indicator of @{text "(0,\<infinity>)"} put into the first family.\<close>
  define h where "h = hof K"
  define g :: "real \<Rightarrow> real" where "g =
    (\<lambda>y. real_eval (Dm (Nof K)) (y ^ 2) ^ 6 / real_eval (Dm K) (y ^ 2) * weight y)"
  define \<phi> :: "nat \<Rightarrow> real \<Rightarrow> real" where "\<phi> =
    (\<lambda>i y. y ^ (2 * i) * indicator {0<..} y)"
  define \<psi> :: "nat \<Rightarrow> real \<Rightarrow> real" where "\<psi> =
    (\<lambda>j y. y ^ (2 * j) * g y)"
  have gy: "\<And>t. real_eval (Dm (Nof K)) (t ^ 2) ^ 6 / real_eval (Dm K) (t ^ 2) * weight t = g t"
    by (simp add: g_def)
  have S0: "(0::nat) \<notin> {1..K}"
    by simp
  have DK: "sqPoleProd {1..K} = Dm K"
    by (simp add: Dm_def sqPoleProd_def)
  have pt: "\<And>m y. real_eval (Dm (Nof K) ^ 6 * pX ^ m) (y ^ 2) / real_eval (Dm K) (y ^ 2) *
    weight y = (y ^ 2) ^ m * g y"
    unfolding g_def real_eval_mult real_eval_power real_eval_pX
    by (simp add: mult_ac)
  have php: "\<And>i j y. \<phi> i y * \<psi> j y =
    indicator {0<..} y *\<^sub>R ((y ^ 2) ^ (i + j) * g y)"
    unfolding \<phi>_def \<psi>_def power_add power_mult
    by (simp add: mult_ac)
  have entry: "\<And>i j. i < h \<Longrightarrow> j < h \<Longrightarrow>
    real_eval (GK K $$ (i, j)) zeta5 = integral\<^sup>L lborel (\<lambda>y. \<phi> i y *
    \<psi> j y)"
  proof -
    fix i j assume ij: "i < h" "j < h"
    have e1: "GK K $$ (i, j) = muX {1..K} (Dm (Nof K) ^ 6 * pX ^ (i + j))"
      using ij by (simp add: GK_def h_def)
    show "real_eval (GK K $$ (i, j)) zeta5 =
      integral\<^sup>L lborel (\<lambda>y. \<phi> i y * \<psi> j y)"
      unfolding e1 muX_zeta5_integral[OF finite_atLeastAtMost S0] DK pt php
        set_lebesgue_integral_def
      by simp
  qed
  have detG: "real_eval (DeltaK K) zeta5 =
    Determinant.det (Matrix.mat h h (\<lambda>(i,
    j). integral\<^sup>L lborel (\<lambda>y. \<phi> i y * \<psi> j y)))"
  proof -
    have d1: "real_eval (DeltaK K) zeta5 =
      Determinant.det (map_mat (\<lambda>P. real_eval P zeta5) (GK K))"
      unfolding DeltaK_def by (rule comm_ring_hom.hom_det[OF real_eval_hom, symmetric])
    have d2: "map_mat (\<lambda>P. real_eval P zeta5) (GK K) =
      Matrix.mat h h (\<lambda>(i, j). integral\<^sup>L lborel (\<lambda>y. \<phi> i y *
      \<psi> j y))"
    proof (rule eq_matI)
      fix i j assume i: "i < dim_row (Matrix.mat h h (\<lambda>(i,
        j). integral\<^sup>L lborel (\<lambda>y. \<phi> i y * \<psi> j y)))"
        and j: "j < dim_col (Matrix.mat h h (\<lambda>(i,
          j). integral\<^sup>L lborel (\<lambda>y. \<phi> i y * \<psi> j y)))"
      show "map_mat (\<lambda>P. real_eval P zeta5) (GK K) $$ (i, j) =
        Matrix.mat h h (\<lambda>(i, j). integral\<^sup>L lborel (\<lambda>y. \<phi> i y *
        \<psi> j y)) $$ (i, j)"
        using i j entry by (simp add: GK_def h_def)
    next
      show "dim_row (map_mat (\<lambda>P. real_eval P zeta5) (GK K)) =
        dim_row (Matrix.mat h h (\<lambda>(i,
        j). integral\<^sup>L lborel (\<lambda>y. \<phi> i y * \<psi> j y)))"
        by (simp add: GK_def h_def)
    next
      show "dim_col (map_mat (\<lambda>P. real_eval P zeta5) (GK K)) =
        dim_col (Matrix.mat h h (\<lambda>(i,
        j). integral\<^sup>L lborel (\<lambda>y. \<phi> i y * \<psi> j y)))"
        by (simp add: GK_def h_def)
    qed
    show ?thesis
      unfolding d1 d2
      by simp
  qed
  have integ: "\<And>i j. i < h \<Longrightarrow> j < h \<Longrightarrow>
    integrable lborel (\<lambda>y. \<phi> i y * \<psi> j y)"
  proof -
    fix i j assume ij: "i < h" "j < h"
    have r: "set_integrable lborel {0<..} (\<lambda>y. real_eval (Dm (Nof K) ^ 6 * pX ^ (i +
      j)) (y ^ 2) / real_eval (sqPoleProd {1..K}) (y ^ 2) * weight y)"
      by (rule rat_integrable[OF finite_atLeastAtMost S0])
    show "integrable lborel (\<lambda>y. \<phi> i y * \<psi> j y)"
      using r[unfolded set_integrable_def DK pt]
      by (simp add: php)
  qed
  have A: "Determinant.det (Matrix.mat h h (\<lambda>(i,
    j). integral\<^sup>L lborel (\<lambda>y. \<phi> i y * \<psi> j y)))
      = 1 / fact h * integral\<^sup>L (PiM {..<h} (\<lambda>_. lborel))
          (\<lambda>x. Determinant.det (Matrix.mat h h (\<lambda>(a,
            b). \<phi> a (x b))) * Determinant.det (Matrix.mat h h (\<lambda>(a,
            b). \<psi> a (x b))))"
    by (rule andreief[OF sigma_finite_lborel integ])
  have V: "\<And>y :: nat \<Rightarrow> real. Determinant.det (Matrix.mat h h (\<lambda>(a,
    b). y b ^ (2 * a))) = (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
    j < h}. (y j ^ 2 - y i ^ 2))"
  proof -
    fix y :: "nat \<Rightarrow> real"
    have "Determinant.det (Matrix.mat h h (\<lambda>(a, b). y b ^ (2 * a))) =
      Determinant.det (Matrix.mat h h (\<lambda>(a, b). (y a ^ 2) ^ b))"
      using andreief_det_swap[of h "\<lambda>a b. (y a ^ 2) ^ b"] by (simp add: power_mult)
    also have "\<dots> = (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
      j < h}. (y j ^ 2 - y i ^ 2))"
      using det_vandermonde_jnf[of h "\<lambda>a. y a ^ 2"] by simp
    finally show "Determinant.det (Matrix.mat h h (\<lambda>(a, b). y b ^ (2 * a))) = (\<Prod> i <
      h. \<Prod> j \<in> {j. i < j \<and> j < h}. (y j ^ 2 - y i ^ 2))" .
  qed
  have Wphi: "\<And>y. Determinant.det (Matrix.mat h h (\<lambda>(a, b). \<phi> a (y b))) =
    (\<Prod> b < h. indicator {0<..} (y b)) * Determinant.det (Matrix.mat h h (\<lambda>(a,
    b). y b ^ (2 * a)))"
    unfolding \<phi>_def
    by (simp add: andreief_det_scale_cols)
  have Wpsi: "\<And>y. Determinant.det (Matrix.mat h h (\<lambda>(a, b). \<psi> a (y b))) =
    (\<Prod> b < h. g (y b)) * Determinant.det (Matrix.mat h h (\<lambda>(a, b). y b ^ (2 * a)))"
    unfolding \<psi>_def
    by (simp add: andreief_det_scale_cols)
  have ind: "\<And>y :: nat \<Rightarrow> real. (\<Prod> b < h. indicator {0<..} (y b) :: real) =
    indicator {y. \<forall>i<h. 0 < y i} y"
  proof -
    fix y :: "nat \<Rightarrow> real"
    show "(\<Prod> b < h. indicator {0<..} (y b) :: real) = indicator {y. \<forall>i<h. 0 < y i} y"
    proof (cases "\<forall>i<h. 0 < y i")
      case True
      then show ?thesis
        by (simp add: indicator_def)
    next
      case False
      then show ?thesis
        by (auto simp: indicator_def prod_zero_iff)
    qed
  qed
  have sq: "\<And>a b :: real. (b - a) * (b - a) = (a - b) ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  have Vsq: "\<And>y :: nat \<Rightarrow> real. (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
    j < h}. (y j ^ 2 - y i ^ 2)) * (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
    j < h}. (y j ^ 2 - y i ^ 2))
      = (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and> j < h}. (y i ^ 2 - y j ^ 2) ^ 2)"
    unfolding prod.distrib[symmetric] sq
    by simp
  have pw: "\<And>y. Determinant.det (Matrix.mat h h (\<lambda>(a,
    b). \<phi> a (y b))) * Determinant.det (Matrix.mat h h (\<lambda>(a, b). \<psi> a (y b)))
      = indicator {y. \<forall>i<h. 0 < y i} y *\<^sub>R ((\<Prod> i < h. \<Prod> j \<in> {j. i <
        j \<and> j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i < h. g (y i)))"
    unfolding Wphi Wpsi ind V Vsq[symmetric]
    by (simp add: mult_ac)
  have fin: "integral\<^sup>L (PiM {..<h} (\<lambda>_. lborel)) (\<lambda>x. Determinant.det
    (Matrix.mat h h (\<lambda>(a, b). \<phi> a (x b))) *
    Determinant.det (Matrix.mat h h (\<lambda>(a, b). \<psi> a (x b))))
      = set_lebesgue_integral (PiM {..<h} (\<lambda>_. lborel)) {y. \<forall>i<h. 0 <
        y i} (\<lambda>y. (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
        j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i < h. g (y i)))"
    unfolding set_lebesgue_integral_def pw
    by simp
  show ?thesis
    unfolding h_def[symmetric] gy detG A fin
    by simp
qed

subsection \<open>(6.12) and the one-coordinate bound\<close>

text \<open>(6.12): @{text "0 \<le> \<Sum>_{j\<le>m} log(t + (j/K)^2) -
  K \<integral>_0^{m/K} log(t + u^2) du \<le> 2 log m + 2"}.\<close>
lemma sum_ge_int:
  "0 < t \<Longrightarrow> 0 < \<kappa> \<Longrightarrow>
    \<kappa> * integral {0..real m / \<kappa>} (\<lambda>u. ln (t + u ^ 2)) \<le> (\<Sum> j =
    1..m. ln (t + (real j / \<kappa>) ^ 2))"
proof (induction m)
  case 0
  thus ?case by simp
next
  case (Suc m)
  define f where "f u = ln (t + u ^ 2)" for u :: real
  have fe: "(\<lambda>u. ln (t + u ^ 2)) = f" by (simp add: f_def fun_eq_iff)
  have t: "0 < t" and k: "0 < \<kappa>" using Suc.prems by auto
  have tp: "0 < t + u ^ 2" for u :: real using t by (simp add: add_pos_nonneg)
  have cont: "continuous_on {a..b} f" for a b
    unfolding f_def by (intro continuous_intros) (use tp in \<open>auto simp: less_le\<close>)
  have intg: "f integrable_on {a..b}" for a b by (rule integrable_continuous_interval[OF cont])
  define a where "a = real m / \<kappa>"
  define b where "b = real (Suc m) / \<kappa>"
  have ab: "0 \<le> a" "a \<le> b" using k by (auto simp: a_def b_def divide_right_mono)
  have comb: "integral {0..a} f + integral {a..b} f = integral {0..b} f"
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF ab intg])
  have "integral {a..b} f \<le> integral {a..b} (\<lambda>_. f b)"
  proof (rule integral_le[OF intg])
    show "(\<lambda>_. f b) integrable_on {a..b}"
      by (rule integrable_continuous_interval) (rule continuous_on_const)
    fix u assume "u \<in> {a..b}"
    hence "0 \<le> u" "u \<le> b" using ab by auto
    hence "u ^ 2 \<le> b ^ 2" by (intro power_mono) auto
    thus "f u \<le> f b" unfolding f_def using tp by (subst ln_le_cancel_iff) auto
  qed
  also have "\<dots> = (b - a) * f b" using ab by simp
  also have "b - a = 1 / \<kappa>" using k by (simp add: a_def b_def field_simps)
  finally have le': "\<kappa> * integral {a..b} f \<le> f b" using k by (simp add: field_simps)
  have IH: "\<kappa> * integral {0..a} f \<le> (\<Sum> j = 1..m. ln (t + (real j / \<kappa>) ^ 2))"
    using Suc.IH[OF t k] unfolding fe a_def .
  have "\<kappa> * integral {0..b} f = \<kappa> * integral {0..a} f + \<kappa> * integral {a..b} f"
    by (simp add: comb[symmetric] distrib_left)
  also have "\<dots> \<le> (\<Sum> j = 1..m. ln (t + (real j / \<kappa>) ^ 2)) + f b"
    using IH le' by linarith
  also have "\<dots> = (\<Sum> j = 1..Suc m. ln (t + (real j / \<kappa>) ^ 2))"
    by (simp add: b_def f_def)
  finally show ?case unfolding fe b_def .
qed

lemma sum_log_le: "1 \<le> m \<Longrightarrow>
  (\<Sum> k = 1..m. ln (real k)) \<le> real m * ln (real m) - real m + ln (real m) + 1"
proof -
  assume "1 \<le> m"
  thus ?thesis
  proof (induction m rule: nat_induct_at_least)
    case base
    show ?case
      by simp
  next
    case (Suc m)
    define A :: real where "A = ln (real m)"
    define B :: real where "B = ln (real (Suc m))"
    have m1: "1 \<le> real m" using Suc.hyps
      by simp
    have IH: "(\<Sum> k = 1..m. ln (real k)) \<le> real m * A - real m + A + 1" using Suc.IH
      unfolding A_def .
    have "ln (real m / real (Suc m)) \<le> real m / real (Suc m) - 1"
      using m1 ln_le_minus_one[of "real m / real (Suc m)"]
      by simp
    moreover have "ln (real m / real (Suc m)) = A - B" using m1 unfolding A_def B_def
      by (simp add: ln_div)
    moreover have "real m / real (Suc m) - 1 = - 1 / real (Suc m)" using m1
      by (simp add: field_simps)
    ultimately have d4a: "A - B \<le> - 1 / real (Suc m)"
      by simp
    have d4: "real (Suc m) * (A - B) \<le> - 1" using mult_left_mono[OF d4a, of "real (Suc m)"] m1
      by simp
    have f: "(\<Sum> k = 1..Suc m. ln (real k)) = B + (\<Sum> k = 1..m. ln (real k))"
      unfolding B_def
      by simp
    have e: "real (Suc m) * (A - B) = real m * A + A - real (Suc m) * B"
      by (simp add: algebra_simps)
    have s: "real (Suc m) = real m + 1"
      by simp
    have "(\<Sum> k = 1..Suc m. ln (real k)) \<le> real (Suc m) * B - real (Suc m) + B + 1"
      using e f d4 IH s
      by simp
    thus ?case unfolding B_def .
  qed
qed

lemma ln_int0: "0 < (c :: real) \<Longrightarrow> ln integrable_on {0..c}"
  using set_borel_integral_eq_integral(1)[OF ln_integrable_near_zero] integrable_on_Icc_iff_Ioo
  by auto

lemma integral_ln_0: "0 < (b :: real) \<Longrightarrow>
  integral {0..b} (\<lambda>u. ln u) = b * ln b - b"
proof -
  assume b: "0 < b"
  have "integral {0..b} (\<lambda>u. ln u) =
    integral {0..b} (\<lambda>u. (1 / 2) *\<^sub>R ln (0 + u ^ 2))"
    by (simp add: ln_realpow)
  also have "\<dots> = (1 / 2) * (2 * (b * ln b - b))" using Ic_zero[OF b]
    by simp
  also have "\<dots> = b * ln b - b"
    by simp
  finally show ?thesis .
qed

text \<open>Telescoping a sum of integrals over the cells
  @{text "[(j-1)/\<kappa>, j/\<kappa>]"}.\<close>
lemma tele_gen:
  fixes g :: "real \<Rightarrow> real" and \<kappa> :: real
  assumes k: "0 < \<kappa>" and gi: "\<And>c. 0 < c \<Longrightarrow> g integrable_on {0..c}"
  shows "(\<Sum> j = 1..n. integral {real (j - 1) / \<kappa>..real j / \<kappa>} g) =
    integral {0..real n / \<kappa>} g"
proof (induction n)
  case 0
  show ?case
    by simp
next
  case (Suc n)
  have a: "0 \<le> real n / \<kappa>" using k
    by simp
  have b: "real n / \<kappa> \<le> real (Suc n) / \<kappa>" using k
    by (simp add: divide_right_mono)
  have i: "g integrable_on {0..real (Suc n) / \<kappa>}" using gi k
    by simp
  have c: "integral {0..real n / \<kappa>} g + integral {real n / \<kappa>..real (Suc n) /
    \<kappa>} g = integral {0..real (Suc n) / \<kappa>} g"
    using Henstock_Kurzweil_Integration.integral_combine[OF a b i] .
  show ?case using Suc.IH c
    by simp
qed

text \<open>(6.12): @{text "\<Sum>_{j\<le>m} log(t + (j/\<kappa>)^2) -
  \<kappa> \<integral>_0^{m/\<kappa>} log(t + u^2) du \<le>
  2 log m + 2"}: on each cell @{text "[(j-1)/\<kappa>, j/\<kappa>]"},
  @{text "log(t + b^2) - log(t + u^2) \<le> 2 log b - 2 log u"}.\<close>
lemma sum_le_int:
  "0 < t \<Longrightarrow> 0 < \<kappa> \<Longrightarrow> 1 \<le> m \<Longrightarrow>
     (\<Sum> j = 1..m. ln (t + (real j / \<kappa>) ^ 2)) \<le>
       \<kappa> * integral {0..real m / \<kappa>} (\<lambda>u. ln (t + u ^ 2)) + 2 * ln (real m) +
       2"
proof -
  assume t: "0 < t" and k: "0 < \<kappa>" and m: "1 \<le> m"
  have cell: "\<And>j. 1 \<le> j \<Longrightarrow>
    ln (t + (real j / \<kappa>) ^ 2) / \<kappa> - integral {real (j - 1) / \<kappa>..real j /
    \<kappa>} (\<lambda>u. ln (t + u ^ 2))
                  \<le> integral {real (j - 1) / \<kappa>..real j / \<kappa>} (\<lambda>u. 2 *
                    ln (real j / \<kappa>) - 2 * ln u)"
  proof -
    fix j :: nat assume j: "1 \<le> j"
    define a where "a = real (j - 1) / \<kappa>"
    define b where "b = real j / \<kappa>"
    have a0: "0 \<le> a" unfolding a_def using k
      by simp
    have b0: "0 < b" unfolding b_def using k j
      by simp
    have ab: "a \<le> b" unfolding a_def b_def using k j
      by (simp add: divide_right_mono)
    have ba: "b - a = 1 / \<kappa>" unfolding a_def b_def using j
      by (simp add: of_nat_diff diff_divide_distrib)
    have tp: "0 < t + u ^ 2" for u :: real using t
      by (simp add: add_pos_nonneg)
    have "t + u ^ 2 \<noteq> 0" for u :: real using tp[of u]
      by simp
    hence c1: "continuous_on {a..b} (\<lambda>u. ln (t + u ^ 2))"
      by (fast intro: continuous_intros)
    have i1: "(\<lambda>u. ln (t + u ^ 2)) integrable_on {a..b}"
      using integrable_continuous_interval[OF c1]
      by simp
    have i2: "(\<lambda>u. 2 * ln b - 2 * ln u) integrable_on {a..b}"
    proof -
      have l: "ln integrable_on {a..b}"
        using integrable_on_subinterval[OF ln_int0[OF b0], of a b] a0
        by simp
      show ?thesis using l
        by (auto intro: Henstock_Kurzweil_Integration.integrable_diff integrable_const_ivl
          integrable_on_cmult_left)
    qed
    have i3: "(\<lambda>u. ln (t + b ^ 2) - ln (t + u ^ 2)) integrable_on {a..b}" using i1
      by (auto intro: Henstock_Kurzweil_Integration.integrable_diff integrable_const_ivl)
    have pw: "ln (t + b ^ 2) - ln (t + u ^ 2) \<le> 2 * ln b - 2 * ln u" if u: "0 < u" "u \<le> b"
      for u
    proof -
      have m: "(t + b ^ 2) * u ^ 2 \<le> b ^ 2 * (t + u ^ 2)"
      proof -
        have "u ^ 2 \<le> b ^ 2" using u
          by (simp add: power_mono)
        hence "t * u ^ 2 \<le> t * b ^ 2" using t
          by (simp add: mult_left_mono)
        thus ?thesis
          by (simp add: algebra_simps)
      qed
      have l: "ln ((t + b ^ 2) * u ^ 2) \<le> ln (b ^ 2 * (t + u ^ 2))"
        using m u tp[of u] tp[of b] b0
        by simp
      have l1: "ln ((t + b ^ 2) * u ^ 2) = ln (t + b ^ 2) + 2 * ln u" using u tp[of b]
        by (simp add: ln_mult ln_realpow)
      have l2: "ln (b ^ 2 * (t + u ^ 2)) = 2 * ln b + ln (t + u ^ 2)" using b0 tp[of u]
        by (simp add: ln_mult ln_realpow)
      show ?thesis using l l1 l2
        by simp
    qed
    have le: "integral {a<..<b} (\<lambda>u. ln (t + b ^ 2) - ln (t + u ^ 2)) \<le>
      integral {a<..<b} (\<lambda>u. 2 * ln b - 2 * ln u)"
    proof (rule integral_le)
      show "(\<lambda>u. ln (t + b ^ 2) - ln (t + u ^ 2)) integrable_on {a<..<b}" using i3
        by (simp add: integrable_on_Icc_iff_Ioo["symmetric"])
      show "(\<lambda>u. 2 * ln b - 2 * ln u) integrable_on {a<..<b}" using i2
        by (simp add: integrable_on_Icc_iff_Ioo["symmetric"])
      fix u assume "u \<in> {a<..<b}"
      thus "ln (t + b ^ 2) - ln (t + u ^ 2) \<le> 2 * ln b - 2 * ln u" using pw a0
        by simp
    qed
    have eqL: "ln (t + b ^ 2) / \<kappa> - integral {a..b} (\<lambda>u. ln (t + u ^ 2)) =
      integral {a<..<b} (\<lambda>u. ln (t + b ^ 2) - ln (t + u ^ 2))"
    proof -
      have "integral {a..b} (\<lambda>u. ln (t + b ^ 2) - ln (t + u ^ 2)) =
        integral {a..b} (\<lambda>u. ln (t + b ^ 2)) - integral {a..b} (\<lambda>u. ln (t + u ^ 2))"
        using i1
        using Henstock_Kurzweil_Integration.integral_diff by blast
      moreover have "integral {a..b} (\<lambda>u. ln (t + b ^ 2)) = ln (t + b ^ 2) / \<kappa>"
        using ab ba
        by (simp add: content_real)
      moreover have "integral {a..b} (\<lambda>u. ln (t + b ^ 2) - ln (t + u ^ 2)) =
        integral {a<..<b} (\<lambda>u. ln (t + b ^ 2) - ln (t + u ^ 2))"
        by (simp add: integral_open_interval_real)
      ultimately show ?thesis
        by simp
    qed
    have eqR: "integral {a..b} (\<lambda>u. 2 * ln b - 2 * ln u) =
      integral {a<..<b} (\<lambda>u. 2 * ln b - 2 * ln u)"
      by (simp add: integral_open_interval_real)
    show "ln (t + (real j / \<kappa>) ^ 2) / \<kappa> - integral {real (j - 1) / \<kappa>..real j /
      \<kappa>} (\<lambda>u. ln (t + u ^ 2))
                  \<le> integral {real (j - 1) / \<kappa>..real j / \<kappa>} (\<lambda>u. 2 *
                    ln (real j / \<kappa>) - 2 * ln u)"
      using le eqL eqR unfolding a_def b_def
      by simp
  qed
  have fi: "(\<lambda>u. ln (t + u ^ 2)) integrable_on {0..c}" for c
  proof -
    have "t + u ^ 2 \<noteq> 0" for u :: real using add_pos_nonneg[OF t zero_le_power2[of u]]
      by simp
    hence "continuous_on {0..c} (\<lambda>u. ln (t + u ^ 2))"
      by (fast intro: continuous_intros)
    thus ?thesis
      by (auto intro: integrable_continuous_interval)
  qed
  have tele: "(\<Sum> j = 1..m. integral {real (j - 1) / \<kappa>..real j /
    \<kappa>} (\<lambda>u. ln (t + u ^ 2))) =
    integral {0..real m / \<kappa>} (\<lambda>u. ln (t + u ^ 2))"
    using tele_gen[OF k fi]
    by simp
  have rhs: "(\<Sum> j = 1..m. integral {real (j - 1) / \<kappa>..real j /
    \<kappa>} (\<lambda>u. 2 * ln (real j / \<kappa>) - 2 * ln u))
               = (2 / \<kappa>) * (\<Sum> j =
                 1..m. ln (real j)) - 2 * (real m / \<kappa>) * ln (real m) + 2 * real m / \<kappa>"
  proof -
    have li: "ln integrable_on {0..c}" if "0 < c" for c :: real using ln_int0[OF that] .
    have cellR: "integral {real (j - 1) / \<kappa>..real j / \<kappa>} (\<lambda>u. 2 * ln (real j /
      \<kappa>) - 2 * ln u) = 2 * ln (real j / \<kappa>) / \<kappa> - 2 * integral {real (j - 1) /
      \<kappa>..real j / \<kappa>} ln" if j: "1 \<le> j" for j
    proof -
      have jb: "0 < real j / \<kappa>" using j k
        by simp
      have lc: "ln integrable_on {real (j - 1) / \<kappa>..real j / \<kappa>}"
        using integrable_on_subinterval[OF li[OF jb],
        of "real (j - 1) / \<kappa>" "real j / \<kappa>"] k
        by (simp add: divide_right_mono)
      have l2: "(\<lambda>u. 2 * ln u) integrable_on {real (j - 1) / \<kappa>..real j / \<kappa>}"
        using lc
        by (auto intro: integrable_on_cmult_left)
      have d: "integral {real (j - 1) / \<kappa>..real j / \<kappa>} (\<lambda>u. 2 * ln (real j /
        \<kappa>) - 2 * ln u) = integral {real (j - 1) / \<kappa>..real j /
        \<kappa>} (\<lambda>u. 2 * ln (real j / \<kappa>)) - integral {real (j - 1) /
        \<kappa>..real j / \<kappa>} (\<lambda>u. 2 * ln u)"
        using l2 Henstock_Kurzweil_Integration.integral_diff[OF integrable_const_ivl l2]
        by simp
      have c: "integral {real (j - 1) / \<kappa>..real j / \<kappa>} (\<lambda>u. 2 * ln (real j /
        \<kappa>)) = 2 * ln (real j / \<kappa>) / \<kappa>" using j k
        by (simp add: content_real of_nat_diff diff_divide_distrib)
      have e: "integral {real (j - 1) / \<kappa>..real j / \<kappa>} (\<lambda>u. 2 * ln u) =
        2 * integral {real (j - 1) / \<kappa>..real j / \<kappa>} ln"
        using integral_mult[OF lc, of 2]
        by simp
      show ?thesis unfolding d c e ..
    qed
    have s1: "(\<Sum> j = 1..m. integral {real (j - 1) / \<kappa>..real j /
      \<kappa>} (\<lambda>u. 2 * ln (real j / \<kappa>) - 2 * ln u)) = (\<Sum> j =
      1..m. 2 * ln (real j / \<kappa>) / \<kappa>) - 2 * (\<Sum> j =
      1..m. integral {real (j - 1) / \<kappa>..real j / \<kappa>} ln)"
      using cellR
      by (simp add: sum_subtractf sum_distrib_left)
    have lnd: "ln (real j / \<kappa>) = ln (real j) - ln \<kappa>" if "1 \<le> j" for j using that k
      by (simp add: ln_div)
    have s2: "(\<Sum> j = 1..m. 2 * ln (real j / \<kappa>) / \<kappa>) =
      (2 / \<kappa>) * (\<Sum> j = 1..m. ln (real j)) - 2 * real m / \<kappa> * ln \<kappa>"
    proof -
      have "(\<Sum> j = 1..m. 2 * ln (real j / \<kappa>) / \<kappa>) = (\<Sum> j =
        1..m. (2 / \<kappa>) * ln (real j) - (2 / \<kappa>) * ln \<kappa>)"
      proof (rule sum.cong)
        fix j assume "j \<in> {1..m}"
        hence j1: "1 \<le> j"
          by simp
        show "2 * ln (real j / \<kappa>) / \<kappa> =
          (2 / \<kappa>) * ln (real j) - (2 / \<kappa>) * ln \<kappa>" using lnd[OF j1]
          by (simp add: diff_divide_distrib right_diff_distrib)
      next
        show "{1..m} = {1..m}"
          by simp
      qed
      also have "\<dots> = (2 / \<kappa>) * (\<Sum> j =
        1..m. ln (real j)) - 2 * real m / \<kappa> * ln \<kappa>"
        by (simp add: sum_subtractf sum_distrib_left)
      finally show ?thesis .
    qed
    have sumL: "(\<Sum> j = 1..m. integral {real (j - 1) / \<kappa>..real j / \<kappa>} ln) =
      integral {0..real m / \<kappa>} ln" using tele_gen[OF k li] .
    have mk: "0 < real m / \<kappa>" using m k
      by simp
    have lnI: "integral {0..real m / \<kappa>} ln =
      real m / \<kappa> * ln (real m / \<kappa>) - real m / \<kappa>" using integral_ln_0[OF mk] .
    have lnm: "ln (real m / \<kappa>) = ln (real m) - ln \<kappa>" using m k
      by (simp add: ln_div)
    show ?thesis unfolding s1 s2 sumL lnI lnm
      by (simp add: algebra_simps)
  qed
  have "(\<Sum> j = 1..m. ln (t + (real j / \<kappa>) ^ 2)) / \<kappa> - integral {0..real m /
    \<kappa>} (\<lambda>u. ln (t + u ^ 2))
          \<le> (2 / \<kappa>) * (\<Sum> j =
            1..m. ln (real j)) - 2 * (real m / \<kappa>) * ln (real m) + 2 * real m / \<kappa>"
    unfolding tele[symmetric] rhs[symmetric] sum_divide_distrib sum_subtractf[symmetric]
      by (rule sum_mono) (use cell in simp)
  also have "\<dots> \<le> (2 / \<kappa>) * (ln (real m) + 1)"
    using sum_log_le[OF m] k by (simp add: field_simps)
  finally have F: "(\<Sum> j = 1..m. ln (t + (real j / \<kappa>) ^ 2)) / \<kappa> -
    integral {0..real m / \<kappa>} (\<lambda>u. ln (t + u ^ 2)) \<le>
    (2 / \<kappa>) * (ln (real m) + 1)" .
  have "\<kappa> * ((\<Sum> j = 1..m. ln (t + (real j / \<kappa>) ^ 2)) / \<kappa> -
    integral {0..real m / \<kappa>} (\<lambda>u. ln (t + u ^ 2))) \<le>
    \<kappa> * ((2 / \<kappa>) * (ln (real m) + 1))"
    using mult_left_mono[OF F less_imp_le[OF k]] by simp
  moreover have "\<kappa> * ((\<Sum> j =
    1..m. ln (t + (real j / \<kappa>) ^ 2)) / \<kappa> - integral {0..real m /
    \<kappa>} (\<lambda>u. ln (t + u ^ 2))) = (\<Sum> j =
    1..m. ln (t + (real j / \<kappa>) ^ 2)) - \<kappa> * integral {0..real m /
    \<kappa>} (\<lambda>u. ln (t + u ^ 2))"
    using k by (simp add: algebra_simps)
  moreover have "\<kappa> * ((2 / \<kappa>) * (ln (real m) + 1)) = 2 * ln (real m) + 2"
    using k by (simp add: algebra_simps)
  ultimately show ?thesis by simp
qed

text \<open>The one-coordinate bound: (6.11) and (6.12) give
  @{text "D_N(y^2)^6/D_K(y^2) w(y) \<le>
    8192 e^1^2 K^{12N+12}/K^{2K} (1+y)^5 e^{-K V((y/K)^2)}"}.\<close>
lemma g_le:
  assumes "1 \<le> N" "N \<le> K" "real N / real K = 3 / 40" "0 < y"
  shows "real_eval (Dm N) (y ^ 2) ^ 6 / real_eval (Dm K) (y ^ 2) * weight y \<le>
         8192 * exp 12 * real K ^ (12 * N + 12) / real K ^ (2 * K) *
           ((1 + y) ^ 5 * exp (- real K * Vf ((y / real K) ^ 2)))"
proof -
  define t where "t = (y / real K) ^ 2"
  define \<kappa> where "\<kappa> = real K"
  have K0: "0 < \<kappa>" using assms unfolding \<kappa>_def by simp
  have t0: "0 < t" using assms unfolding t_def by simp
  have Dm_exp: "\<And>m. real_eval (Dm m) (y ^ 2) = \<kappa> ^ (2 * m) * exp (\<Sum> j =
    1..m. ln (t + (real j / \<kappa>) ^ 2))"
  proof -
    fix m
    have f: "real_eval (Dm m) (y ^ 2) = (\<Prod> j = 1..m. y ^ 2 + real j ^ 2)"
      unfolding Dm_def real_eval_prod
      by (simp add: real_eval_simps of_rat_power)
    have each: "y ^ 2 + real j ^ 2 = \<kappa> ^ 2 * exp (ln (t + (real j / \<kappa>) ^ 2))" for j
    proof -
      have p: "0 < t + (real j / \<kappa>) ^ 2" using t0
        by (simp add: add_pos_nonneg)
      have "y ^ 2 + real j ^ 2 = \<kappa> ^ 2 * (t + (real j / \<kappa>) ^ 2)"
        unfolding t_def \<kappa>_def using K0 unfolding \<kappa>_def
        by (simp add: power_divide field_simps)
      thus ?thesis using p
        by simp
    qed
    have "(\<Prod> j = 1..m. y ^ 2 + real j ^ 2) = (\<Prod> j =
      1..m. \<kappa> ^ 2 * exp (ln (t + (real j / \<kappa>) ^ 2)))" unfolding each ..
    also have "\<dots> = (\<kappa> ^ 2) ^ m * exp (\<Sum> j =
      1..m. ln (t + (real j / \<kappa>) ^ 2))"
      by (simp add: prod.distrib exp_sum)
    also have "\<dots> = \<kappa> ^ (2 * m) * exp (\<Sum> j =
      1..m. ln (t + (real j / \<kappa>) ^ 2))"
      by (simp add: power_mult)
    finally show "real_eval (Dm m) (y ^ 2) = \<kappa> ^ (2 * m) * exp (\<Sum> j =
      1..m. ln (t + (real j / \<kappa>) ^ 2))" unfolding f .
  qed
  have lower: "\<kappa> * integral {0..real K / \<kappa>} (\<lambda>u. ln (t + u ^ 2)) \<le>
    (\<Sum> j = 1..K. ln (t + (real j / \<kappa>) ^ 2))"
    by (rule sum_ge_int[OF t0 K0])
  have upper: "(\<Sum> j = 1..N. ln (t + (real j / \<kappa>) ^ 2)) \<le>
    \<kappa> * integral {0..real N / \<kappa>} (\<lambda>u. ln (t + u ^ 2)) + 2 * ln (real N) + 2"
    by (rule sum_le_int[OF t0 K0 assms(1)])
  have V: "\<kappa> * Vf t = 2 * pi * y + \<kappa> * integral {0..1} (\<lambda>u. ln (t + u ^ 2)) -
    6 * \<kappa> * integral {0..3 / 40} (\<lambda>u. ln (t + u ^ 2))"
    unfolding Vf_def t_def \<kappa>_def
      using real_sqrt_abs[of "y / real K"] assms(4) K0[unfolded \<kappa>_def]
    by (simp add: algebra_simps)
  have ends: "real K / \<kappa> = 1" "real N / \<kappa> = 3 / 40" using assms(3) K0
    unfolding \<kappa>_def by simp_all
  have w: "weight y \<le> 8192 * (1 + y) ^ 5 * exp (- 2 * pi * y)" by (rule weight_le[OF assms(4)])
  have "real_eval (Dm N) (y ^ 2) ^ 6 / real_eval (Dm K) (y ^ 2) * weight y
          \<le> \<kappa> ^ (12 * N) / \<kappa> ^ (2 * K) * exp (6 * (\<kappa> * integral {0..3 /
            40} (\<lambda>u. ln (t + u ^ 2)) + 2 * ln (real N) + 2) - \<kappa> *
            integral {0..1} (\<lambda>u. ln (t + u ^ 2))) * (8192 * (1 + y) ^ 5 * exp (- 2 * pi *
            y))"
  proof -
    have q: "real_eval (Dm N) (y ^ 2) ^ 6 / real_eval (Dm K) (y ^ 2) =
      \<kappa> ^ (12 * N) / \<kappa> ^ (2 * K) * exp (6 * (\<Sum> j =
      1..N. ln (t + (real j / \<kappa>) ^ 2)) - (\<Sum> j =
      1..K. ln (t + (real j / \<kappa>) ^ 2)))"
      unfolding Dm_exp using exp_of_nat_mult[of 6 "\<Sum> j =
        1..N. ln (t + (real j / \<kappa>) ^ 2)"]
      by (simp add: power_mult_distrib exp_diff power_mult["symmetric"])
    have ex: "exp (6 * (\<Sum> j = 1..N. ln (t + (real j / \<kappa>) ^ 2)) - (\<Sum> j =
      1..K. ln (t + (real j / \<kappa>) ^ 2))) \<le>
      exp (6 * (\<kappa> * integral {0..3 / 40} (\<lambda>u. ln (t + u ^ 2)) + 2 * ln (real N) +
      2) - \<kappa> * integral {0..1} (\<lambda>u. ln (t + u ^ 2)))"
      using upper lower unfolding ends
      by simp
    have w0: "0 < weight y" by (rule weight_pos[OF assms(4)])
    have c0: "0 \<le> \<kappa> ^ (12 * N) / \<kappa> ^ (2 * K)" using K0
      by simp
    have "real_eval (Dm N) (y ^ 2) ^ 6 / real_eval (Dm K) (y ^ 2) * weight y =
      \<kappa> ^ (12 * N) / \<kappa> ^ (2 * K) * exp (6 * (\<Sum> j =
      1..N. ln (t + (real j / \<kappa>) ^ 2)) - (\<Sum> j =
      1..K. ln (t + (real j / \<kappa>) ^ 2))) * weight y"
      unfolding q ..
    also have "\<dots> \<le> \<kappa> ^ (12 * N) / \<kappa> ^ (2 * K) * exp (6 * (\<kappa> *
      integral {0..3 / 40} (\<lambda>u. ln (t + u ^ 2)) + 2 * ln (real N) + 2) - \<kappa> *
      integral {0..1} (\<lambda>u. ln (t + u ^ 2))) * (8192 * (1 + y) ^ 5 * exp (- 2 * pi * y))"
      using mult_mono[OF mult_left_mono[OF ex c0] w] less_imp_le[OF w0] mult_nonneg_nonneg[OF c0
        exp_ge_zero]
      by simp
    finally show ?thesis .
  qed
  also have "\<dots> \<le> 8192 * exp 12 * real K ^ (12 * N + 12) / real K ^ (2 * K) * ((1 +
    y) ^ 5 * exp (- real K * Vf ((y / real K) ^ 2)))"
  proof -
    have V': "6 * (\<kappa> * integral {0..3 / 40} (\<lambda>u. ln (t + u ^ 2)) + 2 * ln (real N) +
      2) - \<kappa> * integral {0..1} (\<lambda>u. ln (t + u ^ 2)) + (- 2 * pi * y) =
      12 * ln (real N) + 12 + (- \<kappa> * Vf t)"
      using V
      by simp
    have N0: "0 < real N" using assms(1)
      by simp
    have e1: "exp (6 * (\<kappa> * integral {0..3 / 40} (\<lambda>u. ln (t + u ^ 2)) + 2 *
      ln (real N) + 2) - \<kappa> * integral {0..1} (\<lambda>u. ln (t + u ^ 2))) * exp (- 2 * pi *
      y) = real N ^ 12 * exp 12 * exp (- \<kappa> * Vf t)"
    proof -
      have "exp (6 * (\<kappa> * integral {0..3 / 40} (\<lambda>u. ln (t + u ^ 2)) + 2 *
        ln (real N) + 2) - \<kappa> * integral {0..1} (\<lambda>u. ln (t + u ^ 2))) * exp (- 2 *
        pi * y) = exp (12 * ln (real N)) * exp 12 * exp (- \<kappa> * Vf t)"
        unfolding mult_exp_exp V'
        by (simp add: exp_add)
      also have "exp (12 * ln (real N)) = real N ^ 12"
        using N0 exp_ln[of "real N ^ 12"] ln_realpow[of "real N" 12]
        by simp
      finally show ?thesis .
    qed
    have N12: "real N ^ 12 \<le> real K ^ 12" using assms(2)
      by (simp add: power_mono)
    have "\<kappa> ^ (12 * N) / \<kappa> ^ (2 * K) * exp (6 * (\<kappa> * integral {0..3 /
      40} (\<lambda>u. ln (t + u ^ 2)) + 2 * ln (real N) + 2) - \<kappa> *
      integral {0..1} (\<lambda>u. ln (t + u ^ 2))) * (8192 * (1 + y) ^ 5 * exp (- 2 * pi * y))
        = 8192 * exp 12 * \<kappa> ^ (12 * N) * real N ^ 12 / \<kappa> ^ (2 * K) * ((1 + y) ^ 5 *
          exp (- \<kappa> * Vf t))"
      using e1
      by (simp add: algebra_simps)
    also have "\<dots> \<le> 8192 * exp 12 * \<kappa> ^ (12 * N) * real K ^ 12 / \<kappa> ^ (2 *
      K) * ((1 + y) ^ 5 * exp (- \<kappa> * Vf t))"
      using N12 K0 assms(4)
      by (simp add: mult_left_mono mult_right_mono divide_right_mono)
    also have "\<dots> = 8192 * exp 12 * real K ^ (12 * N + 12) / real K ^ (2 * K) * ((1 + y) ^ 5 *
      exp (- real K * Vf ((y / real K) ^ 2)))"
      unfolding \<kappa>_def t_def
      by (simp add: power_add)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

subsection \<open>(6.9) The bound for every configuration\<close>

text \<open>(6.9): for every configuration @{text "0 \<le> t_1, \<dots>, t_h"} of distinct points,
  @{text "2\<Sum>_{i<j} log|t_i - t_j| - K\<Sum>V(t_i) + \<Sum>\<surd>t_i \<le>
    (\<lambda>M_0 - I(\<rho>))K^2 + (120 + \<surd>2)h + 2h log K"}.
  Proof: regularise by circle measures of radius @{text "\<epsilon> = 1/(4K^2)"}, apply Lemma 6.2 to
  @{text "\<sigma> = K^-^1\<Sum>\<omega>_i"} and @{text \<rho>},
    the circle average of @{text "log|z-a|"}, the arcsine mass bound
  @{text "\<rho>([x-r, x+r]) \<le> 40\<surd>r"}, and (6.7) (Lean: @{text Config69}).\<close>
lemma rho_singleton: "emeasure rho {a} = 0"
  using rho_Icc_le[of 0 a] by simp

text \<open>The cross bound: @{text "\<integral> ln\<^sup>+(\<epsilon>/|x - u|) d\<rho>(u) \<le>
  80 sqrt \<epsilon>"}, by the layer cake over @{text "rho_Icc_le"}.\<close>
lemma cross_bound:
  fixes x e :: real
  assumes e: "0 < e"
  shows "(\<integral>\<^sup>+ u. ennreal (max 0 (ln (e / \<bar>x - u\<bar>))) \<partial>rho) \<le>
    ennreal (80 * sqrt e)"
proof -
  have cake: "\<And>a :: real. 0 \<le> a \<Longrightarrow>
    ennreal a = (\<integral>\<^sup>+ s. indicator {0..<a} s \<partial>lborel)"
    by (simp add: emeasure_lborel_Ico)
  have level: "\<And>s u. 0 \<le> s \<Longrightarrow> u \<noteq> x \<Longrightarrow>
    (s < ln (e / \<bar>x - u\<bar>)) \<longleftrightarrow> \<bar>x - u\<bar> < e * exp (- s)"
  proof -
    fix s u :: real
    assume s0: "0 \<le> s" and ux: "u \<noteq> x"
    have d0: "0 < \<bar>x - u\<bar>" using ux by simp
    have l1: "(s < ln (e / \<bar>x - u\<bar>)) \<longleftrightarrow> exp s < e / \<bar>x - u\<bar>"
      using d0 e ln_less_cancel_iff[of "exp s" "e / \<bar>x - u\<bar>"] by simp
    have l2a: "e * exp (- s) = e / exp s" by (simp add: exp_minus divide_inverse)
    have l2: "exp s < e / \<bar>x - u\<bar> \<longleftrightarrow>
      \<bar>x - u\<bar> < e * exp (- s)" unfolding l2a
      using d0 pos_less_divide_eq[of "\<bar>x -
      u\<bar>" "exp s" e] pos_less_divide_eq[of "exp s" "\<bar>x - u\<bar>" e]
      by (simp add: mult.commute)
    show "(s < ln (e / \<bar>x - u\<bar>)) \<longleftrightarrow> \<bar>x - u\<bar> < e * exp (- s)"
      using l1 l2 by (rule trans)
  qed
  have swap: "(\<integral>\<^sup>+ u. ennreal (max 0 (ln (e / \<bar>x - u\<bar>))) \<partial>rho)
      = (\<integral>\<^sup>+ s. emeasure rho {u. \<bar>x - u\<bar> <
        e * exp (- s)} * indicator {0..} s \<partial>lborel)"
  proof -
    define f where "f u = max 0 (ln (e / \<bar>x - u\<bar>))" for u :: real
    have fnn: "\<And>u. 0 \<le> f u" unfolding f_def by simp
    have A: "(\<integral>\<^sup>+ u. ennreal (f u) \<partial>rho) =
      (\<integral>\<^sup>+ u. (\<integral>\<^sup>+ s. indicator {0..<f u} s \<partial>lborel)
      \<partial>rho)"
      using cake[OF fnn] by simp
    have "finite_measure rho" using rho_univ by (auto simp: rho_def intro: finite_measureI)
    hence ps: "pair_sigma_finite rho lborel" using sigma_finite_lborel
      unfolding pair_sigma_finite_def finite_measure_def by simp
    have sr: "sets (rho \<Otimes>\<^sub>M lborel) = sets (borel \<Otimes>\<^sub>M borel)"
      unfolding rho_def using sets_pair_measure_cong by simp
    have mf0a: "(\<lambda>p :: real \<times> real. indicator {p :: real \<times> real. 0 \<le>
      snd p \<and> snd p < max 0 (ln (e / \<bar>x - fst p\<bar>))} p :: ennreal) \<in>
      borel_measurable (borel \<Otimes>\<^sub>M borel)"
      by measurable
    have mf0e: "(\<lambda>p :: real \<times> real. indicator {0..<f (fst p)} (snd p) :: ennreal) =
      (\<lambda>p :: real \<times> real. indicator {p :: real \<times> real. 0 \<le> snd p \<and>
      snd p < max 0 (ln (e / \<bar>x - fst p\<bar>))} p :: ennreal)"
      unfolding f_def by (simp add: indicator_def)
    have mf0: "(\<lambda>p :: real \<times>
      real. indicator {0..<f (fst p)} (snd p) :: ennreal) \<in>
      borel_measurable (borel \<Otimes>\<^sub>M borel)" unfolding mf0e by (rule mf0a)
    have mf: "(\<lambda>(u, s). indicator {0..<f u} s :: ennreal) \<in>
      borel_measurable (rho \<Otimes>\<^sub>M lborel)" unfolding split_beta'
      using mf0 measurable_cong_sets[OF sr refl] by auto
    have B: "(\<integral>\<^sup>+ u. (\<integral>\<^sup>+ s. indicator {0..<f u} s \<partial>lborel)
      \<partial>rho) = (\<integral>\<^sup>+ s. (\<integral>\<^sup>+ u. indicator {0..<f u} s
      \<partial>rho) \<partial>lborel)"
      using pair_sigma_finite.Fubini'[OF ps mf] by simp
    have C: "\<And>s. (\<integral>\<^sup>+ u. indicator {0..<f u} s \<partial>rho) =
      emeasure rho {u. \<bar>x - u\<bar> < e * exp (- s)} * indicator {0..} s"
    proof -
      fix s :: real
      show "(\<integral>\<^sup>+ u. indicator {0..<f u} s \<partial>rho) =
        emeasure rho {u. \<bar>x - u\<bar> < e * exp (- s)} * indicator {0..} s"
      proof (cases "0 \<le> s")
        case False
        have z: "\<And>u. (indicator {0..<f u} s :: ennreal) = 0" using False by simp
        show ?thesis using False unfolding z by simp
      next
        case True
        have ind: "\<And>u. (indicator {0..<f u} s :: ennreal) = indicator ({u. \<bar>x - u\<bar> <
          e * exp (- s)} - {x}) u"
        proof -
          fix u :: real
          show "(indicator {0..<f u} s :: ennreal) = indicator ({u. \<bar>x - u\<bar> <
            e * exp (- s)} - {x}) u"
          proof (cases "u = x")
            case True
            have fx: "f u = 0" unfolding f_def True by simp
            show ?thesis unfolding fx using True by simp
          next
            case False
            have "(s < f u) \<longleftrightarrow> \<bar>x - u\<bar> < e * exp (- s)"
              unfolding f_def using level[OF \<open>0 \<le> s\<close> False] \<open>0 \<le>
              s\<close> by linarith
            thus ?thesis using False \<open>0 \<le> s\<close> unfolding indicator_def by simp
          qed
        qed
        have meas2: "{u. \<bar>x - u\<bar> < e * exp (- s)} \<in> sets rho" unfolding rho_def
          by simp
        have null: "{x} \<in> null_sets rho" using rho_singleton[of x] unfolding rho_def by auto
        have meas3: "{u. \<bar>x - u\<bar> < e * exp (- s)} - {x} \<in> sets rho" using meas2 null
          by auto
        show ?thesis unfolding ind using True meas3 emeasure_Diff_null_set[OF null meas2] by simp
      qed
    qed
    have "(\<integral>\<^sup>+ u. ennreal (f u) \<partial>rho) =
      (\<integral>\<^sup>+ s. emeasure rho {u. \<bar>x - u\<bar> <
      e * exp (- s)} * indicator {0..} s \<partial>lborel)"
      unfolding A B C ..
    thus ?thesis unfolding f_def .
  qed
  have ball: "\<And>s. emeasure rho {u. \<bar>x - u\<bar> < e * exp (- s)} \<le>
    ennreal (40 * sqrt (e * exp (- s)))"
  proof -
    fix s :: real
    have r0: "0 \<le> e * exp (- s)" using e by simp
    have sub: "{u. \<bar>x - u\<bar> < e * exp (- s)} \<subseteq>
      {x - e * exp (- s)..x + e * exp (- s)}" by auto
    have meas: "{x - e * exp (- s)..x + e * exp (- s)} \<in> sets rho" unfolding rho_def by simp
    show "emeasure rho {u. \<bar>x - u\<bar> < e * exp (- s)} \<le>
      ennreal (40 * sqrt (e * exp (- s)))"
      using emeasure_mono[OF sub meas] rho_Icc_le[OF r0, of x] by (rule order_trans)
  qed
  have tail: "(\<integral>\<^sup>+ s. ennreal (40 * sqrt (e * exp (- s))) *
    indicator {0..} s \<partial>lborel) = ennreal (80 * sqrt e)"
  proof -
    have sq: "\<And>s. sqrt (e * exp (- s)) = sqrt e * exp (- s / 2)"
    proof -
      fix s :: real
      have ee: "exp (- s) = exp (- s / 2) * exp (- s / 2)" by (simp add: exp_add["symmetric"])
      show "sqrt (e * exp (- s)) = sqrt e * exp (- s / 2)" unfolding ee
        using real_sqrt_mult[of e "exp (- s / 2) * exp (- s / 2)"] by simp
    qed
    have m: "(\<lambda>s. 40 * (sqrt e * exp (- s / 2))) \<in> borel_measurable borel" by simp
    have d: "\<And>s. 0 \<le> s \<Longrightarrow>
      ((\<lambda>s. - 80 * sqrt e * exp (- s / 2)) has_real_derivative 40 * (sqrt e * exp (- s /
      2))) (at s)" by (force intro: derivative_eq_intros)
    have n: "\<And>s. 0 \<le> s \<Longrightarrow> 0 \<le> 40 * (sqrt e * exp (- s / 2))" using e
      by simp
    have h1: "filterlim (\<lambda>s::real. 1 / 2 * s) at_top at_top"
      using filterlim_tendsto_pos_mult_at_top[OF tendsto_const _ filterlim_ident,
      of "1 / 2 :: real"] by simp
    have h2: "((\<lambda>y::real. exp (- y)) \<longlongrightarrow> 0) at_top"
      by (intro filterlim_compose[OF exp_at_bot] filterlim_uminus_at_bot_at_top)
    have h3: "((\<lambda>s::real. exp (- (1 / 2 * s))) \<longlongrightarrow> 0) at_top"
      using filterlim_compose[OF h2 h1] by (simp add: o_def)
    have l: "((\<lambda>s. - 80 * sqrt e * exp (- s / 2)) \<longlongrightarrow> 0) at_top"
      using tendsto_mult_right_zero[OF h3, of "- 80 * sqrt e"] by simp
    have ftc: "(\<integral>\<^sup>+ s. ennreal (40 * (sqrt e * exp (- s / 2))) *
      indicator {0..} s \<partial>lborel) = ennreal (80 * sqrt e)"
      using nn_integral_FTC_atLeast[where f = "\<lambda>s. 40 * (sqrt e * exp (- s / 2))" and F =
        "\<lambda>s. - 80 * sqrt e * exp (- s / 2)" and a = 0 and T = 0, OF m d n l] by simp
    show ?thesis unfolding sq using ftc .
  qed
  have mono: "(\<integral>\<^sup>+ s. emeasure rho {u. \<bar>x - u\<bar> <
    e * exp (- s)} * indicator {0..} s \<partial>lborel) \<le>
    (\<integral>\<^sup>+ s. ennreal (40 * sqrt (e * exp (- s))) *
    indicator {0..} s \<partial>lborel)"
    using ball by (force intro: nn_integral_mono mult_right_mono)
  show ?thesis
    unfolding swap using mono tail by simp
qed

text \<open>Helpers for (6.9): the normalised arclength density on @{text "[0, 2\<pi>]"} and the
  circle measures.\<close>

abbreviation cden :: "real measure" where
  "cden \<equiv> density lborel (\<lambda>\<theta>. ennreal (indicator {0..2 * pi} \<theta> / (2 *
    pi)))"

lemma cden_univ: "emeasure cden UNIV = 1"
proof -
  have "emeasure cden UNIV = (\<integral>\<^sup>+ \<theta>. ennreal (indicator {0..2 *
    pi} \<theta> / (2 * pi)) \<partial>lborel)"
    by (simp add: emeasure_density)
  also have "\<dots> = (\<integral>\<^sup>+ \<theta>. ennreal (1 / (2 * pi)) * indicator {0..2 *
    pi} \<theta> \<partial>lborel)"
    by (auto simp: indicator_def intro: nn_integral_cong)
  also have "\<dots> = ennreal (1 / (2 * pi)) * ennreal (2 * pi)"
    by (simp add: nn_integral_cmult_indicator)
  also have "\<dots> = 1"
    by (simp add: ennreal_mult["symmetric"])
  finally show ?thesis .
qed

lemma cden_finite: "finite_measure cden"
  using cden_univ by (auto intro: finite_measureI)

lemma circ_meas: "(\<lambda>\<theta> :: real. c + of_real \<epsilon> * cis \<theta>) \<in>
  borel_measurable borel"
  by (fast intro: borel_measurable_continuous_onI continuous_intros)

lemma circ_meas': "(\<lambda>\<theta> :: real. c + of_real \<epsilon> * cis \<theta>) \<in>
  measurable cden borel"
  using circ_meas[of c \<epsilon>] by simp

lemma sets_circ: "sets (circ c \<epsilon>) = sets borel"
  unfolding circ_def by simp

lemma space_circ: "space (circ c \<epsilon>) = UNIV"
  unfolding circ_def by simp

lemma circ_univ: "emeasure (circ c \<epsilon>) UNIV = 1"
  unfolding circ_def using emeasure_distr[OF circ_meas'[of c \<epsilon>], of UNIV] cden_univ by simp

lemma circ_finite: "finite_measure (circ c \<epsilon>)"
  using circ_univ[of c \<epsilon>] space_circ[of c \<epsilon>] by (auto intro: finite_measureI)

lemma circ_AE: "AE z in circ c \<epsilon>. norm (z - c) = \<bar>\<epsilon>\<bar>"
proof -
  have P: "{z \<in> space borel. norm (z - c) = \<bar>\<epsilon>\<bar>} \<in>
    sets (borel :: complex measure)"
    by measurable
  have pt: "AE \<theta> in cden. norm (c + of_real \<epsilon> * cis \<theta> - c) =
    \<bar>\<epsilon>\<bar>"
    by (simp add: norm_mult)
  show ?thesis unfolding circ_def using AE_distr_iff[OF circ_meas'[of c \<epsilon>] P] pt by simp
qed

lemma circ_integrable_bound:
  fixes f :: "complex \<Rightarrow> real" and B :: real
  assumes m: "f \<in> borel_measurable borel" and b: "\<And>z. norm (z - c) =
    \<bar>\<epsilon>\<bar> \<Longrightarrow> \<bar>f z\<bar> \<le> B"
  shows "integrable (circ c \<epsilon>) f"
proof -
  have m': "f \<in> borel_measurable (circ c \<epsilon>)"
    using m measurable_cong_sets[OF sets_circ[of c \<epsilon>] refl]
    by auto
  have ae: "AE z in circ c \<epsilon>. norm (f z) \<le> B" using circ_AE[of c \<epsilon>] b
    by (auto elim: eventually_mono)
  show ?thesis using finite_measure.integrable_const_bound[OF circ_finite ae m'] .
qed

lemma cis_eq_null: "{\<theta> :: real. cis \<theta> = w} \<in> null_sets lborel"
proof -
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
  show ?thesis using countable_imp_null_set_lborel countable_subset[OF bad]
    by fast
qed

lemma circ_log_integrable:
  assumes e: "0 < \<epsilon>"
  shows "integrable (circ c \<epsilon>) (\<lambda>z. ln (norm (z - a)))"
proof -
  define w where "w = (a - c) / of_real \<epsilon>"
  have mF: "(\<lambda>z :: complex. ln (norm (z - a))) \<in> borel_measurable borel"
    by simp
  have mh: "(\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a))) \<in>
    borel_measurable borel"
    using measurable_compose[OF circ_meas[of c \<epsilon>] mF] by (simp add: o_def)
  have n2: "(\<lambda>\<theta>. norm (cis \<theta> - w)) \<in> borel_measurable borel"
    by (fast intro: borel_measurable_continuous_onI continuous_intros)
  have mk: "(\<lambda>\<theta>. ln \<epsilon> + ln (norm (cis \<theta> - w))) \<in>
    borel_measurable borel" using borel_measurable_ln[OF n2]
    by (auto intro: borel_measurable_add)
  have pw: "ln (norm (c + of_real \<epsilon> * cis \<theta> - a)) =
    ln \<epsilon> + ln (norm (cis \<theta> - w))" if nw: "cis \<theta> \<noteq> w" for \<theta>
  proof -
    have eq: "c + of_real \<epsilon> * cis \<theta> - a = of_real \<epsilon> * (cis \<theta> - w)"
      using e unfolding w_def
      by (simp add: field_simps)
    show ?thesis unfolding eq norm_mult using e nw ln_mult[of \<epsilon> "norm (cis \<theta> - w)"]
      by simp
  qed
  have ae: "AE \<theta> \<in> einterval (min (ereal 0) (ereal (2 * pi))) (max (ereal 0) (ereal (2 *
    pi))) in lborel. ln (norm (c + of_real \<epsilon> * cis \<theta> - a)) =
    ln \<epsilon> + ln (norm (cis \<theta> - w))"
    using AE_I'[OF cis_eq_null[of w], of "\<lambda>\<theta>. \<theta> \<in>
      einterval (min (ereal 0) (ereal (2 * pi))) (max (ereal 0) (ereal (2 * pi))) \<longrightarrow>
      ln (norm (c + of_real \<epsilon> * cis \<theta> - a)) =
      ln \<epsilon> + ln (norm (cis \<theta> - w))"] pw
    by blast
  have ii0: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln \<epsilon> + ln (norm (cis \<theta> - w)))"
    using interval_lebesgue_integral_add(1)[OF interval_integral_const(1) circle_log_integrable[of
      w]] .
  have "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 *
    pi)) (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a)))"
    using interval_lebesgue_integrable_cong_AE[of "\<lambda>\<theta>. ln (norm (c +
      of_real \<epsilon> * cis \<theta> - a))" "\<lambda>\<theta>. ln \<epsilon> +
      ln (norm (cis \<theta> - w))" "ereal 0" "ereal (2 * pi)"] mh mk ae ii0 by simp
  hence "set_integrable lborel {0<..<2 * pi} (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> *
    cis \<theta> - a)))"
    unfolding interval_lebesgue_integrable_def by simp
  hence "set_integrable lborel {0..2 * pi} (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> *
    cis \<theta> - a)))"
    using set_integrable_discrete_difference[where X = "{0, 2 * pi}" and M = lborel and A =
      "{0..2 * pi}" and B = "{0<..<2 * pi}" and f =
      "\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> - a))"]
    by force
  hence i1a: "integrable lborel (\<lambda>\<theta>. (1 / (2 * pi)) * (indicator {0..2 *
    pi} \<theta> *\<^sub>R ln (norm (c + of_real \<epsilon> * cis \<theta> - a))))"
    unfolding set_integrable_def by simp
  have eqf: "(\<lambda>\<theta>. (indicator {0..2 * pi} \<theta> / (2 * pi)) *\<^sub>R ln (norm (c +
    of_real \<epsilon> * cis \<theta> - a))) =
    (\<lambda>\<theta>. (1 / (2 * pi)) * (indicator {0..2 * pi} \<theta> *\<^sub>R ln (norm (c +
    of_real \<epsilon> * cis \<theta> - a))))"
    by (simp add: fun_eq_iff)
  have i1: "integrable lborel (\<lambda>\<theta>. (indicator {0..2 * pi} \<theta> / (2 *
    pi)) *\<^sub>R ln (norm (c + of_real \<epsilon> * cis \<theta> - a)))"
    unfolding eqf by (rule i1a)
  have mg: "(\<lambda>\<theta> :: real. indicator {0..2 * pi} \<theta> / (2 * pi)) \<in>
    borel_measurable lborel"
    by simp
  have i2: "integrable cden (\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> * cis \<theta> -
    a)))"
    using integrable_density[of "\<lambda>\<theta>. ln (norm (c + of_real \<epsilon> *
      cis \<theta> - a))" lborel "\<lambda>\<theta>. indicator {0..2 * pi} \<theta> / (2 *
      pi)"] mh mg i1
    by simp
  show ?thesis unfolding circ_def using integrable_distr_eq[OF circ_meas'[of c \<epsilon>] mF] i2
    by simp
qed

lemma circ_singleton:
  assumes e: "0 < \<epsilon>"
  shows "emeasure (circ c \<epsilon>) {a} = 0"
proof -
  define w where "w = (a - c) / of_real \<epsilon>"
  have pre: "(\<lambda>\<theta>. c + of_real \<epsilon> * cis \<theta>) -` {a} \<inter> space cden =
    {\<theta>. cis \<theta> = w}"
    unfolding w_def using e by (auto simp: field_simps)
  have "{\<theta> :: real. cis \<theta> = w} \<in> sets lborel" using cis_eq_null[of w]
    by (simp add: null_sets_def)
  hence d1: "emeasure cden {\<theta>. cis \<theta> = w} =
    (\<integral>\<^sup>+ \<theta>. ennreal (indicator {0..2 * pi} \<theta> / (2 * pi)) *
    indicator {\<theta>. cis \<theta> = w} \<theta> \<partial>lborel)"
    by (simp add: emeasure_density)
  have d2: "(\<integral>\<^sup>+ \<theta>. ennreal (indicator {0..2 * pi} \<theta> / (2 * pi)) *
    indicator {\<theta>. cis \<theta> = w} \<theta> \<partial>lborel) = 0"
    by (rule nn_integral_null_set[OF cis_eq_null[of w]])
  have d: "emeasure cden {\<theta>. cis \<theta> = w} = 0"
    using d1 d2 by simp
  show ?thesis unfolding circ_def using emeasure_distr[OF circ_meas'[of c \<epsilon>],
    of "{a}"] pre d
    by simp
qed

lemma circ_neg_log:
  fixes c z :: complex and \<epsilon> R :: real
  assumes e: "0 < \<epsilon>" and hc: "norm c + \<epsilon> \<le> R" and hz: "norm z \<le> R"
  shows "(\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>circ c \<epsilon>) \<le>
    ennreal (2 * R - ln \<epsilon>)"
proof -
  define g where "g w = ln (norm (w - z))" for w :: complex
  have ig: "integrable (circ c \<epsilon>) g" unfolding g_def
    using circ_log_integrable[OF e, of c z] .
  have ipos: "integrable (circ c \<epsilon>) (\<lambda>w. max 0 (g w))" using ig
    using integrable_max by simp
  have ineg: "integrable (circ c \<epsilon>) (\<lambda>w. max 0 (- g w))" using ig
    using integrable_max by simp
  have e1: "(\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>circ c \<epsilon>) =
    (\<integral>\<^sup>+ w. ennreal (max 0 (- g w)) \<partial>circ c \<epsilon>)"
    unfolding g_def by (simp add: norm_minus_commute ennreal_max_0)
  have e2: "(\<integral>\<^sup>+ w. ennreal (max 0 (- g w)) \<partial>circ c \<epsilon>) =
    ennreal (integral\<^sup>L (circ c \<epsilon>) (\<lambda>w. max 0 (- g w)))"
    using nn_integral_eq_integral[OF ineg] by simp
  have e3: "integral\<^sup>L (circ c \<epsilon>) (\<lambda>w. max 0 (- g w)) =
    integral\<^sup>L (circ c \<epsilon>) (\<lambda>w. max 0 (g w)) -
    integral\<^sup>L (circ c \<epsilon>) g"
  proof -
    have pt: "(\<lambda>w. max 0 (- g w)) = (\<lambda>w. max 0 (g w) - g w)"
      by (simp add: fun_eq_iff max_def)
    show ?thesis unfolding pt using Bochner_Integration.integral_diff[OF ipos ig] .
  qed
  have h1: "ln \<epsilon> \<le> integral\<^sup>L (circ c \<epsilon>) g" unfolding g_def
    using circ_log[OF e, of c z] e
    by simp
  have R0: "0 \<le> R" using hc e norm_ge_zero[of c]
    by linarith
  have hb: "AE w in circ c \<epsilon>. max 0 (g w) \<le> 2 * R"
  proof -
    have pt: "max 0 (g w) \<le> 2 * R" if hw: "norm (w - c) = \<bar>\<epsilon>\<bar>" for w
    proof -
      have "norm w \<le> R" using hw hc e norm_triangle_ineq[of "w - c" c]
        by simp
      hence w2: "norm (w - z) \<le> 2 * R" using hz norm_triangle_ineq4[of w z]
        by simp
      have w3: "g w \<le> norm (w - z)" unfolding g_def
        by (metis less_eq_real_def ln_0 ln_less_self norm_ge_zero)
      show ?thesis using w2 w3 R0
        by simp
    qed
    show ?thesis using circ_AE[of c \<epsilon>] pt
      by (auto elim: eventually_mono)
  qed
  have h2: "integral\<^sup>L (circ c \<epsilon>) (\<lambda>w. max 0 (g w)) \<le> 2 * R"
  proof -
    have "integral\<^sup>L (circ c \<epsilon>) (\<lambda>w. max 0 (g w)) \<le>
      integral\<^sup>L (circ c \<epsilon>) (\<lambda>w. 2 * R)"
      using integral_mono_AE[OF ipos _ hb] finite_measure.integrable_const[OF circ_finite]
      by auto
    also have "\<dots> = 2 * R" using circ_univ[of c \<epsilon>] space_circ[of c \<epsilon>]
      by (simp add: measure_def)
    finally show ?thesis .
  qed
  show ?thesis unfolding e1 e2 e3 using h1 h2
    using ennreal_leI by simp
qed

text \<open>Finite sums of circle measures,
  realised as a push-forward of @{text "count_space I \<Otimes> cden"}.\<close>

lemma csum_meas:
  fixes c :: "nat \<Rightarrow> complex" and I :: "nat set"
  assumes I: "countable I"
  shows "(\<lambda>(i, \<theta>). c i + of_real \<epsilon> * cis \<theta>) \<in>
    measurable (count_space I \<Otimes>\<^sub>M cden) borel"
  using measurable_pair_measure_countable1[OF I, of "\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>" cden borel] circ_meas'
  by simp

lemma csum_nn:
  fixes c :: "nat \<Rightarrow> complex" and I :: "nat set" and f :: "complex \<Rightarrow> ennreal"
  assumes I: "finite I" and f: "f \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+ z. f z \<partial>distr (count_space I \<Otimes>\<^sub>M cden) borel
    (\<lambda>(i, \<theta>). c i + of_real \<epsilon> * cis \<theta>))
       = (\<Sum> i \<in> I. \<integral>\<^sup>+ z. f z \<partial>circ (c i) \<epsilon>)"
proof -
  have m: "(\<lambda>(i, \<theta>). c i + of_real \<epsilon> * cis \<theta>) \<in>
    measurable (count_space I \<Otimes>\<^sub>M cden) borel"
    using csum_meas[OF countable_finite[OF I]] .
  have sf: "sigma_finite_measure cden" using cden_finite
    by (simp add: finite_measure_def)
  have mfp: "(\<lambda>p. f ((\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>) p)) \<in>
    borel_measurable (count_space I \<Otimes>\<^sub>M cden)"
    using measurable_compose[OF m f] by (simp add: o_def)
  have e1: "(\<integral>\<^sup>+ z. f z \<partial>distr (count_space I \<Otimes>\<^sub>M cden) borel
    (\<lambda>(i, \<theta>). c i + of_real \<epsilon> * cis \<theta>))
      = (\<integral>\<^sup>+ p. f ((\<lambda>(i,
        \<theta>). c i + of_real \<epsilon> *
        cis \<theta>) p) \<partial>(count_space I \<Otimes>\<^sub>M cden))"
    using nn_integral_distr[OF m] f by simp
  have e2: "(\<integral>\<^sup>+ p. f ((\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> *
    cis \<theta>) p) \<partial>(count_space I \<Otimes>\<^sub>M cden))
      = (\<integral>\<^sup>+ i. (\<integral>\<^sup>+ \<theta>. f (c i + of_real \<epsilon> *
        cis \<theta>) \<partial>cden) \<partial>count_space I)"
    using sigma_finite_measure.nn_integral_fst[OF sf mfp] by simp
  have e4: "\<And>i. (\<integral>\<^sup>+ \<theta>. f (c i + of_real \<epsilon> *
    cis \<theta>) \<partial>cden) = (\<integral>\<^sup>+ z. f z \<partial>circ (c i) \<epsilon>)"
    unfolding circ_def using nn_integral_distr[OF circ_meas'] f by simp
  have e3: "(\<integral>\<^sup>+ i. (\<integral>\<^sup>+ \<theta>. f (c i + of_real \<epsilon> *
    cis \<theta>) \<partial>cden) \<partial>count_space I)
      = (\<Sum> i \<in> I. \<integral>\<^sup>+ z. f z \<partial>circ (c i) \<epsilon>)"
    unfolding e4 by (rule nn_integral_count_space_finite[OF I])
  show ?thesis unfolding e1 e2 e3 ..
qed

lemma csum_emeasure:
  fixes c :: "nat \<Rightarrow> complex" and I :: "nat set"
  assumes I: "finite I" and A: "A \<in> sets borel"
  shows "emeasure (distr (count_space I \<Otimes>\<^sub>M cden) borel (\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>)) A = (\<Sum> i \<in>
    I. emeasure (circ (c i) \<epsilon>) A)"
  using csum_nn[OF I, where f = "indicator A" and c = c and \<epsilon> = \<epsilon>] A sets_circ
  by simp

lemma csum_integral:
  fixes c :: "nat \<Rightarrow> complex" and I :: "nat set" and f :: "complex \<Rightarrow> real"
  assumes I: "finite I" and f: "f \<in> borel_measurable borel" and fi: "\<And>i. i \<in>
    I \<Longrightarrow> integrable (circ (c i) \<epsilon>) f"
  shows "integrable (distr (count_space I \<Otimes>\<^sub>M cden) borel (\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>)) f"
    and "integral\<^sup>L (distr (count_space I \<Otimes>\<^sub>M cden) borel (\<lambda>(i,
      \<theta>). c i + of_real \<epsilon> * cis \<theta>)) f = (\<Sum> i \<in>
      I. integral\<^sup>L (circ (c i) \<epsilon>) f)"
proof -
  have m: "(\<lambda>(i, \<theta>). c i + of_real \<epsilon> * cis \<theta>) \<in>
    measurable (count_space I \<Otimes>\<^sub>M cden) borel"
    using csum_meas[OF countable_finite[OF I]] .
  have mn: "(\<lambda>z. ennreal (norm (f z))) \<in> borel_measurable borel" using f
    by simp
  have fin: "\<And>i. i \<in> I \<Longrightarrow>
    (\<integral>\<^sup>+ z. ennreal (norm (f z)) \<partial>circ (c i) \<epsilon>) < \<infinity>"
    using fi
    by (simp add: integrable_iff_bounded)
  have nnD: "(\<integral>\<^sup>+ z. ennreal (norm (f z)) \<partial>distr (count_space I
    \<Otimes>\<^sub>M cden) borel (\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>)) < \<infinity>"
    unfolding csum_nn[OF I mn] using fin I ennreal_sum_less_top[OF I] by simp
  have "f \<in> borel_measurable (distr (count_space I \<Otimes>\<^sub>M cden) borel (\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>))"
    using f by simp
  thus "integrable (distr (count_space I \<Otimes>\<^sub>M cden) borel (\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>)) f"
    using nnD by (simp add: integrable_iff_bounded)
  hence iP: "integrable (count_space I \<Otimes>\<^sub>M cden) (\<lambda>p. f ((\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>) p))"
    using integrable_distr_eq[OF m f] by simp
  have ps: "pair_sigma_finite (count_space I) cden"
    using sigma_finite_measure_count_space_finite[OF I] cden_finite
    unfolding pair_sigma_finite_def by (simp add: finite_measure_def)
  have e1: "integral\<^sup>L (distr (count_space I \<Otimes>\<^sub>M cden) borel (\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>)) f
      = integral\<^sup>L (count_space I \<Otimes>\<^sub>M cden) (\<lambda>p. f ((\<lambda>(i,
        \<theta>). c i + of_real \<epsilon> * cis \<theta>) p))"
    by (rule integral_distr[OF m f])
  have e2: "integral\<^sup>L (count_space I \<Otimes>\<^sub>M cden) (\<lambda>p. f ((\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>) p))
      = (\<integral> i. (\<integral> \<theta>. f (c i + of_real \<epsilon> *
        cis \<theta>) \<partial>cden) \<partial>count_space I)"
    using pair_sigma_finite.integral_fst'[OF ps iP] by simp
  have e4: "\<And>i. (\<integral> \<theta>. f (c i + of_real \<epsilon> *
    cis \<theta>) \<partial>cden) = integral\<^sup>L (circ (c i) \<epsilon>) f"
    unfolding circ_def using integral_distr[OF circ_meas' f] by simp
  have e3: "(\<integral> i. (\<integral> \<theta>. f (c i + of_real \<epsilon> *
    cis \<theta>) \<partial>cden) \<partial>count_space I)
      = (\<Sum> i \<in> I. integral\<^sup>L (circ (c i) \<epsilon>) f)"
    unfolding e4 by (rule lebesgue_integral_count_space_finite[OF I])
  show "integral\<^sup>L (distr (count_space I \<Otimes>\<^sub>M cden) borel (\<lambda>(i,
    \<theta>). c i + of_real \<epsilon> * cis \<theta>)) f = (\<Sum> i \<in>
    I. integral\<^sup>L (circ (c i) \<epsilon>) f)"
    unfolding e1 e2 e3 ..
qed

text \<open>A scaled measure is a density with a constant; the Bochner integral scales.\<close>
lemma scale_density:
  fixes M :: "'a measure" and r :: real
  shows "scale_measure (ennreal r) M = density M (\<lambda>_. ennreal r)"
proof (rule measure_eqI)
  show "sets (scale_measure (ennreal r) M) = sets (density M (\<lambda>_. ennreal r))"
    by simp
  fix A assume A: "A \<in> sets (scale_measure (ennreal r) M)"
  show "emeasure (scale_measure (ennreal r) M) A = emeasure (density M (\<lambda>_. ennreal r)) A"
    using A by (simp add: emeasure_density nn_integral_cmult_indicator)
qed

lemma scale_integral:
  fixes M :: "'a measure" and f :: "'a \<Rightarrow> real" and r :: real
  assumes r: "0 \<le> r" and f: "f \<in> borel_measurable M"
  shows "integral\<^sup>L (scale_measure (ennreal r) M) f = r * integral\<^sup>L M f"
    and "integrable M f \<Longrightarrow> integrable (scale_measure (ennreal r) M) f"
proof -
  have g: "(\<lambda>_. r) \<in> borel_measurable M"
    by simp
  have nn: "AE x in M. 0 \<le> r" using r
    by simp
  show "integral\<^sup>L (scale_measure (ennreal r) M) f = r * integral\<^sup>L M f"
    unfolding scale_density
    using integral_density[OF f g nn] by simp
  show "integrable M f \<Longrightarrow> integrable (scale_measure (ennreal r) M) f"
    unfolding scale_density
    using integrable_density[OF f g nn] by simp
qed

text \<open>Facts about @{text \<rho>} and its image on @{text \<complex>}.\<close>
lemma rho_finite: "finite_measure rho"
  using rho_univ by (auto simp: rho_def intro: finite_measureI)

lemma rhoC_meas: "(of_real :: real \<Rightarrow> complex) \<in> measurable rho borel"
  unfolding rho_def by simp

lemma sets_rhoC: "sets (distr rho borel (of_real :: real \<Rightarrow> complex)) = sets borel"
  by simp

lemma rhoC_finite: "finite_measure (distr rho borel (of_real :: real \<Rightarrow> complex))"
  using finite_measure.finite_measure_distr[OF rho_finite rhoC_meas] .

lemma rhoC_singleton: "emeasure (distr rho borel (of_real :: real \<Rightarrow> complex)) {a} = 0"
proof -
  have sub: "(of_real :: real \<Rightarrow> complex) -` {a} \<inter> space rho \<subseteq> {Re a}"
    by auto
  have sm: "{Re a} \<in> sets rho" unfolding rho_def
    by simp
  have le: "emeasure rho ((of_real :: real \<Rightarrow> complex) -` {a} \<inter> space rho) \<le>
    emeasure rho {Re a}"
    by (rule emeasure_mono[OF sub sm])
  show ?thesis using emeasure_distr[OF rhoC_meas, of "{a}"] le rho_singleton[of "Re a"]
    by simp
qed

lemma rhoC_AE: "AE w in distr rho borel (of_real :: real \<Rightarrow> complex). norm w \<le> 2"
proof -
  have P: "{w \<in> space borel. norm w \<le> (2 :: real)} \<in> sets (borel :: complex measure)"
    by measurable
  have nul: "- {0<..<2 :: real} \<in> null_sets rho" using rho_compl unfolding rho_def
    by auto
  have ae: "AE u in rho. norm (of_real u :: complex) \<le> 2"
    using AE_I'[OF nul, of "\<lambda>u. norm (of_real u :: complex) \<le> 2"]
    by force
  show ?thesis using AE_distr_iff[OF rhoC_meas P] ae
    by simp
qed

lemma rhoC_neg_log: "(\<integral>\<^sup>+ w. ennreal (- ln (norm (z -
  w))) \<partial>distr rho borel (of_real :: real \<Rightarrow> complex)) \<le> ennreal 80"
proof -
  have mf: "(\<lambda>w :: complex. ennreal (- ln (norm (z - w)))) \<in> borel_measurable borel"
    by simp
  have e1: "(\<integral>\<^sup>+ w. ennreal (- ln (norm (z -
    w))) \<partial>distr rho borel (of_real :: real \<Rightarrow> complex)) =
    (\<integral>\<^sup>+ u. ennreal (- ln (norm (z - of_real u))) \<partial>rho)"
    using nn_integral_distr[OF rhoC_meas] mf by simp
  have nul: "{Re z} \<in> null_sets rho" using rho_singleton[of "Re z"] unfolding rho_def
    by auto
  have ae: "AE u in rho. u \<noteq> Re z"
    using AE_I'[OF nul, of "\<lambda>u. u \<noteq> Re z"] by auto
  have pt: "ennreal (- ln (norm (z - of_real u))) \<le>
    ennreal (max 0 (ln (1 / \<bar>Re z - u\<bar>)))" if u: "u \<noteq> Re z" for u
  proof -
    have d0: "0 < \<bar>Re z - u\<bar>" using u
      by simp
    have dle: "\<bar>Re z - u\<bar> \<le> norm (z - of_real u)"
      using abs_Re_le_cmod[of "z - of_real u"]
      by simp
    have l1: "- ln (norm (z - of_real u)) \<le> - ln \<bar>Re z - u\<bar>"
      using d0 dle ln_le_cancel_iff[of "\<bar>Re z - u\<bar>" "norm (z - of_real u)"]
      by linarith
    have l2: "- ln \<bar>Re z - u\<bar> = ln (1 / \<bar>Re z - u\<bar>)" using d0
      by (simp add: ln_div)
    show ?thesis using l1 l2
      using ennreal_leI by simp
  qed
  have e2: "(\<integral>\<^sup>+ u. ennreal (- ln (norm (z - of_real u))) \<partial>rho) \<le>
    (\<integral>\<^sup>+ u. ennreal (max 0 (ln (1 / \<bar>Re z - u\<bar>))) \<partial>rho)"
    using ae pt by (auto intro: nn_integral_mono_AE elim: eventually_mono)
  have e3: "(\<integral>\<^sup>+ u. ennreal (max 0 (ln (1 / \<bar>Re z -
    u\<bar>))) \<partial>rho) \<le> ennreal 80"
    using cross_bound[of 1 "Re z"] by simp
  show ?thesis unfolding e1 using e2 e3 by (rule order_trans)
qed

text \<open>Integrability of @{text "log|z - w|"} against a product of finite measures carried
  by a ball.\<close>
lemma ennreal_abs_ln_le:
  fixes y :: real
  assumes y: "0 \<le> y"
  shows "ennreal \<bar>ln y\<bar> \<le> ennreal y + ennreal (- ln y)"
proof -
  have "ln y \<le> y" using y
    by (metis assms ln_0 ln_bound less_eq_real_def)
  hence "\<bar>ln y\<bar> \<le> y + max 0 (- ln y)" using y
    by simp
  hence "ennreal \<bar>ln y\<bar> \<le> ennreal (y + max 0 (- ln y))" by (rule ennreal_leI)
  also have "\<dots> = ennreal y + ennreal (- ln y)" using y
    by (simp add: ennreal_plus ennreal_max_0)
  finally show ?thesis .
qed

lemma integrable_log_prod:
  fixes \<mu> \<nu> :: "complex measure" and R C :: real
  assumes fm: "finite_measure \<mu>" and fn: "finite_measure \<nu>" and sm: "sets \<mu> =
    sets borel" and sn: "sets \<nu> = sets borel"
    and aem: "AE z in \<mu>. norm z \<le> R" and aen: "AE w in \<nu>. norm w \<le> R"
    and lg: "\<And>z. norm z \<le> R \<Longrightarrow>
      (\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<nu>) \<le> ennreal C"
  shows "integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (\<lambda>p. ln (norm (fst p - snd p)))"
proof -
  have sp: "sets (\<mu> \<Otimes>\<^sub>M \<nu>) = sets (borel \<Otimes>\<^sub>M borel)" using sm sn
    using sets_pair_measure_cong by simp
  have "(\<lambda>p :: complex \<times> complex. ln (norm (fst p - snd p))) \<in>
    borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by simp
  hence m: "(\<lambda>p. ln (norm (fst p - snd p))) \<in>
    borel_measurable (\<mu> \<Otimes>\<^sub>M \<nu>)" using measurable_cong_sets[OF sp refl]
    by blast
  have sfn: "sigma_finite_measure \<nu>" using fn
    by (simp add: finite_measure_def)
  have ma: "(\<lambda>p. ennreal (norm (ln (norm (fst p - snd p))))) \<in>
    borel_measurable (\<mu> \<Otimes>\<^sub>M \<nu>)" using m
    by simp
  have fub: "(\<integral>\<^sup>+ p. ennreal (norm (ln (norm (fst p -
    snd p)))) \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>)) =
    (\<integral>\<^sup>+ z. (\<integral>\<^sup>+ w. ennreal (norm (ln (norm (z -
    w)))) \<partial>\<nu>) \<partial>\<mu>)"
    using sigma_finite_measure.nn_integral_fst[OF sfn ma] by simp
  define B where "B = ennreal (2 * R) * emeasure \<nu> (space \<nu>) + ennreal C"
  have inner: "\<And>z. norm z \<le> R \<Longrightarrow>
    (\<integral>\<^sup>+ w. ennreal (norm (ln (norm (z - w)))) \<partial>\<nu>) \<le> B"
  proof -
    fix z :: complex assume hz: "norm z \<le> R"
    have mw1: "(\<lambda>w. ennreal (norm (z - w))) \<in> borel_measurable \<nu>"
      unfolding measurable_cong_sets[OF sn refl]
      by simp
    have mw2: "(\<lambda>w. ennreal (- ln (norm (z - w)))) \<in> borel_measurable \<nu>"
      unfolding measurable_cong_sets[OF sn refl]
      by simp
    have s1: "(\<integral>\<^sup>+ w. ennreal (norm (ln (norm (z - w)))) \<partial>\<nu>) \<le>
      (\<integral>\<^sup>+ w. ennreal (norm (z - w)) + ennreal (- ln (norm (z -
      w))) \<partial>\<nu>)"
      using ennreal_abs_ln_le by (auto intro: nn_integral_mono)
    have s2: "(\<integral>\<^sup>+ w. ennreal (norm (z - w)) + ennreal (- ln (norm (z -
      w))) \<partial>\<nu>) = (\<integral>\<^sup>+ w. ennreal (norm (z - w)) \<partial>\<nu>) +
      (\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<nu>)"
      by (rule nn_integral_add[OF mw1 mw2])
    have a: "AE w in \<nu>. ennreal (norm (z - w)) \<le> ennreal (2 * R)"
    proof -
      have pt: "ennreal (norm (z - w)) \<le> ennreal (2 * R)" if w: "norm w \<le> R" for w
        using w hz norm_triangle_ineq4[of z w] using ennreal_leI by simp
      show ?thesis using aen pt
        by (auto elim: eventually_mono)
    qed
    have s3: "(\<integral>\<^sup>+ w. ennreal (norm (z - w)) \<partial>\<nu>) \<le>
      ennreal (2 * R) * emeasure \<nu> (space \<nu>)"
      using nn_integral_mono_AE[OF a] by simp
    show "(\<integral>\<^sup>+ w. ennreal (norm (ln (norm (z - w)))) \<partial>\<nu>) \<le> B"
      unfolding B_def using s1 s2 s3 lg[OF hz]
      by (auto intro: add_mono order_trans)
  qed
  have outer: "(\<integral>\<^sup>+ z. (\<integral>\<^sup>+ w. ennreal (norm (ln (norm (z -
    w)))) \<partial>\<nu>) \<partial>\<mu>) \<le> (\<integral>\<^sup>+ z. B \<partial>\<mu>)"
    using aem inner by (fast intro: nn_integral_mono_AE elim: eventually_mono)
  have "B < \<infinity>" unfolding B_def
    using finite_measure.emeasure_finite[OF fn, of "space \<nu>"]
    by (simp add: ennreal_mult_less_top less_top)
  hence fin: "(\<integral>\<^sup>+ z. B \<partial>\<mu>) < \<infinity>"
    using finite_measure.emeasure_finite[OF fm, of "space \<mu>"]
    by (simp add: ennreal_mult_less_top less_top)
  show ?thesis unfolding integrable_iff_bounded using m fub outer fin
    by simp
qed

text \<open>The sum of two measures with the Borel sets, as @{const measure_of}.\<close>
lemma summ_sets:
  fixes \<mu> \<nu> :: "'a::topological_space measure"
  shows "sets (measure_of UNIV (sets borel) (\<lambda>A. emeasure \<mu> A + emeasure \<nu> A)) =
    sets (borel :: 'a measure)"
  using sets.sigma_sets_eq[of borel] sets_measure_of[of "sets borel" UNIV] by simp

lemma summ_emeasure:
  fixes \<mu> \<nu> :: "'a::topological_space measure"
  assumes s1: "sets \<mu> = sets borel" and s2: "sets \<nu> = sets borel" and A: "A \<in>
    sets borel"
  shows "emeasure (measure_of UNIV (sets borel) (\<lambda>A. emeasure \<mu> A +
    emeasure \<nu> A)) A = emeasure \<mu> A + emeasure \<nu> A"
proof (rule emeasure_measure_of_sigma)
  show "sigma_algebra UNIV (sets borel)" using sets.sigma_algebra_axioms[of borel]
    by simp
  show "positive (sets borel) (\<lambda>A. emeasure \<mu> A + emeasure \<nu> A)"
    unfolding positive_def
    by simp
  show "countably_additive (sets borel) (\<lambda>A. emeasure \<mu> A + emeasure \<nu> A)"
    unfolding countably_additive_def
  proof (intro allI impI)
    fix F :: "nat \<Rightarrow> 'a set"
    assume F1: "range F \<subseteq> sets borel" and F2: "disjoint_family F" and F3: "\<Union> (range
      F) \<in> sets borel"
    have a1: "(\<Sum> i. emeasure \<mu> (F i)) = emeasure \<mu> (\<Union> (range F))"
      using suminf_emeasure[of F \<mu>] F1 F2 s1
      by simp
    have a2: "(\<Sum> i. emeasure \<nu> (F i)) = emeasure \<nu> (\<Union> (range F))"
      using suminf_emeasure[of F \<nu>] F1 F2 s2
      by simp
    show "(\<Sum> i. emeasure \<mu> (F i) + emeasure \<nu> (F i)) =
      emeasure \<mu> (\<Union> (range F)) + emeasure \<nu> (\<Union> (range F))"
      unfolding a1[symmetric] a2[symmetric]
        using suminf_add[of "\<lambda>i. emeasure \<mu> (F i)" "\<lambda>i. emeasure \<nu> (F i)"]
      using summableI by simp
  qed
  show "A \<in> sets borel" by (rule A)
qed

lemma summ_nn:
  fixes \<mu> \<nu> :: "'a::topological_space measure" and f :: "'a \<Rightarrow> ennreal"
  assumes s1: "sets \<mu> = sets borel" and s2: "sets \<nu> = sets borel" and f: "f \<in>
    borel_measurable borel"
  shows "(\<integral>\<^sup>+ z. f z \<partial>measure_of UNIV (sets borel) (\<lambda>A. emeasure
    \<mu> A + emeasure \<nu> A)) = (\<integral>\<^sup>+ z. f z \<partial>\<mu>) +
    (\<integral>\<^sup>+ z. f z \<partial>\<nu>)"
proof -
  define \<eta> where "\<eta> = measure_of UNIV (sets borel) (\<lambda>A. emeasure \<mu> A +
    emeasure \<nu> A)"
  have s\<eta>: "sets \<eta> = sets borel" unfolding \<eta>_def by (rule summ_sets)
  have mc: "\<And>g :: 'a \<Rightarrow> ennreal. g \<in> borel_measurable borel \<Longrightarrow>
    g \<in> borel_measurable \<eta> \<and> g \<in> borel_measurable \<mu> \<and>
    g \<in> borel_measurable \<nu>"
    using s\<eta> s1 s2 measurable_cong_sets by simp
  have "(\<integral>\<^sup>+ z. f z \<partial>\<eta>) =
    (\<integral>\<^sup>+ z. f z \<partial>\<mu>) + (\<integral>\<^sup>+ z. f z \<partial>\<nu>)"
    using f
  proof induction
    case (cong f g)
    show ?case using cong
      by (simp add: fun_eq_iff)
  next
    case (set A)
    show ?case using set summ_emeasure[OF s1 s2 set] s\<eta> s1 s2 unfolding \<eta>_def
      by simp
  next
    case (mult u c)
    show ?case using mult mc[OF mult(2)]
      by (simp add: nn_integral_cmult distrib_left)
  next
    case (add u v)
    show ?case using add mc
      by (simp add: nn_integral_add)
  next
    case (seq U)
    have m: "\<And>i. U i \<in> borel_measurable \<eta> \<and>
      U i \<in> borel_measurable \<mu> \<and> U i \<in> borel_measurable \<nu>" using seq mc
      by simp
    have m\<eta>: "\<And>i. U i \<in> borel_measurable \<eta>" using m by blast
    have m\<mu>: "\<And>i. U i \<in> borel_measurable \<mu>" using m by blast
    have m\<nu>: "\<And>i. U i \<in> borel_measurable \<nu>" using m by blast
    have c1: "(\<integral>\<^sup>+ z. (SUP i. U i) z \<partial>\<eta>) =
      (SUP i. \<integral>\<^sup>+ z. U i z \<partial>\<eta>)" unfolding SUP_apply
      by (rule nn_integral_monotone_convergence_SUP[OF \<open>incseq U\<close> m\<eta>])
    have c2: "(\<integral>\<^sup>+ z. (SUP i. U i) z \<partial>\<mu>) =
      (SUP i. \<integral>\<^sup>+ z. U i z \<partial>\<mu>)" unfolding SUP_apply
      by (rule nn_integral_monotone_convergence_SUP[OF \<open>incseq U\<close> m\<mu>])
    have c3: "(\<integral>\<^sup>+ z. (SUP i. U i) z \<partial>\<nu>) =
      (SUP i. \<integral>\<^sup>+ z. U i z \<partial>\<nu>)" unfolding SUP_apply
      by (rule nn_integral_monotone_convergence_SUP[OF \<open>incseq U\<close> m\<nu>])
    have i2: "incseq (\<lambda>i. \<integral>\<^sup>+ z. U i z \<partial>\<mu>)"
      using \<open>incseq U\<close> unfolding incseq_def le_fun_def
      by (auto intro: nn_integral_mono)
    have i3: "incseq (\<lambda>i. \<integral>\<^sup>+ z. U i z \<partial>\<nu>)"
      using \<open>incseq U\<close> unfolding incseq_def le_fun_def
      by (auto intro: nn_integral_mono)
    show ?case unfolding c1 c2 c3 using seq ennreal_SUP_add[OF i2 i3]
      by simp
  qed
  thus ?thesis unfolding \<eta>_def .
qed

text \<open>Logarithmic integrals against @{text \<rho>}.\<close>
lemma abs_ln_max_le:
  fixes e x :: real
  assumes e: "0 < e" and x: "0 \<le> x"
  shows "\<bar>ln (max e x)\<bar> \<le> \<bar>ln e\<bar> + x"
proof (cases "x \<le> e")
  case True
  show ?thesis using True x
    by (simp add: max_def)
next
  case False
  have "ln x \<le> x" using x
    by (metis ln_0 ln_bound less_eq_real_def)
  moreover have "ln e \<le> ln x" using e False
    by simp
  ultimately show ?thesis using False
    using e by linarith
qed

lemma rho_AE_Ioo: "AE u in rho. 0 < u \<and> u < 2"
proof -
  have nul: "- {0<..<2 :: real} \<in> null_sets rho" using rho_compl unfolding rho_def
    by auto
  show ?thesis using AE_I'[OF nul, of "\<lambda>u. 0 < u \<and> u < 2"]
    by force
qed

lemma rho_neg_log_le: "(\<integral>\<^sup>+ u. ennreal (- ln \<bar>x - u\<bar>) \<partial>rho) \<le>
  ennreal 80"
proof -
  have pt: "\<And>u. ennreal (- ln \<bar>x - u\<bar>) =
    ennreal (max 0 (ln (1 / \<bar>x - u\<bar>)))"
    by (simp add: ln_div ennreal_max_0)
  show ?thesis unfolding pt using cross_bound[of 1 x]
    by simp
qed

lemma rho_log_integrable: "integrable rho (\<lambda>u. ln \<bar>x - u\<bar>)"
proof -
  have m: "(\<lambda>u. ln \<bar>x - u\<bar>) \<in> borel_measurable rho" unfolding rho_def
    by simp
  have m1: "(\<lambda>u. ennreal \<bar>x - u\<bar>) \<in> borel_measurable rho" unfolding rho_def
    by simp
  have m2: "(\<lambda>u. ennreal (- ln \<bar>x - u\<bar>)) \<in> borel_measurable rho"
    unfolding rho_def
    by simp
  have s1: "(\<integral>\<^sup>+ u. ennreal (norm (ln \<bar>x - u\<bar>)) \<partial>rho) \<le>
    (\<integral>\<^sup>+ u. ennreal \<bar>x - u\<bar> + ennreal (- ln \<bar>x -
    u\<bar>) \<partial>rho)"
    using ennreal_abs_ln_le by (auto intro: nn_integral_mono)
  have s2: "(\<integral>\<^sup>+ u. ennreal \<bar>x - u\<bar> + ennreal (- ln \<bar>x -
    u\<bar>) \<partial>rho) = (\<integral>\<^sup>+ u. ennreal \<bar>x - u\<bar> \<partial>rho) +
    (\<integral>\<^sup>+ u. ennreal (- ln \<bar>x - u\<bar>) \<partial>rho)"
    by (rule nn_integral_add[OF m1 m2])
  have a: "AE u in rho. ennreal \<bar>x - u\<bar> \<le> ennreal (\<bar>x\<bar> + 2)"
    using rho_AE_Ioo
    by (fastforce intro: ennreal_leI elim: eventually_mono)
  have s3: "(\<integral>\<^sup>+ u. ennreal \<bar>x - u\<bar> \<partial>rho) \<le>
    ennreal (\<bar>x\<bar> + 2) * emeasure rho (space rho)"
    using nn_integral_mono_AE[OF a] by simp
  have f1: "emeasure rho (space rho) < \<infinity>"
    using finite_measure.emeasure_finite[OF rho_finite, of "space rho"]
    by (simp add: less_top)
  have b1: "(\<integral>\<^sup>+ u. ennreal (norm (ln \<bar>x - u\<bar>)) \<partial>rho) \<le>
    ennreal (\<bar>x\<bar> + 2) * emeasure rho (space rho) + ennreal 80"
    using s1 s2 s3 rho_neg_log_le[of x] by (auto intro: add_mono order_trans)
  have b2: "ennreal (\<bar>x\<bar> + 2) * emeasure rho (space rho) + ennreal 80 < \<infinity>"
    using f1
    by (simp add: ennreal_mult_less_top less_top)
  have fin: "(\<integral>\<^sup>+ u. ennreal (norm (ln \<bar>x - u\<bar>)) \<partial>rho) <
    \<infinity>" by (rule le_less_trans[OF b1 b2])
  show ?thesis using m fin unfolding integrable_iff_bounded
    by simp
qed

lemma rho_logmax_integrable:
  assumes e: "0 < \<epsilon>"
  shows "integrable rho (\<lambda>u. ln (max \<epsilon> \<bar>x - u\<bar>))"
proof -
  have m: "(\<lambda>u. ln (max \<epsilon> \<bar>x - u\<bar>)) \<in> borel_measurable rho"
    unfolding rho_def
    by simp
  have pt: "norm (ln (max \<epsilon> \<bar>x - u\<bar>)) \<le>
    \<bar>ln \<epsilon>\<bar> + (\<bar>x\<bar> + 2)" if u: "0 < u \<and> u < 2" for u
  proof -
    have "\<bar>ln (max \<epsilon> \<bar>x - u\<bar>)\<bar> \<le>
      \<bar>ln \<epsilon>\<bar> + \<bar>x - u\<bar>" by (rule abs_ln_max_le[OF e abs_ge_zero])
    thus ?thesis using u
      by (smt (verit, del_insts) real_norm_def)
  qed
  have ae: "AE u in rho. norm (ln (max \<epsilon> \<bar>x - u\<bar>)) \<le>
    \<bar>ln \<epsilon>\<bar> + (\<bar>x\<bar> + 2)" using rho_AE_Ioo pt
    by (auto elim: eventually_mono)
  show ?thesis using finite_measure.integrable_const_bound[OF rho_finite ae m] .
qed

lemma rho_logmax_le:
  assumes e: "0 < \<epsilon>"
  shows "integral\<^sup>L rho (\<lambda>u. ln (max \<epsilon> \<bar>x - u\<bar>)) \<le>
    logPot rho x + 80 * sqrt \<epsilon>"
proof -
  define g where "g u = ln (max \<epsilon> \<bar>x - u\<bar>) - ln \<bar>x - u\<bar>" for u
  have i1: "integrable rho (\<lambda>u. ln (max \<epsilon> \<bar>x - u\<bar>))"
    by (rule rho_logmax_integrable[OF e])
  have i2: "integrable rho (\<lambda>u. ln \<bar>x - u\<bar>)" by (rule rho_log_integrable)
  have ig: "integrable rho g" unfolding g_def using i1 i2
    by simp
  have dif: "integral\<^sup>L rho (\<lambda>u. ln (max \<epsilon> \<bar>x - u\<bar>)) =
    logPot rho x + integral\<^sup>L rho g"
    unfolding g_def logPot_def using Bochner_Integration.integral_diff[OF i1 i2]
    by simp
  have nul: "{x} \<in> null_sets rho" using rho_singleton[of x] unfolding rho_def
    by auto
  have ane: "AE u in rho. u \<noteq> x" using AE_I'[OF nul, of "\<lambda>u. u \<noteq> x"]
    by auto
  have gpt: "g u = max 0 (ln (\<epsilon> / \<bar>x - u\<bar>))" if u: "u \<noteq> x" for u
  proof -
    have d0: "0 < \<bar>x - u\<bar>" using u
      by simp
    have ld: "ln (\<epsilon> / \<bar>x - u\<bar>) = ln \<epsilon> - ln \<bar>x - u\<bar>" using d0 e
      by (simp add: ln_div)
    show ?thesis
    proof (cases "\<epsilon> \<le> \<bar>x - u\<bar>")
      case True
      have "ln \<epsilon> \<le> ln \<bar>x - u\<bar>" using True e d0
        by simp
      thus ?thesis unfolding g_def ld using True
        by (simp add: max_def)
    next
      case False
      have "ln \<bar>x - u\<bar> < ln \<epsilon>" using False e d0
        by simp
      thus ?thesis unfolding g_def ld using False
        by (simp add: max_def)
    qed
  qed
  have gnn: "AE u in rho. 0 \<le> g u" using ane gpt
    by (auto elim: eventually_mono)
  have nnI: "ennreal (integral\<^sup>L rho g) =
    (\<integral>\<^sup>+ u. ennreal (g u) \<partial>rho)"
    using nn_integral_eq_integral[OF ig gnn]
    by simp
  have nnE: "(\<integral>\<^sup>+ u. ennreal (g u) \<partial>rho) =
    (\<integral>\<^sup>+ u. ennreal (max 0 (ln (\<epsilon> / \<bar>x - u\<bar>))) \<partial>rho)"
    using ane gpt by (auto intro: nn_integral_cong_AE elim: eventually_mono)
  have "ennreal (integral\<^sup>L rho g) \<le> ennreal (80 * sqrt \<epsilon>)" unfolding nnI nnE
    by (rule cross_bound[OF e])
  hence b2: "integral\<^sup>L rho g \<le> 80 * sqrt \<epsilon>" using e
    by (simp add: ennreal_le_iff)
  show ?thesis unfolding dif using b2
    by simp
qed

text \<open>The energies of a scaled sum of circle measures.\<close>
lemma csum_scale_integral:
  fixes t :: "nat \<Rightarrow> real" and h :: nat and \<epsilon> r :: real and f :: "complex
    \<Rightarrow> real"
  assumes r: "0 \<le> r" and f: "f \<in> borel_measurable borel" and fi: "\<And>i. i <
    h \<Longrightarrow> integrable (circ (of_real (t i)) \<epsilon>) f"
  shows "integral\<^sup>L (scale_measure (ennreal r) (distr (count_space {..<h} \<Otimes>\<^sub>M
    cden) borel (\<lambda>(i, \<theta>). of_real (t i) + of_real \<epsilon> * cis \<theta>))) f
      = r * (\<Sum> i < h. integral\<^sup>L (circ (of_real (t i)) \<epsilon>) f)"
proof -
  have fi': "\<And>i. i \<in> {..<h} \<Longrightarrow>
    integrable (circ (of_real (t i)) \<epsilon>) f" using fi
    by simp
  have fD: "f \<in> borel_measurable (distr (count_space {..<h} \<Otimes>\<^sub>M cden) borel
    (\<lambda>(i, \<theta>). of_real (t i) + of_real \<epsilon> * cis \<theta>))" using f
    by simp
  show ?thesis using scale_integral(1)[OF r fD] csum_integral(2)[OF finite_lessThan f fi']
    by simp
qed

lemma csum_energy_ge:
  fixes t :: "nat \<Rightarrow> real" and h :: nat and \<epsilon> r :: real and S :: "complex
    measure"
  assumes e: "0 < \<epsilon>" and inj: "inj_on t {..<h}" and r: "0 \<le> r"
    and S: "S = scale_measure (ennreal r) (distr (count_space {..<h} \<Otimes>\<^sub>M cden) borel
      (\<lambda>(i, \<theta>). of_real (t i) + of_real \<epsilon> * cis \<theta>))"
  shows "r ^ 2 * (\<Sum> i < h. \<Sum> j < h. (if i =
    j then ln \<epsilon> else ln \<bar>t i - t j\<bar>)) \<le> logEnergyC S S"
proof -
  define c :: "nat \<Rightarrow> complex" where "c i = of_real (t i)" for i
  define \<Phi> :: "complex \<Rightarrow> real" where "\<Phi> z = (\<Sum> j <
    h. ln (max \<epsilon> (norm (c j - z))))" for z
  have SI: "\<And>f. f \<in> borel_measurable borel \<Longrightarrow>
    (\<And>i. i < h \<Longrightarrow> integrable (circ (c i) \<epsilon>) f) \<Longrightarrow>
    integral\<^sup>L S f = r * (\<Sum> i < h. integral\<^sup>L (circ (c i) \<epsilon>) f)"
    unfolding S c_def using csum_scale_integral[OF r]
    by simp
  have inner: "\<And>z. integral\<^sup>L S (\<lambda>w. ln (norm (z - w))) = r * \<Phi> z"
  proof -
    fix z :: complex
    have fe: "(\<lambda>w. ln (norm (z - w))) = (\<lambda>w. ln (norm (w - z)))"
      by (simp add: norm_minus_commute)
    have mf: "(\<lambda>w :: complex. ln (norm (w - z))) \<in> borel_measurable borel"
      by simp
    have ii: "\<And>i. i < h \<Longrightarrow>
      integrable (circ (c i) \<epsilon>) (\<lambda>w. ln (norm (w - z)))"
      by (rule circ_log_integrable[OF e])
    have cl: "\<And>j. integral\<^sup>L (circ (c j) \<epsilon>) (\<lambda>w. ln (norm (w - z))) =
      ln (max \<epsilon> (norm (c j - z)))"
      by (rule circ_log[OF e])
    show "integral\<^sup>L S (\<lambda>w. ln (norm (z - w))) = r * \<Phi> z"
      unfolding fe \<Phi>_def using SI[OF mf ii] cl
      by simp
  qed
  have m\<Phi>j: "\<And>j. (\<lambda>z. ln (max \<epsilon> (norm (c j - z)))) \<in>
    borel_measurable borel"
    by simp
  have m\<Phi>: "\<Phi> \<in> borel_measurable borel" unfolding \<Phi>_def[abs_def] using m\<Phi>j
    by simp
  have i\<Phi>j: "\<And>i j. integrable (circ (c i) \<epsilon>) (\<lambda>z. ln (max \<epsilon>
    (norm (c j - z))))"
  proof -
    fix i j
    show "integrable (circ (c i) \<epsilon>) (\<lambda>z. ln (max \<epsilon> (norm (c j - z))))"
    proof (rule circ_integrable_bound[where B =
      "\<bar>ln \<epsilon>\<bar> + (norm (c j) + norm (c i) + \<bar>\<epsilon>\<bar>)"])
      show "(\<lambda>z. ln (max \<epsilon> (norm (c j - z)))) \<in> borel_measurable borel"
        by (rule m\<Phi>j)
      fix z :: complex assume hz: "norm (z - c i) = \<bar>\<epsilon>\<bar>"
      have b: "\<bar>ln (max \<epsilon> (norm (c j - z)))\<bar> \<le>
        \<bar>ln \<epsilon>\<bar> + norm (c j - z)" by (rule abs_ln_max_le[OF e norm_ge_zero])
      have nz: "norm (c j - z) \<le> norm (c j) + norm (c i) + \<bar>\<epsilon>\<bar>"
        using hz norm_triangle_ineq4[of "c j" z] norm_triangle_sub[of z "c i"]
        by simp
      show "\<bar>ln (max \<epsilon> (norm (c j - z)))\<bar> \<le>
        \<bar>ln \<epsilon>\<bar> + (norm (c j) + norm (c i) + \<bar>\<epsilon>\<bar>)" using b nz
        by simp
    qed
  qed
  have i\<Phi>: "\<And>i. i < h \<Longrightarrow> integrable (circ (c i) \<epsilon>) \<Phi>"
    unfolding \<Phi>_def using i\<Phi>j
    by simp
  have outer: "logEnergyC S S = r * (r * (\<Sum> i <
    h. integral\<^sup>L (circ (c i) \<epsilon>) \<Phi>))"
    unfolding logEnergyC_def inner using SI[OF m\<Phi> i\<Phi>]
    by simp
  have split: "\<And>i. integral\<^sup>L (circ (c i) \<epsilon>) \<Phi> = (\<Sum> j <
    h. integral\<^sup>L (circ (c i) \<epsilon>) (\<lambda>z. ln (max \<epsilon> (norm (c j - z)))))"
    unfolding \<Phi>_def using i\<Phi>j
    by simp
  have trm: "\<And>i j. i < h \<Longrightarrow> j < h \<Longrightarrow>
    (if i = j then ln \<epsilon> else ln \<bar>t i - t j\<bar>) \<le>
    integral\<^sup>L (circ (c i) \<epsilon>) (\<lambda>z. ln (max \<epsilon> (norm (c j - z))))"
  proof -
    fix i j assume i: "i < h" and j: "j < h"
    show "(if i = j then ln \<epsilon> else ln \<bar>t i - t j\<bar>) \<le>
      integral\<^sup>L (circ (c i) \<epsilon>) (\<lambda>z. ln (max \<epsilon> (norm (c j - z))))"
    proof (cases "i = j")
      case True
      have ae: "AE z in circ (c i) \<epsilon>. ln (max \<epsilon> (norm (c j - z))) =
        ln \<epsilon>" using circ_AE[of "c i" \<epsilon>] True e
        by (auto simp: norm_minus_commute elim: eventually_mono)
      have m1: "(\<lambda>z. ln (max \<epsilon> (norm (c j - z)))) \<in>
        borel_measurable (circ (c i) \<epsilon>)"
        using m\<Phi>j[of j] measurable_cong_sets[OF sets_circ refl]
        by blast
      have ic1: "integral\<^sup>L (circ (c i) \<epsilon>) (\<lambda>z. ln (max \<epsilon> (norm (c j
        - z)))) = integral\<^sup>L (circ (c i) \<epsilon>) (\<lambda>z. ln \<epsilon>)"
        using integral_cong_AE[OF m1 _ ae]
        by simp
      have ic2: "integral\<^sup>L (circ (c i) \<epsilon>) (\<lambda>z. ln \<epsilon>) =
        ln \<epsilon>" using circ_univ[of "c i" \<epsilon>] space_circ[of "c i" \<epsilon>]
        by (simp add: measure_def)
      show ?thesis using True ic1 ic2
        by auto
    next
      case False
      have "t i \<noteq> t j" using inj i j False unfolding inj_on_def
        by auto
      hence dpos: "0 < \<bar>t i - t j\<bar>"
        by simp
      have cne: "norm (c i - c j) = \<bar>t i - t j\<bar>" unfolding c_def
        by (metis norm_of_real of_real_hom.hom_minus)
      have nul: "{c j} \<in> null_sets (circ (c i) \<epsilon>)"
        using circ_singleton[OF e, of "c i" "c j"] sets_circ[of "c i" \<epsilon>]
        by auto
      have ane: "AE z in circ (c i) \<epsilon>. z \<noteq> c j"
        using AE_I'[OF nul, of "\<lambda>z. z \<noteq> c j"]
        by auto
      have pt: "\<And>z. z \<noteq> c j \<Longrightarrow>
        ln (norm (z - c j)) \<le> ln (max \<epsilon> (norm (c j - z)))"
        by (simp add: ln_mono norm_minus_commute)
      have aele: "AE z in circ (c i) \<epsilon>. ln (norm (z - c j)) \<le>
        ln (max \<epsilon> (norm (c j - z)))" using ane pt
        by (auto elim: eventually_mono)
      have i1: "integrable (circ (c i) \<epsilon>) (\<lambda>z. ln (norm (z - c j)))"
        by (rule circ_log_integrable[OF e])
      have mono: "integral\<^sup>L (circ (c i) \<epsilon>) (\<lambda>z. ln (norm (z - c j))) \<le>
        integral\<^sup>L (circ (c i) \<epsilon>) (\<lambda>z. ln (max \<epsilon> (norm (c j - z))))"
        by (rule integral_mono_AE[OF i1 i\<Phi>j aele])
      have cl: "integral\<^sup>L (circ (c i) \<epsilon>) (\<lambda>z. ln (norm (z - c j))) =
        ln (max \<epsilon> (norm (c i - c j)))" by (rule circ_log[OF e])
      have lm: "ln \<bar>t i - t j\<bar> \<le> ln (max \<epsilon> (norm (c i - c j)))"
        unfolding cne using dpos e
        by simp
      show ?thesis using False mono cl lm
        by simp
    qed
  qed
  have sumle: "(\<Sum> i < h. \<Sum> j < h. (if i =
    j then ln \<epsilon> else ln \<bar>t i - t j\<bar>)) \<le> (\<Sum> i <
    h. integral\<^sup>L (circ (c i) \<epsilon>) \<Phi>)"
    unfolding split using trm
    by (auto intro: sum_mono)
  show ?thesis unfolding outer using sumle r mult_left_mono[OF sumle, of "r * r"]
    by (simp add: power2_eq_square mult.assoc)
qed

lemma csum_cross_le:
  fixes t :: "nat \<Rightarrow> real" and h :: nat and \<epsilon> r :: real and S :: "complex
    measure"
  assumes e: "0 < \<epsilon>" and e1: "\<epsilon> \<le> 1" and tnn: "\<And>i. i <
    h \<Longrightarrow> 0 \<le> t i" and r: "0 \<le> r"
    and S: "S = scale_measure (ennreal r) (distr (count_space {..<h} \<Otimes>\<^sub>M cden) borel
      (\<lambda>(i, \<theta>). of_real (t i) + of_real \<epsilon> * cis \<theta>))"
  shows "logEnergyC S (distr rho borel of_real) \<le> r * (\<Sum> i <
    h. (logPot rho (t i) + 80 * sqrt \<epsilon>))"
proof -
  define c :: "nat \<Rightarrow> complex" where "c i = of_real (t i)" for i
  define \<rho>C :: "complex measure" where "\<rho>C = distr rho borel of_real"
  define F :: "complex \<Rightarrow> real" where "F z =
    integral\<^sup>L \<rho>C (\<lambda>w. ln (norm (z - w)))" for z
  have SI: "\<And>f. f \<in> borel_measurable borel \<Longrightarrow>
    (\<And>i. i < h \<Longrightarrow> integrable (circ (c i) \<epsilon>) f) \<Longrightarrow>
    integral\<^sup>L S f = r * (\<Sum> i < h. integral\<^sup>L (circ (c i) \<epsilon>) f)"
    unfolding S c_def using csum_scale_integral[OF r]
    by simp
  have fr: "finite_measure \<rho>C" unfolding \<rho>C_def by (rule rhoC_finite)
  have sr: "sets \<rho>C = sets borel" unfolding \<rho>C_def by (rule sets_rhoC)
  have sfr: "sigma_finite_measure \<rho>C" using fr
    by (simp add: finite_measure_def)
  have mp0: "(\<lambda>p :: complex \<times> complex. ln (norm (fst p - snd p))) \<in>
    borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by simp
  have sp: "sets ((borel :: complex measure) \<Otimes>\<^sub>M \<rho>C) =
    sets (borel \<Otimes>\<^sub>M borel)" using sr
    using sets_pair_measure_cong by simp
  have mp: "(\<lambda>(z, w). ln (norm (z - w))) \<in>
    borel_measurable ((borel :: complex measure) \<Otimes>\<^sub>M \<rho>C)"
    unfolding split_beta' using mp0 measurable_cong_sets[OF sp refl]
    by blast
  have mF: "F \<in> borel_measurable borel" unfolding F_def[abs_def]
    using sigma_finite_measure.borel_measurable_lebesgue_integral[OF sfr mp] .
  have aeR: "AE w in \<rho>C. norm w \<le> 2" unfolding \<rho>C_def by (rule rhoC_AE)
  have lgR: "\<And>z. (\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<rho>C) \<le>
    ennreal 80" unfolding \<rho>C_def by (rule rhoC_neg_log)
  have bound: "integral\<^sup>L (circ (c i) \<epsilon>) F \<le>
    logPot rho (t i) + 80 * sqrt \<epsilon>"
    and iF: "integrable (circ (c i) \<epsilon>) F" if i: "i < h" for i
  proof -
    have ci: "norm (c i) = t i" unfolding c_def using tnn[OF i]
      by simp
    have aeC: "AE z in circ (c i) \<epsilon>. norm z \<le> t i + 3"
    proof -
      have pt: "norm z \<le> t i + 3" if hz: "norm (z - c i) = \<bar>\<epsilon>\<bar>" for z
        using hz ci e e1 norm_triangle_sub[of z "c i"]
        by simp
      show ?thesis using circ_AE[of "c i" \<epsilon>] pt
        by (auto elim: eventually_mono)
    qed
    have aeR': "AE w in \<rho>C. norm w \<le> t i + 3" using aeR tnn[OF i]
      by (auto elim: eventually_mono)
    have Pi: "integrable (circ (c i) \<epsilon> \<Otimes>\<^sub>M \<rho>C) (\<lambda>p. ln (norm
      (fst p - snd p)))"
      by (rule integrable_log_prod[OF circ_finite fr sets_circ sr aeC aeR' lgR])
    have Pi': "integrable (circ (c i) \<epsilon> \<Otimes>\<^sub>M \<rho>C) (\<lambda>(x,
      y). ln (norm (x - y)))"
      unfolding split_beta' by (rule Pi)
    have ps: "pair_sigma_finite (circ (c i) \<epsilon>) \<rho>C"
      using circ_finite[of "c i" \<epsilon>] fr
      unfolding pair_sigma_finite_def by (simp add: finite_measure_def)
    show "integrable (circ (c i) \<epsilon>) F" unfolding F_def[abs_def]
      using pair_sigma_finite.integrable_fst[OF ps Pi'] .
    have s1: "integral\<^sup>L (circ (c i) \<epsilon>) F =
      integral\<^sup>L (circ (c i) \<epsilon> \<Otimes>\<^sub>M \<rho>C) (\<lambda>(x,
      y). ln (norm (x - y)))"
      unfolding F_def[abs_def] using pair_sigma_finite.integral_fst[OF ps Pi'] .
    have s2: "integral\<^sup>L (circ (c i) \<epsilon> \<Otimes>\<^sub>M \<rho>C) (\<lambda>(x,
      y). ln (norm (x - y))) = (\<integral> y. (\<integral> x. ln (norm (x -
      y)) \<partial>circ (c i) \<epsilon>) \<partial>\<rho>C)"
      using pair_sigma_finite.integral_snd[OF ps Pi'] by (rule sym)
    have s3: "\<And>y. (\<integral> x. ln (norm (x - y)) \<partial>circ (c i) \<epsilon>) =
      ln (max \<epsilon> (norm (c i - y)))" by (rule circ_log[OF e])
    have m4: "(\<lambda>y :: complex. ln (max \<epsilon> (norm (c i - y)))) \<in>
      borel_measurable borel"
      by simp
    have s4: "(\<integral> y. ln (max \<epsilon> (norm (c i - y))) \<partial>\<rho>C) =
      (\<integral> u. ln (max \<epsilon> (norm (c i - of_real u))) \<partial>rho)"
      unfolding \<rho>C_def by (rule integral_distr[OF rhoC_meas m4])
    have s5: "\<And>u. norm (c i - of_real u) = \<bar>t i - u\<bar>" unfolding c_def
      by (metis norm_of_real of_real_hom.hom_minus)
    have eqF: "integral\<^sup>L (circ (c i) \<epsilon>) F =
      (\<integral> u. ln (max \<epsilon> \<bar>t i - u\<bar>) \<partial>rho)"
      unfolding s1 s2 s3 s4 s5 ..
    show "integral\<^sup>L (circ (c i) \<epsilon>) F \<le> logPot rho (t i) + 80 * sqrt \<epsilon>"
      unfolding eqF by (rule rho_logmax_le[OF e])
  qed
  have outer: "logEnergyC S \<rho>C = r * (\<Sum> i <
    h. integral\<^sup>L (circ (c i) \<epsilon>) F)"
    unfolding logEnergyC_def F_def[symmetric] using SI[OF mF iF]
    by simp
  have sle: "(\<Sum> i < h. integral\<^sup>L (circ (c i) \<epsilon>) F) \<le> (\<Sum> i <
    h. (logPot rho (t i) + 80 * sqrt \<epsilon>))"
    using bound by (blast intro: sum_mono)
  show ?thesis unfolding \<rho>C_def[symmetric] outer using mult_left_mono[OF sle r] .
qed

theorem configuration_bound:
  fixes t :: "nat \<Rightarrow> real"
  assumes "40 dvd K" "0 < K" "\<And>i. i < hof K \<Longrightarrow>
    0 \<le> t i" "inj_on t {..<hof K}"
  shows "2 * (\<Sum> i < hof K. \<Sum> j \<in> {j. i < j \<and>
    j < hof K}. ln \<bar>t i - t j\<bar>)
           - real K * (\<Sum> i < hof K. Vf (t i)) + (\<Sum> i < hof K. sqrt (t i))
         \<le> (lam_r * of_rat M0c - logEnergy rho) * real K ^ 2
           + (120 + sqrt 2) * real (hof K) + 2 * real (hof K) * ln (real K)"
proof -
  define h where "h = hof K"
  define \<epsilon> where "\<epsilon> = (1 / (2 * real K)) ^ 2"
  have e0: "0 < \<epsilon>" using assms(2) unfolding \<epsilon>_def by simp
  have sqe: "sqrt \<epsilon> = 1 / (2 * real K)" unfolding \<epsilon>_def using assms(2)
    by simp
  have lne: "ln \<epsilon> = - 2 * ln 2 - 2 * ln (real K)" unfolding \<epsilon>_def using assms(2)
    by (simp add: ln_realpow ln_div ln_mult)
  have hK: "real h = lam_r * real K" unfolding h_def using assms(1)
    by (auto elim!: dvdE simp: hof_def lam_r_def)
  text \<open>The regularised configuration
    @{text "\<sigma> = K^-^1 \<Sum>_i \<omega>(t_i, \<epsilon>)"} as one push-forward measure,
    and @{text "\<rho>"} on @{text \<complex>}.\<close>
  define \<sigma> where "\<sigma> = scale_measure (ennreal (1 / real K))
     (distr (count_space {..<h} \<Otimes>\<^sub>M density lborel (\<lambda>\<theta>. ennreal
       (indicator {0..2 * pi} \<theta> / (2 * pi)))) borel
            (\<lambda>(i, \<theta>). of_real (t i) + of_real \<epsilon> * cis \<theta>))"
  define \<rho>C :: "complex measure" where "\<rho>C = distr rho borel of_real"
  have sig_univ: "emeasure \<sigma> UNIV = ennreal (real h / real K)"
  proof -
    have D1: "emeasure (distr (count_space {..<h} \<Otimes>\<^sub>M density lborel
      (\<lambda>\<theta>. ennreal (indicator {0..2 * pi} \<theta> / (2 * pi)))) borel (\<lambda>(i,
      \<theta>). of_real (t i) + of_real \<epsilon> * cis \<theta>)) UNIV = of_nat h"
      using csum_emeasure[where I = "{..<h}" and A = UNIV and c =
        "\<lambda>i. of_real (t i)" and \<epsilon> = \<epsilon>] circ_univ
      by simp
    show ?thesis unfolding \<sigma>_def using D1
      by (simp add: ennreal_of_nat_eq_real_of_nat ennreal_mult'["symmetric"])
  qed
  have rhoC_univ: "emeasure \<rho>C UNIV = ennreal lam_r"
  proof -
    have m: "(of_real :: real \<Rightarrow> complex) \<in> measurable rho borel" unfolding rho_def
      by simp
    have sp: "space rho = UNIV" unfolding rho_def
      by simp
    show ?thesis unfolding \<rho>C_def using emeasure_distr[OF m, of UNIV] sp rho_univ
      by simp
  qed
  have mass: "emeasure \<sigma> UNIV = emeasure \<rho>C UNIV" unfolding sig_univ rhoC_univ hK
    using assms(2) by simp
  have inj': "inj_on t {..<h}" using assms(4) unfolding h_def .
  have k0: "0 \<le> 1 / real K"
    by simp
  have energy_sig_ge: "(1 / real K ^ 2) * ((\<Sum> i < h. \<Sum> j < h. (if i =
    j then ln \<epsilon> else ln \<bar>t i - t j\<bar>))) \<le> logEnergyC \<sigma> \<sigma>"
    using csum_energy_ge[OF e0 inj' k0 \<sigma>_def] by (simp add: power_divide)
  have e1c: "\<epsilon> \<le> 1" unfolding \<epsilon>_def using assms(2)
    by (simp add: power_le_one)
  have tnnc: "\<And>i. i < h \<Longrightarrow> 0 \<le> t i" using assms(3) unfolding h_def
    by simp
  have energy_cross_le: "logEnergyC \<sigma> \<rho>C \<le> (1 / real K) * (\<Sum> i <
    h. (logPot rho (t i) + 80 * sqrt \<epsilon>))"
    unfolding \<rho>C_def by (rule csum_cross_le[OF e0 e1c tnnc k0 \<sigma>_def])
  have energy_rhoC: "logEnergyC \<rho>C \<rho>C = logEnergy rho"
  proof -
    have inner: "\<And>z. integral\<^sup>L \<rho>C (\<lambda>w. ln (norm (z - w))) =
      integral\<^sup>L rho (\<lambda>u. ln (norm (z - of_real u)))"
      unfolding \<rho>C_def using integral_distr[OF rhoC_meas] by force
    have sfr: "sigma_finite_measure rho" using rho_finite
      by (simp add: finite_measure_def)
    have mp0: "(\<lambda>p :: complex \<times> real. ln (norm (fst p - of_real (snd p)))) \<in>
      borel_measurable (borel \<Otimes>\<^sub>M borel)"
      by simp
    have sp: "sets ((borel :: complex measure) \<Otimes>\<^sub>M rho) =
      sets (borel \<Otimes>\<^sub>M borel)" unfolding rho_def
      using sets_pair_measure_cong by simp
    have mp: "(\<lambda>(z, u). ln (norm (z - of_real u))) \<in>
      borel_measurable ((borel :: complex measure) \<Otimes>\<^sub>M rho)"
      unfolding split_beta' using mp0 measurable_cong_sets[OF sp refl] by blast
    have mG: "(\<lambda>z :: complex. integral\<^sup>L rho (\<lambda>u. ln (norm (z -
      of_real u)))) \<in> borel_measurable borel"
      using sigma_finite_measure.borel_measurable_lebesgue_integral[OF sfr mp] .
    have outer: "integral\<^sup>L \<rho>C (\<lambda>z. integral\<^sup>L rho (\<lambda>u. ln (norm (z
      - of_real u)))) = integral\<^sup>L rho (\<lambda>x. integral\<^sup>L rho (\<lambda>u. ln (norm
      (of_real x - of_real u :: complex))))"
      unfolding \<rho>C_def by (rule integral_distr[OF rhoC_meas mG])
    have pt: "\<And>x u :: real. ln (norm (of_real x - of_real u :: complex)) =
      ln \<bar>x - u\<bar>"
      by (metis norm_of_real of_real_hom.hom_minus)
    show ?thesis unfolding logEnergyC_def logEnergy_def logPot_def inner outer pt ..
  qed
  text \<open>The dominating measure @{text "\<eta> = \<sigma> + \<rho>C"}
    for Lemma 6.2 (Isabelle has no sum of measures: use @{text "sup_measure'"} or an explicit
    @{text measure_of}).\<close>
  define \<eta> :: "complex measure" where "\<eta> =
    measure_of UNIV (sets borel) (\<lambda>A. emeasure \<sigma> A + emeasure \<rho>C A)"
  have sets_sig: "sets \<sigma> = sets borel"
    unfolding \<sigma>_def by simp
  have sets_rho: "sets \<rho>C = sets borel"
    unfolding \<rho>C_def by simp
  have sets_eta: "sets \<eta> = sets borel"
    unfolding \<eta>_def by (rule summ_sets)
  have em_eta: "\<And>A. A \<in> sets borel \<Longrightarrow>
    emeasure \<eta> A = emeasure \<sigma> A + emeasure \<rho>C A"
    unfolding \<eta>_def using summ_emeasure[OF sets_sig sets_rho] by simp
  have fin: "finite_measure \<eta>"
    using em_eta[of UNIV] sig_univ rhoC_univ sets_eta sets_eq_imp_space_eq[OF sets_eta]
      by (auto intro: finite_measureI)
  have le1: "\<sigma> \<le> \<eta>"
    using le_measure[of \<sigma> \<eta>] sets_sig sets_eta em_eta by simp
  have le2: "\<rho>C \<le> \<eta>"
    using le_measure[of \<rho>C \<eta>] sets_rho sets_eta em_eta by simp
  have nn_sum: "\<And>f. f \<in> borel_measurable borel \<Longrightarrow>
    (\<integral>\<^sup>+ z. f z \<partial>\<eta>) \<le>
    (\<integral>\<^sup>+ z. f z \<partial>\<sigma>) +
    (\<integral>\<^sup>+ z. f z \<partial>\<rho>C)"
    unfolding \<eta>_def using summ_nn[OF sets_sig sets_rho] by simp
  have int_eta: "integrable (\<eta> \<Otimes>\<^sub>M \<eta>) (\<lambda>zw. ln (norm (fst zw -
    snd zw)))"
  proof -
    define R0 :: real where "R0 = (\<Sum> i < h. t i) + 3"
    have tnn: "\<And>i. i < h \<Longrightarrow> 0 \<le> t i" using assms(3) unfolding h_def
      by simp
    have tle: "\<And>i. i < h \<Longrightarrow> t i \<le> (\<Sum> j < h. t j)" using tnn
      by (auto intro: member_le_sum)
    have e1: "\<epsilon> \<le> 1" unfolding \<epsilon>_def using assms(2)
      by (simp add: power_le_one)
    have R3: "3 \<le> R0" unfolding R0_def using tnn
      by (auto intro: sum_nonneg)
    have cR: "\<And>i. i < h \<Longrightarrow>
      norm (of_real (t i) :: complex) + \<epsilon> \<le> R0" unfolding R0_def using tle tnn e1
      by force
    have lne0: "ln \<epsilon> \<le> 0" using e0 e1
      by simp
    define B where "B = 2 * R0 - ln \<epsilon>"
    have B0: "0 \<le> B" unfolding B_def using R3 lne0
      by simp
    define N where "N = {z :: complex. R0 < norm z}"
    have Nm: "N \<in> sets borel" unfolding N_def
      by (auto intro: borel_open open_Collect_less continuous_intros)
    have cN: "\<And>i. i < h \<Longrightarrow> emeasure (circ (of_real (t i)) \<epsilon>) N = 0"
    proof -
      fix i assume i: "i < h"
      have pt: "z \<notin> N" if hz: "norm (z - of_real (t i)) = \<bar>\<epsilon>\<bar>" for z
        using hz cR[OF i] e0 norm_triangle_sub[of z "of_real (t i)"] unfolding N_def
        by simp
      have ae: "AE z in circ (of_real (t i)) \<epsilon>. z \<notin> N"
        using circ_AE[of "of_real (t i)" \<epsilon>] pt
        by (auto elim: eventually_mono)
      show "emeasure (circ (of_real (t i)) \<epsilon>) N = 0"
        using AE_iff_measurable[of N "circ (of_real (t i)) \<epsilon>" "\<lambda>z. z \<notin> N"]
        ae Nm sets_circ space_circ
        by simp
    qed
    have sN: "emeasure \<sigma> N = 0" unfolding \<sigma>_def
      using csum_emeasure[where I = "{..<h}" and A = N and c =
        "\<lambda>i. of_real (t i)" and \<epsilon> = \<epsilon>] Nm cN
      by simp
    have rN: "emeasure \<rho>C N = 0"
    proof -
      have ae: "AE w in \<rho>C. w \<notin> N" using rhoC_AE R3 unfolding \<rho>C_def N_def
        by (auto elim: eventually_mono)
      show ?thesis using AE_iff_measurable[of N \<rho>C "\<lambda>z. z \<notin> N"] ae Nm sets_rho
        sets_eq_imp_space_eq[OF sets_rho]
        by simp
    qed
    have eN: "emeasure \<eta> N = 0" using em_eta[OF Nm] sN rN
      by simp
    have ae\<eta>: "AE z in \<eta>. norm z \<le> R0"
      using AE_iff_measurable[of N \<eta> "\<lambda>z. norm z \<le>
        R0"] Nm sets_eta sets_eq_imp_space_eq[OF sets_eta] eN unfolding N_def
      by force
    have lg: "\<And>z. norm z \<le> R0 \<Longrightarrow>
      (\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<eta>) \<le>
      ennreal (real h / real K * B + 80)"
    proof -
      fix z :: complex assume hz: "norm z \<le> R0"
      have mf: "(\<lambda>w. ennreal (- ln (norm (z - w)))) \<in> borel_measurable borel"
        by simp
      have mfD: "(\<lambda>w. ennreal (- ln (norm (z - w)))) \<in>
        borel_measurable (distr (count_space {..<h} \<Otimes>\<^sub>M density lborel
        (\<lambda>\<theta>. ennreal (indicator {0..2 * pi} \<theta> / (2 *
        pi)))) borel (\<lambda>(i, \<theta>). of_real (t i) + of_real \<epsilon> * cis \<theta>))"
        using mf
        by simp
      have a1: "(\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<eta>) \<le>
        (\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<sigma>) +
        (\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<rho>C)"
        by (rule nn_sum[OF mf])
      have a2: "(\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<sigma>) =
        ennreal (1 / real K) * (\<Sum> i <
        h. \<integral>\<^sup>+ w. ennreal (- ln (norm (z -
        w))) \<partial>circ (of_real (t i)) \<epsilon>)"
        unfolding \<sigma>_def using nn_integral_scale_measure[OF mfD] csum_nn[OF finite_lessThan
          mf]
        by simp
      have a3: "(\<Sum> i < h. \<integral>\<^sup>+ w. ennreal (- ln (norm (z -
        w))) \<partial>circ (of_real (t i)) \<epsilon>) \<le> (\<Sum> i < h. ennreal B)"
        using circ_neg_log[OF e0 cR hz] unfolding B_def
        by (blast intro: sum_mono)
      have a4: "(\<Sum> i < h. ennreal B) = ennreal (real h * B)" using B0
        by (simp add: ennreal_of_nat_eq_real_of_nat ennreal_mult)
      have a5: "ennreal (1 / real K) * ennreal (real h * B) = ennreal (real h / real K * B)"
        using B0
        by (simp add: ennreal_mult["symmetric"])
      have a6: "(\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<rho>C) \<le>
        ennreal 80" unfolding \<rho>C_def by (rule rhoC_neg_log)
      have a7: "ennreal (real h / real K * B) + ennreal 80 = ennreal (real h / real K * B + 80)"
        using B0
        by (simp add: ennreal_plus)
      have "(\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<eta>) \<le>
        (\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<sigma>) +
        (\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<rho>C)"
        by (rule a1)
      also have "\<dots> \<le> ennreal (1 / real K) * (\<Sum> i < h. ennreal B) + ennreal 80"
        unfolding a2 using a3 a6
        by (force intro: add_mono mult_left_mono)
      also have "\<dots> = ennreal (real h / real K * B + 80)" unfolding a4 a5 a7 ..
      finally show "(\<integral>\<^sup>+ w. ennreal (- ln (norm (z - w))) \<partial>\<eta>) \<le>
        ennreal (real h / real K * B + 80)" .
    qed
    show ?thesis by (rule integrable_log_prod[OF fin fin sets_eta sets_eta ae\<eta> ae\<eta> lg])
  qed
  have diag: "emeasure (\<eta> \<Otimes>\<^sub>M \<eta>) {zw. fst zw = snd zw} = 0"
  proof -
    have sfe: "sigma_finite_measure \<eta>" using fin
      by (simp add: finite_measure_def)
    have Dm0: "{zw :: complex \<times> complex. fst zw = snd zw} \<in>
      sets (borel \<Otimes>\<^sub>M borel)"
    proof -
      have mf: "(\<lambda>p :: complex \<times> complex. fst p - snd p) \<in>
        borel_measurable (borel \<Otimes>\<^sub>M borel)"
        by simp
      have eq: "{p :: complex \<times> complex. fst p = snd p} =
        (\<lambda>p. fst p - snd p) -` {0} \<inter> space (borel \<Otimes>\<^sub>M borel)"
        by (auto simp: space_pair_measure)
      show ?thesis unfolding eq using measurable_sets[OF mf, of "{0}"]
        by simp
    qed
    have Dm: "{zw :: complex \<times> complex. fst zw = snd zw} \<in>
      sets (\<eta> \<Otimes>\<^sub>M \<eta>)" using Dm0 sets_pair_measure_cong[OF sets_eta sets_eta]
      by simp
    have e1: "emeasure (\<eta> \<Otimes>\<^sub>M \<eta>) {zw. fst zw = snd zw} =
      (\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. indicator {zw :: complex \<times>
      complex. fst zw = snd zw} (z, w) \<partial>\<eta> \<partial>\<eta>)"
      by (rule sigma_finite_measure.emeasure_pair_measure[OF sfe Dm])
    have sz: "\<And>z. emeasure \<sigma> {z} = 0"
    proof -
      fix z :: complex
      have "emeasure \<sigma> {z} = ennreal (1 / real K) * (\<Sum> i <
        h. emeasure (circ (of_real (t i)) \<epsilon>) {z})" unfolding \<sigma>_def
        using csum_emeasure[where I = "{..<h}" and A = "{z}" and c =
          "\<lambda>i. of_real (t i)" and \<epsilon> = \<epsilon>] by simp
      thus "emeasure \<sigma> {z} = 0" using circ_singleton[OF e0]
        by simp
    qed
    have rz: "\<And>z. emeasure \<rho>C {z} = 0" unfolding \<rho>C_def by (rule rhoC_singleton)
    have pt: "\<And>z. (\<integral>\<^sup>+ w. indicator {zw :: complex \<times> complex. fst zw =
      snd zw} (z, w) \<partial>\<eta>) = 0"
    proof -
      fix z :: complex
      have ind: "(\<lambda>w. indicator {zw :: complex \<times> complex. fst zw =
        snd zw} (z, w) :: ennreal) = indicator {z}"
        by (simp add: fun_eq_iff indicator_def)
      show "(\<integral>\<^sup>+ w. indicator {zw :: complex \<times> complex. fst zw =
        snd zw} (z, w) \<partial>\<eta>) = 0" unfolding ind using em_eta[of "{z}"] sz rz sets_eta
        by simp
    qed
    show ?thesis unfolding e1 pt
      by simp
  qed
  have eta: "finite_measure \<eta>" "sets \<eta> = sets borel" "\<sigma> \<le>
    \<eta>" "\<rho>C \<le> \<eta>"
      "integrable (\<eta> \<Otimes>\<^sub>M \<eta>) (\<lambda>zw. ln (norm (fst zw -
        snd zw)))" "emeasure (\<eta> \<Otimes>\<^sub>M \<eta>) {zw. fst zw = snd zw} = 0"
    by fact+
  have L62: "logEnergyC \<sigma> \<sigma> - 2 * logEnergyC \<sigma> \<rho>C +
    logEnergyC \<rho>C \<rho>C \<le> 0"
    by (rule log_energy_zero_mass_nonpos[OF eta(1) _ _ eta(2) eta(3,4) mass eta(5,6)]) (simp_all
      add: \<sigma>_def \<rho>C_def)
  have fb: "\<And>i. i < h \<Longrightarrow>
    2 * logPot rho (t i) - Vf (t i) + sqrt (t i) / real K \<le> of_rat M0c + sqrt 2 / real K"
  proof -
    fix i assume i: "i < h"
    have K40: "40 \<le> real K" using assms(1,2)
      by (auto elim: dvdE)
    have t0: "0 \<le> t i" using assms(3) i unfolding h_def
      by simp
    show "2 * logPot rho (t i) - Vf (t i) + sqrt (t i) / real K \<le> of_rat M0c + sqrt 2 / real K"
      using field_bound[OF K40 t0]
      by simp
  qed
  have pair: "(\<Sum> i < h. \<Sum> j < h. (if i =
    j then ln \<epsilon> else ln \<bar>t i - t j\<bar>)) = 2 * (\<Sum> i < h. \<Sum> j \<in> {j. i <
    j \<and> j < h}. ln \<bar>t i - t j\<bar>) + real h * ln \<epsilon>"
  proof -
    define L where "L i j = ln \<bar>t i - t j\<bar>" for i j
    have sym: "L i j = L j i" for i j unfolding L_def
      by (simp add: abs_minus_commute)
    have row: "(\<Sum> j < h. (if i = j then ln \<epsilon> else L i j)) =
      ln \<epsilon> + (\<Sum> j \<in> {j. i < j \<and>
      j < h}. L i j) + (\<Sum> j \<in> {j. j < i}. L i j)" if i: "i < h" for i
    proof -
      have r1: "(\<Sum> j < h. (if i = j then ln \<epsilon> else L i j)) =
        ln \<epsilon> + (\<Sum> j \<in> {..<h} - {i}. L i j)" using i
        by (simp add: sum.remove if_distrib sum.If_cases)
      have r2: "{..<h} - {i} = {j. i < j \<and> j < h} \<union> {j. j < i}" using i
        by auto
      have r3: "(\<Sum> j \<in> {j. i < j \<and>
        j < h} \<union> {j. j < i}. L i j) = (\<Sum> j \<in> {j. i < j \<and>
        j < h}. L i j) + (\<Sum> j \<in> {j. j < i}. L i j)"
        by (auto intro: sum.union_disjoint)
      show ?thesis unfolding r1 r2 r3
        by simp
    qed
    have rows: "(\<Sum> i < h. \<Sum> j < h. (if i = j then ln \<epsilon> else L i j)) =
      real h * ln \<epsilon> + (\<Sum> i < h. \<Sum> j \<in> {j. i < j \<and>
      j < h}. L i j) + (\<Sum> i < h. \<Sum> j \<in> {j. j < i}. L i j)"
      using row
      by (simp add: sum.distrib)
    have sw1: "(\<Sum> i < h. \<Sum> j \<in> {j. j < i}. L i j) = (\<Sum> i < h. \<Sum> j \<in>
      {j. j \<in> {..<h} \<and> j < i}. L i j)"
      by (force intro: sum.cong)
    have sw2: "(\<Sum> i < h. \<Sum> j \<in> {j. j \<in> {..<h} \<and>
      j < i}. L i j) = (\<Sum> j < h. \<Sum> i \<in> {i. i \<in> {..<h} \<and> j < i}. L i j)"
      using sum.swap_restrict[of "{..<h}" "{..<h}" L "\<lambda>i j. j < i"]
      by simp
    have sw3: "(\<Sum> j < h. \<Sum> i \<in> {i. i \<in> {..<h} \<and>
      j < i}. L i j) = (\<Sum> i < h. \<Sum> j \<in> {j. i < j \<and> j < h}. L i j)"
      using sym by (auto simp: conj_commute intro: sum.cong)
    show ?thesis using rows sw1 sw2 sw3 unfolding L_def
      by linarith
  qed
  define S2 where "S2 = (\<Sum> i < h. \<Sum> j \<in> {j. i < j \<and>
    j < h}. ln \<bar>t i - t j\<bar>)"
  define A where "A = (\<Sum> i < h. logPot rho (t i))"
  define Vs where "Vs = (\<Sum> i < h. Vf (t i))"
  define Ss where "Ss = (\<Sum> i < h. sqrt (t i))"
  define I where "I = logEnergy rho"
  define \<kappa> where "\<kappa> = real K"
  have k0: "0 < \<kappa>" unfolding \<kappa>_def using assms(2)
    by simp
  have "(\<Sum> i < h. 2 * logPot rho (t i) - Vf (t i) + sqrt (t i) / real K) \<le> (\<Sum> i <
    h. of_rat M0c + sqrt 2 / real K)"
    using fb
    by (blast intro: sum_mono)
  hence fbs: "2 * A - Vs + Ss / \<kappa> \<le> real h * (of_rat M0c + sqrt 2 / \<kappa>)"
    unfolding A_def Vs_def Ss_def \<kappa>_def
    by (simp add: sum.distrib sum_subtractf sum_distrib_left sum_divide_distrib)
  have fbK: "2 * A * \<kappa> - Vs * \<kappa> + Ss \<le>
    real h * of_rat M0c * \<kappa> + real h * sqrt 2"
  proof -
    have "(2 * A - Vs + Ss / \<kappa>) * \<kappa> \<le>
      real h * (of_rat M0c + sqrt 2 / \<kappa>) * \<kappa>" using fbs k0
      by (simp add: mult_right_mono)
    thus ?thesis using k0
      by (simp add: algebra_simps)
  qed
  have cs: "(\<Sum> i < h. (logPot rho (t i) + 80 * sqrt \<epsilon>)) =
    A + real h * (40 / \<kappa>)" unfolding A_def sqe \<kappa>_def
    by (simp add: sum.distrib)
  have ec: "logEnergyC \<sigma> \<rho>C \<le> (A + real h * (40 / \<kappa>)) / \<kappa>"
    using energy_cross_le unfolding cs \<kappa>_def
    by simp
  have "(2 * S2 + real h * ln \<epsilon>) / \<kappa> ^ 2 \<le> logEnergyC \<sigma> \<sigma>"
    using energy_sig_ge unfolding pair S2_def \<kappa>_def
    by (simp add: power2_eq_square)
  hence comb: "(2 * S2 + real h * ln \<epsilon>) / \<kappa> ^ 2 \<le>
    2 * ((A + real h * (40 / \<kappa>)) / \<kappa>) - I"
    using ec L62 energy_rhoC unfolding I_def
    by linarith
  have combK: "2 * S2 + real h * ln \<epsilon> \<le>
    2 * A * \<kappa> + 80 * real h - I * \<kappa> ^ 2"
  proof -
    have m: "(2 * S2 + real h * ln \<epsilon>) / \<kappa> ^ 2 * \<kappa> ^ 2 \<le>
      (2 * ((A + real h * (40 / \<kappa>)) / \<kappa>) - I) * \<kappa> ^ 2"
      using mult_right_mono[OF comb, of "\<kappa> ^ 2"] k0 by simp
    have e1: "(2 * S2 + real h * ln \<epsilon>) / \<kappa> ^ 2 * \<kappa> ^ 2 =
      2 * S2 + real h * ln \<epsilon>" using k0
      by simp
    have e2: "(2 * ((A + real h * (40 / \<kappa>)) / \<kappa>) - I) * \<kappa> ^ 2 =
      2 * A * \<kappa> + 80 * real h - I * \<kappa> ^ 2"
      using k0 by (simp add: power2_eq_square algebra_simps)
    show ?thesis using m e1 e2
      by simp
  qed
  have hl: "real h * ln \<epsilon> = - 2 * real h * ln 2 - 2 * real h * ln \<kappa>"
    unfolding lne \<kappa>_def by (simp add: algebra_simps)
  have l2: "real h * ln 2 \<le> real h" using mult_left_le[of "ln 2" "real h"] ln_2_less_1
    by simp
  have hM: "real h * of_rat M0c * \<kappa> = lam_r * of_rat M0c * \<kappa> ^ 2"
    unfolding hK \<kappa>_def
    by (simp add: power2_eq_square)
  have fin: "2 * S2 - \<kappa> * Vs + Ss \<le>
    (lam_r * of_rat M0c - I) * \<kappa> ^ 2 + (120 + sqrt 2) * real h + 2 * real h * ln \<kappa>"
  proof -
    have r: "(lam_r * of_rat M0c - I) * \<kappa> ^ 2 + (120 + sqrt 2) * real h + 2 * real h *
      ln \<kappa> = lam_r * of_rat M0c * \<kappa> ^ 2 - I * \<kappa> ^ 2 + 120 * real h + real h *
      sqrt 2 + 2 * real h * ln \<kappa>"
      by (simp add: algebra_simps)
    have v: "\<kappa> * Vs = Vs * \<kappa>"
      by simp
    have h0: "0 \<le> real h"
      by simp
    show ?thesis unfolding r v using fbK combK hl l2 hM h0
      by simp
  qed
  show ?thesis using fin unfolding S2_def Vs_def Ss_def I_def \<kappa>_def h_def .
qed

subsection \<open>(6.14), (6.15) and Proposition 6.3\<close>

text \<open>@{text "\<integral>_0^\<infinity> (1+y)^5 e^{-y/\<kappa>} dy \<le> 3872 \<kappa>^6"}
  (Lean: @{text "phi_bound"}).\<close>
lemma phi_aux:
  fixes \<kappa> :: real
  assumes "1 \<le> \<kappa>"
  shows "set_integrable lborel {0<..} (\<lambda>y. (1 + y) ^ 5 * exp (- y / \<kappa>))"
    and "set_lebesgue_integral lborel {0<..} (\<lambda>y. (1 + y) ^ 5 * exp (- y / \<kappa>)) \<le>
      3872 * \<kappa> ^ 6"
proof -
  have k0: "0 < \<kappa>" using assms
    by simp
  have c0: "0 < 1 / \<kappa>" using k0
    by simp
  define g0 :: "real \<Rightarrow> real" where "g0 y = y ^ 0 * exp (- ((1 / \<kappa>) * y))" for y
  define g5 :: "real \<Rightarrow> real" where "g5 y = y ^ 5 * exp (- ((1 / \<kappa>) * y))" for y
  define \<psi> :: "real \<Rightarrow> real" where "\<psi> y = 32 * g0 y + 32 * g5 y" for y
  have i0: "set_integrable lborel {0<..} g0" unfolding g0_def using gam_integrable[OF c0, of 0]
    by simp
  have i5: "set_integrable lborel {0<..} g5" unfolding g5_def using gam_integrable[OF c0, of 5]
    by simp
  have v0: "set_lebesgue_integral lborel {0<..} g0 = \<kappa>" unfolding g0_def
    using gam[OF c0, of 0] k0
    by simp
  have v5: "set_lebesgue_integral lborel {0<..} g5 = 120 * \<kappa> ^ 6" unfolding g5_def
    using gam[OF c0, of 5] k0
    by (simp add: fact_numeral power_one_over)
  have ipsi: "set_integrable lborel {0<..} \<psi>" unfolding \<psi>_def using i0 i5
    by simp
  have vpsi: "set_lebesgue_integral lborel {0<..} \<psi> = 32 * \<kappa> + 3840 * \<kappa> ^ 6"
    unfolding \<psi>_def using i0 i5 v0 v5
    by simp
  have p5: "(1 + y) ^ 5 \<le> 32 * (1 + y ^ 5)" if y: "0 \<le> y" for y :: real
  proof (cases "y \<le> 1")
    case True
    have "(1 + y) ^ 5 \<le> (2 :: real) ^ 5" using power_mono[of "1 + y" 2 5] True y
      by simp
    moreover have "(2 :: real) ^ 5 = 32"
      by simp
    moreover have "0 \<le> y ^ 5" using y
      by simp
    ultimately show ?thesis
      by argo
  next
    case False
    have "(1 + y) ^ 5 \<le> (2 * y) ^ 5" using power_mono[of "1 + y" "2 * y" 5] False y
      by simp
    also have "\<dots> = 32 * y ^ 5"
      by (simp add: power_mult_distrib)
    finally show ?thesis
      by simp
  qed
  have bound: "(1 + y) ^ 5 * exp (- y / \<kappa>) \<le> \<psi> y" if y: "0 < y" for y
  proof -
    have e: "exp (- y / \<kappa>) = exp (- ((1 / \<kappa>) * y))"
      by simp
    have "(1 + y) ^ 5 * exp (- y / \<kappa>) \<le> 32 * (1 + y ^ 5) * exp (- y / \<kappa>)"
      using p5[of y] y
      by simp
    also have "\<dots> = \<psi> y" unfolding \<psi>_def g0_def g5_def e
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have meas: "set_borel_measurable lborel {0<..} (\<lambda>y. (1 + y) ^ 5 * exp (- y / \<kappa>))"
    unfolding set_borel_measurable_def by simp
  have nn: "0 \<le> (1 + y) ^ 5 * exp (- y / \<kappa>)" if "0 < y" for y :: real using that
    by simp
  have AE: "AE y in lborel. y \<in> {0<..} \<longrightarrow>
    norm ((1 + y) ^ 5 * exp (- y / \<kappa>)) \<le> norm (\<psi> y)"
    using bound nn
    by (force simp: AE_I2)
  show I: "set_integrable lborel {0<..} (\<lambda>y. (1 + y) ^ 5 * exp (- y / \<kappa>))"
    using set_integrable_bound[OF ipsi meas AE] .
  have k6: "\<kappa> ^ 1 \<le> \<kappa> ^ 6" using power_increasing[of 1 6 \<kappa>] assms
    by simp
  have "set_lebesgue_integral lborel {0<..} (\<lambda>y. (1 + y) ^ 5 * exp (- y / \<kappa>)) \<le>
    set_lebesgue_integral lborel {0<..} \<psi>"
    using set_integral_mono[OF I ipsi] bound
    by simp
  also have "\<dots> \<le> 3872 * \<kappa> ^ 6" unfolding vpsi using k6
    by simp
  finally show "set_lebesgue_integral lborel {0<..} (\<lambda>y. (1 + y) ^ 5 * exp (- y /
    \<kappa>)) \<le> 3872 * \<kappa> ^ 6" .
qed

text \<open>(6.14): @{text "log \<Delta>_K(\<zeta>(5)) \<le>
  2h(h + 6N - K) log K + (\<lambda>M_0 - I(\<rho>))K^2 + 18h log K + 160h"}.\<close>
theorem log_DeltaK_zeta5_bound:
  assumes "40 dvd K" "0 < K"
  shows "ln (real_eval (DeltaK K) zeta5) \<le>
           2 * real (hof K) * (real (hof K) + 6 * real (Nof K) - real K) * ln (real K)
           + (lam_r * of_rat M0c - logEnergy rho) * real K ^ 2
           + 18 * real (hof K) * ln (real K) + 160 * real (hof K)"
proof -
  define h where "h = hof K"
  define N where "N = Nof K"
  define E where "E = (lam_r * of_rat M0c - logEnergy rho) * real K ^ 2 + (120 + sqrt 2) * real h +
    2 * real h * ln (real K)"
  define c0 where "c0 = 8192 * exp 12 * real K ^ (12 * N + 12) / real K ^ (2 * K)"
  have hN: "1 \<le> N" "N \<le> K" "real N / real K = 3 / 40" "0 < h"
  proof -
    obtain k where k: "K = 40 * k" using assms(1)
      by auto
    have k1: "1 \<le> k" using assms(2) k
      by simp
    have Nk: "N = 3 * k" unfolding N_def Nof_def k
      by simp
    have hk: "h = 37 * k" unfolding h_def hof_def k
      by simp
    show "1 \<le> N" using Nk k1
      by simp
    show "N \<le> K" using Nk k
      by simp
    show "real N / real K = 3 / 40" using Nk k k1
      by simp
    show "0 < h" using hk k1
      by simp
  qed
  text \<open>Pointwise bound of the Andreief integrand (@{text "g_le"} and (6.9) with
    @{text "t_i = (y_i/K)^2"}).\<close>
  have pointwise: "\<And>y. (\<forall>i<h. 0 < y i) \<Longrightarrow>
      (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
        j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i <
        h. real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) * weight (y i))
        \<le> (real K ^ 4) ^ (h * (h - 1) div 2) * c0 ^ h * exp E * (\<Prod> i <
          h. (1 + y i) ^ 5 * exp (- y i / real K))"
  proof -
    fix y :: "nat \<Rightarrow> real" assume ypos: "\<forall>i<h. 0 < y i"
    have k0: "0 < real K" using assms(2)
      by simp
    define t where "t i = (y i / real K) ^ 2" for i
    define Q where "Q = (\<Prod> i < h. (1 + y i) ^ 5 * exp (- y i / real K))"
    have Q0: "0 \<le> Q" unfolding Q_def using ypos
      by (fastforce intro: prod_nonneg)
    have c00: "0 \<le> c0" unfolding c0_def
      by simp
    have R0: "0 \<le> (real K ^ 4) ^ (h * (h - 1) div 2) * c0 ^ h * exp E * Q" using Q0 c00
      by simp
    have hyt: "y i ^ 2 = real K ^ 2 * t i" for i unfolding t_def using k0
      by (simp add: power_divide)
    have Dpos: "0 < real_eval (Dm m) (u ^ 2)" for m u
    proof -
      have D: "Dm m = sqPoleProd {1..m}"
        by (simp add: Dm_def sqPoleProd_def)
      show ?thesis unfolding D
        by (auto intro: real_eval_sqPoleProd_pos)
    qed
    have g0: "0 \<le> real_eval (Dm N) (u ^ 2) ^ 6 / real_eval (Dm K) (u ^ 2) * weight u"
      if "0 < u" for u
      using Dpos[of N u] Dpos[of K u] weight_pos[OF that]
      by (simp add: divide_nonneg_pos)
    show "(\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
      j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i <
      h. real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) * weight (y i))
        \<le> (real K ^ 4) ^ (h * (h - 1) div 2) * c0 ^ h * exp E * (\<Prod> i <
          h. (1 + y i) ^ 5 * exp (- y i / real K))"
    proof (cases "inj_on t {..<h}")
      case False
      obtain i j where ij: "i < h" "j < h" "t i = t j" "i \<noteq> j" using False
        unfolding inj_on_def
        by auto
      obtain a b where ab: "a < b" "b < h" "t a = t b"
      proof (cases "i < j")
        case True
        show ?thesis using that[of i j] True ij
          by simp
      next
        case False
        show ?thesis using that[of j i] False ij
          by simp
      qed
      have "(y a ^ 2 - y b ^ 2) ^ 2 = 0" using hyt[of a] hyt[of b] ab(3)
        by (simp add: hyt)
      hence "(\<Prod> j \<in> {j. a < j \<and> j < h}. (y a ^ 2 - y j ^ 2) ^ 2) = 0" using ab
        by (auto simp: prod_zero_iff)
      hence Z: "(\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
        j < h}. (y i ^ 2 - y j ^ 2) ^ 2) = 0" using ab
        by (auto simp: prod_zero_iff)
      show ?thesis unfolding Z using R0 unfolding Q_def
        by (simp add: zero_le_mult_iff)
    next
      case True
      define L where "L i j = ln \<bar>t i - t j\<bar>" for i j
      have hfac: "(y i ^ 2 - y j ^ 2) ^ 2 = real K ^ 4 * exp (2 * L i j)" if ij: "i < j" "j < h"
        for i j
      proof -
        have ne: "t i \<noteq> t j" using True ij unfolding inj_on_def
          by auto
        have l: "2 * ln \<bar>t i - t j\<bar> = ln (\<bar>t i - t j\<bar> ^ 2)"
          using ln_realpow[of "\<bar>t i - t j\<bar>" 2]
          by simp
        have e: "exp (2 * L i j) = (t i - t j) ^ 2" unfolding L_def l using ne
          by simp
        have d: "real K ^ 2 * t i - real K ^ 2 * t j = real K ^ 2 * (t i - t j)"
          by (simp add: algebra_simps)
        show ?thesis unfolding e hyt d
          by (simp add: power_mult_distrib)
      qed
      have card: "(\<Sum> i<h. card {j. i < j \<and> j < h}) = h * (h - 1) div 2"
      proof -
        have c1: "card {j. i < j \<and> j < h} = h - Suc i" for i
        proof -
          have "{j. i < j \<and> j < h} = {Suc i..<h}"
            by auto
          thus ?thesis
            by simp
        qed
        have "(\<Sum> i<h. card {j. i < j \<and> j < h}) = (\<Sum> i<h. h - Suc i)" unfolding c1 ..
        also have "\<dots> = (\<Sum> i<h. i)" using sum.nat_diff_reindex[of "\<lambda>i. i" h]
          by simp
        also have "\<dots> = h * (h - 1) div 2"
          by (simp add: Sum_Ico_nat atLeast0LessThan[symmetric])
        finally show ?thesis .
      qed
      have hV: "(\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
        j < h}. (y i ^ 2 - y j ^ 2) ^ 2) = (real K ^ 4) ^ (h * (h - 1) div 2) * exp (2 * (\<Sum> i <
        h. \<Sum> j \<in> {j. i < j \<and> j < h}. L i j))"
      proof -
        have "(\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
          j < h}. (y i ^ 2 - y j ^ 2) ^ 2) = (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
          j < h}. real K ^ 4 * exp (2 * L i j))"
          using hfac
          by simp
        also have "\<dots> = (\<Prod> i < h. (real K ^ 4) ^ card {j. i < j \<and>
          j < h} * exp (2 * (\<Sum> j \<in> {j. i < j \<and> j < h}. L i j)))"
          by (simp add: prod.distrib exp_sum sum_distrib_left)
        also have "\<dots> = (real K ^ 4) ^ (\<Sum> i<h. card {j. i < j \<and>
          j < h}) * exp (2 * (\<Sum> i < h. \<Sum> j \<in> {j. i < j \<and> j < h}. L i j))"
          by (simp add: power_sum exp_sum sum_distrib_left)
        finally show ?thesis unfolding card .
      qed
      have hG: "(\<Prod> i < h. real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) *
        weight (y i)) \<le> (\<Prod> i < h. c0 * ((1 + y i) ^ 5 * exp (- real K * Vf (t i))))"
      proof (rule prod_mono)
        fix i assume "i \<in> {..<h}"
        hence yi: "0 < y i" using ypos
          by simp
        show "0 \<le> real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) *
          weight (y i) \<and> real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) *
          weight (y i) \<le> c0 * ((1 + y i) ^ 5 * exp (- real K * Vf (t i)))"
          using g0[OF yi] g_le[OF hN(1,2,3) yi] unfolding t_def c0_def by simp
      qed
      have hG': "(\<Prod> i < h. c0 * ((1 + y i) ^ 5 * exp (- real K * Vf (t i)))) =
        c0 ^ h * (\<Prod> i < h. (1 + y i) ^ 5) * exp (- real K * (\<Sum> i < h. Vf (t i)))"
        by (simp add: prod.distrib exp_sum sum_distrib_left)
      have sq: "sqrt (t i) = y i / real K" if "i < h" for i unfolding t_def using ypos that k0
        by auto
      have tnn: "0 \<le> t i" for i unfolding t_def
        by simp
      have hc0: "2 * (\<Sum> i < h. \<Sum> j \<in> {j. i < j \<and>
        j < h}. L i j) - real K * (\<Sum> i < h. Vf (t i)) + (\<Sum> i < h. sqrt (t i)) \<le> E"
        using configuration_bound[OF assms(1,2), of t] unfolding h_def[symmetric] E_def L_def
          using True tnn
        by simp
      have ss: "(\<Sum> i < h. sqrt (t i)) = (\<Sum> i < h. y i / real K)" using sq
        by simp
      have "2 * (\<Sum> i < h. \<Sum> j \<in> {j. i < j \<and>
        j < h}. L i j) - real K * (\<Sum> i < h. Vf (t i)) + (\<Sum> i < h. y i / real K) \<le> E"
        using hc0 ss
        by simp
      hence hexp: "exp (2 * (\<Sum> i < h. \<Sum> j \<in> {j. i < j \<and>
        j < h}. L i j)) * exp (- real K * (\<Sum> i < h. Vf (t i))) \<le> exp E * exp (- (\<Sum> i <
        h. y i / real K))"
        unfolding mult_exp_exp by simp
      have ex: "exp (- (\<Sum> i < h. y i / real K)) = (\<Prod> i < h. exp (- y i / real K))"
        by (simp add: exp_sum[symmetric] sum_negf[symmetric])
      have Qe: "Q = (\<Prod> i < h. (1 + y i) ^ 5) * exp (- (\<Sum> i < h. y i / real K))"
        unfolding Q_def ex
        by (simp add: prod.distrib)
      have pp: "0 \<le> (\<Prod> i < h. (1 + y i) ^ 5)" using ypos
        by (force intro: prod_nonneg)
      have Vn: "0 \<le> (real K ^ 4) ^ (h * (h - 1) div 2) * exp (2 * (\<Sum> i < h. \<Sum> j \<in>
        {j. i < j \<and> j < h}. L i j))"
        by simp
      have P0: "0 \<le> (real K ^ 4) ^ (h * (h - 1) div 2) * c0 ^ h * (\<Prod> i <
        h. (1 + y i) ^ 5)" using c00 pp
        by simp
      have "(\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
        j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i <
        h. real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) * weight (y i)) =
        (real K ^ 4) ^ (h * (h - 1) div 2) * exp (2 * (\<Sum> i < h. \<Sum> j \<in> {j. i < j \<and>
        j < h}. L i j)) * (\<Prod> i < h. real_eval (Dm N) (y i ^ 2) ^ 6 /
        real_eval (Dm K) (y i ^ 2) * weight (y i))"
        unfolding hV ..
      also have "\<dots> \<le> (real K ^ 4) ^ (h * (h - 1) div 2) * exp (2 * (\<Sum> i <
        h. \<Sum> j \<in> {j. i < j \<and>
        j < h}. L i j)) * (c0 ^ h * (\<Prod> i < h. (1 + y i) ^ 5) * exp (- real K * (\<Sum> i <
        h. Vf (t i))))"
        using mult_left_mono[OF hG[unfolded hG'] Vn] by simp
      also have "\<dots> = (real K ^ 4) ^ (h * (h - 1) div 2) * c0 ^ h * (\<Prod> i <
        h. (1 + y i) ^ 5) * (exp (2 * (\<Sum> i < h. \<Sum> j \<in> {j. i < j \<and>
        j < h}. L i j)) * exp (- real K * (\<Sum> i < h. Vf (t i))))"
        by (simp add: algebra_simps)
      also have "\<dots> \<le> (real K ^ 4) ^ (h * (h - 1) div 2) * c0 ^ h * (\<Prod> i <
        h. (1 + y i) ^ 5) * (exp E * exp (- (\<Sum> i < h. y i / real K)))"
        using hexp P0
        by (simp add: mult_left_mono)
      also have "\<dots> = (real K ^ 4) ^ (h * (h - 1) div 2) * c0 ^ h * exp E * Q" unfolding Qe
        by (simp add: algebra_simps)
      finally show ?thesis unfolding Q_def .
    qed
  qed
  have phi_bound: "set_lebesgue_integral lborel {0<..} (\<lambda>y. (1 + y) ^ 5 * exp (- y /
    real K)) \<le> 3872 * real K ^ 6"
    using phi_aux(2)[of "real K"] assms(2) by simp
  have A: "real_eval (DeltaK K) zeta5 = 1 / fact h *
      set_lebesgue_integral (PiM {..<h} (\<lambda>_. lborel)) {y. \<forall>i<h. 0 < y i}
        (\<lambda>y. (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
          j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i <
          h. real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) * weight (y i)))"
    unfolding h_def N_def by (rule DeltaK_zeta5_integral[OF assms(1)])
  have B: "set_lebesgue_integral (PiM {..<h} (\<lambda>_. lborel)) {y. \<forall>i<h. 0 < y i}
        (\<lambda>y. (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
          j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i <
          h. real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) * weight (y i)))
        \<le> (real K ^ 4) ^ (h * (h - 1) div 2) * c0 ^ h * exp E * (3872 * real K ^ 6) ^ h"
  proof -
    define \<phi> :: "real \<Rightarrow> real" where "\<phi> y = (1 + y) ^ 5 * exp (- y / real K)"
      for y
    define \<psi> :: "real \<Rightarrow> real" where "\<psi> y = indicator {0<..} y * \<phi> y"
      for y
    define C :: real where "C = (real K ^ 4) ^ (h * (h - 1) div 2) * c0 ^ h * exp E"
    have c00: "0 \<le> c0" unfolding c0_def
      by simp
    have C0: "0 \<le> C" unfolding C_def using c00
      by simp
    have "set_integrable lborel {0<..} \<phi>" unfolding \<phi>_def
      using phi_aux(1)[of "real K"] assms(2)
      by simp
    hence psi_int: "integrable lborel \<psi>" unfolding set_integrable_def \<psi>_def
      by simp
    have psi_eq: "integral\<^sup>L lborel \<psi> = set_lebesgue_integral lborel {0<..} \<phi>"
      unfolding set_lebesgue_integral_def \<psi>_def
      by simp
    have psi_nn: "0 \<le> \<psi> y" for y unfolding \<psi>_def \<phi>_def
      by (simp add: indicator_def)
    have int_nn: "0 \<le> integral\<^sup>L lborel \<psi>" using psi_nn
      by (simp add: integral_nonneg)
    have int_le: "integral\<^sup>L lborel \<psi> \<le> 3872 * real K ^ 6"
      unfolding psi_eq \<phi>_def using phi_bound
      by simp
    interpret PS: product_sigma_finite "\<lambda>_::nat. lborel :: real measure"
      by (auto intro: product_sigma_finite.intro sigma_finite_lborel)
    have prodint: "integrable (PiM {..<h} (\<lambda>_. lborel)) (\<lambda>y. \<Prod> i<h. \<psi> (y
      i))" using psi_int PS.product_integrable_prod[of "{..<h}" "\<lambda>_. \<psi>"]
      by simp
    have prodeq: "integral\<^sup>L (PiM {..<h} (\<lambda>_. lborel)) (\<lambda>y. \<Prod> i<h.
      \<psi> (y i)) = integral\<^sup>L lborel \<psi> ^ h"
      using psi_int PS.product_integral_prod[of "{..<h}" "\<lambda>_. \<psi>"]
      by simp
    have intmaj: "integrable (PiM {..<h} (\<lambda>_. lborel)) (\<lambda>y. C *
      (\<Prod> i<h. \<psi> (y i)))" using prodint
      by simp
    have nn: "0 \<le> C * (\<Prod> i<h. \<psi> (y i))" for y using C0 psi_nn
      by (simp add: prod_nonneg)
    have maj: "indicator {y. \<forall>i<h. 0 < y i} y *\<^sub>R ((\<Prod> i < h. \<Prod> j \<in>
      {j. i < j \<and> j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i <
      h. real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) * weight (y i))) \<le>
      C * (\<Prod> i<h. \<psi> (y i))" for y
    proof (cases "\<forall>i<h. 0 < y i")
      case True
      have ps: "(\<Prod> i<h. \<psi> (y i)) = (\<Prod> i<h. (1 + y i) ^ 5 * exp (- y i / real K))"
        using True unfolding \<psi>_def \<phi>_def
        by simp
      show ?thesis unfolding ps C_def using pointwise[OF True] True
        by simp
    next
      case False
      show ?thesis using False nn[of y]
        by simp
    qed
    have "set_lebesgue_integral (PiM {..<h} (\<lambda>_. lborel)) {y. \<forall>i<h. 0 <
      y i} (\<lambda>y. ((\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
      j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i <
      h. real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) * weight (y i))))
        \<le> integral\<^sup>L (PiM {..<h} (\<lambda>_. lborel)) (\<lambda>y. C *
          (\<Prod> i<h. \<psi> (y i)))"
      unfolding set_lebesgue_integral_def using integral_mono'[OF intmaj maj nn]
      by simp
    also have "\<dots> = C * integral\<^sup>L lborel \<psi> ^ h" using prodeq
      by simp
    also have "\<dots> \<le> C * (3872 * real K ^ 6) ^ h" using int_nn int_le C0
      by (meson mult_left_mono power_mono)
    finally show ?thesis unfolding C_def .
  qed
  have pos: "0 < real_eval (DeltaK K) zeta5" by (rule Delta_zeta5_pos)
  have fact1: "1 / fact h \<le> (1 :: real)"
    by (simp add: divide_le_eq_1)
  define I where "I = set_lebesgue_integral (PiM {..<h} (\<lambda>_. lborel)) {y. \<forall>i<h. 0 <
    y i}
        (\<lambda>y. (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
          j < h}. (y i ^ 2 - y j ^ 2) ^ 2) * (\<Prod> i <
          h. real_eval (Dm N) (y i ^ 2) ^ 6 / real_eval (Dm K) (y i ^ 2) * weight (y i)))"
  define LK :: real where "LK = ln (real K)"
  define P where "P = h * (h - 1) div 2"
  define R where "R = (real K ^ 4) ^ P * c0 ^ h * exp E * (3872 * real K ^ 6) ^ h"
  have A': "real_eval (DeltaK K) zeta5 = 1 / fact h * I" using A unfolding I_def .
  have B': "I \<le> R" using B unfolding I_def R_def P_def .
  have K1: "1 \<le> real K" using assms(2)
    by simp
  have c0pos: "0 < c0" unfolding c0_def using K1
    by simp
  have I00: "0 < 1 / fact h * I" using pos unfolding A'
    by simp
  have I0: "0 < I" using zero_less_mult_pos[OF I00]
    by simp
  have DI: "1 / fact h * I \<le> I" using mult_right_mono[OF fact1, of I] I0
    by simp
  have lnR: "ln (real_eval (DeltaK K) zeta5) \<le> ln R" using A' DI B' pos
    by simp
  have lnR_eq: "ln R = real P * (4 * LK) + real h * ln c0 + E + real h * (ln 3872 + 6 * LK)"
    unfolding R_def LK_def using assms(2) c0pos
    by (simp add: ln_mult ln_realpow distrib_left)
  have p8192: "(8192 :: real) = 2 ^ 13"
    by simp
  have l8192: "ln (8192 :: real) = 13 * ln 2"
    unfolding p8192 ln_realpow by simp
  have lnc0: "ln c0 = 13 * ln 2 + 12 + real (12 * N + 12) * LK - real (2 * K) * LK"
    unfolding c0_def LK_def using assms(2) l8192
    by (simp add: ln_div ln_mult ln_realpow)
  have ev: "even (h * (h - 1))"
    by auto
  have "P * 2 = h * (h - 1)" unfolding P_def using ev
    by simp
  moreover have "real (h * (h - 1)) = real h * real h - real h" using hN(4)
    by (simp add: of_nat_diff algebra_simps)
  ultimately have hP: "real P * 2 = real h * real h - real h"
    by linarith
  have e4: "real P * (4 * LK) = 2 * (real h * real h - real h) * LK"
    by (simp add: hP[symmetric])
  have l2: "ln 2 < (1::real)"
    by (simp add: ln_2_less_1)
  have p4096: "(4096 :: real) = 2 ^ 12"
    by simp
  have "ln 3872 \<le> ln (4096::real)"
    by simp
  moreover have "ln (4096::real) = 12 * ln 2"
    unfolding p4096 ln_realpow by simp
  ultimately have l3872: "ln 3872 \<le> 12 * ln (2::real)"
    by simp
  have s2: "sqrt 2 \<le> (3 / 2 :: real)" using real_le_lsqrt[where x = 2 and y = "3 / 2"]
    by (simp add: power2_eq_square)
  have key: "(2 * real h * (real h + 6 * real N - real K) * LK + (lam_r * of_rat M0c -
    logEnergy rho) * real K ^ 2 + 18 * real h * LK + 160 * real h)
      - (real P * (4 * LK) + real h * ln c0 + E + real h * (ln 3872 + 6 * LK)) =
        real h * (28 - 13 * ln 2 - sqrt 2 - ln 3872)"
    unfolding e4 lnc0 E_def unfolding LK_def[symmetric]
    by (simp add: algebra_simps)
  have nonneg: "0 \<le> real h * (28 - 13 * ln 2 - sqrt 2 - ln 3872)" using l2 l3872 s2
    by simp
  have "ln (real_eval (DeltaK K) zeta5) \<le>
    2 * real h * (real h + 6 * real N - real K) * LK + (lam_r * of_rat M0c - logEnergy rho) *
    real K ^ 2 + 18 * real h * LK + 160 * real h"
    using lnR lnR_eq key nonneg
    by simp
  thus ?thesis unfolding h_def N_def LK_def .
qed

text \<open>(6.15): @{text "log S_K \<le>
  (2\<lambda> - 12\<alpha>\<lambda> - 2\<lambda>^2)K^2 log K + C*K^2 + 6h log K + 6h"}
  (factorial bounds; @{text "Stirling_Formula.ln_fact_bounds"} is available).\<close>
theorem log_SK_bound:
  assumes "40 dvd K" "0 < K"
  shows "ln (of_rat (SK K)) \<le>
           (2 * lam_r - 12 * alpha_r * lam_r - 2 * lam_r ^ 2) * real K ^ 2 * ln (real K)
           + Cstar * real K ^ 2 + 6 * real (hof K) * ln (real K) + 6 * real (hof K)"
proof -
  obtain n where K: "K = 40 * n" and n1: "1 \<le> n" using assms by (auto elim: dvdE)
  have hh: "hof K = 37 * n" and hN: "Nof K = 3 * n" unfolding K hof_def Nof_def by simp_all
  have ln_fact_le: "\<And>m. 1 \<le> m \<Longrightarrow>
    ln (fact m) \<le> real m * ln (real m) - real m + ln (real m) + 2"
  proof -
    fix m :: nat assume "1 \<le> m"
    thus "ln (fact m) \<le> real m * ln (real m) - real m + ln (real m) + 2"
    proof (induction m rule: nat_induct_at_least)
      case base
      show ?case
        by simp
    next
      case (Suc m)
      define A :: real where "A = ln (real m)"
      define B :: real where "B = ln (real (Suc m))"
      have m1: "1 \<le> real m" using Suc.hyps
        by simp
      have IH: "ln (fact m) \<le> real m * A - real m + A + 2" using Suc.IH unfolding A_def .
      have d1: "ln (real m / real (Suc m)) \<le> real m / real (Suc m) - 1"
        using m1 ln_le_minus_one[of "real m / real (Suc m)"]
        by simp
      have d2: "ln (real m / real (Suc m)) = A - B" using m1 unfolding A_def B_def
        by (simp add: ln_div)
      have d3: "real m / real (Suc m) - 1 = - 1 / real (Suc m)" using m1
        by (simp add: field_simps)
      have d4a: "A - B \<le> - 1 / real (Suc m)" using d1 d2 d3
        by simp
      have d4: "real (Suc m) * (A - B) \<le> - 1" using mult_left_mono[OF d4a, of "real (Suc m)"] m1
        by simp
      have f: "ln (fact (Suc m)) = B + ln (fact m)" unfolding B_def
        by (simp add: fact_Suc ln_mult)
      have e: "real (Suc m) * (A - B) = real m * A + A - real (Suc m) * B"
        by (simp add: algebra_simps)
      have s: "real (Suc m) = real m + 1"
        by simp
      have g: "ln (fact (Suc m)) \<le> real (Suc m) * B - real (Suc m) + B + 2" using e f d4 IH s
        by simp
      show ?case using g unfolding B_def .
    qed
  qed
  have le_ln_fact: "\<And>m. 1 \<le> m \<Longrightarrow>
    real m * ln (real m) - real m + 1 \<le> ln (fact m)"
  proof -
    fix m :: nat assume "1 \<le> m"
    thus "real m * ln (real m) - real m + 1 \<le> ln (fact m)"
    proof (induction m rule: nat_induct_at_least)
      case base
      show ?case
        by auto
    next
      case (Suc m)
      define A :: real where "A = ln (real m)"
      define B :: real where "B = ln (real (Suc m))"
      have m1: "1 \<le> real m" using Suc.hyps
        by simp
      have IH: "real m * A - real m + 1 \<le> ln (fact m)" using Suc.IH unfolding A_def .
      have d1: "ln (real (Suc m) / real m) \<le> real (Suc m) / real m - 1"
        using m1 ln_le_minus_one[of "real (Suc m) / real m"]
        by simp
      have d2: "ln (real (Suc m) / real m) = B - A" using m1 unfolding A_def B_def
        by (simp add: ln_div)
      have d3: "real (Suc m) / real m - 1 = 1 / real m" using m1
        by (simp add: field_simps)
      have d4a: "B - A \<le> 1 / real m" using d1 d2 d3
        by simp
      have d4: "real m * (B - A) \<le> 1" using mult_left_mono[OF d4a, of "real m"] m1
        by simp
      have f: "ln (fact (Suc m)) = B + ln (fact m)" unfolding B_def
        by (simp add: fact_Suc ln_mult)
      have e: "real (Suc m) * B - real (Suc m) + 1 = real m * (B - A) + real m * A + B - real m"
        by (simp add: algebra_simps)
      have g: "real (Suc m) * B - real (Suc m) + 1 \<le> ln (fact (Suc m))" using e f d4 IH
        by simp
      show ?case using g unfolding B_def .
    qed
  qed
  have sum_ln_fact_ge: "\<And>h. 1 \<le> h \<Longrightarrow>
    real h ^ 2 * ln (2 * real h) - 3 * real h ^ 2 / 2 - 2 * real h * ln (2 * real h) \<le>
    (\<Sum> i = 1..h - 1. ln (fact (2 * i)))"
  proof -
    fix h :: nat assume "1 \<le> h"
    thus "real h ^ 2 * ln (2 * real h) - 3 * real h ^ 2 / 2 - 2 * real h * ln (2 * real h) \<le>
      (\<Sum> i = 1..h - 1. ln (fact (2 * i)))"
    proof (induction h rule: nat_induct_at_least)
      case base
      have l2: "0 \<le> ln (2::real)"
        by simp
      have b1: "(real 1)\<^sup>2 * ln (2 * real 1) - 3 * (real 1)\<^sup>2 / 2 - 2 * real 1 * ln (2 *
        real 1) = - ln (2::real) - 3 / 2"
        by simp
      have b2: "(\<Sum> i = 1..1 - 1. ln (fact (2 * i))) = (0::real)" by simp
      show ?case unfolding b1 b2 using l2 by linarith
    next
      case (Suc h)
      define A :: real where "A = ln (2 * real h)"
      define B :: real where "B = ln (2 * real (Suc h))"
      have h1: "1 \<le> real h" using Suc.hyps
        by simp
      have IH: "real h ^ 2 * A - 3 * real h ^ 2 / 2 - 2 * real h * A \<le> (\<Sum> i =
        1..h - 1. ln (fact (2 * i)))"
        using Suc.IH unfolding A_def .
      have hf: "2 * real h * A - 2 * real h + 1 \<le> ln (fact (2 * h))"
        using le_ln_fact[of "2 * h"] Suc.hyps unfolding A_def
        by simp
      have d1: "ln ((2 * real (Suc h)) / (2 * real h)) \<le> (2 * real (Suc h)) / (2 * real h) - 1"
        using h1 ln_le_minus_one[of "(2 * real (Suc h)) / (2 * real h)"] by simp
      have d2: "ln ((2 * real (Suc h)) / (2 * real h)) = B - A" using h1 unfolding A_def B_def
        by (simp add: ln_div)
      have d3: "(2 * real (Suc h)) / (2 * real h) - 1 = 1 / real h" using h1
        by (simp add: field_simps)
      have d4a: "B - A \<le> 1 / real h" using d1 d2 d3
        by simp
      have d4: "real h * (B - A) \<le> 1" using mult_left_mono[OF d4a, of "real h"] h1
        by simp
      have d6: "0 \<le> B" unfolding B_def
        by simp
      have hh: "real h * (real h * (B - A)) \<le> real h" using d4 h1
        by (simp add: mult_left_mono)
      obtain k where k: "h = Suc k" using not0_implies_Suc[of h] Suc.hyps
        by auto
      have split: "(\<Sum> i = 1..Suc h - 1. ln (fact (2 * i))) = (\<Sum> i =
        1..h - 1. ln (fact (2 * i))) + ln (fact (2 * h))"
        unfolding k
        by simp
      have e: "real (Suc h) ^ 2 * B - 3 * real (Suc h) ^ 2 / 2 - 2 * real (Suc h) * B
          = real h * (real h * (B - A)) + real h ^ 2 * A - B - 3 * real h ^ 2 / 2 - 3 * real h - 3 /
            2"
        by (simp add: algebra_simps power2_eq_square)
      have g: "real (Suc h) ^ 2 * B - 3 * real (Suc h) ^ 2 / 2 - 2 * real (Suc h) * B \<le>
        (\<Sum> i = 1..Suc h - 1. ln (fact (2 * i)))"
        unfolding e split
      proof -
        show "real h * (real h * (B - A)) + real h ^ 2 * A - B - 3 * real h ^ 2 / 2 - 3 * real h -
          3 / 2 \<le> (\<Sum> i = 1..h - 1. ln (fact (2 * i))) + ln (fact (2 * h))"
          using IH hf hh d6 by simp
      qed
      show ?case using g unfolding B_def .
    qed
  qed
  have SK: "ln (of_rat (SK K)) = 2 * real (hof K) * ln (fact K) + real (hof K - 1) * ln 4 - 12 *
    real (hof K) * ln (fact (Nof K)) - 2 * (\<Sum> i = 1..hof K - 1. ln (fact (2 * i)))"
  proof -
    have fr: "(of_rat (fact m) :: real) = fact m" for m using of_rat_of_nat_eq[of "fact m"] by simp
    have q: "(of_rat (SK K) :: real) = (fact K ^ (2 * hof K) * 4 ^ (hof K - 1)) /
      (fact (Nof K) ^ (12 * hof K) * (\<Prod> i = 1..hof K - 1. fact (2 * i) ^ 2))"
      unfolding SK_def by (simp add: of_rat_divide of_rat_mult of_rat_power of_rat_prod fr)
    have pos: "0 < (\<Prod> i = 1..hof K - 1. (fact (2 * i) :: real) ^ 2)" by (simp add: prod_pos)
    have "ln (of_rat (SK K)) = ln ((fact K :: real) ^ (2 * hof K)) + ln ((4 :: real) ^ (hof K -
      1)) - ln ((fact (Nof K) :: real) ^ (12 * hof K)) - ln (\<Prod> i =
      1..hof K - 1. (fact (2 * i) :: real) ^ 2)"
      unfolding q using pos by (simp add: ln_div ln_mult)
    also have "ln (\<Prod> i = 1..hof K - 1. (fact (2 * i) :: real) ^ 2) = 2 * (\<Sum> i =
      1..hof K - 1. ln (fact (2 * i)))"
      by (simp add: ln_prod ln_realpow sum_distrib_left)
    finally show ?thesis by (simp add: ln_realpow)
  qed
  define x :: real where "x = real n"
  define L :: real where "L = ln (40 * x)"
  define F40 :: real where "F40 = ln (fact (40 * n))"
  define F3 :: real where "F3 = ln (fact (3 * n))"
  define S :: real where "S = (\<Sum> i = 1..37 * n - 1. ln (fact (2 * i)))"
  define a :: real where "a = ln (3 / 40)"
  define b :: real where "b = ln (37 / 20)"
  define l4 :: real where "l4 = ln 4"
  have x1: "1 \<le> x" using n1 unfolding x_def by simp
  have eN: "ln (3 * x) = a + L" using x1 ln_mult_pos[of "3 / 40" "40 * x"] unfolding a_def L_def
    by simp
  have eh: "ln (2 * (37 * x)) = b + L" using x1 ln_mult_pos[of "37 / 20" "40 * x"]
    unfolding b_def L_def by simp
  have hA: "F40 \<le> 40 * x * L - 40 * x + L + 2" using ln_fact_le[of "40 * n"] n1
    unfolding F40_def L_def x_def by simp
  have hB: "3 * x * (a + L) - 3 * x + 1 \<le> F3" using le_ln_fact[of "3 * n"] n1 eN
    unfolding F3_def x_def by simp
  have hC: "(37 * x) ^ 2 * (b + L) - 3 * (37 * x) ^ 2 / 2 - 2 * (37 * x) * (b + L) \<le> S"
    using sum_ln_fact_ge[of "37 * n"] n1 eh unfolding S_def x_def L_def by simp
  have l4u: "l4 \<le> 3" using ln_le_minus_one[of "4 :: real"] unfolding l4_def by simp
  have l4l: "0 \<le> l4" unfolding l4_def by simp
  have bu: "b \<le> 1" using ln_le_minus_one[of "37 / 20 :: real"] unfolding b_def by simp
  have ca: "Cstar = - 2 * (37 / 40) + 12 * (3 / 40) * (37 / 40) * (1 - a) + 3 * (37 / 40) ^ 2 - 2 *
    (37 / 40) ^ 2 * b"
    unfolding Cstar_def lam_r_def alpha_r_def a_def b_def by simp
  have key: "((2 * lam_r - 12 * alpha_r * lam_r - 2 * lam_r ^ 2) * (40 * x) ^ 2 * L + Cstar * (40 *
    x) ^ 2 + 6 * (37 * x) * L + 6 * (37 * x))
       - (2 * (37 * x) * F40 + (37 * x - 1) * l4 - 12 * (37 * x) * F3 - 2 * S)
       = 74 * x * (40 * x * L - 40 * x + L + 2 - F40) + 444 * x * (F3 - (3 * x * (a + L) - 3 * x +
         1))
         + 2 * (S - ((37 * x) ^ 2 * (b + L) - 3 * (37 * x) ^ 2 / 2 - 2 * (37 * x) * (b + L))) + (x *
           (518 - 37 * l4 - 148 * b) + l4)"
    unfolding ca lam_r_def alpha_r_def by (simp add: field_simps power2_eq_square)
  have nn1: "0 \<le> 74 * x * (40 * x * L - 40 * x + L + 2 - F40)" using hA x1 by simp
  have nn2: "0 \<le> 444 * x * (F3 - (3 * x * (a + L) - 3 * x + 1))" using hB x1 by simp
  have nn3: "0 \<le> x * (518 - 37 * l4 - 148 * b)" using l4l l4u bu x1 by simp
  have main: "2 * (37 * x) * F40 + (37 * x - 1) * l4 - 12 * (37 * x) * F3 - 2 * S \<le>
      (2 * lam_r - 12 * alpha_r * lam_r - 2 * lam_r ^ 2) * (40 * x) ^ 2 * L + Cstar * (40 * x) ^ 2 +
        6 * (37 * x) * L + 6 * (37 * x)"
    using key nn1 nn2 nn3 hC l4l by simp
  have sub: "real (37 * n - 1) = 37 * x - 1"
    using n1 unfolding x_def by simp
  show ?thesis
    unfolding SK unfolding hh hN unfolding K
    using main sub by (simp add: x_def L_def F40_def F3_def S_def l4_def)
qed

text \<open>Proposition 6.3 is at the end of this theory (it needs (6.4) from Appendix A).\<close>

lemma real_eval_FK_eq: "real_eval (FK K) zeta5 = of_rat (SK K) * real_eval (DeltaK K) zeta5"
  by (simp add: FK_def real_eval_def map_poly_smult of_rat_mult)

text \<open>Proposition 6.3: @{text "0 < F_K(\<zeta>(5))"} and
  @{text "log F_K(\<zeta>(5)) \<le> UbarK^2 + 24K log K + 200K"}.
  (Needs (6.4) from Appendix A, which is therefore imported.)\<close>
theorem log_FK_zeta5_bound:
  assumes "40 dvd K" "0 < K"
  shows "0 < real_eval (FK K) zeta5 \<and>
         ln (real_eval (FK K) zeta5) \<le>
           of_rat Ubar * real K ^ 2 + 24 * real K * ln (real K) + 200 * real K"
proof -
  have S0: "0 < (of_rat (SK K) :: real)" using SK_pos[of K] by simp
  have D0: "0 < real_eval (DeltaK K) zeta5" by (rule Delta_zeta5_pos)
  have pos: "0 < real_eval (FK K) zeta5" unfolding real_eval_FK_eq using S0 D0 by simp
  obtain k where k: "K = 40 * k" using assms(1) by (elim dvdE)
  have hk: "real (hof K) = 37 * real k" and Nk: "real (Nof K) = 3 * real k" and Kk: "real K =
    40 * real k"
    unfolding k hof_def Nof_def by simp_all
  define LK where "LK = ln (real K)"
  have LK0: "0 \<le> LK" using assms(2) by (simp add: LK_def)
  have hK: "real (hof K) \<le> real K" using hk Kk by simp
  define A where "A = 2 * real (hof K) * (real (hof K) + 6 * real (Nof K) - real K) * LK"
  define B where "B = (2 * lam_r - 12 * alpha_r * lam_r - 2 * lam_r ^ 2) * real K ^ 2 * LK"
  have AB: "A + B = 0" unfolding A_def B_def hk Nk Kk
    by (simp add: lam_r_def alpha_r_def power2_eq_square algebra_simps)
  have L: "ln (real_eval (FK K) zeta5) = ln (of_rat (SK K)) + ln (real_eval (DeltaK K) zeta5)"
    unfolding real_eval_FK_eq using S0 D0 by (simp add: ln_mult)
  have "ln (real_eval (FK K) zeta5)
      \<le> (A + (lam_r * of_rat M0c - logEnergy rho) * real K ^ 2 + 18 * real (hof K) * LK + 160 *
        real (hof K))
        + (B + Cstar * real K ^ 2 + 6 * real (hof K) * LK + 6 * real (hof K))"
    unfolding L A_def B_def LK_def using log_DeltaK_zeta5_bound[OF assms] log_SK_bound[OF assms]
      by linarith
  also have "\<dots> = (A + B) + (lam_r * of_rat M0c - logEnergy rho + Cstar) * real K ^ 2
                  + 24 * (real (hof K) * LK) + 166 * real (hof K)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> of_rat Ubar * real K ^ 2 + 24 * (real K * LK) + 200 * real K"
  proof -
    have e: "(lam_r * of_rat M0c - logEnergy rho + Cstar) * real K ^ 2 \<le>
      of_rat Ubar * real K ^ 2"
      by (rule mult_right_mono[OF rho_energy_bound]) simp
    have l: "real (hof K) * LK \<le> real K * LK" by (rule mult_right_mono[OF hK LK0])
    have h: "166 * real (hof K) \<le> 200 * real K" using hK by simp
    show ?thesis unfolding AB using e l h by linarith
  qed
  finally show ?thesis using pos by (simp add: LK_def mult.assoc)
qed

end



