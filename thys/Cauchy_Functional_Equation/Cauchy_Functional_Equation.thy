(*  Title:   Cauchy_Functional_Equation.thy
    Author:  Michikazu Hirata
*)

theory Cauchy_Functional_Equation
imports
   "HOL-Probability.Probability"
   "Riesz_Representation.Regular_Measure"
begin

section \<open>Cauchy's Functional Equation\<close>
subsection \<open> Case: $h$ is Continuous\<close>
text \<open>The proof of the following lemma is based on
      \<^url>\<open>https://en.wikipedia.org/wiki/Cauchy%27s_functional_equation\<close>,
     accessed 17 January 2026.\<close>
lemma Cauchy_equation_Q_linear:
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and q:"q \<in> \<rat>"
  shows "h (q * v) = q * h v"
proof -
  have h0:"h 0 = 0"
    using h_eq[of 0 0] by simp
  have h_neq:"h (- x) = - h x" for x
    using h_eq[of x "- x"] by (simp add: add_eq_0_iff2 h0)
  have N:"h (of_nat n * r) = of_nat n * h r" for n r
    by(induction n) (auto simp add: h0 mult.commute h_eq distrib_left)
  have Z:"h (of_int i * r) = of_int i * h r" for i r
    by(rule int_cases2[of i])
      (use N h_neq  mult_minus_right[of "h r" "of_nat _"]
           of_int_minus[of "int _"] of_int_of_nat_eq in auto)
  have N_inverse:"h (r / of_nat n) = h r / of_nat n" for r n
    by (metis eq_divide_eq h0 mult.commute N)
  obtain n m where nm: "q = of_int m / of_nat n"
    by (metis Rats_cases' q less_le of_nat_nat)
  show "h (q * v) = q * h v"
    by(simp add: nm N_inverse Z)
qed

lemma Cauchy_equation_isCont_continuous:
  fixes h :: "'a :: real_normed_vector \<Rightarrow> 'b :: real_normed_vector"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and h_Cont:"isCont h x"
  shows "continuous_on UNIV h"
proof(safe intro!: continuous_at_imp_continuous_on)
  have h0:"h 0 = 0"
    using h_eq[of 0 0] by simp
  have h_neg:"h (- x) = - h x" for x
    using h_eq[of x "- x"] by (simp add: add_eq_0_iff2 h0)
  have eq:"h (y + e) - h y = h e" for y e
    using h_eq[of "y + e" "- y"] by(auto simp:  h_neg[symmetric])
  fix y :: 'a
  show "isCont h y"
    using h_Cont
    by(simp add: eq Lim_null[where l="h y"] Lim_null[where l="h x"] isCont_iff)
qed

lemma Cauchy_equation_continuous':
  fixes h :: "_ :: field_char_0 \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and h_Cont:"continuous_on UNIV h"
  shows "h = (\<lambda>x. x * h 1)"
proof
  fix x :: real
  have q_eq:"q \<in> \<rat> \<Longrightarrow> h q = q * h 1" for q
    using Cauchy_equation_Q_linear[of h q 1] h_eq by simp
  have "\<exists>q\<in>\<rat>. x < q \<and> q < x + 1 / (1 + real n)" for n
    using Rats_dense_in_real[of x "x + 1 / (1 + real n)"] by fastforce
  then obtain qn where
    qn:"\<And>n. qn n \<in> \<rat>" "\<And>n. x < qn n" "\<And>n. qn n < x + 1 / (1 + real n)"
    by metis
  have lim_qn:"qn \<longlonglongrightarrow> x"
    unfolding LIMSEQ_iff
  proof safe
    fix r :: real
    assume "0 < r"
    then obtain N where "1 / (1 + real N) < r"
      using nat_approx_posE by auto
    hence "1 / (1 + real n) < r" if n:"N \<le> n" for n
      using divide_mono[of "1 + real N" "1 + real n" 1 1] of_nat_mono[OF n] by simp
    thus "\<exists>no. \<forall>n\<ge>no. norm (qn n - x) < r"
      by(intro exI[where x=N]) (smt (verit, ccfv_SIG) qn real_norm_def)
  qed
  hence "(\<lambda>n. h (qn n)) \<longlonglongrightarrow> h x"
    using h_Cont by(auto simp: continuous_on_sequentially comp_def)
  moreover have "(\<lambda>n. qn n * h 1) \<longlonglongrightarrow> x * h 1"
    using lim_qn by(auto intro!: tendsto_mult_right)
  ultimately show "h x = x * h 1"
    using qn by(auto simp: q_eq[symmetric] intro!: tendsto_unique)
qed

corollary Cauchy_equation_continuous:
  fixes h :: "_ :: field_char_0 \<Rightarrow> real"
  assumes "\<And>x y. h (x + y) = h x + h y"
    and "continuous_on UNIV h"
  shows "\<exists>c. h = (\<lambda>x. x * c)"
  using assms Cauchy_equation_continuous' by blast

corollary
  fixes h :: "_ :: field_char_0 \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and "isCont h a"
  shows Cauchy_equation_continuous_at': "h = (\<lambda>x. x * h 1)"
    and Cauchy_equation_continuous_at: "\<exists>c. h = (\<lambda>x. x * c)"
  using Cauchy_equation_continuous Cauchy_equation_continuous' assms
    Cauchy_equation_isCont_continuous by blast+


subsection \<open> Case: $h$ is Monotone\<close>

lemma Cauchy_bounded_zero_imp_continuous_at_zero:
  fixes h :: "'a :: {linordered_field, linorder_topology} \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and ex:"\<exists>\<epsilon>>0. \<exists>M. \<forall>x. \<bar>x\<bar> < \<epsilon> \<longrightarrow> \<bar>h x\<bar> \<le> M"
  shows "isCont h 0"
proof -
  obtain \<epsilon> M where eps:"0 < \<epsilon>" and bound:"\<And>x. \<bar>x\<bar> < \<epsilon> \<Longrightarrow> \<bar>h x\<bar> \<le> M"
    using ex by blast
  have h0:"h 0 = 0"
    using h_eq[of 0 0] by simp
  have Nmul:"h (of_nat n * r) = of_nat n * h r" for n :: nat and r :: 'a
    by (induction n) (auto simp: h0 h_eq distrib_right)
  have M_nonneg:"0 \<le> M"
    using bound[of 0] eps by simp
  have delta_bound:"\<bar>h x\<bar> \<le> M / real n"
    if n:"1 \<le> n" and x:"\<bar>x\<bar> < \<epsilon> / of_nat n" for x :: 'a and n :: nat
  proof -
    have n_pos:"0 < (of_nat n :: 'a)" and n_pos':"0 < real n"
      using n by auto
    have abs_lt:"\<bar>of_nat n * x\<bar> < \<epsilon>"
      using mult_strict_left_mono[OF x n_pos] n_pos by (simp add: abs_mult)
    have "real n * \<bar>h x\<bar> \<le> M"
      using bound[OF abs_lt] by (simp add: Nmul abs_mult)
    thus ?thesis
      using n_pos' by (simp add: field_simps)
  qed
  have main:"\<exists>\<delta>>0. \<forall>x. \<bar>x\<bar> < \<delta> \<longrightarrow> \<bar>h x\<bar> < e" if e:"0 < e" for e :: real
  proof -
    obtain n0 where n0:"M / e < real n0"
      using reals_Archimedean2 by blast
    define n where "n = max n0 1"
    have n1:"1 \<le> n"
      by (simp add: n_def)
    have n:"M / e < real n"
      using n0 n1 by (simp add: n_def del: max.bounded_iff)
    have Me:"M / real n < e"
      using n n1 e M_nonneg by (simp add: field_simps)
    show ?thesis
    proof (intro exI[of _ "\<epsilon> / of_nat n"] conjI allI impI)
      show "0 < \<epsilon> / of_nat n"
        using eps n1 by simp
      fix x :: 'a
      assume x:"\<bar>x\<bar> < \<epsilon> / of_nat n"
      show "\<bar>h x\<bar> < e"
        using delta_bound[OF n1 x] Me by linarith
    qed
  qed
  have ev_right:"eventually (\<lambda>x. \<bar>h x\<bar> < e) (at_right 0)"
    and ev_left:"eventually (\<lambda>x. \<bar>h x\<bar> < e) (at_left 0)" if e:"0 < e" for e
  proof -
    obtain \<delta> where d:"0 < \<delta>" and d':"\<And>x. \<bar>x\<bar> < \<delta> \<Longrightarrow> \<bar>h x\<bar> < e"
      using main[OF e] by blast
    show "eventually (\<lambda>x. \<bar>h x\<bar> < e) (at_right 0)"
      unfolding eventually_at_right_field
      by (intro exI[of _ \<delta>] allI impI conjI d) (use d' in force)
    show "eventually (\<lambda>x. \<bar>h x\<bar> < e) (at_left 0)"
      unfolding eventually_at_left_field
      by (intro exI[of _ "- \<delta>"] allI impI conjI) (use d d' in force)+
  qed
  show ?thesis
    unfolding isCont_def tendsto_iff eventually_at_split
    using ev_right ev_left by (simp add: h0 dist_real_def)
qed

corollary
  fixes h :: "_ :: field_char_0 \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and ab:"a < b"
    and h_mono:"mono_on {a..b} h"
  shows Cauchy_equation_mono_on': "h = (\<lambda>x. x * h 1)"
    and Cauchy_equation_mono_on: "\<exists>c. h = (\<lambda>x. x * c)"
proof -
  have h0:"h 0 = 0"
    using h_eq[of 0 0] by simp
  have h_neg:"h (- x) = - h x" for x
    using h_eq[of x "- x"] by (simp add: add_eq_0_iff2 h0)
  have h_eq':"h (x - y) = h x - h y" for x y
    using h_eq[of x "- y"] by(auto simp: h_neg[symmetric])
  define m where "m = (a + b) / 2"
  have bound:"\<bar>h y\<bar> \<le> h b - h a" if y:"\<bar>y\<bar> < b - a" for y
  proof -
    define x where "x = y / 2"
    have mem:"m + x \<in> {a..b}" "m - x \<in> {a..b}"
      using y by (auto simp: m_def x_def abs_less_iff, argo+)
    have hb:"h a \<le> h (m + x)" "h (m + x) \<le> h b" "h a \<le> h (m - x)" "h (m - x) \<le> h b"
      using h_mono mem ab by (auto simp: mono_on_def)
    have "h y = h (m + x) - h (m - x)"
      using h_eq'[of "m + x" "m - x"] by (simp add: x_def)
    thus ?thesis
      using hb by linarith
  qed
  have ex:"\<exists>\<epsilon>>0. \<exists>M. \<forall>x. \<bar>x\<bar> < \<epsilon> \<longrightarrow> \<bar>h x\<bar> \<le> M"
    using ab bound by (intro exI[of _ "b - a"] exI[of _ "h b - h a"]) auto
  note isc = Cauchy_bounded_zero_imp_continuous_at_zero[OF h_eq ex]
  show "h = (\<lambda>x. x * h 1)"
    using Cauchy_equation_continuous_at'[OF h_eq isc] .
  thus "\<exists>c. h = (\<lambda>x. x * c)"
    by blast
qed

corollary
  fixes h :: "_ :: field_char_0 \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and h_mono:"mono h"
  shows Cauchy_equation_mono': "h = (\<lambda>x. x * h 1)"
    and Cauchy_equation_mono: "\<exists>c. h = (\<lambda>x. x * c)"
  using Cauchy_equation_mono_on'[of h,OF h_eq _ mono_on_subset[OF h_mono]]
  by auto

corollary
  fixes h :: "_ :: field_char_0 \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and ab:"a < b"
    and h_mono:"antimono_on {a..b} h"
  shows Cauchy_equation_antimono_on': "h = (\<lambda>x. x * h 1)"
    and Cauchy_equation_antimono_on: "\<exists>c. h = (\<lambda>x. x * c)"
proof -
  have h_eq2:"\<And>x y. (- h) (x + y) = (- h) x + (- h) y"
    using h_eq by simp
  have h_mono2:"mono_on {a..b} (- h)"
    using h_mono by (auto simp: monotone_on_def)
  show "h = (\<lambda>x. x * h 1)"
  proof
    fix x
    show "h x = x * h 1"
      using fun_cong[OF Cauchy_equation_mono_on'[OF h_eq2 ab h_mono2], of x] by simp
  qed
  thus "\<exists>c. h = (\<lambda>x. x * c)"
    by blast
qed

subsection \<open> Case: $h$ is Bounded\<close>

corollary
  fixes h :: "_ :: field_char_0 \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and ab:"a < b"
    and h_bdd_above:"\<exists>M. \<forall>x\<in>{a..b}. h x \<le> M"
  shows Cauchy_equation_bounded_above_on': "h = (\<lambda>x. x * h 1)"
    and Cauchy_equation_bounded_above_on: "\<exists>c. h = (\<lambda>x. x * c)"
proof -
  have h0:"h 0 = 0"
    using h_eq[of 0 0] by simp
  have h_neg:"h (- x) = - h x" for x
    using h_eq[of x "- x"] by (simp add: add_eq_0_iff2 h0)
  have h_eq':"h (x - y) = h x - h y" for x y
    using h_eq[of x "- y"] by(auto simp: h_neg[symmetric])
  obtain M where M:"\<And>x. x \<in> {a..b} \<Longrightarrow> h x \<le> M"
    using h_bdd_above by blast
  define L where "L = b - a"
  define M' where "M' = M - h a"
  have L_pos:"0 < L"
    using ab by (simp add: L_def)
  have M'_bound:"h x \<le> M'" if x:"x \<in> {0..L}" for x
    using M[of "x + a"] h_eq[of x a] x by (simp add: L_def M'_def)
  have bound_abs:"\<bar>h x\<bar> \<le> M' + \<bar>h L\<bar>" if x:"x \<in> {0..L}" for x
  proof -
    have "h L - h x \<le> M'"
      using M'_bound[of "L - x"] h_eq'[of L x] x by simp
    thus ?thesis
      using M'_bound[OF x] by linarith
  qed
  have near_0:"\<bar>h x\<bar> \<le> M' + \<bar>h L\<bar>" if xL:"\<bar>x\<bar> < L" for x
    using bound_abs[of x] xL h_neg[of x] bound_abs[of "- x"]
    by (cases "0 \<le> x") auto 
  have ex:"\<exists>\<epsilon>>0. \<exists>M. \<forall>x. \<bar>x\<bar> < \<epsilon> \<longrightarrow> \<bar>h x\<bar> \<le> M"
    using L_pos near_0 by blast
  note isc = Cauchy_bounded_zero_imp_continuous_at_zero[OF h_eq ex]
  show "h = (\<lambda>x. x * h 1)"
    using Cauchy_equation_continuous_at'[OF h_eq isc] .
  thus "\<exists>c. h = (\<lambda>x. x * c)"
    by blast
qed

corollary
  fixes h :: "_ :: field_char_0 \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and ab:"a < b"
    and h_bdd_below:"\<exists>M. \<forall>x\<in>{a..b}. M \<le> h x"
  shows Cauchy_equation_bounded_below_on': "h = (\<lambda>x. x * h 1)"
    and Cauchy_equation_bounded_below_on: "\<exists>c. h = (\<lambda>x. x * c)"
proof -
  have h_eq2:"\<And>x y. (- h) (x + y) = (- h) x + (- h) y"
    using h_eq by simp
  obtain M where M:"\<And>x. x \<in> {a..b} \<Longrightarrow> M \<le> h x"
    using h_bdd_below by blast
  have h_bdd_above2:"\<exists>M. \<forall>x\<in>{a..b}. (- h) x \<le> M"
    using M by (intro exI[of _ "- M"]) simp
  show "h = (\<lambda>x. x * h 1)"
  proof
    fix x
    show "h x = x * h 1"
      using fun_cong[OF Cauchy_equation_bounded_above_on'[OF h_eq2 ab h_bdd_above2], of x]
      by simp
  qed
  thus "\<exists>c. h = (\<lambda>x. x * c)"
    by blast
qed

corollary
  fixes h :: "_ :: field_char_0 \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and ab:"a < b"
    and h_bdd:"\<exists>M. \<forall>x\<in>{a..b}. \<bar>h x\<bar> \<le> M"
  shows Cauchy_equation_bounded_on': "h = (\<lambda>x. x * h 1)"
    and Cauchy_equation_bounded_on: "\<exists>c. h = (\<lambda>x. x * c)"
proof -
  have h_bdd_above:"\<exists>M. \<forall>x\<in>{a..b}. h x \<le> M"
    using h_bdd abs_le_D1 by blast
  show "h = (\<lambda>x. x * h 1)"
    using Cauchy_equation_bounded_above_on'[OF h_eq ab h_bdd_above] .
  thus "\<exists>c. h = (\<lambda>x. x * c)"
    by blast
qed

subsection \<open> Case: $h$ is Measurable\<close>

subsubsection \<open> Lemmas for Regularity of Measures (to be moved)\<close>
(* To be moved to Riesz_Representation.Regular_Measure *)
lemma lborel_inner_regular:
  assumes A[measurable]:"A \<in> sets borel" and A_bdd:"bounded A"
  shows "measure lborel A = (\<Squnion>K\<in>{K. compact K \<and> K \<subseteq> A}. measure lborel K)"
proof -
  obtain a where a:"A \<subseteq> cball 0 a"
    by (meson A_bdd bounded_subset_cball cball_subset_cball_iff order.trans
        order_refl)
  interpret finite_measure "restrict_space lborel (cball 0 a)"
    using emeasure_lborel_cball_finite less_top
    by(fastforce intro!: finite_measureI simp: emeasure_restrict_space)
  let ?X = "subtopology euclidean (cball 0 a)"
  have "measure lborel A = measure (restrict_space lborel (cball 0 a)) A"
    using a by(simp add: measure_restrict_space)
  also have "...
     = (\<Squnion> (measure (restrict_space lborel (cball 0 a)) ` {K. compactin ?X K \<and> K \<subseteq> A}))"
    using a by(intro inner_regular_Polish Polish_space_closedin)
              (auto simp: borel_of_subtopology borel_of_euclidean sets_restrict_space)
  also have "... = (\<Squnion>K\<in>{K. compact K \<and> K \<subseteq> A}. measure lborel K)"
    using a by(auto intro!: Sup.SUP_cong simp: compactin_subtopology measure_restrict_space)
  finally show ?thesis .
qed

corollary lborel_inner_regular_eps:
  assumes A[measurable]:"A \<in> sets borel" and A_bdd:"bounded A"
    and e:"0 < e"
  obtains K where "K \<subseteq> A" "compact K" "measure lborel A < measure lborel K + e"
proof -
  have *:"{K. compact K \<and> K \<subseteq> A} \<noteq> {}"
    by blast
  have **:"bdd_above (measure lborel ` {K. compact K \<and> K \<subseteq> A})"
    by(auto intro!: bdd_aboveI[where M="measure lborel A"] fmeasurableI
        measure_mono_fmeasurable borel_compact emeasure_bounded_finite A_bdd)
  have ***:"\<And>y. y < measure lborel A
             \<Longrightarrow> \<exists>i\<in>{K. compact K \<and> K \<subseteq> A}. y < measure lborel i"
    using lborel_inner_regular[OF A A_bdd] le_cSUP_iff[OF * **] by auto
  show ?thesis
    using that ***[of "measure lborel A - e"] e by force
qed

lemma lborel_outer_regular:
  assumes A[measurable]:"A \<in> sets borel" and A_bdd:"bounded A"
  shows "measure lborel A = (\<Sqinter> (measure lborel ` {C. open C \<and> A \<subseteq> C \<and> bounded C}))"
proof -
  obtain a' where a':"A \<subseteq> cball 0 a'"
    by (meson A_bdd bounded_subset_cball cball_subset_cball_iff order.trans
        order_refl)
  then obtain a where a:"a' < a"
    using gt_ex by blast
  hence A_subst_ball:"A \<subseteq> ball 0 a"
    using a' by fastforce
  interpret finite_measure "restrict_space lborel (ball 0 a)"
    using emeasure_lborel_ball_finite less_top
    by(fastforce intro!: finite_measureI simp: emeasure_restrict_space)
  let ?X = "subtopology euclidean (ball 0 a)"
  have "measure lborel A = measure (restrict_space lborel (ball 0 a)) A"
    using A_subst_ball by(simp add: measure_restrict_space)
  also have "...
    = (\<Sqinter> (measure (restrict_space lborel (ball 0 a))` {C. openin ?X C \<and> A \<subseteq> C}))"
    using A_subst_ball by(intro outer_regularD outer_regular' metrizable_space_subtopology)
      (auto simp: sets_restrict_space borel_of_subtopology borel_of_euclidean
        metrizable_space_euclidean)
  also have "... = (\<Sqinter> (measure lborel ` {C. open C \<and> A \<subseteq> C \<and> bounded C}))" (is "?lhs = ?rhs")
  proof(rule antisym)
    show "?lhs \<ge> ?rhs"
      using A_subst_ball 
      by(intro cInf_superset_mono)
        (auto simp: openin_open_eq[of "ball 0 a"] measure_restrict_space
          dest: bounded_subset_ballI)
  next
    show "?lhs \<le> ?rhs"
    proof(safe intro!: cInf_mono)
      fix U
      assume "open U" "A \<subseteq> U" "bounded U"
      thus "\<exists>a\<in>measure (restrict_space lborel (ball 0 a)) `
                  {C. openin (top_of_set (ball 0 a)) C \<and> A \<subseteq> C}.
              a \<le> Henstock_Kurzweil_Integration.content U"
        using A_subst_ball
        by(auto intro!: exI[where x="ball 0 a \<inter> U"] measure_mono_fmeasurable
             fmeasurableI emeasure_bounded_finite simp: measure_restrict_space)
    qed(use A_subst_ball in "auto intro!: bdd_belowI[where m=0]")
  qed
  finally show ?thesis .
qed

corollary lborel_outer_regular_eps:
  assumes A[measurable]:"A \<in> sets borel" and A_bdd:"bounded A"
    and e:"0 < e"
  obtains U where "A \<subseteq> U" "open U" "bounded U" "measure lborel U < measure lborel A + e"
proof -
  have *:"{C. open C \<and> A \<subseteq> C \<and> bounded C} \<noteq> {}"
    by (metis (no_types, lifting) open_ball bounded_ball A_bdd
        bounded_subset_ballD empty_iff mem_Collect_eq)
  have **:"bdd_below (measure lborel ` {C. open C \<and> A \<subseteq> C \<and> bounded C})"
    by fast
  have ***:"\<And>y. y > measure lborel A
             \<Longrightarrow> \<exists>i\<in>{C. open C \<and> A \<subseteq> C \<and> bounded C}. measure lborel i < y"
    using lborel_outer_regular[OF A A_bdd] cINF_le_iff[OF * **] by auto
  show ?thesis
    using that ***[of "measure lborel A + e"] e by auto
qed

subsubsection \<open>Steinhaus' Theorem\<close>
text \<open>The proof of the following lemma is based on
      \<^url>\<open>https://matthewhr.wordpress.com/2012/11/14/steinhauss-theorem/\<close>.\<close>
lemma weak_Steinhaus:
  fixes A :: "'a :: euclidean_space set"
  assumes [measurable]:"A \<in> sets borel"
    and meas:"0 < emeasure lborel A"
  shows "0 \<in> interior {a - a'|a a'. a \<in> A \<and> a' \<in> A}"
proof -
  have exr:"\<exists>r>0. \<forall>x\<in>K. ball x r \<subseteq> U"
    if K:"compact K" and UK:"K \<subseteq> U" and U:"open U" for U K :: "'a set"
    using Met_TC.lebesgue_number[of K "{U}"] that by auto
  have "\<exists>C'\<in>sets borel. bounded C' \<and> C' \<subseteq> C 
                       \<and> 0 < emeasure lborel C' \<and> emeasure lborel C' < \<top>"
    if C[measurable]:"C \<in> sets borel" "0 < emeasure lborel C" for C :: "'a set"
  proof -
    define Cn where "Cn \<equiv> (\<lambda>n. C \<inter> ball 0 (real n))"
    have [measurable]: "Cn n \<in> sets borel" for n
      by(simp add: Cn_def)
    have inc:"incseq Cn"
      by(auto simp: Cn_def intro!: monoI)
    have Cn_subst:"Cn n \<subseteq> C" for n
      by(simp add: Cn_def)
    have meas_fin:"emeasure lborel (Cn n) < \<top>" for n
      by (metis Cn_def bounded_Int bounded_ball emeasure_bounded_finite
          infinity_ennreal_def)
    have UnCn: "C = (\<Union> (range Cn))"
      using reals_Archimedean2[of "abs _"]
      by(fastforce simp: Cn_def abs_less_iff minus_less_iff)
    have bCn: "bounded (Cn n)" for n
      by(auto simp: Cn_def)
    have "\<exists>n. 0 < emeasure lborel (Cn n)"
    proof(rule ccontr)
      assume "\<nexists>n. 0 < emeasure lborel (Cn n)"
      then have emeasure0:"\<And>n. emeasure lborel (Cn n) = 0"
        by simp
      have "(\<lambda>n. emeasure lborel (Cn n)) \<longlonglongrightarrow> emeasure lborel C"
        by(auto intro!: Lim_emeasure_incseq inc simp: UnCn)
      thus False
        using C by(simp add: emeasure0 LIMSEQ_const_iff)
    qed
    then obtain n where "0 < emeasure lborel (Cn n)"
      by blast
    thus ?thesis
      using Cn_subst bCn meas_fin by(auto intro!: bexI[where x="Cn n"])
  qed
  then obtain A' where
    A'[measurable]: "A' \<in> sets borel" "bounded A'" "A' \<subseteq> A"
                    "0 < emeasure lborel A'" "emeasure lborel A' < \<top>"
    using assms by meson
  hence "0 < measure lborel A'"
    by (simp add: emeasure_eq_ennreal_measure)
  then obtain e where e:"0 < e" "e < measure lborel A' / 4"
    by (metis dense zero_less_divide_iff zero_less_numeral)
  then obtain U K where
    U[measurable]:"A' \<subseteq> U" "open U" "bounded U" "measure lborel U < measure lborel A' + e"
    and K:"K \<subseteq> A'" "compact K" "measure lborel A' < measure lborel K + e"
    using lborel_outer_regular_eps lborel_inner_regular_eps A' by meson
  hence meas_le:"measure lborel A' \<le> measure lborel U"
                "measure lborel K \<le> measure lborel A'"
    by(auto intro!: measure_mono_fmeasurable fmeasurableI borel_compact
        emeasure_bounded_finite A')
  have less_UK:"measure lborel U < 2 * measure lborel K"
  proof -
    have "measure lborel U / 2 \<le> measure lborel U - measure lborel A' / 2"
      using meas_le by simp
    also have "... < measure lborel U - 2 * e"
      using e by auto
    also have "... < measure lborel K"
      using U K by linarith
    finally show ?thesis
      by simp
  qed
  obtain r where r:"\<And>x. x \<in> K \<Longrightarrow> ball x r \<subseteq> U" and r_pos: "r > 0"
    using exr[of K U] U K by fast
  have "ball 0 r \<subseteq> {a - a'|a a'. a \<in> A \<and> a' \<in> A}"
  proof(rule ccontr)
    assume "\<not> ball 0 r \<subseteq> {a - a' |a a'. a \<in> A \<and> a' \<in> A}"
    then have "ball 0 r \<inter> (UNIV - {a - a' |a a'. a \<in> K \<and> a' \<in> K}) \<noteq> {}"
      using K A' by blast
    then obtain x where x:"x \<in> ball 0 r" "(+) x ` K \<inter> K = {}"
      by fastforce
    have Kx_U:"(+) x ` K \<subseteq> U"
    proof safe
      show "k \<in> K \<Longrightarrow> x + k \<in> U" for k
        using r[of k] x
        by (metis Groups.add_ac(2) add_0 image_add_ball rev_image_eqI subset_iff) 
    qed
    have "2 * measure lborel K = 2 * measure lebesgue K"
      by (simp add: K borel_compact)
    also have "... = measure lebesgue ((+) x ` K) + measure lebesgue K"
      by(simp add: measure_translation)
    also have "... = measure lborel ((+) x ` K) + measure lborel K"
      by(simp add: K borel_compact compact_translation)
    also have "... = measure lborel (((+) x ` K) \<union> K)"
      using emeasure_compact_finite[of K] emeasure_compact_finite[of "(+) x ` K"]
      using x by(intro measure_Union[symmetric])
                (auto simp: K compact_translation borel_compact)
    also have "... \<le> measure lborel U"
      using U K r Kx_U
      by(auto intro!: measure_mono_fmeasurable fmeasurableI emeasure_bounded_finite
          simp: compact_translation borel_compact)
    finally show False
      using less_UK by auto
  qed
  thus ?thesis
    using r_pos mem_interior by blast
qed

text \<open>The proof of the following lemma is based on
     \<^url>\<open>https://math.stackexchange.com/questions/45861/show-that-fxy-fxfy-implies-f-continuous-leftrightarrow-f-measur\<close>.\<close>
lemma Cauchy_equation_continuous_iff_measurable:
  fixes h :: "real \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
  shows "continuous_on UNIV h \<longleftrightarrow> h \<in> borel_measurable borel"
proof
  assume [measurable]: "h \<in> borel_measurable borel"
  have h0:"h 0 = 0"
    using h_eq[of 0 0] by simp
  have h_neg:"h (- x) = - h x" for x
    using h_eq[of x "- x"] by (simp add: add_eq_0_iff2 h0)
  have h_eq':"h (x - y) = h x - h y" for x y
    using h_eq[of x "- y"] by(auto simp: h_neg[symmetric])
  have "isCont h 0"
    unfolding continuous_at_real_range
  proof safe
    fix e :: real
    assume e:"0 < e"
    have h0:"h 0 = 0"
      using h_eq[of 0 0] by simp
    have [measurable]:"A \<in> sets borel \<Longrightarrow> h -` A \<in> sets borel" for A
      by(auto intro!: measurable_sets_borel)
    have "\<exists>a b. a < b \<and> b - a = e \<and> 0 < emeasure lborel (h -` {a<..<b})"
    proof(rule ccontr)
      assume "\<nexists>a b. a < b \<and> b - a = e \<and>
          0 < emeasure lborel (h -` {a<..<b})"
      then have h:"\<And>a b. a < b \<Longrightarrow> b - a = e \<Longrightarrow> emeasure lborel (h -` {a<..<b}) = 0"
        using not_gr_zero by blast
      have "\<infinity> = emeasure lborel (UNIV :: real set)"
        by simp
      also have "... = emeasure lborel
       (h -` (\<Union>n. {e * real_of_int (from_nat n) / 2 <..<e * real_of_int (from_nat n) / 2 + e}))"
      proof -
        have "x \<in> (\<Union>n.
               {e * real_of_int (from_nat n) / 2 <..<e * real_of_int (from_nat n) / 2 + e})"
          for x
        proof -
          obtain i :: int where "i \<le> 2 * x / e" and i2: "2 * x / e < i + 1"
            by (meson floor_exists1)
          then have i1:"i - 1 < 2 * x / e"
            by linarith
          obtain n where n:"from_nat n = i - 1"
            using from_nat_to_nat by blast
          thus ?thesis
            using i1 i2 e by(auto intro!: exI[where x=n]
                simp: mult.commute n pos_less_divide_eq pos_divide_less_eq
                right_diff_distrib distrib_left diff_divide_distrib)
        qed
        hence *:"(\<Union>n. {e * real_of_int (from_nat n) / 2 <..<e * real_of_int (from_nat n) / 2 + e})
                  = UNIV"
          by fast
        thus ?thesis
          unfolding * by simp
      qed
      also have "... = emeasure lborel
       ((\<Union>n. h -` ({e * real_of_int (from_nat n) / 2 <..<e * real_of_int (from_nat n) / 2 + e})))"
        by(rule arg_cong[where f="emeasure lborel"]) blast
      also have "... \<le> (\<Sum>n. emeasure lborel
              (h -` {e * real_of_int (from_nat n) / 2 <..<e * real_of_int (from_nat n) / 2 + e}))"
        by(rule emeasure_subadditive_countably) auto
      also have "... = (\<Sum>n. 0)"
        by(intro suminf_cong h) (use e in auto)
      finally show False
        by simp
    qed
    then obtain a b where ab:"a < b" "b - a = e" "0 < emeasure lborel (h -` {a<..<b})"
      by blast
    then obtain d where d: "d > 0"
      "ball 0 d \<subseteq> {\<alpha> - \<beta>|\<alpha> \<beta>. \<alpha> \<in> h -` {a<..<b} \<and> \<beta> \<in> h -` {a<..<b}}"
      using weak_Steinhaus[of "h -` {a<..<b}"]
      by (auto simp: mem_interior)
    have "{\<alpha> - \<beta>|\<alpha> \<beta>. \<alpha> \<in> h -` {a<..<b} \<and> \<beta> \<in> h -` {a<..<b}} \<subseteq>
          h -` {c - d|c d. c \<in> {a<..<b} \<and> d \<in> {a<..<b}}"
      by(fastforce simp: h_eq')
    also have "... \<subseteq> h -` ({-e<..<e})"
      using ab by auto
    finally show "\<exists>\<delta>>0. \<forall>x'. norm (x' - 0) < \<delta> \<longrightarrow> \<bar>h x' - h 0\<bar> < e"
      using d
      by(intro exI[where x=d]) (simp add: abs_less_iff h0 minus_less_iff subset_eq)
  qed
  thus "continuous_on UNIV h"
    by(intro Cauchy_equation_isCont_continuous h_eq)
qed(rule borel_measurable_continuous_onI)

subsubsection \<open>Conclusion\<close>
corollary
  fixes h :: "real \<Rightarrow> real"
  assumes h_meas[measurable]:"h \<in> borel_measurable borel"
    and h_eq:"\<And>x y. h (x + y) = h x + h y"
  shows Cauchy_equation_measurable': "h = (\<lambda>x. x * h 1)"
    and Cauchy_equation_measurable: "\<exists>c. h = (\<lambda>x. x * c)"
  using Cauchy_equation_continuous_iff_measurable assms
    Cauchy_equation_continuous' Cauchy_equation_continuous
  by blast+

subsection \<open> Corollaries \<close>
corollary multiplicative_measurable_powr:
  fixes A :: "real \<Rightarrow> real"
  assumes A:"A \<in> borel_measurable (restrict_space borel {0<..})"
    and A_pos:"\<And>x. 0 < x \<Longrightarrow> 0 < A x"
    and eq:"\<And>x y. 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> A (x * y) = A x * A y"
  obtains \<gamma> where "\<And>x. 0 < x \<Longrightarrow> A x = x powr \<gamma>"
proof -
  define h where "h = (\<lambda>s. ln (A (exp s)))"
  have h_eq:"h (s + t) = h s + h t" for s t
    using A_pos[OF exp_gt_zero[of s]] A_pos[OF exp_gt_zero[of t]]
    by(auto simp: h_def exp_add eq ln_mult)
  have h_meas:"h \<in> borel_measurable borel"
    unfolding h_def
    by (intro borel_measurable_ln measurable_compose[OF _ A] measurable_restrict_space2) auto
  obtain c where c:"h = (\<lambda>s. s * c)"
    using Cauchy_equation_measurable h_meas h_eq by blast
  show ?thesis
  proof (rule that[of c])
    fix x :: real
    assume x:"0 < x"
    have "A x = exp (h (ln x))"
      unfolding h_def using x A_pos[OF x] by simp
    also have "\<dots> = x powr c"
      using c x by (simp add: powr_def)
    finally show "A x = x powr c" .
  qed
qed

lemma cocycle_mono_solution:
  fixes H :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes mono:"mono H"
    and eq:"\<And>u v. H (u + v) = H u * exp (\<gamma> * v) + H v"
  obtains c where "0 \<le> c"
    and "\<And>u. H u = (if \<gamma> = 0 then c * u else c * (exp (\<gamma> * u) - 1) / \<gamma>)"
proof -
  have H0:"H 0 = 0"
    using eq[of 0 0] by simp
  have H1_nonneg:"0 \<le> H 1"
    using monoD[OF mono, of 0 1] H0 by simp
  show ?thesis
  proof (cases "\<gamma> = 0")
    assume gamma:"\<gamma> = 0"
    have eq':"H (u + v) = H u + H v" for u v
      using eq[of u v] gamma by simp
    obtain c where c:"H = (\<lambda>x. x * c)"
      using Cauchy_equation_mono eq' mono by blast
    have "0 \<le> c"
      using monoD[OF mono, of 0 1] c by simp
    thus ?thesis
      using that[of c] by(simp add: gamma c)
  next
    assume gamma:"\<gamma> \<noteq> 0"
    have swap:"H u * (exp (\<gamma> * v) - 1) = H v * (exp (\<gamma> * u) - 1)" for u v
      using eq[of u v] eq[of v u] by (simp add: algebra_simps)
    define k where "k = H 1 / (exp \<gamma> - 1)"
    have Hform:"H u = k * (exp (\<gamma> * u) - 1)" for u
      using swap[of u 1] gamma by (simp add: k_def field_simps)
    define c where "c = \<gamma> * k"
    have ratio_pos:"0 < \<gamma> / (exp \<gamma> - 1)"
      by(cases "0 < \<gamma>")
        (use gamma in "auto simp add: zero_less_divide_iff")
    have "0 \<le> c"
      using mult_nonneg_nonneg[OF H1_nonneg less_imp_le[OF ratio_pos]]
      by(simp add: c_def k_def mult.commute)
    thus ?thesis
      using that[of c] by(simp add: gamma Hform c_def)
  qed
qed

section \<open>Non-Linear Solutions\<close>
text \<open> Cf. Hamel~\<^cite>\<open>Hamel1905\<close> and
           \<^url>\<open>https://en.wikipedia.org/wiki/Cauchy%27s_functional_equation\<close>.\<close>
subsection \<open> Existence \<close>
lemma infinite_Hamel_basis:
  fixes B :: "real set"
  assumes "module.span (\<lambda>q x. of_rat q * x) B = UNIV"
  shows "infinite B"
proof -
  interpret ratvs: vector_space "\<lambda>q x. of_rat q * (x :: real)"
    by unfold_locales (auto simp: of_rat_add of_rat_mult algebra_simps)
  have *:"countable (range (\<lambda>u :: real \<Rightarrow> rat. \<Sum>v\<in>S. of_rat (u v) * v))"
    if S:"finite S" for S
  proof -
    have sub:"range (\<lambda>u :: real \<Rightarrow> rat. \<Sum>v\<in>S. of_rat (u v) * v)
                \<subseteq> (\<lambda>u. \<Sum>v\<in>S. of_rat (u v) * v) ` (S \<rightarrow>\<^sub>E (UNIV :: rat set))"
    proof safe
      fix u :: "real \<Rightarrow> rat"
      show "(\<Sum>v\<in>S. of_rat (u v) * v)
              \<in> (\<lambda>u. \<Sum>v\<in>S. of_rat (u v) * v) ` (S \<rightarrow>\<^sub>E (UNIV :: rat set))"
        unfolding image_iff
        by (intro bexI[of _ "restrict u S"] sum.cong) (auto simp: PiE_iff)
    qed
    show ?thesis
      by (intro countable_subset[OF sub] countable_image countable_PiE S) auto
  qed
  show ?thesis
  proof
    assume fin:"finite B"
    have "countable (ratvs.span B)"
      using ratvs.span_finite[OF fin] *[OF fin] by simp
    thus False
      using assms uncountable_UNIV_real by simp
  qed
qed

lemma rat_Hamel_basisE:
  obtains B :: "real set"
  where "module.independent (\<lambda>q x. of_rat q * x) B"
    and "module.span (\<lambda>q x. of_rat q * x) B = UNIV"
    and "0 \<notin> B"
proof -
  interpret ratvs: vector_space "\<lambda>q x. of_rat q * (x :: real)"
    by unfold_locales (auto simp: of_rat_add of_rat_mult algebra_simps)
  obtain B where B:"ratvs.independent B" "UNIV \<subseteq> ratvs.span B"
    using ratvs.maximal_independent_subset[of UNIV] by auto
  hence sp:"ratvs.span B = UNIV"
    by auto
  have "0 \<notin> B"
    using B ratvs.dependent_zero by auto
  with B sp
  show ?thesis
    by (intro that) auto
qed

lemma lists_lepoll_infinite:
  assumes inf:"infinite A"
  shows "lists A \<lesssim> A"
proof -
  define L where "L \<equiv> \<lambda>n. {l \<in> lists A. length l = n}"
  have AA:"A \<times> A \<approx> A"
    using card_of_Times_same_infinite[OF inf] by (simp add: eqpoll_iff_card_of_ordIso)
  have L:"L n \<lesssim> A" for n
  proof (induction n)
    case ih:(Suc n)
    have inj:"inj_on (\<lambda>l. (hd l, tl l)) (L (Suc n))"
      by (auto simp: inj_on_def L_def)
        (metis hd_Cons_tl length_greater_0_conv zero_less_Suc)
    have img:"(\<lambda>l. (hd l, tl l)) ` L (Suc n) \<subseteq> A \<times> L n"
    proof (rule image_subsetI)
      fix l
      assume l:"l \<in> L (Suc n)"
      then obtain a l' where "l = a # l'"
        by (cases l) (auto simp: L_def)
      with l show "(hd l, tl l) \<in> A \<times> L n"
        by (auto simp: L_def)
    qed
    have "L (Suc n) \<lesssim> A \<times> L n"
      unfolding lepoll_def by (intro exI[of _ "\<lambda>l. (hd l, tl l)"] conjI inj img)
    also have "A \<times> L n \<lesssim> A \<times> A"
      by (intro times_lepoll_mono lepoll_refl ih)
    also have "A \<times> A \<approx> A"
      by (rule AA)
    finally show ?case .
  qed (auto simp: L_def intro!: finite_lepoll_infinite inf)
  have "lists A \<lesssim> Sigma (UNIV :: nat set) L"
    unfolding lepoll_def
    by (intro exI[of _ "\<lambda>l. (length l, l)"] conjI) (auto simp: inj_on_def L_def)
  also have "... \<lesssim> (UNIV :: nat set) \<times> A"
    by (intro Sigma_lepoll_mono subset_refl L)
  also have "... \<lesssim> A \<times> A"
    by (intro times_lepoll_mono lepoll_refl infinite_le_lepoll[THEN iffD1, OF inf])
  also have "A \<times> A \<approx> A"
    by (rule AA)
  finally show ?thesis .
qed

lemma UNIV_real_lepoll_basis_Diff:
  fixes u v :: real
  assumes sp:"module.span (\<lambda>q x. of_rat q * x) B = UNIV"
  shows "(UNIV :: real set) \<lesssim> B - {u, v}"
proof -
  interpret ratvs: vector_space "\<lambda>q x. of_rat q * (x :: real)"
    by unfold_locales (auto simp: of_rat_add of_rat_mult algebra_simps)
  note inf = infinite_Hamel_basis[OF sp]
  have Binf:"infinite (B - {u, v})"
    by (intro Diff_infinite_finite inf) simp
  have "(UNIV :: real set) \<subseteq> (\<lambda>l. \<Sum>(q, y)\<leftarrow>l. of_rat q * y) ` lists (UNIV \<times> B)"
  proof
    fix x :: real
    have "x \<in> ratvs.span B"
      by (simp add: sp)
    then obtain t r where t_fin:"finite t" and tB:"t \<subseteq> B"
      and x:"x = (\<Sum>a\<in>t. of_rat (r a) * a)"
      unfolding ratvs.span_explicit by blast
    obtain xs where xs:"set xs = t" and xs_dist:"distinct xs"
      using finite_distinct_list t_fin by blast
    have "x = (\<Sum>(q, y)\<leftarrow>map (\<lambda>a. (r a, a)) xs. of_rat q * y)"
      by (simp add: x xs xs_dist sum_list_distinct_conv_sum_set)
    moreover have "map (\<lambda>a. (r a, a)) xs \<in> lists (UNIV \<times> B)"
      using tB xs by (auto simp: in_lists_conv_set)
    ultimately show "x \<in> (\<lambda>l. \<Sum>(q, y)\<leftarrow>l. of_rat q * y) ` lists (UNIV \<times> B)"
      by blast
  qed
  hence "(UNIV :: real set) \<lesssim> lists ((UNIV :: rat set) \<times> B)"
    by (rule subset_image_lepoll[where f="\<lambda>l. \<Sum>(q, y)\<leftarrow>l. of_rat q * y"])
  also have "lists ((UNIV :: rat set) \<times> B) \<lesssim> (UNIV :: rat set) \<times> B"
    using inf finite_cartesian_productD2 by (intro lists_lepoll_infinite) blast
  also have "(UNIV :: rat set) \<times> B \<lesssim> B \<times> B"
  proof (intro times_lepoll_mono lepoll_refl)
    have "(UNIV :: rat set) \<lesssim> (UNIV :: nat set)"
      unfolding lepoll_def by (intro exI[of _ to_nat] conjI) simp_all
    thus "(UNIV :: rat set) \<lesssim> B"
      using infinite_le_lepoll[THEN iffD1, OF inf] lepoll_trans by blast
  qed
  also have "B \<times> B \<approx> B"
    using card_of_Times_same_infinite[OF inf]
    by(simp add: eqpoll_iff_card_of_ordIso)
  also have "... \<lesssim> insert u (insert v (B - {u, v}))"
    by (intro subset_imp_lepoll) auto
  also have "... \<approx> insert v (B - {u, v})"
    using Binf by (intro infinite_insert_eqpoll) simp
  also have "... \<approx> B - {u, v}"
    using Binf by (rule infinite_insert_eqpoll)
  finally show ?thesis .
qed

corollary card_Hamel_basis:
  fixes B :: "real set"
  assumes sp: "module.span (\<lambda>q x. of_rat q * x) B = UNIV"
  shows "B \<approx> (UNIV :: real set)"
proof(rule lepoll_antisym)
  have "(UNIV :: real set) \<lesssim> B - {0, 0}"
    by(intro UNIV_real_lepoll_basis_Diff sp)
  also have "... \<lesssim> B"
    by (simp add: subset_imp_lepoll)
  finally show "(UNIV :: real set) \<lesssim> B" .
qed(simp add: subset_imp_lepoll)

lemma UNIV_fun_lepoll_nonlinear:
  "(UNIV :: (real \<Rightarrow> real) set)
    \<lesssim> {h :: real \<Rightarrow> real. (\<forall>x y. h (x + y) = h x + h y) \<and> (\<forall>c. h \<noteq> (\<lambda>x. x * c))}"
proof -
  interpret ratvsp: vector_space_pair
    "\<lambda>q x. of_rat q * (x :: real)" "\<lambda>q x. of_rat q * (x :: real)"
    by unfold_locales (auto simp: of_rat_add of_rat_mult algebra_simps)
  obtain B :: "real set"
    where indep:"\<not> module.dependent (\<lambda>q x. of_rat q * x) B"
      and span:"module.span (\<lambda>q x. of_rat q * x) B = UNIV" and 0:"0 \<notin> B"
    by (rule rat_Hamel_basisE)
  note inf = infinite_Hamel_basis[OF span]
  obtain b1 where b1:"b1 \<in> B"
    using inf all_not_in_conv by fastforce
  have "infinite (B - {b1})"
    using inf by (simp add: infinite_remove)
  then obtain b2 where b2:"b2 \<in> B" and b2_ne:"b2 \<noteq> b1"
    using infinite_imp_nonempty by blast
  obtain \<iota> :: "real \<Rightarrow> real" where \<iota>_inj:"inj \<iota>" and \<iota>_range:"range \<iota> \<subseteq> B - {b1, b2}"
    using UNIV_real_lepoll_basis_Diff[OF span, of b1 b2]
    by (auto simp: lepoll_def)
  define \<Phi> :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
    "\<Phi> \<phi> = ratvsp.construct B (\<lambda>b. if b = b1 then 1 else if b = b2 then 0 else \<phi> (inv \<iota> b))"
    for \<phi>
  have add:"\<Phi> \<phi> (x + y) = \<Phi> \<phi> x + \<Phi> \<phi> y" for \<phi> x y
    using ratvsp.linear_add[OF ratvsp.linear_construct[OF indep]] by (simp add: \<Phi>_def)
  have vb1:"\<Phi> \<phi> b1 = 1" for \<phi>
    using ratvsp.construct_basis[OF indep b1] by (simp add: \<Phi>_def)
  have vb2:"\<Phi> \<phi> b2 = 0" for \<phi>
    using ratvsp.construct_basis[OF indep b2] b2_ne by (simp add: \<Phi>_def)
  have v\<iota>:"\<Phi> \<phi> (\<iota> x) = \<phi> x" for \<phi> x
  proof -
    have \<iota>B:"\<iota> x \<in> B" and \<iota>b1:"\<iota> x \<noteq> b1" and \<iota>b2:"\<iota> x \<noteq> b2"
      using \<iota>_range by auto
    show ?thesis
      using ratvsp.construct_basis[OF indep \<iota>B] \<iota>b1 \<iota>b2 inv_f_f[OF \<iota>_inj]
      by (simp add: \<Phi>_def)
  qed
  have nonlin:"\<Phi> \<phi> \<noteq> (\<lambda>x. x * c)" for \<phi> c
  proof
    assume eq:"\<Phi> \<phi> = (\<lambda>x. x * c)"
    have "c = 0"
      using fun_cong[OF eq, of b2] vb2[of \<phi>] b2 0 by auto
    thus False
      using fun_cong[OF eq, of b1] vb1[of \<phi>] by simp
  qed
  have "inj \<Phi>"
    using v\<iota> by (metis ext inj_def)
  moreover have "range \<Phi> \<subseteq> {h. (\<forall>x y. h (x + y) = h x + h y) \<and> (\<forall>c. h \<noteq> (\<lambda>x. x * c))}"
    by (intro image_subsetI CollectI conjI allI add nonlin)
  ultimately show ?thesis
    unfolding lepoll_def by (intro exI[of _ \<Phi>] conjI)
qed

lemma Cauchy_equation_nonlinear_solution_ex:
  "\<exists>h :: real \<Rightarrow> real. (\<forall>x y. h (x + y) = h x + h y) \<and> (\<forall>c. h \<noteq> (\<lambda>x. x * c))"
proof -
  obtain \<Phi> :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real"
    where "range \<Phi> \<subseteq> {h. (\<forall>x y. h (x + y) = h x + h y) \<and> (\<forall>c. h \<noteq> (\<lambda>x. x * c))}"
    using UNIV_fun_lepoll_nonlinear by (auto simp: lepoll_def)
  thus ?thesis
    by blast
qed

lemma Cauchy_equation_nonlinear_solution:
  obtains h :: "real \<Rightarrow> real"
  where "\<And>x y. h (x + y) = h x + h y"
    and "\<And>c. h \<noteq> (\<lambda>x. x * c)"
  using Cauchy_equation_nonlinear_solution_ex that by blast

subsection \<open> Cardinality \<close>
lemma card_Cauchy_equation_nonlinear_solutions:
  "{h :: real \<Rightarrow> real. (\<forall>x y. h (x + y) = h x + h y) \<and> (\<forall>c. h \<noteq> (\<lambda>x. x * c))}
    \<approx> (UNIV :: (real \<Rightarrow> real) set)"
  by (intro lepoll_antisym subset_imp_lepoll subset_UNIV UNIV_fun_lepoll_nonlinear)

subsection \<open>Density of the Graph of a Non-Linear Solution\<close>

lemma Cauchy_equation_nonlinear_graph_indep:
  fixes h :: "real \<Rightarrow> real"
  assumes "\<And>c. h \<noteq> (\<lambda>x. x * c)"
  obtains x\<^sub>1 x\<^sub>2 where "x\<^sub>1 * h x\<^sub>2 - x\<^sub>2 * h x\<^sub>1 \<noteq> 0"
  using assms by (metis mult_cancel_right2 right_minus_eq)

theorem Cauchy_equation_nonlinear_graph_dense:
  fixes h :: "real \<Rightarrow> real"
  assumes h_eq:"\<And>x y. h (x + y) = h x + h y"
    and nonlin:"\<And>c. h \<noteq> (\<lambda>x. x * c)"
  shows "closure (range (\<lambda>x. (x, h x))) = UNIV"
proof -
  obtain x\<^sub>1 x\<^sub>2 where D:"x\<^sub>1 * h x\<^sub>2 - x\<^sub>2 * h x\<^sub>1 \<noteq> 0"
    using Cauchy_equation_nonlinear_graph_indep assms by blast
  have key:"\<exists>x. \<bar>x - a\<bar> < e \<and> \<bar>h x - b\<bar> < e" if e:"0 < e" for a b e
  proof -
    define M where "M = \<bar>x\<^sub>1\<bar> + \<bar>x\<^sub>2\<bar> + \<bar>h x\<^sub>1\<bar> + \<bar>h x\<^sub>2\<bar> + 1"
    have M_pos:"0 < M"
      unfolding M_def by (intro add_nonneg_pos add_nonneg_nonneg) auto
    have M1:"\<bar>x\<^sub>1\<bar> + \<bar>x\<^sub>2\<bar> < M" and M2:"\<bar>h x\<^sub>1\<bar> + \<bar>h x\<^sub>2\<bar> < M"
      by (auto simp: M_def)
    define \<delta> where "\<delta> = e / M"
    have \<delta>_pos:"0 < \<delta>"
      using e M_pos by (simp add: \<delta>_def)
    define q\<^sub>1 where "q\<^sub>1 = (a * h x\<^sub>2 - x\<^sub>2 * b) / (x\<^sub>1 * h x\<^sub>2 - x\<^sub>2 * h x\<^sub>1)"
    define q\<^sub>2 where "q\<^sub>2 = (x\<^sub>1 * b - a * h x\<^sub>1) / (x\<^sub>1 * h x\<^sub>2 - x\<^sub>2 * h x\<^sub>1)"
    have quot:"q\<^sub>1 * s\<^sub>1 + q\<^sub>2 * s\<^sub>2
                 = ((a * h x\<^sub>2 - x\<^sub>2 * b) * s\<^sub>1 + (x\<^sub>1 * b - a * h x\<^sub>1) * s\<^sub>2)
                    / (x\<^sub>1 * h x\<^sub>2 - x\<^sub>2 * h x\<^sub>1)" for s\<^sub>1 s\<^sub>2
      by (simp add: q\<^sub>1_def q\<^sub>2_def add_divide_distrib)
    have a_eq:"q\<^sub>1 * x\<^sub>1 + q\<^sub>2 * x\<^sub>2 = a" and b_eq:"q\<^sub>1 * h x\<^sub>1 + q\<^sub>2 * h x\<^sub>2 = b"
      unfolding quot using D by (simp_all add: field_simps)
    obtain r\<^sub>1 where r\<^sub>1:"r\<^sub>1 \<in> \<rat>" and r\<^sub>1':"q\<^sub>1 < r\<^sub>1" "r\<^sub>1 < q\<^sub>1 + \<delta>"
      using Rats_dense_in_real[of "q\<^sub>1" "q\<^sub>1 + \<delta>"] \<delta>_pos by auto
    obtain r\<^sub>2 where r\<^sub>2:"r\<^sub>2 \<in> \<rat>" and r\<^sub>2':"q\<^sub>2 < r\<^sub>2" "r\<^sub>2 < q\<^sub>2 + \<delta>"
      using Rats_dense_in_real[of "q\<^sub>2" "q\<^sub>2 + \<delta>"] \<delta>_pos by auto
    have r\<^sub>1\<delta>:"\<bar>r\<^sub>1 - q\<^sub>1\<bar> < \<delta>" and r\<^sub>2\<delta>:"\<bar>r\<^sub>2 - q\<^sub>2\<bar> < \<delta>"
      using r\<^sub>1' r\<^sub>2' by auto
    have est:"\<bar>(r\<^sub>1 - q\<^sub>1) * s\<^sub>1 + (r\<^sub>2 - q\<^sub>2) * s\<^sub>2\<bar> < e" if s:"\<bar>s\<^sub>1\<bar> + \<bar>s\<^sub>2\<bar> < M"
      for s\<^sub>1 s\<^sub>2
    proof -
      have "\<bar>(r\<^sub>1 - q\<^sub>1) * s\<^sub>1 + (r\<^sub>2 - q\<^sub>2) * s\<^sub>2\<bar> \<le> \<bar>r\<^sub>1 - q\<^sub>1\<bar> * \<bar>s\<^sub>1\<bar> + \<bar>r\<^sub>2 - q\<^sub>2\<bar> * \<bar>s\<^sub>2\<bar>"
        by (metis abs_mult abs_triangle_ineq)
      also have "... \<le> \<delta> * \<bar>s\<^sub>1\<bar> + \<delta> * \<bar>s\<^sub>2\<bar>"
        using r\<^sub>1\<delta> r\<^sub>2\<delta> by (intro add_mono mult_right_mono) auto
      also have "... = \<delta> * (\<bar>s\<^sub>1\<bar> + \<bar>s\<^sub>2\<bar>)"
        by (simp add: distrib_left)
      also have "... < \<delta> * M"
        using \<delta>_pos s by (intro mult_strict_left_mono) auto
      also have "... = e"
        using M_pos by (simp add: \<delta>_def)
      finally show ?thesis .
    qed
    define x where "x = r\<^sub>1 * x\<^sub>1 + r\<^sub>2 * x\<^sub>2"
    have hx:"h x = r\<^sub>1 * h x\<^sub>1 + r\<^sub>2 * h x\<^sub>2"
      unfolding x_def h_eq[of "r\<^sub>1 * x\<^sub>1" "r\<^sub>2 * x\<^sub>2"]
      by (simp add: Cauchy_equation_Q_linear[of h r\<^sub>1 x\<^sub>1, OF h_eq r\<^sub>1]
                    Cauchy_equation_Q_linear[of h r\<^sub>2 x\<^sub>2, OF h_eq r\<^sub>2])
    have "\<bar>x - a\<bar> < e"
      using est[OF M1]
      unfolding x_def a_eq[symmetric]
      by (simp add: algebra_simps)
    moreover have "\<bar>h x - b\<bar> < e"
      using est[OF M2]
      unfolding hx b_eq[symmetric]
      by (simp add: algebra_simps)
    ultimately show ?thesis
      by blast
  qed
  have "z \<in> closure (range (\<lambda>x. (x, h x)))" for z
  proof (cases z)
    case (Pair a b)
    show ?thesis
      unfolding Pair closure_approachable
    proof (intro allI impI)
      fix e :: real
      assume e:"0 < e"
      then obtain x where x:"\<bar>x - a\<bar> < e / 2" "\<bar>h x - b\<bar> < e / 2"
        using key[of "e / 2" a b] by auto
      have "dist (x, h x) (a, b) \<le> \<bar>x - a\<bar> + \<bar>h x - b\<bar>"
        using sqrt_sum_squares_le_sum[of "\<bar>x - a\<bar>" "\<bar>h x - b\<bar>"]
        by (simp add: dist_Pair_Pair dist_real_def)
      also have "... < e"
        using x by simp
      finally show "\<exists>y\<in>range (\<lambda>x. (x, h x)). dist y (a, b) < e"
        by (intro bexI[of _ "(x, h x)"]) auto
    qed
  qed
  thus ?thesis
    by blast
qed

end