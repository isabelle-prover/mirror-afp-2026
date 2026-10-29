(*  Title:   Rational_Padic_Valuations.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Rational_Padic_Valuations
  imports "Kummer_Congruence.Rat_Congruence" "Jordan_Normal_Form.Determinant" "HOL-Library.Log_Nat"
begin

section \<open>A calculus for lower bounds on \<open>p\<close>-adic valuations of rationals and
  polynomials\<close>

text \<open>The \<open>p\<close>-adic valuation of a rational number is @{const qmultiplicity} from
  the AFP entry
  Kummer\_Congruence.  This theory provides the predicate @{text "vge p x b"} (\<open>x =
    0\<close> or
  \<open>v\<^sub>p(x) \<ge> b\<close>) and its coefficientwise version @{text "vpGge p A b"}
    for polynomials (the Gauss
  valuation), together with their closure under sums, products, powers, polynomial evaluation,
  division by monic polynomials and the Leibniz terms of determinants, the ultrametric
  inequality for @{const qmultiplicity} (absent from the AFP), and the valuations of powers and
  products.  Nothing here depends on the irrationality proof.\<close>

subsection \<open>Definitions\<close>

text \<open>The polynomial indeterminate.\<close>
abbreviation pX :: "rat poly" where "pX \<equiv> Polynomial.monom 1 1"

text \<open>The @{text p}-adic valuation of a rational (Mathlib: @{text padicValRat}).\<close>
definition vp :: "nat \<Rightarrow> rat \<Rightarrow> int" where
  "vp p x = qmultiplicity (int p) x"

text \<open>@{text "\<lfloor>log_p n\<rfloor>"} (Mathlib's @{text "Nat.log p n"}; 0
  for @{text "n = 0"} or @{text "p \<le> 1"}).\<close>
definition nat_log :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_log p n = floorlog p n - 1"

text \<open>@{text "x = 0 \<or> b \<le> v_p(x)"}.\<close>
definition vge :: "nat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> bool" where
  "vge p x b \<longleftrightarrow> (x \<noteq> 0 \<longrightarrow> b \<le> of_int (vp p x))"

text \<open>@{text "v_p^G(A) \<ge> b"}: every nonzero coefficient has valuation at least
  @{text b}.\<close>
definition vpGge :: "nat \<Rightarrow> rat poly \<Rightarrow> rat \<Rightarrow> bool" where
  "vpGge p A b \<longleftrightarrow> (\<forall>i. Polynomial.coeff A i \<noteq> 0 \<longrightarrow>
    b \<le> of_int (vp p (Polynomial.coeff A i)))"

subsection \<open>Basic closure properties\<close>


lemma prime_multiplicity_prime:
  fixes p q :: "'a :: factorial_semiring"
  assumes "prime p" "prime q"
  shows   "multiplicity p q = (if p = q then 1 else 0)"
  using assms by (auto simp: prime_multiplicity_other)

lemma vge_zero: "vge p 0 b" by (simp add: vge_def)
lemma vge_mono: "vge p x b \<Longrightarrow> b' \<le> b \<Longrightarrow> vge p x b'"
  by (auto simp: vge_def)

subsection \<open>The ultrametric inequality for @{const qmultiplicity} (not in the AFP)\<close>

lemma qmultiplicity_power_int:
  assumes "prime p"
  shows "qmultiplicity (int p) (of_nat p powi k) = k"
proof -
  have pe: "prime_elem (int p)" using assms by (simp add: prime_nat_int_transfer)
  have pow: "\<And>n. qmultiplicity (int p) (of_nat p ^ n) = int n"
  proof -
    fix n :: nat
    have "qmultiplicity (int p) (of_nat p ^ n) = qmultiplicity (int p) (of_nat (p ^ n))" by simp
    also have "\<dots> = int (multiplicity (int p) (int (p ^ n)))" by (rule qmultiplicity_of_nat)
    also have "\<dots> = int n" using pe by (simp add: multiplicity_prime_power)
    finally show "qmultiplicity (int p) (of_nat p ^ n) = int n" .
  qed
  show ?thesis
    by (cases "k \<ge> 0") (simp_all add: power_int_def pow power_inverse)
qed

lemma qmultiplicity_nonneg_add:
  assumes "prime p" "0 \<le> qmultiplicity (int p) x" "0 \<le>
    qmultiplicity (int p) y" "x + y \<noteq> 0"
  shows "0 \<le> qmultiplicity (int p) (x + y)"
proof -
  obtain a b where ab: "quotient_of x = (a, b)" using prod.exhaust by blast
  obtain c d where cd: "quotient_of y = (c, d)" using prod.exhaust by blast
  have b: "b > 0" and d: "d > 0" using ab cd quotient_of_denom_pos by blast+
  have p1: "\<bar>int p\<bar> \<noteq> 1" using prime_gt_1_nat[OF assms(1)] by simp
  have nb: "\<not> int p dvd b" using qmultiplicity_nonneg_imp_not_dvd_denom[OF assms(2) p1] ab
    by simp
  have nd: "\<not> int p dvd d" using qmultiplicity_nonneg_imp_not_dvd_denom[OF assms(3) p1] cd
    by simp
  have x: "x = of_int a / of_int b" and y: "y = of_int c / of_int d"
    using ab cd by (simp_all add: quotient_of_div)
  have xy: "x + y = of_int (a * d + c * b) / of_int (b * d)"
    using b d by (simp add: x y add_frac_eq)
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  have num: "a * d + c * b \<noteq> 0"
  proof
    assume "a * d + c * b = 0"
    hence "(of_int (a * d + c * b) :: rat) = 0" by simp
    with xy have "x + y = 0" by simp
    thus False using assms(4) by simp
  qed
  have n0: "(of_int (a * d + c * b) :: rat) \<noteq> 0" using num
    by (simp only: of_int_eq_0_iff num simp_thms)
  have "qmultiplicity (int p) (x + y) =
          qmultiplicity (int p) (of_int (a * d + c * b)) - qmultiplicity (int p) (of_int (b * d))"
    unfolding xy by (intro qmultiplicity_divide pe n0) (use b d in simp)
  also have "\<dots> = int (multiplicity (int p) (a * d + c * b)) - int (multiplicity (int p) (b *
    d))"
    by (simp only: qmultiplicity_of_int)
  finally have "qmultiplicity (int p) (x + y) =
          int (multiplicity (int p) (a * d + c * b)) - int (multiplicity (int p) (b * d))" .
  moreover have "multiplicity (int p) (b * d) = 0"
    using nb nd assms(1) by (intro not_dvd_imp_multiplicity_0) (simp add: prime_dvd_mult_iff
      prime_nat_int_transfer)
  ultimately show ?thesis by simp
qed

lemma qmultiplicity_add_ge:
  assumes "prime p" "x \<noteq> 0" "y \<noteq> 0" "x + y \<noteq> 0"
  shows "min (qmultiplicity (int p) x) (qmultiplicity (int p) y) \<le>
    qmultiplicity (int p) (x + y)"
proof -
  define k where "k = min (qmultiplicity (int p) x) (qmultiplicity (int p) y)"
  define u :: rat where "u = of_nat p powi (- k)"
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  have u0: "u \<noteq> 0" using assms(1) by (simp add: u_def prime_gt_0_nat)
  have qu: "qmultiplicity (int p) u = - k" using assms(1)
    by (simp add: u_def qmultiplicity_power_int)
  have "0 \<le> qmultiplicity (int p) (x * u)" "0 \<le> qmultiplicity (int p) (y * u)"
    using assms u0 pe qu by (simp_all add: qmultiplicity_mult k_def)
  moreover have "x * u + y * u \<noteq> 0" using assms u0 by (simp add: distrib_right[symmetric])
  ultimately have "0 \<le> qmultiplicity (int p) ((x + y) * u)"
    using qmultiplicity_nonneg_add[OF assms(1)] by (simp add: distrib_right)
  thus ?thesis using assms u0 pe qu by (simp add: qmultiplicity_mult k_def)
qed

lemma vge_add:
  assumes "prime p" "vge p x b" "vge p y b"
  shows "vge p (x + y) b"
proof (cases "x = 0 \<or> y = 0 \<or> x + y = 0")
  case True
  thus ?thesis using assms by (auto simp: vge_def)
next
  case False
  hence "x \<noteq> 0" "y \<noteq> 0" "x + y \<noteq> 0" by auto
  have "b \<le> of_int (min (qmultiplicity (int p) x) (qmultiplicity (int p) y))"
    using assms(2,3) \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close>
      by (auto simp: vge_def vp_def min_def)
  also have "\<dots> \<le> of_int (qmultiplicity (int p) (x + y))"
    using qmultiplicity_add_ge[OF assms(1) \<open>x \<noteq> 0\<close> \<open>y \<noteq>
      0\<close> \<open>x + y \<noteq> 0\<close>] by (simp only: of_int_le_iff)
  finally show ?thesis by (simp add: vge_def vp_def)
qed
lemma vge_neg: "vge p x b \<Longrightarrow> vge p (- x) b" by (simp add: vge_def vp_def)
lemma vge_sum:
  assumes "prime p" "finite I" "\<And>i. i \<in> I \<Longrightarrow> vge p (f i) b"
  shows "vge p (\<Sum> i \<in> I. f i) b"
  using assms(2,3) by (induction I rule: finite_induct) (auto simp: vge_zero vge_add[OF assms(1)])
lemma vge_mul:
  assumes "prime p" "vge p x a" "vge p y b"
  shows "vge p (x * y) (a + b)"
proof (cases "x = 0 \<or> y = 0")
  case True
  thus ?thesis by (auto simp: vge_def)
next
  case False
  have "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  with False assms show ?thesis by (simp add: vge_def vp_def qmultiplicity_mult)
qed
lemma vge_one: "vge p 1 0" by (simp add: vge_def vp_def)
lemma vge_pow: "prime p \<Longrightarrow> vge p x 0 \<Longrightarrow> vge p (x ^ n) 0"
  by (induction n) (auto simp: vge_one dest: vge_mul[where a = 0 and b = 0, simplified])

lemma vge_inv_p: "prime p \<Longrightarrow> vge p (1 / of_nat p) (- 1)"
  by (simp add: vge_def vp_def inverse_eq_divide[symmetric] prime_gt_0_nat)
lemma vge_of_int: "prime p \<Longrightarrow> vge p (of_int n) 0" by (simp add: vge_def vp_def)

lemma vpGge_iff: "vpGge p A b \<longleftrightarrow> (\<forall>i. vge p (Polynomial.coeff A i) b)"
  by (simp add: vpGge_def vge_def)
lemma vpGge_zero: "vpGge p 0 b" by (simp add: vpGge_def)
lemma vpGge_mono: "vpGge p A b \<Longrightarrow> b' \<le> b \<Longrightarrow> vpGge p A b'"
  by (auto simp: vpGge_def)
lemma vpGge_add: "prime p \<Longrightarrow> vpGge p A b \<Longrightarrow>
  vpGge p B b \<Longrightarrow> vpGge p (A + B) b" by (auto simp: vpGge_iff vge_add)
lemma vpGge_neg: "vpGge p A b \<Longrightarrow> vpGge p (- A) b" by (simp add: vpGge_def vp_def)
lemma vpGge_sum:
  assumes "prime p" "finite I" "\<And>i. i \<in> I \<Longrightarrow> vpGge p (f i) b"
  shows "vpGge p (\<Sum> i \<in> I. f i) b"
  using assms(2,3) by (induction I rule: finite_induct) (auto simp: vpGge_zero vpGge_add[OF
    assms(1)])
lemma vpGge_C: "vge p c b \<Longrightarrow> vpGge p [:c:] b"
  by (auto simp: vpGge_def vge_def coeff_pCons split: nat.splits)
lemma vpGge_one: "vpGge p 1 0" by (simp add: vpGge_def vp_def)
lemma vpGge_mul: "prime p \<Longrightarrow> vpGge p A a \<Longrightarrow>
  vpGge p B b \<Longrightarrow> vpGge p (A * B) (a + b)"
  by (auto simp: vpGge_iff coeff_mult intro!: vge_sum vge_mul)
lemma vpGge_prod:
  assumes "prime p" "finite I" "\<And>i. i \<in> I \<Longrightarrow> vpGge p (f i) (b i)"
  shows "vpGge p (\<Prod> i \<in> I. f i) (\<Sum> i \<in> I. b i)"
  using assms(2,3) by (induction I rule: finite_induct) (auto simp: vpGge_one vpGge_mul[OF
    assms(1)])

text \<open>Determinant bound from entry bounds:
  if every Leibniz term has valuation at least @{text B},
  so does the determinant (Lean: @{text vpGge_det_of_terms}).  Proof via
    @{text "Determinant.det_def'"}.\<close>
lemma vpGge_det_of_terms:
  assumes "prime p" "A \<in> carrier_mat n n"
    and "\<And>\<sigma>. \<sigma> permutes {0..<n} \<Longrightarrow>
      vpGge p (\<Prod> i = 0..<n. A $$ (i, \<sigma> i)) B"
  shows "vpGge p (Determinant.det A) B"
proof -
  have "vpGge p (\<Sum>\<sigma> \<in> {\<sigma>. \<sigma> permutes {0..<n}}. signof \<sigma> *
    (\<Prod> i = 0..<n. A $$ (i, \<sigma> i))) B"
  proof (intro vpGge_sum)
    fix \<sigma> assume "\<sigma> \<in> {\<sigma>. \<sigma> permutes {0..<n}}"
    hence perm: "\<sigma> permutes {0..<n}" by simp
    have s: "vpGge p (of_int (Permutations.sign \<sigma>)) 0"
      by (cases \<sigma> rule: Permutations.sign_cases) (simp_all add: vpGge_one vpGge_neg[OF
        vpGge_one])
    have "vpGge p (signof \<sigma> * (\<Prod> i = 0..<n. A $$ (i, \<sigma> i))) (0 + B)"
      using vpGge_mul[OF assms(1) s assms(3)[OF perm]] .
    thus "vpGge p (signof \<sigma> * (\<Prod> i = 0..<n. A $$ (i, \<sigma> i))) B" by simp
  qed (use assms(1) in \<open>auto simp: finite_permutations\<close>)
  thus ?thesis using assms(2) by (simp add: Determinant.det_def')
qed

text \<open>The intended content of @{text vpGge_div_monic}, with monicity written as
  @{term "lead_coeff Q = 1"}.\<close>
lemma vpGge_div_lead1:
  assumes p: "prime p" and Q1: "lead_coeff Q = 1" and Qi: "vpGge p Q 0"
  shows "vpGge p P 0 \<Longrightarrow> vpGge p (P div Q) 0"
proof (induction P rule: measure_induct_rule[where f = degree])
  case (less P)
  show ?case
  proof (cases "degree P < degree Q \<or> P = 0")
    case True
    hence "P div Q = 0" by (auto simp: div_poly_less)
    thus ?thesis by (simp add: vpGge_zero)
  next
    case False
    hence ge: "degree Q \<le> degree P" and P0: "P \<noteq> 0" by auto
    have Q0: "Q \<noteq> 0" using Q1 by auto
    define k where "k = degree P - degree Q"
    define c where "c = lead_coeff P"
    define P' where "P' = P - Polynomial.monom c k * Q"
    have c0: "c \<noteq> 0" using P0 by (simp add: c_def)
    have mi: "vpGge p (Polynomial.monom c k) 0"
      using less.prems unfolding vpGge_def c_def by (auto simp: coeff_monom split: if_splits)
    have "vpGge p (Polynomial.monom c k * Q) 0" using vpGge_mul[OF p mi Qi] by simp
    hence "vpGge p (P + - (Polynomial.monom c k * Q)) 0"
      by (intro vpGge_add[OF p less.prems] vpGge_neg)
    hence P'i: "vpGge p P' 0" by (simp add: P'_def)
    have d1: "degree (Polynomial.monom c k * Q) = degree P"
      using c0 Q0 ge by (simp add: degree_mult_eq degree_monom_eq k_def)
    have "Polynomial.coeff (Polynomial.monom c k * Q) (degree P) = c"
      using d1 Q1 by (metis lead_coeff_mult lead_coeff_monom mult_1_right)
    hence z: "Polynomial.coeff P' (degree P) = 0" unfolding P'_def by (simp add: c_def)
    have le: "degree P' \<le> degree P" unfolding P'_def using d1 by (intro degree_diff_le) auto
    have IH: "vpGge p (P' div Q) 0"
    proof (cases "P' = 0")
      case True
      thus ?thesis by (simp add: vpGge_zero)
    next
      case False
      hence "degree P' \<noteq> degree P" using z by (metis leading_coeff_0_iff)
      hence "degree P' < degree P" using le by simp
      thus ?thesis using less.IH P'i by blast
    qed
    have "P = P' + Polynomial.monom c k * Q" by (simp add: P'_def)
    hence "P div Q = Polynomial.monom c k + P' div Q"
      using Q0 by (metis div_mult_self1)
    thus ?thesis using vpGge_add[OF p mi IH] by simp
  qed
qed

text \<open>Division of an integral polynomial by an integral monic polynomial is integral
  (monicity written as @{text "lead_coeff Q = 1"};
    @{text monic} is not a constant in the base image).\<close>
lemma vpGge_div_monic:
  "prime p \<Longrightarrow> vpGge p P 0 \<Longrightarrow> lead_coeff Q = 1 \<Longrightarrow>
    vpGge p Q 0 \<Longrightarrow> vpGge p (P div Q) 0"
  by (rule vpGge_div_lead1)

lemma vge_poly_eval:
  "prime p \<Longrightarrow> vpGge p P 0 \<Longrightarrow> vge p x 0 \<Longrightarrow>
    vge p (poly P x) 0" unfolding poly_altdef
    by (auto simp: vpGge_iff intro!: vge_sum vge_mul[where a = 0 and b = 0, simplified] vge_pow)

subsection \<open>Valuations of powers and products\<close>

lemma vp_power_rat:
  assumes "prime p" "x \<noteq> 0"
  shows "vp p (x ^ n) = int n * vp p x"
proof -
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  show ?thesis
    by (induction n) (use assms(2) pe in \<open>simp_all add: vp_def qmultiplicity_mult
      algebra_simps\<close>)
qed


lemma vp_powi_rat:
  assumes "prime p" "x \<noteq> 0"
  shows "vp p (x powi k) = k * vp p x"
proof (cases "0 \<le> k")
  case True
  thus ?thesis using vp_power_rat[OF assms, of "nat k"] by (simp add: power_int_def)
next
  case False
  have "vp p (x powi k) = vp p (inverse x ^ nat (- k))" using False by (simp add: power_int_def)
  also have "\<dots> = int (nat (- k)) * vp p (inverse x)"
    using assms by (intro vp_power_rat) auto
  finally show ?thesis using False by (simp add: vp_def qmultiplicity_inverse)
qed


lemma vp_prod_rat:
  assumes "prime p" "finite I" "\<And>i. i \<in> I \<Longrightarrow> f i \<noteq> 0"
  shows "vp p (\<Prod> i \<in> I. f i) = (\<Sum> i \<in> I. vp p (f i))"
  using assms(2,3)
proof (induction I rule: finite_induct)
  case (insert x F)
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  have "(\<Prod> i \<in> F. f i) \<noteq> 0" using insert by simp
  thus ?case using insert pe by (simp add: vp_def qmultiplicity_mult)
qed (simp add: vp_def)


lemma vpGge_C_vp: "vpGge p [:c:] (of_int (vp p c))"
  by (rule vpGge_C) (simp add: vge_def)

text \<open>Composition with powers and with the identity polynomial @{term pX}.\<close>
lemma pcompose_power_left: "pcompose (p ^ n) q = (pcompose p q) ^ n" for p q :: "rat poly"
  by (induction n) (simp_all add: pcompose_mult pcompose_1)

lemma pcompose_pX: "pcompose pX q = q"
  by (simp add: monom_Suc pcompose_pCons pcompose_1)



text \<open>@{text "v_p(1/j) \<ge> -\<lfloor>log_p j\<rfloor>"}.\<close>
lemma vge_inv_nat: "prime p \<Longrightarrow> 1 \<le> j \<Longrightarrow>
  vge p (1 / of_nat j) (- of_nat (nat_log p j))"
proof -
  assume p: "prime p" and j: "1 \<le> j"
  have "p ^ multiplicity p j dvd j" by (rule multiplicity_dvd)
  hence "p ^ multiplicity p j \<le> j" using j by (intro dvd_imp_le) auto
  hence "Suc (multiplicity p j) \<le> floorlog p j"
    by (intro floorlog_geI) (use prime_gt_1_nat[OF p] in auto)
  hence "multiplicity p j \<le> nat_log p j" by (simp add: nat_log_def)
  thus ?thesis by (simp add: vge_def vp_def inverse_eq_divide[symmetric] multiplicity_int)
qed

lemma nat_log_mono: "m \<le> n \<Longrightarrow> nat_log p m \<le> nat_log p n"
  by (simp add: nat_log_def floorlog_mono diff_le_mono)

lemma vge_prod0: "prime p \<Longrightarrow> finite I \<Longrightarrow>
  (\<And>i. i \<in> I \<Longrightarrow> vge p (f i) 0) \<Longrightarrow>
  vge p (\<Prod> i \<in> I. f i) 0"
proof -
  assume p: "prime p" and I: "finite I" and hf: "\<And>i. i \<in> I \<Longrightarrow> vge p (f i) 0"
  show ?thesis using I hf
  proof (induction I rule: finite_induct)
    case empty
    show ?case using vge_one  by simp
  next
    case (insert x F)
    have "vge p (f x * (\<Prod> i \<in> F. f i)) (0 + 0)" using vge_mul[OF p] insert  by blast
    thus ?case using insert  by simp
  qed
qed

text \<open>Strict ultrametric inequality:
  @{text "v(a) < v(u) \<Longrightarrow> v(a + u) = v(a)"}.\<close>
lemma vp_add_eq_of_lt:
  "prime p \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> u \<noteq> 0 \<Longrightarrow>
    vp p a < vp p u \<Longrightarrow> a + u \<noteq> 0 \<and> vp p (a + u) = vp p a"
proof -
  assume p: "prime p" and a: "a \<noteq> 0" and u: "u \<noteq> 0" and lt: "vp p a < vp p u"
  have ne: "a + u \<noteq> 0"
  proof
    assume "a + u = 0"
    hence "- a = u" by (simp only: neg_eq_iff_add_eq_0)
    hence "vp p u = vp p a" by (auto simp: vp_def qmultiplicity_minus)
    thus False using lt by simp
  qed
  have "min (vp p a) (vp p u) \<le> vp p (a + u)" using qmultiplicity_add_ge[OF p a u ne]
    by (simp add: vp_def)
  moreover have "min (vp p (a + u)) (vp p u) \<le> vp p a"
    using qmultiplicity_add_ge[of p "a + u" "- u"] p a u ne
      by (simp add: vp_def qmultiplicity_minus)
  ultimately show ?thesis using lt ne by (auto simp: min_def split: if_splits)
qed

end
