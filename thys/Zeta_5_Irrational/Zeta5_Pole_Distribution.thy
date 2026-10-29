(*  Title:   Zeta5_Pole_Distribution.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Pole_Distribution
  imports Zeta5_Truncated_Expansions
begin

section \<open>The distribution formula (3.7) and Lemma 3.2\<close>

text \<open>Section 3.2 of the paper (Lean theory @{text Distribution}): a Raabe-type multiplication
  formula
  for \<open>\<tau>\<close> on polynomials, the sum over the residue classes \<open>a <
    p\<close> of the truncated pole values
  (by induction on the pole, with the truncation error controlled), compatibility of partial
  fractions with the substitution \<open>x =
    a + p z\<close>, and Lemma 3.2 (@{text tauX_distribution_formula}).\<close>

subsection \<open>Raabe's multiplication formula\<close>

lemma Lfun_uminus: "Lfun (- P) = - Lfun P"
  using Lfun_smult[of "- 1" P] by simp

lemma Lfun_sub: "Lfun (P - Q) = Lfun P - Lfun Q"
  by (simp only: diff_conv_add_uminus Lfun_add Lfun_uminus)

lemma Lfun_zero: "Lfun 0 = 0"
  using Lfun_smult[of 0 0] by simp

lemma Lfun_sum: "Lfun (\<Sum> i \<in> I. f i) = (\<Sum> i \<in> I. Lfun (f i))"
  by (induction I rule: infinite_finite_induct) (simp_all add: Lfun_add Lfun_zero)

lemma sum_const_poly: "(\<Sum> i \<in> I. [:f i:]) = [:\<Sum> i \<in> I. f i:]"
  by (induction I rule: infinite_finite_induct) simp_all

lemma Lfun_pX_pow: "Lfun (pX ^ n) = bernoulli n"
  by (simp only: pX_pow_monom Lfun_monom mult_1)

lemma Lfun_fwd_monom:
  "Lfun (pcompose (Polynomial.monom c n) (pX + 1) - Polynomial.monom c n) = (if n =
    1 then c else 0)"
proof -
  have m: "Polynomial.monom c n = Polynomial.smult c (pX ^ n)"
    unfolding pX_pow_monom by (simp add: smult_monom)
  have "Lfun (pcompose (Polynomial.monom c n) (pX + 1) - Polynomial.monom c n)
      = c * Lfun (pcompose (pX ^ n) (pX + 1) - pX ^ n)"
    unfolding m pcompose_smult smult_diff_right[symmetric] Lfun_smult ..
  also have "Lfun (pcompose (pX ^ n) (pX + 1) - pX ^ n) = (\<Sum> k <
    n. of_nat (n choose k) * bernoulli k)"
    unfolding pX_shift_pow_diff Lfun_sum Lfun_monom ..
  finally show ?thesis unfolding sum_binomial_bernoulli_lt by simp
qed

text \<open>@{text "L(f(x+1) - f(x)) = f'(0)"}: the defining recursion of the Bernoulli
  numbers.\<close>
lemma Lfun_fwd: "Lfun (pcompose f (pX + 1) - f) = poly (pderiv f) 0"
proof -
  define D where "D = degree f"
  define M where "M n = Polynomial.monom (Polynomial.coeff f n) n" for n
  have e: "(\<Sum> n \<le> D. M n) = f" unfolding D_def M_def by (rule poly_as_sum_of_monoms)
  have "Lfun (pcompose f (pX + 1) - f) = Lfun (pcompose (\<Sum> n \<le>
    D. M n) (pX + 1) - (\<Sum> n \<le> D. M n))"
    by (simp only: e)
  also have "\<dots> = Lfun (\<Sum> n \<le> D. (pcompose (M n) (pX + 1) - M n))"
    by (simp only: pcompose_sum sum_subtractf)
  also have "\<dots> = (\<Sum> n \<le> D. if n = 1 then Polynomial.coeff f n else 0)"
    by (simp only: Lfun_sum M_def Lfun_fwd_monom)
  also have "\<dots> = Polynomial.coeff f 1"
    by (cases "1 \<le> D") (auto simp: D_def coeff_eq_0)
  also have "\<dots> = poly (pderiv f) 0"
    by (simp add: poly_0_coeff_0 coeff_pderiv)
  finally show ?thesis .
qed

lemma pderiv_pcompose_affine:
  "pderiv (pcompose Q ([:a:] + [:c:] * pX)) =
    Polynomial.smult c (pcompose (pderiv Q) ([:a:] + [:c:] * pX))"
proof -
  have d: "pderiv ([:a:] + [:c:] * pX) = [:c:]"
    by (simp add: pderiv_add pderiv_smult pderiv_monom pderiv_pCons)
  show ?thesis unfolding pderiv_pcompose d by (simp add: mult.commute)
qed

lemma Lfun_raabe:
  "(\<Sum> a < p. Lfun (pcompose f ([:of_nat a:] + [:of_nat p:] * pX))) = of_nat p * Lfun f"
proof -
  obtain g where g: "pcompose g (pX + 1) - g = f" using exists_antidiff by blast
  define G where "G = pcompose g ([:of_nat p:] * pX)"
  have e: "\<And>a. pcompose f ([:of_nat a:] + [:of_nat p:] * pX) =
             pcompose g ([:of_nat (Suc a):] + [:of_nat p:] * pX) - pcompose g ([:of_nat a:] +
               [:of_nat p:] * pX)"
  proof -
    fix a :: nat
    have r: "pcompose (pX + 1) ([:of_nat a:] + [:of_nat p:] * pX) =
      [:of_nat (Suc a):] + [:of_nat p:] * pX"
      unfolding pcompose_add pcompose_pX pcompose_1 by (simp add: one_pCons)
    show "pcompose f ([:of_nat a:] + [:of_nat p:] * pX) =
             pcompose g ([:of_nat (Suc a):] + [:of_nat p:] * pX) - pcompose g ([:of_nat a:] +
               [:of_nat p:] * pX)"
      unfolding g[symmetric] pcompose_diff pcompose_assoc[symmetric] r ..
  qed
  have tel: "(\<Sum> a < p. Lfun (pcompose f ([:of_nat a:] + [:of_nat p:] * pX))) =
             Lfun (pcompose g ([:of_nat p:] + [:of_nat p:] * pX)) - Lfun (pcompose g ([:0:] +
               [:of_nat p:] * pX))"
    unfolding e Lfun_sub
    using sum_lessThan_telescope[of "\<lambda>a. Lfun (pcompose g ([:of_nat a:] + [:of_nat p:] *
      pX))" p] by simp
  have h1: "pcompose g ([:of_nat p:] + [:of_nat p:] * pX) = pcompose G (pX + 1)"
    and h2: "pcompose g ([:0:] + [:of_nat p:] * pX) = G"
  proof -
    have c: "pcompose ([:of_nat p:] * pX) (pX + 1) = [:of_nat p:] + [:of_nat p:] * pX"
      unfolding pcompose_mult pcompose_pX pcompose_const by (simp add: algebra_simps)
    show "pcompose g ([:of_nat p:] + [:of_nat p:] * pX) = pcompose G (pX + 1)"
      unfolding G_def pcompose_assoc[symmetric] c ..
    show "pcompose g ([:0:] + [:of_nat p:] * pX) = G"
      unfolding G_def by simp
  qed
  have "Lfun (pcompose G (pX + 1)) - Lfun G = poly (pderiv G) 0"
    by (simp only: Lfun_sub[symmetric] Lfun_fwd)
  also have "\<dots> = of_nat p * poly (pderiv g) 0"
    unfolding G_def using pderiv_pcompose_affine[of g 0 "of_nat p"]
      by (simp add: poly_pcompose poly_monom)
  also have "poly (pderiv g) 0 = Lfun f"
    by (simp only: g[symmetric] Lfun_fwd)
  finally show ?thesis using tel h1 h2 by simp
qed

lemma tau_raabe:
  "(\<Sum> a < p. tau (pcompose Q ([:of_nat a:] + [:of_nat p:] * pX))) = of_nat p ^ 4 * tau Q"
proof -
  have e: "\<And>a. tau (pcompose Q ([:of_nat a:] + [:of_nat p:] * pX)) =
             of_nat p ^ 3 * Lfun (pcompose ((pderiv ^^ 3) Q) ([:of_nat a:] + [:of_nat p:] * pX)) /
               24"
  proof -
    fix a :: nat
    have d: "(pderiv ^^ 3) (pcompose Q ([:of_nat a:] + [:of_nat p:] * pX)) =
        Polynomial.smult (of_nat p ^ 3) (pcompose ((pderiv ^^ 3) Q) ([:of_nat a:] + [:of_nat p:] *
          pX))"
      by (simp only: numeral_3_eq_3 funpow.simps o_apply id_apply pderiv_pcompose_affine
        pderiv_smult smult_smult)
        (simp add: mult_ac)
    show "tau (pcompose Q ([:of_nat a:] + [:of_nat p:] * pX)) =
             of_nat p ^ 3 * Lfun (pcompose ((pderiv ^^ 3) Q) ([:of_nat a:] + [:of_nat p:] * pX)) /
               24"
      unfolding tau_def d Lfun_smult ..
  qed
  have "(\<Sum> a < p. tau (pcompose Q ([:of_nat a:] + [:of_nat p:] * pX))) =
        of_nat p ^ 3 * (\<Sum> a < p. Lfun (pcompose ((pderiv ^^ 3) Q) ([:of_nat a:] +
          [:of_nat p:] * pX))) / 24"
    by (simp only: e sum_divide_distrib[symmetric] sum_distrib_left[symmetric])
  also have "\<dots> = of_nat p ^ 3 * (of_nat p * Lfun ((pderiv ^^ 3) Q)) / 24"
    by (simp only: Lfun_raabe)
  also have "\<dots> = of_nat p ^ 4 * tau Q"
    by (simp add: tau_def power4_eq_xxxx power3_eq_cube)
  finally show ?thesis .
qed

subsection \<open>Harmonic increments and the pole sums\<close>

lemma H5_dIdx_sub: "H5 (dIdx n) - H5 (dIdx (n - 1)) = (if n = 0 then 0 else 1 / of_int n ^ 5)"
proof -
  consider "n < 0" | "n = 0" | "n > 0" by linarith
  thus ?thesis
  proof cases
    case 1
    define j where "j = nat (- n)"
    have j0: "j \<noteq> 0" using 1 by (simp add: j_def)
    have jn: "of_nat j = (- of_int n :: rat)" using 1 by (simp add: j_def)
    have d: "dIdx n = j - 1" "dIdx (n - 1) = j" using 1
      by (auto simp: dIdx_def j_def nat_diff_distrib)
    have h: "H5 j = H5 (j - 1) + 1 / of_nat j ^ 5" by (rule H5_Suc_pred[OF j0])
    have i: "1 / of_nat j ^ 5 = - (1 / of_int n ^ 5 :: rat)" unfolding jn
      by (simp add: power_minus_odd)
    show ?thesis using 1 unfolding d by (simp add: h i)
  next
    case 2
    thus ?thesis by (simp add: dIdx_def)
  next
    case 3
    define j where "j = nat n"
    have j0: "j \<noteq> 0" using 3 by (simp add: j_def)
    have jn: "of_nat j = (of_int n :: rat)" using 3 by (simp add: j_def)
    have d: "dIdx n = j" "dIdx (n - 1) = j - 1" using 3
      by (auto simp: dIdx_def j_def nat_diff_distrib)
    have h: "H5 j = H5 (j - 1) + 1 / of_nat j ^ 5" by (rule H5_Suc_pred[OF j0])
    show ?thesis using 3 unfolding d by (simp add: h jn)
  qed
qed

text \<open>The scalar part of the truncated @{text "\<tau>_Y^{ext}(1/(z - n/p))"}.\<close>
definition phi_tr :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> rat" where
  "phi_tr p n M = (if int p dvd n then H5 (dIdx (n div int p)) - Cp_tr p M
                   else tauAnPole_tr p (of_int n / of_nat p) M)"

lemma vp_int_div_p: "prime p \<Longrightarrow> \<not> int p dvd n \<Longrightarrow>
  vp p (of_int n / of_nat p) = - 1 \<and> (of_int n / of_nat p :: rat) \<noteq> 0"
proof -
  assume p: "prime p" and nd: "\<not> int p dvd n"
  have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer)
  have n0: "n \<noteq> 0" using nd by auto
  have p0: "int p \<noteq> 0" using prime_gt_0_nat[OF p] by simp
  have "vp p (of_int n / of_nat p) = qmultiplicity (int p) (of_int n / of_int (int p))"
    by (simp add: vp_def)
  also have "\<dots> = int (multiplicity (int p) n) - int (multiplicity (int p) (int p))"
    by (rule qmultiplicity_divide_of_int[OF n0 p0 pe])
  also have "\<dots> = - 1" using nd pe by (simp add: not_dvd_imp_multiplicity_0 multiplicity_prime)
  finally show ?thesis using n0 p0 by simp
qed

lemma phi_tr_sub:
  assumes p: "prime p"
  shows "\<exists>M0. \<forall>M \<ge> M0. vge p (phi_tr p n M - phi_tr p (n - int p) M
                               - of_nat p ^ 5 * (H5 (dIdx n) - H5 (dIdx (n - 1)))) B"
proof (cases "int p dvd n")
  case True
  have "phi_tr p n M - phi_tr p (n - int p) M - of_nat p ^ 5 * (H5 (dIdx n) - H5 (dIdx (n - 1))) =
    0" for M
  proof -
    obtain m where m: "n = int p * m" using True by blast
    have p0: "int p \<noteq> 0" using prime_gt_0_nat[OF p] by simp
    have pq: "(of_nat p :: rat) \<noteq> 0" using prime_gt_0_nat[OF p] by simp
    have d1: "n div int p = m" using p0 by (simp add: m)
    have nm: "n - int p = int p * (m - 1)" by (simp add: m algebra_simps)
    have d2: "(n - int p) div int p = m - 1" using p0 by (simp add: nm)
    have "int p dvd (n - int p)" using True by simp
    with True have "phi_tr p n M - phi_tr p (n - int p) M = H5 (dIdx m) - H5 (dIdx (m - 1))"
      by (simp add: phi_tr_def d1 d2)
    also have "\<dots> = (if m = 0 then 0 else 1 / of_int m ^ 5)" by (rule H5_dIdx_sub)
    also have "\<dots> = of_nat p ^ 5 * (H5 (dIdx n) - H5 (dIdx (n - 1)))"
      unfolding H5_dIdx_sub using pq by (cases "m = 0") (simp_all add: m power_mult_distrib)
    finally show ?thesis by simp
  qed
  thus ?thesis by (auto simp: vge_zero)
next
  case False
  have nd': "\<not> int p dvd (n - int p)"
    by (metis False diff_add_cancel dvd_add dvd_refl)
  define s where "s = of_int n / (of_nat p :: rat)"
  have sv0: "vp p s = - 1" and s0: "s \<noteq> 0" using vp_int_div_p[OF p False] unfolding s_def
    by blast+
  have sv: "vp p s < 0" using sv0 by simp
  have s1: "of_int (n - int p) / of_nat p = s - 1"
    using prime_gt_0_nat[OF p] unfolding s_def by (simp add: diff_divide_distrib)
  have e: "\<And>M. phi_tr p n M - phi_tr p (n - int p) M - of_nat p ^ 5 * (H5 (dIdx n) -
    H5 (dIdx (n - 1))) =
             tauAnPole_tr p s M - tauAnPole_tr p (s - 1) M - s powi (- 5)"
  proof -
    fix M
    have n0: "n \<noteq> 0" using False by auto
    have a: "phi_tr p n M = tauAnPole_tr p s M" using False by (simp add: phi_tr_def s_def)
    have b: "phi_tr p (n - int p) M = tauAnPole_tr p (s - 1) M"
      by (simp only: phi_tr_def nd' if_False s1)
    have c: "of_nat p ^ 5 * (H5 (dIdx n) - H5 (dIdx (n - 1))) = s powi (- 5)"
      using n0 by (simp add: H5_dIdx_sub s_def power_int_minus power_divide)
    show "phi_tr p n M - phi_tr p (n - int p) M - of_nat p ^ 5 * (H5 (dIdx n) - H5 (dIdx (n - 1))) =
             tauAnPole_tr p s M - tauAnPole_tr p (s - 1) M - s powi (- 5)"
      by (simp only: a b c)
  qed
  show ?thesis unfolding e by (rule tauAnPole_tr_sub[OF p sv s0])
qed

definition Gsum_tr :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> rat" where
  "Gsum_tr p r M = (\<Sum> a < p. phi_tr p (r - int a) M)"

lemma Gsum_tr_step: "0 < p \<Longrightarrow>
  Gsum_tr p n M - Gsum_tr p (n - 1) M = phi_tr p n M - phi_tr p (n - int p) M"
proof -
  assume "0 < p"
  then obtain q where q: "p = Suc q" by (cases p) auto
  have A: "Gsum_tr p n M = phi_tr p n M + (\<Sum> a < q. phi_tr p (n - int (Suc a)) M)"
    unfolding Gsum_tr_def q sum.lessThan_Suc_shift by simp
  have B: "Gsum_tr p (n - 1) M = (\<Sum> a <
    q. phi_tr p (n - int (Suc a)) M) + phi_tr p (n - int p) M"
    unfolding Gsum_tr_def q sum.lessThan_Suc by (simp add: algebra_simps)
  show ?thesis unfolding A B by simp
qed

lemma Gsum_tr_zero: "prime p \<Longrightarrow> Gsum_tr p 0 M = 0"
proof -
  assume p: "prime p"
  have "1 < p" using p by (rule prime_gt_1_nat)
  then obtain q where q: "p = Suc q" by (cases p) auto
  have nd: "\<not> int p dvd - int a" if "0 < a" "a < p" for a
    using that by (auto dest: dvd_imp_le)
  have C: "Cp_tr p M = (\<Sum> a < q. tauAnPole_tr p (- of_nat (Suc a) / of_nat p) M)"
    unfolding Cp_tr_def q diff_Suc_1 image_Suc_lessThan[symmetric] sum.reindex[OF inj_Suc] o_def ..
  have "Gsum_tr p 0 M = phi_tr p 0 M + (\<Sum> a < q. phi_tr p (- int (Suc a)) M)"
    unfolding Gsum_tr_def q sum.lessThan_Suc_shift by simp
  also have "phi_tr p 0 M = - Cp_tr p M" by (simp add: phi_tr_def dIdx_def H5_def)
  also have "(\<Sum> a < q. phi_tr p (- int (Suc a)) M) = (\<Sum> a <
    q. tauAnPole_tr p (- of_nat (Suc a) / of_nat p) M)"
  proof (rule sum.cong[OF refl])
    fix a assume "a \<in> {..<q}"
    hence "\<not> int p dvd - int (Suc a)" using nd[of "Suc a"] q by simp
    thus "phi_tr p (- int (Suc a)) M = tauAnPole_tr p (- of_nat (Suc a) / of_nat p) M"
      by (simp add: phi_tr_def)
  qed
  finally show ?thesis using C by simp
qed

lemma Gsum_tr_eq:
  assumes p: "prime p"
  shows "\<exists>M0. \<forall>M \<ge> M0. vge p (Gsum_tr p r M - of_nat p ^ 5 * H5 (dIdx r)) B"
proof -
  have step: "\<And>n. \<exists>M0. \<forall>M \<ge>
    M0. vge p ((Gsum_tr p n M - of_nat p ^ 5 * H5 (dIdx n)) -
                                      (Gsum_tr p (n - 1) M - of_nat p ^ 5 * H5 (dIdx (n - 1)))) B"
  proof -
    fix n
    obtain M0 where M0: "\<forall>M \<ge>
      M0. vge p (phi_tr p n M - phi_tr p (n - int p) M - of_nat p ^ 5 * (H5 (dIdx n) - H5 (dIdx (n -
      1)))) B"
      using phi_tr_sub[OF p] by blast
    have eq: "(Gsum_tr p n M - of_nat p ^ 5 * H5 (dIdx n)) - (Gsum_tr p (n - 1) M - of_nat p ^ 5 *
      H5 (dIdx (n - 1))) =
              phi_tr p n M - phi_tr p (n - int p) M - of_nat p ^ 5 * (H5 (dIdx n) - H5 (dIdx (n -
                1)))" for M
      using Gsum_tr_step[OF prime_gt_0_nat[OF p], of n M] by (simp add: algebra_simps)
    show "\<exists>M0. \<forall>M \<ge> M0. vge p ((Gsum_tr p n M - of_nat p ^ 5 * H5 (dIdx n)) -
                                      (Gsum_tr p (n - 1) M - of_nat p ^ 5 * H5 (dIdx (n - 1)))) B"
      unfolding eq using M0 by blast
  qed
  have base: "\<And>M. Gsum_tr p 0 M - of_nat p ^ 5 * H5 (dIdx 0) = 0"
    by (simp add: Gsum_tr_zero[OF p] dIdx_def H5_def)
  define D where "D r M = Gsum_tr p r M - of_nat p ^ 5 * H5 (dIdx r)" for r M
  have stepD: "\<And>n. \<exists>M0. \<forall>M \<ge> M0. vge p (D n M - D (n - 1) M) B"
    unfolding D_def by (rule step)
  have baseD: "\<And>M. D 0 M = 0" unfolding D_def by (rule base)
  have "\<exists>M0. \<forall>M \<ge> M0. vge p (D r M) B"
  proof (rule int_induct[where k = 0 and P = "\<lambda>r. \<exists>M0. \<forall>M \<ge>
    M0. vge p (D r M) B"])
    show "\<exists>M0. \<forall>M \<ge> M0. vge p (D 0 M) B" by (simp add: baseD vge_zero)
  next
    fix i :: int assume "0 \<le> i" and "\<exists>M0. \<forall>M \<ge> M0. vge p (D i M) B"
    then obtain M1 where M1: "\<forall>M \<ge> M1. vge p (D i M) B" by blast
    obtain M2 where M2: "\<forall>M \<ge> M2. vge p (D (i + 1) M - D i M) B"
      using stepD[of "i + 1"] by auto
    show "\<exists>M0. \<forall>M \<ge> M0. vge p (D (i + 1) M) B"
    proof (intro exI[of _ "max M1 M2"] allI impI)
      fix M assume "max M1 M2 \<le> M"
      hence a: "vge p (D i M) B" and b: "vge p (D (i + 1) M - D i M) B" using M1 M2 by auto
      show "vge p (D (i + 1) M) B" using vge_add[OF p b a] by simp
    qed
  next
    fix i :: int assume "i \<le> 0" and "\<exists>M0. \<forall>M \<ge> M0. vge p (D i M) B"
    then obtain M1 where M1: "\<forall>M \<ge> M1. vge p (D i M) B" by blast
    obtain M2 where M2: "\<forall>M \<ge> M2. vge p (D i M - D (i - 1) M) B" using stepD[of i]
      by auto
    show "\<exists>M0. \<forall>M \<ge> M0. vge p (D (i - 1) M) B"
    proof (intro exI[of _ "max M1 M2"] allI impI)
      fix M assume "max M1 M2 \<le> M"
      hence a: "vge p (D i M) B" and b: "vge p (D i M - D (i - 1) M) B" using M1 M2 by auto
      show "vge p (D (i - 1) M) B" using vge_add[OF p a vge_neg[OF b]] by simp
    qed
  qed
  thus ?thesis by (simp only: D_def)
qed

subsection \<open>The pole values of @{text "\<tau>^{ext}_Y"} on the distributed poles\<close>

lemma quotient_of_int_div_prime:
  assumes "prime p" "\<not> int p dvd n"
  shows "snd (quotient_of (of_int n / of_nat p)) \<noteq> 1"
  using far_denom_ne_1[OF assms(1) conjunct1[OF vp_int_div_p[OF assms]]] .

lemma tauPoleP_tr_int_div:
  assumes "prime p"
  shows "tauPoleP_tr p (Yp_tr p M) (of_int n / of_nat p) M =
         [:phi_tr p n M:] - (if int p dvd n then [:of_nat p ^ 5:] * pX else 0)"
proof (cases "int p dvd n")
  case True
  then obtain m where m: "n = int p * m" by blast
  have p0: "int p \<noteq> 0" using prime_gt_0_nat[OF assms] by simp
  have pq: "(of_nat p :: rat) \<noteq> 0" using prime_gt_0_nat[OF assms] by simp
  have e: "of_int n / of_nat p = (of_int m :: rat)" using pq by (simp add: m)
  have d: "n div int p = m" using p0 by (simp add: m)
  show ?thesis unfolding e tauPoleP_tr_near using True
    by (simp add: phi_tr_def d Yp_tr_def algebra_simps)
next
  case False
  show ?thesis using False tauPoleP_tr_far[OF assms conjunct1[OF vp_int_div_p[OF assms False]]]
    by (simp add: phi_tr_def)
qed

lemma sum_tauPoleP_tr:
  assumes p: "prime p"
  shows "\<exists>M0. \<forall>M \<ge> M0.
    vpGge p ((\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
             - [:of_nat p ^ 5:] * ([:H5 (dIdx r):] - pX)) B"
proof -
  have e: "\<And>M. (\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M) =
             [:Gsum_tr p r M:] - [:of_nat p ^ 5:] * pX"
  proof -
    fix M
    have p0: "0 < p" using p by (rule prime_gt_0_nat)
    have c: "(of_int r - of_nat a) / of_nat p = (of_int (r - int a) / of_nat p :: rat)" for a
      by simp
    have iff: "int p dvd (r - int a) \<longleftrightarrow> a = nat (r mod int p)" if "a < p" for a
    proof -
      have "int a mod int p = int a" using that by simp
      hence "int p dvd (r - int a) \<longleftrightarrow> r mod int p = int a"
        using mod_eq_dvd_iff[of r "int p" "int a"] by simp
      also have "\<dots> \<longleftrightarrow> a = nat (r mod int p)"
        using pos_mod_sign[of "int p" r] p0 by auto
      finally show ?thesis .
    qed
    have lt: "nat (r mod int p) < p" using pos_mod_bound[of "int p" r] pos_mod_sign[of "int p" r] p0
      by (simp add: nat_less_iff)
    have "(\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M) =
          (\<Sum> a < p. [:phi_tr p (r - int a) M:] - (if int p dvd (r -
            int a) then [:of_nat p ^ 5:] * pX else 0))"
      unfolding c tauPoleP_tr_int_div[OF p] ..
    also have "\<dots> = (\<Sum> a < p. [:phi_tr p (r - int a) M:]) - (\<Sum> a <
      p. (if int p dvd (r - int a) then [:of_nat p ^ 5:] * pX else 0))"
      by (rule sum_subtractf)
    also have "(\<Sum> a < p. [:phi_tr p (r - int a) M:]) = [:Gsum_tr p r M:]"
      unfolding Gsum_tr_def sum_const_poly ..
    also have "(\<Sum> a < p. (if int p dvd (r - int a) then [:of_nat p ^ 5:] * pX else 0)) =
               (\<Sum> a < p. (if a = nat (r mod int p) then [:of_nat p ^ 5:] * pX else 0))"
      by (rule sum.cong[OF refl]) (simp add: iff)
    also have "\<dots> = [:of_nat p ^ 5:] * pX" using lt
      by (simp only: sum.delta finite_lessThan lessThan_iff if_True)
    finally show "(\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M) =
             [:Gsum_tr p r M:] - [:of_nat p ^ 5:] * pX" .
  qed
  from Gsum_tr_eq[OF p, of r B] obtain M0 where M0: "\<forall>M \<ge>
    M0. vge p (Gsum_tr p r M - of_nat p ^ 5 * H5 (dIdx r)) B" by blast
  show ?thesis
  proof (intro exI[of _ M0] allI impI)
    fix M assume "M0 \<le> M"
    hence v: "vge p (Gsum_tr p r M - of_nat p ^ 5 * H5 (dIdx r)) B" using M0 by blast
    have eq: "[:Gsum_tr p r M:] - [:of_nat p ^ 5:] * pX - [:of_nat p ^ 5:] * ([:H5 (dIdx r):] -
      pX) =
              [:Gsum_tr p r M - of_nat p ^ 5 * H5 (dIdx r):]"
      by (simp add: algebra_simps)
    show "vpGge p ((\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
                   - [:of_nat p ^ 5:] * ([:H5 (dIdx r):] - pX)) B"
      unfolding e eq by (rule vpGge_C[OF v])
  qed
qed

subsection \<open>Partial fractions and the substitution @{text "x = a + p z"}\<close>

text \<open>@{text "\<tau>^{ext}"} of a rational function given
  by an explicit partial fraction decomposition.\<close>
lemma tauExt_tr_decomp:
  assumes "finite S" "inj_on f S"
    and "U = Q' * qPoleProd (f ` S) + (\<Sum> r \<in> S. [:\<rho> r:] * qPoleProd (f ` (S - {r})))"
  shows "tauExt_tr p Y U (f ` S) M = [:tau Q':] + (\<Sum> r \<in>
    S. [:\<rho> r:] * tauPoleP_tr p Y (f r) M)"
proof -
  note S = assms(1) and inj = assms(2) and U = assms(3)
  define Pi where "Pi = qPoleProd (f ` S)"
  define R where "R = (\<Sum> r \<in> S. [:\<rho> r:] * qPoleProd (f ` (S - {r})))"
  have fS: "finite (f ` S)" using S by simp
  have Pi0: "Pi \<noteq> 0" using qPoleProd_monic[OF fS] by (auto simp: Pi_def)
  have dPi: "degree Pi = card S" unfolding Pi_def degree_qPoleProd[OF fS] using card_image[OF inj] .
  have cardr: "card (f ` (S - {r})) = card S - 1" if "r \<in> S" for r
    using card_image[OF inj_on_subset[OF inj, of "S - {r}"]] S that by auto
  have RdivPi: "R div Pi = 0"
  proof (cases "S = {}")
    case True thus ?thesis by (simp add: R_def)
  next
    case False
    have cS: "0 < card S" using S False by (simp add: card_gt_0_iff)
    have "degree R \<le> card S - 1"
      unfolding R_def
    proof (rule degree_sum_le[OF S])
      fix r assume r: "r \<in> S"
      have "degree ([:\<rho> r:] * qPoleProd (f ` (S - {r}))) \<le>
        degree (qPoleProd (f ` (S - {r})))"
        by (simp add: degree_smult_le)
      also have "\<dots> = card S - 1" using S r by (simp add: degree_qPoleProd cardr)
      finally show "degree ([:\<rho> r:] * qPoleProd (f ` (S - {r}))) \<le> card S - 1" .
    qed
    hence "degree R < degree Pi" using cS dPi by simp
    thus ?thesis by (rule div_poly_less)
  qed
  have div: "U div qPoleProd (f ` S) = Q'"
    unfolding U Pi_def[symmetric] R_def[symmetric] using Pi0 RdivPi by simp
  have res: "qRes (f ` S) U (f r) = \<rho> r" if r: "r \<in> S" for r
  proof -
    have img: "f ` S - {f r} = f ` (S - {r})" using inj r by (auto simp: inj_on_def)
    have "f r \<notin> f ` (S - {r})" using inj r by (auto simp: inj_on_def)
    with S have den: "(\<Prod> t \<in> f ` (S - {r}). f r - t) \<noteq> 0"
      by (auto simp: prod_zero_iff)
    have z: "poly (qPoleProd (f ` S)) (f r) = 0" using S r
      by (auto simp: poly_qPoleProd prod_zero_iff)
    have z2: "poly (qPoleProd (f ` (S - {r'}))) (f r) = 0" if "r' \<in> S" "r' \<noteq> r" for r'
      using S r that by (auto simp: poly_qPoleProd prod_zero_iff)
    have "poly U (f r) = (\<Sum> r' \<in> S. \<rho> r' * poly (qPoleProd (f ` (S - {r'}))) (f r))"
      unfolding U using z by (simp add: poly_sum)
    also have "\<dots> = \<rho> r * poly (qPoleProd (f ` (S - {r}))) (f r) + (\<Sum> r' \<in>
      S - {r}. \<rho> r' * poly (qPoleProd (f ` (S - {r'}))) (f r))"
      by (rule sum.remove[OF S r])
    also have "(\<Sum> r' \<in> S - {r}. \<rho> r' * poly (qPoleProd (f ` (S - {r'}))) (f r)) = 0"
      using z2 by (intro sum.neutral) auto
    also have "poly (qPoleProd (f ` (S - {r}))) (f r) = (\<Prod> t \<in> f ` (S - {r}). f r - t)"
      by (rule poly_qPoleProd)
    finally show ?thesis using den unfolding qRes_def img by simp
  qed
  have "tauExt_tr p Y U (f ` S) M = [:tauK Q':] + (\<Sum> s \<in>
    f ` S. [:qRes (f ` S) U s:] * tauPoleP_tr p Y s M)"
    unfolding tauExt_tr_def div ..
  also have "(\<Sum> s \<in> f ` S. [:qRes (f ` S) U s:] * tauPoleP_tr p Y s M) = (\<Sum> r \<in>
    S. [:qRes (f ` S) U (f r):] * tauPoleP_tr p Y (f r) M)"
    by (simp only: sum.reindex[OF inj] o_def)
  also have "\<dots> = (\<Sum> r \<in> S. [:\<rho> r:] * tauPoleP_tr p Y (f r) M)"
    by (rule sum.cong[OF refl]) (simp add: res)
  finally show ?thesis by (simp only: tauK_eq_tau)
qed

lemma distrib_inj: "0 < p \<Longrightarrow>
  inj (\<lambda>r. (of_int r - of_nat a) / (of_nat p :: rat))"
  by (auto simp: inj_def)

text \<open>@{text "(\<Prod>_{r\<in>T}(x - r))(a + p z) =
  p^{|T|} \<Prod>_{r\<in>T}(z - (r - a)/p)"}.\<close>
lemma linPoleProd_distrib:
  assumes "0 < p" "finite T"
  shows "pcompose (linPoleProd T) ([:of_nat a:] + [:of_nat p:] * pX) =
         Polynomial.smult (of_nat p ^ card T) (qPoleProd (distribPoles p T a))"
proof -
  have p0: "(of_nat p :: rat) \<noteq> 0" using assms(1) by simp
  have inj: "inj_on (\<lambda>r. (of_int r - of_nat a) / (of_nat p :: rat)) T"
    using distrib_inj[OF assms(1), of a] by (simp add: inj_on_def inj_def)
  have X: "pX = [:0, 1:]" by (simp add: monom_Suc)
  have fac: "pcompose (pX - [:of_int r:]) ([:of_nat a:] + [:of_nat p:] * pX) =
             [:of_nat p:] * (pX - [:(of_int r - of_nat a) / of_nat p:])" for r
    unfolding X using p0 by (simp add: pcompose_pCons algebra_simps)
  have "pcompose (linPoleProd T) ([:of_nat a:] + [:of_nat p:] * pX) =
        (\<Prod> r \<in> T. [:of_nat p:] * (pX - [:(of_int r - of_nat a) / of_nat p:]))"
    unfolding linPoleProd_def pcompose_prod fac ..
  also have "\<dots> = [:of_nat p:] ^ card T * (\<Prod> r \<in>
    T. pX - [:(of_int r - of_nat a) / of_nat p:])"
    by (simp only: prod.distrib prod_constant)
  also have "(\<Prod> r \<in> T. pX - [:(of_int r - of_nat a) / of_nat p:]) =
    qPoleProd (distribPoles p T a)"
    unfolding qPoleProd_def distribPoles_def prod.reindex[OF inj] o_def ..
  finally show ?thesis by (simp add: const_poly_power)
qed

lemma summand_eq:
  assumes p: "prime p" and S: "finite S"
  shows "tauExt_tr p Y (distribNum p S P a) (distribPoles p S a) M =
         [:tau (pcompose (P div linPoleProd S) ([:of_nat a:] + [:of_nat p:] * pX)):]
         + (\<Sum> r \<in> S. [:linResidue S P r / of_nat p:] * tauPoleP_tr p Y ((of_int r -
           of_nat a) / of_nat p) M)"
proof -
  define Q where "Q = P div linPoleProd S"
  define f where "f = (\<lambda>r. (of_int r - of_nat a) / (of_nat p :: rat))"
  have p0: "0 < p" using p by (rule prime_gt_0_nat)
  have inj: "inj_on f S" using distrib_inj[OF p0, of a] by (simp add: f_def inj_on_def)
  have P: "P = Q * linPoleProd S + (\<Sum> r \<in> S. [:linResidue S P r:] * linPoleProd (S - {r}))"
    unfolding Q_def by (rule div_mult_mod_eq[of P "linPoleProd S", unfolded mod_linPoleProd[OF S],
      symmetric])
  have U: "distribNum p S P a = pcompose Q ([:of_nat a:] + [:of_nat p:] * pX) * qPoleProd (f ` S)
             + (\<Sum> r \<in> S. [:linResidue S P r / of_nat p:] * qPoleProd (f ` (S - {r})))"
  proof -
    define R where "R = [:of_nat a:] + [:of_nat p:] * pX"
    define c where "c = (of_nat p :: rat) powi (- int (card S))"
    have pq: "(of_nat p :: rat) \<noteq> 0" using p0 by simp
    have dS: "distribPoles p T a = f ` T" for T by (simp add: distribPoles_def f_def)
    have c1: "c * of_nat p ^ card S = 1" using pq by (simp add: c_def power_int_minus)
    have c2: "c * of_nat p ^ card (S - {r}) = 1 / of_nat p" if r: "r \<in> S" for r
    proof -
      have cS: "card S = Suc (card (S - {r}))" by (rule card.remove[OF S r])
      have "c * of_nat p ^ card (S - {r}) * of_nat p = 1" using c1 unfolding cS
        by (simp add: mult_ac)
      thus ?thesis using pq by (simp add: field_simps)
    qed
    have e1: "pcompose P R = pcompose Q R * pcompose (linPoleProd S) R +
                (\<Sum> r \<in> S. [:linResidue S P r:] * pcompose (linPoleProd (S - {r})) R)"
    proof -
      have "pcompose P R = pcompose (Q * linPoleProd S + (\<Sum> r \<in>
        S. [:linResidue S P r:] * linPoleProd (S - {r}))) R"
        by (rule arg_cong[where f = "\<lambda>x. pcompose x R", OF P])
      thus ?thesis by (simp only: pcompose_add pcompose_mult pcompose_sum pcompose_const)
    qed
    have L1: "pcompose (linPoleProd S) R = Polynomial.smult (of_nat p ^ card S) (qPoleProd (f ` S))"
      unfolding R_def dS[symmetric] by (rule linPoleProd_distrib[OF p0 S])
    have L2: "pcompose (linPoleProd (S - {r})) R =
      Polynomial.smult (of_nat p ^ card (S - {r})) (qPoleProd (f ` (S - {r})))" for r
      unfolding R_def dS[symmetric] by (rule linPoleProd_distrib[OF p0 finite_Diff[OF S]])
    have h1: "[:c:] * (A * Polynomial.smult k B) = Polynomial.smult (c * k) (A * B)"
      for A B :: "rat poly" and k
      by (simp add: mult_ac)
    have h2: "[:c:] * ([:x:] * Polynomial.smult k B) = [:x * (c * k):] * B"
      for B :: "rat poly" and x k
      by (simp add: mult_ac)
    have "distribNum p S P a = [:c:] * pcompose P R" unfolding distribNum_def c_def R_def ..
    also have "\<dots> = [:c:] * (pcompose Q R *
      Polynomial.smult (of_nat p ^ card S) (qPoleProd (f ` S)))
         + (\<Sum> r \<in> S. [:c:] * ([:linResidue S P r:] * Polynomial.smult (of_nat p ^ card (S -
           {r})) (qPoleProd (f ` (S - {r})))))"
      unfolding e1 L1 L2 distrib_left sum_distrib_left ..
    also have "\<dots> = pcompose Q R * qPoleProd (f ` S) + (\<Sum> r \<in>
      S. [:linResidue S P r / of_nat p:] * qPoleProd (f ` (S - {r})))"
    proof -
      have "(\<Sum> r \<in> S. [:c:] * ([:linResidue S P r:] *
        Polynomial.smult (of_nat p ^ card (S - {r})) (qPoleProd (f ` (S - {r})))))
          = (\<Sum> r \<in> S. [:linResidue S P r / of_nat p:] * qPoleProd (f ` (S - {r})))"
      proof (rule sum.cong[OF refl])
        fix r assume r: "r \<in> S"
        show "[:c:] * ([:linResidue S P r:] * Polynomial.smult (of_nat p ^ card (S -
          {r})) (qPoleProd (f ` (S - {r})))) =
              [:linResidue S P r / of_nat p:] * qPoleProd (f ` (S - {r}))"
          unfolding h2 c2[OF r] by simp
      qed
      thus ?thesis unfolding h1 c1 smult_1_left by simp
    qed
    finally show ?thesis unfolding R_def .
  qed
  have "tauExt_tr p Y (distribNum p S P a) (f ` S) M =
        [:tau (pcompose Q ([:of_nat a:] + [:of_nat p:] * pX)):] + (\<Sum> r \<in>
          S. [:linResidue S P r / of_nat p:] * tauPoleP_tr p Y (f r) M)"
    by (rule tauExt_tr_decomp[OF S inj U])
  thus ?thesis by (simp add: f_def Q_def distribPoles_def)
qed

subsection \<open>Lemma 3.2\<close>

lemma finite_eventually_all:
  assumes "finite S" "\<And>r. r \<in> S \<Longrightarrow>
    \<exists>M0::nat. \<forall>M \<ge> M0. Q r M"
  shows "\<exists>M0. \<forall>r \<in> S. \<forall>M \<ge> M0. Q r M"
  using assms
proof (induction S rule: finite_induct)
  case empty thus ?case by simp
next
  case (insert x F)
  obtain M1 where M1: "\<forall>r \<in> F. \<forall>M \<ge> M1. Q r M" using insert by blast
  obtain M2 where M2: "\<forall>M \<ge> M2. Q x M" using insert.prems by blast
  show ?case by (rule exI[of _ "max M1 M2"]) (use M1 M2 in auto)
qed

lemma C_mul_diff_C_mul: "[:c:] * (X - [:k:] * T) = [:c:] * X - [:c * k:] * (T :: rat poly)"
  by (simp add: smult_diff_right)

lemma distribution_formula_aux:
  fixes c k t :: rat and A :: "rat poly" and x :: "'a \<Rightarrow> rat" and T :: "'a \<Rightarrow>
    rat poly"
  assumes ck: "c * k = 1"
  shows "[:t:] + (\<Sum> r \<in> S. [:x r:] * T r) - [:c:] * ([:k * t:] + A) =
         - [:c:] * (A - (\<Sum> r \<in> S. [:x r * k:] * T r))"
proof -
  have 3: "y * k * c = y" for y using ck
    by (metis mult.commute mult.left_commute mult.right_neutral)
  have 1: "[:c:] * [:k * t:] = [:t:]" using ck
    by (simp add: mult.assoc[symmetric] mult.commute[of k c])
  have 2: "[:c:] * (\<Sum> r \<in> S. [:x r * k:] * T r) = (\<Sum> r \<in> S. [:x r:] * T r)"
    unfolding sum_distrib_left by (rule sum.cong[OF refl]) (simp add: 3)
  have "[:t:] + (\<Sum> r \<in> S. [:x r:] * T r) - [:c:] * ([:k * t:] + A) = (\<Sum> r \<in>
    S. [:x r:] * T r) - [:c:] * A"
    unfolding distrib_left 1 by simp
  also have "\<dots> = - [:c:] * (A - (\<Sum> r \<in> S. [:x r * k:] * T r))"
    by (simp only: mult_minus_left right_diff_distrib 2 minus_diff_eq)
  finally show ?thesis .
qed

text \<open>@{text "\<tau>_X(g) = p^{-4} \<Sum>_{a<p} \<tau>_Y^{ext}(g(a + p x))"} with
  @{text "Y = p^5X + C_p"}
  (Lean: @{text "lemma_3_2'"}); the truncated right-hand side agrees with the left-hand side modulo
    any
  prescribed power of @{text p} once @{text M} is large.\<close>
theorem tauX_distribution_formula:
  assumes p: "prime p" and p7: "7 \<le> p" and S: "finite S"
  shows "\<exists>M0. \<forall>M \<ge> M0.
    vpGge p (tauX S P - [:of_nat p powi (- 4):] *
               (\<Sum> a < p. tauExt_tr p (Yp_tr p M) (distribNum p S P a) (distribPoles p S a) M))
                 B"
proof -
  define Q where "Q = P div linPoleProd S"
  define res where "res = linResidue S P"
  have p0: "(of_nat p :: rat) \<noteq> 0" using p by (simp add: prime_gt_0_nat)
  \<comment> \<open>the right-hand side, rearranged with @{text "summand_eq"} and Raabe\<close>
  have rhs: "\<And>M. (\<Sum> a < p. tauExt_tr p (Yp_tr p M) (distribNum p S P a) (distribPoles p S
    a) M) =
      [:of_nat p ^ 4 * tau Q:] + (\<Sum> r \<in> S. [:res r / of_nat p:] *
          (\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M))"
    unfolding summand_eq[OF p S] sum.distrib sum_const_poly tau_raabe Q_def[symmetric]
      res_def[symmetric]
    by (subst sum.swap) (simp only: sum_distrib_left)
  \<comment> \<open>the pole parts converge to @{text "[:res r * p^4:] * tauPole r"}\<close>
  have pole: "\<And>r B'. r \<in> S \<Longrightarrow> \<exists>M0. \<forall>M \<ge> M0.
      vpGge p ([:res r / of_nat p:] * (\<Sum> a <
        p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
               - [:res r * of_nat p ^ 4:] * tauPole r) B'"
  proof -
    fix r B' assume r: "r \<in> S"
    define c where "c = res r / of_nat p"
    obtain M0 where M0: "\<forall>M \<ge> M0. vpGge p ((\<Sum> a <
      p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
             - [:of_nat p ^ 5:] * ([:H5 (dIdx r):] - pX)) (B' - of_int (vp p c))"
      using sum_tauPoleP_tr[OF p, of r "B' - of_int (vp p c)"] by blast
    have k: "c * of_nat p ^ 5 = res r * of_nat p ^ 4" unfolding c_def using p0
      by (simp add: field_simps eval_nat_numeral)
    have e: "[:c:] * (X - [:of_nat p ^ 5:] * ([:H5 (dIdx r):] - pX)) =
      [:res r / of_nat p:] * X - [:res r * of_nat p ^ 4:] * tauPole r" for X
      unfolding C_mul_diff_C_mul k unfolding c_def tauPole_def ..
    show "\<exists>M0. \<forall>M \<ge> M0.
      vpGge p ([:res r / of_nat p:] * (\<Sum> a <
        p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
               - [:res r * of_nat p ^ 4:] * tauPole r) B'"
    proof (intro exI[of _ M0] allI impI)
      fix M assume M: "M0 \<le> M"
      have v: "vpGge p ([:c:] * ((\<Sum> a <
        p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
             - [:of_nat p ^ 5:] * ([:H5 (dIdx r):] - pX))) (of_int (vp p c) + (B' -
               of_int (vp p c)))"
        using vpGge_mul[OF p vpGge_C_vp M0[rule_format, OF M]] .
      show "vpGge p ([:res r / of_nat p:] * (\<Sum> a <
        p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
               - [:res r * of_nat p ^ 4:] * tauPole r) B'"
        using v[unfolded e] by simp
    qed
  qed
  have "\<exists>M0. \<forall>r \<in> S. \<forall>M \<ge> M0. vpGge p ([:res r / of_nat p:] *
      (\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
      - [:res r * of_nat p ^ 4:] * tauPole r) (B + 4)"
    by (rule finite_eventually_all[OF S]) (rule pole)
  then obtain M0 where M0: "\<And>r M. r \<in> S \<Longrightarrow> M0 \<le> M \<Longrightarrow>
    vpGge p ([:res r / of_nat p:] *
      (\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
      - [:res r * of_nat p ^ 4:] * tauPole r) (B + 4)" by blast
  show ?thesis
  proof (intro exI[of _ M0] allI impI)
    fix M assume M: "M0 \<le> M"
    have lhs: "tauX S P = [:tau Q:] + (\<Sum> r \<in> S. [:res r:] * tauPole r)"
      by (simp add: tauX_def Q_def res_def)
    have diff: "tauX S P - [:of_nat p powi (- 4):] *
        (\<Sum> a < p. tauExt_tr p (Yp_tr p M) (distribNum p S P a) (distribPoles p S a) M) =
        - [:of_nat p powi (- 4):] * (\<Sum> r \<in> S. [:res r / of_nat p:] *
          (\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
          - [:res r * of_nat p ^ 4:] * tauPole r)"
      unfolding lhs rhs sum_subtractf
      by (rule distribution_formula_aux) (use p0 in \<open>simp add: power_int_minus\<close>)
    have "vpGge p (\<Sum> r \<in> S. [:res r / of_nat p:] *
          (\<Sum> a < p. tauPoleP_tr p (Yp_tr p M) ((of_int r - of_nat a) / of_nat p) M)
          - [:res r * of_nat p ^ 4:] * tauPole r) (B + 4)"
      by (rule vpGge_sum[OF p S]) (rule M0[OF _ M])
    moreover have "vpGge p (- [:of_nat p powi (- 4):]) (- 4)"
      by (rule vpGge_neg, rule vpGge_C) (simp add: vge_def vp_def qmultiplicity_power_int[OF p])
    ultimately show "vpGge p (tauX S P - [:of_nat p powi (- 4):] *
        (\<Sum> a < p. tauExt_tr p (Yp_tr p M) (distribNum p S P a) (distribPoles p S a) M)) B"
      unfolding diff using vpGge_mul[OF p] by fastforce
  qed
qed

end
