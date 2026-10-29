(*  Title:   Zeta5_Functionals.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Functionals
  imports Zeta5_Definitions
begin

section \<open>The functionals \<open>\<mu>\<^sub>X\<close> and \<open>\<tau>\<^sub>X\<close>:
  algebra and partial fractions\<close>

text \<open>Well-definedness (a common factor of numerator and pole product cancels), linearity, the
  Lagrange partial-fraction decomposition,
    \<open>\<tau>\<close> on polynomials and the pullback identity (3.1) of
  the paper.  Corresponds to the Lean theories @{text Functionals} and parts of
    @{text Distribution}.\<close>

subsection \<open>Linearity\<close>

lemma muPoly_eq_sum:
  assumes "degree P \<le> N"
  shows "muPoly P = (\<Sum> e \<le> N. Polynomial.coeff P e * muMono e)"
  unfolding muPoly_def
  by (rule sum.mono_neutral_left) (use assms in \<open>auto simp: coeff_eq_0\<close>)

lemma muPoly_add: "muPoly (P + Q) = muPoly P + muPoly Q"
proof -
  define N where "N = max (degree P) (degree Q)"
  have "degree (P + Q) \<le> N" "degree P \<le> N" "degree Q \<le> N"
    using degree_add_le_max[of P Q] by (auto simp: N_def)
  thus ?thesis by (simp add: muPoly_eq_sum[of _ N] sum.distrib algebra_simps)
qed

lemma muPoly_smult: "muPoly (Polynomial.smult c P) = c * muPoly P"
  using degree_smult_le[of c P]
  by (simp add: muPoly_eq_sum[of _ "degree P"] sum_distrib_left mult.assoc)

lemma Lfun_eq_sum:
  assumes "degree P \<le> N"
  shows "Lfun P = (\<Sum> k \<le> N. Polynomial.coeff P k * bernoulli k)"
  unfolding Lfun_def
  by (rule sum.mono_neutral_left) (use assms in \<open>auto simp: coeff_eq_0\<close>)

lemma Lfun_add: "Lfun (P + Q) = Lfun P + Lfun Q"
proof -
  define N where "N = max (degree P) (degree Q)"
  have "degree (P + Q) \<le> N" "degree P \<le> N" "degree Q \<le> N"
    using degree_add_le_max[of P Q] by (auto simp: N_def)
  thus ?thesis by (simp add: Lfun_eq_sum[of _ N] sum.distrib algebra_simps)
qed

lemma Lfun_smult: "Lfun (Polynomial.smult c P) = c * Lfun P"
  using degree_smult_le[of c P]
  by (simp add: Lfun_eq_sum[of _ "degree P"] sum_distrib_left mult.assoc)

lemma tau_add: "tau (P + Q) = tau P + tau Q"
  by (simp add: tau_def numeral_3_eq_3 pderiv_add Lfun_add add_divide_distrib)

lemma tau_smult: "tau (Polynomial.smult c P) = c * tau P"
  by (simp add: tau_def numeral_3_eq_3 pderiv_smult Lfun_smult)

lemma sqResidue_add: "sqResidue S (P + Q) j = sqResidue S P j + sqResidue S Q j"
  by (simp add: sqResidue_def add_divide_distrib)

lemma sqResidue_smult: "sqResidue S (Polynomial.smult c P) j = c * sqResidue S P j"
  by (simp add: sqResidue_def)

lemma linResidue_add: "linResidue S (P + Q) r = linResidue S P r + linResidue S Q r"
  by (simp add: linResidue_def add_divide_distrib)

lemma linResidue_smult: "linResidue S (Polynomial.smult c P) r = c * linResidue S P r"
  by (simp add: linResidue_def)

lemma muX_add: "muX S (P + Q) = muX S P + muX S Q"
  unfolding muX_def
  by (simp add: poly_div_add_left muPoly_add sqResidue_add smult_add_left sum.distrib algebra_simps)

lemma smult_sum_right: "Polynomial.smult c (\<Sum> i \<in> S. f i) = (\<Sum> i \<in>
  S. Polynomial.smult c (f i))"
  by (induction S rule: infinite_finite_induct) (auto simp: smult_add_right)

lemma muX_C_mul: "muX S ([:c:] * P) = [:c:] * muX S P"
  unfolding muX_def
  by (auto simp: div_smult_left muPoly_smult sqResidue_smult smult_add_right smult_smult
    smult_sum_right)

lemma tauX_add: "tauX S (P + Q) = tauX S P + tauX S Q"
  unfolding tauX_def
  by (simp add: poly_div_add_left tau_add linResidue_add smult_add_left sum.distrib algebra_simps)

lemma tauX_C_mul: "tauX S ([:c:] * P) = [:c:] * tauX S P"
  unfolding tauX_def
  by (simp add: div_smult_left tau_smult linResidue_smult smult_add_right smult_smult
    smult_sum_right)

subsection \<open>Well-definedness: common factors cancel\<close>

text \<open>@{text "mu_X"} depends only on the rational function (Lean:
  @{text muX_mul_cancel}).\<close>
lemma muX_mul_cancel:
  "finite S \<Longrightarrow> j \<notin> S \<Longrightarrow>
    muX (insert j S) (P * (pX + [:of_nat j ^ 2:])) = muX S P"
proof -
  assume S: "finite S" and j: "j \<notin> S"
  define c where "c = pX + [:of_nat j ^ 2:]"
  have c0: "c \<noteq> 0"
  proof
    assume "c = 0"
    hence "degree c = 0" by simp
    moreover have "degree c = 1" unfolding c_def by (simp add: monom_Suc)
    ultimately show False by simp
  qed
  have pc: "poly c x = x + of_nat j ^ 2" for x by (simp add: c_def poly_monom)
  have SP: "sqPoleProd (insert j S) = c * sqPoleProd S"
    unfolding sqPoleProd_def c_def using S j by simp
  have quot: "(P * c) div sqPoleProd (insert j S) = P div sqPoleProd S"
    unfolding SP by (subst mult.commute) (rule div_mult_mult1[OF c0])
  have resj: "sqResidue (insert j S) (P * c) j = 0"
    by (simp add: sqResidue_def pc)
  have resk: "sqResidue (insert j S) (P * c) k = sqResidue S P k" if k: "k \<in> S" for k
  proof -
    have jk: "j \<noteq> k" using j k by auto
    have d0: "(of_nat j ^ 2 - of_nat k ^ 2 :: rat) \<noteq> 0" using jk by simp
    have ins: "insert j S - {k} = insert j (S - {k})" using jk by auto
    have "sqResidue (insert j S) (P * c) k
        = poly P (- (of_nat k ^ 2)) * (of_nat j ^ 2 - of_nat k ^ 2)
          / ((of_nat j ^ 2 - of_nat k ^ 2) * (\<Prod> l \<in>
            S - {k}. of_nat l ^ 2 - of_nat k ^ 2))"
      unfolding sqResidue_def ins using S j by (simp add: pc)
    also have "\<dots> = sqResidue S P k"
      unfolding sqResidue_def by (rule nonzero_mult_divide_mult_cancel_right2[OF d0])
    finally show ?thesis .
  qed
  have "muX (insert j S) (P * c)
      = [:muPoly (P div sqPoleProd S):] + (\<Sum> k \<in>
        S. [:sqResidue (insert j S) (P * c) k:] * muPole k)"
    unfolding muX_def quot using S j by (simp add: resj)
  also have "(\<Sum> k \<in> S. [:sqResidue (insert j S) (P * c) k:] * muPole k) = (\<Sum> k \<in>
    S. [:sqResidue S P k:] * muPole k)"
    by (rule sum.cong) (simp_all add: resk)
  finally show ?thesis unfolding c_def muX_def .
qed

lemma muX_mul_cancel_set:
  "finite S \<Longrightarrow> finite T \<Longrightarrow> T \<inter> S = {} \<Longrightarrow>
    muX (T \<union> S) (P * sqPoleProd T) = muX S P"
proof -
  assume S: "finite S" and T: "finite T"
  show "T \<inter> S = {} \<Longrightarrow> muX (T \<union> S) (P * sqPoleProd T) = muX S P"
    using T
  proof (induction T rule: finite_induct)
    case empty
    thus ?case by (simp add: sqPoleProd_def)
  next
    case (insert j T)
    have jTS: "j \<notin> T \<union> S" using insert by auto
    have e: "P * sqPoleProd (insert j T) = (P * sqPoleProd T) * (pX + [:of_nat j ^ 2:])"
      unfolding sqPoleProd_def using insert.hyps by (simp add: ac_simps)
    have "muX (insert j T \<union> S) (P * sqPoleProd (insert j T))
        = muX (insert j (T \<union> S)) ((P * sqPoleProd T) * (pX + [:of_nat j ^ 2:]))"
      unfolding e by simp
    also have "\<dots> = muX (T \<union> S) (P * sqPoleProd T)"
      by (rule muX_mul_cancel) (use S insert.hyps(1) jTS in auto)
    also have "\<dots> = muX S P" using insert by auto
    finally show ?case .
  qed
qed

subsection \<open>Partial fractions (Lagrange decomposition)\<close>

text \<open>@{text "P = \<Pi> (P div \<Pi>) + \<Sum>_s res_s \<Prod>_{s' \<noteq> s} (X - s')"}
  (Lean: @{text pt_lagrange}).\<close>
lemma pX_minus_const: "pX - [:s:] = [:- s, 1:]"
  by (simp add: monom_Suc)

lemma qPoleProd_lead_coeff: "finite S \<Longrightarrow> lead_coeff (qPoleProd S) = 1"
  unfolding qPoleProd_def pX_minus_const
proof (induction S rule: finite_induct)
  case (insert x F)
  show ?case
    unfolding prod.insert[OF insert.hyps] lead_coeff_mult insert.IH by simp
qed simp

text \<open>Monicity is written as @{text "lead_coeff _ = 1"} (@{text monic} is not a constant in
  the base image).\<close>
lemma qPoleProd_monic: "finite S \<Longrightarrow> lead_coeff (qPoleProd S) = 1"
  by (rule qPoleProd_lead_coeff)

lemma degree_qPoleProd: "finite S \<Longrightarrow> degree (qPoleProd S) = card S"
  unfolding qPoleProd_def pX_minus_const
proof (induction S rule: finite_induct)
  case (insert x F)
  have "(\<Prod>s\<in>F. [:- s, 1:]) \<noteq> 0"
    using insert.hyps(1) by (simp add: prod_zero_iff)
  thus ?case
    unfolding prod.insert[OF insert.hyps] using insert
    by (subst degree_mult_eq) auto
qed simp

lemma poly_qPoleProd: "poly (qPoleProd T) x = (\<Prod> t \<in> T. x - t)"
  unfolding qPoleProd_def by (simp add: poly_prod poly_monom)

lemma poly_eq_0_of_roots:
  fixes Q :: "rat poly"
  assumes "finite S" "degree Q < card S" "\<And>s. s \<in> S \<Longrightarrow> poly Q s = 0"
  shows "Q = 0"
proof (rule ccontr)
  assume Q0: "Q \<noteq> 0"
  have "S \<subseteq> {x. poly Q x = 0}" using assms(3) by auto
  hence "card S \<le> card {x. poly Q x = 0}"
    by (intro card_mono) (use Q0 poly_roots_finite in auto)
  also have "\<dots> \<le> degree Q" by (rule poly_roots_degree[OF Q0])
  finally show False using assms(2) by simp
qed

lemma lagrange_decomp_aux:
  assumes S: "finite S"
  shows "P = qPoleProd S * (P div qPoleProd S) + (\<Sum> s \<in>
    S. [:qRes S P s:] * qPoleProd (S - {s}))"
proof -
  define Pi where "Pi = qPoleProd S"
  define R where "R = P mod Pi"
  define L where "L = (\<Sum> s \<in> S. [:qRes S P s:] * qPoleProd (S - {s}))"
  have Pi0: "Pi \<noteq> 0" using qPoleProd_lead_coeff[OF S] by (auto simp: Pi_def)
  have dPi: "degree Pi = card S" unfolding Pi_def by (rule degree_qPoleProd[OF S])
  have PR: "P = Pi * (P div Pi) + R" unfolding R_def by simp
  have "R = L"
  proof (cases "S = {}")
    case True
    hence "Pi = 1" by (simp add: Pi_def qPoleProd_def)
    thus ?thesis using True by (simp add: R_def L_def)
  next
    case Sne: False
    have cS: "0 < card S" using S Sne by (simp add: card_gt_0_iff)
    have dR: "degree R < card S"
    proof (cases "R = 0")
      case True thus ?thesis using cS by simp
    next
      case False thus ?thesis using degree_mod_less'[OF Pi0] dPi by (simp add: R_def)
    qed
    have dL: "degree L < card S"
    proof -
      have "degree L \<le> card S - 1"
        unfolding L_def
      proof (rule degree_sum_le[OF S])
        fix s assume s: "s \<in> S"
        have "degree ([:qRes S P s:] * qPoleProd (S - {s})) \<le> degree (qPoleProd (S - {s}))"
          by (simp add: degree_smult_le)
        also have "\<dots> = card S - 1" using S s by (simp add: degree_qPoleProd)
        finally show "degree ([:qRes S P s:] * qPoleProd (S - {s})) \<le> card S - 1" .
      qed
      thus ?thesis using cS by simp
    qed
    have roots: "poly (R - L) s = 0" if s: "s \<in> S" for s
    proof -
      have "poly Pi s = 0" unfolding Pi_def poly_qPoleProd using S s by (auto simp: prod_zero_iff)
      hence pR: "poly R s = poly P s" using arg_cong[OF PR, of "\<lambda>q. poly q s"] by simp
      have nz: "(\<Prod> t \<in> S - {s}. s - t) \<noteq> 0" using S by (simp add: prod_zero_iff)
      have "poly L s = (\<Sum> s' \<in> S. qRes S P s' * (\<Prod> t \<in> S - {s'}. s - t))"
        unfolding L_def by (simp add: poly_sum poly_qPoleProd)
      also have "\<dots> = qRes S P s * (\<Prod> t \<in> S - {s}. s - t)
                      + (\<Sum> s' \<in> S - {s}. qRes S P s' * (\<Prod> t \<in> S - {s'}. s - t))"
        using S s by (simp add: sum.remove)
      also have "(\<Sum> s' \<in> S - {s}. qRes S P s' * (\<Prod> t \<in> S - {s'}. s - t)) = 0"
        using S s by (intro sum.neutral) (auto simp: prod_zero_iff)
      also have "qRes S P s * (\<Prod> t \<in> S - {s}. s - t) = poly P s"
        using nz by (simp add: qRes_def)
      finally show ?thesis using pR by simp
    qed
    have "R - L = 0"
    proof (rule poly_eq_0_of_roots[OF S _ roots])
      show "degree (R - L) < card S"
        using degree_diff_le_max[of R L] dR dL by simp
    qed
    thus ?thesis by simp
  qed
  thus ?thesis using PR by (simp add: Pi_def L_def)
qed

lemma lagrange_decomp:
  "finite S \<Longrightarrow> P = qPoleProd S * (P div qPoleProd S) + (\<Sum> s \<in>
    S. [:qRes S P s:] * qPoleProd (S - {s}))"
  by (rule lagrange_decomp_aux)

subsection \<open>(3.1) The pullback identity\<close>

text \<open>The pullback identity (3.1) is stated and proved at the end of this theory.\<close>

subsection \<open>\<open>\<tau>\<close> on polynomials\<close>

text \<open>@{text "\<tau>(z^d) = \<kappa>_d"}, and @{text "tauK = tau"}.\<close>
lemma pX_pow_monom: "pX ^ d = Polynomial.monom 1 d"
  by (simp add: monom_power)

lemma Lfun_monom: "Lfun (Polynomial.monom c k) = c * bernoulli k"
proof -
  have "Lfun (Polynomial.monom c k) = (\<Sum> j \<le>
    k. Polynomial.coeff (Polynomial.monom c k) j * bernoulli j)"
    by (rule Lfun_eq_sum) (simp add: degree_monom_le)
  also have "\<dots> = (\<Sum> j \<le> k. if j = k then c * bernoulli k else 0)"
    by (rule sum.cong) (auto simp: coeff_monom)
  finally show ?thesis by simp
qed

lemma tau_X_pow_eq_kappa: "tau (pX ^ d) = kappa d"
proof -
  have "(pderiv ^^ 3) (pX ^ d) = Polynomial.monom (of_nat (d-2) * (of_nat (d-1) * of_nat d)) (d-3)"
    unfolding pX_pow_monom by (simp add: numeral_3_eq_3 numeral_2_eq_2 pderiv_monom)
  hence "tau (pX ^ d) = of_nat (d-2) * (of_nat (d-1) * of_nat d) * bernoulli (d-3) / 24"
    by (simp add: tau_def Lfun_monom)
  also have "\<dots> = kappa d"
  proof -
    consider "d = 0" | "d = 1" | "d = 2" | "3 \<le> d" by arith
    thus ?thesis
      by cases (auto simp: kappa_def of_nat_diff)
  qed
  finally show ?thesis .
qed
lemma tau_zero: "tau 0 = 0"
  using tau_smult[of 0 0] by simp

lemma tau_sum: "tau (\<Sum> i \<in> S. f i) = (\<Sum> i \<in> S. tau (f i))"
  by (induction S rule: infinite_finite_induct) (auto simp: tau_add tau_zero)

lemma tau_monom: "tau (Polynomial.monom c d) = c * kappa d"
proof -
  have "Polynomial.monom c d = Polynomial.smult c (pX ^ d)"
    unfolding pX_pow_monom by (simp add: smult_monom)
  thus ?thesis by (simp only: tau_smult tau_X_pow_eq_kappa)
qed

lemma tauK_eq_tau: "tauK Q = tau Q"
proof -
  have "tau Q = tau (\<Sum> d \<le> degree Q. Polynomial.monom (Polynomial.coeff Q d) d)"
    by (simp only: poly_as_sum_of_monoms)
  also have "\<dots> = tauK Q"
    by (simp add: tau_sum tau_monom tauK_def)
  finally show ?thesis by simp
qed

lemma sum_binomial_bernoulli_lt:
  "(\<Sum> k < n. of_nat (n choose k) * bernoulli k) = (if n = 1 then 1 else (0 :: rat))"
proof -
  have "real_of_rat (\<Sum> k < n. of_nat (n choose k) * bernoulli k) = real_of_rat (if n =
    1 then 1 else 0)"
    by (cases "n = 1")
       (simp_all add: of_rat_sum of_rat_mult of_rat_bernoulli sum_binomial_times_bernoulli')
  thus ?thesis by (simp only: of_rat_eq_iff)
qed

lemma kappa_0: "kappa 0 = 0" and kappa_1: "kappa 1 = 0" and kappa_2: "kappa 2 = 0"
  and kappa_Suc_0: "kappa (Suc 0) = 0" and kappa_Suc_Suc_0: "kappa (Suc (Suc 0)) = 0"
  by (simp_all add: kappa_def)

lemma kappa_Suc3:
  "kappa (Suc (Suc (Suc j))) = of_nat (Suc (Suc (Suc j)) * Suc (Suc j) * Suc j) * bernoulli j / 24"
  by (simp add: kappa_def algebra_simps)

lemma choose_falling3:
  "(Suc (Suc (Suc m)) choose Suc (Suc (Suc j))) * (Suc (Suc (Suc j)) * Suc (Suc j) * Suc j)
     = Suc (Suc (Suc m)) * Suc (Suc m) * Suc m * (m choose j)"
proof -
  have "(Suc (Suc (Suc m)) choose Suc (Suc (Suc j))) * (Suc (Suc (Suc j)) * Suc (Suc j) * Suc j)
      = (Suc (Suc (Suc j)) * (Suc (Suc (Suc m)) choose Suc (Suc (Suc j)))) * Suc (Suc j) * Suc j"
    by (simp only: ac_simps)
  also have "\<dots> = Suc (Suc (Suc m)) * ((Suc (Suc j)) * (Suc (Suc m) choose Suc (Suc j))) *
    Suc j"
    by (subst Suc_times_binomial) (simp only: ac_simps)
  also have "\<dots> = Suc (Suc (Suc m)) * Suc (Suc m) * (Suc j * (Suc m choose Suc j))"
    by (subst Suc_times_binomial) (simp only: ac_simps)
  also have "\<dots> = Suc (Suc (Suc m)) * Suc (Suc m) * Suc m * (m choose j)"
    by (subst Suc_times_binomial) (simp only: ac_simps)
  finally show ?thesis .
qed

lemma sum_choose_kappa_aux:
  "(\<Sum> d \<le> n. of_nat (n choose d) * kappa d) = (if n = 4 then 1 else 0) + kappa n"
proof (cases "n < 3")
  case True
  have k0: "kappa d = 0" if "d \<le> n" for d
    using that True kappa_0 kappa_1 kappa_2 by (cases "d = 0 \<or> d = 1 \<or> d = 2") auto
  have "(\<Sum> d \<le> n. of_nat (n choose d) * kappa d) = 0"
    by (rule sum.neutral) (simp add: k0)
  thus ?thesis using True k0[of n] by simp
next
  case False
  define m where "m = n - 3"
  have n: "n = Suc (Suc (Suc m))" using False unfolding m_def by arith
  define c :: rat where "c = of_nat (Suc (Suc (Suc m)) * Suc (Suc m) * Suc m) / 24"
  have tm: "of_nat (Suc (Suc (Suc m)) choose Suc (Suc (Suc j))) * kappa (Suc (Suc (Suc j)))
      = c * (of_nat (m choose j) * bernoulli j)" for j
  proof -
    have "of_nat (Suc (Suc (Suc m)) choose Suc (Suc (Suc j))) * kappa (Suc (Suc (Suc j)))
        = of_nat ((Suc (Suc (Suc m)) choose Suc (Suc (Suc j))) * (Suc (Suc (Suc j)) * Suc (Suc j) *
          Suc j))
          * bernoulli j / 24"
      unfolding kappa_Suc3 by (simp only: of_nat_mult)
    also have "\<dots> = of_nat (Suc (Suc (Suc m)) * Suc (Suc m) * Suc m * (m choose j)) *
      bernoulli j / 24"
      by (simp only: choose_falling3)
    also have "\<dots> = c * (of_nat (m choose j) * bernoulli j)"
      unfolding c_def by (simp only: of_nat_mult) (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have "(\<Sum> d \<le> n. of_nat (n choose d) * kappa d)
      = (\<Sum> j \<le> m. of_nat (Suc (Suc (Suc m)) choose Suc (Suc (Suc j))) *
        kappa (Suc (Suc (Suc j))))"
    unfolding n by (simp only: sum.atMost_Suc_shift) (simp add: kappa_0 kappa_Suc_0 kappa_Suc_Suc_0)
  also have "\<dots> = c * (\<Sum> j \<le> m. of_nat (m choose j) * bernoulli j)"
    by (simp only: tm sum_distrib_left)
  also have "(\<Sum> j \<le> m. of_nat (m choose j) * bernoulli j) = (if m =
    1 then 1 else 0) + (bernoulli m :: rat)"
    by (simp only: lessThan_Suc_atMost[symmetric] sum.lessThan_Suc sum_binomial_bernoulli_lt) simp
  also have "c * ((if m = 1 then 1 else 0) + bernoulli m) = (if n = 4 then 1 else 0) + kappa n"
    unfolding n kappa_Suc3 c_def by (cases "m = 1") simp_all
  finally show ?thesis .
qed

lemma tau_uminus: "tau (- P) = - tau P"
  using tau_smult[of "-1" P] by simp

lemma tau_diff: "tau (P - Q) = tau P - tau Q"
  using tau_add[of P "- Q"] by (simp add: tau_uminus)

lemma tau_of_nat_mult: "tau (of_nat c * P) = of_nat c * tau P"
proof -
  have "of_nat c * P = Polynomial.smult (of_nat c) P" by (simp add: of_nat_poly)
  thus ?thesis by (simp only: tau_smult)
qed

lemma tau_shift_pow: "tau ((pX + 1) ^ n) = (if n = 4 then 1 else 0) + kappa n"
proof -
  have eq: "(pX + 1) ^ n = (\<Sum> k \<le> n. of_nat (n choose k) * pX ^ k)"
    using binomial_ring[of pX 1 n] by simp
  have "tau ((pX + 1) ^ n) = (\<Sum> k \<le> n. of_nat (n choose k) * kappa k)"
    unfolding eq by (simp only: tau_sum tau_of_nat_mult tau_X_pow_eq_kappa)
  thus ?thesis by (simp only: sum_choose_kappa_aux)
qed

lemma tau_fwd_monom:
  "tau (pcompose (Polynomial.monom c n) (pX + 1) - Polynomial.monom c n) = (if n = 4 then c else 0)"
proof -
  have m: "Polynomial.monom c n = Polynomial.smult c (pX ^ n)"
    unfolding pX_pow_monom by (simp add: smult_monom)
  have "tau (pcompose (Polynomial.monom c n) (pX + 1) - Polynomial.monom c n)
      = c * ((if n = 4 then 1 else 0) + kappa n) - c * kappa n"
    unfolding m pcompose_smult pcompose_power_left pcompose_pX tau_diff tau_smult tau_shift_pow
      tau_X_pow_eq_kappa ..
  thus ?thesis by (simp add: algebra_simps)
qed

lemma tau_fwd_aux: "tau (pcompose f (pX + 1) - f) = Polynomial.coeff f 4"
proof -
  define D where "D = degree f"
  define M where "M n = Polynomial.monom (Polynomial.coeff f n) n" for n
  have e: "(\<Sum> n \<le> D. M n) = f" unfolding D_def M_def by (rule poly_as_sum_of_monoms)
  have "tau (pcompose f (pX + 1) - f) = tau (pcompose (\<Sum> n \<le>
    D. M n) (pX + 1) - (\<Sum> n \<le> D. M n))"
    by (simp only: e)
  also have "\<dots> = tau (\<Sum> n \<le> D. (pcompose (M n) (pX + 1) - M n))"
    by (simp only: pcompose_sum sum_subtractf)
  also have "\<dots> = (\<Sum> n \<le> D. if n = 4 then Polynomial.coeff f n else 0)"
    by (simp only: tau_sum M_def tau_fwd_monom)
  also have "\<dots> = Polynomial.coeff f 4"
    by (cases "4 \<le> D") (auto simp: D_def coeff_eq_0)
  finally show ?thesis .
qed

text \<open>(3.3) for polynomials: @{text "\<tau>(f(x+1) - f(x)) = f''''(0)/24 = [x^4] f"} (Lean:
  @{text tau_fwd}).\<close>
lemma tau_fwd: "tau (pcompose f (pX + 1) - f) = Polynomial.coeff f 4"
  by (rule tau_fwd_aux)

text \<open>@{text "\<Sum>_{d \<le> n} C(n,d) \<kappa>_d = [n = 4] + \<kappa>_n"}.\<close>
lemma sum_choose_kappa:
  "(\<Sum> d \<le> n. of_nat (n choose d) * kappa d) = (if n = 4 then 1 else 0) + kappa n"
  by (rule sum_choose_kappa_aux)

text \<open>Every polynomial is a forward difference.\<close>
lemma pX_shift_pow_diff:
  "pcompose (pX ^ m) (pX + 1) - pX ^ m = (\<Sum> k < m. Polynomial.monom (of_nat (m choose k)) k)"
proof -
  have "(pX + 1) ^ m = (\<Sum> k \<le> m. of_nat (m choose k) * pX ^ k)"
    using binomial_ring[of pX 1 m] by simp
  also have "\<dots> = (\<Sum> k \<le> m. Polynomial.monom (of_nat (m choose k)) k)"
    by (rule sum.cong[OF refl], unfold pX_pow_monom, simp add: of_nat_poly smult_monom)
  also have "\<dots> = (\<Sum> k < m. Polynomial.monom (of_nat (m choose k)) k) + pX ^ m"
    unfolding pX_pow_monom by (simp add: lessThan_Suc_atMost[symmetric])
  finally show ?thesis unfolding pcompose_power_left pcompose_pX by simp
qed

lemma exists_antidiff_aux: "\<exists>g. pcompose g (pX + 1) - g = f"
proof (induction f rule: measure_induct_rule[where f = degree])
  case (less f)
  show ?case
  proof (cases "f = 0")
    case True
    thus ?thesis by (intro exI[of _ 0]) simp
  next
    case False
    define n where "n = degree f"
    define c where "c = lead_coeff f"
    define a where "a = c / of_nat (Suc n)"
    define E where "E = (\<Sum> k < Suc n. Polynomial.monom (of_nat (Suc n choose k)) k :: rat
      poly)"
    define g0 where "g0 = Polynomial.smult a (pX ^ Suc n)"
    have Dg0: "pcompose g0 (pX + 1) - g0 = Polynomial.smult a E"
      unfolding g0_def pcompose_smult smult_diff_right[symmetric] pX_shift_pow_diff E_def ..
    have dE: "degree E \<le> n"
      unfolding E_def by (rule degree_sum_le) (auto intro: order_trans[OF degree_monom_le])
    have cE: "Polynomial.coeff E n = of_nat (Suc n)"
      unfolding E_def by (simp add: coeff_sum coeff_monom)
    define f' where "f' = f - Polynomial.smult a E"
    have df': "degree f' \<le> n"
      unfolding f'_def n_def using dE[unfolded n_def]
      by (intro degree_diff_le) (auto intro: order_trans[OF degree_smult_le])
    have cf': "Polynomial.coeff f' n = 0"
      unfolding f'_def using cE by (simp add: a_def c_def n_def)
    obtain g' where g': "pcompose g' (pX + 1) - g' = f'"
    proof (cases "f' = 0")
      case True
      thus ?thesis using that[of 0] by simp
    next
      case False
      hence "degree f' \<noteq> n" using cf' by (metis leading_coeff_0_iff)
      hence "degree f' < degree f" using df' by (simp add: n_def)
      thus ?thesis using less.IH that by blast
    qed
    have "pcompose (g0 + g') (pX + 1) - (g0 + g')
        = (pcompose g0 (pX + 1) - g0) + (pcompose g' (pX + 1) - g')"
      by (simp add: pcompose_add algebra_simps)
    also have "\<dots> = f" unfolding Dg0 g' f'_def by simp
    finally show ?thesis by blast
  qed
qed

lemma exists_antidiff: "\<exists>g. pcompose g (pX + 1) - g = f"
  by (rule exists_antidiff_aux)



subsection \<open>(3.1) The pullback identity: proof\<close>

definition pullbackR :: "nat set \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "pullbackR S P = tauX (signedPoles S) ([:(-1) ^ card S:] * pX ^ 5 * pcompose P (- (pX ^ 2)))"

lemma muX_zero: "muX S 0 = 0"
  using muX_C_mul[of S 0 0] by simp

lemma muX_sum: "muX S (\<Sum> i \<in> I. f i) = (\<Sum> i \<in> I. muX S (f i))"
  by (induction I rule: infinite_finite_induct) (simp_all add: muX_add muX_zero)

lemma tauX_zero: "tauX T 0 = 0"
  using tauX_C_mul[of T 0 0] by simp

lemma pullbackR_add: "pullbackR S (P + Q) = pullbackR S P + pullbackR S Q"
  unfolding pullbackR_def pcompose_add distrib_left tauX_add ..

lemma pullbackR_C_mul: "pullbackR S ([:a:] * P) = [:a:] * pullbackR S P"
proof -
  have "[:(-1) ^ card S:] * pX ^ 5 * pcompose ([:a:] * P) (- (pX ^ 2))
      = [:a:] * ([:(-1) ^ card S:] * pX ^ 5 * pcompose P (- (pX ^ 2)))"
    unfolding pcompose_mult pcompose_const by (simp only: ac_simps)
  thus ?thesis unfolding pullbackR_def by (simp only: tauX_C_mul)
qed

lemma pullbackR_zero: "pullbackR S 0 = 0"
  by (simp add: pullbackR_def tauX_zero)

lemma pullbackR_sum: "pullbackR S (\<Sum> i \<in> I. f i) = (\<Sum> i \<in> I. pullbackR S (f i))"
  by (induction I rule: infinite_finite_induct) (simp_all add: pullbackR_add pullbackR_zero)

lemma pcompose_sq_factor:
  "pcompose (pX + [:of_nat j ^ 2:]) (- (pX ^ 2))
     = [:- 1:] * ((pX - [:of_int (int j):]) * (pX - [:of_int (- int j):]))"
proof -
  have "pcompose (pX + [:of_nat j ^ 2:]) (- (pX ^ 2)) = - (pX ^ 2) + [:of_nat j ^ 2:]"
    unfolding pcompose_add pcompose_pX pcompose_const ..
  also have "\<dots> = [:- 1:] * ((pX - [:of_nat j:]) * (pX + [:of_nat j:]))"
    by (simp add: algebra_simps power2_eq_square)
  finally show ?thesis by simp
qed

lemma const_poly_power: "[:a:] ^ n = [:a ^ n:]"
  by (induction n) (simp_all add: mult.commute)

lemma minus_one_poly: "(- 1 :: rat poly) = [:- 1:]"
  by (simp add: one_pCons)

lemma pcompose_sqPoleProd:
  assumes S: "finite S" and S0: "0 \<notin> S"
  shows "pcompose (sqPoleProd S) (- (pX ^ 2)) = [:(-1) ^ card S:] * linPoleProd (signedPoles S)"
proof -
  define A where "A j = pX - [:of_int (int j) :: rat:]" for j :: nat
  define B where "B j = pX - [:of_int (- int j) :: rat:]" for j :: nat
  have "pcompose (sqPoleProd S) (- (pX ^ 2)) = (\<Prod> j \<in> S. [:- 1:] * (A j * B j))"
    unfolding sqPoleProd_def pcompose_prod pcompose_sq_factor A_def B_def ..
  also have "\<dots> = [:- 1:] ^ card S * ((\<Prod> j \<in> S. A j) * (\<Prod> j \<in> S. B j))"
    by (simp only: prod.distrib prod_constant)
  also have "(\<Prod> j \<in> S. A j) * (\<Prod> j \<in> S. B j) = linPoleProd (signedPoles S)"
  proof -
    have inj1: "inj_on int S" by simp
    have inj2: "inj_on (\<lambda>j. - int j) S" by (auto intro: inj_onI)
    have "\<And>x j. int x = - int j \<Longrightarrow> x = 0" by linarith
    with S0 have "int ` S \<inter> (\<lambda>j. - int j) ` S = {}" by fastforce
    with S have "linPoleProd (signedPoles S)
        = (\<Prod> r \<in> int ` S. pX - [:of_int r:]) * (\<Prod> r \<in>
          (\<lambda>j. - int j) ` S. pX - [:of_int r:])"
      unfolding linPoleProd_def signedPoles_def by (simp add: prod.union_disjoint)
    also have "\<dots> = (\<Prod> j \<in> S. A j) * (\<Prod> j \<in> S. B j)"
      by (simp add: prod.reindex[OF inj1] prod.reindex[OF inj2] A_def B_def o_def)
    finally show ?thesis by simp
  qed
  finally show ?thesis by (simp add: const_poly_power)
qed

lemma kappa_odd_muMono: "(- 1) ^ e * kappa (2 * e + 5) = muMono e"
  by (simp add: kappa_def muMono_def algebra_simps)

lemma tau_pullback_monom:
  "tau (pX ^ 5 * pcompose (Polynomial.monom c e) (- (pX ^ 2))) = c * muMono e"
proof -
  have m: "Polynomial.monom c e = Polynomial.smult c (pX ^ e)"
    unfolding pX_pow_monom by (simp add: smult_monom)
  have neg: "(- (pX ^ 2) :: rat poly) ^ e = [:(- 1) ^ e:] * pX ^ (2 * e)"
  proof -
    have "(- (pX ^ 2) :: rat poly) ^ e = (- 1) ^ e * (pX ^ 2) ^ e" by (rule power_minus)
    also have "(- 1 :: rat poly) ^ e = [:(- 1) ^ e:]"
      unfolding minus_one_poly by (rule const_poly_power)
    also have "(pX ^ 2) ^ e = pX ^ (2 * e)" by (simp add: power_mult)
    finally show ?thesis .
  qed
  have "pX ^ 5 * pcompose (Polynomial.monom c e) (- (pX ^ 2))
      = Polynomial.smult (c * (- 1) ^ e) (pX ^ (2 * e + 5))"
    unfolding m pcompose_smult pcompose_power_left pcompose_pX neg
    by (simp add: power_add ac_simps)
  hence "tau (pX ^ 5 * pcompose (Polynomial.monom c e) (- (pX ^ 2))) =
    c * ((- 1) ^ e * kappa (2 * e + 5))"
    by (simp only: tau_smult tau_X_pow_eq_kappa mult.assoc)
  thus ?thesis by (simp only: kappa_odd_muMono)
qed

lemma tau_pullback_poly: "tau (pX ^ 5 * pcompose Q (- (pX ^ 2))) = muPoly Q"
proof -
  define M where "M e = Polynomial.monom (Polynomial.coeff Q e) e" for e
  have e: "(\<Sum> e \<le> degree Q. M e) = Q" unfolding M_def by (rule poly_as_sum_of_monoms)
  have "tau (pX ^ 5 * pcompose Q (- (pX ^ 2))) = tau (pX ^ 5 * pcompose (\<Sum> e \<le>
    degree Q. M e) (- (pX ^ 2)))"
    by (simp only: e)
  also have "\<dots> = (\<Sum> e \<le> degree Q. tau (pX ^ 5 * pcompose (M e) (- (pX ^ 2))))"
    by (simp only: pcompose_sum sum_distrib_left tau_sum)
  also have "\<dots> = (\<Sum> e \<le> degree Q. Polynomial.coeff Q e * muMono e)"
    by (simp only: M_def tau_pullback_monom)
  finally show ?thesis by (simp add: muPoly_def)
qed

lemma sqPoleProd_nonzero: "finite S \<Longrightarrow> sqPoleProd S \<noteq> 0"
proof -
  assume S: "finite S"
  have "pX + [:of_nat j ^ 2:] \<noteq> (0 :: rat poly)" for j
  proof
    assume "pX + [:of_nat j ^ 2:] = (0 :: rat poly)"
    hence "Polynomial.coeff (pX + [:of_nat j ^ 2:]) 1 = 0" by simp
    thus False by (simp add: coeff_monom)
  qed
  thus ?thesis using S by (simp add: sqPoleProd_def)
qed

lemma linPoleProd_nonzero: "finite T \<Longrightarrow> linPoleProd T \<noteq> 0"
proof -
  assume T: "finite T"
  have "pX - [:of_int r:] \<noteq> (0 :: rat poly)" for r
  proof
    assume "pX - [:of_int r:] = (0 :: rat poly)"
    hence "Polynomial.coeff (pX - [:of_int r:]) 1 = 0" by simp
    thus False by (simp add: coeff_monom)
  qed
  thus ?thesis using T by (simp add: linPoleProd_def)
qed

lemma muX_poly_mult:
  assumes S: "finite S"
  shows "muX S (sqPoleProd S * Q) = [:muPoly Q:]"
proof -
  have q: "(sqPoleProd S * Q) div sqPoleProd S = Q"
    using sqPoleProd_nonzero[OF S] by simp
  have r: "sqResidue S (sqPoleProd S * Q) j = 0" if j: "j \<in> S" for j
  proof -
    have "poly (sqPoleProd S) (- (of_nat j ^ 2)) = 0"
      unfolding sqPoleProd_def poly_prod using S j by (auto simp: prod_zero_iff poly_monom)
    thus ?thesis by (simp add: sqResidue_def)
  qed
  show ?thesis unfolding muX_def q using r by simp
qed

lemma tauX_poly_mult:
  assumes T: "finite T"
  shows "tauX T (G * linPoleProd T) = [:tau G:]"
proof -
  have q: "(G * linPoleProd T) div linPoleProd T = G"
    using linPoleProd_nonzero[OF T] by simp
  have r: "linResidue T (G * linPoleProd T) r = 0" if r: "r \<in> T" for r
  proof -
    have "poly (linPoleProd T) (of_int r) = 0"
      unfolding linPoleProd_def poly_prod using T r by (auto simp: prod_zero_iff poly_monom)
    thus ?thesis by (simp add: linResidue_def)
  qed
  show ?thesis unfolding tauX_def q using r by simp
qed

lemma pullback_poly:
  assumes S: "finite S" and S0: "0 \<notin> S"
  shows "muX S (sqPoleProd S * Q) = pullbackR S (sqPoleProd S * Q)"
proof -
  define c :: rat where "c = (- 1) ^ card S"
  define L where "L = linPoleProd (signedPoles S)"
  have cc: "[:c:] * [:c:] = 1" by (simp add: c_def power_mult_distrib[symmetric])
  have TS: "finite (signedPoles S)" using S by (simp add: signedPoles_def)
  have "[:c:] * pX ^ 5 * pcompose (sqPoleProd S * Q) (- (pX ^ 2))
      = ([:c:] * [:c:]) * (pX ^ 5 * pcompose Q (- (pX ^ 2))) * L"
    unfolding pcompose_mult pcompose_sqPoleProd[OF S S0] c_def L_def by (simp only: ac_simps)
  also have "\<dots> = (pX ^ 5 * pcompose Q (- (pX ^ 2))) * L" by (simp only: cc mult_1)
  finally have F: "[:c:] * pX ^ 5 * pcompose (sqPoleProd S * Q) (- (pX ^ 2)) =
    (pX ^ 5 * pcompose Q (- (pX ^ 2))) * L" .
  show ?thesis
    unfolding pullbackR_def c_def[symmetric] F L_def tauX_poly_mult[OF TS] muX_poly_mult[OF S]
      tau_pullback_poly ..
qed

lemma degree_pX_plus_const: "degree (pX + [:a:]) = 1"
  by (simp add: monom_Suc)

lemma degree_pX_minus_const: "degree (pX - [:a:]) = 1"
  by (simp add: monom_Suc)

lemma pX_plus_const_nonzero: "pX + [:a:] \<noteq> 0"
  using degree_pX_plus_const[of a] by auto

lemma pX_minus_const_nonzero: "pX - [:a:] \<noteq> 0"
  using degree_pX_minus_const[of a] by auto

lemma muX_single_pole:
  assumes S: "finite S" and j: "j \<in> S"
  shows "muX S (sqPoleProd (S - {j})) = muPole j"
proof -
  define Pj where "Pj = sqPoleProd (S - {j})"
  have D: "sqPoleProd S = (pX + [:of_nat j ^ 2:]) * Pj"
    unfolding sqPoleProd_def Pj_def using S j by (simp add: prod.remove)
  have Pj0: "Pj \<noteq> 0" unfolding Pj_def using S by (simp add: sqPoleProd_nonzero)
  have "degree (sqPoleProd S) = 1 + degree Pj"
    unfolding D degree_mult_eq[OF pX_plus_const_nonzero Pj0] degree_pX_plus_const ..
  hence q: "Pj div sqPoleProd S = 0" by (intro div_poly_less) simp
  have r: "sqResidue S Pj k = (if k = j then 1 else 0)" if k: "k \<in> S" for k
  proof (cases "k = j")
    case True
    have nz: "(\<Prod> l \<in> S - {j}. of_nat l ^ 2 - of_nat j ^ 2 :: rat) \<noteq> 0"
      using S by (simp add: prod_zero_iff)
    have "poly Pj (- (of_nat j ^ 2)) = (\<Prod> l \<in> S - {j}. of_nat l ^ 2 - of_nat j ^ 2)"
      unfolding Pj_def sqPoleProd_def poly_prod by (simp add: poly_monom)
    thus ?thesis using True nz by (simp add: sqResidue_def)
  next
    case False
    have "poly Pj (- (of_nat k ^ 2)) = 0"
      unfolding Pj_def sqPoleProd_def poly_prod using S k False
      by (auto simp: prod_zero_iff poly_monom intro!: bexI[of _ k])
    thus ?thesis using False by (simp add: sqResidue_def)
  qed
  have "muX S Pj = [:muPoly 0:] + (\<Sum> k \<in> S. [:if k = j then 1 else 0:] * muPole k)"
    unfolding muX_def q using r by (simp cong: sum.cong)
  also have "(\<Sum> k \<in> S. [:if k = j then 1 else 0:] * muPole k) = (\<Sum> k \<in> S.
    if k = j then muPole k else 0)"
    by (rule sum.cong) auto
  also have "[:muPoly 0:] + (\<Sum> k \<in> S. if k = j then muPole k else 0) = muPole j"
    using S j by (simp add: muPoly_def)
  finally show ?thesis unfolding Pj_def .
qed

lemma quintic_division_identity:
  fixes x A :: "'a :: comm_ring_1"
  shows "x ^ 5 = ((x - A) * (x - - A)) * (x ^ 3 + A ^ 2 * x) + A ^ 4 * x"
  by (simp add: numeral_eq_Suc algebra_simps)

lemma H5_Suc_pred: "j \<noteq> 0 \<Longrightarrow> H5 j = H5 (j - 1) + 1 / of_nat j ^ 5"
proof -
  assume "j \<noteq> 0"
  then obtain i where i: "j = Suc i" by (cases j) auto
  show ?thesis unfolding i H5_def by simp
qed

lemma pullbackR_single_pole:
  assumes S: "finite S" and S0: "0 \<notin> S" and j: "j \<in> S"
  shows "pullbackR S (sqPoleProd (S - {j})) = muPole j"
proof -
  define S' where "S' = S - {j}"
  define T' where "T' = signedPoles S'"
  define M where "M = linPoleProd T'"
  define a :: rat where "a = of_nat j"
  define A :: "rat poly" where "A = [:a:]"
  have j0: "j \<noteq> 0"
  proof
    assume "j = 0"
    thus False using S0 j by simp
  qed
  have a0: "a \<noteq> 0" using j0 by (simp add: a_def)
  have a5: "a ^ 5 = a * a ^ 4" by (simp add: eval_nat_numeral)
  have S'f: "finite S'" "0 \<notin> S'" using S S0 by (auto simp: S'_def)
  have T'f: "finite T'" using S'f by (simp add: T'_def signedPoles_def)
  have cardS: "card S = Suc (card S')" using S j card_gt_0_iff[of S] by (auto simp: S'_def)
  have nn: "\<And>x y :: nat. int x = - int y \<Longrightarrow> x = 0" by linarith
  have jT1: "int j \<notin> T'" using j0 nn by (auto simp: T'_def signedPoles_def S'_def)
  have jT2: "- int j \<notin> T'" using j0 nn by (auto simp: T'_def signedPoles_def S'_def)
  have Teq: "signedPoles S = insert (int j) (insert (- int j) T')"
    using j by (auto simp: T'_def signedPoles_def S'_def)
  have jne: "int j \<noteq> - int j" using j0 by simp
  have M0: "M \<noteq> 0" unfolding M_def by (rule linPoleProd_nonzero[OF T'f])
  have L: "linPoleProd (signedPoles S) = (pX - A) * ((pX - - A) * M)"
    unfolding Teq linPoleProd_def M_def using T'f jT1 jT2 jne by (simp add: A_def a_def)
  \<comment> \<open>the pulled-back numerator\<close>
  define F where "F = [:(-1) ^ card S:] * pX ^ 5 * pcompose (sqPoleProd S') (- (pX ^ 2))"
  have sq1: "(-1 :: rat) ^ n * (-1) ^ n = 1" for n by (simp add: power_mult_distrib[symmetric])
  have F': "F = - (pX ^ 5 * M)"
  proof -
    have "F = ([:(-1) ^ Suc (card S'):] * [:(-1) ^ card S':]) * (pX ^ 5 * M)"
      unfolding F_def pcompose_sqPoleProd[OF S'f] cardS M_def T'_def by (simp only: ac_simps)
    also have "[:(-1) ^ Suc (card S'):] * [:(-1) ^ card S':] = [:- 1 :: rat:]"
      using sq1[of "card S'"] by simp
    finally show ?thesis by simp
  qed
  \<comment> \<open>polynomial division by the pole product\<close>
  define G where "G = - (pX ^ 3 + A ^ 2 * pX)"
  define R where "R = - (A ^ 4 * pX * M)"
  have FGR: "F = R + G * linPoleProd (signedPoles S)"
    unfolding F' L G_def R_def quintic_division_identity[of pX A] by (simp add: algebra_simps)
  have L0: "linPoleProd (signedPoles S) \<noteq> 0"
    unfolding L using M0 pX_minus_const_nonzero[of a] pX_minus_const_nonzero[of "- a"]
    by (simp add: A_def)
  have dL: "degree (linPoleProd (signedPoles S)) = 2 + degree M"
  proof -
    have n1: "pX - A \<noteq> 0" "pX - - A \<noteq> 0"
      using pX_minus_const_nonzero[of a] pX_minus_const_nonzero[of "- a"] by (simp_all add: A_def)
    have n2: "(pX - - A) * M \<noteq> 0" using n1(2) M0 by simp
    have d1: "degree (pX - A) = 1" "degree (pX - - A) = 1"
      using degree_pX_minus_const[of a] degree_pX_minus_const[of "- a"] by (simp_all add: A_def)
    show ?thesis unfolding L degree_mult_eq[OF n1(1) n2] degree_mult_eq[OF n1(2) M0] d1 by simp
  qed
  have dR: "degree R < degree (linPoleProd (signedPoles S))"
  proof -
    have "A ^ 4 * pX * M = Polynomial.smult (a ^ 4) (pX * M)"
      by (simp add: A_def const_poly_power)
    hence "degree R \<le> degree (pX * M)" unfolding R_def by (simp add: degree_smult_le)
    also have "\<dots> \<le> degree (pX :: rat poly) + degree M" by (rule degree_mult_le)
    also have "degree (pX :: rat poly) = 1" by (simp add: degree_monom_eq)
    finally show ?thesis unfolding dL by simp
  qed
  have quot: "F div linPoleProd (signedPoles S) = G"
    unfolding FGR div_mult_self1[OF L0] div_poly_less[OF dR] by simp
  have tauG: "tau G = - (1 / 4)"
  proof -
    have "G = - (pX ^ 3 + Polynomial.smult (a ^ 2) (pX ^ 1))"
      by (simp add: G_def A_def const_poly_power)
    hence "tau G = - (kappa 3 + a ^ 2 * kappa 1)"
      by (simp only: tau_uminus tau_add tau_smult tau_X_pow_eq_kappa)
    thus ?thesis by (simp add: kappa_def bernoulli_0 numeral_3_eq_3)
  qed
  \<comment> \<open>residues\<close>
  have polyM: "poly M x = (\<Prod> s \<in> T'. x - of_int s)" for x
    unfolding M_def linPoleProd_def poly_prod by (simp add: poly_monom)
  have polyF: "poly F x = - (x ^ 5 * poly M x)" for x unfolding F' by (simp add: poly_monom)
  have PM0: "poly M x \<noteq> 0" if "x = a \<or> x = - a" for x
  proof -
    have "x - of_int s \<noteq> 0" if s: "s \<in> T'" for s
    proof
      assume "x - of_int s = 0"
      hence "x = of_int s" by simp
      hence "s = int j \<or> s = - int j" using \<open>x = a \<or> x = - a\<close>
        by (auto simp: a_def)
      thus False using s jT1 jT2 by auto
    qed
    thus ?thesis unfolding polyM using T'f by (simp add: prod_zero_iff)
  qed
  define lr where "lr r = linResidue (signedPoles S) F r" for r
  have lrT': "lr r = 0" if r: "r \<in> T'" for r
  proof -
    have "poly M (of_int r) = 0" unfolding polyM using T'f r by (auto simp: prod_zero_iff)
    thus ?thesis by (simp add: lr_def linResidue_def polyF)
  qed
  have lrj: "lr (int j) = - (a ^ 4 / 2)"
  proof -
    have e: "signedPoles S - {int j} = insert (- int j) T'" unfolding Teq using jT1 jne by auto
    have "(\<Prod> s \<in> signedPoles S - {int j}. of_int (int j) - of_int s) =
      (a - - a) * poly M a"
      unfolding e polyM using T'f jT2 by (simp add: a_def)
    hence "lr (int j) = - (a ^ 5 * poly M a) / ((a - - a) * poly M a)"
      by (simp add: lr_def linResidue_def polyF a_def)
    also have "\<dots> = - (a ^ 4 / 2)" using a0 PM0[of a] unfolding a5 by (simp add: field_simps)
    finally show ?thesis .
  qed
  have lrmj: "lr (- int j) = - (a ^ 4 / 2)"
  proof -
    have e: "signedPoles S - {- int j} = insert (int j) T'" unfolding Teq using jT2 jne by auto
    have "(\<Prod> s \<in> signedPoles S - {- int j}. of_int (- int j) - of_int s) =
      (- a - a) * poly M (- a)"
      unfolding e polyM using T'f jT1 by (simp add: a_def)
    hence "lr (- int j) = - ((- a) ^ 5 * poly M (- a)) / ((- a - a) * poly M (- a))"
      by (simp add: lr_def linResidue_def polyF a_def)
    also have "\<dots> = - (a ^ 4 / 2)" using a0 PM0[of "- a"] by (simp add: field_simps a5)
    finally show ?thesis .
  qed
  have tp1: "tauPole (int j) = [:H5 j:] - pX" by (simp add: tauPole_def dIdx_def)
  have tp2: "tauPole (- int j) = [:H5 (j - 1):] - pX"
    using j0 by (simp add: tauPole_def dIdx_def nat_diff_distrib')
  have sumres: "(\<Sum> r \<in> signedPoles S. [:lr r:] * tauPole r)
      = [:- (a ^ 4 / 2):] * ([:H5 j:] - pX) + [:- (a ^ 4 / 2):] * ([:H5 (j - 1):] - pX)"
  proof -
    have "(\<Sum> r \<in> T'. [:lr r:] * tauPole r) = 0" by (rule sum.neutral) (simp add: lrT')
    thus ?thesis unfolding Teq using T'f jT1 jT2 jne by (simp add: lrj lrmj tp1 tp2)
  qed
  have "pullbackR S (sqPoleProd S') = [:- (1 / 4):] + ([:- (a ^ 4 / 2):] * ([:H5 j:] - pX)
                                        + [:- (a ^ 4 / 2):] * ([:H5 (j - 1):] - pX))"
    unfolding pullbackR_def F_def[symmetric] tauX_def quot tauG lr_def[symmetric] sumres ..
  also have "\<dots> = muPole j"
  proof (rule poly_eqI)
    fix n
    have H: "H5 j = H5 (j - 1) + 1 / a ^ 5" using H5_Suc_pred[OF j0] by (simp add: a_def)
    show "Polynomial.coeff ([:- (1 / 4):] + ([:- (a ^ 4 / 2):] * ([:H5 j:] - pX)
             + [:- (a ^ 4 / 2):] * ([:H5 (j - 1):] - pX))) n = Polynomial.coeff (muPole j) n"
    proof (cases "n = 0")
      case True
      have i: "a ^ 4 * (1 / a ^ 5) = 1 / a" using a0 unfolding a5 by simp
      have c0L: "Polynomial.coeff ([:- (1 / 4):] + ([:- (a ^ 4 / 2):] * ([:H5 j:] - pX)
             + [:- (a ^ 4 / 2):] * ([:H5 (j - 1):] - pX))) 0
           = - (1 / 4) - a ^ 4 / 2 * H5 j - a ^ 4 / 2 * H5 (j - 1)"
        by (simp add: coeff_monom)
      have c0R: "Polynomial.coeff (muPole j) 0 = - (a ^ 4 * H5 j) - 1 / 4 + 1 / (2 * a)"
        unfolding muPole_def a_def[symmetric] by (simp add: coeff_monom)
      have "- (1 / 4) - a ^ 4 / 2 * H5 j - a ^ 4 / 2 * H5 (j - 1) =
        - (a ^ 4 * H5 j) - 1 / 4 + 1 / (2 * a)"
        unfolding H using i by (simp add: algebra_simps add_divide_distrib)
      thus ?thesis unfolding True c0L c0R .
    next
      case False
      then obtain m where "n = Suc m" by (cases n) auto
      thus ?thesis unfolding muPole_def a_def[symmetric] by (cases m) (simp_all add: coeff_monom)
    qed
  qed
  finally show ?thesis unfolding S'_def .
qed

lemma sq_lagrange:
  assumes S: "finite S"
  shows "P = sqPoleProd S * (P div sqPoleProd S) + (\<Sum> j \<in>
    S. [:sqResidue S P j:] * sqPoleProd (S - {j}))"
proof -
  define g :: "nat \<Rightarrow> rat" where "g j = - (of_nat j ^ 2)" for j
  define S' where "S' = g ` S"
  have inj: "inj_on g S" by (auto intro!: inj_onI simp: g_def)
  have S'f: "finite S'" using S by (simp add: S'_def)
  have fac: "pX - [:g j:] = pX + [:of_nat j ^ 2:]" for j by (simp add: g_def)
  have qp: "qPoleProd (g ` T) = sqPoleProd T" if "T \<subseteq> S" for T
  proof -
    have iT: "inj_on g T" using inj that by (rule inj_on_subset)
    show ?thesis unfolding qPoleProd_def sqPoleProd_def prod.reindex[OF iT] o_def fac ..
  qed
  have rm: "S' - {g j} = g ` (S - {j})" if "j \<in> S" for j
    using inj that unfolding S'_def by (auto simp: inj_on_def)
  have res: "qRes S' P (g j) = sqResidue S P j" if j: "j \<in> S" for j
  proof -
    have i2: "inj_on g (S - {j})" using inj by (rule inj_on_subset) auto
    have "(\<Prod> s' \<in> S' - {g j}. g j - s') = (\<Prod> k \<in> S - {j}. g j - g k)"
      unfolding rm[OF j] by (simp add: prod.reindex[OF i2])
    also have "\<dots> = (\<Prod> k \<in> S - {j}. of_nat k ^ 2 - of_nat j ^ 2)"
      by (simp add: g_def)
    finally show ?thesis by (simp add: qRes_def sqResidue_def g_def)
  qed
  have "P = qPoleProd S' * (P div qPoleProd S') + (\<Sum> s \<in>
    S'. [:qRes S' P s:] * qPoleProd (S' - {s}))"
    by (rule lagrange_decomp[OF S'f])
  also have "qPoleProd S' = sqPoleProd S" unfolding S'_def by (rule qp) simp
  also have "(\<Sum> s \<in> S'. [:qRes S' P s:] * qPoleProd (S' - {s}))
      = (\<Sum> j \<in> S. [:qRes S' P (g j):] * qPoleProd (S' - {g j}))"
    unfolding S'_def by (simp add: sum.reindex[OF inj])
  also have "\<dots> = (\<Sum> j \<in> S. [:sqResidue S P j:] * sqPoleProd (S - {j}))"
    by (rule sum.cong) (simp_all add: res rm qp)
  finally show ?thesis .
qed

theorem pullback_aux:
  assumes S: "finite S" and S0: "0 \<notin> S"
  shows "muX S P = pullbackR S P"
proof -
  define Q where "Q = P div sqPoleProd S"
  define r where "r j = sqResidue S P j" for j
  have P: "P = sqPoleProd S * Q + (\<Sum> j \<in> S. [:r j:] * sqPoleProd (S - {j}))"
    unfolding Q_def r_def by (rule sq_lagrange[OF S])
  have "muX S P = muX S (sqPoleProd S * Q) + (\<Sum> j \<in>
    S. [:r j:] * muX S (sqPoleProd (S - {j})))"
    by (subst P) (simp only: muX_add muX_sum muX_C_mul)
  also have "\<dots> = pullbackR S (sqPoleProd S * Q) + (\<Sum> j \<in>
    S. [:r j:] * pullbackR S (sqPoleProd (S - {j})))"
    by (simp add: pullback_poly[OF S S0] muX_single_pole[OF S] pullbackR_single_pole[OF S S0])
  also have "\<dots> = pullbackR S P"
    by (subst P) (simp only: pullbackR_add pullbackR_sum pullbackR_C_mul)
  finally show ?thesis .
qed


text \<open>@{text "mu_X(R) = \<tau>_X(x^5 R(-x^2))"};
  the numerator picks up @{text "(-1)^{|S|}"} because
  @{text "\<Prod>_{j\<in>S}(j^2 - x^2) = (-1)^{|S|} \<Prod>_{r=\<plusminus>j}(x - r)"}.\<close>
theorem pullback:
  assumes "finite S" "0 \<notin> S"
  shows "muX S P = tauX (signedPoles S) ([:(-1) ^ card S:] * pX ^ 5 * pcompose P (- (pX ^ 2)))"
  using pullback_aux[OF assms] by (simp only: pullbackR_def)

end
