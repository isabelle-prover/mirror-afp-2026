(*  Title:   Zeta5_Truncated_Expansions.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Truncated_Expansions
  imports Zeta5_Far_Poles "HOL-Computational_Algebra.Polynomial_FPS"
begin

section \<open>The truncated \<open>p\<close>-adic layer and Lemma 3.1\<close>

text \<open>Section 3.1 of the paper (Lean theory @{text PadicTau}).  Lean works in
  \<open>\<rat>\<^sub>p\<close> with convergent
  series; here every truncated series is a polynomial, so the difference identity (3.3) for a far
  pole comes with an explicit error polynomial whose coefficients are divisible
    by \<open>p\<^sup>N\<^sup>+\<^sup>1\<close>.  The
  near residues and the analytic part (handled with formal power series) are shown to be integral,
  and Lemma 3.1 is proved in this truncated rational form (@{text tauX_far_pole_valuation}).\<close>

subsection \<open>Truncated expansions of @{text "1/(z - s)"} as polynomials\<close>

text \<open>@{text "farPoly s N = -\<Sum>_{d<N} s^{-(d+1)} z^d"},
  the degree @{text "< N"} truncation of @{text "1/(z - s)"}.\<close>
definition farPoly :: "rat \<Rightarrow> nat \<Rightarrow> rat poly" where
  "farPoly s N = - (\<Sum> d < N. Polynomial.smult (inverse s ^ (d + 1)) (pX ^ d))"

lemma coeff_farPoly:
  "Polynomial.coeff (farPoly s N) d = (if d < N then - (inverse s ^ (d + 1)) else 0)"
  unfolding farPoly_def pX_pow_monom by (simp add: coeff_sum coeff_monom if_distrib[where f =
    "\<lambda>x. _ * x"] cong: if_cong)

lemma degree_farPoly_lt: "0 < N \<Longrightarrow> degree (farPoly s N) < N"
proof -
  assume N: "0 < N"
  have "degree (farPoly s N) \<le> N - 1"
    by (rule degree_le) (use N in \<open>auto simp: coeff_farPoly\<close>)
  thus ?thesis using N by linarith
qed

lemma tau_farPoly: "tau (farPoly s N) = - (\<Sum> d < N. kappa d * inverse s ^ (d + 1))"
  unfolding farPoly_def tau_uminus tau_sum tau_smult tau_X_pow_eq_kappa by (simp add: mult.commute)

text \<open>The truncated series (3.5) is @{text \<tau>} of the truncated expansion.\<close>
lemma tauAnPole_tr_eq_tau: "tauAnPole_tr p s M = tau (farPoly s (M + 3))"
proof -
  have c: "\<And>k. (Suc (Suc (Suc k)) choose 3) * 6 = Suc (Suc (Suc k)) * Suc (Suc k) * Suc k"
  proof -
    fix k :: nat
    show "(Suc (Suc (Suc k)) choose 3) * 6 = Suc (Suc (Suc k)) * Suc (Suc k) * Suc k"
      using choose_falling3[of k 0] by (simp add: numeral_3_eq_3)
  qed
  have kap: "\<And>k. kappa (Suc (Suc (Suc k))) =
    of_nat (Suc (Suc (Suc k)) choose 3) * bernoulli k / 4"
  proof -
    fix k :: nat
    have e: "(of_nat (Suc (Suc (Suc k)) * Suc (Suc k) * Suc k) :: rat) =
      of_nat (Suc (Suc (Suc k)) choose 3) * 6"
      unfolding c[of k, symmetric] by simp
    show "kappa (Suc (Suc (Suc k))) = of_nat (Suc (Suc (Suc k)) choose 3) * bernoulli k / 4"
      unfolding kappa_Suc3 e by simp
  qed
  have pw: "\<And>k. s powi (- (int k + 4)) = inverse s ^ (k + 4)"
  proof -
    fix k :: nat
    have "- (int k + 4) = - int (k + 4)" by simp
    thus "s powi (- (int k + 4)) = inverse s ^ (k + 4)"
      by (simp only: power_int_minus power_int_of_nat power_inverse)
  qed
  have M3: "M + 3 = Suc (Suc (Suc M))" by simp
  have "tau (farPoly s (M + 3)) = - (\<Sum> k <
    M. kappa (Suc (Suc (Suc k))) * inverse s ^ (Suc (Suc (Suc k)) + 1))"
    unfolding tau_farPoly M3 sum.lessThan_Suc_shift
      by (simp add: kappa_0 kappa_Suc_0 kappa_Suc_Suc_0)
  also have "(\<Sum> k < M. kappa (Suc (Suc (Suc k))) * inverse s ^ (Suc (Suc (Suc k)) + 1)) =
             (1 / 4) * (\<Sum> k < M. of_nat ((k + 3) choose 3) * bernoulli k * s powi (- (int k +
               4)))"
    unfolding sum_distrib_left
  proof (rule sum.cong[OF refl])
    fix k :: nat
    have k3: "k + 3 = Suc (Suc (Suc k))" "Suc (Suc (Suc k)) + 1 = k + 4" by simp_all
    show "kappa (Suc (Suc (Suc k))) * inverse s ^ (Suc (Suc (Suc k)) + 1) =
          1 / 4 * (of_nat ((k + 3) choose 3) * bernoulli k * s powi (- (int k + 4)))"
      unfolding kap pw k3 by simp
  qed
  finally show ?thesis unfolding tauAnPole_tr_def by simp
qed

lemma tauAnPole_tr_eq_sum: "tauAnPole_tr p s M = - (\<Sum> d <
  M + 3. kappa d * inverse s ^ (d + 1))"
  by (simp only: tauAnPole_tr_eq_tau tau_farPoly)

text \<open>@{text "(z - s) farPoly s N = 1 - s^{-N} z^N"}.\<close>
lemma farPoly_mul:
  "s \<noteq> 0 \<Longrightarrow> (pX - [:s:]) * farPoly s N =
    1 - Polynomial.smult (inverse s ^ N) (pX ^ N)"
proof -
  assume s: "s \<noteq> 0"
  show ?thesis
  proof (induction N)
    case 0
    show ?case by (simp add: farPoly_def)
  next
    case (Suc N)
    have fs: "farPoly s (Suc N) = farPoly s N - Polynomial.smult (inverse s ^ (N + 1)) (pX ^ N)"
      by (simp add: farPoly_def)
    have m: "(pX - [:s:]) * Polynomial.smult (inverse s ^ (N + 1)) (pX ^ N) =
             Polynomial.smult (inverse s ^ (N + 1)) (pX ^ Suc N) -
               Polynomial.smult (inverse s ^ N) (pX ^ N)"
    proof -
      have e: "s * inverse s ^ (N + 1) = inverse s ^ N" using s by (simp add: field_simps)
      have "(pX - [:s:]) * Polynomial.smult (inverse s ^ (N + 1)) (pX ^ N) =
            Polynomial.smult (inverse s ^ (N + 1)) (pX * pX ^ N) - Polynomial.smult (s *
              inverse s ^ (N + 1)) (pX ^ N)"
        by (simp add: algebra_simps smult_diff_right)
      thus ?thesis unfolding e by simp
    qed
    show ?case unfolding fs right_diff_distrib Suc.IH m by (simp add: algebra_simps)
  qed
qed

text \<open>The shifted-pole correction @{text "farPoly s N (z + 1) - farPoly (s - 1) N"},
  as an explicit polynomial
  whose coefficients are divisible by @{text "p^{N+1}"} when @{text "v_p(s) < 0"}.\<close>
definition hPoly :: "rat \<Rightarrow> nat \<Rightarrow> rat poly" where
  "hPoly s N = Polynomial.smult (inverse (s * (s - 1)))
     (\<Sum> i < N. (Polynomial.smult (inverse (s - 1)) pX) ^ i *
       (Polynomial.smult (inverse s) (pX + 1)) ^ (N - 1 - i))"

lemma vp_sub_one_lt: "prime p \<Longrightarrow> vp p s < 0 \<Longrightarrow> s - 1 \<noteq> 0 \<and>
  vp p (s - 1) < 0"
proof -
  assume p: "prime p" and s: "vp p s < 0"
  have s0: "s \<noteq> 0" using s by (auto simp: vp_def)
  have v1: "vp p (- 1) = 0" by (simp add: vp_def)
  have "s + - 1 \<noteq> 0 \<and> vp p (s + - 1) = vp p s"
    by (rule vp_add_eq_of_lt[OF p s0]) (use s v1 in auto)
  thus ?thesis using s by simp
qed

lemma vpGge_pow: "prime p \<Longrightarrow> vpGge p A a \<Longrightarrow>
  vpGge p (A ^ n) (of_nat n * a)"
proof -
  assume p: "prime p" and A: "vpGge p A a"
  show ?thesis
  proof (induction n)
    case 0 show ?case using vpGge_one by simp
  next
    case (Suc n)
    have "vpGge p (A * A ^ n) (a + of_nat n * a)" by (rule vpGge_mul[OF p A Suc.IH])
    thus ?case by (simp add: algebra_simps)
  qed
qed

lemma vge_inverse_of_vp_lt: "prime p \<Longrightarrow> vp p s < 0 \<Longrightarrow>
  vge p (inverse s) 1"
  by (simp add: vge_def vp_def qmultiplicity_inverse)

lemma smult_as_C_mult: "Polynomial.smult c P = [:c:] * P"
  by simp

lemma vpGge_hPoly:
  assumes "prime p" "vp p s < 0"
  shows "vpGge p (hPoly s N) (of_nat (N + 1))"
proof -
  obtain v1: "vp p (s - 1) < 0" using vp_sub_one_lt[OF assms] by blast
  have is0: "vge p (inverse s) 1" by (rule vge_inverse_of_vp_lt[OF assms])
  have is1: "vge p (inverse (s - 1)) 1" by (rule vge_inverse_of_vp_lt[OF assms(1) v1])
  have c: "vge p (inverse (s * (s - 1))) (1 + 1)"
    unfolding inverse_mult_distrib by (rule vge_mul[OF assms(1) is0 is1])
  define u where "u = Polynomial.smult (inverse (s - 1)) pX"
  define w where "w = Polynomial.smult (inverse s) (pX + 1)"
  have u: "vpGge p u (1 + 0)"
    unfolding u_def smult_as_C_mult by (rule vpGge_mul[OF assms(1) vpGge_C[OF is1] vpGge_pX])
  have w: "vpGge p w (1 + 0)"
    unfolding w_def smult_as_C_mult by (rule vpGge_mul[OF assms(1) vpGge_C[OF is0] vpGge_add[OF
      assms(1) vpGge_pX vpGge_one]])
  have sum: "vpGge p (\<Sum> i < N. u ^ i * w ^ (N - 1 - i)) (of_nat N - 1)"
  proof (rule vpGge_sum[OF assms(1) finite_lessThan])
    fix i assume i: "i \<in> {..<N}"
    have "vpGge p (u ^ i * w ^ (N - 1 - i)) (of_nat i * (1 + 0) + of_nat (N - 1 - i) * (1 + 0))"
      by (rule vpGge_mul[OF assms(1) vpGge_pow[OF assms(1) u] vpGge_pow[OF assms(1) w]])
    moreover have "of_nat i * (1 + 0) + of_nat (N - 1 - i) * (1 + 0) = (of_nat N - 1 :: rat)"
      using i by (simp add: of_nat_diff)
    ultimately show "vpGge p (u ^ i * w ^ (N - 1 - i)) (of_nat N - 1)" by simp
  qed
  have "vpGge p ([:inverse (s * (s - 1)):] * (\<Sum> i <
    N. u ^ i * w ^ (N - 1 - i))) (1 + 1 + (of_nat N - 1))"
    by (rule vpGge_mul[OF assms(1) vpGge_C[OF c] sum])
  hence "vpGge p (Polynomial.smult (inverse (s * (s - 1))) (\<Sum> i <
    N. u ^ i * w ^ (N - 1 - i))) (of_nat (N + 1))"
    unfolding smult_as_C_mult[of _ "\<Sum> i < N. u ^ i * w ^ (N - 1 - i)"]
      by (rule vpGge_mono) simp
  thus ?thesis unfolding hPoly_def u_def w_def .
qed

lemma farPoly_shift:
  assumes "s \<noteq> 0" "s - 1 \<noteq> 0"
  shows "pcompose (farPoly s N) (pX + 1) - farPoly (s - 1) N = hPoly s N"
proof -
  have nz: "pX - [:s - 1:] \<noteq> 0" by (rule pX_minus_const_nonzero)
  have lhs: "(pX - [:s - 1:]) * (pcompose (farPoly s N) (pX + 1) - farPoly (s - 1) N) =
             Polynomial.smult (inverse (s - 1) ^ N) (pX ^ N) -
               Polynomial.smult (inverse s ^ N) ((pX + 1) ^ N)"
  proof -
    have c1: "pcompose (pX - [:s:]) (pX + 1) = pX - [:s - 1:]"
      unfolding pcompose_diff pcompose_pX pcompose_const by (simp add: one_pCons algebra_simps)
    have c2: "pcompose (1 - Polynomial.smult (inverse s ^ N) (pX ^ N)) (pX + 1) =
              1 - Polynomial.smult (inverse s ^ N) ((pX + 1) ^ N)"
      unfolding pcompose_diff pcompose_1 pcompose_smult pcompose_power_left pcompose_pX ..
    have A: "(pX - [:s - 1:]) * pcompose (farPoly s N) (pX + 1) =
      1 - Polynomial.smult (inverse s ^ N) ((pX + 1) ^ N)"
      using arg_cong[OF farPoly_mul[OF assms(1), of N], of "\<lambda>P. pcompose P (pX + 1)"]
        unfolding pcompose_mult c1 c2 .
    have B: "(pX - [:s - 1:]) * farPoly (s - 1) N =
      1 - Polynomial.smult (inverse (s - 1) ^ N) (pX ^ N)"
      by (rule farPoly_mul[OF assms(2)])
    show ?thesis unfolding right_diff_distrib A B by simp
  qed
  have rhs: "(pX - [:s - 1:]) * hPoly s N =
             Polynomial.smult (inverse (s - 1) ^ N) (pX ^ N) -
               Polynomial.smult (inverse s ^ N) ((pX + 1) ^ N)"
  proof -
    define u where "u = Polynomial.smult (inverse (s - 1)) pX"
    define w where "w = Polynomial.smult (inverse s) (pX + 1)"
    have X: "pX = [:0, 1:]" by (simp add: monom_Suc)
    have uw: "u - w = Polynomial.smult (inverse (s * (s - 1))) (pX - [:s - 1:])"
      unfolding pX_minus_const unfolding u_def w_def X using assms
        by (simp add: one_pCons field_simps)
    have tel: "u ^ N - w ^ N = (u - w) * (\<Sum> i < N. u ^ i * w ^ (N - 1 - i))"
      using power_diff_sumr2[of u N w] by (simp add: mult.commute)
    have e1: "(pX - [:s - 1:]) * hPoly s N = (u - w) * (\<Sum> i < N. u ^ i * w ^ (N - 1 - i))"
      unfolding hPoly_def uw u_def[symmetric] w_def[symmetric] by simp
    have uN: "u ^ N = Polynomial.smult (inverse (s - 1) ^ N) (pX ^ N)" unfolding u_def
      by (rule smult_power)
    have wN: "w ^ N = Polynomial.smult (inverse s ^ N) ((pX + 1) ^ N)" unfolding w_def
      by (rule smult_power)
    show ?thesis unfolding e1 tel[symmetric] uN wN ..
  qed
  show ?thesis using lhs rhs nz by (metis mult_cancel_left)
qed

lemma vge_kappa_m4: "prime p \<Longrightarrow> vge p (kappa d) (- 4)"
proof -
  assume p: "prime p"
  have m24: "vp p 24 \<le> 3"
  proof (cases "p = 2")
    case False
    thus ?thesis using vp_24[OF p False] by simp
  next
    case True
    have "multiplicity (2::int) 24 = 3" by (rule multiplicity_eqI) simp_all
    thus ?thesis unfolding True vp_def using qmultiplicity_of_int[of 2 24] by simp
  qed
  have "vp p (inverse 24) = - vp p 24" unfolding vp_def by (rule qmultiplicity_inverse)
  hence i24: "vge p (inverse 24) (- 3)" unfolding vge_def using m24 by simp
  have B: "vge p (bernoulli (d - 3)) (- 1)"
    using vp_bernoulli_ge[OF p, of "d - 3"] unfolding vge_def
      by (metis of_int_le_iff of_int_minus of_int_1)
  have "vge p (of_int (int d * (int d - 1) * (int d - 2)) * bernoulli (d - 3) * inverse 24) (0 + -
    1 + - 3)"
    by (intro vge_mul[OF p] vge_of_int[OF p] B i24)
  note v = this
  have e: "kappa d = of_int (int d * (int d - 1) * (int d - 2)) * bernoulli (d - 3) * inverse 24"
    unfolding kappa_eq by (rule divide_inverse)
  show ?thesis unfolding e by (rule vge_mono[OF v]) simp
qed

lemma vge_tau_of_vpGge: "prime p \<Longrightarrow> vpGge p P b \<Longrightarrow>
  vge p (tau P) (b - 4)"
proof -
  assume p: "prime p" and P: "vpGge p P b"
  have "vge p (tauK P) (b + - 4)"
    unfolding tauK_def by (intro vge_sum[OF p] finite_atMost vge_mul[OF p] vge_kappa_m4[OF p]) (use
      P in \<open>simp add: vpGge_iff\<close>)
  thus ?thesis by (simp add: tauK_eq_tau)
qed

lemma coeff_farPoly_4: "5 \<le> N \<Longrightarrow>
  Polynomial.coeff (farPoly s N) 4 = - (s powi (- 5))"
proof -
  assume "5 \<le> N"
  hence "Polynomial.coeff (farPoly s N) 4 = - (inverse s ^ 5)" by (simp add: coeff_farPoly)
  also have "inverse s ^ 5 = s powi (- 5)" by (simp add: power_int_minus power_inverse)
  finally show ?thesis .
qed

text \<open>The difference identity (3.3)
  for a far pole, with explicit error: the discrepancy equals
  @{text "\<tau>(h)"} and has valuation @{text "\<ge> M"}.\<close>
lemma tauAnPole_tr_sub_eq:
  assumes p: "prime p" and s: "vp p s < 0" and s0: "s \<noteq> 0" and M2: "2 \<le> M"
  shows "vge p (tauAnPole_tr p s M - tauAnPole_tr p (s - 1) M - s powi (- 5)) (of_nat M)"
proof -
  define N where "N = M + 3"
  have s1: "s - 1 \<noteq> 0" using vp_sub_one_lt[OF p s] by simp
  have e1: "tauAnPole_tr p s M - tauAnPole_tr p (s - 1) M - s powi (- 5) =
            tau (farPoly s N) - tau (farPoly (s - 1) N) - s powi (- 5)"
    by (simp only: tauAnPole_tr_eq_tau N_def)
  have e2: "tau (pcompose (farPoly s N) (pX + 1)) - tau (farPoly s N) = - (s powi (- 5))"
    using tau_fwd[of "farPoly s N"] coeff_farPoly_4[of N s] M2 by (simp add: tau_diff N_def)
  have e3: "tau (pcompose (farPoly s N) (pX + 1)) - tau (farPoly (s - 1) N) = tau (hPoly s N)"
    using arg_cong[OF farPoly_shift[OF s0 s1, of N], of tau] by (simp add: tau_diff)
  have v: "vge p (tau (hPoly s N)) (of_nat (N + 1) - 4)"
    by (rule vge_tau_of_vpGge[OF p vpGge_hPoly[OF p s]])
  have "tauAnPole_tr p s M - tauAnPole_tr p (s - 1) M - s powi (- 5) = tau (hPoly s N)"
    using e1 e2 e3 by linarith
  thus ?thesis using v by (simp add: N_def)
qed

text \<open>The difference identity (3.3) for a far pole:
  @{text "\<tau>^{an}(1/(z-s)) - \<tau>^{an}(1/(z-(s-1))) = s^{-5}"} holds in @{text "\<rat>_p"};
    for the partial sums it
  holds modulo any prescribed power of @{text p} once @{text M} is large (Lean:
    @{text tauAnPole_sub}).\<close>
lemma tauAnPole_tr_sub:
  assumes "prime p" "vp p s < 0" "s \<noteq> 0"
  shows "\<exists>M0. \<forall>M \<ge> M0. vge p (tauAnPole_tr p s M - tauAnPole_tr p (s - 1) M -
    s powi (- 5)) B"
proof
  show "\<forall>M \<ge> nat \<lceil>B\<rceil> + 2. vge p (tauAnPole_tr p s M - tauAnPole_tr p (s -
    1) M - s powi (- 5)) B"
  proof (intro allI impI)
    fix M assume M: "nat \<lceil>B\<rceil> + 2 \<le> M"
    have v: "vge p (tauAnPole_tr p s M - tauAnPole_tr p (s - 1) M - s powi (- 5)) (of_nat M)"
      by (rule tauAnPole_tr_sub_eq[OF assms]) (use M in simp)
    have "nat \<lceil>B\<rceil> \<le> M" using M by simp
    hence "\<lceil>B\<rceil> \<le> int M" by (simp add: nat_le_iff)
    hence "(of_int \<lceil>B\<rceil> :: rat) \<le> of_nat M"
      by (metis of_int_le_iff of_int_of_nat_eq)
    hence "B \<le> of_nat M" using le_of_int_ceiling[of B] by linarith
    thus "vge p (tauAnPole_tr p s M - tauAnPole_tr p (s - 1) M - s powi (- 5)) B"
      by (rule vge_mono[OF v])
  qed
qed

subsection \<open>The near residues\<close>

lemma vp_of_int_nonneg: "prime p \<Longrightarrow> of_int r \<noteq> (0 :: rat) \<Longrightarrow>
  0 \<le> vp p (of_int r)"
  by (simp add: vp_def qmultiplicity_of_int)

lemma far_ne_int: "prime p \<Longrightarrow> vp p s = - 1 \<Longrightarrow> s \<noteq> of_int r"
proof -
  assume p: "prime p" and v: "vp p s = - 1"
  show ?thesis
  proof
    assume e: "s = of_int r"
    show False
    proof (cases "(of_int r :: rat) = 0")
      case True thus False using v e by (simp add: vp_def)
    next
      case False thus False using vp_of_int_nonneg[OF p False] v e by simp
    qed
  qed
qed

lemma far_disj: "prime p \<Longrightarrow> (\<And>s. s \<in> F \<Longrightarrow>
  vp p s = - 1) \<Longrightarrow> of_int ` T \<inter> F = {}"
proof -
  assume p: "prime p" and h: "\<And>s. s \<in> F \<Longrightarrow> vp p s = - 1"
  show ?thesis using far_ne_int[OF p h] by blast
qed

text \<open>An integer minus a far pole has valuation exactly @{text "-1"}.\<close>
lemma vp_int_sub_far:
  "prime p \<Longrightarrow> vp p s = - 1 \<Longrightarrow> of_int r - s \<noteq> 0 \<and>
    vp p (of_int r - s) = - 1"
proof -
  assume p: "prime p" and v: "vp p s = - 1"
  have s0: "s \<noteq> 0" using v by (auto simp: vp_def)
  have vm: "vp p (- s) = - 1" using v by (simp add: vp_def)
  show ?thesis
  proof (cases "(of_int r :: rat) = 0")
    case True thus ?thesis using s0 vm by simp
  next
    case False
    have "- s + of_int r \<noteq> 0 \<and> vp p (- s + of_int r) = vp p (- s)"
      by (rule vp_add_eq_of_lt[OF p]) (use s0 vm vp_of_int_nonneg[OF p False] False in auto)
    thus ?thesis using vm by (simp add: algebra_simps)
  qed
qed

lemma vp_int_sub_near:
  "prime p \<Longrightarrow> \<not> int p dvd (r - r') \<Longrightarrow>
    of_int r - of_int r' \<noteq> (0 :: rat) \<and> vp p (of_int r - of_int r') = 0"
proof -
  assume "prime p" and nd: "\<not> int p dvd (r - r')"
  have "r - r' \<noteq> 0" using nd by auto
  moreover have "multiplicity (int p) (r - r') = 0" by (rule not_dvd_imp_multiplicity_0[OF nd])
  ultimately show ?thesis unfolding of_int_diff[symmetric] vp_def
    by (simp add: qmultiplicity_of_int del: of_int_diff)
qed

lemma vp_neg_p_powi: "prime p \<Longrightarrow> vp p ((- of_nat p) powi (- int n)) = - int n"
proof -
  assume p: "prime p"
  have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer)
  have ne: "(- of_nat p :: rat) \<noteq> 0" using prime_gt_0_nat[OF p] by simp
  have "vp p (- of_nat p) = 1" using pe
    by (simp add: vp_def qmultiplicity_of_nat multiplicity_prime)
  with vp_powi_rat[OF p ne, of "- int n"] show ?thesis by simp
qed

text \<open>The near residues are integral (Lean: @{text pt_near_res_vge}): poles @{text T} distinct
  modulo @{text p},
  far poles @{text F} with @{text "v_p(s) = -1"},
    numerator @{text "(-p)^{-|F|} U"} with @{text U} integral.\<close>
lemma near_res_vge:
  assumes p: "prime p" and T: "finite T" and F: "finite F"
    and hT: "\<And>r s. r \<in> T \<Longrightarrow> s \<in> T \<Longrightarrow>
      r \<noteq> s \<Longrightarrow> \<not> int p dvd (r - s)"
    and hF: "\<And>s. s \<in> F \<Longrightarrow>
      vp p s = - 1" and U: "vpGge p U 0" and r: "r \<in> T"
  shows "vge p (qRes (of_int ` T \<union> F) ([:(- of_nat p) powi (- int (card F)):] *
    U) (of_int r)) 0"
proof -
  define Tq :: "rat set" where "Tq = of_int ` T"
  define c where "c = ((- of_nat p) powi (- int (card F)) :: rat)"
  have disj: "Tq \<inter> F = {}" unfolding Tq_def by (rule far_disj[OF p hF])
  have "of_int r \<in> Tq" using r by (simp add: Tq_def)
  with disj have erase: "(Tq \<union> F) - {of_int r} = (Tq - {of_int r}) \<union> F" by auto
  have near: "\<And>x. x \<in> Tq - {of_int r} \<Longrightarrow> of_int r - x \<noteq> 0 \<and>
    vp p (of_int r - x) = 0"
  proof -
    fix x assume "x \<in> Tq - {of_int r}"
    then obtain r' where r': "r' \<in> T" "x = of_int r'" "r' \<noteq> r" unfolding Tq_def by auto
    show "of_int r - x \<noteq> 0 \<and> vp p (of_int r - x) = 0"
      unfolding r'(2) by (rule vp_int_sub_near[OF p hT[OF r r'(1)]]) (use r' in auto)
  qed
  have far: "\<And>s. s \<in> F \<Longrightarrow> of_int r - s \<noteq> 0 \<and>
    vp p (of_int r - s) = - 1"
    using vp_int_sub_far[OF p hF] .
  have den: "(\<Prod> x \<in> (Tq \<union> F) - {of_int r}. of_int r - x) =
             (\<Prod> x \<in> Tq - {of_int r}. of_int r - x) * (\<Prod> s \<in> F. of_int r - s)"
    unfolding erase by (rule prod.union_disjoint) (use disj T F in \<open>auto simp: Tq_def\<close>)
  have den_ne: "(\<Prod> x \<in> Tq - {of_int r}. of_int r - x) * (\<Prod> s \<in>
    F. of_int r - s) \<noteq> 0"
  proof -
    have "finite (Tq - {of_int r})" using T by (simp add: Tq_def)
    hence "(\<Prod> x \<in> Tq - {of_int r}. of_int r - x) \<noteq> 0" using near
      by (simp add: prod_zero_iff)
    moreover have "(\<Prod> s \<in> F. of_int r - s) \<noteq> 0" using F far
      by (simp add: prod_zero_iff)
    ultimately show ?thesis by simp
  qed
  have den_v: "vp p ((\<Prod> x \<in> Tq - {of_int r}. of_int r - x) * (\<Prod> s \<in>
    F. of_int r - s)) = - int (card F)"
  proof -
    have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer)
    have fT: "finite (Tq - {of_int r})" using T by (simp add: Tq_def)
    have A0: "(\<Prod> x \<in> Tq - {of_int r}. of_int r - x) \<noteq> 0" and B0: "(\<Prod> s \<in>
      F. of_int r - s) \<noteq> 0"
      using den_ne by auto
    have "vp p (\<Prod> x \<in> Tq - {of_int r}. of_int r - x) = (\<Sum> x \<in>
      Tq - {of_int r}. vp p (of_int r - x))"
      by (rule vp_prod_rat[OF p fT]) (use near in blast)
    also have "\<dots> = 0" by (rule sum.neutral) (use near in blast)
    finally have vA: "vp p (\<Prod> x \<in> Tq - {of_int r}. of_int r - x) = 0" .
    have "vp p (\<Prod> s \<in> F. of_int r - s) = (\<Sum> s \<in> F. vp p (of_int r - s))"
      by (rule vp_prod_rat[OF p F]) (use far in blast)
    also have "\<dots> = (\<Sum> s \<in> F. - 1)" by (rule sum.cong[OF refl]) (use far in blast)
    finally have vB: "vp p (\<Prod> s \<in> F. of_int r - s) = - int (card F)" by simp
    have "vp p ((\<Prod> x \<in> Tq - {of_int r}. of_int r - x) * (\<Prod> s \<in>
      F. of_int r - s)) =
          vp p (\<Prod> x \<in> Tq - {of_int r}. of_int r - x) + vp p (\<Prod> s \<in>
            F. of_int r - s)"
      using A0 B0 pe by (simp add: vp_def qmultiplicity_mult)
    thus ?thesis using vA vB by simp
  qed
  have num: "vge p (poly ([:c:] * U) (of_int r)) (- of_nat (card F))"
  proof -
    have vc: "vge p c (- of_nat (card F))" unfolding c_def vge_def
      using vp_neg_p_powi[OF p, of "card F"] by simp
    have "vge p (c * poly U (of_int r)) (- of_nat (card F) + 0)"
      by (rule vge_mul[OF p vc vge_poly_eval[OF p U vge_of_int[OF p]]])
    thus ?thesis by simp
  qed
  show ?thesis
    unfolding qRes_def Tq_def[symmetric] c_def[symmetric] den
  proof -
    have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer)
    define n where "n = poly ([:c:] * U) (of_int r)"
    define D where "D = (\<Prod> x \<in> Tq - {of_int r}. of_int r - x) * (\<Prod> s \<in>
      F. of_int r - s)"
    have D0: "D \<noteq> 0" unfolding D_def by (rule den_ne)
    have vD: "vp p D = - int (card F)" unfolding D_def by (rule den_v)
    have vn: "vge p n (- of_nat (card F))" unfolding n_def by (rule num)
    have "vge p (n / D) 0"
    proof (cases "n = 0")
      case True thus ?thesis by (simp add: vge_def)
    next
      case False
      have "vp p (n / D) = vp p n - vp p D" unfolding vp_def using False D0 pe
        by (simp add: qmultiplicity_divide)
      thus ?thesis using vn vD False D0 by (simp add: vge_def)
    qed
    thus "vge p (poly ([:c:] * U) (of_int r) / ((\<Prod> x \<in>
      Tq - {of_int r}. of_int r - x) * (\<Prod> s \<in> F. of_int r - s))) 0"
      unfolding n_def D_def .
  qed
qed

subsection \<open>The analytic part\<close>

text \<open>@{text "-1/(X - s) = \<Sum> s^{-(d+1)} X^d"} as a formal power series.\<close>
definition farSeries :: "rat \<Rightarrow> rat fps" where
  "farSeries s = Abs_fps (\<lambda>d. inverse s ^ (d + 1))"

lemma X_sub_C_mul_farSeries: "s \<noteq> 0 \<Longrightarrow>
  fps_of_poly (pX - [:s:]) * farSeries s = - 1"
proof -
  assume s: "s \<noteq> 0"
  show ?thesis
  proof (rule fps_ext)
    fix n
    show "(fps_of_poly (pX - [:s:]) * farSeries s) $ n = (- 1 :: rat fps) $ n"
    proof (cases n)
      case 0 thus ?thesis using s unfolding pX_minus_const by (simp add: farSeries_def fps_mult_nth)
    next
      case (Suc m)
      have "(fps_of_poly (pX - [:s:]) * farSeries s) $ n =
            - s * inverse s ^ (Suc m + 1) + (\<Sum> i =
              0..m. Polynomial.coeff [:1:] i * inverse s ^ (m - i + 1))"
        unfolding Suc pX_minus_const fps_mult_nth sum.atLeast0_atMost_Suc_shift
          by (simp add: farSeries_def)
      also have "\<dots> = 0" using s by (simp add: atLeast0AtMost coeff_pCons sum.atMost_shift
        field_simps)
      finally show ?thesis using Suc by simp
    qed
  qed
qed

text \<open>The Taylor coefficients of @{text "Q + \<Sum>_{s\<in>F} \<rho>_s/(z - s)"}:
  @{text "\<Pi>_F \<cdot> f = \<Pi>_F Q + \<Sum> \<rho>_s \<Pi>_{F - s}"}.\<close>
lemma qPoleProd_mul_fCoeff:
  assumes "finite F" "\<And>s. s \<in> F \<Longrightarrow> s \<noteq> 0"
  shows "fps_of_poly (qPoleProd F) * Abs_fps (fCoeff Q F \<rho>) =
         fps_of_poly (qPoleProd F * Q + (\<Sum> s \<in> F. [:\<rho> s:] * qPoleProd (F - {s})))"
proof -
  have A: "Abs_fps (fCoeff Q F \<rho>) = fps_of_poly Q - (\<Sum> s \<in>
    F. fps_const (\<rho> s) * farSeries s)"
    by (rule fps_ext) (simp add: fCoeff_def farSeries_def fps_sum_nth)
  have B: "\<And>s. s \<in> F \<Longrightarrow>
    fps_of_poly (qPoleProd F) * farSeries s = - fps_of_poly (qPoleProd (F - {s}))"
  proof -
    fix s assume sF: "s \<in> F"
    have "qPoleProd F = (pX - [:s:]) * qPoleProd (F - {s})" unfolding qPoleProd_def
      using assms(1) sF by (rule prod.remove)
    hence "fps_of_poly (qPoleProd F) * farSeries s =
      fps_of_poly (qPoleProd (F - {s})) * (fps_of_poly (pX - [:s:]) * farSeries s)"
      by (simp only: fps_of_poly_mult ac_simps)
    also have "\<dots> = - fps_of_poly (qPoleProd (F - {s}))"
      using X_sub_C_mul_farSeries[OF assms(2)[OF sF]] by simp
    finally show "fps_of_poly (qPoleProd F) * farSeries s = - fps_of_poly (qPoleProd (F - {s}))" .
  qed
  have "fps_of_poly (qPoleProd F) * Abs_fps (fCoeff Q F \<rho>) =
        fps_of_poly (qPoleProd F * Q) - (\<Sum> s \<in>
          F. fps_const (\<rho> s) * (fps_of_poly (qPoleProd F) * farSeries s))"
    unfolding A by (simp add: fps_of_poly_mult right_diff_distrib sum_distrib_left ac_simps)
  also have "(\<Sum> s \<in> F. fps_const (\<rho> s) * (fps_of_poly (qPoleProd F) * farSeries s)) =
             (\<Sum> s \<in> F. - (fps_const (\<rho> s) * fps_of_poly (qPoleProd (F - {s}))))"
    by (rule sum.cong[OF refl]) (simp add: B)
  also have "fps_of_poly (qPoleProd F * Q) - (\<Sum> s \<in>
    F. - (fps_const (\<rho> s) * fps_of_poly (qPoleProd (F - {s})))) =
             fps_of_poly (qPoleProd F * Q + (\<Sum> s \<in> F. [:\<rho> s:] * qPoleProd (F - {s})))"
    by (simp add: sum_negf fps_of_poly_add fps_of_poly_sum fps_of_poly_mult fps_of_poly_smult)
  finally show ?thesis .
qed

text \<open>If @{text "\<Psi> f = N"} as power series, with @{text "\<Psi>(0)"} a unit,
  the other coefficients of @{text \<Psi>} in
  @{text "p\<int>_p"}, @{text N} integral and @{text "\<equiv> 0 (mod p)"} beyond degree
    @{text "p+1"}, then so is @{text f}.\<close>
lemma series_vge:
  assumes p: "prime p" and P0: "Polynomial.coeff \<Psi> 0 \<noteq>
    0" and P0v: "vp p (Polynomial.coeff \<Psi> 0) = 0"
    and P1: "\<And>n. 1 \<le> n \<Longrightarrow> vge p (Polynomial.coeff \<Psi> n) 1"
    and N0: "vpGge p N 0" and N1: "\<And>d. p + 1 < d \<Longrightarrow>
      vge p (Polynomial.coeff N d) 1"
    and mul: "fps_of_poly \<Psi> * Abs_fps f = fps_of_poly N"
  shows "vge p (f d) 0 \<and> (p + 1 < d \<longrightarrow> vge p (f d) 1)"
proof (induction d rule: less_induct)
  case (less d)
  have fd: "f d = inverse (Polynomial.coeff \<Psi> 0) *
              (Polynomial.coeff N d - (\<Sum> i <
                d. Polynomial.coeff \<Psi> (i + 1) * f (d - (i + 1))))"
  proof -
    have "Polynomial.coeff N d = (fps_of_poly \<Psi> * Abs_fps f) $ d" unfolding mul by simp
    also have "\<dots> = (\<Sum> i \<le> d. Polynomial.coeff \<Psi> i * f (d - i))"
      by (simp add: fps_mult_nth atLeast0AtMost)
    also have "\<dots> = Polynomial.coeff \<Psi> 0 * f d + (\<Sum> i <
      d. Polynomial.coeff \<Psi> (Suc i) * f (d - Suc i))"
      by (simp add: sum.atMost_shift)
    finally have e: "Polynomial.coeff \<Psi> 0 * f d = Polynomial.coeff N d - (\<Sum> i <
      d. Polynomial.coeff \<Psi> (Suc i) * f (d - Suc i))"
      by simp
    show ?thesis using P0 by (simp add: e[symmetric] mult.assoc[symmetric])
  qed
  have S: "vge p (\<Sum> i < d. Polynomial.coeff \<Psi> (i + 1) * f (d - (i + 1))) 1"
  proof (rule vge_sum[OF p finite_lessThan])
    fix i assume i: "i \<in> {..<d}"
    have "d - (i + 1) < d" using i by auto
    hence fi: "vge p (f (d - (i + 1))) 0" using less.IH by blast
    have "vge p (Polynomial.coeff \<Psi> (i + 1) * f (d - (i + 1))) (1 + 0)"
      by (rule vge_mul[OF p P1 fi]) simp
    thus "vge p (Polynomial.coeff \<Psi> (i + 1) * f (d - (i + 1))) 1" by simp
  qed
  have inv: "vge p (inverse (Polynomial.coeff \<Psi> 0)) 0"
    using P0v by (simp add: vge_def vp_def qmultiplicity_inverse)
  have Nd: "vge p (Polynomial.coeff N d) 0" using N0 by (simp add: vpGge_iff)
  have S0: "vge p (\<Sum> i < d. Polynomial.coeff \<Psi> (i + 1) * f (d - (i + 1))) 0"
    by (rule vge_mono[OF S]) simp
  have "vge p (f d) 0" unfolding fd using vge_mul[OF p inv vge_diff[OF p Nd S0]] by simp
  moreover have "vge p (f d) 1" if dd: "p + 1 < d"
    unfolding fd using vge_mul[OF p inv vge_diff[OF p N1[OF dd] S]] by simp
  ultimately show ?case by blast
qed

text \<open>The shape of @{text "\<Psi> = \<Prod> (p s - p z)"}: unit constant term,
  other coefficients in @{text "p\<int>_p"}.\<close>
definition PsiShape :: "nat \<Rightarrow> rat poly \<Rightarrow> bool" where
  "PsiShape p P \<longleftrightarrow> Polynomial.coeff P 0 \<noteq> 0 \<and>
    vp p (Polynomial.coeff P 0) = 0 \<and>
                   (\<forall>n. 1 \<le> n \<longrightarrow> vge p (Polynomial.coeff P n) 1)"

lemma PsiShape_one: "PsiShape p 1"
  by (auto simp: PsiShape_def vp_def vge_def one_pCons coeff_pCons split: nat.splits)

lemma PsiShape_vpGge: "prime p \<Longrightarrow> PsiShape p P \<Longrightarrow> vpGge p P 0"
proof -
  assume "PsiShape p P"
  hence a: "Polynomial.coeff P 0 \<noteq> 0" "vp p (Polynomial.coeff P 0) = 0" "\<And>n. 1 \<le>
    n \<Longrightarrow> vge p (Polynomial.coeff P n) 1"
    unfolding PsiShape_def by auto
  show ?thesis unfolding vpGge_iff
  proof
    fix i show "vge p (Polynomial.coeff P i) 0"
    proof (cases i)
      case 0 thus ?thesis using a by (simp add: vge_def)
    next
      case (Suc j) thus ?thesis by (intro vge_mono[OF a(3)[of i]]) simp_all
    qed
  qed
qed

lemma PsiShape_mult: "prime p \<Longrightarrow> PsiShape p P \<Longrightarrow>
  PsiShape p Q \<Longrightarrow> PsiShape p (P * Q)"
proof -
  assume p: "prime p" and P: "PsiShape p P" and Q: "PsiShape p Q"
  have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer)
  have P0: "vpGge p P 0" by (rule PsiShape_vpGge[OF p P])
  have Q0: "vpGge p Q 0" by (rule PsiShape_vpGge[OF p Q])
  from P have a: "Polynomial.coeff P 0 \<noteq> 0" "vp p (Polynomial.coeff P 0) =
    0" "\<And>n. 1 \<le> n \<Longrightarrow> vge p (Polynomial.coeff P n) 1"
    unfolding PsiShape_def by auto
  from Q have b: "Polynomial.coeff Q 0 \<noteq> 0" "vp p (Polynomial.coeff Q 0) =
    0" "\<And>n. 1 \<le> n \<Longrightarrow> vge p (Polynomial.coeff Q n) 1"
    unfolding PsiShape_def by auto
  have c0: "Polynomial.coeff (P * Q) 0 = Polynomial.coeff P 0 * Polynomial.coeff Q 0"
    by (simp add: coeff_mult)
  have hi: "\<And>n. 1 \<le> n \<Longrightarrow> vge p (Polynomial.coeff (P * Q) n) 1"
  proof -
    fix n :: nat assume n: "1 \<le> n"
    show "vge p (Polynomial.coeff (P * Q) n) 1" unfolding coeff_mult
    proof (rule vge_sum[OF p finite_atMost])
      fix i assume i: "i \<in> {..n}"
      show "vge p (Polynomial.coeff P i * Polynomial.coeff Q (n - i)) 1"
      proof (cases "i = 0")
        case True
        have q: "vge p (Polynomial.coeff Q (n - i)) 1" by (rule b(3)) (use True n in simp)
        have "vge p (Polynomial.coeff P i * Polynomial.coeff Q (n - i)) (0 + 1)"
          by (rule vge_mul[OF p _ q]) (use P0 in \<open>simp add: vpGge_iff\<close>)
        thus ?thesis by simp
      next
        case False
        have q: "vge p (Polynomial.coeff P i) 1" by (rule a(3)) (use False in simp)
        have "vge p (Polynomial.coeff P i * Polynomial.coeff Q (n - i)) (1 + 0)"
          by (rule vge_mul[OF p q]) (use Q0 in \<open>simp add: vpGge_iff\<close>)
        thus ?thesis by simp
      qed
    qed
  qed
  show ?thesis unfolding PsiShape_def using a b c0 hi pe by (simp add: vp_def qmultiplicity_mult)
qed

lemma PsiShape_prod:
  "prime p \<Longrightarrow> finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow>
    PsiShape p (f i)) \<Longrightarrow> PsiShape p (\<Prod> i \<in> I. f i)"
proof -
  assume p: "prime p" and fin: "finite I" and h: "\<And>i. i \<in> I \<Longrightarrow>
    PsiShape p (f i)"
  show ?thesis using fin h
  proof (induction I rule: finite_induct)
    case empty thus ?case by (simp add: PsiShape_one)
  next
    case (insert x F)
    have "PsiShape p (f x)" using insert.prems by simp
    moreover have "PsiShape p (\<Prod> i \<in> F. f i)" using insert.prems by (intro insert.IH) simp
    ultimately show ?case using insert.hyps by (simp add: PsiShape_mult[OF p])
  qed
qed

text \<open>A factor @{text "p s - p z"} with @{text "v_p(s) = -1"}.\<close>
lemma PsiShape_factor: "prime p \<Longrightarrow> vp p s = - 1 \<Longrightarrow>
  PsiShape p [:of_nat p * s, - of_nat p:]"
proof -
  assume p: "prime p" and v: "vp p s = - 1"
  have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer)
  have s0: "s \<noteq> 0" using v by (auto simp: vp_def)
  have p0: "(of_nat p :: rat) \<noteq> 0" using prime_gt_0_nat[OF p] by simp
  have vpp: "vp p (of_nat p) = 1" using pe
    by (simp add: vp_def qmultiplicity_of_nat multiplicity_prime)
  have c0: "vp p (of_nat p * s) = 0"
  proof -
    have "vp p (of_nat p * s) = vp p (of_nat p) + vp p s" using pe p0 s0
      by (simp add: vp_def qmultiplicity_mult)
    thus ?thesis using vpp v by simp
  qed
  have hi: "\<And>n. 1 \<le> n \<Longrightarrow>
    vge p (Polynomial.coeff [:of_nat p * s, - of_nat p:] n) 1"
  proof -
    fix n :: nat assume n: "1 \<le> n"
    show "vge p (Polynomial.coeff [:of_nat p * s, - of_nat p:] n) 1"
    proof (cases "n = 1")
      case True thus ?thesis using vge_neg[OF vge_p_self[OF p]] by simp
    next
      case False
      define k where "k = n - 2"
      have nk: "n = Suc (Suc k)" unfolding k_def using n False by arith
      show ?thesis unfolding nk by (simp add: vge_zero)
    qed
  qed
  show ?thesis unfolding PsiShape_def using p0 s0 c0 hi by simp
qed

text \<open>Division by an integral monic polynomial preserves "@{text "\<equiv> 0 (mod p)"} beyond
  degree @{text "p+1"}".\<close>
lemma degree_div_le_rat: "degree (x div y) \<le> degree (x :: rat poly)"
proof (cases "y = 0 \<or> x div y = 0")
  case True thus ?thesis by auto
next
  case False
  hence y: "y \<noteq> 0" and q: "x div y \<noteq> 0" by auto
  have dq: "degree (y * (x div y)) = degree y + degree (x div y)" using y q by (rule degree_mult_eq)
  have "degree (y * (x div y) + x mod y) = degree (y * (x div y))"
  proof (cases "x mod y = 0")
    case True thus ?thesis by simp
  next
    case False
    have "degree (x mod y) < degree y" using degree_mod_less[OF y, of x] False by blast
    hence "degree (x mod y) < degree (y * (x div y))" using dq by linarith
    thus ?thesis by (rule degree_add_eq_left)
  qed
  hence "degree x = degree (y * (x div y))" by (simp only: mult_div_mod_eq)
  thus ?thesis using dq by simp
qed

lemma div_lead1_high:
  assumes p: "prime p" and R0: "vpGge p R 0" and R1: "\<And>d. p + 1 < d \<Longrightarrow>
    vge p (Polynomial.coeff R d) 1"
    and Q1: "lead_coeff Q = 1" and Q0: "vpGge p Q 0" and d: "p + 1 < d"
  shows "vge p (Polynomial.coeff (R div Q) d) 1"
proof -
  define Rlo where "Rlo = (\<Sum> i < p + 2. Polynomial.monom (Polynomial.coeff R i) i)"
  define Rhi where "Rhi = Polynomial.smult (1 / of_nat p) (R - Rlo)"
  have coeff_Rlo: "\<And>i. Polynomial.coeff Rlo i = (if i <
    p + 2 then Polynomial.coeff R i else 0)"
    unfolding Rlo_def by (simp add: coeff_sum coeff_monom)
  have split: "R = Rlo + Polynomial.smult (of_nat p) Rhi"
  proof -
    have "(of_nat p :: rat) \<noteq> 0" using prime_gt_0_nat[OF p] by simp
    thus ?thesis unfolding Rhi_def by simp
  qed
  have Rhi0: "vpGge p Rhi 0"
    unfolding vpGge_iff
  proof
    fix i
    show "vge p (Polynomial.coeff Rhi i) 0"
    proof (cases "i < p + 2")
      case True thus ?thesis by (simp add: Rhi_def coeff_Rlo vge_zero)
    next
      case False
      hence "Polynomial.coeff Rhi i = 1 / of_nat p * Polynomial.coeff R i"
        by (simp add: Rhi_def coeff_Rlo)
      moreover have "vge p (1 / of_nat p * Polynomial.coeff R i) (- 1 + 1)"
        by (rule vge_mul[OF p vge_inv_p[OF p] R1]) (use False in simp)
      ultimately show ?thesis by simp
    qed
  qed
  have deg: "degree (Rlo div Q) \<le> p + 1"
  proof -
    have "degree Rlo \<le> p + 1" by (rule degree_le) (simp add: coeff_Rlo)
    thus ?thesis using degree_div_le_rat[of Rlo Q] by linarith
  qed
  have "R div Q = Rlo div Q + Polynomial.smult (of_nat p) (Rhi div Q)"
    by (subst split) (simp add: poly_div_add_left div_smult_left)
  hence "Polynomial.coeff (R div Q) d = of_nat p * Polynomial.coeff (Rhi div Q) d"
    using deg d by (simp add: coeff_eq_0)
  thus ?thesis
    using vge_mul[OF p vge_p_self[OF p] vpGge_div_monic[OF p Rhi0 Q1 Q0, unfolded vpGge_iff,
      rule_format, of d]] by simp
qed

lemma card_le_prime_of_distinct_mod:
  assumes "prime p" "finite T" "\<And>r s. r \<in> T \<Longrightarrow> s \<in> T \<Longrightarrow>
    r \<noteq> s \<Longrightarrow> \<not> int p dvd (r - s)"
  shows "card T \<le> p"
proof -
  have pp: "0 < int p" using prime_gt_0_nat[OF assms(1)] by simp
  have inj: "inj_on (\<lambda>r. nat (r mod int p)) T"
  proof (rule inj_onI)
    fix r s assume r: "r \<in> T" and s: "s \<in> T" and e: "nat (r mod int p) = nat (s mod int p)"
    have "r mod int p = s mod int p" using e pp by (simp add: eq_nat_nat_iff pos_mod_sign)
    hence "int p dvd (r - s)" by (simp add: mod_eq_dvd_iff)
    thus "r = s" using assms(3)[OF r s] by blast
  qed
  have "card T = card ((\<lambda>r. nat (r mod int p)) ` T)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card {..<p}"
    by (rule card_mono) (use pp in \<open>auto simp: nat_less_iff pos_mod_sign
      pos_mod_bound\<close>)
  finally show ?thesis by simp
qed

lemma vpGge_qPoleProd_int:
  "prime p \<Longrightarrow> finite A \<Longrightarrow> A \<subseteq> of_int ` T \<Longrightarrow>
    vpGge p (qPoleProd A) 0"
proof -
  assume p: "prime p" and A: "finite A" and sub: "A \<subseteq> of_int ` T"
  have "vpGge p (\<Prod> s \<in> A. pX - [:s:]) (\<Sum> s \<in> A. 0)"
  proof (rule vpGge_prod[OF p A])
    fix s assume "s \<in> A"
    then obtain r where s: "s = of_int r" using sub by auto
    show "vpGge p (pX - [:s:]) 0" unfolding s diff_conv_add_uminus
      by (rule vpGge_add[OF p vpGge_pX vpGge_neg[OF vpGge_C[OF vge_of_int[OF p]]]])
  qed
  thus ?thesis by (simp add: qPoleProd_def)
qed

text \<open>The analytic part is integral (Lean: @{text pt_far_vge}): every @{text "\<kappa>_d f_d"}
  is @{text p}-integral,
  @{text "f_d"} the Taylor coefficients of @{text "Q + \<Sum>_{s\<in>F} \<rho>_s/(z-s)"}.\<close>
lemma far_vge:
  assumes p: "prime p" and p7: "7 \<le> p" and T: "finite T" and F: "finite F"
    and hT: "\<And>r s. r \<in> T \<Longrightarrow> s \<in> T \<Longrightarrow>
      r \<noteq> s \<Longrightarrow> \<not> int p dvd (r - s)"
    and hF: "\<And>s. s \<in> F \<Longrightarrow> vp p s = - 1"
    and U0: "vpGge p U 0" and U1: "\<And>d. p + 1 < d \<Longrightarrow>
      vge p (Polynomial.coeff U d) 1"
  shows "vge p (kappa d * fCoeff (([:(- of_nat p) powi (- int (card F)):] *
    U) div qPoleProd (of_int ` T \<union> F))
                   F (qRes (of_int ` T \<union> F) ([:(- of_nat p) powi (- int (card F)):] *
                     U)) d) 0"
proof -
  define Tq :: "rat set" where "Tq = of_int ` T"
  define S where "S = Tq \<union> F"
  define c where "c = ((- of_nat p) powi (- int (card F)) :: rat)"
  define U' where "U' = [:c:] * U"
  define Q where "Q = U' div qPoleProd S"
  define \<rho> where "\<rho> = qRes S U'"
  have finT: "finite Tq" and finS: "finite S" by (simp_all add: Tq_def S_def T F)
  have disj: "Tq \<inter> F = {}" unfolding Tq_def by (rule far_disj[OF p hF])
  have F0: "\<And>s. s \<in> F \<Longrightarrow> s \<noteq> 0"
  proof -
    fix s assume "s \<in> F"
    hence "vp p s = - 1" by (rule hF)
    thus "s \<noteq> 0" by (auto simp: vp_def)
  qed
  have p0: "(of_nat p :: rat) \<noteq> 0" using p by (simp add: prime_gt_0_nat)
  \<comment> \<open>the Lagrange decomposition, split into near and far poles\<close>
  define Mq where "Mq = qPoleProd F * Q + (\<Sum> s \<in> F. [:\<rho> s:] * qPoleProd (F - {s}))"
  define W0 where "W0 = (\<Sum> r \<in> Tq. [:\<rho> r:] * qPoleProd (Tq - {r}))"
  have Lag: "U' = qPoleProd Tq * Mq + qPoleProd F * W0"
  proof -
    have qU: "\<And>A B. finite A \<Longrightarrow> finite B \<Longrightarrow>
      A \<inter> B = {} \<Longrightarrow> qPoleProd (A \<union> B) = qPoleProd A * qPoleProd B"
      unfolding qPoleProd_def by (rule prod.union_disjoint)
    have L: "U' = qPoleProd S * Q + (\<Sum> s \<in> S. [:\<rho> s:] * qPoleProd (S - {s}))"
      unfolding Q_def \<rho>_def by (rule lagrange_decomp[OF finS])
    have P: "qPoleProd S = qPoleProd Tq * qPoleProd F" unfolding S_def by (rule qU[OF finT F disj])
    have sumS: "(\<Sum> s \<in> S. [:\<rho> s:] * qPoleProd (S - {s})) =
                (\<Sum> s \<in> Tq. [:\<rho> s:] * qPoleProd (S - {s})) + (\<Sum> s \<in>
                  F. [:\<rho> s:] * qPoleProd (S - {s}))"
      unfolding S_def by (rule sum.union_disjoint[OF finT F disj])
    have sT: "(\<Sum> s \<in> Tq. [:\<rho> s:] * qPoleProd (S - {s})) = qPoleProd F * W0"
    proof -
      have "(\<Sum> s \<in> Tq. [:\<rho> s:] * qPoleProd (S - {s})) = (\<Sum> r \<in>
        Tq. qPoleProd F * ([:\<rho> r:] * qPoleProd (Tq - {r})))"
      proof (rule sum.cong[OF refl])
        fix r assume r: "r \<in> Tq"
        have "S - {r} = (Tq - {r}) \<union> F" using r disj unfolding S_def by auto
        hence "qPoleProd (S - {r}) = qPoleProd (Tq - {r}) * qPoleProd F"
          using qU[of "Tq - {r}" F] finT F disj by auto
        thus "[:\<rho> r:] * qPoleProd (S - {r}) =
          qPoleProd F * ([:\<rho> r:] * qPoleProd (Tq - {r}))" by (simp add: ac_simps)
      qed
      thus ?thesis unfolding W0_def by (simp add: sum_distrib_left)
    qed
    have sF: "(\<Sum> s \<in> F. [:\<rho> s:] * qPoleProd (S - {s})) =
      qPoleProd Tq * (\<Sum> s \<in> F. [:\<rho> s:] * qPoleProd (F - {s}))"
    proof -
      have "(\<Sum> s \<in> F. [:\<rho> s:] * qPoleProd (S - {s})) = (\<Sum> s \<in>
        F. qPoleProd Tq * ([:\<rho> s:] * qPoleProd (F - {s})))"
      proof (rule sum.cong[OF refl])
        fix s assume s: "s \<in> F"
        have "S - {s} = Tq \<union> (F - {s})" using s disj unfolding S_def by auto
        hence "qPoleProd (S - {s}) = qPoleProd Tq * qPoleProd (F - {s})"
          using qU[of Tq "F - {s}"] finT F disj by auto
        thus "[:\<rho> s:] * qPoleProd (S - {s}) =
          qPoleProd Tq * ([:\<rho> s:] * qPoleProd (F - {s}))" by (simp add: ac_simps)
      qed
      thus ?thesis by (simp add: sum_distrib_left)
    qed
    show ?thesis unfolding Mq_def by (subst L) (simp only: P sumS sT sF algebra_simps)
  qed
  \<comment> \<open>clearing the constant @{text c}\<close>
  define kap where "kap = ((- of_nat p) ^ card F :: rat)"
  have kc: "kap * c = 1"
    unfolding kap_def c_def power_int_minus power_int_of_nat using p0 by simp
  define Psi where "Psi = (\<Prod> s \<in> F. [:of_nat p * s, - of_nat p:])"
  have Psi_eq: "Psi = [:kap:] * qPoleProd F"
  proof -
    have f: "\<And>s. [:of_nat p * s, - of_nat p:] = [:- of_nat p:] * (pX - [:s:])"
      unfolding pX_minus_const by simp
    have "Psi = (\<Prod> s \<in> F. [:- of_nat p:] * (pX - [:s:]))" unfolding Psi_def f ..
    also have "\<dots> = [:- of_nat p:] ^ card F * qPoleProd F"
      by (simp only: prod.distrib prod_constant qPoleProd_def)
    also have "\<dots> = [:kap:] * qPoleProd F" by (simp only: kap_def const_poly_power)
    finally show ?thesis .
  qed
  define Nq where "Nq = [:kap:] * Mq"
  have Ueq: "U = qPoleProd Tq * Nq + Psi * W0"
  proof -
    have "U = [:kap:] * U'" unfolding U'_def mult.assoc[symmetric] using kc
      by (simp add: mult.commute[of c kap])
    also have "\<dots> = qPoleProd Tq * Nq + Psi * W0" unfolding Lag Nq_def Psi_eq
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have Ndiv: "Nq = (U - Psi * W0) div qPoleProd Tq"
  proof -
    have nz: "qPoleProd Tq \<noteq> 0" using qPoleProd_monic[OF finT] by auto
    have e: "U - Psi * W0 = qPoleProd Tq * Nq" using Ueq by simp
    show ?thesis unfolding e using nz by simp
  qed
  \<comment> \<open>integrality\<close>
  have \<rho>T: "\<And>r. r \<in> Tq \<Longrightarrow> vge p (\<rho> r) 0"
  proof -
    fix r assume "r \<in> Tq"
    then obtain r' where r': "r' \<in> T" "r = of_int r'" unfolding Tq_def by auto
    show "vge p (\<rho> r) 0" unfolding r'(2) \<rho>_def S_def U'_def c_def Tq_def
      by (rule near_res_vge[OF p T F hT hF U0 r'(1)])
  qed
  have W0i: "vpGge p W0 0"
    unfolding W0_def
  proof (rule vpGge_sum[OF p finT])
    fix r assume r: "r \<in> Tq"
    have "vpGge p ([:\<rho> r:] * qPoleProd (Tq - {r})) (0 + 0)"
      by (rule vpGge_mul[OF p vpGge_C[OF \<rho>T[OF r]] vpGge_qPoleProd_int[OF p]]) (use finT in
        \<open>auto simp: Tq_def\<close>)
    thus "vpGge p ([:\<rho> r:] * qPoleProd (Tq - {r})) 0" by simp
  qed
  have shape: "PsiShape p Psi"
    unfolding Psi_def by (rule PsiShape_prod[OF p F]) (rule PsiShape_factor[OF p hF])
  have Psii: "vpGge p Psi 0" by (rule PsiShape_vpGge[OF p shape])
  have Ri: "vpGge p (U - Psi * W0) 0"
  proof -
    have "vpGge p (Psi * W0) 0" using vpGge_mul[OF p Psii W0i] by simp
    thus ?thesis unfolding diff_conv_add_uminus by (rule vpGge_add[OF p U0 vpGge_neg])
  qed
  have W0deg: "\<And>j. p \<le> j \<Longrightarrow> Polynomial.coeff W0 j = 0"
  proof -
    fix j assume j: "p \<le> j"
    have cT: "card Tq \<le> p" unfolding Tq_def
      using card_image_le[OF T, of "of_int :: int \<Rightarrow> rat"]
        card_le_prime_of_distinct_mod[OF p T] hT by fastforce
    have z: "\<And>r. r \<in> Tq \<Longrightarrow>
      Polynomial.coeff ([:\<rho> r:] * qPoleProd (Tq - {r})) j = 0"
    proof -
      fix r assume r: "r \<in> Tq"
      have "degree ([:\<rho> r:] * qPoleProd (Tq - {r})) \<le> degree (qPoleProd (Tq - {r}))"
        by (simp add: degree_smult_le)
      also have "\<dots> = card (Tq - {r})" using finT by (simp add: degree_qPoleProd)
      finally have dg: "degree ([:\<rho> r:] * qPoleProd (Tq - {r})) < p"
        using card_Diff1_less[OF finT r] cT by linarith
      show "Polynomial.coeff ([:\<rho> r:] * qPoleProd (Tq - {r})) j = 0"
        by (rule coeff_eq_0) (use dg j in linarith)
    qed
    show "Polynomial.coeff W0 j = 0" unfolding W0_def coeff_sum
      by (rule sum.neutral) (use z in blast)
  qed
  have R1: "\<And>d. p + 1 < d \<Longrightarrow> vge p (Polynomial.coeff (U - Psi * W0) d) 1"
  proof -
    fix d assume d: "p + 1 < d"
    have sh: "\<And>n. 1 \<le> n \<Longrightarrow> vge p (Polynomial.coeff Psi n) 1" using shape
      unfolding PsiShape_def by blast
    have "vge p (Polynomial.coeff (Psi * W0) d) 1" unfolding coeff_mult
    proof (rule vge_sum[OF p finite_atMost])
      fix i assume i: "i \<in> {..d}"
      show "vge p (Polynomial.coeff Psi i * Polynomial.coeff W0 (d - i)) 1"
      proof (cases "i = 0")
        case True
        have "Polynomial.coeff W0 (d - i) = 0" using True d by (intro W0deg) simp
        thus ?thesis by (simp add: vge_zero)
      next
        case False
        have q: "vge p (Polynomial.coeff Psi i) 1" by (rule sh) (use False in simp)
        have "vge p (Polynomial.coeff Psi i * Polynomial.coeff W0 (d - i)) (1 + 0)"
          by (rule vge_mul[OF p q]) (use W0i in \<open>simp add: vpGge_iff\<close>)
        thus ?thesis by simp
      qed
    qed
    thus "vge p (Polynomial.coeff (U - Psi * W0) d) 1" unfolding coeff_diff
      by (rule vge_diff[OF p U1[OF d]])
  qed
  have TqT: "Tq \<subseteq> of_int ` T" by (simp add: Tq_def)
  have Ni: "vpGge p Nq 0"
    unfolding Ndiv by (rule vpGge_div_monic[OF p Ri qPoleProd_monic[OF finT] vpGge_qPoleProd_int[OF
      p finT TqT]])
  have N1: "\<And>d. p + 1 < d \<Longrightarrow> vge p (Polynomial.coeff Nq d) 1"
    unfolding Ndiv by (rule div_lead1_high[OF p Ri R1 qPoleProd_monic[OF finT]
      vpGge_qPoleProd_int[OF p finT TqT]])
  \<comment> \<open>the power series identity\<close>
  have mul: "fps_of_poly Psi * Abs_fps (fCoeff Q F \<rho>) = fps_of_poly Nq"
    unfolding Psi_eq Nq_def Mq_def fps_of_poly_mult mult.assoc
      by (subst qPoleProd_mul_fCoeff[OF F F0]) simp_all
  have f: "vge p (fCoeff Q F \<rho> d) 0 \<and> (p + 1 < d \<longrightarrow>
    vge p (fCoeff Q F \<rho> d) 1)"
    using shape unfolding PsiShape_def by (intro series_vge[OF p _ _ _ Ni N1 mul]) blast+
  \<comment> \<open>the factor @{text "\<kappa>_d"}\<close>
  have "vge p (kappa d * fCoeff Q F \<rho> d) 0"
  proof (cases "p + 1 < d")
    case True
    have k: "vge p (kappa d) (- 1)"
      using kappa_padicVal_ge[OF p, of d] p7 by (auto simp: vge_def)
    show ?thesis using vge_mul[OF p k conjunct2[OF f, rule_format, OF True]] by simp
  next
    case False
    have k: "vge p (kappa d) 0"
      using kappa_integral[OF p p7, of d] False by (auto simp: vge_def)
    show ?thesis using vge_mul[OF p k conjunct1[OF f]] by simp
  qed
  thus ?thesis by (simp add: Q_def \<rho>_def U'_def S_def Tq_def c_def)
qed

subsection \<open>Lemma 3.1 with far poles, truncated rational form\<close>

lemma tauPoleP_tr_near: "tauPoleP_tr p Y (of_int r) M = [:H5 (dIdx r):] - Y"
  by (simp add: tauPoleP_tr_def)

lemma far_denom_ne_1: "prime p \<Longrightarrow> vp p s = - 1 \<Longrightarrow>
  snd (quotient_of s) \<noteq> 1"
proof -
  assume p: "prime p" and v: "vp p s = - 1"
  show ?thesis
  proof
    assume d1: "snd (quotient_of s) = 1"
    obtain n d where q: "quotient_of s = (n, d)" by (cases "quotient_of s")
    hence "s = of_int n / of_int d" by (rule quotient_of_div)
    with d1 q have "s = of_int n" by simp
    thus False using far_ne_int[OF p v, of n] by simp
  qed
qed

lemma tauPoleP_tr_far: "prime p \<Longrightarrow> vp p s = - 1 \<Longrightarrow>
  tauPoleP_tr p Y s M = [:tauAnPole_tr p s M:]"
  by (simp add: tauPoleP_tr_def far_denom_ne_1)

lemma vge_H5_small: "prime p \<Longrightarrow> n < p \<Longrightarrow> vge p (H5 n) 0"
proof -
  assume p: "prime p" and n: "n < p"
  show ?thesis unfolding H5_def
  proof (rule vge_sum[OF p finite_atLeastAtMost])
    fix v assume v: "v \<in> {1..n}"
    have nd: "\<not> p dvd v" using v n by (auto dest: dvd_imp_le)
    have "vge p (inverse (of_nat v) ^ 5) 0" by (rule vge_pow[OF p vge_inverse_unit[OF p nd]])
    thus "vge p (1 / of_nat v ^ 5) 0" by (simp add: inverse_eq_divide power_one_over)
  qed
qed

text \<open>Lemma 3.1 with far poles, rational form (Lean: @{text lemma_3_1_rat}): with @{text "Y"}
  integral,
  near poles @{text T} distinct modulo @{text p} and @{text "d(r) < p"},
    far poles @{text F} with @{text "v_p(s) = -1"},
  numerator @{text "(-p)^{-|F|} U"} with @{text U} integral and @{text "\<equiv> 0 (mod p)"} beyond
    degree @{text "p+1"},
  the truncated @{text "\<tau>^{ext}_Y"} is integral.  The truncation must cover the polynomial
    part: @{text "deg U \<le> M"}.\<close>
lemma sum_const_poly: "(\<Sum> i \<in> I. [:f i:]) = [:\<Sum> i \<in> I. f i:]"
  by (induction I rule: infinite_finite_induct) simp_all

theorem tauX_far_pole_valuation:
  assumes p: "prime p" and p7: "7 \<le> p" and T: "finite T" and F: "finite F"
    and hT: "\<And>r s. r \<in> T \<Longrightarrow> s \<in> T \<Longrightarrow>
      r \<noteq> s \<Longrightarrow> \<not> int p dvd (r - s)" and hd: "\<And>r. r \<in>
      T \<Longrightarrow> dIdx r < p"
    and hF: "\<And>s. s \<in> F \<Longrightarrow> vp p s = - 1"
    and Y: "vpGge p Y 0"
    and U0: "vpGge p U 0" and U1: "\<And>d. p + 1 < d \<Longrightarrow>
      vge p (Polynomial.coeff U d) 1"
    and dU: "degree U \<le> M"
  shows "vpGge p (tauExt_tr p Y ([:(- of_nat p) powi (- int (card F)):] *
    U) (of_int ` T \<union> F) M) 0"
proof -
  define Tq :: "rat set" where "Tq = of_int ` T"
  define S where "S = Tq \<union> F"
  define c where "c = ((- of_nat p) powi (- int (card F)) :: rat)"
  define U' where "U' = [:c:] * U"
  define Q where "Q = U' div qPoleProd S"
  define \<rho> where "\<rho> = qRes S U'"
  have disj: "Tq \<inter> F = {}" unfolding Tq_def by (rule far_disj[OF p hF])
  have inj: "inj_on (of_int :: int \<Rightarrow> rat) T" by (simp add: inj_on_def)
  have dQ: "degree Q < M + 3"
  proof -
    have "degree Q \<le> degree U'" unfolding Q_def by (rule degree_div_le_rat)
    also have "\<dots> \<le> degree U" unfolding U'_def by (simp add: degree_smult_le)
    finally show ?thesis using dU by linarith
  qed
  have Ext: "tauExt_tr p Y U' S M =
      [:tauK Q:] + (\<Sum> r \<in> T. [:\<rho> (of_int r):] * ([:H5 (dIdx r):] - Y)) +
        (\<Sum> s \<in> F. [:\<rho> s * tauAnPole_tr p s M:])"
  proof -
    have finTq: "finite Tq" using T by (simp add: Tq_def)
    have e1: "tauExt_tr p Y U' S M = [:tauK Q:] + (\<Sum> s \<in>
      S. [:\<rho> s:] * tauPoleP_tr p Y s M)"
      unfolding tauExt_tr_def Q_def \<rho>_def ..
    have e2: "(\<Sum> s \<in> S. [:\<rho> s:] * tauPoleP_tr p Y s M) =
              (\<Sum> s \<in> Tq. [:\<rho> s:] * tauPoleP_tr p Y s M) + (\<Sum> s \<in>
                F. [:\<rho> s:] * tauPoleP_tr p Y s M)"
      unfolding S_def by (rule sum.union_disjoint[OF finTq F disj])
    have e3: "(\<Sum> s \<in> Tq. [:\<rho> s:] * tauPoleP_tr p Y s M) = (\<Sum> r \<in>
      T. [:\<rho> (of_int r):] * ([:H5 (dIdx r):] - Y))"
      unfolding Tq_def sum.reindex[OF inj] by (simp add: tauPoleP_tr_near)
    have e4: "(\<Sum> s \<in> F. [:\<rho> s:] * tauPoleP_tr p Y s M) = (\<Sum> s \<in>
      F. [:\<rho> s * tauAnPole_tr p s M:])"
      by (rule sum.cong[OF refl]) (simp add: tauPoleP_tr_far[OF p hF])
    show ?thesis unfolding e1 e2 e3 e4 by (simp only: add.assoc)
  qed
  have analytic: "tauK Q + (\<Sum> s \<in> F. \<rho> s * tauAnPole_tr p s M) = (\<Sum> d <
    M + 3. kappa d * fCoeff Q F \<rho> d)"
  proof -
    have t: "tauK Q = (\<Sum> d < M + 3. Polynomial.coeff Q d * kappa d)"
    proof -
      have "tauK Q = (\<Sum> d \<in> {..degree Q}. Polynomial.coeff Q d * kappa d)"
        by (simp add: tauK_def)
      also have "\<dots> = (\<Sum> d \<in> {..<M + 3}. Polynomial.coeff Q d * kappa d)"
        by (rule sum.mono_neutral_left) (use dQ in \<open>auto simp: coeff_eq_0\<close>)
      finally show ?thesis .
    qed
    have "(\<Sum> s \<in> F. \<rho> s * tauAnPole_tr p s M) = - (\<Sum> s \<in> F. \<Sum> d <
      M + 3. kappa d * (\<rho> s * inverse s ^ (d + 1)))"
      unfolding tauAnPole_tr_eq_sum by (simp add: sum_distrib_left sum_negf mult_ac)
    also have "(\<Sum> s \<in> F. \<Sum> d < M + 3. kappa d * (\<rho> s * inverse s ^ (d + 1))) =
               (\<Sum> d < M + 3. \<Sum> s \<in> F. kappa d * (\<rho> s * inverse s ^ (d + 1)))"
                 by (rule sum.swap)
    finally have a: "(\<Sum> s \<in> F. \<rho> s * tauAnPole_tr p s M) = - (\<Sum> d <
      M + 3. \<Sum> s \<in> F. kappa d * (\<rho> s * inverse s ^ (d + 1)))" .
    show ?thesis unfolding t a fCoeff_def
      by (simp add: right_diff_distrib sum_subtractf sum_distrib_left mult_ac)
  qed
  have an_int: "vge p (\<Sum> d < M + 3. kappa d * fCoeff Q F \<rho> d) 0"
    unfolding Q_def \<rho>_def U'_def S_def Tq_def c_def
    by (intro vge_sum[OF p] finite_lessThan) (blast intro: far_vge[OF p p7 T F hT hF U0 U1])
  have \<rho>T: "\<And>r. r \<in> T \<Longrightarrow> vge p (\<rho> (of_int r)) 0"
    unfolding \<rho>_def U'_def S_def Tq_def c_def by (blast intro: near_res_vge[OF p T F hT hF U0])
  have near_int: "\<And>r. r \<in> T \<Longrightarrow>
    vpGge p ([:\<rho> (of_int r):] * ([:H5 (dIdx r):] - Y)) 0"
  proof -
    fix r assume r: "r \<in> T"
    have h: "vpGge p ([:H5 (dIdx r):] - Y) 0" unfolding diff_conv_add_uminus
      by (rule vpGge_add[OF p vpGge_C[OF vge_H5_small[OF p hd[OF r]]] vpGge_neg[OF Y]])
    show "vpGge p ([:\<rho> (of_int r):] * ([:H5 (dIdx r):] - Y)) 0"
      using vpGge_mul[OF p vpGge_C[OF \<rho>T[OF r]] h] by simp
  qed
  have const: "[:tauK Q:] + (\<Sum> s \<in> F. [:\<rho> s * tauAnPole_tr p s M:]) = [:\<Sum> d <
    M + 3. kappa d * fCoeff Q F \<rho> d:]"
    unfolding sum_const_poly analytic[symmetric] by simp
  have e: "[:tauK Q:] + (\<Sum> r \<in> T. [:\<rho> (of_int r):] * ([:H5 (dIdx r):] - Y)) +
    (\<Sum> s \<in> F. [:\<rho> s * tauAnPole_tr p s M:]) =
           [:\<Sum> d < M + 3. kappa d * fCoeff Q F \<rho> d:] + (\<Sum> r \<in>
             T. [:\<rho> (of_int r):] * ([:H5 (dIdx r):] - Y))"
    unfolding const[symmetric] by (simp only: ac_simps)
  have "vpGge p (tauExt_tr p Y U' S M) 0"
    unfolding Ext e by (rule vpGge_add[OF p vpGge_C[OF an_int] vpGge_sum[OF p T near_int]])
  thus ?thesis by (simp add: U'_def S_def Tq_def c_def)
qed

end
