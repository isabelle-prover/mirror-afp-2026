(*  Title:   Zeta5_Asymptotics.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Asymptotics
  imports Zeta5_Integral_Representation Prime_Sum_Limits Zeta5_Explicit_Integrals
    Zeta5_Uniform_Asymptotics
begin

section \<open>Normalisation and the asymptotics of \<open>Q\<^sub>K\<^sub>,\<^sub>M\<close>:
  Propositions 5.1 and 5.2\<close>

text \<open>Section 5 of the paper: the standing hypotheses, Legendre's formula and the uniformity
  estimates, integrality of \<open>Q\<^sub>K\<^sub>,\<^sub>M\<close> (Proposition 5.1,
    @{text QKM_int_poly}), the small-prime sum, the
  prime sums through the prime number theorem,
    and the limit (5.21) of \<open>K\<^sup>-\<^sup>2 ln m\<^sub>K\<^sub>,\<^sub>M\<close>
  (Proposition 5.2, @{text log_mKM_limsup},
    @{text log_mKM_limsup_AM}).  Lean theories @{text Section5},
  @{text Prop51}, @{text Legendre5}, @{text PrimeSums}, @{text PNT}, @{text Prop52},
  @{text Section5Final}.\<close>

subsection \<open>The small-prime sum\<close>

lemma hof_le_lam: "real (hof K) \<le> lam_r * real K"
  using of_nat_div_le_of_nat[of "37 * K" 40] by (simp add: hof_def lam_r_def)

text \<open>Small primes @{text "p \<le> K/M"}: the contribution of @{text "-L_p"} is
  @{text "6\<lambda>K^2/M + o(K^2)"}.\<close>
theorem small_prime_sum_bound:
  assumes M: "0 < M" and e: "0 < \<epsilon>"
  shows "\<forall>\<^sub>F K in at_top.
    (\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> p * M \<le> K}.
        real (6 * hof K * nat_log p (5 * K) + hof K * multiplicity p (24::nat)) * ln (real p))
      \<le> (6 * lam_r / real M + \<epsilon>) * real K ^ 2"
proof -
  define \<delta> where "\<delta> = \<epsilon> / 13"
  have d0: "0 < \<delta>" unfolding \<delta>_def using e by simp
  have Mr: "0 < real M" using M by simp
  have "\<forall>\<^sub>F K :: nat in at_top. primes_theta (1 / real M * real K) - primes_theta (0 *
    real K) \<le> (1 / real M - 0 + \<delta>) * real K"
    by (rule cell_upper) (use Mr d0 in simp_all)
  moreover have "\<forall>\<^sub>F K :: nat in at_top. 2 * ln (real (5 * K)) * sqrt (real (5 *
    K)) \<le> \<delta> * real K"
    by (rule eventually_psi_theta_small[OF d0])
  moreover have "\<forall>\<^sub>F K :: nat in at_top. 25 * ln 24 / \<delta> \<le> real K"
    using filterlim_real_sequentially unfolding filterlim_at_top by simp
  ultimately show ?thesis
    using eventually_gt_at_top[of "0 :: nat"]
  proof (eventually_elim)
    case (elim K)
    let ?s = "{p. p \<le> K \<and> prime p \<and> p * M \<le> K}"
    have fin: "finite ?s" by simp
    have Kr: "0 < real K" using elim(4) by simp
    have split: "(\<Sum> p \<in> ?s. real (6 * hof K * nat_log p (5 * K) + hof K *
      multiplicity p (24::nat)) * ln (real p))
        = 6 * real (hof K) * ((\<Sum> p \<in> ?s. ln (real p)) + (\<Sum> p \<in>
          ?s. (real (nat_log p (5 * K)) - 1) * ln (real p)))
          + real (hof K) * (\<Sum> p \<in> ?s. real (multiplicity p (24::nat)) * ln (real p))"
    proof -
      have pw: "real (6 * hof K * nat_log p (5 * K) + hof K * multiplicity p (24::nat)) *
        ln (real p) =
          6 * real (hof K) * (ln (real p) + (real (nat_log p (5 * K)) - 1) * ln (real p)) +
            real (hof K) * (real (multiplicity p (24::nat)) * ln (real p))" for p
        by (simp add: algebra_simps)
      show ?thesis unfolding pw by (simp add: sum.distrib sum_distrib_left[symmetric])
    qed
    have th: "(\<Sum> p \<in> ?s. ln (real p)) = primes_theta (1 / real M * real K)"
    proof -
      have nn: "0 \<le> 1 / real M * real K" by simp
      have seq: "?s = {p. prime p \<and> real p \<le> 1 / real M * real K}"
      proof (intro equalityI subsetI)
        fix p assume "p \<in> ?s"
        hence p: "prime p" "p * M \<le> K" by auto
        have "real p * real M \<le> real K" using p(2) by (metis of_nat_mult of_nat_le_iff)
        hence "real p \<le> 1 / real M * real K" using Mr by (simp add: field_simps)
        thus "p \<in> {p. prime p \<and> real p \<le> 1 / real M * real K}" using p(1) by simp
      next
        fix p assume "p \<in> {p. prime p \<and> real p \<le> 1 / real M * real K}"
        hence p: "prime p" "real p \<le> 1 / real M * real K" by auto
        have "real p * real M \<le> real K" using p(2) Mr by (simp add: field_simps)
        hence pM: "p * M \<le> K" by (metis of_nat_mult of_nat_le_iff)
        have "p \<le> p * M" using M by simp
        hence "p \<le> K" using pM by (rule le_trans)
        thus "p \<in> ?s" using p(1) pM by simp
      qed
      show ?thesis unfolding seq theta_eq_sum[OF nn] ..
    qed
    have psi: "(\<Sum> p \<in> ?s. (real (nat_log p (5 * K)) - 1) * ln (real p)) \<le>
      2 * ln (real (5 * K)) * sqrt (real (5 * K))"
    proof -
      have "(\<Sum> p \<in> ?s. (real (nat_log p (5 * K)) - 1) * ln (real p)) \<le> (\<Sum> p \<in>
        {p. prime p \<and> p \<le> 5 * K}. (real (nat_log p (5 * K)) - 1) * ln (real p))"
      proof (rule sum_mono2)
        show "finite {p. prime p \<and> p \<le> 5 * K}" by simp
        show "?s \<subseteq> {p. prime p \<and> p \<le> 5 * K}" by fastforce
        fix p assume "p \<in> {p. prime p \<and> p \<le> 5 * K} - ?s"
        hence p: "prime p" "p \<le> 5 * K" by auto
        have p1: "1 < p" using p(1) by (rule prime_gt_1_nat)
        have "Suc 1 \<le> floorlog p (5 * K)" by (rule floorlog_ge_SucI) (use p p1 in simp_all)
        hence "1 \<le> nat_log p (5 * K)" unfolding nat_log_def by linarith
        moreover have "0 \<le> ln (real p)" using p1 by simp
        ultimately show "0 \<le> (real (nat_log p (5 * K)) - 1) * ln (real p)" by simp
      qed
      also have "\<dots> \<le> 2 * ln (real (5 * K)) * sqrt (real (5 * K))"
        by (rule psi_minus_theta_sum) (use elim(4) in simp)
      finally show ?thesis .
    qed
    have s24: "(\<Sum> p \<in> ?s. real (multiplicity p (24::nat)) * ln (real p)) \<le> 25 * ln 24"
    proof -
      have "(\<Sum> p \<in> ?s. real (multiplicity p (24::nat)) * ln (real p)) \<le> (\<Sum> p \<in>
        ?s. if p \<le> 24 then ln 24 else 0)"
        by (rule sum_mono) (simp add: mult24_log_le)
      also have "\<dots> \<le> (\<Sum> p \<in> {..24::nat}. ln 24)"
      proof -
        have "(\<Sum> p \<in> ?s. if p \<le> 24 then ln 24 else (0::real)) = (\<Sum> p \<in>
          ?s \<inter> {..24}. ln 24)"
          using sum.inter_restrict[OF fin, of "\<lambda>p. ln (24::real)" "{..24}"] by simp
        also have "\<dots> \<le> (\<Sum> p \<in> {..24::nat}. ln 24)"
          by (rule sum_mono2) (simp_all add: ln_ge_zero)
        finally show ?thesis .
      qed
      finally show ?thesis by (simp add: card_atMost)
    qed
    have h24: "25 * ln 24 \<le> \<delta> * real K" using elim(3) d0
      by (simp add: divide_le_eq mult.commute)
    have hh: "real (hof K) \<le> lam_r * real K" by (rule hof_le_lam)
    have hh0: "0 \<le> real (hof K)" by simp
    have A: "(\<Sum> p \<in> ?s. ln (real p)) + (\<Sum> p \<in>
      ?s. (real (nat_log p (5 * K)) - 1) * ln (real p)) \<le> (1 / real M + 2 * \<delta>) * real K"
      using elim(1) elim(2) psi unfolding th
    proof -
      have "primes_theta (0 * real K) = 0" by (simp add: primes_theta_def prime_sum_upto_def)
      hence "primes_theta (1 / real M * real K) \<le> (1 / real M + \<delta>) * real K"
        using elim(1) by simp
      thus "primes_theta (1 / real M * real K) + (\<Sum> p \<in>
        ?s. (real (nat_log p (5 * K)) - 1) * ln (real p)) \<le>
        (1 / real M + 2 * \<delta>) * real K"
        using elim(2) psi by (simp add: algebra_simps)
    qed
    let ?X = "(\<Sum> p \<in> ?s. ln (real p)) + (\<Sum> p \<in>
      ?s. (real (nat_log p (5 * K)) - 1) * ln (real p))"
    let ?Y = "\<Sum> p \<in> ?s. real (multiplicity p (24::nat)) * ln (real p)"
    have A0: "0 \<le> (1 / real M + 2 * \<delta>) * real K" using Mr d0 Kr by simp
    have "6 * real (hof K) * ?X \<le> 6 * real (hof K) * ((1 / real M + 2 * \<delta>) * real K)"
      by (rule mult_left_mono[OF A]) simp
    also have "\<dots> \<le> 6 * (lam_r * real K) * ((1 / real M + 2 * \<delta>) * real K)"
      by (rule mult_right_mono[OF _ A0]) (use hh in simp)
    finally have e12: "6 * real (hof K) * ?X \<le>
      6 * (lam_r * real K) * ((1 / real M + 2 * \<delta>) * real K)" .
    from s24 h24 have "?Y \<le> \<delta> * real K" by linarith
    hence "real (hof K) * ?Y \<le> real (hof K) * (\<delta> * real K)"
      by (rule mult_left_mono[OF _ hh0])
    also have "\<dots> \<le> (lam_r * real K) * (\<delta> * real K)"
      by (rule mult_right_mono[OF hh]) (use d0 Kr in simp)
    finally have e34: "real (hof K) * ?Y \<le> (lam_r * real K) * (\<delta> * real K)" .
    have q: "6 * (lam_r * real K) * ((1 / real M + 2 * \<delta>) * real K) + (lam_r * real K) *
      (\<delta> * real K) =
        (6 * lam_r / real M + lam_r * \<epsilon>) * real K ^ 2"
      unfolding \<delta>_def using Mr by (simp add: field_simps power2_eq_square)
    have le: "lam_r * \<epsilon> \<le> \<epsilon>" using e by (simp add: lam_r_def)
    have K2: "0 \<le> real K ^ 2" by simp
    have r: "(6 * lam_r / real M + lam_r * \<epsilon>) * real K ^ 2 \<le>
      (6 * lam_r / real M + \<epsilon>) * real K ^ 2"
      by (rule mult_right_mono[OF _ K2]) (use le in simp)
    show ?case unfolding split using e12 e34 q r by linarith
  qed
qed

subsection \<open>Standing hypotheses and integrality\<close>

text \<open>The standing hypotheses of Theorem 2.1.\<close>
definition StdHyp :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "StdHyp K M \<longleftrightarrow> 40 \<le> M \<and> 40 dvd K \<and> 0 < K \<and>
    200 * M ^ 2 \<le> K"

lemma mKM_pos: "0 < mKM K M"
  unfolding mKM_def
  by (fastforce simp: power_int_def prime_gt_0_nat intro: prod_pos)

text \<open>A rational polynomial that is @{text p}-integral at every prime has integer
  coefficients.\<close>
lemma int_of_vge:
  assumes "\<And>p. prime p \<Longrightarrow> vge p x 0"
  shows "\<exists>n::int. x = of_int n"
proof (cases "x = 0")
  case True
  thus ?thesis by (intro exI[of _ 0]) simp
next
  case False
  obtain a b where ab: "quotient_of x = (a, b)" by (cases "quotient_of x")
  have b0: "b > 0" using quotient_of_denom_pos[OF ab] .
  have "b = 1"
  proof (rule ccontr)
    assume "b \<noteq> 1"
    hence "nat b \<noteq> 1" using b0 by simp
    then obtain p where p: "prime p" "p dvd nat b" using prime_factor_nat by blast
    have "0 \<le> qmultiplicity (int p) x"
      using assms[OF p(1)] False by (simp add: vge_def vp_def)
    hence "\<not> int p dvd snd (quotient_of x)"
      by (rule qmultiplicity_nonneg_imp_not_dvd_denom) (use prime_gt_1_nat[OF p(1)] in simp)
    moreover have "int p dvd int (nat b)"
      using p(2) by (simp only: int_dvd_int_iff)
    ultimately show False using ab b0 by simp
  qed
  thus ?thesis using quotient_of_div[OF ab] by auto
qed

lemma intPoly_of_vge:
  assumes "\<And>p. prime p \<Longrightarrow> vpGge p Q 0"
  shows "\<exists>P :: int poly. map_poly of_int P = Q"
proof -
  have int: "\<exists>m::int. Polynomial.coeff Q n = of_int m" for n
    by (rule int_of_vge) (use assms in \<open>auto simp: vpGge_def vge_def\<close>)
  define f :: "rat \<Rightarrow> int" where "f c = (SOME m. c = of_int m)" for c
  have f0: "f 0 = 0"
    unfolding f_def by (rule some_equality) auto
  have fc: "of_int (f (Polynomial.coeff Q n)) = Polynomial.coeff Q n" for n
    unfolding f_def by (rule sym, rule someI_ex[OF int[of n]])
  show ?thesis
    by (intro exI[of _ "map_poly f Q"] poly_eqI) (simp add: coeff_map_poly f0 fc)
qed


subsection \<open>Legendre's formula and the uniformity estimates\<close>

text \<open>(5.3), Legendre's formula for @{text "v_p(S_K)"} (@{text "K > 0"};
  false at @{text "K = 0"}).\<close>
theorem vpS_legendre:
  assumes "prime p" "40 dvd K" "0 < K"
  defines "B \<equiv> 2 * hof K + K + 1"
  shows "vpS K p = 2 * int (hof K) * (\<Sum> a = 1..B. int (K div p ^ a))
                   - 12 * int (hof K) * (\<Sum> a = 1..B. int (Nof K div p ^ a))
                   - 2 * (\<Sum> i = 1..hof K - 1. \<Sum> a = 1..B. int (2 * i div p ^ a))
                   + (int (hof K) - 1) * int (multiplicity p (4::nat))"
proof -
  define h where "h = hof K"
  define N where "N = Nof K"
  have pe: "prime_elem p" using assms(1) by simp
  have pei: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  have "40 \<le> K" using assms(2,3) by (auto elim!: dvdE)
  hence h1: "1 \<le> h" unfolding h_def hof_def by linarith
  have NK: "N \<le> K" unfolding N_def Nof_def by linarith
  define A :: nat where "A = fact K ^ (2 * h) * 4 ^ (h - 1)"
  define D :: nat where "D = fact N ^ (12 * h) * (\<Prod> i = 1..h - 1. fact (2 * i) ^ 2)"
  have A0: "A \<noteq> 0" and D0: "D \<noteq> 0" by (simp_all add: A_def D_def)
  have SK: "SK K = of_nat A / of_nat D" by (simp add: SK_def A_def D_def h_def N_def)
  have v: "vpS K p = int (multiplicity p A) - int (multiplicity p D)"
    unfolding vpS_def vp_def SK using A0 D0 pei
    by (simp add: qmultiplicity_divide qmultiplicity_of_nat multiplicity_int)
  have mA: "multiplicity p A = 2 * h * multiplicity p (fact K) + (h - 1) * multiplicity p (4::nat)"
    unfolding A_def using pe
    by (simp add: prime_elem_multiplicity_mult_distrib prime_elem_multiplicity_power_distrib)
  have mD: "multiplicity p D = 12 * h * multiplicity p (fact N)
              + (\<Sum> i = 1..h - 1. 2 * multiplicity p (fact (2 * i)))"
  proof -
    have "multiplicity p (\<Prod> i = 1..h - 1. fact (2 * i) ^ 2) = (\<Sum> i =
      1..h - 1. multiplicity p (fact (2 * i) ^ 2))"
      by (rule prime_elem_multiplicity_prod_distrib[OF pe]) auto
    also have "\<dots> = (\<Sum> i = 1..h - 1. 2 * multiplicity p (fact (2 * i)))"
      by (rule sum.cong) (use pe in \<open>simp_all add:
        prime_elem_multiplicity_power_distrib\<close>)
    finally have P: "multiplicity p (\<Prod> i = 1..h - 1. fact (2 * i) ^ 2) = (\<Sum> i =
      1..h - 1. 2 * multiplicity p (fact (2 * i)))" .
    show ?thesis unfolding D_def using pe
      by (subst prime_elem_multiplicity_mult_distrib) (simp_all add: P[unfolded One_nat_def]
        prime_elem_multiplicity_power_distrib)
  qed
  have LK: "multiplicity p (fact K) = (\<Sum> a = 1..B. K div p ^ a)"
    by (rule legendre_sum[OF assms(1)]) (simp add: B_def)
  have LN: "multiplicity p (fact N) = (\<Sum> a = 1..B. N div p ^ a)"
    by (rule legendre_sum[OF assms(1)]) (use NK in \<open>simp add: B_def\<close>)
  have Li: "multiplicity p (fact (2 * i)) = (\<Sum> a = 1..B. 2 * i div p ^ a)"
    if "i \<in> {1..h - 1}" for i
    by (rule legendre_sum[OF assms(1)]) (use that in \<open>auto simp: B_def h_def\<close>)
  have mD': "multiplicity p D = 12 * h * (\<Sum> a = 1..B. N div p ^ a)
              + (\<Sum> i = 1..h - 1. 2 * (\<Sum> a = 1..B. 2 * i div p ^ a))"
    unfolding mD LN by (simp add: Li)
  have iA: "int (multiplicity p A) = 2 * int h * (\<Sum> a =
    1..B. int (K div p ^ a)) + (int h - 1) * int (multiplicity p (4::nat))"
    unfolding mA LK of_nat_add of_nat_mult of_nat_diff[OF h1] of_nat_sum by simp
  have iD: "int (multiplicity p D) = 12 * int h * (\<Sum> a = 1..B. int (N div p ^ a))
              + 2 * (\<Sum> i = 1..h - 1. \<Sum> a = 1..B. int (2 * i div p ^ a))"
    unfolding mD' of_nat_add of_nat_mult of_nat_sum by (simp add: sum_distrib_left)
  show ?thesis unfolding v iA iD h_def N_def by simp
qed

subsection \<open>Proposition 5.1\<close>

lemma vp_prime_powi:
  assumes "prime p" "prime q"
  shows "vp p (of_nat q powi k) = (if q = p then k else 0)"
proof -
  have q0: "(of_nat q :: rat) \<noteq> 0" using assms(2) by (simp add: prime_gt_0_nat)
  have "vp p (of_nat q) = (if q = p then 1 else 0)"
    using assms by (auto simp: vp_def qmultiplicity_of_nat multiplicity_int prime_multiplicity_other
                                multiplicity_prime)
  thus ?thesis using vp_powi_rat[OF assms(1) q0, of k] by simp
qed

lemma vp_mKM:
  assumes "prime p"
  shows "vp p (mKM K M) = (if p \<le> 2 * hof K then - Lp K M p else 0)"
proof -
  let ?Q = "{q. q \<le> 2 * hof K \<and> prime q}"
  have "vp p (mKM K M) = (\<Sum> q \<in> ?Q. vp p (of_nat q powi (- Lp K M q)))"
    unfolding mKM_def by (rule vp_prod_rat[OF assms]) (auto simp: prime_gt_0_nat)
  also have "\<dots> = (\<Sum> q \<in> ?Q. if q = p then - Lp K M q else 0)"
    by (rule sum.cong) (use assms in \<open>auto simp: vp_prime_powi\<close>)
  also have "\<dots> = (if p \<le> 2 * hof K then - Lp K M p else 0)"
    using assms by (simp add: sum.delta')
  finally show ?thesis .
qed

lemma vpS_eq_0_large:
  assumes "prime p" "40 dvd K" "0 < K" "2 * hof K < p"
  shows "vpS K p = 0"
proof -
  define B where "B = 2 * hof K + K + 1"
  have K40: "40 \<le> K" using assms(2,3) by (auto elim!: dvdE)
  obtain k where k: "K = 40 * k" using assms(2) by (elim dvdE)
  have hk: "hof K = 37 * k" unfolding k hof_def by simp
  have Kp: "K < p" using assms(4) hk k by linarith
  have NK: "Nof K \<le> K" unfolding Nof_def by linarith
  have p1: "p \<le> p ^ a" if "1 \<le> a" for a
    using that prime_gt_1_nat[OF assms(1)] by (simp add: self_le_power)
  have z1: "K div p ^ a = 0" if "a \<in> {1..B}" for a using that p1[of a] Kp
    by (auto intro!: div_less)
  have z2: "Nof K div p ^ a = 0" if "a \<in> {1..B}" for a using that p1[of a] Kp NK
    by (auto intro!: div_less)
  have z3: "2 * i div p ^ a = 0" if "i \<in> {1..hof K - 1}" "a \<in> {1..B}" for i a
    using that p1[of a] assms(4) by (auto intro!: div_less)
  have p4: "\<not> p dvd 4"
  proof
    assume "p dvd 4"
    hence "p \<le> 4" by (rule dvd_imp_le) simp
    thus False using assms(4) K40 hk k by linarith
  qed
  have m4: "multiplicity p (4::nat) = 0" by (rule not_dvd_imp_multiplicity_0[OF p4])
  show ?thesis
    unfolding vpS_legendre[OF assms(1-3), folded B_def] using z1 z2 z3 m4 by simp
qed

lemma QKM_vpGge:
  assumes "StdHyp K M" "prime p"
  shows "vpGge p (QKM K M) 0"
proof -
  from assms(1) have M40: "40 \<le> M" and K40d: "40 dvd K" and K0: "0 <
    K" and KM: "200 * M ^ 2 \<le> K"
    by (auto simp: StdHyp_def)
  obtain k where k: "K = 40 * k" using K40d by (elim dvdE)
  have hk: "hof K = 37 * k" unfolding k hof_def Nof_def by simp_all
  have K2h: "K \<le> 2 * hof K" using hk k by simp
  have SKi: "vpGge p [:SK K:] (of_int (vpS K p))" unfolding vpS_def by (rule vpGge_C_vp)
  have F: "vpGge p (FK K) (of_int (Lp K M p))"
  proof (cases "p * M \<le> K")
    case True
    have "vpGge p (FK K) (- 6 * of_nat (hof K) * of_nat (nat_log p (5 * K))
                         - of_nat (hof K) * of_nat (multiplicity p (24::nat)))"
      by (rule vpG_F_ge[OF assms(2) K40d])
    thus ?thesis using True by (simp add: Lp_def)
  next
    case nb1: False
    show ?thesis
    proof (cases "3 * p \<le> K")
      case True
      have IH: "InnerHyp K M p" using M40 K40d K0 KM nb1 True by (auto simp: InnerHyp_def)
      obtain n where n: "gammaIn K M p = of_int n" using gammaIn_isInt by blast
      have "vpGge p ([:SK K:] * DeltaK K) (of_int (vpS K p) + gammaIn K M p)"
        by (rule vpGge_mul[OF assms(2) SKi DeltaK_vpGge_inner[OF assms(2) IH]])
      thus ?thesis using nb1 True n by (simp add: Lp_def FK_def)
    next
      case nb2: False
      show ?thesis
      proof (cases "p \<le> K")
        case True
        have OH: "OuterHyp K p" using M40 K40d KM assms(2) nb2 True
          by (intro outer_hyp_of_range) auto
        have "vpGge p ([:SK K:] * DeltaK K) (of_int (vpS K p) + of_int (gammaOut K p))"
          by (rule vpGge_mul[OF assms(2) SKi DeltaK_vpGge_outer[OF assms(2) K40d OH]])
        thus ?thesis using nb1 nb2 True by (simp add: Lp_def FK_def)
      next
        case False
        have "vpGge p ([:SK K:] * DeltaK K) (of_int (vpS K p) + 0)"
          by (rule vpGge_mul[OF assms(2) SKi DeltaK_vpGge_large_prime[OF assms(2) K40d]]) (use False
            in simp)
        thus ?thesis using nb1 nb2 False by (simp add: Lp_def FK_def)
      qed
    qed
  qed
  have m: "vpGge p [:mKM K M:] (of_int (vp p (mKM K M)))" by (rule vpGge_C_vp)
  have Q: "vpGge p (QKM K M) (of_int (vp p (mKM K M)) + of_int (Lp K M p))"
    unfolding QKM_def by (rule vpGge_mul[OF assms(2) m F])
  have "0 \<le> vp p (mKM K M) + Lp K M p"
  proof (cases "p \<le> 2 * hof K")
    case True
    thus ?thesis by (simp add: vp_mKM[OF assms(2)])
  next
    case False
    hence "K < p" using K2h by linarith
    moreover have "p \<le> p * M" using M40 by simp
    ultimately have "\<not> p * M \<le> K" "\<not> 3 * p \<le> K" "\<not> p \<le> K" by linarith+
    hence "Lp K M p = vpS K p" by (simp add: Lp_def)
    also have "\<dots> = 0" using False by (intro vpS_eq_0_large[OF assms(2) K40d K0]) simp
    finally show ?thesis using False by (simp add: vp_mKM[OF assms(2)])
  qed
  thus ?thesis using Q by (intro vpGge_mono[OF Q]) simp
qed

text \<open>Proposition 5.1: @{text "Q_{K,M} \<in> \<int>[X]"}.  At each prime,
  @{text "L_p(K,M)"} is covered by (3.12),
  Proposition 4.1 or Proposition 4.3.\<close>
theorem QKM_int_poly: "StdHyp K M \<Longrightarrow>
  \<exists>P :: int poly. map_poly of_int P = QKM K M"
  by (rule intPoly_of_vge) (rule QKM_vpGge)

text \<open>(5.7), inner range: @{text "\<gamma>_p^in = p\<Gamma>(K/p) + O_M(1)"} and
  @{text "v_p(S_K) = pN(K/p) + O_M(1)"},
  uniformly over (4.1) (the Lean constant is @{text "1000M^2"}).\<close>

subsection \<open>The outer range of the uniformity estimate (Lean: Legendre5)\<close>

text \<open>For @{text "n < p^2"} only @{text "a = 1"} contributes to Legendre's sum.\<close>
lemma sum_div_pow_single:
  assumes "prime p" "1 \<le> B" "n < (p :: nat) ^ 2"
  shows "(\<Sum> a = 1..B. n div p ^ a) = n div p"
proof -
  have z: "n div p ^ a = 0" if "a \<in> {1..B}" "a \<noteq> 1" for a
  proof -
    have a2: "2 \<le> a" using that by auto
    have "p ^ 2 \<le> p ^ a" by (rule power_increasing[OF a2]) (use prime_ge_1_nat[OF assms(1)] in
      simp)
    thus ?thesis using assms(3) by (intro div_less) linarith
  qed
  show ?thesis
    using assms(2) z by (subst sum.remove[of _ 1]) auto
qed

text \<open>Under (4.9), Legendre's formula collapses to a single term per factorial:
  @{text "v_p(S_K) = 2h \<lfloor>K/p\<rfloor> -
    2 \<Sum>_{i=1}^{h-1} \<lfloor>2i/p\<rfloor>"}.\<close>
lemma vpS_outer:
  assumes p: "prime p" and K: "40 dvd K" and h: "OuterHyp K p"
  shows "vpS K p = 2 * int (hof K) * int (K div p) - 2 * int (\<Sum> i = 1..hof K - 1. 2 * i div p)"
proof -
  have facts: "7 \<le> p" "p \<le> K" "K < 3 * p" "2 * K < p ^ 2" "2 * Nof K < p"
    using h unfolding OuterHyp_def by auto
  have K0: "0 < K" using facts by linarith
  define B where "B = 2 * hof K + K + 1"
  have B1: "1 \<le> B" unfolding B_def by simp
  have sK: "(\<Sum> a = 1..B. K div p ^ a) = K div p"
    by (rule sum_div_pow_single[OF p B1]) (use facts in linarith)
  have sN: "(\<Sum> a = 1..B. Nof K div p ^ a) = Nof K div p"
  proof -
    have "Nof K \<le> K" unfolding Nof_def by linarith
    thus ?thesis using facts by (intro sum_div_pow_single[OF p B1]) linarith
  qed
  have si: "(\<Sum> a = 1..B. 2 * i div p ^ a) = 2 * i div p" if "i \<in> {1..hof K - 1}" for i
  proof -
    have "hof K \<le> K" unfolding hof_def by linarith
    moreover have "1 \<le> i" "i \<le> hof K - 1" using that by auto
    ultimately have "2 * i < p ^ 2" using facts(4) by arith
    thus ?thesis by (rule sum_div_pow_single[OF p B1])
  qed
  have N0: "Nof K div p = 0" using facts by simp
  have m4: "multiplicity p (4::nat) = 0"
  proof -
    have "\<not> p dvd 4"
    proof
      assume "p dvd 4"
      hence "p \<le> 4" by (rule dvd_imp_le) simp
      thus False using facts by linarith
    qed
    thus ?thesis by (rule not_dvd_imp_multiplicity_0)
  qed
  have leg: "vpS K p = 2 * int (hof K) * int (K div p) - 12 * int (hof K) * int (Nof K div p)
               - 2 * int (\<Sum> i = 1..hof K - 1. 2 * i div p) + (int (hof K) - 1) *
                 int (multiplicity p (4::nat))"
  proof -
    have L: "vpS K p = 2 * int (hof K) * (\<Sum> a = 1..B. int (K div p ^ a))
                   - 12 * int (hof K) * (\<Sum> a = 1..B. int (Nof K div p ^ a))
                   - 2 * (\<Sum> i = 1..hof K - 1. \<Sum> a = 1..B. int (2 * i div p ^ a))
                   + (int (hof K) - 1) * int (multiplicity p (4::nat))"
      unfolding B_def by (rule vpS_legendre[OF p K K0])
    have s1: "(\<Sum> a = 1..B. int (K div p ^ a)) = int (K div p)"
      unfolding of_nat_sum[symmetric] sK ..
    have s2: "(\<Sum> a = 1..B. int (Nof K div p ^ a)) = int (Nof K div p)"
      unfolding of_nat_sum[symmetric] sN ..
    have s3: "(\<Sum> i = 1..hof K - 1. \<Sum> a = 1..B. int (2 * i div p ^ a)) = int (\<Sum> i =
      1..hof K - 1. 2 * i div p)"
    proof -
      have "(\<Sum> i = 1..hof K - 1. \<Sum> a = 1..B. int (2 * i div p ^ a)) = (\<Sum> i =
        1..hof K - 1. int (2 * i div p))"
        by (rule sum.cong[OF refl]) (simp only: of_nat_sum[symmetric] si)
      thus ?thesis by simp
    qed
    show ?thesis unfolding L s1 s2 s3 ..
  qed
  show ?thesis unfolding leg N0 m4 by simp
qed

text \<open>@{text "\<Sum>_{i=1}^{h-1} \<lfloor>2i/p\<rfloor> =
  \<Sum>_{j=1}^{5} (h - \<lceil>jp/2\<rceil>)_+"} when @{text "2h < 6p"}: count the
  @{text "j \<ge> 1"} with @{text "jp \<le> 2i"} and swap the sums.\<close>
lemma sum_if_one_card: "finite A \<Longrightarrow> (\<Sum> x \<in> A.
  if P x then (1::nat) else 0) = card {x \<in> A. P x}"
  by (simp add: sum.inter_filter[symmetric])

lemma half_ceil_le_iff: "((m + 1) div 2 \<le> (i::nat)) = (m \<le> 2 * i)"
  by linarith

lemma suc_pred_sub: "1 \<le> x \<Longrightarrow> Suc (h - 1) - x = h - (x::nat)"
  by arith

lemma half_ceil_ge_1: "1 \<le> (m::nat) \<Longrightarrow> 1 \<le> (m + 1) div 2"
  by fastforce

lemma sum_floor_eq:
  assumes p: "prime p" and hh: "2 * h < 6 * (p :: nat)"
  shows "(\<Sum> i = 1..h - 1. 2 * i div p) = (\<Sum> j = 1..5. h - (j * p + 1) div 2)"
proof -
  have p0: "0 < p" using p by (simp add: prime_gt_0_nat)
  have cnt: "2 * i div p = (\<Sum> j = 1..5. if j * p \<le> 2 * i then 1 else 0)"
    if "i \<in> {1..h - 1}" for i
  proof -
    have le5: "2 * i div p \<le> 5"
    proof -
      have "1 \<le> i" "i \<le> h - 1" using that by auto
      hence "2 * i < 6 * p" using hh by arith
      hence "2 * i div p < 6" using p0 by (simp add: div_less_iff_less_mult mult.commute)
      thus ?thesis by simp
    qed
    have "{j \<in> {1..5}. j * p \<le> 2 * i} = {1..2 * i div p}"
    proof -
      have iff: "\<And>j. (j \<le> 2 * i div p) = (j * p \<le> 2 * i)" using p0
        by (simp add: less_eq_div_iff_mult_less_eq)
      have j5: "\<And>j. j * p \<le> 2 * i \<Longrightarrow> j \<le> 5" using iff le5
        by (meson order_trans)
      show ?thesis using iff j5 by auto
    qed
    hence "card {j \<in> {1..5}. j * p \<le> 2 * i} = 2 * i div p" by simp
    thus ?thesis
      by (simp add: sum_if_one_card)
  qed
  have "(\<Sum> i = 1..h - 1. 2 * i div p) = (\<Sum> i = 1..h - 1. \<Sum> j = 1..5.
    if j * p \<le> 2 * i then 1 else 0)"
    by (rule sum.cong[OF refl]) (simp add: cnt)
  also have "\<dots> = (\<Sum> j = 1..5. \<Sum> i = 1..h - 1. if j * p \<le> 2 * i then 1 else 0)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum> j = 1..5. h - (j * p + 1) div 2)"
  proof (intro sum.cong refl)
    fix j :: nat assume j: "j \<in> {1..5}"
    have jp: "1 \<le> j * p" using j p0 by (simp add: Suc_le_eq)
    have "{i \<in> {1..h - 1}. j * p \<le> 2 * i} = {(j * p + 1) div 2..h - 1}"
    proof -
      have lb: "\<And>i. (j * p + 1) div 2 \<le> i \<Longrightarrow> 1 \<le> i"
        using half_ceil_ge_1[OF jp] by linarith
      show ?thesis using lb by (auto simp: half_ceil_le_iff[symmetric])
    qed
    thus "(\<Sum> i = 1..h - 1. if j * p \<le> 2 * i then 1 else 0) = h - (j * p + 1) div 2"
    proof -
      assume e: "{i \<in> {1..h - 1}. j * p \<le> 2 * i} = {(j * p + 1) div 2..h - 1}"
      have "(\<Sum> i = 1..h - 1. if j * p \<le> 2 * i then 1 else 0) =
        card {(j * p + 1) div 2..h - 1}"
        unfolding e[symmetric] by (rule sum_if_one_card) simp
      also have "\<dots> = h - (j * p + 1) div 2" unfolding card_atLeastAtMost
        by (rule suc_pred_sub[OF half_ceil_ge_1[OF jp]])
      finally show ?thesis .
    qed
  qed
  finally show ?thesis .
qed

text \<open>The integer @{text "K (R_0(p/K) - d(p/K))"}, written with @{text "N = Nof K"}.\<close>
definition Eout :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "Eout K p = (let N = int (Nof K); K' = int K; p' = int p in
     if K < 2 * p
     then 7 * (K' - p') - 6 * min N (K' - p') - 6 * max (K' + N - 2 * p') 0 + max (K' + 4 * N - 2 *
       p') 0
     else 8 * K' - 9 * p' - 8 * N - 5 * min N (K' - 2 * p') - 5 * max (K' + N - 3 * p') 0
          - max (K' + 4 * N - 3 * p' - max (K' + N - 3 * p') 0) 0)"

text \<open>@{text "p < K"} under (4.9) with @{text "40 | K"}: @{text "p = K"} would make
  @{text "40 | p"}.\<close>
lemma outer_p_less:
  assumes p: "prime p" and K: "40 dvd K" and h: "OuterHyp K p"
  shows "p < K"
proof -
  have f: "7 \<le> p" "p \<le> K" using h unfolding OuterHyp_def by auto
  have "p \<noteq> K"
  proof
    assume "p = K"
    hence "2 dvd p" using K by (metis dvd_trans dvd_triv_left mult_2 numeral_Bit0)
    hence "(2::nat) = 1 \<or> 2 = p" using p unfolding prime_nat_iff by auto
    hence "2 = p" by linarith
    thus False using f by linarith
  qed
  thus ?thesis using f by simp
qed

lemma odd_prime_ge_7: "prime p \<Longrightarrow> 7 \<le> (p :: nat) \<Longrightarrow>
  \<not> 2 dvd p"
  using prime_odd_nat[of p] by linarith

text \<open>@{text "|-\<gamma>_p^out - E_out| \<le> 7"}: pure integer arithmetic with
  @{text "K mod p = K - p"} resp. @{text "K - 2p"}.\<close>
lemma int_nat_sub: "int (a - b) = max (int a - int b) 0"
  by (cases "b \<le> a") (simp_all add: of_nat_diff)

lemma int_min_nat: "int (min a b) = min (int a) (int b)"
  by (simp add: min_def)

lemma gammaOut_sub_Eout:
  assumes p: "prime p" and K: "40 dvd K" and h: "OuterHyp K p"
  shows "\<bar>- gammaOut K p - Eout K p\<bar> \<le> 7"
proof -
  have facts: "7 \<le> p" "p \<le> K" "K < 3 * p" "2 * Nof K < p" "5 * Nof K \<le> 2 * p - 2"
    using h unfolding OuterHyp_def by auto
  have pK: "p < K" by (rule outer_p_less[OF p K h])
  show ?thesis
  proof (cases "K < 2 * p")
    case True
    have "K div p = 1" and m: "K mod p = K - p"
    proof -
      show d: "K div p = 1" by (rule div_nat_eqI) (use facts True in auto)
      show "K mod p = K - p" using minus_div_mult_eq_mod[of K p] d by simp
    qed
    have n40: "40 * Nof K \<le> 3 * K" "3 * K < 40 * Nof K + 40" unfolding Nof_def by linarith+
    have i: "7 \<le> int p" "int p < int K" "int K < 2 * int p" "2 * int (Nof K) < int p"
            "40 * int (Nof K) \<le> 3 * int K" "3 * int K < 40 * int (Nof K) + 40"
      using facts pK True n40 by simp_all
    show ?thesis
      unfolding gammaOut_def rOut_def Eout_def Let_def if_P[OF True] m
      using i unfolding int_nat_sub int_min_nat of_nat_add of_nat_mult of_nat_1 of_nat_numeral
        min_def max_def abs_if
      by (auto split: if_splits)
  next
    case False
    have "K div p = 2" and m: "K mod p = K - 2 * p"
    proof -
      show d: "K div p = 2" by (rule div_nat_eqI) (use facts False in auto)
      show "K mod p = K - 2 * p" using minus_div_mult_eq_mod[of K p] d by (simp add: mult.commute)
    qed
    have n40: "40 * Nof K \<le> 3 * K" "3 * K < 40 * Nof K + 40" unfolding Nof_def by linarith+
    have i: "7 \<le> int p" "int p < int K" "2 * int p \<le> int K" "int K <
      3 * int p" "2 * int (Nof K) < int p"
            "40 * int (Nof K) \<le> 3 * int K" "3 * int K < 40 * int (Nof K) + 40"
      using facts pK False n40 by simp_all
    show ?thesis
      unfolding gammaOut_def rOut_def Eout_def Let_def if_not_P[OF False] m
      using i unfolding int_nat_sub int_min_nat of_nat_add of_nat_mult of_nat_1 of_nat_numeral
        min_def max_def abs_if
      by (auto split: if_splits)
  qed
qed

lemma hof_real: "40 dvd K \<Longrightarrow> real (hof K) = lam_r * real K"
proof -
  assume "40 dvd K"
  then obtain n where n: "K = 40 * n" by (elim dvdE)
  have "hof K = 37 * n" unfolding hof_def n by auto
  thus ?thesis unfolding n lam_r_def by simp
qed

lemma Nof_real: "40 dvd K \<Longrightarrow> real (Nof K) = alpha_r * real K"
proof -
  assume "40 dvd K"
  then obtain n where n: "K = 40 * n" by (elim dvdE)
  have "Nof K = 3 * n" unfolding Nof_def n by auto
  thus ?thesis unfolding n alpha_r_def by simp
qed

lemma hof_le: "hof K \<le> K" and Nof_le: "Nof K \<le> K" and Nof_lt_hof: "2 \<le>
  K \<Longrightarrow> Nof K < hof K"
proof -
  show "hof K \<le> K" unfolding hof_def by linarith
  show "Nof K \<le> K" unfolding Nof_def by linarith
  show "2 \<le> K \<Longrightarrow> Nof K < hof K" unfolding Nof_def hof_def by linarith
qed

text \<open>The real identity behind @{text "E_out"}.\<close>
lemma mult_min_nonneg:
  assumes "0 \<le> (c::real)" shows "c * min a b = min (c * a) (c * b)"
proof (cases "a \<le> b")
  case True
  hence "c * a \<le> c * b" using assms by (rule mult_left_mono)
  thus ?thesis using True by (simp add: min.absorb1)
next
  case False
  hence ba: "b \<le> a" by simp
  hence "c * b \<le> c * a" using assms by (rule mult_left_mono)
  thus ?thesis using ba by (simp add: min.absorb2)
qed

lemma mult_pos_r_nonneg:
  assumes "0 \<le> (c::real)" shows "c * pos_r a = max (c * a) 0"
proof (cases "a \<le> 0")
  case True
  hence "c * a \<le> 0" using assms by (simp add: mult_nonneg_nonpos)
  thus ?thesis using True unfolding pos_r_def by (simp add: max.absorb2)
next
  case False
  hence "0 \<le> c * a" using assms by simp
  thus ?thesis using False unfolding pos_r_def by (simp add: max.absorb1)
qed

lemma K_mul_R0_sub_dfun:
  assumes p: "prime p" and K: "40 dvd K" and h: "OuterHyp K p"
  shows "real K * (R0_r (real p / real K) - dfun_r (real p / real K)) = of_int (Eout K p)"
proof -
  have facts: "7 \<le> p" "p \<le> K" "K < 3 * p" using h unfolding OuterHyp_def by auto
  have pK: "p < K" by (rule outer_p_less[OF p K h])
  have K0: "0 < real K" using facts by simp
  define y where "y = real p / real K"
  have Ky: "real K * y = real p" unfolding y_def using K0 by simp
  have N: "real (Nof K) = alpha_r * real K" by (rule Nof_real[OF K])
  have Kmin: "real K * min a b = min (real K * a) (real K * b)" for a b
    by (rule mult_min_nonneg) simp
  have Kpos: "real K * pos_r a = max (real K * a) 0" for a
    by (rule mult_pos_r_nonneg) simp
  have pKr: "real p < real K" and K3: "real K < 3 * real p" using pK facts by simp_all
  show ?thesis
  proof (cases "K < 2 * p")
    case True
    hence y1: "1 / 2 < y" "y < 1" and ny: "\<not> (1 / 3 < y \<and> y < 1 / 2)"
    proof -
      have "real K < real (2 * p)" using True by (simp only: of_nat_less_iff)
      hence K2: "real K < 2 * real p" by simp
      show a: "1 / 2 < y" unfolding y_def using K0 K2 by (simp add: field_simps)
      show "y < 1" unfolding y_def using K0 pKr by (simp add: field_simps)
      show "\<not> (1 / 3 < y \<and> y < 1 / 2)" using a by (simp add: not_less less_imp_le)
    qed
    have "real K * (R0_r y - dfun_r y) =
            real K * (7 * (1 - y) - 6 * min alpha_r (1 - y) - 6 * pos_r (1 + alpha_r - 2 * y) +
              pos_r (1 + 4 * alpha_r - 2 * y))"
      unfolding R0_r_def dfun_r_def using y1 ny by simp
    also have "\<dots> = of_int (Eout K p)"
    proof -
      have ga: "real K * alpha_r = real (Nof K)" using N by simp
      have g1: "real K * (1 - y) = real K - real p" unfolding y_def using K0
        by (simp add: field_simps)
      have g2: "real K * (1 + alpha_r - 2 * y) = real K + real (Nof K) - 2 * real p"
        unfolding y_def using K0 N by (simp add: field_simps)
      have g3: "real K * (1 + 4 * alpha_r - 2 * y) = real K + 4 * real (Nof K) - 2 * real p"
        unfolding y_def using K0 N by (simp add: field_simps)
      have "real K * (7 * (1 - y) - 6 * min alpha_r (1 - y) - 6 * pos_r (1 + alpha_r - 2 * y) +
        pos_r (1 + 4 * alpha_r - 2 * y)) =
            7 * (real K * (1 - y)) - 6 * (real K * min alpha_r (1 - y)) - 6 * (real K * pos_r (1 +
              alpha_r - 2 * y))
            + real K * pos_r (1 + 4 * alpha_r - 2 * y)" by (simp add: algebra_simps)
      also have "\<dots> = 7 * (real K - real p) - 6 * min (real (Nof K)) (real K - real p)
            - 6 * max (real K + real (Nof K) - 2 * real p) 0 + max (real K + 4 * real (Nof K) - 2 *
              real p) 0"
        unfolding Kmin Kpos g1 g2 g3 ga ..
      also have "\<dots> = of_int (Eout K p)" unfolding Eout_def Let_def if_P[OF True]
        by (simp add: of_int_min of_int_max)
      finally show ?thesis .
    qed
    finally show ?thesis unfolding y_def .
  next
    case False
    hence y1: "1 / 3 < y" "y < 1 / 2"
    proof -
      have odd: "\<not> 2 dvd p" by (rule odd_prime_ge_7[OF p facts(1)])
      have ne: "K \<noteq> 2 * p" using K odd by force
      have "2 * p < K" using False ne by linarith
      hence "real (2 * p) < real K" by (simp only: of_nat_less_iff)
      hence K2: "2 * real p < real K" by simp
      show "1 / 3 < y" unfolding y_def using K0 K3 by (simp add: field_simps)
      show "y < 1 / 2" unfolding y_def using K0 K2 by (simp add: field_simps)
    qed
    have "real K * (R0_r y - dfun_r y) =
            real K * ((8 - 9 * y - 8 * alpha_r - 5 * min alpha_r (1 - 2 * y) - 5 * pos_r (1 +
              alpha_r - 3 * y))
                       - pos_r ((1 + 4 * alpha_r - 3 * y) - pos_r (1 + alpha_r - 3 * y)))"
      unfolding R0_r_def dfun_r_def using y1 by simp
    also have "\<dots> = of_int (Eout K p)"
    proof -
      have ga: "real K * alpha_r = real (Nof K)" using N by simp
      have Ky': "real K * y = real p" by (rule Ky)
      have h1: "real K * (1 - 2 * y) = real K - 2 * real p" unfolding y_def using K0
        by (simp add: field_simps)
      have h2: "real K * (1 + alpha_r - 3 * y) = real K + real (Nof K) - 3 * real p"
        unfolding y_def using K0 N by (simp add: field_simps)
      have h3: "real K * (1 + 4 * alpha_r - 3 * y) = real K + 4 * real (Nof K) - 3 * real p"
        unfolding y_def using K0 N by (simp add: field_simps)
      have h3': "real K * ((1 + 4 * alpha_r - 3 * y) - pos_r (1 + alpha_r - 3 * y)) =
                 real K + 4 * real (Nof K) - 3 * real p - max (real K + real (Nof K) - 3 *
                   real p) 0"
        by (simp only: right_diff_distrib[of "real K" "1 + 4 * alpha_r - 3 * y"] Kpos h2 h3)
      have "real K * ((8 - 9 * y - 8 * alpha_r - 5 * min alpha_r (1 - 2 * y) - 5 * pos_r (1 +
        alpha_r - 3 * y))
                       - pos_r ((1 + 4 * alpha_r - 3 * y) - pos_r (1 + alpha_r - 3 * y))) =
            8 * real K - 9 * (real K * y) - 8 * (real K * alpha_r) - 5 * (real K * min alpha_r (1 -
              2 * y))
            - 5 * (real K * pos_r (1 + alpha_r - 3 * y)) - real K * pos_r ((1 + 4 * alpha_r - 3 *
              y) - pos_r (1 + alpha_r - 3 * y))"
        by (simp add: algebra_simps)
      also have "\<dots> = 8 * real K - 9 * real p - 8 * real (Nof K) - 5 *
        min (real (Nof K)) (real K - 2 * real p)
            - 5 * max (real K + real (Nof K) - 3 * real p) 0
            - max (real K + 4 * real (Nof K) - 3 * real p - max (real K + real (Nof K) - 3 *
              real p) 0) 0"
        unfolding Kmin Kpos h1 h2 h3' ga Ky' ..
      also have "\<dots> = of_int (Eout K p)" unfolding Eout_def Let_def if_not_P[OF False]
        by (simp add: of_int_min of_int_max)
      finally show ?thesis .
    qed
    finally show ?thesis unfolding y_def .
  qed
qed

text \<open>@{text "-v_p(S_K)"} against its limit (5.7,
  outer): an explicit sum of five bounded terms.\<close>
lemma vpS_sub_limit:
  assumes p: "prime p" and K: "40 dvd K" and h: "OuterHyp K p"
  shows "- of_int (vpS K p) - real K * (- 2 * lam_r * of_int (floor (real K / real p)) +
           (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * (real p / real K))))
         = of_int (\<Sum> j = 1..5. 2 * int (hof K - (j * p + 1) div 2) - max (2 * int (hof K) -
           int j * int p) 0)"
proof -
  have facts: "7 \<le> p" "p \<le> K" "K < 3 * p" using h unfolding OuterHyp_def by auto
  have K0: "0 < real K" using facts by simp
  have hh: "real (hof K) = lam_r * real K" by (rule hof_real[OF K])
  have fl: "floor (real K / real p) = int (K div p)"
    by (rule floor_divide_of_nat_eq)
  have trm: "real K * pos_r (2 * lam_r - real j * (real p / real K)) =
    of_int (max (2 * int (hof K) - int j * int p) 0)" for j
  proof -
    have t: "real K * (2 * lam_r - real j * (real p / real K)) = 2 * real (hof K) - real j * real p"
      using K0 hh by (simp add: field_simps)
    show ?thesis unfolding mult_pos_r_nonneg[OF of_nat_0_le_iff] t by (simp add: of_int_max)
  qed
  have hh6: "2 * hof K < 6 * p" using hof_le[of K] facts by linarith
  have "- of_int (vpS K p) = - (2 * real (hof K) * real (K div p)) + 2 * (\<Sum> j =
    1..5. real (hof K - (j * p + 1) div 2))"
    unfolding vpS_outer[OF p K h] sum_floor_eq[OF p hh6] by simp
  moreover have "of_int (\<Sum> j = 1..5. 2 * int (hof K - (j * p + 1) div 2) - max (2 *
    int (hof K) - int j * int p) 0)
      = 2 * (\<Sum> j = 1..5. real (hof K - (j * p + 1) div 2)) - (\<Sum> j =
        1..5. (of_int (max (2 * int (hof K) - int j * int p) 0) :: real))"
    by (simp add: of_int_sum sum_subtractf sum_distrib_left)
  moreover have "real K * (- 2 * lam_r * of_int (int (K div p))) =
    - (2 * real (hof K) * real (K div p))"
    by (simp add: hh algebra_simps)
  ultimately show ?thesis
    unfolding fl distrib_left sum_distrib_left trm by linarith
qed

lemma half_ceil_abs:
  fixes h m :: nat
  shows "\<bar>2 * int (h - (m + 1) div 2) - max (2 * int h - int m) 0\<bar> \<le> 1"
  unfolding abs_if max_def by presburger

lemma two_sub_half_le:
  fixes h m :: nat
  shows "2 * real (h - (m + 1) div 2) \<le> max (2 * real h - real m) 0"
proof -
  have "2 * int (h - (m + 1) div 2) \<le> max (2 * int h - int m) 0" unfolding max_def by presburger
  hence "real_of_int (2 * int (h - (m + 1) div 2)) \<le> real_of_int (max (2 * int h - int m) 0)"
    by (simp only: of_int_le_iff)
  thus ?thesis by (simp add: of_int_max)
qed

lemma vpS_sub_limit_abs:
  assumes p: "prime p" and K: "40 dvd K" and h: "OuterHyp K p"
  shows "\<bar>- of_int (vpS K p) - real K * (- 2 * lam_r * of_int (floor (real K / real p)) +
           (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * (real p / real K))))\<bar> \<le> 5"
proof -
  have one: "\<bar>2 * int (hof K - (j * p + 1) div 2) - max (2 * int (hof K) - int j *
    int p) 0\<bar> \<le> 1" for j
    using half_ceil_abs[of "hof K" "j * p"] by simp
  have s: "\<bar>\<Sum> j = 1..5. 2 * int (hof K - (j * p + 1) div 2) - max (2 * int (hof K) -
    int j * int p) 0\<bar> \<le> 5"
  proof -
    have "\<bar>\<Sum> j = 1..5. 2 * int (hof K - (j * p + 1) div 2) - max (2 * int (hof K) -
      int j * int p) 0\<bar>
          \<le> (\<Sum> j = 1..5. \<bar>2 * int (hof K - (j * p + 1) div 2) - max (2 * int (hof K) -
            int j * int p) 0\<bar>)"
      by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum> j \<in> {1..5::nat}. (1::int))" by (rule sum_mono) (rule one)
    also have "\<dots> = (5::int)" by simp
    finally show ?thesis .
  qed
  show ?thesis unfolding vpS_sub_limit[OF p K h] of_int_abs[symmetric] of_int_le_numeral_iff
    by (rule s)
qed

text \<open>The outer analogue of (5.7) (constant 7).\<close>
theorem uniformity_outer:
  "\<exists>Cst. \<forall>K p. prime p \<longrightarrow> 40 dvd K \<longrightarrow>
    OuterHyp K p \<longrightarrow>
     \<bar>- of_int (gammaOut K p) - real K * (R0_r (real p / real K) - dfun_r (real p /
       real K))\<bar> \<le> Cst \<and>
     \<bar>- of_int (vpS K p) - real K * (- 2 * lam_r * of_int (floor (real K / real p)) +
          (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * (real p / real K))))\<bar> \<le> Cst"
proof (intro exI[of _ 7] allI impI conjI)
  fix K p assume p: "prime p" and K: "40 dvd K" and h: "OuterHyp K p"
  have "\<bar>- of_int (gammaOut K p) - of_int (Eout K p)\<bar> \<le> (7 :: real)"
    using gammaOut_sub_Eout[OF p K h]
    by (simp flip: of_int_minus of_int_diff of_int_abs)
  thus "\<bar>- of_int (gammaOut K p) - real K * (R0_r (real p / real K) - dfun_r (real p /
    real K))\<bar> \<le> 7"
    unfolding K_mul_R0_sub_dfun[OF p K h] .
  show "\<bar>- of_int (vpS K p) - real K * (- 2 * lam_r * of_int (floor (real K / real p)) +
          (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * (real p / real K))))\<bar> \<le> 7"
    using vpS_sub_limit_abs[OF p K h] by linarith
qed

subsection \<open>Exact integrals and tails\<close>

text \<open>@{text "\<integral>_{1/3}^{1/2} d(y) dy = 9/640"}.\<close>
theorem integral_dfun: "interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (1 / 2)) dfun_r =
  9 / 640"
  by (rule integral_dfun_eq)

text \<open>(5.12)-(5.14): @{text "R(x) = x F(x) + Q(x)"} with @{text "-1/2 \<le> Q(x) \<le> 13/8"}
  (for all @{text "x > 0"}).\<close>
theorem R_decomp_bound:
  assumes "3 \<le> x"
  shows "- 1 / 2 \<le> R_r x - x * (4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r *
    x)) \<and>
         R_r x - x * (4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x)) \<le>
           13 / 8"
  by (rule R_decomp_bound_all)

text \<open>The mean of @{text P} over a period is @{text "2923/240"}.\<close>
theorem Pper_mean: "interval_lebesgue_integral lborel (ereal 0) (ereal 40) Pper / 40 = 2923 / 240"
  by (rule Pper_mean_eq)


text \<open>@{text "R(x)/x^3"} is integrable on @{text "[3, \<infinity>)"}.\<close>
theorem R_integrableOn: "set_integrable lborel {3..} (\<lambda>x. R_r x / x ^ 3)"
  by (rule R_div_cube_integrable)

subsection \<open>Prime sums via the prime number theorem\<close>

text \<open>The prime number theorem in Chebyshev's form, from the AFP
  (@{text "Prime_Number_Theorem.\<theta>_asymptotics"}: @{text "\<theta> \<sim> x"}).\<close>
lemma theta_div_tendsto: "((\<lambda>x. primes_theta x / x) \<longlongrightarrow> 1) at_top"
  by (rule pnt_theta)

text \<open>Chebyshev's bound @{text "\<theta>(n) \<le> n log 4"} (from
  Prime\_Distribution\_Elementary).\<close>
lemma sum_log_primes_le: "(\<Sum> p \<in> {p. p \<le> n \<and>
  prime p}. ln (real p)) \<le> ln 4 * real n"
proof -
  have eq: "(\<Sum> p \<in> {p. p \<le> n \<and> prime p}. ln (real p)) = primes_theta (real n)"
    unfolding primes_theta_def prime_sum_upto_def by (rule sum.cong) auto
  show ?thesis
  proof (cases "n = 0")
    case True
    thus ?thesis unfolding eq by (simp add: prime_sum_upto_eq_0 primes_theta_def)
  next
    case False
    hence "primes_theta (real n) < ln 4 * real n" by (intro \<theta>_upper_bound) simp
    thus ?thesis unfolding eq by simp
  qed
qed

text \<open>Outer range, variable @{text "y = p/K"}: Riemann-sum upper bound
  for a bounded, almost-everywhere
  continuous @{text \<phi>} (step majorants + the PNT cell estimates).\<close>
theorem outer_prime_sum_limsup:
  assumes "0 < a" "a \<le> b" "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> Bd" "countable D"
    and "\<And>y. y \<in> {a<..<b} \<Longrightarrow> y \<notin> D \<Longrightarrow>
      isCont \<phi> y" "0 < \<epsilon>"
  shows "\<forall>\<^sub>F K in at_top.
    (\<Sum> p \<in> {p. p \<le> nat (floor (b * real K)) \<and> prime p \<and>
      a * real K < real p \<and> real p \<le> b * real K}.
        \<phi> (real p / real K) * ln (real p))
      \<le> (interval_lebesgue_integral lborel (ereal a) (ereal b) \<phi> + \<epsilon>) * real K"
  using assms by (rule outer_prime_sum_bound)

text \<open>Inner range, variable @{text "x = K/p"}.\<close>
theorem inner_prime_sum_limsup:
  assumes "3 < M" "\<And>x. x \<in> {3..real M} \<Longrightarrow>
    \<bar>f x\<bar> \<le> Bd" "countable D"
    and "\<And>x. x \<in> {3<..<real M} \<Longrightarrow> x \<notin> D \<Longrightarrow>
      isCont f x" "0 < \<epsilon>"
  shows "\<forall>\<^sub>F K in at_top.
    (\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and>
      3 * p \<le> K}. real p * f (real K / real p) * ln (real p))
      \<le> (interval_lebesgue_integral lborel (ereal 3) (ereal (real M)) (\<lambda>x. f x /
        x ^ 3) + \<epsilon>) * real K ^ 2"
  using assms by (rule inner_prime_sum_bound)

subsection \<open>Continuity of the limiting functions off a countable set\<close>

theorem R_continuousAt_off: "\<exists>D. countable D \<and> (\<forall>x. 0 < x \<longrightarrow>
  x \<notin> D \<longrightarrow> isCont R_r x)"
  by (rule R_isCont_off_countable)
theorem outerIntegrand_continuousAt_off: "\<exists>D. countable D \<and>
  (\<forall>y. 0 < y \<longrightarrow> y \<notin> D \<longrightarrow> isCont outer_integrand y)"
  by (rule outer_integrand_isCont_off_countable)
theorem outerIntegrand_bounded: "\<exists>Bd. \<forall>y \<in>
  {1 / 3..2 * lam_r}. \<bar>outer_integrand y\<bar> \<le> Bd"
  by (rule outer_integrand_bounded)

subsection \<open>Proposition 5.2 and (5.21)\<close>

lemma of_rat_power_int: "of_rat (x powi k) = (of_rat x :: 'a :: real_field) powi k"
  unfolding power_int_def by (auto simp: of_rat_power of_rat_inverse)

lemma ln_power_int: "0 < x \<Longrightarrow> ln (x powi k) = of_int k * ln (x :: real)"
  unfolding power_int_def by (fastforce simp: ln_realpow ln_inverse)

lemma log_mKM:
  "ln (of_rat (mKM K M)) = (\<Sum> p \<in> {p. p \<le> 2 * hof K \<and>
    prime p}. - of_int (Lp K M p) * ln (real p))"
proof -
  have fin: "finite {p. p \<le> 2 * hof K \<and> prime p}" by simp
  have "ln (of_rat (mKM K M)) = ln (\<Prod> p \<in> {p. p \<le> 2 * hof K \<and>
    prime p}. (real p) powi (- Lp K M p))"
    unfolding mKM_def by (simp add: of_rat_prod of_rat_power_int)
  also have "\<dots> = (\<Sum> p \<in> {p. p \<le> 2 * hof K \<and>
    prime p}. ln ((real p) powi (- Lp K M p)))"
    by (intro ln_prod fin) (auto simp: power_int_def prime_gt_0_nat)
  also have "\<dots> = (\<Sum> p \<in> {p. p \<le> 2 * hof K \<and>
    prime p}. - of_int (Lp K M p) * ln (real p))"
    by (intro sum.cong refl) (simp add: ln_power_int prime_gt_0_nat)
  finally show ?thesis .
qed

text \<open>@{text "|R(x)| \<le> 18M + 2"} on @{text "[3, M]"}, from (5.12)-(5.14).\<close>
theorem R_bounded: "\<exists>Bd. \<forall>x \<in> {3..real M}. \<bar>R_r x\<bar> \<le> Bd"
proof (intro exI[of _ "18 * real M + 2"] ballI)
  fix x assume x: "x \<in> {3..real M}"
  have Q: "- 1 / 2 \<le> R_r x - x * (4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r *
    x))"
          "R_r x - x * (4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x)) \<le>
            13 / 8"
    using R_decomp_bound[of x] x by auto
  have f: "0 \<le> frac x" "frac x < 1" "0 \<le> frac (alpha_r * x)" "frac (alpha_r * x) < 1"
    by (auto simp: frac_lt_1)
  have F: "\<bar>x * (4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x))\<bar> \<le>
    8 * x"
  proof -
    have b: "\<bar>4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x)\<bar> \<le> 8"
      unfolding abs_le_iff lam_r_def using f by (intro conjI; linarith)
    have x0: "0 \<le> x" using x by auto
    have "x * \<bar>4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x)\<bar> \<le>
      x * 8"
      by (rule mult_left_mono[OF b x0])
    thus ?thesis using x0 by (simp add: abs_mult mult.commute)
  qed
  have F1: "x * (4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x)) \<le> 8 * x"
           "- (x * (4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x))) \<le> 8 * x"
    using F unfolding abs_le_iff by auto
  have xm: "x \<le> real M" using x by auto
  show "\<bar>R_r x\<bar> \<le> 18 * real M + 2" unfolding abs_le_iff using Q F1 xm
    by (intro conjI; linarith)
qed

text \<open>For @{text "K < p \<le> 2h"}: @{text "-v_p(S_K) \<le> K \<cdot> outerIntegrand(p/K)"}
  (Legendre again, now @{text "K < p"}).\<close>
lemma vpS_large:
  assumes p: "prime p" and K: "40 dvd K" "40 \<le> K" and Kp: "K < p" and p2h: "p \<le> 2 * hof K"
  shows "- of_int (vpS K p) \<le> real K * outer_integrand (real p / real K)"
proof -
  have K0: "0 < K" using K by linarith
  define B where "B = 2 * hof K + K + 1"
  have B1: "1 \<le> B" unfolding B_def by simp
  have m4: "multiplicity p (4::nat) = 0"
  proof -
    have "\<not> p dvd 4"
    proof
      assume "p dvd 4"
      hence "p \<le> 4" by (rule dvd_imp_le) simp
      thus False using K Kp by linarith
    qed
    thus ?thesis by (rule not_dvd_imp_multiplicity_0)
  qed
  have leg: "vpS K p = - 2 * int (\<Sum> i = 1..hof K - 1. 2 * i div p)"
  proof -
    have pp: "2 * p \<le> p ^ 2" using mult_le_mono1[OF prime_ge_2_nat[OF p], of p]
      by (simp add: power2_eq_square)
    have hK: "hof K \<le> K" and NK: "Nof K \<le> K" by (rule hof_le, rule Nof_le)
    have L: "vpS K p = 2 * int (hof K) * (\<Sum> a = 1..B. int (K div p ^ a))
                   - 12 * int (hof K) * (\<Sum> a = 1..B. int (Nof K div p ^ a))
                   - 2 * (\<Sum> i = 1..hof K - 1. \<Sum> a = 1..B. int (2 * i div p ^ a))
                   + (int (hof K) - 1) * int (multiplicity p (4::nat))"
      unfolding B_def by (rule vpS_legendre[OF p K(1) K0])
    have Kp2: "K < p ^ 2" using pp Kp by linarith
    have Np2: "Nof K < p ^ 2" using pp Kp NK by linarith
    have sK: "(\<Sum> a = 1..B. K div p ^ a) = 0"
      using sum_div_pow_single[OF p B1 Kp2] Kp by simp
    have sN: "(\<Sum> a = 1..B. Nof K div p ^ a) = 0"
      using sum_div_pow_single[OF p B1 Np2] Kp NK by simp
    have si: "(\<Sum> a = 1..B. 2 * i div p ^ a) = 2 * i div p" if "i \<in> {1..hof K - 1}" for i
    proof -
      have i: "1 \<le> i" "i \<le> hof K - 1" using that by auto
      have "2 * i < p ^ 2" using pp Kp hK i by arith
      thus ?thesis by (rule sum_div_pow_single[OF p B1])
    qed
    have s1: "(\<Sum> a = 1..B. int (K div p ^ a)) = 0" unfolding of_nat_sum[symmetric] sK by simp
    have s2: "(\<Sum> a = 1..B. int (Nof K div p ^ a)) = 0" unfolding of_nat_sum[symmetric] sN
      by simp
    have s3: "(\<Sum> i = 1..hof K - 1. \<Sum> a = 1..B. int (2 * i div p ^ a)) = int (\<Sum> i =
      1..hof K - 1. 2 * i div p)"
    proof -
      have "(\<Sum> i = 1..hof K - 1. \<Sum> a = 1..B. int (2 * i div p ^ a)) = (\<Sum> i =
        1..hof K - 1. int (2 * i div p))"
        by (rule sum.cong[OF refl]) (simp only: of_nat_sum[symmetric] si)
      thus ?thesis by simp
    qed
    show ?thesis unfolding L s1 s2 s3 m4 by simp
  qed
  have hh6: "2 * hof K < 6 * p" using hof_le[of K] Kp by linarith
  have hv: "- of_int (vpS K p) = (\<Sum> j = 1..5. 2 * real (hof K - (j * p + 1) div 2))"
    unfolding leg sum_floor_eq[OF p hh6] by (simp add: sum_distrib_left sum_negf)
  have Kr: "0 < real K" using K0 by simp
  define y where "y = real p / real K"
  have y1: "1 < y" unfolding y_def using Kp Kr by (simp add: less_divide_eq)
  have R0: "R0_r y = 0" and d: "dfun_r y = 0" and fl: "floor (1 / y) = 0"
  proof -
    have n: "\<not> y < 1 / 2" "\<not> y < 1" using y1 by linarith+
    show "R0_r y = 0" unfolding R0_r_def using n by simp
    show "dfun_r y = 0" unfolding dfun_r_def using n by simp
    have "0 \<le> 1 / y" "1 / y < 1" using y1 by (simp_all add: field_simps)
    thus "floor (1 / y) = 0" by (simp add: floor_eq_iff)
  qed
  have oi: "real K * outer_integrand y = (\<Sum> j = 1..5. real K * pos_r (2 * lam_r - real j * y))"
    unfolding outer_integrand_def R0 d fl by (simp add: sum_distrib_left)
  have hh: "real (hof K) = lam_r * real K" by (rule hof_real[OF K(1)])
  have trm: "2 * real (hof K - (j * p + 1) div 2) \<le> real K * pos_r (2 * lam_r - real j * y)"
    for j
  proof -
    have e: "real K * pos_r (2 * lam_r - real j * y) = max (2 * real (hof K) - real j * real p) 0"
    proof -
      have t: "real K * (2 * lam_r - real j * y) = 2 * real (hof K) - real j * real p"
        unfolding y_def using Kr hh by (simp add: field_simps)
      show ?thesis unfolding mult_pos_r_nonneg[OF of_nat_0_le_iff] t ..
    qed
    show ?thesis unfolding e
      using two_sub_half_le[of "hof K" "j * p"] by simp
  qed
  show ?thesis unfolding hv y_def[symmetric] oi by (rule sum_mono) (rule trm)
qed

text \<open>The main term of @{text "-L_p(K, M)"}.\<close>
definition mainCoef :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "mainCoef K M p =
     (if p * M \<le> K then real (6 * hof K * nat_log p (5 * K) + hof K * multiplicity p (24::nat))
      else if 3 * p \<le> K then real p * R_r (real K / real p)
      else real K * outer_integrand (real p / real K))"

text \<open>Termwise: @{text "-L_p \<le> mainCoef + (2 C_1 + 1 + 2 C_2)"}
  for every prime @{text "p \<le> 2h"}.\<close>
lemma neg_Lp_le:
  assumes M: "40 \<le> M" and C1: "0 \<le> C1" and C2: "0 \<le> C2"
    and hin: "\<And>K p. prime p \<Longrightarrow> InnerHyp K M p \<Longrightarrow>
       \<bar>of_rat (gammaIn K M p) - real p * Gam_r (real K / real p)\<bar> \<le> C1 \<and>
       \<bar>of_int (vpS K p) - real p * Nfun_r (real K / real p)\<bar> \<le> C1"
    and hout: "\<And>K p. prime p \<Longrightarrow> 40 dvd K \<Longrightarrow>
      OuterHyp K p \<Longrightarrow>
       \<bar>- of_int (gammaOut K p) - real K * (R0_r (real p / real K) - dfun_r (real p /
         real K))\<bar> \<le> C2 \<and>
       \<bar>- of_int (vpS K p) - real K * (- 2 * lam_r * of_int (floor (real K / real p)) +
            (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * (real p / real K))))\<bar> \<le> C2"
    and K: "40 dvd K" "200 * M ^ 2 \<le> K" "0 < K" and p: "prime p" "p \<le> 2 * hof K"
  shows "- of_int (Lp K M p) \<le> mainCoef K M p + (2 * C1 + 1 + 2 * C2)"
proof -
  have K40: "40 \<le> K"
  proof -
    have "M \<le> M ^ 2" using M by (intro self_le_power) auto
    thus ?thesis using M K(2) by linarith
  qed
  show ?thesis
  proof (cases "p * M \<le> K")
    case True
    have "- of_int (Lp K M p) = mainCoef K M p" unfolding Lp_def mainCoef_def if_P[OF True] by simp
    thus ?thesis using C1 C2 by linarith
  next
    case small: False
    show ?thesis
    proof (cases "3 * p \<le> K")
      case True
      have IH: "InnerHyp K M p" unfolding InnerHyp_def using M K small True by auto
      have h1: "\<bar>of_rat (gammaIn K M p) - real p * Gam_r (real K / real p)\<bar> \<le> C1"
        and h2: "\<bar>of_int (vpS K p) - real p * Nfun_r (real K / real p)\<bar> \<le> C1"
        using hin[OF p(1) IH] by auto
      have fl: "of_rat (gammaIn K M p) - 1 \<le> (of_int (floor (gammaIn K M p)) :: real)"
      proof -
        have "gammaIn K M p < of_int \<lfloor>gammaIn K M p\<rfloor> + 1"
          using floor_correct[of "gammaIn K M p"] by simp
        hence "gammaIn K M p - 1 \<le> of_int \<lfloor>gammaIn K M p\<rfloor>" by linarith
        hence "of_rat (gammaIn K M p - 1) \<le>
          (of_rat (of_int \<lfloor>gammaIn K M p\<rfloor>) :: real)"
          by (simp only: of_rat_less_eq)
        thus ?thesis by (simp add: of_rat_diff)
      qed
      have e: "mainCoef K M p = - (real p * Gam_r (real K / real p)) - real p * Nfun_r (real K /
        real p)"
        unfolding mainCoef_def R_r_def using small True by (simp add: algebra_simps)
      have l: "- of_int (Lp K M p) = - of_int (vpS K p) - (of_int (floor (gammaIn K M p)) :: real)"
        unfolding Lp_def using small True by simp
      show ?thesis
        using e l h1[unfolded abs_le_iff] h2[unfolded abs_le_iff] fl C2 by linarith
    next
      case inner: False
      show ?thesis
      proof (cases "p \<le> K")
        case True
        have OH: "OuterHyp K p"
          unfolding OuterHyp_def
        proof -
          have Kp3: "K < 3 * p" using inner by simp
          have p7: "7 \<le> p" using Kp3 K40 by linarith
          have "K * K < (3 * p) * (3 * p)" using Kp3 by (intro mult_strict_mono) auto
          moreover have "18 * K \<le> K * K" using K40 by (intro mult_le_mono1) linarith
          moreover have "(3 * p) * (3 * p) = 9 * p ^ 2" by (simp add: power2_eq_square)
          ultimately have sq: "2 * K < p ^ 2" by linarith
          have n1: "2 * (3 * K div 40) < p" using Kp3 by linarith
          have n2: "5 * (3 * K div 40) \<le> 2 * p - 2" using Kp3 p7 by linarith
          show "7 \<le> p \<and> p \<le> K \<and> K < 3 * p \<and> 2 * K < p ^ 2 \<and>
            2 * Nof K < p \<and> 5 * Nof K \<le> 2 * p - 2"
            unfolding Nof_def using p7 True Kp3 sq n1 n2 by blast
        qed
        have h1: "\<bar>- of_int (gammaOut K p) - real K * (R0_r (real p / real K) -
          dfun_r (real p / real K))\<bar> \<le> C2"
          and h2: "\<bar>- of_int (vpS K p) - real K * (- 2 * lam_r * of_int (floor (real K /
            real p)) +
                     (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * (real p / real K))))\<bar> \<le>
                       C2"
          using hout[OF p(1) K(1) OH] by auto
        have fl: "floor (1 / (real p / real K)) = floor (real K / real p)"
          by simp
        have e: "mainCoef K M p = real K * (R0_r (real p / real K) - dfun_r (real p / real K))
                  + real K * (- 2 * lam_r * of_int (floor (real K / real p)) + (\<Sum> j =
                    1..5. pos_r (2 * lam_r - real j * (real p / real K))))"
          unfolding mainCoef_def outer_integrand_def fl using small inner
            by (simp add: algebra_simps)
        have l: "- of_int (Lp K M p) = - of_int (vpS K p) - (of_int (gammaOut K p) :: real)"
          unfolding Lp_def using small inner True by simp
        show ?thesis
          using e l h1[unfolded abs_le_iff] h2[unfolded abs_le_iff] C1 by linarith
      next
        case False
        have "- of_int (vpS K p) \<le> real K * outer_integrand (real p / real K)"
          by (rule vpS_large[OF p(1) K(1) K40 _ p(2)]) (use False in simp)
        moreover have "- (of_int (Lp K M p) :: real) = - of_int (vpS K p)" unfolding Lp_def
          using small inner False by simp
        moreover have "mainCoef K M p = real K * outer_integrand (real p / real K)"
          unfolding mainCoef_def using small inner by simp
        ultimately show ?thesis using C1 C2 by linarith
      qed
    qed
  qed
qed

lemma sum_log_P_le:
  "(\<Sum> p \<in> {p. p \<le> 2 * hof K \<and> prime p}. ln (real p)) \<le> 2 * real K * ln 4"
proof -
  have "(\<Sum> p \<in> {p. p \<le> 2 * hof K \<and>
    prime p}. ln (real p)) \<le> ln 4 * real (2 * hof K)"
    by (rule sum_log_primes_le)
  also have "\<dots> \<le> ln 4 * (2 * real K)"
    using hof_le[of K] by (intro mult_left_mono ln_ge_zero) simp_all
  finally show ?thesis by (simp add: mult.commute)
qed

text \<open>The primes @{text "p \<le> 2h"} split into the three ranges of (5.1) (@{text "40 | K"},
  @{text "K > 0"}, @{text "M \<ge> 3"}),
  and @{text mainCoef} takes the corresponding branch on each.\<close>
lemma three_le_mul: "3 \<le> M \<Longrightarrow> 3 * q \<le> q * (M::nat)"
  by (metis mult.commute mult_le_mono1)

lemma not_mul_le_of_lt: "3 \<le> M \<Longrightarrow> K < 3 * q \<Longrightarrow>
  \<not> q * M \<le> (K::nat)"
  using three_le_mul[of M q] by linarith

lemma le_of_three_mul: "3 * q \<le> K \<Longrightarrow> q \<le> (K::nat)"
  by linarith

lemma primes_split:
  assumes K: "40 dvd K" "0 < K" and M: "3 \<le> M"
  shows "{p. p \<le> 2 * hof K \<and> prime p} =
           {p. p \<le> K \<and> prime p \<and> p * M \<le> K} \<union> {p. p \<le> K \<and>
             prime p \<and> K < p * M \<and> 3 * p \<le> K}
           \<union> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
             1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K}"
    and "{p. p \<le> K \<and> prime p \<and> p * M \<le> K} \<inter> {p. p \<le> K \<and>
      prime p \<and> K < p * M \<and> 3 * p \<le> K} = {}"
    and "({p. p \<le> K \<and> prime p \<and> p * M \<le> K} \<union> {p. p \<le> K \<and>
      prime p \<and> K < p * M \<and> 3 * p \<le> K})
           \<inter> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
             1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K} = {}"
    and "\<And>p. p \<in> {p. p \<le> K \<and> prime p \<and> p * M \<le> K} \<Longrightarrow>
           mainCoef K M p = real (6 * hof K * nat_log p (5 * K) + hof K * multiplicity p (24::nat))"
    and "\<And>p. p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and>
      3 * p \<le> K} \<Longrightarrow> mainCoef K M p = real p * R_r (real K / real p)"
    and "\<And>p. p \<in> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
      1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K} \<Longrightarrow>
           mainCoef K M p = real K * outer_integrand (real p / real K)"
proof -
  have fl: "nat (floor (2 * lam_r * real K)) = 2 * hof K"
  proof -
    have e: "2 * lam_r * real K = real (2 * hof K)" using hof_real[OF K(1)]
      by (simp add: mult.assoc)
    show ?thesis unfolding e by (simp only: floor_of_nat nat_int)
  qed
  have le: "real p \<le> 2 * lam_r * real K \<longleftrightarrow> p \<le> 2 * hof K" for p
  proof -
    have e: "2 * lam_r * real K = real (2 * hof K)" using hof_real[OF K(1)]
      by (simp add: mult.assoc)
    show ?thesis unfolding e of_nat_le_iff ..
  qed
  have lt: "1 / 3 * real K < real p \<longleftrightarrow> K < 3 * p" for p
  proof
    assume "1 / 3 * real K < real p"
    hence "real K < real (3 * p)" by (simp only: of_nat_mult of_nat_numeral)
    thus "K < 3 * p" by (simp only: of_nat_less_iff)
  next
    assume "K < 3 * p"
    hence "real K < real (3 * p)" by (simp only: of_nat_less_iff)
    hence "real K < 3 * real p" by (simp only: of_nat_mult of_nat_numeral)
    thus "1 / 3 * real K < real p" by linarith
  qed
  have hK: "K \<le> 2 * hof K"
    using K(1) unfolding hof_def by fastforce
  show "{p. p \<le> 2 * hof K \<and> prime p} =
           {p. p \<le> K \<and> prime p \<and> p * M \<le> K} \<union> {p. p \<le> K \<and>
             prime p \<and> K < p * M \<and> 3 * p \<le> K}
           \<union> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
             1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K}"
    unfolding fl le lt using hK M
    by (auto simp: not_le dest: le_of_three_mul order_trans[OF three_le_mul[OF M]] intro:
      order_trans[OF _ hK])
  show "{p. p \<le> K \<and> prime p \<and> p * M \<le> K} \<inter> {p. p \<le> K \<and>
    prime p \<and> K < p * M \<and> 3 * p \<le> K} = {}"
    by auto
  show "({p. p \<le> K \<and> prime p \<and> p * M \<le> K} \<union> {p. p \<le> K \<and>
    prime p \<and> K < p * M \<and> 3 * p \<le> K})
           \<inter> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
             1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K} = {}"
    unfolding fl le lt using M
    by (auto simp: not_mul_le_of_lt[OF M] dest: leD)
  show "mainCoef K M p = real (6 * hof K * nat_log p (5 * K) + hof K * multiplicity p (24::nat))"
    if "p \<in> {p. p \<le> K \<and> prime p \<and> p * M \<le> K}" for p
    using that unfolding mainCoef_def by simp
  show "mainCoef K M p = real p * R_r (real K / real p)"
    if "p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and> 3 * p \<le> K}" for p
    using that unfolding mainCoef_def by simp
  show "mainCoef K M p = real K * outer_integrand (real p / real K)"
    if "p \<in> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
      1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K}" for p
    using that M unfolding mainCoef_def lt
    using not_mul_le_of_lt[OF M, of K p] by (auto dest: leD)
qed

lemma filterlim_40: "filterlim (\<lambda>n :: nat. 40 * n) at_top at_top"
  by (rule filterlim_subseq) (simp add: strict_mono_Suc_iff)

text \<open>Proposition 5.2 (with @{text "K = 40n"}):
  @{text "limsup K^-^2 log m_{K,M} \<le>
    I_out + 6\<lambda>/M + \<integral>_3^M R(x)/x^3 dx"}.\<close>
theorem log_mKM_limsup:
  assumes M: "40 \<le> M" and e: "0 < \<epsilon>"
  shows "\<forall>\<^sub>F n in at_top.
    ln (of_rat (mKM (40 * n) M)) / real (40 * n) ^ 2 \<le>
      of_rat Iout + 6 * lam_r / real M
      + interval_lebesgue_integral lborel (ereal 3) (ereal (real M)) (\<lambda>x. R_r x / x ^ 3) +
        \<epsilon>"
proof -
  define IR where "IR = interval_lebesgue_integral lborel (ereal 3) (ereal (real M)) (\<lambda>x.
    R_r x / x ^ 3)"
  obtain C1' where C1': "\<And>K p. prime p \<Longrightarrow> InnerHyp K M p \<Longrightarrow>
       \<bar>of_rat (gammaIn K M p) - real p * Gam_r (real K / real p)\<bar> \<le> C1' \<and>
       \<bar>of_int (vpS K p) - real p * Nfun_r (real K / real p)\<bar> \<le> C1'"
    using gammaIn_uniform_estimate[OF M] by blast
  obtain C2' where C2': "\<And>K p. prime p \<Longrightarrow> 40 dvd K \<Longrightarrow>
    OuterHyp K p \<Longrightarrow>
       \<bar>- of_int (gammaOut K p) - real K * (R0_r (real p / real K) - dfun_r (real p /
         real K))\<bar> \<le> C2' \<and>
       \<bar>- of_int (vpS K p) - real K * (- 2 * lam_r * of_int (floor (real K / real p)) +
            (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * (real p / real K))))\<bar> \<le> C2'"
    using uniformity_outer by blast
  define C1 where "C1 = max C1' 0"
  define C2 where "C2 = max C2' 0"
  have C1: "0 \<le> C1" and C2: "0 \<le> C2" unfolding C1_def C2_def by simp_all
  have hin: "\<And>K p. prime p \<Longrightarrow> InnerHyp K M p \<Longrightarrow>
       \<bar>of_rat (gammaIn K M p) - real p * Gam_r (real K / real p)\<bar> \<le> C1 \<and>
       \<bar>of_int (vpS K p) - real p * Nfun_r (real K / real p)\<bar> \<le> C1"
    unfolding C1_def using C1' by (meson max.coboundedI1)
  have hout: "\<And>K p. prime p \<Longrightarrow> 40 dvd K \<Longrightarrow>
    OuterHyp K p \<Longrightarrow>
       \<bar>- of_int (gammaOut K p) - real K * (R0_r (real p / real K) - dfun_r (real p /
         real K))\<bar> \<le> C2 \<and>
       \<bar>- of_int (vpS K p) - real K * (- 2 * lam_r * of_int (floor (real K / real p)) +
            (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * (real p / real K))))\<bar> \<le> C2"
    unfolding C2_def using C2' by (meson max.coboundedI1)
  define C where "C = 2 * C1 + 1 + 2 * C2"
  have C0: "0 \<le> C" unfolding C_def using C1 C2 by linarith
  have e4: "0 < \<epsilon> / 4" using e by simp
  have M3': "3 \<le> M" and M0: "0 < M" using M by simp_all
  have E1: "\<forall>\<^sub>F K in at_top.
      (\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> p * M \<le> K}.
          real (6 * hof K * nat_log p (5 * K) + hof K * multiplicity p (24::nat)) * ln (real p))
        \<le> (6 * lam_r / real M + \<epsilon> / 4) * real K ^ 2"
    by (rule small_prime_sum_bound[OF M0 e4])
  obtain BR where BR: "\<And>x. x \<in> {3..real M} \<Longrightarrow> \<bar>R_r x\<bar> \<le> BR"
    using R_bounded by blast
  obtain DR where DR: "countable DR" "\<And>x. 0 < x \<Longrightarrow>
    x \<notin> DR \<Longrightarrow> isCont R_r x"
    using R_continuousAt_off by blast
  have E2: "\<forall>\<^sub>F K in at_top.
      (\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and>
        3 * p \<le> K}. real p * R_r (real K / real p) * ln (real p))
        \<le> (IR + \<epsilon> / 4) * real K ^ 2"
  proof -
    have m3: "3 < M" using M by linarith
    have dr: "\<And>x. x \<in> {3<..<real M} \<Longrightarrow> x \<notin> DR \<Longrightarrow>
      isCont R_r x" using DR(2) by simp
    show ?thesis unfolding IR_def by (rule inner_prime_sum_limsup[OF m3 BR DR(1) dr e4])
  qed
  obtain BO where BO: "\<And>y. y \<in> {1 / 3..2 * lam_r} \<Longrightarrow>
    \<bar>outer_integrand y\<bar> \<le> BO"
    using outerIntegrand_bounded by blast
  obtain DO where DO: "countable DO" "\<And>y. 0 < y \<Longrightarrow>
    y \<notin> DO \<Longrightarrow> isCont outer_integrand y"
    using outerIntegrand_continuousAt_off by blast
  have E3: "\<forall>\<^sub>F K in at_top.
      (\<Sum> p \<in> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
        1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K}.
          outer_integrand (real p / real K) * ln (real p))
        \<le> (of_rat Iout + \<epsilon> / 4) * real K"
    using outer_prime_sum_limsup[of "1 / 3" "2 * lam_r" outer_integrand BO DO "\<epsilon> /
      4"] BO DO e4
    unfolding outer_integral_value by (auto simp: lam_r_def)
  have E4: "\<forall>\<^sub>F K in at_top. 200 * M ^ 2 \<le> K \<and>
    C * (2 * real K * ln 4) \<le> \<epsilon> / 4 * real K ^ 2"
  proof -
    have "\<forall>\<^sub>F K in at_top. nat (ceiling (8 * C * ln 4 / \<epsilon>)) \<le> K"
      by (rule eventually_ge_at_top)
    moreover have "\<forall>\<^sub>F K in at_top. 200 * M ^ 2 \<le> K"
      by (rule eventually_ge_at_top)
    ultimately show ?thesis
    proof (eventually_elim)
      case (elim K)
      have "8 * C * ln 4 / \<epsilon> \<le> real K"
      proof -
        have "real (nat (ceiling (8 * C * ln 4 / \<epsilon>))) \<le> real K" using elim(1)
          by (simp only: of_nat_le_iff)
        thus ?thesis using real_nat_ceiling_ge[of "8 * C * ln 4 / \<epsilon>"] by linarith
      qed
      hence "8 * C * ln 4 \<le> \<epsilon> * real K" using e
        by (simp add: divide_le_eq mult.commute)
      hence a: "8 * C * ln 4 * real K \<le> \<epsilon> * real K * real K"
        by (rule mult_right_mono) simp
      have b: "C * (2 * real K * ln 4) = (8 * C * ln 4 * real K) / 4" by (simp add: algebra_simps)
      have c: "\<epsilon> / 4 * real K ^ 2 = (\<epsilon> * real K * real K) / 4"
        by (simp add: power2_eq_square algebra_simps)
      show ?case using elim(2) a b c by (intro conjI) linarith+
    qed
  qed
  have all: "\<forall>\<^sub>F K in at_top.
      (\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> p * M \<le> K}.
          real (6 * hof K * nat_log p (5 * K) + hof K * multiplicity p (24::nat)) * ln (real p))
        \<le> (6 * lam_r / real M + \<epsilon> / 4) * real K ^ 2 \<and>
      (\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and>
        3 * p \<le> K}. real p * R_r (real K / real p) * ln (real p))
        \<le> (IR + \<epsilon> / 4) * real K ^ 2 \<and>
      (\<Sum> p \<in> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
        1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K}.
          outer_integrand (real p / real K) * ln (real p))
        \<le> (of_rat Iout + \<epsilon> / 4) * real K \<and>
      (200 * M ^ 2 \<le> K \<and> C * (2 * real K * ln 4) \<le> \<epsilon> / 4 * real K ^ 2)"
    by (intro eventually_conj E1 E2 E3 E4)
  show ?thesis
    using eventually_compose_filterlim[OF all filterlim_40] eventually_gt_at_top[of "0 :: nat"]
  proof (eventually_elim)
    case (elim n)
    define K where "K = 40 * n"
    note F = elim(1)[folded K_def]
    have K40: "40 dvd K" and K0: "0 < K" unfolding K_def using elim(2) by simp_all
    have h1: "(\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> p * M \<le> K}.
          real (6 * hof K * nat_log p (5 * K) + hof K * multiplicity p (24::nat)) * ln (real p))
        \<le> (6 * lam_r / real M + \<epsilon> / 4) * real K ^ 2"
      and h2: "(\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and>
        3 * p \<le> K}. real p * R_r (real K / real p) * ln (real p))
        \<le> (IR + \<epsilon> / 4) * real K ^ 2"
      and h3: "(\<Sum> p \<in> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
        1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K}.
          outer_integrand (real p / real K) * ln (real p))
        \<le> (of_rat Iout + \<epsilon> / 4) * real K"
      and hKM: "200 * M ^ 2 \<le> K" and h4: "C * (2 * real K * ln 4) \<le>
        \<epsilon> / 4 * real K ^ 2"
      using F by blast+
    let ?P = "{p. p \<le> 2 * hof K \<and> prime p}"
    have hterm: "ln (of_rat (mKM K M)) \<le> (\<Sum> p \<in>
      ?P. mainCoef K M p * ln (real p)) + C * (\<Sum> p \<in> ?P. ln (real p))"
    proof -
      have "ln (of_rat (mKM K M)) = (\<Sum> p \<in> ?P. - of_int (Lp K M p) * ln (real p))"
        by (rule log_mKM)
      also have "\<dots> \<le> (\<Sum> p \<in> ?P. (mainCoef K M p + C) * ln (real p))"
      proof (rule sum_mono)
        fix p assume "p \<in> ?P"
        hence pp: "prime p" "p \<le> 2 * hof K" by auto
        have "- of_int (Lp K M p) \<le> mainCoef K M p + C"
          unfolding C_def by (rule neg_Lp_le[OF M C1 C2 hin hout K40 hKM K0 pp])
        moreover have "0 \<le> ln (real p)"
          by (rule ln_ge_zero) (use prime_ge_1_nat[OF pp(1)] in simp)
        ultimately show "- of_int (Lp K M p) * ln (real p) \<le> (mainCoef K M p + C) * ln (real p)"
          by (rule mult_right_mono)
      qed
      also have "\<dots> = (\<Sum> p \<in> ?P. mainCoef K M p * ln (real p)) + C * (\<Sum> p \<in>
        ?P. ln (real p))"
        by (simp add: sum.distrib sum_distrib_left distrib_right)
      finally show ?thesis .
    qed
    have hsplit: "(\<Sum> p \<in> ?P. mainCoef K M p * ln (real p)) =
        (\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> p * M \<le> K}.
            real (6 * hof K * nat_log p (5 * K) + hof K * multiplicity p (24::nat)) * ln (real p))
        + (\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and>
          3 * p \<le> K}. real p * R_r (real K / real p) * ln (real p))
        + real K * (\<Sum> p \<in> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and>
          prime p \<and> 1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K}.
            outer_integrand (real p / real K) * ln (real p))"
    proof -
      note ps = primes_split[OF K40 K0 M3']
      let ?A = "{p. p \<le> K \<and> prime p \<and> p * M \<le> K}"
      let ?B = "{p. p \<le> K \<and> prime p \<and> K < p * M \<and> 3 * p \<le> K}"
      let ?C = "{p. p \<le> nat (floor (2 * lam_r * real K)) \<and> prime p \<and>
        1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K}"
      have fA: "finite ?A" by (rule finite_subset[of _ "{..K}"]) auto
      have fB: "finite ?B" by (rule finite_subset[of _ "{..K}"]) auto
      have fC: "finite ?C" by (rule finite_subset[of _ "{..nat (floor (2 * lam_r * real K))}"]) auto
      have s: "(\<Sum> p \<in> ?P. mainCoef K M p * ln (real p)) =
               (\<Sum> p \<in> ?A. mainCoef K M p * ln (real p)) + (\<Sum> p \<in>
                 ?B. mainCoef K M p * ln (real p))
               + (\<Sum> p \<in> ?C. mainCoef K M p * ln (real p))"
        unfolding ps(1) sum.union_disjoint[OF finite_UnI[OF fA fB] fC ps(3)] sum.union_disjoint[OF
          fA fB ps(2)] ..
      have c1: "(\<Sum> p \<in> ?A. mainCoef K M p * ln (real p)) =
                (\<Sum> p \<in> ?A. real (6 * hof K * nat_log p (5 * K) + hof K *
                  multiplicity p (24::nat)) * ln (real p))"
        by (rule sum.cong[OF refl]) (simp add: ps(4))
      have c2: "(\<Sum> p \<in> ?B. mainCoef K M p * ln (real p)) = (\<Sum> p \<in>
        ?B. real p * R_r (real K / real p) * ln (real p))"
        by (rule sum.cong[OF refl]) (simp add: ps(5))
      have c3: "(\<Sum> p \<in> ?C. mainCoef K M p * ln (real p)) = real K * (\<Sum> p \<in>
        ?C. outer_integrand (real p / real K) * ln (real p))"
        by (subst sum_distrib_left) (rule sum.cong[OF refl], simp add: ps(6))
      show ?thesis unfolding s c1 c2 c3 ..
    qed
    have hlogP: "(\<Sum> p \<in> ?P. ln (real p)) \<le> 2 * real K * ln 4" by (rule sum_log_P_le)
    have Kr: "0 \<le> real K" by simp
    have h3': "real K * (\<Sum> p \<in> {p. p \<le> nat (floor (2 * lam_r * real K)) \<and>
      prime p \<and> 1 / 3 * real K < real p \<and> real p \<le> 2 * lam_r * real K}.
            outer_integrand (real p / real K) * ln (real p)) \<le>
              (of_rat Iout + \<epsilon> / 4) * real K ^ 2"
      using mult_left_mono[OF h3 Kr] by (simp add: power2_eq_square algebra_simps)
    have h5: "C * (\<Sum> p \<in> ?P. ln (real p)) \<le> C * (2 * real K * ln 4)"
      by (rule mult_left_mono[OF hlogP C0])
    have "ln (of_rat (mKM K M)) \<le> (of_rat Iout + 6 * lam_r / real M + IR + \<epsilon>) *
      real K ^ 2"
      using hterm[unfolded hsplit] h1 h2 h3' h4 h5 by (simp add: algebra_simps)
    moreover have "0 < real K ^ 2" using K0 by simp
    ultimately show ?case unfolding IR_def[symmetric] K_def[symmetric] by (simp add: divide_le_eq)
  qed
qed

text \<open>(5.21): @{text "limsup K^-^2 log m_{K,M} \<le> A_M"}
  for @{text "M \<in> 40\<int>"}, @{text "M \<ge> 40"}: split the integral at 20 and
  at @{text M} and use (5.16)-(5.18).\<close>
theorem log_mKM_limsup_AM:
  assumes M: "40 \<le> M" "40 dvd M" and e: "0 < \<epsilon>"
  shows "\<forall>\<^sub>F n in at_top. ln (of_rat (mKM (40 * n) M)) / real (40 * n) ^ 2 \<le>
    of_rat (AM M) + \<epsilon>"
proof -
  let ?f = "\<lambda>x. R_r x / x ^ 3"
  have M': "40 \<le> real M" using M by simp
  have int3: "set_integrable lborel {3..} ?f" by (rule R_integrableOn)
  have sub: "set_integrable lborel S ?f" if "S \<subseteq> {3..}" "S \<in> sets borel" for S
    by (rule set_integrable_subset[OF int3]) (use that in auto)
  have split1: "interval_lebesgue_integral lborel (ereal 3) (ereal (real M)) ?f
      = interval_lebesgue_integral lborel (ereal 3) (ereal 20) ?f +
        interval_lebesgue_integral lborel (ereal 20) (ereal (real M)) ?f"
  proof -
    have mn: "min (ereal 3) (min (ereal 20) (ereal (real M))) = ereal 3"
             "max (ereal 3) (max (ereal 20) (ereal (real M))) = ereal (real M)" using M'
               by (simp_all add: min_def max_def)
    have "interval_lebesgue_integrable lborel (ereal 3) (ereal (real M)) ?f"
      unfolding interval_lebesgue_integrable_def einterval_eq using M' by (auto intro!: sub)
    thus ?thesis using interval_integral_sum[of "ereal 3" "ereal 20" "ereal (real M)" ?f] mn by simp
  qed
  have split2: "interval_lebesgue_integral lborel (ereal 20) (ereal (real M)) ?f =
    set_lebesgue_integral lborel {20<..real M} ?f"
    by (rule interval_integral_Ioc) (use M' in simp)
  have split3: "set_lebesgue_integral lborel {20<..} ?f =
    set_lebesgue_integral lborel {20<..real M} ?f + set_lebesgue_integral lborel {real M<..} ?f"
  proof -
    have u: "{20<..} = {20<..real M} \<union> {real M<..}" using M' by auto
    have s1: "{20<..real M} \<subseteq> {3..}" by force
    have s2: "{real M<..} \<subseteq> {3..}" using M' by fastforce
    have d: "{20<..real M} \<inter> {real M<..} = {}" by force
    show ?thesis unfolding u by (rule set_integral_Un[OF d]) (auto intro!: sub s1 s2)
  qed
  have h16: "set_lebesgue_integral lborel {20<..} ?f \<le> - 2689 / 48000" by (rule R_tail_20_bound)
  have h17: "- lam_r / real M + (2923 / 240 - 1 / 4) / real M ^ 2 - 32 / real M ^ 3 \<le>
    set_lebesgue_integral lborel {real M<..} ?f"
    by (rule R_tail_M_bound) (use M in auto)
  have key: "of_rat Iout + 6 * lam_r / real M +
    interval_lebesgue_integral lborel (ereal 3) (ereal (real M)) ?f \<le> of_rat (AM M)"
  proof -
    have nA: "Astar = Iout + 322437603634266857629 / 7535670527041937280000 - 2689 / 48000"
      unfolding Astar_def Iout_def by simp
    have AM: "of_rat (AM M) = of_rat Astar + 7 * (lam_r / real M) - (2923 / 240 - 1 / 4) /
      real M ^ 2 + 32 / real M ^ 3"
      unfolding AM_def lam_q_def lam_r_def
        by (simp add: of_rat_add of_rat_diff of_rat_divide of_rat_mult of_rat_power)
    have As: "(of_rat Astar :: real) = of_rat Iout + 322437603634266857629 /
      7535670527041937280000 - 2689 / 48000"
      unfolding nA by (simp add: of_rat_add of_rat_diff of_rat_divide)
    have e6: "6 * lam_r / real M = 6 * (lam_r / real M)" by simp
    have e1: "- lam_r / real M = - (lam_r / real M)" by simp
    show ?thesis unfolding split1 split2 R_integral_3_20 e6 using h16 h17[unfolded e1] split3 AM As
      by linarith
  qed
  show ?thesis
    using log_mKM_limsup[OF M(1) e] by (rule eventually_mono) (use key in linarith)
qed

end


