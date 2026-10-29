(*  Title:   Zeta5_Far_Poles.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Far_Poles
  imports Zeta5_IntValued Legendre_Factorial_Valuation
begin

section \<open>The far-pole constant and Lemma 3.3\<close>

text \<open>Section 3 of the paper: the valuations of the Bernoulli numbers (von Staudt--Clausen,
  from the
  AFP), the far-pole constant \<open>C\<^sub>p\<close> of Section 3.1, counting lemmas
    for multiples and valuations
  of integers, partial fractions with linear poles, the product-difference estimate and
  Lemma 3.3 (@{text far_pole_valuation_bound}).  Lean theories @{text Section3}, @{text Lemma33},
    @{text MuMod}.\<close>

subsection \<open>Bernoulli valuations (von Staudt-Clausen, from the AFP)\<close>

text \<open>@{text "v_p(\<kappa>_d) \<ge> -1"} for odd @{text p} (false
  for @{text "p = 2"}: @{text "\<kappa>_3 = 1/4"}).
  Follows from @{text "Bernoulli_FPS.vonStaudt_Clausen"} /
    @{text "Bernoulli_FPS.prime_dvd_bernoulli_denom_iff"}:
  the denominator of @{text "B_n"} is squarefree.\<close>
lemma multiplicity_24:
  assumes "prime p" "p \<noteq> 2"
  shows "multiplicity p (24::nat) = (if p = 3 then 1 else 0)"
proof -
  have m3: "multiplicity p (3::nat) = (if p = 3 then 1 else 0)"
    using assms(1) by (force simp: prime_multiplicity_prime)
  have "\<not> p dvd (2 ^ 3 :: nat)"
  proof
    assume "p dvd (2 ^ 3 :: nat)"
    hence "p dvd 2" by (rule prime_dvd_power[OF assms(1)])
    hence "p = 2" using primes_dvd_imp_eq[OF assms(1) two_is_prime_nat] by simp
    thus False using assms(2) by simp
  qed
  hence m8: "multiplicity p (2 ^ 3 :: nat) = 0" by (rule not_dvd_imp_multiplicity_0)
  have "multiplicity p (3 * 2 ^ 3 :: nat) = multiplicity p 3 + multiplicity p (2 ^ 3)"
    using assms(1) by (intro prime_elem_multiplicity_mult_distrib) auto
  thus ?thesis using m3 m8 by simp
qed

text \<open>The denominator of a Bernoulli number is squarefree (von Staudt--Clausen):
  @{text "v_p(B_n) \<ge> -1"}.\<close>
lemma vp_bernoulli_ge:
  assumes "prime p" "(bernoulli n :: rat) \<noteq> 0"
  shows "- 1 \<le> vp p (bernoulli n)"
proof -
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  have "bernoulli_num n \<noteq> 0" using assms(2) by (auto simp: bernoulli_conv_num_denom)
  hence "vp p (bernoulli n) = int (multiplicity (int p) (bernoulli_num n)) -
    int (multiplicity p (bernoulli_denom n))"
    unfolding vp_def bernoulli_conv_num_denom using pe
      by (simp add: qmultiplicity_divide_of_int multiplicity_int)
  moreover have "multiplicity p (bernoulli_denom n) \<le> 1"
    using squarefree_bernoulli_denom[of n] assms(1)
      by (intro squarefree_imp_multiplicity_prime_le_1) auto
  ultimately show ?thesis by simp
qed

text \<open>@{text "B_n"} is @{text p}-integral unless @{text "(p - 1) | n"} (for odd
  @{text p}).\<close>
lemma vp_bernoulli_nonneg:
  assumes "prime p" "p \<noteq> 2" "\<not> (p - 1) dvd n"
  shows "0 \<le> vp p (bernoulli n)"
proof (cases "(bernoulli n :: rat) = 0")
  case True
  thus ?thesis by (simp add: vp_def)
next
  case False
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  have num: "bernoulli_num n \<noteq> 0" using False by (auto simp: bernoulli_conv_num_denom)
  have nd: "\<not> p dvd bernoulli_denom n"
  proof (cases "even n \<and> 0 < n")
    case True
    thus ?thesis using assms(1,3) by (simp add: prime_dvd_bernoulli_denom_iff)
  next
    case F: False
    hence "bernoulli_denom n = 1 \<or> bernoulli_denom n = 2" by (auto simp: bernoulli_denom_def)
    thus ?thesis using assms(1,2) primes_dvd_imp_eq[OF assms(1) two_is_prime_nat] by auto
  qed
  have "vp p (bernoulli n) = int (multiplicity (int p) (bernoulli_num n)) -
    int (multiplicity p (bernoulli_denom n))"
    unfolding vp_def bernoulli_conv_num_denom using num pe
      by (simp add: qmultiplicity_divide_of_int multiplicity_int)
  thus ?thesis using nd by (simp add: not_dvd_imp_multiplicity_0)
qed

lemma three_dvd_consec: "(3::int) dvd m * (m - 1) * (m - 2)"
proof -
  have "3 dvd m \<or> 3 dvd (m - 1) \<or> 3 dvd (m - 2)" by presburger
  thus ?thesis by (auto intro: dvd_mult dvd_mult2)
qed

lemma kappa_eq: "kappa d = of_int (int d * (int d - 1) * (int d - 2)) * bernoulli (d - 3) / 24"
  by (simp add: kappa_def)

lemma vp_24: "prime p \<Longrightarrow> p \<noteq> 2 \<Longrightarrow>
  vp p 24 = (if p = 3 then 1 else 0)"
  unfolding vp_def using multiplicity_24[of p]
  by (simp add: multiplicity_int[of p 24, symmetric] qmultiplicity_of_nat[of "int p" 24,
    simplified])

lemma kappa_padicVal_ge:
  assumes "prime p" "p \<noteq> 2" "kappa d \<noteq> 0"
  shows "- 1 \<le> vp p (kappa d)"
proof -
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  define m where "m = int d * (int d - 1) * (int d - 2)"
  have m0: "m \<noteq> 0" and B0: "(bernoulli (d - 3) :: rat) \<noteq> 0" using assms(3)
    by (auto simp: kappa_eq m_def)
  have eq: "vp p (kappa d) = vp p (of_int m) + vp p (bernoulli (d - 3)) - vp p 24"
    unfolding kappa_eq m_def[symmetric] vp_def using pe m0 B0
      by (simp add: qmultiplicity_mult qmultiplicity_divide)
  have "0 \<le> vp p (of_int m) - vp p 24"
  proof (cases "p = 3")
    case True
    have "int 3 dvd m" unfolding m_def by (simp add: three_dvd_consec)
    hence "1 \<le> multiplicity (int 3) m" using m0
      by (force intro: multiplicity_geI)
    hence "1 \<le> vp p (of_int m)" using True by (simp add: vp_def)
    moreover have "vp p 24 = 1" using vp_24[OF assms(1,2)] True by simp
    ultimately show ?thesis by simp
  next
    case False
    have "vp p 24 = 0" using vp_24[OF assms(1,2)] False by simp
    moreover have "0 \<le> vp p (of_int m)" by (simp add: vp_def)
    ultimately show ?thesis by simp
  qed
  moreover have "- 1 \<le> vp p (bernoulli (d - 3))" by (rule vp_bernoulli_ge[OF assms(1) B0])
  ultimately show ?thesis using eq by linarith
qed

text \<open>@{text "\<kappa>_d \<in> \<int>_p"}
  for @{text "d \<le> p + 1"}, @{text "p \<ge> 7"} (in fact for @{text "d \<le> 4p - 2"}).\<close>
lemma kappa_integral:
  assumes "prime p" "7 \<le> p" "d \<le> p + 1" "kappa d \<noteq> 0"
  shows "0 \<le> vp p (kappa d)"
proof -
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  define m where "m = int d * (int d - 1) * (int d - 2)"
  have m0: "m \<noteq> 0" and B0: "(bernoulli (d - 3) :: rat) \<noteq> 0" using assms(4)
    by (auto simp: kappa_eq m_def)
  have d3: "3 \<le> d" using m0 by (cases d rule: nat.exhaust; cases "d - 1"; auto simp: m_def)
  have "vp p (kappa d) = vp p (of_int m) + vp p (bernoulli (d - 3)) - vp p 24"
    unfolding kappa_eq m_def[symmetric] vp_def using pe m0 B0
      by (simp add: qmultiplicity_mult qmultiplicity_divide)
  moreover have "vp p 24 = 0" using assms(1,2) by (simp add: vp_24)
  moreover have "0 \<le> vp p (of_int m)" by (simp add: vp_def)
  moreover have "0 \<le> vp p (bernoulli (d - 3))"
  proof (cases "d = 3")
    case True
    have "(bernoulli 0 :: rat) = 1"
      by (rule bernoulli_0)
    thus ?thesis using True by (simp add: vp_def)
  next
    case False
    hence "\<not> (p - 1) dvd (d - 3)" using assms(2,3) d3 dvd_imp_le[of "p - 1" "d - 3"] by auto
    thus ?thesis using assms(1,2) by (intro vp_bernoulli_nonneg) auto
  qed
  ultimately show ?thesis by linarith
qed

text \<open>The polynomial moments: @{text "v_p(mu(t^e)) \<ge> -1"}, and @{text "p"}-integral
  for @{text "e < 2p - 3"}.\<close>
lemma muMono_eq:
  "muMono e = (-1) ^ e * (bernoulli (2 * e + 2) * of_int ((2 * int e + 3) * (2 * int e + 4) * (2 *
    int e + 5)) / 24)"
  by (simp add: muMono_def)

lemma muMono_padicVal:
  assumes "prime p" "7 \<le> p" "muMono e \<noteq> 0"
  shows "- 1 \<le> vp p (muMono e) \<and> (e < 2 * p - 3 \<longrightarrow> 0 \<le> vp p (muMono e))"
proof -
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  define m where "m = (2 * int e + 3) * (2 * int e + 4) * (2 * int e + 5)"
  have m0: "m \<noteq> 0" unfolding m_def by (auto simp: mult_pos_pos)
  have B0: "(bernoulli (2 * e + 2) :: rat) \<noteq> 0" using assms(3) by (auto simp: muMono_eq)
  have v24: "vp p 24 = 0" using assms(1,2) by (simp add: vp_24)
  have sign: "vp p (muMono e) = vp p (bernoulli (2 * e + 2) * of_int m / 24)"
  proof (cases "even e")
    case True
    thus ?thesis unfolding muMono_eq m_def[symmetric] by (simp add: neg_one_even_power)
  next
    case False
    thus ?thesis unfolding muMono_eq m_def[symmetric] vp_def by (simp add: neg_one_odd_power)
  qed
  have eq: "vp p (muMono e) = vp p (bernoulli (2 * e + 2)) + vp p (of_int m)"
  proof -
    have "vp p (bernoulli (2 * e + 2) * of_int m / 24) =
      vp p (bernoulli (2 * e + 2)) + vp p (of_int m) - vp p 24"
      unfolding vp_def using pe m0 B0 by (simp add: qmultiplicity_mult qmultiplicity_divide)
    thus ?thesis using sign v24 by simp
  qed
  have vm: "0 \<le> vp p (of_int m)" by (simp add: vp_def)
  have vB: "- 1 \<le> vp p (bernoulli (2 * e + 2))" by (rule vp_bernoulli_ge[OF assms(1) B0])
  have part2: "0 \<le> vp p (muMono e)" if e: "e < 2 * p - 3"
  proof (cases "(p - 1) dvd (2 * e + 2)")
    case False
    hence "0 \<le> vp p (bernoulli (2 * e + 2))" using assms(1,2)
      by (intro vp_bernoulli_nonneg) auto
    thus ?thesis using eq vm by linarith
  next
    case True
    then obtain k where k: "2 * e + 2 = (p - 1) * k" by (elim dvdE)
    have "(p - 1) * k = 2 * e + 2" using k by simp
    also have "\<dots> < (p - 1) * 4" using e assms(2) by (simp add: diff_mult_distrib)
    finally have "k < 4" using assms(2) mult_less_cancel1 by blast
    moreover have "k \<noteq> 0" using k by (cases k) auto
    ultimately have "k = 1 \<or> k = 2 \<or> k = 3" by auto
    moreover have k': "2 * int e + 2 = (int p - 1) * int k"
    proof -
      have "int (2 * e + 2) = int ((p - 1) * k)" using k by simp
      thus ?thesis using assms(2) by (simp add: of_nat_diff)
    qed
    ultimately have "int p dvd m"
    proof (elim disjE)
      assume "k = 1"
      hence p: "int p = 2 * int e + 3" using k' by simp
      have "m = int p * ((2 * int e + 4) * (2 * int e + 5))" unfolding m_def p
        by (simp add: algebra_simps)
      thus ?thesis by simp
    next
      assume "k = 2"
      hence p: "int p = int e + 2" using k' by simp
      have "m = int p * (2 * (2 * int e + 3) * (2 * int e + 5))" unfolding m_def p
        by (simp add: algebra_simps)
      thus ?thesis by simp
    next
      assume "k = 3"
      hence p: "3 * int p = 2 * int e + 5" using k' by simp
      have "m = int p * (3 * ((2 * int e + 3) * (2 * int e + 4)))" unfolding m_def p[symmetric]
        by (simp add: algebra_simps)
      thus ?thesis by simp
    qed
    hence "1 \<le> multiplicity (int p) m" using m0 pe
      by (metis dvd_imp_multiplicity_le multiplicity_prime)
    hence "1 \<le> vp p (of_int m)" by (simp add: vp_def)
    thus ?thesis using eq vB by linarith
  qed
  show ?thesis using eq vm vB part2 by linarith
qed

text \<open>The modified moments @{text "mu(t^e) - c_e/p"} are @{text p}-integral (Lean:
  @{text muMod_vge}).\<close>
lemma vge_one_of_qcong_0:
  assumes "prime p" "[z = 0] (qmod int p)"
  shows "vge p z 1"
proof (cases "z = 0")
  case True
  thus ?thesis by (simp add: vge_zero)
next
  case False
  have pe: "prime_elem (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  obtain a b where ab: "quotient_of z = (a, b)" by (cases "quotient_of z")
  from assms(2) ab have dvd: "int p dvd a" and cop: "coprime b (int p)"
    by (auto simp: qcong_0_iff)
  have a0: "a \<noteq> 0" using False quotient_of_div[OF ab] by auto
  have ndvd: "\<not> int p dvd b"
  proof
    assume d: "int p dvd b"
    have "coprime (int p) b" using cop by (simp add: coprime_commute)
    hence "is_unit (int p)" using coprime_absorb_left[OF d] by simp
    thus False using pe by (simp add: prime_elem_def)
  qed
  have mb: "multiplicity (int p) b = 0" by (rule not_dvd_imp_multiplicity_0[OF ndvd])
  have ma: "1 \<le> multiplicity (int p) a"
    using dvd a0 pe by (metis dvd_imp_multiplicity_le multiplicity_prime)
  have "qmultiplicity (int p) z = int (multiplicity (int p) a) - int (multiplicity (int p) b)"
    by (simp add: qmultiplicity_def ab)
  thus ?thesis using ma mb by (simp add: vge_def vp_def)
qed

lemma muMod_vge: "prime p \<Longrightarrow> 7 \<le> p \<Longrightarrow>
  vge p (muMono e - cCorr p e / of_nat p) 0"
proof -
  assume p: "prime p" and p7: "7 \<le> p"
  have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer)
  have p0: "p \<noteq> 0" and p1: "1 < int p" using prime_gt_1_nat[OF p] by auto
  show "vge p (muMono e - cCorr p e / of_nat p) 0"
  proof (cases "muMono e = 0")
    case True
    thus ?thesis by (simp add: cCorr_def vge_zero)
  next
    case mu0: False
    note mv = muMono_padicVal[OF p p7 mu0]
    show ?thesis
    proof (cases "e < 2 * p - 3")
      case True
      thus ?thesis using mv by (simp add: cCorr_def vge_def)
    next
      case False
      define y where "y = of_nat p * muMono e"
      define r where "r = y qmod int p"
      have cc: "cCorr p e = of_int r" using False by (simp add: cCorr_def r_def y_def)
      have "vp p y = vp p (of_nat p) + vp p (muMono e)"
        unfolding y_def vp_def using pe p0 mu0 by (simp add: qmultiplicity_mult)
      also have "vp p (of_nat p) = 1"
        using pe by (simp add: vp_def qmultiplicity_of_nat multiplicity_prime)
      finally have vy: "0 \<le> qmultiplicity (int p) y" using mv by (simp add: vp_def)
      have "coprime (snd (quotient_of y)) (int p)"
        by (rule qmultiplicity_prime_nonneg_imp_coprime_denom[OF vy]) (use p in \<open>simp add:
          prime_nat_int_transfer\<close>)
      hence qc: "[y = of_int r] (qmod int p)"
        unfolding qcong_def using p1 by (simp add: qmod_of_int r_def qmod_mod_absorb)
      have qr: "[of_int r = (of_int r :: rat)] (qmod int p)"
        by (rule qcong_refl) simp
      have "[y - of_int r = of_int r - of_int r] (qmod int p)"
        by (rule qcong_diff[OF qc qr]) (use p1 in simp)
      hence "[y - of_int r = 0] (qmod int p)" by simp
      hence vz: "vge p (y - of_int r) 1" by (rule vge_one_of_qcong_0[OF p])
      have eq: "muMono e - cCorr p e / of_nat p = (y - of_int r) * (1 / of_nat p)"
        unfolding cc y_def using p0 by (simp add: field_simps)
      show ?thesis
        unfolding eq using vge_mul[OF p vz vge_inv_p[OF p]] by simp
    qed
  qed
qed

subsection \<open>Section 3.1 The far-pole constant @{text "C_p"}\<close>


text \<open>Section 3.2: @{text "C_p \<in> p^5 \<int>_p"};
  every partial sum already has valuation @{text "\<ge> 5"}
  (the @{text "k = 0"} term uses @{text "\<Sum>_{a=1}^{p-1} a^{-4} \<equiv> 0 (mod p)"},
    Lean: @{text pt_invPowSum_vge}).\<close>

lemma vge_of_nat: "prime p \<Longrightarrow> vge p (of_nat n) 0"
  using vge_of_int[of p "int n"] by simp

lemma vge_p_self: "prime p \<Longrightarrow> vge p (of_nat p) 1"
proof -
  assume "prime p"
  hence "prime_elem (int p)" by (simp add: prime_nat_int_transfer)
  thus ?thesis by (simp add: vge_def vp_def qmultiplicity_of_nat multiplicity_prime)
qed

lemma vge_dvd_nat: "prime p \<Longrightarrow> p dvd n \<Longrightarrow> vge p (of_nat n) 1"
proof -
  assume p: "prime p" and "p dvd n"
  then obtain t where t: "n = p * t" by (elim dvdE)
  have "vge p (of_nat p * of_nat t) (1 + 0)"
    by (rule vge_mul[OF p vge_p_self[OF p] vge_of_nat[OF p]])
  thus ?thesis by (simp add: t)
qed

lemma vge_inverse_unit: "prime p \<Longrightarrow> \<not> p dvd a \<Longrightarrow>
  vge p (inverse (of_nat a)) 0"
proof -
  assume "prime p" and a: "\<not> p dvd a"
  have "\<not> int p dvd int a" using a by simp
  hence "multiplicity (int p) (int a) = 0" by (rule not_dvd_imp_multiplicity_0)
  thus ?thesis by (simp add: vge_def vp_def qmultiplicity_inverse qmultiplicity_of_nat)
qed

lemma vge_pow4_diff:
  assumes "prime p" "vge p x 0" "vge p y 0" "vge p (x - y) 1"
  shows "vge p (x ^ 4 - y ^ 4) 1"
proof -
  have e: "x ^ 4 - y ^ 4 = (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)"
    by (simp add: algebra_simps power_numeral_reduce)
  have m0: "\<And>u v. vge p u 0 \<Longrightarrow> vge p v 0 \<Longrightarrow> vge p (u * v) 0"
    using vge_mul[OF assms(1), where a = 0 and b = 0] by simp
  have c: "vge p (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) 0"
    using assms(2,3)
    by (intro vge_add[OF assms(1)] m0 vge_pow[OF assms(1)])
  have "vge p ((x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)) (1 + 0)"
    by (rule vge_mul[OF assms(1) assms(4) c])
  thus ?thesis unfolding e by simp
qed

lemma sum_pow4_mod_prime:
  fixes p :: nat
  assumes p: "prime p" "7 \<le> p"
  shows "p dvd (\<Sum> c = 1..p - 1. c ^ 4)"
proof -
  define A where "A = {1..p - 1}"
  define f where "f c = 2 * c mod p" for c
  have p0: "0 < p" using p by simp
  have nd2: "\<not> p dvd 2" using p(2) by (auto dest: dvd_imp_le)
  have cop2: "coprime 2 p" by (rule coprime_commute[THEN iffD1, OF prime_imp_coprime[OF p(1) nd2]])
  have fA: "f ` A \<subseteq> A"
  proof
    fix y assume "y \<in> f ` A"
    then obtain c where c: "c \<in> A" "y = f c" by auto
    have "\<not> p dvd 2 * c"
    proof
      assume "p dvd 2 * c"
      hence "p dvd c" using cop2 by (simp add: coprime_dvd_mult_right_iff coprime_commute)
      moreover have "0 < c" "c < p" using c(1) p0 by (auto simp: A_def)
      ultimately show False by (simp add: nat_dvd_not_less)
    qed
    hence "y \<noteq> 0" using c(2) by (simp add: f_def mod_eq_0_iff_dvd)
    moreover have "y < p" using c(2) p0 by (simp add: f_def)
    ultimately show "y \<in> A" by (auto simp: A_def)
  qed
  have inj: "inj_on f A"
  proof (rule inj_onI)
    fix x y assume xy: "x \<in> A" "y \<in> A" "f x = f y"
    hence "[2 * x = 2 * y] (mod p)" by (simp add: f_def cong_def)
    hence "[x = y] (mod p)" using cop2 by (simp add: cong_mult_lcancel_nat)
    thus "x = y" using xy(1,2) by (auto simp: A_def cong_def)
  qed
  have fAA: "f ` A = A" by (rule endo_inj_surj[OF _ fA inj]) (simp add: A_def)
  define S where "S = (\<Sum> c \<in> A. c ^ 4)"
  have "S = (\<Sum> c \<in> f ` A. c ^ 4)" unfolding fAA S_def ..
  also have "\<dots> = (\<Sum> c \<in> A. f c ^ 4)" by (rule sum.reindex[OF inj, unfolded o_def])
  finally have S1: "S = (\<Sum> c \<in> A. f c ^ 4)" .
  have "[(\<Sum> c \<in> A. f c ^ 4) = (\<Sum> c \<in> A. (2 * c) ^ 4)] (mod p)"
    by (rule cong_sum, rule cong_pow) (simp add: f_def cong_def)
  also have "(\<Sum> c \<in> A. (2 * c) ^ 4) = 16 * S"
    by (simp add: S_def sum_distrib_left power_mult_distrib)
  finally have "[16 * S = S] (mod p)" using S1 by (simp add: cong_sym_eq)
  hence "p dvd 16 * S - S" by (subst cong_altdef_nat[symmetric]) simp_all
  hence "p dvd 15 * S" by simp
  hence "p dvd 15 \<or> p dvd S" using p(1) by (simp add: prime_dvd_mult_iff)
  moreover have "\<not> p dvd 15"
  proof
    assume "p dvd 15"
    hence "p dvd 3 * 5" by simp
    hence "p dvd 3 \<or> p dvd 5" using p(1) by (simp only: prime_dvd_mult_iff)
    thus False using p(2) by (auto dest: dvd_imp_le)
  qed
  ultimately show ?thesis by (simp add: S_def A_def)
qed

lemma invPowSum_vge: "prime p \<Longrightarrow> 7 \<le> p \<Longrightarrow>
  vge p (\<Sum> a = 1..p - 1. inverse (of_nat a) ^ 4) 1"
proof -
  assume p: "prime p" and p7: "7 \<le> p"
  define A where "A = {1..p - 1}"
  have p0: "0 < p" using p7 by simp
  have ex: "\<exists>b. b \<in> A \<and> [a * b = 1] (mod p)" if a: "a \<in> A" for a
  proof -
    have "coprime p 1" by simp
    moreover have "0 < a" "a < p" using a p0 by (auto simp: A_def)
    ultimately obtain y where y: "0 < y \<and> y < p \<and> [a * y = 1] (mod p)"
      using cong_solve_unique_nontrivial[OF p] by blast
    show ?thesis using y by (intro exI[of _ y]) (auto simp: A_def)
  qed
  define bf where "bf a = (SOME b. b \<in> A \<and> [a * b = 1] (mod p))" for a
  have bf: "bf a \<in> A" "[a * bf a = 1] (mod p)" if "a \<in> A" for a
    using someI_ex[OF ex[OF that]] unfolding bf_def by auto
  have ndvd: "\<not> p dvd a" if "a \<in> A" for a
    using that p0 by (auto simp: A_def dest: dvd_imp_le)
  have inj: "inj_on bf A"
  proof (rule inj_onI)
    fix x y assume xy: "x \<in> A" "y \<in> A" "bf x = bf y"
    have "[x * bf x = y * bf x] (mod p)" using bf(2)[OF xy(1)] bf(2)[OF xy(2)] xy(3)
      by (metis cong_sym cong_trans)
    moreover have "coprime (bf x) p" using ndvd[OF bf(1)[OF xy(1)]] p
      by (simp add: prime_imp_coprime coprime_commute)
    ultimately have "[x = y] (mod p)" by (simp add: cong_mult_rcancel_nat)
    thus "x = y" using xy(1,2) by (auto simp: A_def cong_def)
  qed
  have bAA: "bf ` A = A" by (rule endo_inj_surj) (use bf(1) inj in \<open>auto simp: A_def\<close>)
  have diff: "vge p (inverse (of_nat a) ^ 4 - of_nat (bf a) ^ 4) 1" if a: "a \<in> A" for a
  proof -
    have a0: "a \<noteq> 0" using a by (auto simp: A_def)
    have abf_pos: "1 \<le> a * bf a" using a0 bf(1)[OF a] by (auto simp: A_def)
    have "p dvd a * bf a - 1" using bf(2)[OF a] abf_pos by (simp add: cong_altdef_nat)
    hence v1: "vge p (- of_nat (a * bf a - 1)) 1" by (intro vge_neg vge_dvd_nat[OF p])
    have "vge p (- of_nat (a * bf a - 1) * inverse (of_nat a)) (1 + 0)"
      by (rule vge_mul[OF p v1 vge_inverse_unit[OF p ndvd[OF a]]])
    moreover have "- of_nat (a * bf a - 1) * inverse (of_nat a) =
      inverse (of_nat a) - (of_nat (bf a) :: rat)"
      using a0 abf_pos by (simp add: of_nat_diff field_simps)
    ultimately have "vge p (inverse (of_nat a) - of_nat (bf a)) 1" by simp
    thus ?thesis
      by (intro vge_pow4_diff[OF p vge_inverse_unit[OF p ndvd[OF a]] vge_of_nat[OF p]])
  qed
  have "(\<Sum> a \<in> A. of_nat (bf a) ^ 4 :: rat) = (\<Sum> c \<in> bf ` A. of_nat c ^ 4)"
    by (rule sum.reindex[OF inj, unfolded o_def, symmetric])
  also have "\<dots> = of_nat (\<Sum> c \<in> A. c ^ 4)" unfolding bAA by simp
  finally have sb: "(\<Sum> a \<in> A. of_nat (bf a) ^ 4 :: rat) = of_nat (\<Sum> c \<in>
    A. c ^ 4)" .
  have v2: "vge p (\<Sum> a \<in> A. of_nat (bf a) ^ 4 :: rat) 1"
    unfolding sb unfolding A_def by (rule vge_dvd_nat[OF p sum_pow4_mod_prime[OF p p7]])
  have v1: "vge p (\<Sum> a \<in> A. inverse (of_nat a) ^ 4 - of_nat (bf a) ^ 4) 1"
    by (rule vge_sum[OF p]) (use diff in \<open>simp_all add: A_def\<close>)
  have "vge p ((\<Sum> a \<in> A. inverse (of_nat a) ^ 4 - of_nat (bf a) ^ 4) + (\<Sum> a \<in>
    A. of_nat (bf a) ^ 4)) 1"
    by (rule vge_add[OF p v1 v2])
  thus ?thesis by (simp add: sum_subtractf A_def)
qed

lemma vge_p_pow: "prime p \<Longrightarrow> vge p (of_nat p ^ n) (of_nat n)"
proof -
  assume p: "prime p"
  have "qmultiplicity (int p) (of_nat p powi int n) = int n" by (rule qmultiplicity_power_int[OF p])
  thus ?thesis by (simp add: vge_def vp_def power_int_of_nat)
qed

lemma vge_small_unit:
  assumes "prime p" "7 \<le> p" "0 < c" "c < 7"
  shows "vge p (inverse (of_nat c)) 0"
  by (rule vge_inverse_unit[OF assms(1)]) (use assms in \<open>auto dest: dvd_imp_le\<close>)

lemma powi_neg_frac:
  assumes "a \<noteq> 0" "p \<noteq> 0"
  shows "(- of_nat a / of_nat p :: rat) powi (- (int k + 4))
           = (- 1) ^ (k + 4) * of_nat p ^ (k + 4) * inverse (of_nat a) ^ (k + 4)"
proof -
  have "- (int k + 4) = - int (k + 4)" by simp
  hence "(- of_nat a / of_nat p :: rat) powi (- (int k + 4)) =
    inverse ((- of_nat a / of_nat p) ^ (k + 4))"
    by (simp only: power_int_minus power_int_of_nat)
  also have "\<dots> = (- (of_nat p / of_nat a)) ^ (k + 4)"
    by (simp add: power_inverse[symmetric])
  also have "\<dots> = (- 1) ^ (k + 4) * of_nat p ^ (k + 4) * inverse (of_nat a) ^ (k + 4)"
    by (simp add: power_minus' power_divide divide_inverse power_mult_distrib power_inverse)
  finally show ?thesis .
qed

lemma Cp_tr_vge: "prime p \<Longrightarrow> 7 \<le> p \<Longrightarrow> vge p (Cp_tr p M) 5"
proof -
  assume p: "prime p" and p7: "7 \<le> p"
  define A where "A = {1..p - 1}"
  have p0: "p \<noteq> 0" using p7 by simp
  have ndvd: "\<not> p dvd a" if "a \<in> A" for a
    using that p7 by (auto simp: A_def dest: dvd_imp_le)
  define I where "I n = (\<Sum> a \<in> A. inverse (of_nat a :: rat) ^ n)" for n
  have I0: "vge p (I n) 0" for n
    unfolding I_def
  proof (rule vge_sum[OF p])
    fix a assume "a \<in> A"
    thus "vge p (inverse (of_nat a) ^ n) 0" by (intro vge_pow[OF p] vge_inverse_unit[OF p] ndvd)
  qed (simp add: A_def)
  have I4: "vge p (I 4) 1" unfolding I_def A_def by (rule invPowSum_vge[OF p p7])
  have u2: "vge p (inverse (of_nat 2)) 0" by (rule vge_small_unit[OF p p7]) simp_all
  have u4: "vge p (inverse (of_nat 4)) 0" by (rule vge_small_unit[OF p p7]) simp_all
  have mul: "\<And>x y b c. vge p x b \<Longrightarrow> vge p y c \<Longrightarrow>
    vge p (x * y) (b + c)" by (rule vge_mul[OF p])
  have sgn: "vge p ((- 1) ^ n) 0" for n by (rule vge_pow[OF p]) (rule vge_neg[OF vge_one])
  define T where "T k = of_nat ((k + 3) choose 3) * bernoulli k * ((- 1) ^ (k + 4) * of_nat p ^ (k +
    4) * I (k + 4))" for k
  have swap: "Cp_tr p M = - (1 / 4) * (\<Sum> k < M. T k)"
  proof -
    have "Cp_tr p M = (\<Sum> a \<in> A. - (1 / 4) * (\<Sum> k <
      M. of_nat ((k + 3) choose 3) * bernoulli k *
                         ((- 1) ^ (k + 4) * of_nat p ^ (k + 4) * inverse (of_nat a) ^ (k + 4))))"
      unfolding Cp_tr_def tauAnPole_tr_def A_def
    proof (rule sum.cong[OF refl])
      fix a assume a: "a \<in> {1..p - 1}"
      have a0': "a \<noteq> 0" using a by simp
      show "- (1 / 4) * (\<Sum> k < M. of_nat ((k + 3) choose 3) * (bernoulli k :: rat) *
        (- of_nat a / of_nat p) powi (- (int k + 4)))
          = - (1 / 4) * (\<Sum> k < M. of_nat ((k + 3) choose 3) * bernoulli k *
                         ((- 1) ^ (k + 4) * of_nat p ^ (k + 4) * inverse (of_nat a) ^ (k + 4)))"
        by (simp only: powi_neg_frac[OF a0' p0])
    qed
    also have "\<dots> = - (1 / 4) * (\<Sum> k < M. T k)"
      unfolding T_def I_def
      by (simp add: sum_distrib_left sum_distrib_right sum.swap[of _ A] mult_ac)
    finally show ?thesis .
  qed
  have Tk: "vge p (T k) 5" for k
  proof -
    have C: "vge p (of_nat ((k + 3) choose 3)) 0" by (rule vge_of_nat[OF p])
    have Pn: "vge p (of_nat p ^ (k + 4)) (of_nat (k + 4))" by (rule vge_p_pow[OF p])
    consider "k = 0" | "k = 1" | "2 \<le> k" by arith
    thus ?thesis
    proof cases
      case 1
      have Ik: "vge p (I (k + 4)) 1" using I4 1 by simp
      have B0: "vge p (bernoulli k) 0" using 1 by (simp add: bernoulli_0 vge_one)
      have "vge p (T k) (0 + 0 + (0 + of_nat (k + 4) + 1))"
        unfolding T_def by (intro mul C B0 sgn Pn Ik)
      thus ?thesis using 1 by simp
    next
      case 2
      have be: "bernoulli k = - inverse (of_nat 2)" unfolding 2 bernoulli_1 by simp
      have B: "vge p (bernoulli k) 0" unfolding be by (rule vge_neg[OF u2])
      have "vge p (T k) (0 + 0 + (0 + of_nat (k + 4) + 0))"
        unfolding T_def by (intro mul C B sgn Pn I0)
      thus ?thesis using 2 by simp
    next
      case 3
      have B: "vge p (bernoulli k) (- 1)"
        unfolding vge_def
      proof
        assume "(bernoulli k :: rat) \<noteq> 0"
        hence "- 1 \<le> vp p (bernoulli k)" by (rule vp_bernoulli_ge[OF p])
        thus "- 1 \<le> (of_int (vp p (bernoulli k)) :: rat)"
          by (metis of_int_le_iff of_int_minus of_int_1)
      qed
      have v: "vge p (T k) (0 + - 1 + (0 + of_nat (k + 4) + 0))"
        unfolding T_def by (intro mul C B sgn Pn I0)
      show ?thesis by (rule vge_mono[OF v]) (use 3 in simp)
    qed
  qed
  have "vge p (- (1 / 4) * (\<Sum> k < M. T k)) (0 + 5)"
  proof (rule mul)
    have "- (1 / 4) = - inverse (of_nat 4 :: rat)" by simp
    thus "vge p (- (1 / 4)) 0" using vge_neg[OF u4] by (simp only:)
    show "vge p (\<Sum> k < M. T k) 5" by (rule vge_sum[OF p]) (simp_all add: Tk)
  qed
  thus ?thesis unfolding swap by simp
qed


subsection \<open>Section 3.3 Lemma 3.3 and the small-prime bound\<close>

text \<open>Lemma 3.3, (3.10): if @{text A} is integer-valued with @{text "deg A \<le> d"} and
  @{text "g = (K!)^2 A(x)/\<Prod>_{0<|r|\<le>K}(x - r)"}, then
  @{text "v_p^G(\<tau>_X(g)) \<ge> -6\<lfloor>log_p max(2K, d+1)\<rfloor> - v_p(24)"}.  Proof: the
    residues are
  @{text "\<plusminus>(K!)^2 r A(r)/((K+r)!(K-r)!)"}, root counting modulo @{text "p^j"},
    two-case estimate.\<close>
lemma vge_diff: "prime p \<Longrightarrow> vge p x b \<Longrightarrow> vge p y b \<Longrightarrow>
  vge p (x - y) b"
  using vge_add[of p x b "- y"] vge_neg[of p y b] by simp

subsection \<open>Counting multiples in an interval\<close>

text \<open>At most @{text "2K div q + 1"} elements of @{text "[-K, K]"} lie in one residue class
  modulo @{text q}.\<close>
lemma card_filter_dvd_Icc_le:
  assumes "0 < q"
  shows "card {s \<in> {- int K..int K}. int q dvd (x - s)} \<le> 2 * K div q + 1"
proof -
  let ?C = "{s \<in> {- int K..int K}. int q dvd (x - s)}"
  let ?f = "\<lambda>s. (s + int K) div int q"
  have inj: "inj_on ?f ?C"
  proof (rule inj_onI)
    fix s t assume s: "s \<in> ?C" and t: "t \<in> ?C" and e: "?f s = ?f t"
    have "int q dvd (x - t) - (x - s)" by (rule dvd_diff) (use s t in simp_all)
    hence "int q dvd (s + int K) - (t + int K)" by (simp add: algebra_simps)
    hence m: "(s + int K) mod int q = (t + int K) mod int q" by (simp only: mod_eq_dvd_iff)
    have "s + int K = (t + int K)"
      by (metis e m div_mult_mod_eq)
    thus "s = t" by simp
  qed
  have sub: "?f ` ?C \<subseteq> {0..int (2 * K div q)}"
  proof
    fix z assume "z \<in> ?f ` ?C"
    then obtain s where s: "s \<in> ?C" and z: "z = ?f s" by blast
    have "0 \<le> z" using s assms unfolding z by (simp add: pos_imp_zdiv_nonneg_iff)
    moreover have "z \<le> int (2 * K) div int q" unfolding z
      by (rule zdiv_mono1) (use s assms in auto)
    ultimately show "z \<in> {0..int (2 * K div q)}" by (simp add: zdiv_int)
  qed
  have "card ?C = card (?f ` ?C)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card {0..int (2 * K div q)}" by (rule card_mono[OF _ sub]) simp
  also have "\<dots> = 2 * K div q + 1" by simp
  finally show ?thesis .
qed

lemma two_mul_div_le_nat: "0 < q \<Longrightarrow> 2 * K div q \<le> 2 * (K div q) + (1::nat)"
proof -
  assume q: "0 < q"
  have K: "K = K div q * q + K mod q" by simp
  have "K mod q < q" using q by simp
  hence "2 * K < 2 * (K div q * q) + 2 * q" using K by linarith
  hence "2 * K < (2 * (K div q) + 2) * q" by (simp add: algebra_simps)
  hence "2 * K div q < 2 * (K div q) + 2" using div_less_iff_less_mult[OF q] by blast
  thus ?thesis by simp
qed
lemma card_filter_dvd_le:
  "0 < q \<Longrightarrow> T \<subseteq> {- int K..int K} \<Longrightarrow>
    card {s \<in> T. int q dvd (x - s)} \<le> 2 * K div q + 1"
proof -
  assume q: "0 < q" and T: "T \<subseteq> {- int K..int K}"
  have fC: "finite {s \<in> {- int K..int K}. int q dvd (x - s)}"
    by (rule finite_subset[of _ "{- int K..int K}"]) auto
  have "card {s \<in> T. int q dvd (x - s)} \<le> card {s \<in>
    {- int K..int K}. int q dvd (x - s)}"
    by (rule card_mono[OF fC]) (use T in auto)
  also have "\<dots> \<le> 2 * K div q + 1" by (rule card_filter_dvd_Icc_le[OF q])
  finally show ?thesis .
qed

text \<open>If @{text "x0 \<in> [-K, K] - T"} lies in the residue class, the count drops
  by one.\<close>
lemma card_filter_dvd_le_excl:
  "0 < q \<Longrightarrow> T \<subseteq> {- int K..int K} \<Longrightarrow>
    x0 \<in> {- int K..int K} \<Longrightarrow> x0 \<notin> T \<Longrightarrow>
    int q dvd (x - x0) \<Longrightarrow>
   card {s \<in> T. int q dvd (x - s)} \<le> 2 * K div q"
proof -
  assume q: "0 < q" and T: "T \<subseteq> {- int K..int K}" and x0: "x0 \<in>
    {- int K..int K}" "x0 \<notin> T"
    and d: "int q dvd (x - x0)"
  have fin: "finite {s \<in> T. int q dvd (x - s)}"
    by (rule finite_subset[of _ "{- int K..int K}"]) (use T in auto)
  have fC: "finite {s \<in> {- int K..int K}. int q dvd (x - s)}"
    by (rule finite_subset[of _ "{- int K..int K}"]) auto
  have "card (insert x0 {s \<in> T. int q dvd (x - s)}) = Suc (card {s \<in> T. int q dvd (x - s)})"
    using fin x0(2) by simp
  moreover have "card (insert x0 {s \<in> T. int q dvd (x - s)}) \<le> card {s \<in>
    {- int K..int K}. int q dvd (x - s)}"
    by (rule card_mono[OF fC]) (use T x0 d in auto)
  moreover have "card {s \<in> {- int K..int K}. int q dvd (x - s)} \<le> 2 * K div q + 1"
    by (rule card_filter_dvd_Icc_le[OF q])
  ultimately show ?thesis by linarith
qed

lemma lt_pow_nat_log_succ: "prime p \<Longrightarrow> 0 < n \<Longrightarrow>
  n < p ^ (nat_log p n + 1)"
proof -
  assume p: "prime p" and n: "0 < n"
  have b: "1 < p" using p by (rule prime_gt_1_nat)
  have "floorlog p n \<noteq> 0" using b n by (simp add: floorlog_eq_zero_iff)
  hence "nat_log p n + 1 = floorlog p n" by (simp add: nat_log_def)
  thus ?thesis using floorlog_bounds[OF n b] by simp
qed

lemma div_eq_zero_of_gt_nat_log: "prime p \<Longrightarrow> nat_log p (2 * K) < j \<Longrightarrow>
  2 * K div p ^ j = 0"
proof -
  assume p: "prime p" and j: "nat_log p (2 * K) < j"
  show ?thesis
  proof (cases "K = 0")
    case False
    have "2 * K < p ^ (nat_log p (2 * K) + 1)" using False by (intro lt_pow_nat_log_succ[OF p]) simp
    also have "\<dots> \<le> p ^ j" using j prime_gt_1_nat[OF p]
      by (intro power_increasing) simp_all
    finally show ?thesis by simp
  qed simp
qed

subsection \<open>Valuations of integers as counts\<close>

lemma multiplicity_int_eq_card:
  assumes "prime p" "z \<noteq> 0" "multiplicity (int p) z < B"
  shows "multiplicity (int p) z = card {j \<in> {1..<B}. int p ^ j dvd z}"
proof -
  have "prime (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  hence pu: "\<not> is_unit (int p)" by (metis not_prime_unit)
  have "{j \<in> {1..<B}. int p ^ j dvd z} = {1..multiplicity (int p) z}"
    using assms(3) by (auto simp: power_dvd_iff_le_multiplicity[OF assms(2) pu])
  thus ?thesis by simp
qed

lemma sum_multiplicity_le:
  assumes "prime p" "finite T" "\<And>s. s \<in> T \<Longrightarrow> x - s \<noteq> 0"
    and "\<And>s. s \<in> T \<Longrightarrow> multiplicity (int p) (x - s) < B"
    and "\<And>j. j \<in> {1..<B} \<Longrightarrow>
      card {s \<in> T. int p ^ j dvd (x - s)} \<le> c j"
  shows "(\<Sum> s \<in> T. multiplicity (int p) (x - s)) \<le> (\<Sum> j \<in> {1..<B}. c j)"
proof -
  have cs: "card {y \<in> A. Q y} = (\<Sum> y \<in> A. if Q y then 1 else 0)" if "finite A"
    for A :: "'b set" and Q
    by (simp only: card_eq_sum sum.inter_filter[OF that])
  have "(\<Sum> s \<in> T. multiplicity (int p) (x - s))
      = (\<Sum> s \<in> T. \<Sum> j \<in> {1..<B}. if int p ^ j dvd (x - s) then 1 else 0)"
  proof (rule sum.cong[OF refl])
    fix s assume s: "s \<in> T"
    have "multiplicity (int p) (x - s) = card {j \<in> {1..<B}. int p ^ j dvd (x - s)}"
      by (rule multiplicity_int_eq_card[OF assms(1) assms(3)[OF s] assms(4)[OF s]])
    also have "\<dots> = (\<Sum> j \<in> {1..<B}. if int p ^ j dvd (x - s) then 1 else 0)"
      by (rule cs) simp
    finally show "multiplicity (int p) (x - s) = (\<Sum> j \<in> {1..<B}.
      if int p ^ j dvd (x - s) then 1 else 0)" .
  qed
  also have "\<dots> = (\<Sum> j \<in> {1..<B}. \<Sum> s \<in> T.
    if int p ^ j dvd (x - s) then 1 else 0)" by (rule sum.swap)
  also have "\<dots> = (\<Sum> j \<in> {1..<B}. card {s \<in> T. int p ^ j dvd (x - s)})"
    by (rule sum.cong[OF refl]) (rule cs[OF assms(2), symmetric])
  also have "\<dots> \<le> (\<Sum> j \<in> {1..<B}. c j)" by (rule sum_mono) (rule assms(5))
  finally show ?thesis .
qed

text \<open>The factorial ratio @{text "(K!)^2 / \<Prod>_{s\<in>T} (x - s)"},
  from per-level counts: if at each level @{text j}
  at most @{text "2\<lfloor>K/p^j\<rfloor> + e [j \<le> L0]"} of the @{text "x - s"} are divisible
    by @{text "p^j"}, the ratio has
  @{text "v_p \<ge> -e L0"}, where @{text "L0 = \<lfloor>log_p 2K\<rfloor>"}.\<close>
lemma vge_factorial_sq_div_prod:
  assumes p: "prime p" and T: "finite T" and x: "\<And>s. s \<in> T \<Longrightarrow>
    x - s \<noteq> 0"
    and hc: "\<And>j. 1 \<le> j \<Longrightarrow> card {s \<in> T. int p ^ j dvd (x - s)} \<le>
                2 * (K div p ^ j) + (if j \<le> nat_log p (2 * K) then e else 0)"
  shows "vge p (fact K ^ 2 / (\<Prod> s \<in>
    T. of_int x - of_int s)) (- of_nat (e * nat_log p (2 * K)))"
proof -
  define L0 where "L0 = nat_log p (2 * K)"
  define B where "B = (\<Sum> s \<in> T. multiplicity (int p) (x - s)) + L0 + K + 1"
  have hB: "\<And>s. s \<in> T \<Longrightarrow> multiplicity (int p) (x - s) < B"
  proof -
    fix s assume s: "s \<in> T"
    have "multiplicity (int p) (x - s) \<le> (\<Sum> s \<in> T. multiplicity (int p) (x - s))"
      by (rule member_le_sum[OF s _ T]) simp
    thus "multiplicity (int p) (x - s) < B" by (simp add: B_def)
  qed
  have hsum: "(\<Sum> s \<in> T. multiplicity (int p) (x - s)) \<le>
    2 * multiplicity p (fact K) + L0 * e"
  proof -
    define c where "c j = 2 * (K div p ^ j) + (if j \<le> L0 then e else 0)" for j
    have B1: "1 \<le> B" by (simp add: B_def)
    have leg: "(\<Sum> j \<in> {1..<B}. K div p ^ j) = multiplicity p (fact K)"
    proof -
      have "{1..<B} = {1..B - 1}" using B1 by auto
      moreover have "K \<le> B - 1" by (simp add: B_def)
      ultimately show ?thesis using legendre_sum[OF p, of K "B - 1"] by simp
    qed
    have cnt: "(\<Sum> j \<in> {1..<B}. if j \<le> L0 then e else 0) = L0 * e"
    proof -
      have "(\<Sum> j \<in> {1..<B}. if j \<le> L0 then e else 0) = (\<Sum> j \<in> {j \<in>
        {1..<B}. j \<le> L0}. e)"
        by (rule sum.inter_filter[symmetric]) simp
      also have "{j \<in> {1..<B}. j \<le> L0} = {1..L0}" by (auto simp: B_def)
      finally show ?thesis by simp
    qed
    have "(\<Sum> s \<in> T. multiplicity (int p) (x - s)) \<le> (\<Sum> j \<in> {1..<B}. c j)"
      by (rule sum_multiplicity_le[OF p T x hB]) (use hc in \<open>auto simp: c_def L0_def\<close>)
    also have "\<dots> = 2 * (\<Sum> j \<in> {1..<B}. K div p ^ j) + (\<Sum> j \<in> {1..<B}.
      if j \<le> L0 then e else 0)"
      by (simp add: c_def sum.distrib sum_distrib_left)
    also have "\<dots> = 2 * multiplicity p (fact K) + L0 * e" by (simp only: leg cnt)
    finally show ?thesis .
  qed
  have prod_ne: "(\<Prod> s \<in> T. of_int x - of_int s :: rat) \<noteq> 0"
    using T x by (auto simp: prod_zero_iff)
  have vprod: "vp p (\<Prod> s \<in> T. of_int x - of_int s) = (\<Sum> s \<in>
    T. int (multiplicity (int p) (x - s)))"
  proof -
    have "vp p (\<Prod> s \<in> T. of_int x - of_int s) = (\<Sum> s \<in>
      T. vp p (of_int x - of_int s))"
      by (rule vp_prod_rat[OF p T]) (use x in auto)
    also have "\<dots> = (\<Sum> s \<in> T. int (multiplicity (int p) (x - s)))"
      by (rule sum.cong[OF refl]) (simp add: vp_def qmultiplicity_of_int flip: of_int_diff)
    finally show ?thesis .
  qed
  have vfact: "vp p (fact K ^ 2) = 2 * int (multiplicity p (fact K))"
  proof -
    have "vp p (fact K :: rat) = qmultiplicity (int p) (of_nat (fact K))" by (simp add: vp_def)
    also have "\<dots> = int (multiplicity (int p) (int (fact K)))" by (rule qmultiplicity_of_nat)
    also have "\<dots> = int (multiplicity p (fact K))" by (simp only: multiplicity_int)
    finally have vf: "vp p (fact K :: rat) = int (multiplicity p (fact K))" .
    show ?thesis by (simp add: vp_power_rat[OF p] vf)
  qed
  have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer prime_imp_prime_elem)
  have "vp p (fact K ^ 2 / (\<Prod> s \<in> T. of_int x - of_int s)) =
    vp p (fact K ^ 2) - vp p (\<Prod> s \<in> T. of_int x - of_int s)"
    unfolding vp_def by (rule qmultiplicity_divide[OF pe _ prod_ne]) simp
  hence vq: "vp p (fact K ^ 2 / (\<Prod> s \<in> T. of_int x - of_int s))
      = 2 * int (multiplicity p (fact K)) - (\<Sum> s \<in> T. int (multiplicity (int p) (x - s)))"
    using vprod vfact by simp
  have "int (\<Sum> s \<in> T. multiplicity (int p) (x - s)) \<le>
    int (2 * multiplicity p (fact K) + L0 * e)"
    using hsum by (simp only: of_nat_le_iff)
  hence "(\<Sum> s \<in> T. int (multiplicity (int p) (x - s))) \<le>
    2 * int (multiplicity p (fact K)) + int L0 * int e"
    by simp
  with vq have "- (int L0 * int e) \<le> vp p (fact K ^ 2 / (\<Prod> s \<in>
    T. of_int x - of_int s))" by linarith
  hence "(of_int (- (int L0 * int e)) :: rat) \<le> of_int (vp p (fact K ^ 2 / (\<Prod> s \<in>
    T. of_int x - of_int s)))"
    by (simp only: of_int_le_iff)
  thus ?thesis unfolding vge_def by (simp add: L0_def mult.commute)
qed

subsection \<open>Partial fractions with linear poles\<close>

lemma degree_div_le_self:
  fixes G M :: "rat poly"
  assumes "M \<noteq> 0"
  shows "degree (G div M) \<le> degree G"
proof (cases "G div M = 0")
  case True
  thus ?thesis by simp
next
  case False
  have dm: "degree (M * (G div M)) = degree M + degree (G div M)" using assms False
    by (rule degree_mult_eq)
  have "G mod M = 0 \<or> degree (G mod M) < degree (M * (G div M))"
    using degree_mod_less[OF assms, of G] dm by auto
  hence "degree (M * (G div M) + G mod M) = degree (M * (G div M))"
  proof
    assume "G mod M = 0"
    thus ?thesis by (simp only: add_0_right)
  next
    assume "degree (G mod M) < degree (M * (G div M))"
    thus ?thesis by (rule degree_add_eq_left)
  qed
  hence "degree G = degree M + degree (G div M)" using dm by simp
  thus ?thesis by simp
qed
lemma linPoleProd_eq_qPoleProd: "linPoleProd S = qPoleProd (of_int ` S)"
  unfolding linPoleProd_def qPoleProd_def by (subst prod.reindex) (auto simp: inj_on_def)

lemma degree_linPoleProd: "finite S \<Longrightarrow> degree (linPoleProd S) = card S"
proof -
  assume S: "finite S"
  have "inj_on (of_int :: int \<Rightarrow> rat) S" by (simp add: inj_on_def)
  thus ?thesis using S by (simp add: linPoleProd_eq_qPoleProd degree_qPoleProd card_image)
qed

lemma lead_coeff_linPoleProd: "finite S \<Longrightarrow> lead_coeff (linPoleProd S) = 1"
  by (simp add: linPoleProd_eq_qPoleProd qPoleProd_monic)

lemma linPoleProd_nonzero: "finite S \<Longrightarrow> linPoleProd S \<noteq> 0"
  using lead_coeff_linPoleProd[of S] by auto

lemma poly_linPoleProd: "poly (linPoleProd S) y = (\<Prod> r \<in> S. y - of_int r)"
  unfolding linPoleProd_def poly_prod by (simp add: poly_monom)

text \<open>Lagrange: @{text "P mod \<Prod>_{r\<in>S}(x - r) = \<Sum>_r res_r \<Prod>_{s \<noteq>
  r} (x - s)"}.\<close>
lemma mod_linPoleProd:
  assumes "finite S"
  shows "P mod linPoleProd S = (\<Sum> r \<in> S. [:linResidue S P r:] * linPoleProd (S - {r}))"
proof -
  define S' where "S' = (of_int ` S :: rat set)"
  have inj: "inj_on (of_int :: int \<Rightarrow> rat) X" for X by (simp add: inj_on_def)
  have fin': "finite S'" using assms by (simp add: S'_def)
  have Pi: "linPoleProd S = qPoleProd S'" by (simp add: S'_def linPoleProd_eq_qPoleProd)
  have L: "P = linPoleProd S * (P div linPoleProd S) + (\<Sum>s\<in>S'. [:qRes S' P s:] *
    qPoleProd (S' - {s}))"
    unfolding Pi by (rule lagrange_decomp[OF fin'])
  have R: "(\<Sum>s\<in>S'. [:qRes S' P s:] * qPoleProd (S' - {s}))
      = (\<Sum> r \<in> S. [:linResidue S P r:] * linPoleProd (S - {r}))"
  proof -
    have "(\<Sum>s\<in>S'. [:qRes S' P s:] * qPoleProd (S' - {s}))
        = (\<Sum> r \<in> S. [:qRes S' P (of_int r):] * qPoleProd (S' - {of_int r}))"
      unfolding S'_def by (subst sum.reindex[OF inj]) simp
    also have "\<dots> = (\<Sum> r \<in> S. [:linResidue S P r:] * linPoleProd (S - {r}))"
    proof (rule sum.cong[OF refl])
      fix r assume r: "r \<in> S"
      have e: "S' - {of_int r} = of_int ` (S - {r})" by (auto simp: S'_def)
      have "qRes S' P (of_int r) = linResidue S P r"
        unfolding qRes_def linResidue_def e by (subst prod.reindex[OF inj]) (simp add: o_def)
      moreover have "qPoleProd (S' - {of_int r}) = linPoleProd (S - {r})"
        unfolding e by (simp add: linPoleProd_eq_qPoleProd)
      ultimately show "[:qRes S' P (of_int r):] * qPoleProd (S' - {of_int r}) =
        [:linResidue S P r:] * linPoleProd (S - {r})"
        by simp
    qed
    finally show ?thesis .
  qed
  have "linPoleProd S * (P div linPoleProd S) + P mod linPoleProd S
      = linPoleProd S * (P div linPoleProd S) + (\<Sum>s\<in>S'. [:qRes S' P s:] * qPoleProd (S' -
        {s}))"
    by (subst mult_div_mod_eq) (rule L)
  hence "P mod linPoleProd S = (\<Sum>s\<in>S'. [:qRes S' P s:] * qPoleProd (S' - {s}))"
    by (simp only: add_left_cancel)
  thus ?thesis using R by simp
qed

text \<open>Evaluating the partial-fraction decomposition away from the poles.\<close>
lemma poly_div_linPoleProd:
  assumes "finite S" "\<And>r. r \<in> S \<Longrightarrow> y - of_int r \<noteq> 0"
  shows "poly (P div linPoleProd S) y =
         poly P y / (\<Prod> r \<in> S. y - of_int r) - (\<Sum> r \<in>
           S. linResidue S P r / (y - of_int r))"
proof -
  define D where "D = (\<Prod> r \<in> S. y - of_int r)"
  have D0: "D \<noteq> 0" using assms by (simp add: D_def prod_zero_iff)
  have rem: "(\<Prod> s \<in> S - {r}. y - of_int s) = D / (y - of_int r)" if r: "r \<in> S" for r
  proof -
    have eq: "D = (y - of_int r) * (\<Prod> s \<in> S - {r}. y - of_int s)" unfolding D_def
      by (rule prod.remove[OF assms(1) r])
    show ?thesis unfolding eq using assms(2)[OF r] by simp
  qed
  have "poly P y = poly (linPoleProd S * (P div linPoleProd S) + P mod linPoleProd S) y" by simp
  also have "\<dots> = D * poly (P div linPoleProd S) y + (\<Sum> r \<in>
    S. linResidue S P r * (\<Prod> s \<in> S - {r}. y - of_int s))"
    by (simp add: mod_linPoleProd[OF assms(1)] poly_linPoleProd poly_sum D_def)
  also have "(\<Sum> r \<in> S. linResidue S P r * (\<Prod> s \<in> S - {r}. y - of_int s)) =
    D * (\<Sum> r \<in> S. linResidue S P r / (y - of_int r))"
    unfolding sum_distrib_left by (rule sum.cong[OF refl]) (simp add: rem)
  finally have "poly P y = D * (poly (P div linPoleProd S) y + (\<Sum> r \<in>
    S. linResidue S P r / (y - of_int r)))"
    by (simp add: distrib_left)
  hence "poly (P div linPoleProd S) y + (\<Sum> r \<in> S. linResidue S P r / (y - of_int r)) =
    poly P y / D"
    using D0 by (simp add: eq_divide_eq mult.commute)
  thus ?thesis unfolding D_def[symmetric] by (simp add: algebra_simps)
qed

subsection \<open>Valuations of integers\<close>

lemma vp_int_le_nat_log:
  "prime p \<Longrightarrow> z \<noteq> 0 \<Longrightarrow>
    nat \<bar>z\<bar> \<le> M \<Longrightarrow> vp p (of_int z) \<le> int (nat_log p M)"
proof -
  assume p: "prime p" and z: "z \<noteq> 0" and M: "nat \<bar>z\<bar> \<le> M"
  let ?m = "multiplicity (int p) z"
  have "int p ^ ?m dvd z" by (rule multiplicity_dvd)
  hence "\<bar>int p ^ ?m\<bar> \<le> \<bar>z\<bar>" by (rule dvd_imp_le_int[OF z])
  hence "int p ^ ?m \<le> \<bar>z\<bar>" by simp
  also have "\<dots> \<le> int M" using M by (simp only: nat_le_iff)
  finally have "int p ^ ?m \<le> int M" .
  hence "int (p ^ ?m) \<le> int M" by (simp only: of_nat_power)
  hence "p ^ (Suc ?m - 1) \<le> M" by (simp only: of_nat_le_iff diff_Suc_1)
  hence "Suc ?m \<le> floorlog p M" by (rule floorlog_geI) (rule prime_gt_1_nat[OF p])
  thus ?thesis by (simp add: vp_def qmultiplicity_of_int nat_log_def)
qed

lemma lt_vp_of_dvd:
  "prime p \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> int p ^ (k + 1) dvd z \<Longrightarrow>
    int k < vp p (of_int z)"
proof -
  assume p: "prime p" and z: "z \<noteq> 0" and d: "int p ^ (k + 1) dvd z"
  have "prime (int p)" using p by (simp add: prime_nat_int_transfer)
  hence pu: "\<not> is_unit (int p)" by (metis not_prime_unit)
  have "k + 1 \<le> multiplicity (int p) z"
    by (subst power_dvd_iff_le_multiplicity[OF z pu, symmetric]) (rule d)
  thus ?thesis by (simp add: vp_def qmultiplicity_of_int)
qed

lemma vge_inv_int:
  "prime p \<Longrightarrow> z \<noteq> 0 \<Longrightarrow>
    \<not> int p ^ (k + 1) dvd z \<Longrightarrow> vge p (1 / of_int z) (- of_nat k)"
proof -
  assume p: "prime p" and z: "z \<noteq> 0" and d: "\<not> int p ^ (k + 1) dvd z"
  have "prime (int p)" using p by (simp add: prime_nat_int_transfer)
  hence pu: "\<not> is_unit (int p)" by (metis not_prime_unit)
  have "multiplicity (int p) z \<le> k" using d power_dvd_iff_le_multiplicity[OF z pu, of "k + 1"]
    by simp
  thus ?thesis using z by (simp add: vge_def vp_def inverse_eq_divide[symmetric]
    qmultiplicity_inverse qmultiplicity_of_int)
qed

text \<open>The pole values @{text "H^{(5)}_m"}
  for @{text "m \<le> K"} have @{text "v_p \<ge> -5\<lfloor>log_p K\<rfloor>"}.\<close>
lemma vge_H5: "prime p \<Longrightarrow> m \<le> K \<Longrightarrow>
  vge p (H5 m) (- 5 * of_nat (nat_log p K))"
proof -
  assume p: "prime p" and mK: "m \<le> K"
  show ?thesis unfolding H5_def
  proof (rule vge_sum[OF p])
    fix v assume "v \<in> {1..m}"
    hence v1: "1 \<le> v" and vK: "v \<le> K" using mK by auto
    have nz: "(1 / of_nat v :: rat) \<noteq> 0" using v1 by simp
    have "- of_nat (nat_log p v) \<le> (of_int (vp p (1 / of_nat v)) :: rat)"
      using vge_inv_nat[OF p v1] nz by (simp add: vge_def)
    moreover have "(of_nat (nat_log p v) :: rat) \<le> of_nat (nat_log p K)" using vK
      by (simp add: nat_log_mono)
    ultimately show "vge p (1 / of_nat v ^ 5) (- 5 * of_nat (nat_log p K))"
      unfolding vge_def power_one_over[symmetric] vp_power_rat[OF p nz] by simp
  qed simp
qed

lemma vpGge_pX: "vpGge p pX 0"
  by (auto simp: vpGge_iff coeff_monom vge_one vge_zero)

subsection \<open>The product-difference estimate\<close>

text \<open>@{text "v(\<Prod>(a_i + u) - \<Prod> a_i) \<ge> v(u) - L + \<Sum> v(a_i)"} when every
  @{text "v(a_i) \<le> L < v(u)"}.\<close>
lemma vge_prod_add_sub_prod:
  assumes p: "prime p" and I: "finite I" and u: "u \<noteq> 0"
    and a0: "\<And>i. i \<in> I \<Longrightarrow>
      a i \<noteq> 0" and aL: "\<And>i. i \<in> I \<Longrightarrow> of_int (vp p (a i)) \<le> L"
    and Lu: "L < of_int (vp p u)"
  shows "vge p ((\<Prod> i \<in> I. a i + u) - (\<Prod> i \<in> I. a i))
               (of_int (vp p u) - L + (\<Sum> i \<in> I. of_int (vp p (a i))))"
  using I a0 aL
proof (induction I rule: finite_induct)
  case empty
  thus ?case by (simp add: vge_zero)
next
  case (insert b I)
  have IH: "vge p ((\<Prod> i \<in> I. a i + u) - (\<Prod> i \<in> I. a i))
                  (of_int (vp p u) - L + (\<Sum> i \<in> I. of_int (vp p (a i))))"
    using insert.IH insert.prems by simp
  have e: "(\<Prod> i \<in> insert b I. a i + u) - (\<Prod> i \<in> insert b I. a i) =
           a b * ((\<Prod> i \<in> I. a i + u) - (\<Prod> i \<in> I. a i)) + u * (\<Prod> i \<in>
             I. a i + u)"
    using insert.hyps by (simp add: algebra_simps)
  have 1: "vge p (a b * ((\<Prod> i \<in> I. a i + u) - (\<Prod> i \<in> I. a i)))
                 (of_int (vp p u) - L + (\<Sum> i \<in> insert b I. of_int (vp p (a i))))"
  proof -
    have ab: "vge p (a b) (of_int (vp p (a b)))" by (simp add: vge_def)
    have "vge p (a b * ((\<Prod> i \<in> I. a i + u) - (\<Prod> i \<in> I. a i)))
        (of_int (vp p (a b)) + (of_int (vp p u) - L + (\<Sum> i \<in> I. of_int (vp p (a i)))))"
      by (rule vge_mul[OF p ab IH])
    thus ?thesis by (simp add: sum.insert[OF insert.hyps] algebra_simps)
  qed
  have 2: "vge p (u * (\<Prod> i \<in> I. a i + u))
                 (of_int (vp p u) - L + (\<Sum> i \<in> insert b I. of_int (vp p (a i))))"
  proof -
    have bI: "b \<in> insert b I" by simp
    have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer prime_imp_prime_elem)
    have lt: "vp p (a i) < vp p u" if i: "i \<in> insert b I" for i
    proof -
      have "of_int (vp p (a i)) < (of_int (vp p u) :: rat)" using insert.prems(2)[OF i] Lu
        by linarith
      thus ?thesis by simp
    qed
    have e: "a i + u \<noteq> 0 \<and> vp p (a i + u) = vp p (a i)" if i: "i \<in> I" for i
      using vp_add_eq_of_lt[OF p insert.prems(1) u lt] i by simp
    have pne: "(\<Prod> i \<in> I. a i + u) \<noteq> 0" using e insert.hyps(1)
      by (simp add: prod_zero_iff)
    have V1: "vp p (u * (\<Prod> i \<in> I. a i + u)) = vp p u + vp p (\<Prod> i \<in> I. a i + u)"
      unfolding vp_def by (rule qmultiplicity_mult[OF pe u pne])
    have V2: "vp p (\<Prod> i \<in> I. a i + u) = (\<Sum> i \<in> I. vp p (a i + u))"
      by (rule vp_prod_rat[OF p insert.hyps(1)]) (use e in simp)
    have V3: "(\<Sum> i \<in> I. vp p (a i + u)) = (\<Sum> i \<in> I. vp p (a i))"
      by (rule sum.cong[OF refl]) (simp add: e)
    have "of_int (vp p (a b)) \<le> L" using insert.prems(2)[OF bI] .
    hence "of_int (vp p u) - L + (\<Sum> i \<in> insert b I. of_int (vp p (a i)))
        \<le> (of_int (vp p (u * (\<Prod> i \<in> I. a i + u))) :: rat)"
      unfolding V1 V2 V3 by (simp add: sum.insert[OF insert.hyps])
    thus ?thesis by (simp add: vge_def)
  qed
  show ?case unfolding e by (rule vge_add[OF p 1 2])
qed

subsection \<open>Lemma 3.3\<close>

lemma symPoles_subset: "symPoles K \<subseteq> {- int K..int K}"
  by (auto simp: symPoles_def)

lemma finite_symPoles: "finite (symPoles K)"
  using symPoles_subset finite_subset by blast

lemma symPoles_abs_sub_le: "r \<in> symPoles K \<Longrightarrow>
  s \<in> symPoles K \<Longrightarrow> nat \<bar>r - s\<bar> \<le> 2 * K"
  by (auto simp: symPoles_def)

lemma dIdx_le_symPoles: "r \<in> symPoles K \<Longrightarrow> dIdx r \<le> K"
  by (auto simp: symPoles_def dIdx_def)

theorem far_pole_valuation_bound:
  assumes p: "prime p" and A: "IntValuedAt p A" and dA: "degree A \<le> d"
  shows "vpGge p (tauX (symPoles K) ([:fact K ^ 2:] * A))
           (- 6 * of_nat (nat_log p (max (2 * K) (d + 1))) - of_nat (multiplicity p (24::nat)))"
proof -
  define R where "R = symPoles K"
  define G where "G = [:fact K ^ 2:] * A"
  define L0 where "L0 = nat_log p (2 * K)"
  define Ld where "Ld = nat_log p (max 1 d)"
  define L' where "L' = nat_log p (max (2 * K) (d + 1))"
  have L0L: "L0 \<le> L'" unfolding L0_def L'_def by (rule nat_log_mono) (auto simp: max_def)
  have LdL: "Ld \<le> L'" unfolding Ld_def L'_def by (rule nat_log_mono) (auto simp: max_def)
  have Ld1: "nat_log p (d + 1) \<le> L'" unfolding L'_def
    by (rule nat_log_mono) (auto simp: max_def)
  have LKL: "nat_log p K \<le> L'" unfolding L'_def by (rule nat_log_mono) (auto simp: max_def)
  have finR: "finite R" and Rsub: "R \<subseteq> {- int K..int K}"
    by (simp_all add: R_def finite_symPoles symPoles_subset)
  have Geval: "\<And>y. poly G y = fact K ^ 2 * poly A y" by (simp add: G_def)
  \<comment> \<open>(a) the residues have @{text "v_p \<ge> -L0"}\<close>
  have F0: "\<And>r. r \<in> R \<Longrightarrow>
    vge p (fact K ^ 2 / (\<Prod> s \<in> R - {r}. of_int r - of_int s)) (- of_nat L0)"
  proof -
    fix r assume r: "r \<in> R"
    have hc: "card {s \<in> R - {r}. int p ^ j dvd (r - s)} \<le> 2 * (K div p ^ j) + (if j \<le>
      nat_log p (2 * K) then 1 else 0)"
      if j1: "1 \<le> j" for j
    proof -
      have q: "0 < p ^ j" using prime_gt_0_nat[OF p] by simp
      have s1: "R - {r} \<subseteq> {- int K..int K}" using Rsub by auto
      have s2: "r \<in> {- int K..int K}" using Rsub r by auto
      have s3: "r \<notin> R - {r}" by simp
      have s4: "int (p ^ j) dvd (r - r)" by simp
      have "card {s \<in> R - {r}. int (p ^ j) dvd (r - s)} \<le> 2 * K div p ^ j"
        by (rule card_filter_dvd_le_excl[OF q s1 s2 s3 s4])
      moreover have "2 * K div p ^ j \<le> 2 * (K div p ^ j) + (if j \<le>
        nat_log p (2 * K) then 1 else 0)"
        using two_mul_div_le_nat[OF q, of K] div_eq_zero_of_gt_nat_log[OF p, of K j] by auto
      ultimately show ?thesis by simp
    qed
    have "vge p (fact K ^ 2 / (\<Prod> s \<in>
      R - {r}. of_int r - of_int s)) (- of_nat (1 * nat_log p (2 * K)))"
      by (rule vge_factorial_sq_div_prod[OF p _ _ hc]) (use finR in auto)
    thus "vge p (fact K ^ 2 / (\<Prod> s \<in> R - {r}. of_int r - of_int s)) (- of_nat L0)"
      by (simp add: L0_def)
  qed
  have res: "\<And>r. r \<in> R \<Longrightarrow> vge p (linResidue R G r) (- of_nat L0)"
  proof -
    fix r assume r: "r \<in> R"
    have e: "linResidue R G r = poly A (of_int r) * (fact K ^ 2 / (\<Prod> s \<in>
      R - {r}. of_int r - of_int s))"
      by (simp add: linResidue_def Geval mult.commute)
    have "vge p (poly A (of_int r) * (fact K ^ 2 / (\<Prod> s \<in>
      R - {r}. of_int r - of_int s))) (0 + - of_nat L0)"
      by (rule vge_mul[OF p IntValuedAt_vge[OF A] F0[OF r]])
    thus "vge p (linResidue R G r) (- of_nat L0)" unfolding e by simp
  qed
  \<comment> \<open>(c) the polynomial part @{text "Q = G div \<Prod>(x - r)"},
    bounded at the @{text "d + 1"} integers @{text "K+1, ..., K+1+d"}\<close>
  define Q where "Q = G div linPoleProd R"
  have dQ: "degree Q \<le> d"
  proof -
    have "degree Q \<le> degree G" unfolding Q_def
      by (rule degree_div_le_self[OF linPoleProd_nonzero[OF finR]])
    also have "degree G \<le> degree A" unfolding G_def using degree_smult_le[of "fact K ^ 2" A]
      by simp
    also note dA
    finally show ?thesis .
  qed
  define a where "a = (of_nat (L0 + max L0 Ld) :: rat)"
  have a2L0: "- (2 * of_nat L0) \<ge> - a" and aLd: "- (of_nat Ld + of_nat L0) \<ge> - a"
    by (simp_all add: a_def)
  have hval: "\<And>i. i \<le> d \<Longrightarrow>
    vge p (poly Q (of_int (int K + 1) + of_nat i)) (- a)"
  proof -
    fix i assume "i \<le> d"
    define n where "n = int K + 1 + int i"
    have ncast: "of_int (int K + 1) + of_nat i = (of_int n :: rat)" by (simp add: n_def)
    have nr: "\<And>r. r \<in> R \<Longrightarrow> n - r \<noteq> 0" using Rsub
      by (auto simp: n_def)
    have nrq: "\<And>r. r \<in> R \<Longrightarrow> of_int n - of_int r \<noteq> (0 :: rat)"
      using nr by simp
    have Qn: "poly Q (of_int n) = fact K ^ 2 * poly A (of_int n) / (\<Prod> r \<in>
      R. of_int n - of_int r)
                                 - (\<Sum> r \<in> R. linResidue R G r / (of_int n - of_int r))"
      by (simp only: Q_def poly_div_linPoleProd[OF finR nrq] Geval)
    \<comment> \<open>a pole term @{text "res_r / (n - r)"} with
      @{text "v_p(n - r) \<le> L0"}\<close>
    have hterm: "\<And>r. r \<in> R \<Longrightarrow>
      \<not> int p ^ (L0 + 1) dvd (n - r) \<Longrightarrow>
                   vge p (linResidue R G r / (of_int n - of_int r)) (- a)"
    proof -
      fix r assume r: "r \<in> R" and nd: "\<not> int p ^ (L0 + 1) dvd (n - r)"
      have e: "linResidue R G r / (of_int n - of_int r) = linResidue R G r * (1 / of_int (n - r))"
        by simp
      have "vge p (linResidue R G r * (1 / of_int (n - r))) (- of_nat L0 + - of_nat L0)"
        by (rule vge_mul[OF p res[OF r] vge_inv_int[OF p nr[OF r] nd]])
      hence "vge p (linResidue R G r / (of_int n - of_int r)) (- of_nat L0 + - of_nat L0)"
        unfolding e .
      thus "vge p (linResidue R G r / (of_int n - of_int r)) (- a)"
        by (rule vge_mono) (use a2L0 in simp)
    qed
    show "vge p (poly Q (of_int (int K + 1) + of_nat i)) (- a)"
      unfolding ncast
    proof (cases "\<exists>r0 \<in> R. int p ^ (L0 + 1) dvd (n - r0)")
      case True
      \<comment> \<open>Case B: @{text n} is @{text p}-adically close to exactly one pole
        @{text r0}\<close>
      then obtain r0 where r0: "r0 \<in> R" and dv: "int p ^ (L0 + 1) dvd (n - r0)" by blast
      define T where "T = R - {r0}"
      have Tsub: "T \<subseteq> {- int K..int K}" using Rsub by (auto simp: T_def)
      have sep: "\<And>s. s \<in> T \<Longrightarrow> \<not> int p ^ (L0 + 1) dvd (r0 - s)"
      proof -
        fix s assume s: "s \<in> T"
        have sR: "s \<in> R" and sr: "s \<noteq> r0" using s by (auto simp: T_def)
        have ne: "r0 - s \<noteq> 0" using sr by simp
        have le: "nat \<bar>r0 - s\<bar> \<le> 2 * K" using symPoles_abs_sub_le[of r0 K s] r0 sR
          by (simp add: R_def)
        have K0: "0 < 2 * K" using le ne by (cases "K = 0") auto
        have lt: "2 * K < p ^ (L0 + 1)" unfolding L0_def by (rule lt_pow_nat_log_succ[OF p K0])
        show "\<not> int p ^ (L0 + 1) dvd (r0 - s)"
        proof
          assume "int p ^ (L0 + 1) dvd (r0 - s)"
          hence "\<bar>int p ^ (L0 + 1)\<bar> \<le> \<bar>r0 - s\<bar>"
            by (rule dvd_imp_le_int[OF ne])
          hence "int p ^ (L0 + 1) \<le> \<bar>r0 - s\<bar>" by simp
          also have "\<dots> \<le> int (2 * K)" using le by (simp only: nat_le_iff)
          finally have "int p ^ (L0 + 1) \<le> int (2 * K)" .
          hence "int (p ^ (L0 + 1)) \<le> int (2 * K)" by (simp only: of_nat_power)
          hence "p ^ (L0 + 1) \<le> 2 * K" by (simp only: of_nat_le_iff)
          thus False using lt by simp
        qed
      qed
      have P1: "(\<Prod> s \<in> T. of_int r0 - of_int s :: rat) \<noteq>
        0" and P2: "(\<Prod> s \<in> T. of_int n - of_int s :: rat) \<noteq> 0"
        using finR nrq by (auto simp: T_def prod_zero_iff)
      have Fn: "vge p (fact K ^ 2 / (\<Prod> s \<in> T. of_int n - of_int s)) (- of_nat L0)"
      proof -
        have finT: "finite T" using finR by (simp add: T_def)
        have hc: "card {s \<in> T. int p ^ j dvd (n - s)} \<le> 2 * (K div p ^ j) + (if j \<le>
          nat_log p (2 * K) then 1 else 0)"
          if j1: "1 \<le> j" for j
        proof (cases "j \<le> L0")
          case True
          have q: "0 < p ^ j" using prime_gt_0_nat[OF p] by simp
          have "int p ^ j dvd int p ^ (L0 + 1)" using True by (intro le_imp_power_dvd) simp
          hence dj: "int (p ^ j) dvd (n - r0)" using dvd_trans[OF _ dv] by simp
          have "card {s \<in> T. int (p ^ j) dvd (n - s)} \<le> 2 * K div p ^ j"
            by (rule card_filter_dvd_le_excl[OF q Tsub _ _ dj]) (use r0 Rsub in \<open>auto simp:
              T_def\<close>)
          hence "card {s \<in> T. int p ^ j dvd (n - s)} \<le> 2 * K div p ^ j"
            by (simp only: of_nat_power)
          also have "\<dots> \<le> 2 * (K div p ^ j) + 1" by (rule two_mul_div_le_nat[OF q])
          finally have c: "card {s \<in> T. int p ^ j dvd (n - s)} \<le> 2 * (K div p ^ j) + 1" .
          have jle: "j \<le> nat_log p (2 * K)" using True by (simp add: L0_def)
          show ?thesis unfolding if_P[OF jle] by (rule c)
        next
          case False
          have "{s \<in> T. int p ^ j dvd (n - s)} = {}"
          proof (rule ccontr)
            assume "{s \<in> T. int p ^ j dvd (n - s)} \<noteq> {}"
            then obtain s where s: "s \<in> T" and ds: "int p ^ j dvd (n - s)" by blast
            have "int p ^ (L0 + 1) dvd int p ^ j" using False by (intro le_imp_power_dvd) simp
            hence "int p ^ (L0 + 1) dvd (n - s)" using ds by (rule dvd_trans)
            hence "int p ^ (L0 + 1) dvd (n - s) - (n - r0)" using dv by (rule dvd_diff)
            moreover have "(n - s) - (n - r0) = r0 - s" by simp
            ultimately have "int p ^ (L0 + 1) dvd (r0 - s)" by simp
            thus False using sep[OF s] by simp
          qed
          hence c0: "card {s \<in> T. int p ^ j dvd (n - s)} = 0" by (simp only: card.empty)
          show ?thesis unfolding c0 by simp
        qed
        have "vge p (fact K ^ 2 / (\<Prod> s \<in>
          T. of_int n - of_int s)) (- of_nat (1 * nat_log p (2 * K)))"
          by (rule vge_factorial_sq_div_prod[OF p finT _ hc]) (use nr in \<open>auto simp:
            T_def\<close>)
        thus ?thesis by (simp add: L0_def)
      qed
      have PD: "vge p (((\<Prod> s \<in> T. of_int r0 - of_int s) - (\<Prod> s \<in>
        T. of_int n - of_int s)) /
                       ((\<Prod> s \<in>
                         T. of_int r0 - of_int s) * (of_int n - of_int r0))) (- of_nat L0)"
      proof -
        have finT: "finite T" using finR by (simp add: T_def)
        have pe: "prime_elem (int p)" using p
          by (simp add: prime_nat_int_transfer prime_imp_prime_elem)
        define u where "u = (of_int n - of_int r0 :: rat)"
        have u0: "u \<noteq> 0" using nrq[OF r0] by (simp add: u_def)
        have a0: "(of_int r0 - of_int s :: rat) \<noteq> 0" if "s \<in> T" for s using that
          by (auto simp: T_def)
        have aL: "of_int (vp p (of_int r0 - of_int s :: rat)) \<le> (of_nat L0 :: rat)"
          if s: "s \<in> T" for s
        proof -
          have sR: "s \<in> R" and sr: "s \<noteq> r0" using s by (auto simp: T_def)
          have "vp p (of_int (r0 - s)) \<le> int (nat_log p (2 * K))"
            by (rule vp_int_le_nat_log[OF p]) (use sr symPoles_abs_sub_le[of r0 K s] r0 sR in
              \<open>simp_all add: R_def\<close>)
          hence "vp p (of_int r0 - of_int s) \<le> int L0" by (simp add: L0_def)
          hence "(of_int (vp p (of_int r0 - of_int s :: rat)) :: rat) \<le> of_int (int L0)"
            by (simp only: of_int_le_iff)
          thus ?thesis by simp
        qed
        have Lu: "(of_nat L0 :: rat) < of_int (vp p u)"
        proof -
          have "int L0 < vp p (of_int (n - r0))" by (rule lt_vp_of_dvd[OF p nr[OF r0] dv])
          hence "int L0 < vp p u" by (simp add: u_def)
          hence "(of_int (int L0) :: rat) < of_int (vp p u)" by (simp only: of_int_less_iff)
          thus ?thesis by simp
        qed
        have main: "vge p ((\<Prod> s \<in> T. (of_int r0 - of_int s) + u) - (\<Prod> s \<in>
          T. of_int r0 - of_int s))
            (of_int (vp p u) - of_nat L0 + (\<Sum> s \<in>
              T. of_int (vp p (of_int r0 - of_int s))))"
          by (rule vge_prod_add_sub_prod[OF p finT u0 a0 aL Lu])
        have e1: "(\<Prod> s \<in> T. (of_int r0 - of_int s) + u) = (\<Prod> s \<in>
          T. of_int n - of_int s)" by (simp add: u_def)
        define Pr where "Pr = (\<Prod> s \<in> T. of_int r0 - of_int s :: rat)"
        define Pn where "Pn = (\<Prod> s \<in> T. of_int n - of_int s :: rat)"
        have main': "vge p (Pn - Pr) (of_int (vp p u) - of_nat L0 + (\<Sum> s \<in>
          T. of_int (vp p (of_int r0 - of_int s))))"
          using main unfolding e1 Pr_def[symmetric] Pn_def[symmetric] .
        have Pr0: "Pr \<noteq> 0" unfolding Pr_def using P1 .
        have vPr: "vp p Pr = (\<Sum> s \<in> T. vp p (of_int r0 - of_int s))" unfolding Pr_def
          by (rule vp_prod_rat[OF p finT a0])
        have "vge p ((Pr - Pn) / (Pr * u)) (- of_nat L0)"
          unfolding vge_def
        proof
          assume "(Pr - Pn) / (Pr * u) \<noteq> 0"
          hence N0: "Pn - Pr \<noteq> 0" by auto
          have N0': "Pr - Pn \<noteq> 0" using N0 by simp
          have m1: "vp p (Pn - Pr) = vp p (Pr - Pn)"
          proof -
            have "Pn - Pr = - (Pr - Pn)" by simp
            thus ?thesis by (simp only: vp_def qmultiplicity_minus)
          qed
          have A1: "of_int (vp p u) - of_nat L0 + (\<Sum> s \<in>
            T. of_int (vp p (of_int r0 - of_int s)))
              \<le> (of_int (vp p (Pr - Pn)) :: rat)"
            using main' N0 m1 by (simp add: vge_def)
          have vq: "vp p ((Pr - Pn) / (Pr * u)) = vp p (Pr - Pn) - (vp p Pr + vp p u)"
            unfolding vp_def by (simp add: qmultiplicity_divide[OF pe N0'] qmultiplicity_mult[OF pe
              Pr0 u0] Pr0 u0)
          have "(of_int (vp p ((Pr - Pn) / (Pr * u))) :: rat)
              = of_int (vp p (Pr - Pn)) - ((\<Sum> s \<in>
                T. of_int (vp p (of_int r0 - of_int s))) + of_int (vp p u))"
            unfolding vq vPr by simp
          with A1 show "- of_nat L0 \<le> (of_int (vp p ((Pr - Pn) / (Pr * u))) :: rat)" by linarith
        qed
        thus ?thesis unfolding Pr_def Pn_def u_def .
      qed
      have split: "fact K ^ 2 * poly A (of_int n) / (\<Prod> r \<in> R. of_int n - of_int r)
                     - (\<Sum> r \<in> R. linResidue R G r / (of_int n - of_int r)) =
          (poly A (of_int n) - poly A (of_int r0)) / (of_int n - of_int r0) *
              (fact K ^ 2 / (\<Prod> s \<in> T. of_int n - of_int s))
          + poly A (of_int r0) * ((fact K ^ 2 / (\<Prod> s \<in> T. of_int n - of_int s)) *
              (((\<Prod> s \<in> T. of_int r0 - of_int s) - (\<Prod> s \<in>
                T. of_int n - of_int s)) /
               ((\<Prod> s \<in> T. of_int r0 - of_int s) * (of_int n - of_int r0))))
          - (\<Sum> r \<in> T. linResidue R G r / (of_int n - of_int r))"
      proof -
        have pr: "(\<Prod> r \<in> R. of_int n - of_int r) =
          (of_int n - of_int r0) * (\<Prod> s \<in> T. of_int n - of_int s :: rat)"
          unfolding T_def by (rule prod.remove[OF finR r0])
        have sm: "(\<Sum> r \<in> R. linResidue R G r / (of_int n - of_int r)) =
            linResidue R G r0 / (of_int n - of_int r0) + (\<Sum> r \<in>
              T. linResidue R G r / (of_int n - of_int r))"
          unfolding T_def by (rule sum.remove[OF finR r0])
        have rr: "linResidue R G r0 = fact K ^ 2 * poly A (of_int r0) / (\<Prod> s \<in>
          T. of_int r0 - of_int s)"
          by (simp add: linResidue_def Geval T_def)
        have w0: "(of_int n - of_int r0 :: rat) \<noteq> 0" by (rule nrq[OF r0])
        have gen: "c * An / (w * Pn) - (c * Ar / Pr / w + Sg) =
            (An - Ar) / w * (c / Pn) + Ar * ((c / Pn) * ((Pr - Pn) / (Pr * w))) - Sg"
          if "Pr \<noteq> 0" "Pn \<noteq> 0" "w \<noteq> 0" for c An Ar Pr Pn w Sg :: rat
          using that by (simp add: field_simps)
        show ?thesis unfolding pr sm rr by (rule gen[OF P1 P2 w0])
      qed
      have t1: "vge p ((poly A (of_int n) - poly A (of_int r0)) / (of_int n - of_int r0) *
                       (fact K ^ 2 / (\<Prod> s \<in> T. of_int n - of_int s))) (- a)"
      proof -
        have dq: "n \<noteq> r0" using nr[OF r0] by simp
        have "vge p ((poly A (of_int n) - poly A (of_int r0)) / (of_int n - of_int r0) *
                       (fact K ^ 2 / (\<Prod> s \<in>
                         T. of_int n - of_int s))) (- of_nat (nat_log p (max 1 d)) + - of_nat L0)"
          by (rule vge_mul[OF p diffQuot_vge[OF p A dA dq] Fn])
        thus ?thesis by (rule vge_mono) (use aLd in \<open>simp add: Ld_def\<close>)
      qed
      have t2: "vge p (poly A (of_int r0) * ((fact K ^ 2 / (\<Prod> s \<in>
        T. of_int n - of_int s)) *
              (((\<Prod> s \<in> T. of_int r0 - of_int s) - (\<Prod> s \<in>
                T. of_int n - of_int s)) /
               ((\<Prod> s \<in> T. of_int r0 - of_int s) * (of_int n - of_int r0))))) (- a)"
        using vge_mul[OF p IntValuedAt_vge[OF A] vge_mul[OF p Fn PD]]
          by (rule vge_mono) (use a2L0 in simp)
      have t3: "vge p (\<Sum> r \<in> T. linResidue R G r / (of_int n - of_int r)) (- a)"
      proof (rule vge_sum[OF p])
        show "finite T" using finR by (simp add: T_def)
        fix r assume r: "r \<in> T"
        have rR: "r \<in> R" using r by (simp add: T_def)
        have "\<not> int p ^ (L0 + 1) dvd (n - r)"
        proof
          assume "int p ^ (L0 + 1) dvd (n - r)"
          hence "int p ^ (L0 + 1) dvd (n - r) - (n - r0)" using dv by (rule dvd_diff)
          moreover have "(n - r) - (n - r0) = r0 - r" by simp
          ultimately show False using sep[OF r] by simp
        qed
        thus "vge p (linResidue R G r / (of_int n - of_int r)) (- a)" by (rule hterm[OF rR])
      qed
      show "vge p (poly Q (of_int n)) (- a)"
        unfolding Qn split by (intro vge_diff[OF p] vge_add[OF p] t1 t2 t3)
    next
      case False
      \<comment> \<open>Case A: @{text n} is @{text p}-adically far from every pole\<close>
      have Gn: "vge p (fact K ^ 2 / (\<Prod> r \<in> R. of_int n - of_int r)) (- of_nat (2 * L0))"
      proof -
        have hc: "card {r \<in> R. int p ^ j dvd (n - r)} \<le> 2 * (K div p ^ j) + (if j \<le>
          nat_log p (2 * K) then 2 else 0)"
          if j1: "1 \<le> j" for j
        proof (cases "j \<le> L0")
          case True
          have q: "0 < p ^ j" using prime_gt_0_nat[OF p] by simp
          have "card {r \<in> R. int (p ^ j) dvd (n - r)} \<le> 2 * K div p ^ j + 1"
            by (rule card_filter_dvd_le[OF q Rsub])
          hence "card {r \<in> R. int p ^ j dvd (n - r)} \<le> 2 * K div p ^ j + 1"
            by (simp only: of_nat_power)
          moreover have "2 * K div p ^ j \<le> 2 * (K div p ^ j) + 1"
            by (rule two_mul_div_le_nat[OF q])
          ultimately have c: "card {r \<in> R. int p ^ j dvd (n - r)} \<le> 2 * (K div p ^ j) + 2"
            by linarith
          have jle: "j \<le> nat_log p (2 * K)" using True by (simp add: L0_def)
          show ?thesis unfolding if_P[OF jle] by (rule c)
        next
          case False
          have "{r \<in> R. int p ^ j dvd (n - r)} = {}"
          proof (rule ccontr)
            assume "{r \<in> R. int p ^ j dvd (n - r)} \<noteq> {}"
            then obtain r where r: "r \<in> R" and dr: "int p ^ j dvd (n - r)" by blast
            have "int p ^ (L0 + 1) dvd int p ^ j" using False by (intro le_imp_power_dvd) simp
            hence "int p ^ (L0 + 1) dvd (n - r)" using dr by (rule dvd_trans)
            thus False using \<open>\<not> (\<exists>r0 \<in>
              R. int p ^ (L0 + 1) dvd (n - r0))\<close> r by blast
          qed
          hence c0: "card {r \<in> R. int p ^ j dvd (n - r)} = 0" by (simp only: card.empty)
          show ?thesis unfolding c0 by simp
        qed
        have "vge p (fact K ^ 2 / (\<Prod> r \<in>
          R. of_int n - of_int r)) (- of_nat (2 * nat_log p (2 * K)))"
          by (rule vge_factorial_sq_div_prod[OF p finR _ hc]) (use nr in auto)
        thus ?thesis by (simp add: L0_def)
      qed
      have s1: "vge p (fact K ^ 2 * poly A (of_int n) / (\<Prod> r \<in>
        R. of_int n - of_int r)) (- a)"
      proof -
        have e: "fact K ^ 2 * poly A (of_int n) / (\<Prod> r \<in> R. of_int n - of_int r)
            = poly A (of_int n) * (fact K ^ 2 / (\<Prod> r \<in> R. of_int n - of_int r))"
              by (simp add: mult.commute)
        show ?thesis unfolding e using vge_mul[OF p IntValuedAt_vge[OF A] Gn]
          by (rule vge_mono) (use a2L0 in simp)
      qed
      have s2: "vge p (\<Sum> r \<in> R. linResidue R G r / (of_int n - of_int r)) (- a)"
      proof (rule vge_sum[OF p finR])
        fix r assume r: "r \<in> R"
        have "\<not> int p ^ (L0 + 1) dvd (n - r)" using False r by blast
        thus "vge p (linResidue R G r / (of_int n - of_int r)) (- a)" by (rule hterm[OF r])
      qed
      show "vge p (poly Q (of_int n)) (- a)"
        unfolding Qn by (intro vge_diff[OF p] s1 s2)
    qed
  qed
  have Qv: "vge p (tau Q) (- a - 4 * of_nat (nat_log p (d + 1)))"
    by (rule tau_vge_of_values[OF p dQ hval])
  \<comment> \<open>assemble the coefficients of
    @{text "\<tau>_X(G) = [:\<tau>(Q):] + \<Sum>_r [:res_r:] * (H5 (dIdx r) - X)"}\<close>
  have num: "- 6 * of_nat L' - of_nat (multiplicity p (24::nat)) \<le>
    - a - 4 * (of_nat (nat_log p (d + 1)) :: rat)"
  proof -
    have "L0 + max L0 Ld \<le> 2 * L'" using L0L LdL by simp
    hence "(of_nat (L0 + max L0 Ld) :: rat) \<le> of_nat (2 * L')" by (simp only: of_nat_le_iff)
    hence "a \<le> 2 * of_nat L'" by (simp add: a_def)
    moreover have "(of_nat (nat_log p (d + 1)) :: rat) \<le> of_nat L'" using Ld1 by simp
    moreover have "(0::rat) \<le> of_nat (multiplicity p (24::nat))" by simp
    ultimately show ?thesis by linarith
  qed
  have pole: "\<And>r. r \<in> R \<Longrightarrow> vpGge p ([:linResidue R G r:] * tauPole r)
                 (- 6 * of_nat L' - of_nat (multiplicity p (24::nat)))"
  proof -
    fix r assume r: "r \<in> R"
    have rK: "r \<in> symPoles K" using r by (simp add: R_def)
    have h: "vge p (H5 (dIdx r)) (- 5 * of_nat (nat_log p K))"
      by (rule vge_H5[OF p dIdx_le_symPoles[OF rK]])
    have x: "vpGge p (- pX) (- 5 * of_nat (nat_log p K))"
      by (rule vpGge_neg[OF vpGge_mono[OF vpGge_pX]]) simp
    have tp: "vpGge p (tauPole r) (- 5 * of_nat (nat_log p K))"
      unfolding tauPole_def diff_conv_add_uminus by (rule vpGge_add[OF p vpGge_C[OF h] x])
    have "vpGge p ([:linResidue R G r:] * tauPole r) (- of_nat L0 + - 5 * of_nat (nat_log p K))"
      by (rule vpGge_mul[OF p vpGge_C[OF res[OF r]] tp])
    moreover have "- 6 * of_nat L' - of_nat (multiplicity p (24::nat)) \<le>
      - of_nat L0 + - 5 * (of_nat (nat_log p K) :: rat)"
    proof -
      have "(of_nat L0 :: rat) \<le> of_nat L'" using L0L by simp
      moreover have "(of_nat (nat_log p K) :: rat) \<le> of_nat L'" using LKL by simp
      moreover have "(0::rat) \<le> of_nat (multiplicity p (24::nat))" by simp
      ultimately show ?thesis by linarith
    qed
    ultimately show "vpGge p ([:linResidue R G r:] * tauPole r) (- 6 * of_nat L' -
      of_nat (multiplicity p (24::nat)))"
      by (rule vpGge_mono)
  qed
  have "vpGge p (tauX R G) (- 6 * of_nat L' - of_nat (multiplicity p (24::nat)))"
    unfolding tauX_def Q_def[symmetric]
    by (intro vpGge_add[OF p] vpGge_C vge_mono[OF Qv num] vpGge_sum[OF p finR] pole)
  thus ?thesis by (simp add: R_def G_def L'_def)
qed

end

