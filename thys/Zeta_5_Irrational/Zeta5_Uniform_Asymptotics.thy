(*  Title:   Zeta5_Uniform_Asymptotics.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Uniform_Asymptotics
  imports Zeta5_Inner_Range Piecewise_Interval_Integrals
begin

section \<open>The uniform estimate (5.7) in the inner range\<close>

text \<open>For fixed \<open>M \<ge> 40\<close>, \<open>\<gamma>\<^sub>p\<^sup>i\<^sup>n =
  p \<Gamma>(K/p) + O\<^sub>M(1)\<close> and \<open>v\<^sub>p(S\<^sub>K) =
  p N(K/p) + O\<^sub>M(1)\<close>
  uniformly over the range (4.1), with the explicit constant \<open>1000 M\<^sup>2\<close>
    (@{text gammaIn_uniform_estimate}).
  Floors and \<open>v\<^sub>p(S\<^sub>K)\<close>, a Riemann-sum identity
    for the \<open>z\<close>-integral, exact class counts and the
  discrete decomposition of \<open>\<gamma>\<^sub>p\<^sup>i\<^sup>n\<close>;
    everything else is integer arithmetic.  Lean theory
  @{text Uniform57}.\<close>

subsection \<open>Floors and @{text "v_p(S_K)"} in the inner range\<close>

lemma floor_nat_div: "floor (real n / real d) = int (n div d)"
  by (rule floor_divide_of_nat_eq)

text \<open>Legendre with a single term: @{text "v_p(n!) = \<lfloor>n/p\<rfloor>"}
  for @{text "n < p^2"}.\<close>
lemma multiplicity_fact_small:
  assumes "prime p" "n < p ^ 2"
  shows "multiplicity p (fact n) = n div p"
proof -
  have L: "multiplicity p (fact n) = (\<Sum> a = 1..n + 1. n div p ^ a)"
    by (rule legendre_sum[OF assms(1)]) simp
  have "n div p ^ a = 0" if "a \<in> {1..n + 1}" "a \<noteq> 1" for a
  proof -
    from that have "2 \<le> a" by auto
    hence "p ^ 2 \<le> p ^ a" by (rule power_increasing) (use prime_ge_1_nat[OF assms(1)] in simp)
    thus ?thesis using assms(2) by (intro div_less) linarith
  qed
  hence "(\<Sum> a = 1..n + 1. n div p ^ a) = n div p" by (subst sum.remove[of _ 1]) auto
  thus ?thesis using L by simp
qed

text \<open>Under (4.1) all factorial arguments are @{text "< p^2"} (@{text "innerHyp_bounds"}:
  @{text "5K < p^2"}).\<close>
lemma vpS_inner:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "vpS K p = 2 * int (hof K) * int (K div p) - 12 * int (hof K) * int (Nof K div p)
                   - 2 * int (\<Sum> i = 1..hof K - 1. 2 * i div p)"
proof -
  have b: "5 * K < p ^ 2" using innerHyp_bounds[OF h] by simp
  have p7: "7 \<le> p" using hyp_facts[OF p h] by simp
  have m4: "multiplicity p (4::nat) = 0"
  proof -
    have "\<not> p dvd 4"
    proof
      assume "p dvd 4"
      hence "p \<le> 4" by (rule dvd_imp_le) simp
      thus False using p7 by linarith
    qed
    thus ?thesis by (rule not_dvd_imp_multiplicity_0)
  qed
  define A :: nat where "A = fact K ^ (2 * hof K) * 4 ^ (hof K - 1)"
  define D :: nat where "D = fact (Nof K) ^ (12 * hof K) * (\<Prod> i =
    1..hof K - 1. fact (2 * i) ^ 2)"
  have SK: "SK K = of_nat A / of_nat D" by (simp add: SK_def A_def D_def)
  have mA: "multiplicity p A = 2 * hof K * (K div p)"
  proof -
    have pe: "prime_elem p" using p by simp
    have Kp: "K < p ^ 2" using b by linarith
    have "multiplicity p A = 2 * hof K * multiplicity p (fact K) + (hof K - 1) *
      multiplicity p (4::nat)"
      unfolding A_def using pe by (simp add: prime_elem_multiplicity_mult_distrib
        prime_elem_multiplicity_power_distrib)
    thus ?thesis unfolding multiplicity_fact_small[OF p Kp] m4 by presburger
  qed
  have mD: "multiplicity p D = 12 * hof K * (Nof K div p) + 2 * (\<Sum> i =
    1..hof K - 1. 2 * i div p)"
  proof -
    have pe: "prime_elem p" using p by simp
    have hK: "hof K \<le> K" unfolding hof_def by linarith
    have NK: "Nof K < p ^ 2" using b unfolding Nof_def by linarith
    have fi: "multiplicity p (fact (2 * i) ^ 2) = 2 * (2 * i div p)" if "i \<in> {1..hof K - 1}"
      for i
    proof -
      have i: "1 \<le> i" "i \<le> hof K - 1" using that by auto
      have ip: "2 * i < p ^ 2" using hK i b by arith
      show ?thesis using pe by (force simp: prime_elem_multiplicity_power_distrib
        multiplicity_fact_small[OF p ip])
    qed
    have P: "multiplicity p (\<Prod> i = 1..hof K - 1. fact (2 * i) ^ 2) = (\<Sum> i =
      1..hof K - 1. 2 * (2 * i div p))"
    proof -
      have "multiplicity p (\<Prod> i = 1..hof K - 1. fact (2 * i) ^ 2) = (\<Sum> i =
        1..hof K - 1. multiplicity p (fact (2 * i) ^ 2))"
        by (rule prime_elem_multiplicity_prod_distrib[OF pe]) auto
      also have "\<dots> = (\<Sum> i = 1..hof K - 1. 2 * (2 * i div p))"
        by (rule sum.cong[OF refl]) (rule fi)
      finally show ?thesis .
    qed
    have "multiplicity p D = 12 * hof K * multiplicity p (fact (Nof K)) +
      multiplicity p (\<Prod> i = 1..hof K - 1. fact (2 * i) ^ 2)"
      unfolding D_def using pe by (subst prime_elem_multiplicity_mult_distrib) (simp_all add:
        prime_elem_multiplicity_power_distrib)
    thus ?thesis unfolding P multiplicity_fact_small[OF p NK] by (metis sum_distrib_left)
  qed
  have pei: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer)
  have A0: "A \<noteq> 0" and D0: "D \<noteq> 0" by (simp_all add: A_def D_def)
  have v: "vpS K p = int (multiplicity p A) - int (multiplicity p D)"
    unfolding vpS_def vp_def SK using A0 D0 pei
    by (simp add: qmultiplicity_divide qmultiplicity_of_nat multiplicity_int)
  show ?thesis unfolding v mA mD by auto
qed

text \<open>@{text "G_4(n) = 4 t n - p t (t + 1)"}, @{text "t = \<lfloor>2n/p\<rfloor>"};
  @{text "G_4(n)/4 = p J(n/p)"}.\<close>
definition G4 :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "G4 p n = 4 * int (2 * n div p) * int n - int p * int (2 * n div p) * (int (2 * n div p) + 1)"

lemma G4_step:
  assumes "2 \<le> p"
  shows "0 \<le> G4 p (n + 1) - G4 p n - 4 * int (2 * n div p) \<and>
         G4 p (n + 1) - G4 p n - 4 * int (2 * n div p) \<le>
           4 * (int (2 * (n + 1) div p) - int (2 * n div p))"
proof -
  define t where "t = 2 * n div p"
  define t' where "t' = 2 * (n + 1) div p"
  have tt: "t \<le> t'" "t' \<le> t + 1"
  proof -
    show "t \<le> t'" unfolding t_def t'_def by (rule div_le_mono) simp
    have "2 * (n + 1) \<le> 2 * n + p" using assms by simp
    hence "t' \<le> (2 * n + p) div p" unfolding t'_def by (rule div_le_mono)
    also have "(2 * n + p) div p = t + 1" unfolding t_def using assms by force
    finally show "t' \<le> t + 1" .
  qed
  have bounds: "t * p \<le> 2 * n" "2 * n < (t + 1) * p" "t' * p \<le> 2 * (n + 1)" "2 * (n + 1) <
    (t' + 1) * p"
  proof -
    have p0: "0 < p" using assms by simp
    have g: "x div p * p \<le> x" "x < (x div p + 1) * p" for x
    proof -
      show "x div p * p \<le> x" by fastforce
      show "x < (x div p + 1) * p"
      proof -
        have e: "(x div p + 1) * p = x div p * p + p" by (simp add: algebra_simps)
        show ?thesis unfolding e using mod_less_divisor[OF p0, of x] div_mult_mod_eq[of x p]
          by linarith
      qed
    qed
    show "t * p \<le> 2 * n" "2 * n < (t + 1) * p" "t' * p \<le> 2 * (n + 1)" "2 * (n + 1) <
      (t' + 1) * p"
      unfolding t_def t'_def by (rule g)+
  qed
  show ?thesis
  proof (cases "t' = t")
    case True
    have e: "G4 p (n + 1) - G4 p n - 4 * int (2 * n div p) = 0"
      unfolding G4_def t_def[symmetric] t'_def[symmetric] True by (fastforce simp: algebra_simps)
    show ?thesis using True unfolding e unfolding t_def[symmetric] t'_def[symmetric] by simp
  next
    case False
    hence t1: "t' = t + 1" using tt by linarith
    have e: "G4 p (n + 1) - G4 p n - 4 * int (2 * n div p) = 2 * (2 * int n + 2 - int p * int t')"
      unfolding G4_def t_def[symmetric] t'_def[symmetric] t1 by (simp add: algebra_simps)
    have b1: "int t' * int p \<le> 2 * int n + 2"
    proof -
      have "int (t' * p) \<le> int (2 * (n + 1))" using bounds(3) by (simp only: of_nat_le_iff)
      thus ?thesis by auto
    qed
    have b2: "2 * int n < (int t + 1) * int p"
    proof -
      have "int (2 * n) < int ((t + 1) * p)" using bounds(2) by (simp only: of_nat_less_iff)
      thus ?thesis by (auto simp: algebra_simps)
    qed
    have b3: "int t' = int t + 1" using t1 by simp
    have e1: "int t' * int p = int p * int t + int p" "(int t + 1) * int p = int p * int t + int p"
      "int p * int t' = int p * int t + int p" unfolding b3 by (simp_all add: algebra_simps)
    have "0 \<le> 2 * (2 * int n + 2 - int p * int t')" using b1 e1 by presburger
    moreover have "2 * (2 * int n + 2 - int p * int t') \<le> 4 * (int t' - int t)" using b2 b3 e1
      by presburger
    ultimately show ?thesis unfolding e unfolding t_def[symmetric] t'_def[symmetric] by (rule conjI)
  qed
qed

lemma G4_tele:
  assumes "2 \<le> p"
  shows "0 \<le> G4 p n - 4 * (\<Sum> i < n. int (2 * i div p)) \<and>
         G4 p n - 4 * (\<Sum> i < n. int (2 * i div p)) \<le> 4 * int (2 * n div p)"
proof (induction n)
  case 0
  show ?case by (simp add: G4_def)
next
  case (Suc n)
  show ?case using Suc G4_step[OF assms, of n] by (simp add: algebra_simps)
qed

lemma sum_Icc_eq_range: "f 0 = (0 :: int) \<Longrightarrow> 1 \<le> (h :: nat) \<Longrightarrow>
  (\<Sum> i = 1..h - 1. f i) = (\<Sum> i < h. f i)"
proof -
  assume f0: "f 0 = (0 :: int)" and h: "1 \<le> h"
  obtain k where k: "h = Suc k" using h by (cases h) auto
  have s: "{..<h} = insert 0 {1..h - 1}" unfolding k by force
  show ?thesis unfolding s using f0 by (auto simp: sum.insert)
qed

text \<open>@{text "v_p(S_K) - p N(K/p) = (G_4(h) - 4 \<Sum>_{i<h} \<lfloor>2i/p\<rfloor>)/2"}
  (@{text "K = 40n"}: @{text "\<lambda>K/p = h/p"}, @{text "\<alpha>K/p = N/p"} exactly).\<close>
lemma vpS_sub:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "of_int (vpS K p) - real p * Nfun_r (real K / real p)
           = of_int (G4 p (hof K) - 4 * (\<Sum> i < hof K. int (2 * i div p))) / 2"
proof -
  obtain n where K: "K = 40 * n" using h unfolding InnerHyp_def by (auto elim: dvdE)
  have hh: "hof K = 37 * n" and hN: "Nof K = 3 * n" unfolding K hof_def Nof_def by simp_all
  have pr: "0 < real p" using p by (simp add: prime_gt_0_nat)
  have v: "vpS K p = 2 * int (hof K) * int (K div p) - 12 * int (hof K) * int (Nof K div p) - 2 *
    (\<Sum> i < hof K. int (2 * i div p))"
    unfolding vpS_inner[OF p h] of_nat_sum
  proof -
    have "0 < n" using h unfolding InnerHyp_def K by simp
    hence h1: "1 \<le> hof K" unfolding hh by fastforce
    have s: "(\<Sum> i = 1..hof K - 1. int (2 * i div p)) = (\<Sum> i < hof K. int (2 * i div p))"
      by (rule sum_Icc_eq_range) (use h1 in simp_all)
    show "2 * int (hof K) * int (K div p) - 12 * int (hof K) * int (Nof K div p) - 2 * (\<Sum> i =
      1..hof K - 1. int (2 * i div p))
        = 2 * int (hof K) * int (K div p) - 12 * int (hof K) * int (Nof K div p) - 2 * (\<Sum> i <
          hof K. int (2 * i div p))"
      unfolding s ..
  qed
  have e1: "lam_r * real K / real p = real (hof K) / real p" and e2: "alpha_r * (real K / real p) =
    real (Nof K) / real p"
    and e3: "2 * (real (hof K) / real p) = real (2 * hof K) / real p"
    unfolding hh hN unfolding K lam_r_def alpha_r_def by (simp_all add: field_simps)
  have f1: "floor (real K / real p) = int (K div p)" by (rule floor_nat_div)
  have f2: "floor (alpha_r * (real K / real p)) = int (Nof K div p)" unfolding e2
    by (rule floor_nat_div)
  have l: "lam_r * (real K / real p) = real (hof K) / real p" using e1 by argo
  have f3: "floor (2 * (lam_r * (real K / real p))) = int (2 * hof K div p)" unfolding l e3
    by (rule floor_nat_div)
  have pN: "real p * Nfun_r (real K / real p) =
    2 * real (hof K) * real (K div p) - 12 * real (hof K) * real (Nof K div p)
               - 2 * real (2 * hof K div p) * real (hof K) + real p * real (2 * hof K div p) *
                 (real (2 * hof K div p) + 1) / 2"
  proof -
    have hh': "real (hof K) = lam_r * real K" unfolding hh unfolding K lam_r_def by simp
    show ?thesis unfolding Nfun_r_def J_r_def f1 f2 f3 using pr by (fastforce simp: field_simps hh')
  qed
  show ?thesis unfolding v pN G4_def by (force simp: of_int_sum)
qed

lemma vpS_bound:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "\<bar>of_int (vpS K p) - real p * Nfun_r (real K / real p)\<bar> \<le> 4 * real M"
proof -
  have p2: "2 \<le> p" using p by (rule prime_ge_2_nat)
  have t: "0 \<le> G4 p (hof K) - 4 * (\<Sum> i < hof K. int (2 * i div p)) \<and>
           G4 p (hof K) - 4 * (\<Sum> i < hof K. int (2 * i div p)) \<le> 4 * int (2 * hof K div p)"
    by (rule G4_tele[OF p2])
  have q: "2 * hof K div p \<le> 2 * M"
  proof -
    have "hof K \<le> K" unfolding hof_def by linarith
    moreover have "K < p * M" using h unfolding InnerHyp_def by simp
    ultimately have "2 * hof K < 2 * (p * M)" by linarith
    hence "2 * hof K < (2 * M) * p" by (force simp: algebra_simps)
    hence "2 * hof K div p < 2 * M" using p2 by (force simp: div_less_iff_less_mult)
    thus ?thesis by simp
  qed
  define X where "X = G4 p (hof K) - 4 * (\<Sum> i < hof K. int (2 * i div p))"
  have "0 \<le> (of_int X :: real)" using t unfolding X_def[symmetric] by linarith
  moreover have "(of_int X :: real) \<le> 8 * real M"
  proof -
    have "X \<le> 4 * int (2 * hof K div p)" using t unfolding X_def by simp
    also have "\<dots> \<le> 4 * int (2 * M)" using q by simp
    finally have "X \<le> 8 * int M" by simp
    thus ?thesis by simp
  qed
  ultimately show ?thesis unfolding vpS_sub[OF p h] X_def[symmetric] by (force simp: abs_le_iff)
qed


subsection \<open>The Riemann-sum identity for the @{text z}-integral\<close>

lemma floor_between:
  assumes "0 < p" "of_int j / real p < y" "y < (of_int j + 1) / real p"
  shows "floor y = j div int p"
proof -
  have pr: "0 < real p" using assms(1) by simp
  have r0: "0 \<le> j mod int p" "j mod int p < int p" using assms(1) by simp_all
  have d: "j div int p * int p + j mod int p = j" by (rule div_mult_mod_eq)
  have e: "(j div int p + 1) * int p = j div int p * int p + int p" by (simp add: algebra_simps)
  have i1: "j div int p * int p \<le> j" using r0 d by linarith
  have i2: "j + 1 \<le> (j div int p + 1) * int p" unfolding e using r0 d by linarith
  have l1: "of_int (j div int p) * real p \<le> of_int j"
  proof -
    have "real_of_int (j div int p * int p) \<le> real_of_int j" using i1
      by (simp only: of_int_le_iff)
    thus ?thesis by simp
  qed
  have l2: "of_int j + 1 \<le> (of_int (j div int p) + 1) * real p"
  proof -
    have "real_of_int (j + 1) \<le> real_of_int ((j div int p + 1) * int p)" using i2
      by (simp only: of_int_le_iff)
    thus ?thesis by simp
  qed
  have y1: "of_int j < y * real p" using assms(2) pr pos_divide_less_eq by blast
  have y2: "y * real p < of_int j + 1" using assms(3) pr by (fastforce simp: pos_less_divide_eq)
  have "of_int (j div int p) \<le> y"
  proof -
    have "of_int (j div int p) * real p < y * real p" using l1 y1 by linarith
    thus ?thesis using pr by force
  qed
  moreover have "y < of_int (j div int p) + 1"
  proof -
    have "y * real p < (of_int (j div int p) + 1) * real p" using l2 y2 by linarith
    thus ?thesis using pr by fastforce
  qed
  ultimately show ?thesis by (simp add: floor_eq_iff)
qed

text \<open>@{text "l"} on the @{text a}-th grid cell @{text "(a/p, (a+1)/p)"}.\<close>
definition ellZ :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "ellZ p A a = (int A - int a - 1) div int p + (int A + int a) div int p + 1"

definition gg :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "gg T v l = (T - 3 * v) * (T + 3 * v - l - 5)"

lemma ell_on_cell:
  assumes "0 < p" "real a / real p < z" "z < (real a + 1) / real p"
  shows "ell_r (real A / real p) z = of_int (ellZ p A a)"
proof -
  have f1: "floor (real A / real p - z) = (int A - int a - 1) div int p"
  proof (rule floor_between[OF assms(1)])
    show "real_of_int (int A - int a - 1) / real p < real A / real p - z" using assms(3)
      by (auto simp: diff_divide_distrib add_divide_distrib)
    show "real A / real p - z < (real_of_int (int A - int a - 1) + 1) / real p" using assms(2)
      by (fastforce simp: diff_divide_distrib add_divide_distrib)
  qed
  have f2: "floor (real A / real p + z) = (int A + int a) div int p"
  proof (rule floor_between[OF assms(1)])
    show "real_of_int (int A + int a) / real p < real A / real p + z" using assms(2)
      by (force simp: diff_divide_distrib add_divide_distrib)
    show "real A / real p + z < (real_of_int (int A + int a) + 1) / real p" using assms(3)
      by (fastforce simp: diff_divide_distrib add_divide_distrib)
  qed
  show ?thesis unfolding ell_r_def ellZ_def f1 f2 by simp
qed

definition phiZ :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> real
  \<Rightarrow> real" where
  "phiZ p N K T z = (of_int T - 3 * ell_r (real N / real p) z) * (of_int T + 3 * ell_r (real N /
    real p) z - ell_r (real K / real p) z - 5)"

lemma phi_on_cell:
  assumes "0 < p" "real a / real p < z" "z < (real a + 1) / real p"
  shows "phiZ p N K T z = of_int (gg T (ellZ p N a) (ellZ p K a))"
  unfolding phiZ_def gg_def ell_on_cell[OF assms, of N] ell_on_cell[OF assms, of K]
    by (simp add: algebra_simps)

lemma integral_cell:
  assumes "0 < p" "real a / real p \<le> c" "c \<le> (real a + 1) / real p"
  shows "interval_lebesgue_integrable lborel (ereal (real a /
    real p)) (ereal c) (phiZ p N K T) \<and>
         interval_lebesgue_integral lborel (ereal (real a / real p)) (ereal c) (phiZ p N K T)
           = (c - real a / real p) * of_int (gg T (ellZ p N a) (ellZ p K a))"
  by (rule const_piece[OF assms(2)]) (use assms(1,3) in \<open>auto simp: phi_on_cell\<close>)

text \<open>@{text "p \<integral>_0^{1/2} \<phi> = \<Sum>_{a<m} gg(a) + gg(m)/2"}
  for @{text "p = 2m + 1"}.\<close>
lemma integral_sum:
  assumes pm: "p = 2 * m + 1"
  shows "real p * interval_lebesgue_integral lborel (ereal 0) (ereal (1 / 2)) (phiZ p N K T)
           = (\<Sum> a < m. of_int (gg T (ellZ p N a) (ellZ p K a))) +
             of_int (gg T (ellZ p N m) (ellZ p K m)) / 2"
proof -
  have p0: "0 < p" using pm by simp
  have pr: "real p = 2 * real m + 1" using pm by simp
  have pre: "0 < real p" using p0 by simp
  have cells: "interval_lebesgue_integrable lborel (ereal 0) (ereal (real k /
    real p)) (phiZ p N K T) \<and>
      interval_lebesgue_integral lborel (ereal 0) (ereal (real k / real p)) (phiZ p N K T)
        = (\<Sum> a < k. (1 / real p) * of_int (gg T (ellZ p N a) (ellZ p K a)))" if "k \<le> m"
          for k
    using that
  proof (induction k)
    case 0
    show ?case
      using const_piece[of 0 0 "phiZ p N K T" 0] by force
  next
    case (Suc k)
    have c: "interval_lebesgue_integrable lborel (ereal (real k / real p)) (ereal (real (Suc k) /
      real p)) (phiZ p N K T) \<and>
        interval_lebesgue_integral lborel (ereal (real k / real p)) (ereal (real (Suc k) /
          real p)) (phiZ p N K T)
          = (real (Suc k) / real p - real k / real p) * of_int (gg T (ellZ p N k) (ellZ p K k))"
      by (rule integral_cell[OF p0]) (simp_all add: divide_right_mono)
    have ih: "interval_lebesgue_integrable lborel (ereal 0) (ereal (real k /
      real p)) (phiZ p N K T) \<and>
      interval_lebesgue_integral lborel (ereal 0) (ereal (real k / real p)) (phiZ p N K T)
        = (\<Sum> a < k. (1 / real p) * of_int (gg T (ellZ p N a) (ellZ p K a)))"
      using Suc.IH Suc.prems by simp
    have ch: "interval_lebesgue_integrable lborel (ereal 0) (ereal (real (Suc k) /
      real p)) (phiZ p N K T) \<and>
      interval_lebesgue_integral lborel (ereal 0) (ereal (real (Suc k) / real p)) (phiZ p N K T)
        = (\<Sum> a < k. (1 / real p) * of_int (gg T (ellZ p N a) (ellZ p K a)))
          + (real (Suc k) / real p - real k / real p) * of_int (gg T (ellZ p N k) (ellZ p K k))"
      by (rule chain[OF _ _ ih c]) (simp_all add: divide_right_mono)
    have e: "real (Suc k) / real p - real k / real p = 1 / real p"
      by (force simp: diff_divide_distrib[symmetric])
    show ?case using ch unfolding e by simp
  qed
  have last: "interval_lebesgue_integrable lborel (ereal (real m / real p)) (ereal (1 /
    2)) (phiZ p N K T) \<and>
      interval_lebesgue_integral lborel (ereal (real m / real p)) (ereal (1 / 2)) (phiZ p N K T)
        = (1 / 2 - real m / real p) * of_int (gg T (ellZ p N m) (ellZ p K m))"
    by (rule integral_cell[OF p0]) (use pr pre in \<open>simp_all add: divide_le_eq
      le_divide_eq\<close>)
  have half: "1 / 2 - real m / real p = 1 / (2 * real p)"
  proof -
    have "2 * real m + 1 \<noteq> 0" by simp
    hence d: "1 / 2 - real m / (2 * real m + 1) =
      (1 * (2 * real m + 1) - real m * 2) / (2 * (2 * real m + 1))"
      by (simp add: diff_frac_eq)
    have n: "1 * (2 * real m + 1) - real m * 2 = (1::real)" by simp
    show ?thesis unfolding pr d n by metis
  qed
  from chain[OF _ _ cells[OF le_refl] last]
  have "interval_lebesgue_integral lborel (ereal 0) (ereal (1 / 2)) (phiZ p N K T)
          = (\<Sum> a < m. (1 / real p) * of_int (gg T (ellZ p N a) (ellZ p K a))) + (1 / 2 -
            real m / real p) * of_int (gg T (ellZ p N m) (ellZ p K m))"
    using pr pre by (simp add: divide_le_eq)
  thus ?thesis unfolding half using pre by (simp add: sum_distrib_left field_simps)
qed


subsection \<open>Exact class counts\<close>

lemma count_mod_eq:
  assumes "0 < p" "1 \<le> r" "r < p"
  shows "card {j \<in> {1..A}. j mod p = r} = (A + p - r) div p"
proof -
  have e: "{j \<in> {1..A}. j mod p = r} = (\<lambda>t. t * p + r) ` {..<(A + p - r) div p}"
  proof (intro equalityI subsetI)
    fix j assume "j \<in> {j \<in> {1..A}. j mod p = r}"
    hence j: "1 \<le> j" "j \<le> A" "j mod p = r" by auto
    have jd: "j = j div p * p + r" using j(3) div_mult_mod_eq[of j p] by simp
    have "(j div p + 1) * p \<le> A + p - r" using jd j(2) by (simp add: algebra_simps)
    hence "j div p + 1 \<le> (A + p - r) div p" using assms(1) using less_eq_div_iff_mult_less_eq
      by blast
    hence "j div p < (A + p - r) div p" by linarith
    thus "j \<in> (\<lambda>t. t * p + r) ` {..<(A + p - r) div p}" using jd
      by (intro rev_image_eqI[of "j div p"]) simp_all
  next
    fix j assume "j \<in> (\<lambda>t. t * p + r) ` {..<(A + p - r) div p}"
    then obtain t where t: "t < (A + p - r) div p" "j = t * p + r" by auto
    have "t + 1 \<le> (A + p - r) div p" using t(1) by linarith
    hence "(t + 1) * p \<le> A + p - r" using assms(1) by (metis less_eq_div_iff_mult_less_eq)
    hence "j \<le> A" using t(2) assms by (simp add: algebra_simps)
    moreover have "j mod p = r" using t(2) assms(3) by simp
    ultimately show "j \<in> {j \<in> {1..A}. j mod p = r}" using t(2) assms(2) by simp
  qed
  have inj: "inj_on (\<lambda>t. t * p + r) {..<(A + p - r) div p}" using assms(1)
    by (auto simp: inj_on_def)
  show ?thesis unfolding e card_image[OF inj] by simp
qed

lemma ell_exact:
  assumes "odd p" "1 \<le> a" "a \<le> mHalf p"
  shows "ell p A a = (A + p - a) div p + (A + a) div p"
proof -
  have ap: "a < p" "p - a \<noteq> a" "1 \<le> p - a" "p - a < p" using assms unfolding mHalf_def
    by (auto elim!: oddE)
  have split: "{j \<in> {1..A}. j mod p = a mod p \<or>
    (j + a) mod p = 0} = {j \<in> {1..A}. j mod p = a} \<union> {j \<in> {1..A}. j mod p = p - a}"
  proof -
    have p0: "0 < p" using ap(1) by simp
    have m: "(j + a) mod p = 0 \<longleftrightarrow> j mod p = p - a" for j
    proof -
      have r: "j mod p < p" using p0 by simp
      have "(j + a) mod p = 0 \<longleftrightarrow> j mod p + a = 0 \<or> j mod p + a = p"
        using mod_add_zero_iff_aux[OF r ap(1)] by (simp add: mod_add_left_eq)
      thus ?thesis using assms(2) ap(1) r by auto
    qed
    show ?thesis using m ap by auto
  qed
  have disj: "{j \<in> {1..A}. j mod p = a} \<inter> {j \<in> {1..A}. j mod p = p - a} = {}"
    using ap by auto
  have p0: "0 < p" using ap(1) by simp
  have c: "card ({j \<in> {1..A}. j mod p = a} \<union> {j \<in> {1..A}. j mod p = p - a})
           = card {j \<in> {1..A}. j mod p = a} + card {j \<in> {1..A}. j mod p = p - a}"
    by (rule card_Un_disjoint) (use disj in auto)
  have c1: "card {j \<in> {1..A}. j mod p = a} = (A + p - a) div p"
    by (rule count_mod_eq) (use p0 ap assms(2) in auto)
  have c2: "card {j \<in> {1..A}. j mod p = p - a} = (A + a) div p"
    using count_mod_eq[OF p0 ap(3) ap(4), of A] ap(1) by simp
  show ?thesis unfolding ell_def split c c1 c2 ..
qed

lemma ell_succ_eq:
  assumes "odd p" "a + 1 \<le> mHalf p"
  shows "int (ell p A (a + 1)) = ellZ p A a + ((int A + int a + 1) div int p - (int A +
    int a) div int p)"
proof -
  have ap: "a + 1 < p" using assms unfolding mHalf_def by linarith
  have ex: "ell p A (a + 1) = (A + p - (a + 1)) div p + (A + (a + 1)) div p"
    by (rule ell_exact[OF assms(1) _ assms(2)]) simp
  have e1: "int ((A + p - (a + 1)) div p) = (int A - int a - 1) div int p + 1"
  proof -
    have "int ((A + p - (a + 1)) div p) = int (A + p - (a + 1)) div int p" by (rule zdiv_int)
    also have "int (A + p - (a + 1)) = (int A - int a - 1) + int p" using ap by simp
    also have "((int A - int a - 1) + int p) div int p = (int A - int a - 1) div int p + 1"
      using ap by simp
    finally show ?thesis .
  qed
  have e2: "int ((A + (a + 1)) div p) = (int A + int a + 1) div int p" unfolding zdiv_int
    by (simp add: algebra_simps)
  show ?thesis unfolding ex ellZ_def of_nat_add e1 e2 by linarith
qed

lemma sum_disc:
  assumes "0 < p" "m < p"
  shows "(\<Sum> a < m. ((int A + int a + 1) div int p - (int A + int a) div int p)) \<le> 1"
    and "0 \<le> (int A + int a + 1) div int p - (int A + int a) div int p"
proof -
  have tele: "(\<Sum> a < k. ((int A + int a + 1) div int p - (int A + int a) div int p)) =
    (int A + int k) div int p - int A div int p" for k
    by (induction k) (simp_all add: algebra_simps)
  show "(\<Sum> a < m. ((int A + int a + 1) div int p - (int A + int a) div int p)) \<le> 1"
    unfolding tele
    using zdiv_mono1[of "int A + int m" "int A + int p" "int p"] assms by (simp add: div_add_self2)
  show "0 \<le> (int A + int a + 1) div int p - (int A + int a) div int p"
    using zdiv_mono1[of "int A + int a" "int A + int a + 1" "int p"] assms(1) by simp
qed

lemma ell_cases:
  assumes "odd p" "1 \<le> a" "a \<le> mHalf p"
  shows "ell p A a = 2 * A div p \<or> ell p A a = 2 * A div p + 1"
proof -
  have p0: "0 < p" using assms(1) by (rule odd_pos)
  have ap: "a < p" using assms(3) p0 unfolding mHalf_def by linarith
  define u where "u = (A + p - a) div p"
  define v where "v = (A + a) div p"
  define q where "q = 2 * A div p"
  have g: "x div p * p \<le> x" "x < (x div p + 1) * p" for x
  proof -
    show "x div p * p \<le> x" by fastforce
    have e: "(x div p + 1) * p = x div p * p + p" by (simp add: algebra_simps)
    show "x < (x div p + 1) * p" unfolding e
      using mod_less_divisor[OF p0, of x] div_mult_mod_eq[of x p] by linarith
  qed
  have bu: "u * p \<le> A + p - a" "A + p - a < (u + 1) * p" unfolding u_def by (rule g)+
  have bv: "v * p \<le> A + a" "A + a < (v + 1) * p" unfolding v_def by (rule g)+
  have bq: "q * p \<le> 2 * A" "2 * A < (q + 1) * p" unfolding q_def by (rule g)+
  have s1: "(u + v) * p < (q + 2) * p" using bu bv bq ap by (simp add: algebra_simps)
  have s2: "(q + 1) * p < (u + v + 2) * p" using bu bv bq ap by (simp add: algebra_simps)
  have "u + v < q + 2" using s1 using mult_less_cancel2 by blast
  moreover have "q + 1 < u + v + 2" using s2 using mult_less_cancel2 by blast
  ultimately show ?thesis unfolding ell_exact[OF assms] u_def[symmetric] v_def[symmetric]
    q_def[symmetric] by linarith
qed

lemma card_inter_of_chain: "P \<subseteq> Q \<or> Q \<subseteq> P \<Longrightarrow>
  finite P \<Longrightarrow> finite Q \<Longrightarrow> card (P \<inter> Q) = min (card P) (card Q)"
proof -
  assume c: "P \<subseteq> Q \<or> Q \<subseteq> P" and fP: "finite P" and fQ: "finite Q"
  show ?thesis
  proof (cases "P \<subseteq> Q")
    case True
    hence "P \<inter> Q = P" "card P \<le> card Q" using card_mono[OF fQ True] by auto
    thus ?thesis by simp
  next
    case False
    hence Q: "Q \<subseteq> P" using c by simp
    hence "P \<inter> Q = Q" "card Q \<le> card P" using card_mono[OF fP Q] by auto
    thus ?thesis by (simp add: min.absorb2)
  qed
qed

lemma sum_two_lin: "(\<Sum> i < L. 2 * (of_nat i + c)) =
  of_nat L * (of_nat L - 1) + 2 * of_nat L * (c :: rat)"
  by (induction L) (simp_all add: algebra_simps)


subsection \<open>The discrete decomposition of @{text "\<gamma>_p^in"}\<close>

text \<open>The number of classes with @{text "l_K(a) = q + 1"},
  @{text "q = \<lfloor>2K/p\<rfloor>"}.\<close>
definition c1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c1 K p = card {a \<in> {1..mHalf p}. ell p K a = 2 * K div p + 1}"

lemma sum_ellK:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "(\<Sum> a = 1..mHalf p. ell p K a) = mHalf p * (2 * K div p) + c1 K p"
proof -
  have odd: "odd p" using hyp_facts[OF p h] by simp
  have e: "\<And>a. a \<in> {1..mHalf p} \<Longrightarrow>
    ell p K a = 2 * K div p + (if ell p K a = 2 * K div p + 1 then 1 else 0)"
    using ell_cases[OF odd] by fastforce
  have "(\<Sum> a = 1..mHalf p. ell p K a) = (\<Sum> a = 1..mHalf p. 2 * K div p + (if ell p K a =
    2 * K div p + 1 then 1 else 0))"
    by (rule sum.cong[OF refl]) (rule e)
  also have "\<dots> = mHalf p * (2 * K div p) + card {a \<in> {1..mHalf p}. ell p K a =
    2 * K div p + 1}"
    by (simp add: sum.distrib sum.inter_filter[symmetric])
  finally show ?thesis unfolding c1_def .
qed

lemma sum_ellK':
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "(\<Sum> a = 1..mHalf p. ell p K a) = K - K div p"
  using sum_ell[OF p] hyp_facts[OF p h] by simp

lemma c1_le: "c1 K p \<le> mHalf p"
  unfolding c1_def by (rule order_trans[OF card_mono[of "{1..mHalf p}"]]) auto

text \<open>@{text "\<epsilon>_a \<in> {0, 1}"},
  and @{text "\<epsilon>_a = 1"} exactly when the rank of @{text a} is @{text "< E"}.\<close>
lemma eps_cases: "epsIn K M p a = 0 \<or> epsIn K M p a = 1"
  by (simp add: epsIn_def)

lemma eps_iff:
  assumes p: "prime p" and h: "InnerHyp K M p" and a: "a \<in> {1..mHalf p}"
  shows "epsIn K M p a = 1 \<longleftrightarrow> int (defaultPos K p a) < Ein K M p"
proof -
  define m where "m = mHalf p"
  define A where "A = {1..m}"
  define r where "r c a \<longleftrightarrow> ell p K a < ell p K c \<or>
    (ell p K c = ell p K a \<and> c < a)" for c a
  have rk: "defaultPos K p a = card {c \<in> A. r c a}" for a
    by (simp add: defaultPos_def A_def m_def r_def)
  have irr: "\<And>x. \<not> r x x" and tr: "\<And>x y z. r x y \<Longrightarrow>
    r y z \<Longrightarrow> r x z"
    and tot: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
      x \<noteq> y \<Longrightarrow> r x y \<or> r y x"
    unfolding r_def by auto
  note RP = rank_props[of A r, OF _ irr tr tot, folded rk]
  have iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
    defaultPos K p x < defaultPos K p y \<longleftrightarrow> r x y" for x y
    using RP(1) by (simp add: A_def)
  have aA: "a \<in> A" using a by (simp add: A_def m_def)
  have "{c \<in> {1..mHalf p}. defaultPos K p c < defaultPos K p a} = {c \<in> A. r c a}"
    using iff[OF _ aA] by (auto simp: A_def m_def)
  hence "card {c \<in> {1..mHalf p}. defaultPos K p c < defaultPos K p a} = defaultPos K p a"
    using rk by simp
  thus ?thesis unfolding epsIn_def by simp
qed

lemma defaultPos_lt:
  assumes "a \<in> {1..mHalf p}" "c \<in> {1..mHalf p}" "ell p K c < ell p K a"
  shows "defaultPos K p a < defaultPos K p c"
proof -
  define m where "m = mHalf p"
  define A where "A = {1..m}"
  define r where "r c a \<longleftrightarrow> ell p K a < ell p K c \<or>
    (ell p K c = ell p K a \<and> c < a)" for c a
  have rk: "defaultPos K p a = card {c \<in> A. r c a}" for a
    by (simp add: defaultPos_def A_def m_def r_def)
  have irr: "\<And>x. \<not> r x x" and tr: "\<And>x y z. r x y \<Longrightarrow>
    r y z \<Longrightarrow> r x z"
    and tot: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
      x \<noteq> y \<Longrightarrow> r x y \<or> r y x"
    unfolding r_def by auto
  note RP = rank_props[of A r, OF _ irr tr tot, folded rk]
  have iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
    defaultPos K p x < defaultPos K p y \<longleftrightarrow> r x y" for x y
    using RP(1) by (simp add: A_def)
  have aA: "a \<in> A" and cA: "c \<in> A" using assms(1,2) by (simp_all add: A_def m_def)
  show ?thesis using iff[OF aA cA] assms(3) unfolding r_def by simp
qed

text \<open>@{text "\<Sum>_a \<epsilon>_a l_K(a) = q E + min(E, c_1)"}: the classes with
  @{text "\<epsilon> = 1"} and those with @{text "l_K = q + 1"} form a chain.\<close>
lemma sum_if_const: "finite A \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  (\<Sum> x \<in> A. if x \<in> B then c else 0) = int (card B) * (c :: int)"
  by (simp add: sum.If_cases Int_absorb1 Int_absorb2)

lemma sum_eps_ell:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "(\<Sum> a = 1..mHalf p. epsIn K M p a * int (ell p K a)) =
    int (2 * K div p) * Ein K M p + min (Ein K M p) (int (c1 K p))"
proof -
  have odd: "odd p" using hyp_facts[OF p h] by simp
  have E: "0 \<le> Ein K M p" "Ein K M p < int (mHalf p)" using TE_spec[OF p h] by auto
  define P where "P = {a \<in> {1..mHalf p}. int (defaultPos K p a) < Ein K M p}"
  define Q where "Q = {a \<in> {1..mHalf p}. ell p K a = 2 * K div p + 1}"
  have cardP: "int (card P) = Ein K M p"
  proof -
    define m where "m = mHalf p"
    define A where "A = {1..m}"
    define r where "r c a \<longleftrightarrow> ell p K a < ell p K c \<or>
      (ell p K c = ell p K a \<and> c < a)" for c a
    have rk: "defaultPos K p a = card {c \<in> A. r c a}" for a
      by (simp add: defaultPos_def A_def m_def r_def)
    have irr: "\<And>x. \<not> r x x" and tr: "\<And>x y z. r x y \<Longrightarrow>
      r y z \<Longrightarrow> r x z"
      and tot: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
        x \<noteq> y \<Longrightarrow> r x y \<or> r y x"
      unfolding r_def by auto
    note RP = rank_props[of A r, OF _ irr tr tot, folded rk]
    have cA: "card A = m" by (simp add: A_def)
    have bij: "bij_betw (defaultPos K p) A {..<m}" using RP(2) cA by (simp add: A_def)
    define En where "En = nat (Ein K M p)"
    have En: "Ein K M p = int En" "En \<le> m" using E by (auto simp: En_def m_def)
    have PE: "P = {a \<in> A. defaultPos K p a < En}" unfolding P_def A_def m_def En(1) by simp
    have "card {a \<in> A. defaultPos K p a < En} = card {..<En}"
    proof -
      have inj: "inj_on (defaultPos K p) {a \<in> A. defaultPos K p a < En}"
        using bij by (auto simp: bij_betw_def intro: inj_on_subset)
      have "defaultPos K p ` {a \<in> A. defaultPos K p a < En} = {..<En}"
      proof (intro equalityI subsetI)
        fix i assume "i \<in> {..<En}"
        hence "i \<in> {..<m}" using En by auto
        hence "i \<in> defaultPos K p ` A" using bij by (simp add: bij_betw_def)
        then obtain a where "a \<in> A" "defaultPos K p a = i" by blast
        thus "i \<in> defaultPos K p ` {a \<in> A. defaultPos K p a < En}"
          using \<open>i \<in> {..<En}\<close> by auto
      qed auto
      thus ?thesis using card_image[OF inj] by simp
    qed
    thus ?thesis unfolding PE using En by simp
  qed
  have cardQ: "card Q = c1 K p" unfolding Q_def c1_def ..
  have e: "\<And>a. a \<in> {1..mHalf p} \<Longrightarrow>
    epsIn K M p a * int (ell p K a) = (if a \<in> P then int (2 * K div p) else 0) + (if a \<in>
    P \<inter> Q then 1 else 0)"
  proof -
    fix a assume a: "a \<in> {1..mHalf p}"
    have "epsIn K M p a = 1 \<longleftrightarrow> a \<in> P" using eps_iff[OF p h a] a
      unfolding P_def by simp
    moreover have "epsIn K M p a = 0 \<or> epsIn K M p a = 1" by (rule eps_cases)
    moreover have "ell p K a = 2 * K div p \<or> ell p K a = 2 * K div p + 1"
      using ell_cases[OF odd] a by auto
    moreover have "a \<in> Q \<longleftrightarrow> ell p K a = 2 * K div p + 1" using a
      unfolding Q_def by simp
    ultimately show "epsIn K M p a * int (ell p K a) = (if a \<in>
      P then int (2 * K div p) else 0) + (if a \<in> P \<inter> Q then 1 else 0)"
      by fastforce
  qed
  have chain: "P \<subseteq> Q \<or> Q \<subseteq> P"
  proof (rule ccontr)
    assume "\<not> (P \<subseteq> Q \<or> Q \<subseteq> P)"
    then obtain c a where c: "c \<in> P" "c \<notin> Q" and a: "a \<in> Q" "a \<notin> P" by blast
    have c1: "c \<in> {1..mHalf p}" and a1: "a \<in> {1..mHalf p}" using a c unfolding P_def Q_def
      by auto
    have cq: "ell p K c = 2 * K div p" using ell_cases[OF odd, of c K] c c1 unfolding Q_def by auto
    have aq: "ell p K a = 2 * K div p + 1" using a unfolding Q_def by auto
    have "defaultPos K p a < defaultPos K p c" by (rule defaultPos_lt[OF a1 c1]) (use cq aq in simp)
    hence "a \<in> P" using c a1 unfolding P_def by auto
    thus False using a by simp
  qed
  have "(\<Sum> a = 1..mHalf p. epsIn K M p a * int (ell p K a)) =
    int (2 * K div p) * int (card P) + int (card (P \<inter> Q))"
  proof -
    have s1: "(\<Sum> a = 1..mHalf p. epsIn K M p a * int (ell p K a)) = (\<Sum> a =
      1..mHalf p. (if a \<in> P then int (2 * K div p) else 0) + (if a \<in>
      P \<inter> Q then 1 else 0))"
      using e by simp
    have Psub: "P \<subseteq> {1..mHalf p}" unfolding P_def by blast
    have PQsub: "P \<inter> Q \<subseteq> {1..mHalf p}" using Psub by blast
    note s2 = sum_if_const[OF finite_atLeastAtMost Psub, of "int (2 * K div p)"]
    note s3 = sum_if_const[OF finite_atLeastAtMost PQsub, of 1]
    show ?thesis unfolding s1 sum.distrib s2 s3 by (simp add: algebra_simps)
  qed
  note s = this
  have fin: "finite P" "finite Q" by (simp_all add: P_def Q_def)
  have m: "int (card (P \<inter> Q)) = min (Ein K M p) (int (c1 K p))"
    unfolding card_inter_of_chain[OF chain fin] using cardP cardQ by simp
  show ?thesis unfolding s m cardP ..
qed

text \<open>The sum over the rows of class @{text "a \<ge> 1"}.\<close>
lemma class_sum:
  assumes p: "prime p" and h: "InnerHyp K M p" and a: "a \<in> {1..mHalf p}"
  shows "(\<Sum> i < nat (Lin K M p a). 2 * wIn K M p a i)
           = of_int (gg (Tin K M p) (int (ell p (Nof K) a)) (int (ell p K a)) + epsIn K M p a * (2 *
             Tin K M p - int (ell p K a) - 4))"
proof -
  have a0: "a \<noteq> 0" using a by auto
  have L: "0 \<le> Lin K M p a" using Lin_nonneg[OF p h] a by auto
  have Lq: "(of_nat (nat (Lin K M p a)) :: rat) =
    of_int (Tin K M p) - 3 * of_nat (ell p (Nof K) a) + of_int (epsIn K M p a)"
    using L unfolding Lin_def bIn_def by (simp add: a0)
  have w: "\<And>i. wIn K M p a i = of_nat i + (of_int (bIn K p a) - (of_nat (ell p K a) + 4) / 2)"
    using a0 by (simp add: wIn_def)
  have "(\<Sum> i < nat (Lin K M p a). 2 * wIn K M p a i) = (\<Sum> i <
    nat (Lin K M p a). 2 * (of_nat i + (of_int (bIn K p a) - (of_nat (ell p K a) + 4) / 2)))"
    by (simp add: w)
  also have "\<dots> = of_nat (nat (Lin K M p a)) * (of_nat (nat (Lin K M p a)) - 1) + 2 *
    of_nat (nat (Lin K M p a)) * (of_int (bIn K p a) - (of_nat (ell p K a) + 4) / 2)"
    by (rule sum_two_lin)
  finally have F: "(\<Sum> i < nat (Lin K M p a). 2 * wIn K M p a i) =
    of_nat (nat (Lin K M p a)) * (of_nat (nat (Lin K M p a)) - 1)
      + 2 * of_nat (nat (Lin K M p a)) * (of_int (bIn K p a) - (of_nat (ell p K a) + 4) / 2)" .
  show ?thesis
    unfolding F Lq gg_def bIn_def using eps_cases[of K M p a] by (auto simp: algebra_simps)
qed

definition Sd :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "Sd K p T = (\<Sum> a = 1..mHalf p. gg T (int (ell p (Nof K) a)) (int (ell p K a)))"

text \<open>@{text "\<gamma>_in = 2 \<Sum>_{i <
  4M+10} w_{0,i} + [S_d(T) + E (2T - q - 4) - min(E, c_1)]"}.\<close>
lemma gamma_decomp:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "gammaIn K M p = 2 * (\<Sum> i < 4 * M + 10. wIn K M p 0 i)
           + of_int (Sd K p (Tin K M p) + Ein K M p * (2 * Tin K M p - int (2 * K div p) - 4) -
             min (Ein K M p) (int (c1 K p)))"
proof -
  have L0: "nat (Lin K M p 0) = 4 * M + 10" by (simp add: Lin_def L0_def)
  have "gammaIn K M p = 2 * (\<Sum> i < 4 * M + 10. wIn K M p 0 i) + (\<Sum> a =
    1..mHalf p. \<Sum> i < nat (Lin K M p a). 2 * wIn K M p a i)"
  proof -
    have s: "{..mHalf p} = insert 0 {1..mHalf p}" by auto
    show ?thesis unfolding gammaIn_def s using L0 by (simp add: sum_distrib_left)
  qed
  also have "(\<Sum> a = 1..mHalf p. \<Sum> i < nat (Lin K M p a). 2 * wIn K M p a i)
      = of_int (Sd K p (Tin K M p) + Ein K M p * (2 * Tin K M p - int (2 * K div p) - 4) -
        min (Ein K M p) (int (c1 K p)))"
  proof -
    have es0: "(\<Sum> a = 1..mHalf p. epsIn K M p a * (2 * Tin K M p - int (ell p K a) - 4))
        = (\<Sum> a = 1..mHalf p. epsIn K M p a) * (2 * Tin K M p - 4) - (\<Sum> a =
          1..mHalf p. epsIn K M p a * int (ell p K a))"
    proof -
      have pt: "\<And>a. epsIn K M p a * (2 * Tin K M p - int (ell p K a) - 4) =
        epsIn K M p a * (2 * Tin K M p - 4) - epsIn K M p a * int (ell p K a)"
        by (simp add: algebra_simps)
      show ?thesis unfolding pt sum_subtractf by (simp add: sum_distrib_right)
    qed
    have es: "(\<Sum> a = 1..mHalf p. epsIn K M p a * (2 * Tin K M p - int (ell p K a) - 4))
        = Ein K M p * (2 * Tin K M p - int (2 * K div p) - 4) - min (Ein K M p) (int (c1 K p))"
      unfolding es0 sum_epsIn[OF p h] sum_eps_ell[OF p h] by (simp add: algebra_simps)
    have cs: "(\<Sum> a = 1..mHalf p. \<Sum> i < nat (Lin K M p a). 2 * wIn K M p a i)
        = (\<Sum> a = 1..mHalf p. (of_int (gg (Tin K M p) (int (ell p (Nof K) a)) (int (ell p K a))
          + epsIn K M p a * (2 * Tin K M p - int (ell p K a) - 4)) :: rat))"
      using class_sum[OF p h] by simp
    have cs2: "(\<Sum> a = 1..mHalf p. (of_int (gg (Tin K M p) (int (ell p (Nof K) a)) (int (ell p K
      a)) + epsIn K M p a * (2 * Tin K M p - int (ell p K a) - 4)) :: rat))
        = of_int (Sd K p (Tin K M p) + (\<Sum> a =
          1..mHalf p. epsIn K M p a * (2 * Tin K M p - int (ell p K a) - 4)))"
      by (simp add: Sd_def of_int_sum sum.distrib)
    show ?thesis unfolding cs cs2 es by simp
  qed
  finally show ?thesis .
qed

lemma Tin_ge:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "- 1 \<le> Tin K M p"
proof -
  have "1 \<le> mHalf p" using hyp_facts[OF p h] unfolding mHalf_def by linarith
  hence "0 \<le> Lin K M p 1" by (rule Lin_nonneg[OF p h])
  moreover have "Lin K M p 1 = Tin K M p - bIn K p 1 + epsIn K M p 1" by (simp add: Lin_def)
  moreover have "0 \<le> bIn K p 1" by (simp add: bIn_def)
  moreover have "epsIn K M p 1 \<le> 1" by (simp add: epsIn_def)
  ultimately show ?thesis by linarith
qed

lemma w0_bound:
  assumes p: "prime p" and h: "InnerHyp K M p" and i: "i < 4 * M + 10"
  shows "\<bar>wIn K M p 0 i\<bar> \<le> 15 * of_nat M"
proof -
  have hf: "7 \<le> p" "odd p" "K div p < M" "Nof K div p < M" using hyp_facts[OF p h] by auto
  have M: "40 \<le> M" using h unfolding InnerHyp_def by simp
  have Tl: "- 1 \<le> Tin K M p" by (rule Tin_ge[OF p h])
  have Tu: "Tin K M p \<le> 4 * int M" by (rule Tin_le[OF p h])
  define x0 :: rat where "x0 = 2 * of_nat i + 6 * of_nat (Nof K div p) - of_nat (K div p) + 1 / 2"
  define f :: "nat \<Rightarrow> rat" where "f c =
    of_int (Zin K M p c) - (of_nat (ell p K c) + 4) / 2" for c
  define S where "S = insert x0 (f ` {1..mHalf p})"
  have w: "wIn K M p 0 i = Min S" unfolding wIn_def S_def x0_def f_def by simp
  have fin: "finite S" and ne: "S \<noteq> {}" unfolding S_def by simp_all
  have fb: "- 15 * of_nat M \<le> f c \<and> f c \<le> 15 * of_nat M" if c: "c \<in> {1..mHalf p}"
    for c
  proof -
    have lb: "ell p K c \<le> 2 * (K div p) + 2" using ell_bounds[OF hf(2)] c by auto
    have ec: "epsIn K M p c = 0 \<or> epsIn K M p c = 1" by (rule eps_cases)
    have l2q: "(of_nat (ell p K c) :: rat) \<le> 2 * of_nat M" using lb hf(3) by linarith
    have Tq1: "(- 1 :: rat) \<le> of_int (Tin K M p)" using Tl by linarith
    have Tq2: "(of_int (Tin K M p) :: rat) \<le> 4 * of_nat M" using Tu by linarith
    have eq1: "(0 :: rat) \<le> of_int (epsIn K M p c)" using ec by linarith
    have eq2: "(of_int (epsIn K M p c) :: rat) \<le> 1" using ec by linarith
    have Mq: "(40 :: rat) \<le> of_nat M" using M by linarith
    have l0: "(0 :: rat) \<le> of_nat (ell p K c)" by simp
    have "- 15 * of_nat M \<le> of_int (Tin K M p) + of_int (epsIn K M p c) - (of_nat (ell p K c) +
      4) / (2::rat)"
      using Tq1 Tq2 eq1 eq2 l0 l2q Mq by (simp add: field_simps)
    moreover have "of_int (Tin K M p) + of_int (epsIn K M p c) - (of_nat (ell p K c) + 4) /
      (2::rat) \<le> 15 * of_nat M"
      using Tq1 Tq2 eq1 eq2 l0 l2q Mq by (simp add: field_simps)
    ultimately show ?thesis unfolding f_def Zin_def of_int_add by satx
  qed
  have x0b: "- 15 * of_nat M \<le> x0 \<and> x0 \<le> 15 * of_nat M"
  proof -
    have "(of_nat (K div p) :: rat) \<le> of_nat M" and "(of_nat (Nof K div p) :: rat) \<le>
      of_nat M"
      using hf(3,4) by simp_all
    moreover have "(of_nat i :: rat) \<le> 4 * of_nat M + 10" using i by linarith
    moreover have "(40 :: rat) \<le> of_nat M" using M by simp
    ultimately show ?thesis unfolding x0_def by linarith
  qed
  have "- 15 * of_nat M \<le> Min S"
    using fin ne fb x0b unfolding S_def using Min_ge_iff by blast
  moreover have "Min S \<le> 15 * of_nat M"
  proof -
    have "Min S \<le> x0" using fin unfolding S_def by (simp add: Min_le)
    thus ?thesis using x0b by linarith
  qed
  ultimately show ?thesis unfolding w by (simp add: abs_le_iff)
qed

lemma Z0_bound:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "\<bar>2 * (\<Sum> i < 4 * M + 10. wIn K M p 0 i)\<bar> \<le> 150 * of_nat M ^ 2"
proof -
  have "\<bar>\<Sum> i < 4 * M + 10. wIn K M p 0 i\<bar> \<le> (\<Sum> i <
    4 * M + 10. 15 * of_nat M)"
    by (rule order_trans[OF sum_abs]) (rule sum_mono, rule w0_bound[OF p h], simp)
  note hs = this
  have M: "(40 :: rat) \<le> of_nat M" using h unfolding InnerHyp_def by simp
  have s: "(\<Sum> i < 4 * M + 10. (15 :: rat) * of_nat M) = (4 * of_nat M + 10) * (15 * of_nat M)"
    by simp
  have b: "\<bar>\<Sum> i < 4 * M + 10. wIn K M p 0 i\<bar> \<le>
    (4 * of_nat M + 10) * (15 * of_nat M)" using hs s by order
  have "40 * (of_nat M :: rat) \<le> of_nat M ^ 2" using M by (simp add: power2_eq_square)
  moreover have "(4 * of_nat M + 10) * (15 * of_nat M) =
    60 * of_nat M ^ 2 + 150 * (of_nat M :: rat)" by (simp add: power2_eq_square algebra_simps)
  moreover have "\<bar>2 * (\<Sum> i < 4 * M + 10. wIn K M p 0 i)\<bar> = 2 * \<bar>\<Sum> i <
    4 * M + 10. wIn K M p 0 i\<bar>" by (simp add: abs_mult)
  ultimately show ?thesis using b M by linarith
qed

text \<open>@{text "p \<Gamma>(K/p)"} in terms of the @{text z}-integral of @{text phiZ} at
  @{text "T_f = \<lfloor>2H_c K/p\<rfloor>"}.\<close>
lemma Gam_eq:
  assumes p: "prime p" and h: "InnerHyp K M p"
  defines "Tf \<equiv> floor (2 * Hc_r * (real K / real p))"
    and "s \<equiv> Hc_r * (real K / real p) - of_int (floor (2 * Hc_r * (real K / real p))) / 2"
  shows "real p * Gam_r (real K / real p)
           = real p * interval_lebesgue_integral lborel (ereal 0) (ereal (1 /
             2)) (phiZ p (Nof K) K Tf)
             + real p * s * (2 * of_int Tf - real (2 * K div p) - 4)
             - min (real p * s) (real K - real p * real (2 * K div p) / 2)"
proof -
  obtain n where K: "K = 40 * n" using h unfolding InnerHyp_def by (auto elim: dvdE)
  have pr: "0 < real p" using p by (simp add: prime_gt_0_nat)
  have N: "real (Nof K) = 3 * real n" unfolding K Nof_def by simp
  have al: "alpha_r * (real K / real p) = real (Nof K) / real p" unfolding N
    unfolding K alpha_r_def by (simp add: field_simps)
  have q: "floor (2 * (real K / real p)) = int (2 * K div p)"
  proof -
    have "2 * (real K / real p) = real (2 * K) / real p" by simp
    thus ?thesis by (simp only: floor_nat_div)
  qed
  define nn where "nn = (2 * (real K / real p) - real (2 * K div p)) / 2"
  have ph: "(\<lambda>z. (of_int Tf - 3 * ell_r (real (Nof K) / real p) z) * (of_int Tf + 3 *
    ell_r (real (Nof K) / real p) z - ell_r (real K / real p) z - 5))
            = phiZ p (Nof K) K Tf" by (rule ext) (simp add: phiZ_def)
  have G: "Gam_r (real K / real p) = interval_lebesgue_integral lborel (ereal 0) (ereal (1 /
    2)) (phiZ p (Nof K) K Tf)
             + s * (2 * of_int Tf - real (2 * K div p) - 5) + pos_r (s - nn)"
    unfolding Gam_r_def Let_def unfolding s_def[symmetric]
      unfolding Tf_def[symmetric] al q nn_def ph by simp
  have mn: "pos_r (s - nn) = s - min s nn" by (simp add: pos_r_def min_def max_def)
  have pm: "real p * min s nn = min (real p * s) (real p * nn)" using pr
    by (simp add: min_def mult_left_mono)
  have pn: "real p * nn = real K - real p * real (2 * K div p) / 2" unfolding nn_def using pr
    by (simp add: field_simps)
  show ?thesis unfolding G mn using pm pn using algebra_simps by argo
qed


subsection \<open>Discrete sum versus the integral\<close>

lemma sum_Icc_shift: "(\<Sum> a = 1..m. f a) = (\<Sum> a < (m :: nat). f (a + 1))"
proof (induction m)
  case 0
  show ?case by simp
next
  case (Suc m)
  show ?case using Suc by (simp add: sum.cl_ivl_Suc)
qed

lemma ellZ_bounds:
  assumes "0 < p" "a < p"
  shows "0 \<le> ellZ p A a \<and> ellZ p A a \<le> 2 * int (A div p) + 2"
proof -
  have ip: "0 < int p" using assms(1) by simp
  have "- 1 \<le> (int A - int a - 1) div int p"
  proof -
    have "(- int p) div int p \<le> (int A - int a - 1) div int p" using assms ip
      by (intro zdiv_mono1) simp_all
    moreover have "(- int p) div int p = - 1" using ip by (simp add: zdiv_zminus1_eq_if)
    ultimately show ?thesis by linarith
  qed
  moreover have "(int A - int a - 1) div int p \<le> int A div int p" using ip
    by (intro zdiv_mono1) simp_all
  moreover have "(int A + int a) div int p \<le> int A div int p + 1"
  proof -
    have "(int A + int a) div int p \<le> (int A + int p) div int p" using assms ip
      by (intro zdiv_mono1) simp_all
    thus ?thesis using ip by simp
  qed
  moreover have "0 \<le> (int A + int a) div int p" using ip by (simp add: pos_imp_zdiv_nonneg_iff)
  moreover have "int A div int p = int (A div p)" by (simp add: zdiv_int)
  ultimately show ?thesis unfolding ellZ_def by linarith
qed

lemma disc_01:
  assumes "0 < p"
  shows "(int A + int a + 1) div int p - (int A + int a) div int p = 0 \<or>
    (int A + int a + 1) div int p - (int A + int a) div int p = 1"
proof -
  have ip: "0 < int p" using assms(1) by simp
  have "(int A + int a) div int p \<le> (int A + int a + 1) div int p" using ip
    by (intro zdiv_mono1) simp_all
  moreover have "(int A + int a + 1) div int p \<le> (int A + int a) div int p + 1"
  proof -
    have "(int A + int a + 1) div int p \<le> (int A + int a + int p) div int p" using assms ip
      by (intro zdiv_mono1) simp_all
    thus ?thesis using ip by simp
  qed
  ultimately show ?thesis by linarith
qed

lemma gg_lip:
  assumes "40 \<le> M" "- 2 \<le> T" "T \<le> 4 * int M + 1" "0 \<le> v" "v \<le>
    2 * int M" "0 \<le> l" "l \<le> 2 * int M"
    "dv = 0 \<or> dv = 1" "dl = 0 \<or> dl = 1"
  shows "\<bar>gg T (v + dv) (l + dl) - gg T v l\<bar> \<le> 100 * int M * (dv + dl)"
proof -
  have d1: "gg T v (l + 1) - gg T v l = 3 * v - T" by (simp add: gg_def algebra_simps)
  have d2: "gg T (v + 1) l - gg T v l = 3 * l - 18 * v + 6" by (simp add: gg_def algebra_simps)
  have d3: "gg T (v + 1) (l + 1) - gg T v l = 3 * l - 15 * v - T + 9"
    by (simp add: gg_def algebra_simps)
  consider "dv = 0" "dl = 0" | "dv = 0" "dl = 1" | "dv = 1" "dl = 0" | "dv = 1" "dl = 1"
    using assms(8,9) by blast
  then show ?thesis
  proof cases
    case 1 thus ?thesis by simp
  next
    case 2 thus ?thesis using d1 assms(1-7) by (simp add: abs_le_iff)
  next
    case 3 thus ?thesis using d2 assms(1-7) by (simp add: abs_le_iff)
  next
    case 4 thus ?thesis using d3 assms(1-7) by (simp add: abs_le_iff)
  qed
qed

lemma gg_bound:
  assumes "40 \<le> M" "- 2 \<le> T" "T \<le> 4 * int M + 1" "0 \<le> v" "v \<le>
    2 * int M" "0 \<le> l" "l \<le> 2 * int M"
  shows "\<bar>gg T v l\<bar> \<le> 150 * int M ^ 2"
proof -
  have "\<bar>T - 3 * v\<bar> \<le> 11 * int M" and "\<bar>T + 3 * v - l - 5\<bar> \<le>
    13 * int M" using assms by (auto simp: abs_le_iff)
  hence "\<bar>gg T v l\<bar> \<le> (11 * int M) * (13 * int M)" unfolding gg_def abs_mult
    by (rule mult_mono) simp_all
  thus ?thesis by (simp add: power2_eq_square)
qed

text \<open>@{text "|S_d(T) - p \<integral>_0^{1/2} \<phi>_T| \<le> 100 M^2"}: per-cell comparison
  plus the last half cell.\<close>
lemma S_vs_I:
  assumes p: "prime p" and h: "InnerHyp K M p" and T: "- 2 \<le> T" "T \<le> 4 * int M + 1"
  shows "\<bar>of_int (Sd K p T) - real p * interval_lebesgue_integral lborel (ereal 0) (ereal (1 /
    2)) (phiZ p (Nof K) K T)\<bar> \<le> 100 * real M ^ 2"
proof -
  have facts: "7 \<le> p" "odd p" "2 * mHalf p + 1 = p" "K div p < M" "Nof K div p < M"
    using hyp_facts[OF p h] by auto
  have M: "40 \<le> M" using h unfolding InnerHyp_def by simp
  define m where "m = mHalf p"
  have p0: "0 < p" using facts by simp
  have mp: "m < p" unfolding m_def using facts by simp
  have I: "real p * interval_lebesgue_integral lborel (ereal 0) (ereal (1 / 2)) (phiZ p (Nof K) K T)
             = (\<Sum> a < m. of_int (gg T (ellZ p (Nof K) a) (ellZ p K a))) +
               of_int (gg T (ellZ p (Nof K) m) (ellZ p K m)) / 2"
    unfolding m_def by (rule integral_sum) (use facts in simp)
  have S: "Sd K p T = (\<Sum> a < m. gg T (int (ell p (Nof K) (a + 1))) (int (ell p K (a + 1))))"
    unfolding Sd_def m_def by (rule sum_Icc_shift)
  have cell: "\<bar>gg T (int (ell p (Nof K) (a + 1))) (int (ell p K (a + 1))) -
    gg T (ellZ p (Nof K) a) (ellZ p K a)\<bar>
                \<le> 100 * int M * (((int (Nof K) + int a + 1) div int p - (int (Nof K) +
                  int a) div int p) + ((int K + int a + 1) div int p - (int K + int a) div int p))"
    if a: "a < m" for a
  proof -
    have a1: "a + 1 \<le> mHalf p" using a unfolding m_def by simp
    have ap: "a < p" using a mp by simp
    have eN: "int (ell p (Nof K) (a + 1)) =
      ellZ p (Nof K) a + ((int (Nof K) + int a + 1) div int p - (int (Nof K) + int a) div int p)"
      by (rule ell_succ_eq[OF facts(2) a1])
    have eK: "int (ell p K (a + 1)) = ellZ p K a + ((int K + int a + 1) div int p - (int K +
      int a) div int p)"
      by (rule ell_succ_eq[OF facts(2) a1])
    have bN: "0 \<le> ellZ p (Nof K) a \<and> ellZ p (Nof K) a \<le> 2 * int (Nof K div p) + 2"
      by (rule ellZ_bounds[OF p0 ap])
    have bK: "0 \<le> ellZ p K a \<and> ellZ p K a \<le> 2 * int (K div p) + 2"
      by (rule ellZ_bounds[OF p0 ap])
    have nN: "2 * int (Nof K div p) + 2 \<le> 2 * int M" using facts(5) by simp
    have nK: "2 * int (K div p) + 2 \<le> 2 * int M" using facts(4) by simp
    show ?thesis unfolding eN eK
    proof (rule gg_lip[OF M T])
      show "0 \<le> ellZ p (Nof K) a" using bN by simp
      show "ellZ p (Nof K) a \<le> 2 * int M" using bN nN by linarith
      show "0 \<le> ellZ p K a" using bK by simp
      show "ellZ p K a \<le> 2 * int M" using bK nK by linarith
      show "(int (Nof K) + int a + 1) div int p - (int (Nof K) + int a) div int p = 0 \<or>
            (int (Nof K) + int a + 1) div int p - (int (Nof K) + int a) div int p = 1"
              by (rule disc_01[OF p0])
      show "(int K + int a + 1) div int p - (int K + int a) div int p = 0 \<or>
            (int K + int a + 1) div int p - (int K + int a) div int p = 1" by (rule disc_01[OF p0])
    qed
  qed
  have diff: "\<bar>Sd K p T - (\<Sum> a < m. gg T (ellZ p (Nof K) a) (ellZ p K a))\<bar> \<le>
    200 * int M"
  proof -
    define dN where "dN a = (int (Nof K) + int a + 1) div int p - (int (Nof K) + int a) div int p"
      for a
    define dK where "dK a = (int K + int a + 1) div int p - (int K + int a) div int p" for a
    have "\<bar>Sd K p T - (\<Sum> a < m. gg T (ellZ p (Nof K) a) (ellZ p K a))\<bar>
        = \<bar>\<Sum> a < m. (gg T (int (ell p (Nof K) (a + 1))) (int (ell p K (a + 1))) -
          gg T (ellZ p (Nof K) a) (ellZ p K a))\<bar>"
      unfolding S sum_subtractf ..
    also have "\<dots> \<le> (\<Sum> a <
      m. \<bar>gg T (int (ell p (Nof K) (a + 1))) (int (ell p K (a + 1))) -
      gg T (ellZ p (Nof K) a) (ellZ p K a)\<bar>)"
      by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum> a < m. 100 * int M * (dN a + dK a))"
      unfolding dN_def dK_def by (rule sum_mono) (rule cell, simp)
    also have "\<dots> = 100 * int M * ((\<Sum> a < m. dN a) + (\<Sum> a < m. dK a))"
      by (simp add: distrib_left sum.distrib sum_distrib_left)
    also have "\<dots> \<le> 100 * int M * (1 + 1)"
    proof -
      have "(\<Sum> a < m. dN a) \<le> 1" unfolding dN_def by (rule sum_disc(1)[OF p0 mp])
      moreover have "(\<Sum> a < m. dK a) \<le> 1" unfolding dK_def by (rule sum_disc(1)[OF p0 mp])
      ultimately show ?thesis by (intro mult_left_mono) simp_all
    qed
    finally show ?thesis by simp
  qed
  have last: "\<bar>gg T (ellZ p (Nof K) m) (ellZ p K m)\<bar> \<le> 150 * int M ^ 2"
  proof -
    have bN: "0 \<le> ellZ p (Nof K) m \<and> ellZ p (Nof K) m \<le> 2 * int (Nof K div p) + 2"
      by (rule ellZ_bounds[OF p0 mp])
    have bK: "0 \<le> ellZ p K m \<and> ellZ p K m \<le> 2 * int (K div p) + 2"
      by (rule ellZ_bounds[OF p0 mp])
    have nN: "2 * int (Nof K div p) + 2 \<le> 2 * int M" using facts(5) by simp
    have nK: "2 * int (K div p) + 2 \<le> 2 * int M" using facts(4) by simp
    show ?thesis by (rule gg_bound[OF M T]) (use bN bK nN nK in linarith)+
  qed
  have "\<bar>of_int (Sd K p T) - (\<Sum> a <
    m. (of_int (gg T (ellZ p (Nof K) a) (ellZ p K a)) :: real))\<bar> \<le> 200 * real M"
  proof -
    have "real_of_int \<bar>Sd K p T - (\<Sum> a <
      m. gg T (ellZ p (Nof K) a) (ellZ p K a))\<bar> \<le> real_of_int (200 * int M)"
      using diff by (simp only: of_int_le_iff)
    thus ?thesis by (simp add: of_int_sum)
  qed
  moreover have "\<bar>(of_int (gg T (ellZ p (Nof K) m) (ellZ p K m)) :: real)\<bar> \<le>
    150 * real M ^ 2"
  proof -
    have "real_of_int \<bar>gg T (ellZ p (Nof K) m) (ellZ p K m)\<bar> \<le>
      real_of_int (150 * int M ^ 2)"
      using last by (simp only: of_int_le_iff)
    thus ?thesis by simp
  qed
  moreover have "40 \<le> real M" using M by simp
  hence "200 * real M \<le> 25 * real M ^ 2" by (simp add: power2_eq_square)
  ultimately show ?thesis unfolding I using abs_le_iff by linarith
qed


subsection \<open>The comparison functions\<close>

definition Dd :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> real \<Rightarrow> real"
  where
  "Dd K p T E = of_int (Sd K p T) + E * (2 * of_int T - real (2 * K div p) - 4) -
    min E (real (c1 K p))"

definition Cc :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> real \<Rightarrow> real"
  where
  "Cc K p T \<sigma> = real p * interval_lebesgue_integral lborel (ereal 0) (ereal (1 /
    2)) (phiZ p (Nof K) K T)
                 + \<sigma> * (2 * of_int T - real (2 * K div p) - 4) - min \<sigma> (real K -
                   real p * real (2 * K div p) / 2)"

lemma Dd_trans:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "Dd K p T (real (mHalf p)) = Dd K p (T + 1) 0"
proof -
  have s: "(\<Sum> a = 1..mHalf p. ell p K a) = mHalf p * (2 * K div p) + c1 K p"
    by (rule sum_ellK[OF p h])
  have c: "c1 K p \<le> mHalf p" by (rule c1_le)
  have e: "Sd K p (T + 1) = Sd K p T + int (mHalf p) * (2 * T - 4) - int (mHalf p * (2 * K div p) +
    c1 K p)"
  proof -
    have g: "gg (T + 1) v l = gg T v l + (2 * T - 4) - l" for v l
      by (simp add: gg_def algebra_simps)
    show ?thesis unfolding Sd_def s[symmetric] g by (simp add: sum.distrib sum_subtractf of_nat_sum)
  qed
  show ?thesis
    unfolding Dd_def e using c by (simp add: min_def algebra_simps)
qed

lemma q_le:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "2 * K div p \<le> 2 * M"
proof -
  have KpM: "K < p * M" using h unfolding InnerHyp_def by simp
  have p0: "0 < p" using prime_gt_0_nat[OF p] .
  have "2 * K < (2 * M) * p" using KpM by (simp add: algebra_simps)
  hence "2 * K div p < 2 * M" using p0 by (simp add: div_less_iff_less_mult)
  thus ?thesis by simp
qed

lemma slope_bound:
  assumes p: "prime p" and h: "InnerHyp K M p" and T: "- 2 \<le> T" "T \<le> 4 * int M + 1"
  shows "\<bar>2 * of_int T - real (2 * K div p) - 4\<bar> \<le> 11 * real M"
  using q_le[OF p h] T h unfolding InnerHyp_def by (auto simp: abs_le_iff)

lemma Dd_lip:
  assumes p: "prime p" and h: "InnerHyp K M p" and T: "- 2 \<le> T" "T \<le> 4 * int M + 1"
  shows "\<bar>Dd K p T E1 - Dd K p T E2\<bar> \<le> \<bar>E1 - E2\<bar> * (11 * real M + 1)"
proof -
  have s: "\<bar>2 * of_int T - real (2 * K div p) - 4\<bar> \<le> 11 * real M"
    by (rule slope_bound[OF p h T])
  have m: "\<bar>min E1 (real (c1 K p)) - min E2 (real (c1 K p))\<bar> \<le> \<bar>E1 - E2\<bar>"
    using min_def abs_le_iff by linarith
  have e: "Dd K p T E1 - Dd K p T E2 = (E1 - E2) * (2 * of_int T - real (2 * K div p) - 4) -
    (min E1 (real (c1 K p)) - min E2 (real (c1 K p)))"
    unfolding Dd_def by (simp add: algebra_simps)
  have "\<bar>(E1 - E2) * (2 * of_int T - real (2 * K div p) - 4)\<bar> \<le>
    \<bar>E1 - E2\<bar> * (11 * real M)"
    unfolding abs_mult by (rule mult_left_mono[OF s]) simp
  thus ?thesis unfolding e using m abs_triangle_ineq4[of "(E1 - E2) * (2 * of_int T - real (2 *
    K div p) - 4)"
      "min E1 (real (c1 K p)) - min E2 (real (c1 K p))"] using algebra_simps by argo
qed

lemma c1_close:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "\<bar>real (c1 K p) - (real K - real p * real (2 * K div p) / 2)\<bar> \<le> 1"
proof -
  have facts: "2 * mHalf p + 1 = p" "7 \<le> p" using hyp_facts[OF p h] by auto
  have s: "mHalf p * (2 * K div p) + c1 K p = K - K div p"
    using sum_ellK[OF p h] sum_ellK'[OF p h] by simp
  have q: "2 * (K div p) \<le> 2 * K div p" "2 * K div p \<le> 2 * (K div p) + 1"
  proof -
    have p0: "0 < p" using facts by simp
    have g1: "K div p * p \<le> K" by fastforce
    have g2: "K < (K div p + 1) * p"
    proof -
      have e: "(K div p + 1) * p = K div p * p + p" by (simp add: algebra_simps)
      show ?thesis unfolding e using mod_less_divisor[OF p0, of K] div_mult_mod_eq[of K p]
        by linarith
    qed
    show "2 * (K div p) \<le> 2 * K div p" using g1 p0 by (simp add: less_eq_div_iff_mult_less_eq)
    have "2 * K < (2 * (K div p) + 2) * p" using g2 by (simp add: algebra_simps)
    hence "2 * K div p < 2 * (K div p) + 2" using p0 by (simp add: div_less_iff_less_mult)
    thus "2 * K div p \<le> 2 * (K div p) + 1" by simp
  qed
  have kk: "K div p \<le> K" by (rule div_le_dividend)
  have c: "real (c1 K p) = real K - real (K div p) - real (mHalf p) * real (2 * K div p)"
  proof -
    have c0: "c1 K p = (K - K div p) - mHalf p * (2 * K div p)" using s by linarith
    have le: "mHalf p * (2 * K div p) \<le> K - K div p" using s by linarith
    show ?thesis unfolding c0 of_nat_diff[OF le] of_nat_diff[OF kk] by simp
  qed
  have pr: "real p = 2 * real (mHalf p) + 1" using facts(1)
    by (metis of_nat_1 of_nat_add of_nat_mult of_nat_numeral)
  have "2 * real (K div p) \<le> real (2 * K div p)" "real (2 * K div p) \<le>
    2 * real (K div p) + 1" using q by simp_all
  thus ?thesis unfolding c pr by (simp add: abs_le_iff algebra_simps)
qed

lemma Dd_Cc:
  assumes p: "prime p" and h: "InnerHyp K M p" and T: "- 2 \<le> T" "T \<le> 4 * int M + 1"
  shows "\<bar>Dd K p T E - Cc K p T \<sigma>\<bar> \<le>
    100 * real M ^ 2 + \<bar>E - \<sigma>\<bar> * (11 * real M + 1) + 1"
proof -
  have s: "\<bar>2 * of_int T - real (2 * K div p) - 4\<bar> \<le> 11 * real M"
    by (rule slope_bound[OF p h T])
  have SI: "\<bar>of_int (Sd K p T) - real p *
    interval_lebesgue_integral lborel (ereal 0) (ereal (1 / 2)) (phiZ p (Nof K) K T)\<bar> \<le>
    100 * real M ^ 2"
    by (rule S_vs_I[OF p h T])
  have "\<bar>real (c1 K p) - (real K - real p * real (2 * K div p) / 2)\<bar> \<le> 1"
    by (rule c1_close[OF p h])
  hence m: "\<bar>min E (real (c1 K p)) - min \<sigma> (real K - real p * real (2 * K div p) /
    2)\<bar> \<le> \<bar>E - \<sigma>\<bar> + 1"
    using min_def abs_le_iff by argo
  have e: "Dd K p T E - Cc K p T \<sigma>
      = (of_int (Sd K p T) - real p * interval_lebesgue_integral lborel (ereal 0) (ereal (1 /
        2)) (phiZ p (Nof K) K T))
        + (E - \<sigma>) * (2 * of_int T - real (2 * K div p) - 4)
        - (min E (real (c1 K p)) - min \<sigma> (real K - real p * real (2 * K div p) / 2))"
    unfolding Dd_def Cc_def by (simp add: algebra_simps)
  have a: "\<bar>(E - \<sigma>) * (2 * of_int T - real (2 * K div p) - 4)\<bar> \<le>
    \<bar>E - \<sigma>\<bar> * (11 * real M)"
    unfolding abs_mult by (rule mult_left_mono[OF s]) simp
  have M0: "0 \<le> \<bar>E - \<sigma>\<bar>" by simp
  show ?thesis unfolding e using a m SI M0 by (simp add: abs_le_iff algebra_simps)
qed


subsection \<open>Assembly\<close>

lemma gamma_real:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "of_rat (gammaIn K M p) = of_rat (2 * (\<Sum> i <
    4 * M + 10. wIn K M p 0 i)) + Dd K p (Tin K M p) (of_int (Ein K M p))"
  unfolding gamma_decomp[OF p h] Dd_def of_rat_add of_rat_of_int_eq
  by (simp add: of_int_min)

text \<open>The fill relation: @{text "mT + E = m \<cdot> 2H_c K/p + \<Delta>"} with
  @{text "|\<Delta>| \<le> 8M"}.\<close>
lemma fill_rel:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "\<bar>(real (mHalf p) * of_int (Tin K M p) + of_int (Ein K M p)) - real (mHalf p) * (2 *
    Hc_r * (real K / real p))\<bar> \<le> 8 * real M"
proof -
  have facts: "7 \<le> p" "2 * mHalf p + 1 = p" "Nof K div p < M" using hyp_facts[OF p h] by auto
  have TE: "int (mHalf p) * Tin K M p + Ein K M p = rhs44 K M p" using TE_spec[OF p h] by simp
  obtain n where K: "K = 40 * n" using h unfolding InnerHyp_def by (auto elim: dvdE)
  have M: "40 \<le> M" and KpM: "K < p * M" using h unfolding InnerHyp_def by auto
  have hh: "hof K = 37 * n" and hN: "Nof K = 3 * n" unfolding K hof_def Nof_def by simp_all
  have pr: "real p = 2 * real (mHalf p) + 1" using facts(2)
    by (metis of_nat_1 of_nat_add of_nat_mult of_nat_numeral)
  have p0: "0 < real p" using facts(1) by simp
  have lhs: "real (mHalf p) * of_int (Tin K M p) + of_int (Ein K M p) =
    37 * real n - (4 * real M + 10) + 3 * (3 * real n - real (3 * n div p))"
  proof -
    have "real_of_int (int (mHalf p) * Tin K M p + Ein K M p) = real_of_int (rhs44 K M p)" using TE
      by simp
    thus ?thesis unfolding rhs44_def L0_def hh hN by simp
  qed
  have mv: "real (mHalf p) * (2 * Hc_r * (real K / real p)) = 46 * real n - 46 * real n / real p"
    unfolding K Hc_r_def using pr p0 by (simp add: field_simps)
  have "46 * real n / real p \<le> 46 * real M / 40"
  proof -
    have "real (40 * n) < real (p * M)" using KpM unfolding K by (simp only: of_nat_less_iff)
    hence "40 * real n < real p * real M" by simp
    thus ?thesis using p0 by (simp add: field_simps)
  qed
  moreover have "0 \<le> 46 * real n / real p" using p0 by simp
  moreover have "real (3 * n div p) \<le> real M" and "0 \<le> real (3 * n div p)"
    using facts(3) hN by simp_all
  moreover have "(40 :: real) \<le> real M" using M by linarith
  ultimately show ?thesis
    unfolding lhs mv using p0
    using abs_le_iff by argo
qed

lemma m_large:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "100 * real M \<le> real (mHalf p)"
proof -
  have "200 * M < p" using innerHyp_bounds[OF h] by simp
  moreover have "2 * mHalf p + 1 = p" using hyp_facts[OF p h] by simp
  ultimately have "100 * M \<le> mHalf p" by linarith
  thus ?thesis by (simp only: of_nat_le_iff[symmetric] of_nat_mult of_nat_numeral)
qed

text \<open>@{text "|\<gamma>_in - p \<Gamma>(K/p)| \<le> 1000 M^2"}:
  @{text "T_f \<in> {T - 1, T, T + 1}"} and three cases.\<close>
theorem gamma_bound:
  assumes p: "prime p" and h: "InnerHyp K M p"
  shows "\<bar>of_rat (gammaIn K M p) - real p * Gam_r (real K / real p)\<bar> \<le>
    1000 * real M ^ 2"
proof -
  have facts: "7 \<le> p" "2 * mHalf p + 1 = p" using hyp_facts[OF p h] by auto
  have M: "40 \<le> M" using h unfolding InnerHyp_def by simp
  have Mr: "40 \<le> real M" using M by simp
  have M2: "40 * real M \<le> real M ^ 2" using Mr by (simp add: power2_eq_square)
  have Tl: "- 1 \<le> Tin K M p" by (rule Tin_ge[OF p h])
  have Tu: "Tin K M p \<le> 4 * int M" by (rule Tin_le[OF p h])
  have E: "0 \<le> Ein K M p" "Ein K M p < int (mHalf p)" using TE_spec[OF p h] by auto
  have Z: "\<bar>of_rat (2 * (\<Sum> i < 4 * M + 10. wIn K M p 0 i))\<bar> \<le> 150 * real M ^ 2"
  proof -
    have "of_rat \<bar>2 * (\<Sum> i < 4 * M + 10. wIn K M p 0 i)\<bar> \<le>
      (of_rat (150 * of_nat M ^ 2) :: real)"
      using Z0_bound[OF p h] by (simp only: of_rat_less_eq)
    note hz = this
    have e: "(of_rat (150 * of_nat M ^ 2) :: real) = 150 * real M ^ 2"
      by (simp add: of_rat_mult of_rat_power)
    have e2: "\<bar>(of_rat (2 * (\<Sum> i < 4 * M + 10. wIn K M p 0 i)) :: real)\<bar> =
      of_rat \<bar>2 * (\<Sum> i < 4 * M + 10. wIn K M p 0 i)\<bar>" by (metis abs_of_rat)
    show ?thesis using hz unfolding e e2 by satx
  qed
  define m where "m = real (mHalf p)"
  define v where "v = 2 * Hc_r * (real K / real p)"
  define T where "T = Tin K M p"
  define E' where "E' = (of_int (Ein K M p) :: real)"
  define Tf where "Tf = floor v"
  define \<sigma> where "\<sigma> = (2 * m + 1) * (v - of_int Tf) / 2"
  define Zr :: real where "Zr = of_rat (2 * (\<Sum> i < 4 * M + 10. wIn K M p 0 i))"
  have pr: "real p = 2 * m + 1" unfolding m_def using facts(2)
    by (metis of_nat_1 of_nat_add of_nat_mult of_nat_numeral)
  have G: "real p * Gam_r (real K / real p) = Cc K p Tf \<sigma>"
  proof -
    have g: "real p * Gam_r (real K / real p)
           = real p * interval_lebesgue_integral lborel (ereal 0) (ereal (1 /
             2)) (phiZ p (Nof K) K Tf)
             + real p * (Hc_r * (real K / real p) - of_int Tf / 2) * (2 * of_int Tf - real (2 *
               K div p) - 4)
             - min (real p * (Hc_r * (real K / real p) - of_int Tf / 2)) (real K - real p *
               real (2 * K div p) / 2)"
      using Gam_eq[OF p h] unfolding Tf_def v_def .
    have ps: "real p * (Hc_r * (real K / real p) - of_int Tf / 2) = \<sigma>"
      unfolding \<sigma>_def v_def pr[symmetric] by (simp add: algebra_simps)
    show ?thesis unfolding g ps Cc_def ..
  qed
  have decomp: "of_rat (gammaIn K M p) - real p * Gam_r (real K / real p) =
    Zr + (Dd K p T E' - Cc K p Tf \<sigma>)"
    unfolding G Zr_def T_def E'_def gamma_real[OF p h] by simp
  have fill: "\<bar>(m * of_int T + E') - m * v\<bar> \<le> 8 * real M"
    unfolding m_def T_def E'_def v_def by (rule fill_rel[OF p h])
  have ml: "100 * real M \<le> m" unfolding m_def by (rule m_large[OF p h])
  have E0: "0 \<le> E'" and Em: "E' < m" unfolding E'_def m_def using E by simp_all
  have f1: "of_int Tf \<le> v" and f2: "v < of_int Tf + 1" unfolding Tf_def by simp_all
  have Tf_range: "Tf = T \<or> Tf = T + 1 \<or> Tf = T - 1"
  proof -
    have fl1: "m * (of_int T - v) + E' \<le> 8 * real M"
      using fill by (simp add: abs_le_iff algebra_simps)
    have fl2: "- (8 * real M) \<le> m * (of_int T - v) + E'"
      using fill by (simp add: abs_le_iff algebra_simps)
    have m0: "0 \<le> m" using ml Mr by linarith
    have "Tf \<le> T + 1"
    proof (rule ccontr)
      assume "\<not> Tf \<le> T + 1"
      hence "T + 2 \<le> Tf" by simp
      hence "real_of_int (T + 2) \<le> of_int Tf" by (simp only: of_int_le_iff)
      hence "real_of_int T + 2 \<le> of_int Tf" by simp
      hence "2 \<le> v - of_int T" using f1 by linarith
      hence "m * 2 \<le> m * (v - of_int T)" by (rule mult_left_mono[OF _ m0])
      thus False using fl2 Em ml Mr by (simp add: algebra_simps)
    qed
    moreover have "T - 1 \<le> Tf"
    proof (rule ccontr)
      assume "\<not> T - 1 \<le> Tf"
      hence "Tf \<le> T - 2" by simp
      hence "real_of_int Tf \<le> of_int (T - 2)" by (simp only: of_int_le_iff)
      hence "real_of_int Tf \<le> of_int T - 2" by simp
      hence "1 \<le> of_int T - v" using f2 by linarith
      hence "m * 1 \<le> m * (of_int T - v)" by (rule mult_left_mono[OF _ m0])
      thus False using fl1 E0 ml Mr by (simp add: algebra_simps)
    qed
    ultimately show ?thesis by linarith
  qed
  have main: "\<bar>Dd K p T E' - Cc K p Tf \<sigma>\<bar> \<le> 850 * real M ^ 2"
    using Tf_range
  proof (elim disjE)
    assume e: "Tf = T"
    have c: "\<bar>Dd K p T E' - Cc K p T \<sigma>\<bar> \<le>
      100 * real M ^ 2 + \<bar>E' - \<sigma>\<bar> * (11 * real M + 1) + 1"
      by (rule Dd_Cc[OF p h]) (use Tl Tu T_def in linarith)+
    have Es: "\<bar>E' - \<sigma>\<bar> \<le> 8 * real M + 1"
    proof -
      have id: "E' - \<sigma> = ((m * of_int T + E') - m * v) - (v - of_int T) / 2"
        unfolding \<sigma>_def e by (simp add: algebra_simps field_simps)
      have r: "0 \<le> v - of_int T" "v - of_int T < 1" using f1 f2 unfolding e by simp_all
      show ?thesis unfolding id using fill r abs_le_iff by argo
    qed
    have "\<bar>E' - \<sigma>\<bar> * (11 * real M + 1) \<le> (8 * real M + 1) * (11 * real M + 1)"
      by (rule mult_right_mono[OF Es]) (use Mr in simp)
    moreover have "(8 * real M + 1) * (11 * real M + 1) = 88 * real M ^ 2 + 19 * real M + 1"
      by (simp add: algebra_simps power2_eq_square)
    ultimately show ?thesis unfolding e using c M2 Mr by linarith
  next
    assume e: "Tf = T + 1"
    have lip: "\<bar>Dd K p T E' - Dd K p T m\<bar> \<le> \<bar>E' - m\<bar> * (11 * real M + 1)"
      by (rule Dd_lip[OF p h]) (use Tl Tu T_def in linarith)+
    have tr: "Dd K p T m = Dd K p (T + 1) 0" unfolding m_def by (rule Dd_trans[OF p h])
    have c: "\<bar>Dd K p (T + 1) 0 - Cc K p (T + 1) \<sigma>\<bar> \<le>
      100 * real M ^ 2 + \<bar>0 - \<sigma>\<bar> * (11 * real M + 1) + 1"
      by (rule Dd_Cc[OF p h]) (use Tl Tu T_def in linarith)+
    have mE: "m - E' \<le> 8 * real M"
    proof -
      have vt: "of_int T + 1 \<le> v" using f1 unfolding e by simp
      have m0: "0 \<le> m" using ml Mr by linarith
      have "m * (of_int T + 1) \<le> m * v" by (rule mult_left_mono[OF vt m0])
      thus ?thesis using fill by (simp add: abs_le_iff algebra_simps)
    qed
    have s0: "0 \<le> \<sigma>" and s1: "\<sigma> \<le> 12 * real M"
    proof -
      have r: "0 \<le> v - of_int Tf" "v - of_int Tf < 1" using f1 f2 by simp_all
      have m0: "0 \<le> m" using ml Mr by linarith
      show "0 \<le> \<sigma>" unfolding \<sigma>_def using r m0 by simp
      have mm: "m * (v - of_int Tf) \<le> 8 * real M"
      proof -
        have "m * (v - of_int Tf) = m * v - m * (of_int T + 1)" unfolding e
          by (simp add: algebra_simps)
        thus ?thesis using fill Em by (simp add: abs_le_iff algebra_simps)
      qed
      have "\<sigma> = m * (v - of_int Tf) + (v - of_int Tf) / 2" unfolding \<sigma>_def
        by (simp add: field_simps)
      thus "\<sigma> \<le> 12 * real M" using mm r Mr by argo
    qed
    have eq: "Dd K p T E' - Cc K p (T + 1) \<sigma> =
      (Dd K p T E' - Dd K p T m) + (Dd K p (T + 1) 0 - Cc K p (T + 1) \<sigma>)"
      unfolding tr by simp
    have em: "\<bar>E' - m\<bar> \<le> 8 * real M" using mE Em by (simp add: abs_le_iff)
    have a: "\<bar>E' - m\<bar> * (11 * real M + 1) \<le> 8 * real M * (11 * real M + 1)"
      by (rule mult_right_mono[OF em]) (use Mr in simp)
    have s': "\<bar>0 - \<sigma>\<bar> \<le> 12 * real M" using s0 s1 by simp
    have b: "\<bar>0 - \<sigma>\<bar> * (11 * real M + 1) \<le> 12 * real M * (11 * real M + 1)"
      by (rule mult_right_mono[OF s']) (use Mr in simp)
    have c2: "8 * real M * (11 * real M + 1) + 12 * real M * (11 * real M + 1) =
      220 * real M ^ 2 + 20 * real M"
      by (simp add: algebra_simps power2_eq_square)
    have t: "\<bar>(Dd K p T E' - Dd K p T m) + (Dd K p (T + 1) 0 - Cc K p (T + 1) \<sigma>)\<bar>
        \<le> \<bar>Dd K p T E' - Dd K p T m\<bar> + \<bar>Dd K p (T + 1) 0 - Cc K p (T +
          1) \<sigma>\<bar>" by (rule abs_triangle_ineq)
    show ?thesis unfolding e eq using t lip c a b c2 M2 Mr by linarith
  next
    assume e: "Tf = T - 1"
    have lip: "\<bar>Dd K p T E' - Dd K p T 0\<bar> \<le> \<bar>E' - 0\<bar> * (11 * real M + 1)"
      by (rule Dd_lip[OF p h]) (use Tl Tu T_def in linarith)+
    have tr: "Dd K p (T - 1) m = Dd K p T 0" using Dd_trans[OF p h, of "T - 1"] unfolding m_def
      by simp
    have c: "\<bar>Dd K p (T - 1) m - Cc K p (T - 1) \<sigma>\<bar> \<le>
      100 * real M ^ 2 + \<bar>m - \<sigma>\<bar> * (11 * real M + 1) + 1"
      by (rule Dd_Cc[OF p h]) (use Tl Tu T_def in linarith)+
    have E8: "E' \<le> 8 * real M"
    proof -
      have vt: "v \<le> of_int T" using f2 unfolding e by simp
      have m0: "0 \<le> m" using ml Mr by linarith
      have "m * v \<le> m * of_int T" by (rule mult_left_mono[OF vt m0])
      thus ?thesis using fill by (simp add: abs_le_iff algebra_simps)
    qed
    have ms: "\<bar>m - \<sigma>\<bar> \<le> 12 * real M"
    proof -
      have r: "0 < of_int T - v" "of_int T - v \<le> 1" using f1 f2 unfolding e by simp_all
      have m0: "0 \<le> m" using ml Mr by linarith
      have id: "m - \<sigma> = m * (of_int T - v) - (1 - (of_int T - v)) / 2"
        unfolding \<sigma>_def e by (simp add: algebra_simps field_simps)
      have "m * (of_int T - v) \<le> 8 * real M" using fill E0
        by (simp add: abs_le_iff algebra_simps)
      moreover have "0 \<le> m * (of_int T - v)" using r m0 by simp
      ultimately show ?thesis unfolding id using r Mr abs_le_iff by argo
    qed
    have eq: "Dd K p T E' - Cc K p (T - 1) \<sigma> =
      (Dd K p T E' - Dd K p T 0) + (Dd K p (T - 1) m - Cc K p (T - 1) \<sigma>)"
      unfolding tr by simp
    have em: "\<bar>E' - 0\<bar> \<le> 8 * real M" using E0 E8 by simp
    have a: "\<bar>E' - 0\<bar> * (11 * real M + 1) \<le> 8 * real M * (11 * real M + 1)"
      by (rule mult_right_mono[OF em]) (use Mr in simp)
    have b: "\<bar>m - \<sigma>\<bar> * (11 * real M + 1) \<le> 12 * real M * (11 * real M + 1)"
      by (rule mult_right_mono[OF ms]) (use Mr in simp)
    have c2: "8 * real M * (11 * real M + 1) + 12 * real M * (11 * real M + 1) =
      220 * real M ^ 2 + 20 * real M"
      by (simp add: algebra_simps power2_eq_square)
    have t: "\<bar>(Dd K p T E' - Dd K p T 0) + (Dd K p (T - 1) m - Cc K p (T - 1) \<sigma>)\<bar>
        \<le> \<bar>Dd K p T E' - Dd K p T 0\<bar> + \<bar>Dd K p (T - 1) m - Cc K p (T -
          1) \<sigma>\<bar>" by (rule abs_triangle_ineq)
    show ?thesis unfolding e eq using t lip c a b c2 M2 Mr by linarith
  qed
  show ?thesis
    unfolding decomp
    using abs_triangle_ineq[of Zr "Dd K p T E' - Cc K p Tf \<sigma>"] Z[folded Zr_def] main
      by linarith
qed


text \<open>Lemma 5.7 with @{text "C(M) = 1000 M^2"}.\<close>
theorem gammaIn_uniform_estimate:
  assumes "40 \<le> M"
  shows "\<exists>Cst. \<forall>K p. prime p \<longrightarrow> InnerHyp K M p \<longrightarrow>
           \<bar>of_rat (gammaIn K M p) - real p * Gam_r (real K / real p)\<bar> \<le> Cst \<and>
           \<bar>of_int (vpS K p) - real p * Nfun_r (real K / real p)\<bar> \<le> Cst"
proof (intro exI[of _ "1000 * real M ^ 2"] allI impI conjI)
  fix K p assume p: "prime p" and h: "InnerHyp K M p"
  show "\<bar>of_rat (gammaIn K M p) - real p * Gam_r (real K / real p)\<bar> \<le>
    1000 * real M ^ 2" by (rule gamma_bound[OF p h])
  have "4 * real M \<le> 1000 * real M ^ 2"
  proof -
    have Mr: "40 \<le> real M" using assms by simp
    have "40 * real M \<le> real M ^ 2" using Mr by (simp add: power2_eq_square)
    thus ?thesis using Mr by linarith
  qed
  thus "\<bar>of_int (vpS K p) - real p * Nfun_r (real K / real p)\<bar> \<le> 1000 * real M ^ 2"
    using vpS_bound[OF p h] by linarith
qed


end




