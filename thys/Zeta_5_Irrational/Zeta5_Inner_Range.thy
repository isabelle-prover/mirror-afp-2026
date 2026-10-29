(*  Title:   Zeta5_Inner_Range.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Inner_Range
  imports Zeta5_Small_Primes Zeta5_Pole_Distribution Polynomial_Taylor_Shift Unimodular_Determinants
begin

section \<open>The inner range: Proposition 4.1\<close>

text \<open>Section 4.1 of the paper: the inner basis,
  extraction of powers of \<open>p\<close> from \<open>g(c + p z)\<close>, the
  entry bounds (4.2) and (4.3), and the unimodularity of the inner Gram matrix (Proposition 4.1,
  @{text DeltaK_vpGge_inner}).  Lean theories @{text Section4}, @{text InnerBasis},
    @{text InnerEntries},
  @{text InnerFinal}.\<close>

subsection \<open>Section 4.1 The inner range\<close>

text \<open>(4.1): the inner range.\<close>
definition InnerHyp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "InnerHyp K M p \<longleftrightarrow> 40 \<le> M \<and> 40 dvd K \<and> 0 < K \<and>
    200 * M ^ 2 \<le> K \<and> K < p * M \<and> 3 * p \<le> K"

text \<open>Under (4.1): @{text "p > 200M"} and @{text "p^2 > 5K"}.\<close>
lemma innerHyp_bounds:
  assumes "InnerHyp K M p"
  shows "200 * M < p \<and> 5 * K < p ^ 2"
proof -
  have hM: "40 \<le> M" and hK: "200 * M ^ 2 \<le> K" and hp: "K < p * M"
    using assms by (auto simp: InnerHyp_def)
  have "200 * M * M < p * M" using le_less_trans[OF hK hp]
    by (simp only: power2_eq_square mult.assoc)
  hence h1: "200 * M < p" using hM by simp
  have "5 * K < p * (5 * M)" using hp by simp
  also have "\<dots> \<le> p * p" using h1 by (auto intro: mult_le_mono2)
  finally show ?thesis using h1 by (simp add: power2_eq_square)
qed

text \<open>(4.4): @{text "0 \<le> E < m"} and @{text "mT + E = h - L_0 + 3(N - m_N)"}.\<close>
lemma TE_spec:
  assumes "prime p" "InnerHyp K M p"
  shows "0 \<le> Ein K M p \<and> Ein K M p < int (mHalf p) \<and>
    int (mHalf p) * Tin K M p + Ein K M p = rhs44 K M p"
proof -
  have "8000 < p" using innerHyp_bounds[OF assms(2)] assms(2) by (auto simp: InnerHyp_def)
  hence "0 < mHalf p" by (simp add: mHalf_def)
  hence "0 < int (mHalf p)" by simp
  thus ?thesis unfolding Ein_def Tin_def using pos_mod_sign pos_mod_bound mult_div_mod_eq
    by presburger
qed

text \<open>(4.8): @{text "\<gamma>_p^in"} is an integer (twice a sum of half-integers).\<close>
lemma two_wIn_Ints: "2 * wIn K M p a i \<in> (\<int> :: rat set)"
proof (cases "a = 0")
  case True
  define S where "S = insert (2 * of_nat i + 6 * of_nat (Nof K div p) - of_nat (K div p) + 1 /
    2 :: rat)
      ((\<lambda>c. of_int (Zin K M p c) - (of_nat (ell p K c) + 4) / 2) ` {1..mHalf p})"
  have wS: "wIn K M p a i = Min S" using True by (simp add: wIn_def S_def)
  have "Min S \<in> S" unfolding S_def by (rule Min_in) auto
  moreover have "2 * y \<in> \<int>" if "y \<in> S" for y
  proof -
    from that consider "y = 2 * of_nat i + 6 * of_nat (Nof K div p) - of_nat (K div p) + 1 / 2"
      | c where "y = of_int (Zin K M p c) - (of_nat (ell p K c) + 4) / 2"
      unfolding S_def by auto
    thus ?thesis
    proof cases
      case 1
      have "2 * y = of_int (4 * int i + 12 * int (Nof K div p) - 2 * int (K div p) + 1)"
        using 1 by (simp add: algebra_simps)
      thus ?thesis by (metis Ints_of_int)
    next
      case (2 c)
      have "2 * y = of_int (2 * Zin K M p c - int (ell p K c) - 4)"
        using 2 by (simp add: field_simps)
      thus ?thesis by (metis Ints_of_int)
    qed
  qed
  ultimately show ?thesis using wS by simp
next
  case False
  have "2 * wIn K M p a i = of_int (2 * int i + 2 * bIn K p a - int (ell p K a) - 4)"
    using False by (simp add: wIn_def field_simps)
  thus ?thesis by (metis Ints_of_int)
qed

lemma gammaIn_isInt: "\<exists>n::int. gammaIn K M p = of_int n"
proof -
  have "gammaIn K M p \<in> \<int>"
    unfolding gammaIn_def sum_distrib_left by (intro Ints_sum two_wIn_Ints)
  thus ?thesis by (auto elim: Ints_cases)
qed

text \<open>Section 4.1: the dimensions @{text "L_a"} are nonnegative and
  @{text "L_0 + \<Sum>_{a\<ge>1} L_a = h"}.\<close>
lemma card_cong_class_le:
  assumes "0 < p" "A \<subseteq> {..N}" "\<And>x y. x \<in> A \<Longrightarrow>
    y \<in> A \<Longrightarrow> x mod p = y mod p"
  shows "card A \<le> N div p + 1"
proof -
  have inj: "inj_on (\<lambda>j. j div p) A"
  proof (rule inj_onI)
    fix x y assume xy: "x \<in> A" "y \<in> A" "x div p = y div p"
    have "x = x div p * p + x mod p" by simp
    also have "\<dots> = y div p * p + y mod p" using xy assms(3)[OF xy(1,2)] by simp
    also have "\<dots> = y" by simp
    finally show "x = y" .
  qed
  have "(\<lambda>j. j div p) ` A \<subseteq> {..N div p}" using assms(2)
    by (auto intro: div_le_mono)
  hence "card ((\<lambda>j. j div p) ` A) \<le> card {..N div p}" by (intro card_mono) auto
  thus ?thesis using card_image[OF inj] by simp
qed

lemma ell_le:
  assumes "0 < p"
  shows "ell p N a \<le> 2 * (N div p) + 2"
proof -
  define A1 where "A1 = {j \<in> {1..N}. j mod p = a mod p}"
  define A2 where "A2 = {j \<in> {1..N}. (j + a) mod p = 0}"
  have "ell p N a = card (A1 \<union> A2)" unfolding ell_def A1_def A2_def
    by (rule arg_cong[where f = card]) auto
  also have "\<dots> \<le> card A1 + card A2" by (rule card_Un_le)
  also have "card A1 \<le> N div p + 1"
    by (rule card_cong_class_le[OF assms]) (auto simp: A1_def)
  also have "card A2 \<le> N div p + 1"
  proof (rule card_cong_class_le[OF assms])
    show "A2 \<subseteq> {..N}" by (auto simp: A2_def)
  next
    fix x y assume "x \<in> A2" "y \<in> A2"
    hence "[x + a = y + a] (mod p)" by (simp add: A2_def cong_def)
    hence "[x = y] (mod p)" by (rule cong_add_rcancel_nat[THEN iffD1])
    thus "x mod p = y mod p" by (simp only: cong_def)
  qed
  finally show ?thesis by simp
qed

lemma Lin_nonneg: "prime p \<Longrightarrow> InnerHyp K M p \<Longrightarrow>
  a \<le> mHalf p \<Longrightarrow> 0 \<le> Lin K M p a"
proof -
  assume "prime p" and H: "InnerHyp K M p" and "a \<le> mHalf p"
  show "0 \<le> Lin K M p a"
  proof (cases "a = 0")
    case True
    thus ?thesis by (simp add: Lin_def)
  next
    case False
    from H have M40: "40 \<le> M" and K40: "40 dvd K" and KM: "200 * M ^ 2 \<le> K"
      and pK: "3 * p \<le> K" by (auto simp: InnerHyp_def)
    obtain k where k: "K = 40 * k" using K40 by (elim dvdE)
    have hk: "hof K = 37 * k" and Nk: "Nof K = 3 * k" unfolding k hof_def Nof_def by simp_all
    have p8: "8000 < p" using innerHyp_bounds[OF H] M40 by linarith
    define m where "m = mHalf p"
    define q where "q = Nof K div p"
    have m0: "0 < m" using p8 by (simp add: m_def mHalf_def)
    have m2: "2 * m \<le> p" by (simp add: m_def mHalf_def)
    have "q * p \<le> 3 * k" unfolding q_def Nk[symmetric] by (rule div_times_less_eq_dividend)
    hence qp: "p * q \<le> 3 * k" by (simp add: mult.commute)
    have "2 * m * q \<le> p * q" using m2 by (rule mult_le_mono1)
    hence mq: "2 * (m * q) \<le> p * q" by (simp add: mult.assoc)
    have MM: "40 * M \<le> M * M" using M40 by (rule mult_le_mono1)
    have kM: "200 * (M * M) \<le> 40 * k" using KM k by (simp add: power2_eq_square)
    have qq: "q \<le> p * q" using p8 by simp
    have "6 * (m * (q + 1)) + 4 * M + 10 + 3 * q \<le> 46 * k"
    proof (cases "q = 0")
      case True
      have e: "m * (q + 1) = m" using True by simp
      show ?thesis unfolding e using True m2 pK k MM kM M40 by linarith
    next
      case False
      have e: "m * (q + 1) = m * q + m" by simp
      have e2: "6 * (m * q + m) = 6 * (m * q) + 6 * m" by (rule add_mult_distrib2)
      have pq: "p \<le> p * q" using False by simp
      have "6 * (m * q) \<le> 9 * k" using mq qp by linarith
      moreover have "6 * m \<le> 9 * k" using m2 pq qp by linarith
      moreover have "3 * q \<le> 9 * k" using qq qp by linarith
      moreover have "4 * M + 10 \<le> 19 * k" using MM kM M40 by linarith
      ultimately show ?thesis unfolding e e2 by linarith
    qed
    hence "int (6 * (m * (q + 1)) + 4 * M + 10 + 3 * q) \<le> int (46 * k)"
      by (simp only: of_nat_le_iff)
    hence r: "int (6 * (q + 1)) * int m \<le> rhs44 K M p"
      unfolding rhs44_def q_def[symmetric] unfolding hk Nk L0_def
      by (simp add: algebra_simps)
    have T: "int (6 * (q + 1)) \<le> Tin K M p"
    proof -
      have "int (6 * (q + 1)) = (int (6 * (q + 1)) * int m) div int m" using m0 by simp
      also have "\<dots> \<le> rhs44 K M p div int m" by (rule zdiv_mono1[OF r]) (use m0 in simp)
      finally show ?thesis by (simp add: Tin_def m_def)
    qed
    have e: "0 \<le> epsIn K M p a" by (simp add: epsIn_def)
    have l: "ell p (Nof K) a \<le> 2 * q + 2" unfolding q_def using p8 by (intro ell_le) simp
    show ?thesis using False T e l by (simp add: Lin_def bIn_def)
  qed
qed

lemma card_multiples_upto:
  assumes "0 < p"
  shows "card {j \<in> {1..N}. p dvd j} = N div p"
proof -
  have "{j \<in> {1..N}. p dvd j} = (\<lambda>i. p * i) ` {1..N div p}"
  proof (intro equalityI subsetI)
    fix j assume "j \<in> {j \<in> {1..N}. p dvd j}"
    then obtain i where j: "j = p * i" "1 \<le> p * i" "p * i \<le> N" by (auto elim!: dvdE)
    have "1 \<le> i" using j(2) by (cases i) auto
    moreover have "i \<le> N div p" using div_le_mono[OF j(3), of p] assms by simp
    ultimately show "j \<in> (\<lambda>i. p * i) ` {1..N div p}" using j(1) by auto
  next
    fix j assume "j \<in> (\<lambda>i. p * i) ` {1..N div p}"
    then obtain i where "i \<in> {1..N div p}" "j = p * i" by blast
    hence i: "j = p * i" "1 \<le> i" "i \<le> N div p" by auto
    have "p * i \<le> N" using mult_le_mono2[OF i(3), of p] times_div_less_eq_dividend[of p N]
      by linarith
    moreover have "1 \<le> p * i" using i(2) assms by simp
    ultimately show "j \<in> {j \<in> {1..N}. p dvd j}" using i(1) by auto
  qed
  moreover have "inj_on (\<lambda>i. p * i) {1..N div p}" using assms by (auto intro: inj_onI)
  ultimately show ?thesis by (simp add: card_image)
qed

lemma sum_ell:
  assumes "prime p" "2 < p"
  shows "(\<Sum> a = 1..mHalf p. ell p N a) = N - N div p"
proof -
  define m where "m = mHalf p"
  have p0: "0 < p" using assms by simp
  have "odd p" using assms by (metis prime_odd_nat)
  hence m2: "2 * m = p - 1" unfolding m_def mHalf_def by (auto elim!: oddE)
  define C where "C a = {j \<in> {1..N}. j mod p = a \<or> j mod p = p - a}" for a
  have Ceq: "{j \<in> {1..N}. j mod p = a mod p \<or> (j + a) mod p = 0} = C a"
    if a: "a \<in> {1..m}" for a
  proof -
    have ap: "0 < a" "a < p" using a m2 by auto
    have "(j + a) mod p = 0 \<longleftrightarrow> j mod p = p - a" for j
    proof -
      have r: "j mod p < p" using p0 by simp
      have "(j + a) mod p = (j mod p + a) mod p" by (simp add: mod_add_left_eq)
      also have "\<dots> = 0 \<longleftrightarrow> j mod p + a = p"
      proof
        assume h: "(j mod p + a) mod p = 0"
        have "j mod p + a < 2 * p" using r ap by linarith
        moreover have "p dvd j mod p + a" using h by (simp add: mod_eq_0_iff_dvd)
        then obtain t where t: "j mod p + a = p * t" by (elim dvdE)
        ultimately have "t < 2" by simp
        moreover have "t \<noteq> 0"
        proof
          assume "t = 0"
          hence "j mod p + a = 0" using t by simp
          thus False using ap by simp
        qed
        ultimately show "j mod p + a = p" using t by (cases t) auto
      qed simp
      finally show ?thesis using ap by linarith
    qed
    thus ?thesis using ap by (auto simp: C_def)
  qed
  have "(\<Sum> a = 1..m. ell p N a) = (\<Sum> a = 1..m. card (C a))"
  proof (rule sum.cong)
    fix a assume a: "a \<in> {1..m}"
    show "ell p N a = card (C a)" unfolding ell_def Ceq[OF a] ..
  qed simp
  also have "\<dots> = card (\<Union> a \<in> {1..m}. C a)"
  proof (rule card_UN_disjoint[symmetric])
    show "\<forall>i \<in> {1..m}. \<forall>j \<in> {1..m}. i \<noteq> j \<longrightarrow>
      C i \<inter> C j = {}"
      using m2 by (auto simp: C_def)
  qed (auto simp: C_def)
  also have "(\<Union> a \<in> {1..m}. C a) = {1..N} - {j \<in> {1..N}. p dvd j}"
  proof (intro equalityI subsetI)
    fix j assume "j \<in> (\<Union> a \<in> {1..m}. C a)"
    then obtain a where a: "a \<in> {1..m}" "j \<in> C a" by auto
    hence "j mod p \<noteq> 0" using m2 by (auto simp: C_def)
    thus "j \<in> {1..N} - {j \<in> {1..N}. p dvd j}" using a by (auto simp: C_def dvd_eq_mod_eq_0)
  next
    fix j assume j: "j \<in> {1..N} - {j \<in> {1..N}. p dvd j}"
    hence r0: "j mod p \<noteq> 0" by (auto simp: dvd_eq_mod_eq_0)
    have rp: "j mod p < p" using p0 by simp
    show "j \<in> (\<Union> a \<in> {1..m}. C a)"
    proof (cases "j mod p \<le> m")
      case True
      thus ?thesis using j r0 by (auto simp: C_def intro!: bexI[of _ "j mod p"])
    next
      case False
      hence "p - j mod p \<in> {1..m}" using rp m2 by auto
      moreover have "j \<in> C (p - j mod p)" using j rp by (auto simp: C_def)
      ultimately show ?thesis by blast
    qed
  qed
  also have "card ({1..N} - {j \<in> {1..N}. p dvd j}) = N - N div p"
    by (subst card_Diff_subset) (use card_multiples_upto[OF p0, of N] in auto)
  finally show ?thesis by (simp add: m_def)
qed

lemma rank_props:
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes A: "finite A" and irr: "\<And>x. \<not> r x x" and tr: "\<And>x y z. r x y
    \<Longrightarrow> r y z \<Longrightarrow> r x z"
    and tot: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
      x \<noteq> y \<Longrightarrow> r x y \<or> r y x"
  defines "rk \<equiv> \<lambda>x. card {c \<in> A. r c x}"
  shows "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
    rk x < rk y \<longleftrightarrow> r x y"
    and "bij_betw rk A {..<card A}"
proof -
  have mono: "rk x < rk y" if "x \<in> A" "y \<in> A" "r x y" for x y
  proof -
    have "{c \<in> A. r c x} \<subset> {c \<in> A. r c y}"
      using that irr tr by blast
    thus ?thesis unfolding rk_def by (rule psubset_card_mono[rotated]) (use A in simp)
  qed
  show "rk x < rk y \<longleftrightarrow> r x y" if "x \<in> A" "y \<in> A" for x y
  proof
    assume "rk x < rk y"
    thus "r x y" using mono[OF that(2,1)] tot[OF that] by (cases "x = y") auto
  qed (rule mono[OF that])
  have inj: "inj_on rk A"
  proof (rule inj_onI)
    fix x y assume "x \<in> A" "y \<in> A" "rk x = rk y"
    thus "x = y" using mono tot by (metis less_irrefl)
  qed
  have sub: "rk ` A \<subseteq> {..<card A}"
  proof
    fix i assume "i \<in> rk ` A"
    then obtain x where x: "x \<in> A" "i = rk x" by auto
    have "{c \<in> A. r c x} \<subseteq> A - {x}" using irr by auto
    hence "rk x \<le> card (A - {x})" unfolding rk_def by (intro card_mono) (use A in auto)
    also have "\<dots> < card A" by (rule card_Diff1_less[OF A x(1)])
    finally show "i \<in> {..<card A}" using x by simp
  qed
  have "rk ` A = {..<card A}"
    by (rule card_subset_eq) (use sub card_image[OF inj] in auto)
  thus "bij_betw rk A {..<card A}" using inj by (simp add: bij_betw_def)
qed

lemma sum_epsIn:
  assumes "prime p" "InnerHyp K M p"
  shows "(\<Sum> a = 1..mHalf p. epsIn K M p a) = Ein K M p"
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
  have iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
    defaultPos K p x < defaultPos K p y \<longleftrightarrow> r x y" for x y
    using RP(1) by (simp add: A_def)
  have bij: "bij_betw (defaultPos K p) A {..<m}" using RP(2) cA by (simp add: A_def)
  have TE: "0 \<le> Ein K M p" "Ein K M p < int m" using TE_spec[OF assms] by (auto simp: m_def)
  define E where "E = nat (Ein K M p)"
  have E: "Ein K M p = int E" "E \<le> m" using TE by (auto simp: E_def)
  have eps: "epsIn K M p a = (if defaultPos K p a < E then 1 else 0)" if a: "a \<in> A" for a
  proof -
    have "{c \<in> {1..mHalf p}. defaultPos K p c < defaultPos K p a} = {c \<in> A. r c a}"
      using iff[OF _ a] by (auto simp: A_def m_def)
    thus ?thesis by (simp add: epsIn_def rk[symmetric] E)
  qed
  have "(\<Sum> a = 1..mHalf p. epsIn K M p a) = (\<Sum> a \<in> A.
    if defaultPos K p a < E then 1 else 0)"
    unfolding A_def m_def by (rule sum.cong) (simp_all add: eps[unfolded A_def m_def])
  also have "\<dots> = int (card {a \<in> A. defaultPos K p a < E})"
    by (simp add: sum.If_cases A_def Int_def)
  also have "card {a \<in> A. defaultPos K p a < E} = card {..<E}"
  proof -
    have inj: "inj_on (defaultPos K p) {a \<in> A. defaultPos K p a < E}"
      using bij by (auto simp: bij_betw_def intro: inj_on_subset)
    have "defaultPos K p ` {a \<in> A. defaultPos K p a < E} = {..<E}"
    proof (intro equalityI subsetI)
      fix i assume "i \<in> {..<E}"
      hence "i \<in> {..<m}" using E by auto
      hence "i \<in> defaultPos K p ` A" using bij by (simp add: bij_betw_def)
      then obtain a where "a \<in> A" "defaultPos K p a = i" by blast
      thus "i \<in> defaultPos K p ` {a \<in> A. defaultPos K p a < E}"
        using \<open>i \<in> {..<E}\<close> by auto
    qed auto
    thus ?thesis using card_image[OF inj] by simp
  qed
  finally show ?thesis using E by simp
qed

lemma sum_Lin: "prime p \<Longrightarrow> InnerHyp K M p \<Longrightarrow>
  (\<Sum> a \<le> mHalf p. Lin K M p a) = int (hof K)"
proof -
  assume p: "prime p" and H: "InnerHyp K M p"
  define m where "m = mHalf p"
  have p8: "8000 < p" using innerHyp_bounds[OF H] H by (auto simp: InnerHyp_def)
  have "{..m} = insert 0 {1..m}" by auto
  hence "(\<Sum> a \<le> m. Lin K M p a) = Lin K M p 0 + (\<Sum> a = 1..m. Lin K M p a)" by simp
  also have "(\<Sum> a = 1..m. Lin K M p a)
      = (\<Sum> a = 1..m. Tin K M p - 3 * int (ell p (Nof K) a) + epsIn K M p a)"
    by (rule sum.cong) (auto simp: Lin_def bIn_def)
  also have "\<dots> = int m * Tin K M p - 3 * int (\<Sum> a = 1..m. ell p (Nof K) a) + (\<Sum> a =
    1..m. epsIn K M p a)"
    by (simp add: sum.distrib sum_subtractf sum_distrib_left of_nat_sum)
  also have "(\<Sum> a = 1..m. ell p (Nof K) a) = Nof K - Nof K div p"
    unfolding m_def by (rule sum_ell[OF p]) (use p8 in simp)
  also have "(\<Sum> a = 1..m. epsIn K M p a) = Ein K M p"
    unfolding m_def by (rule sum_epsIn[OF p H])
  finally have "(\<Sum> a \<le> m. Lin K M p a)
      = int (L0 M) + (int m * Tin K M p + Ein K M p) - 3 * int (Nof K - Nof K div p)"
    by (simp add: Lin_def)
  also have "int m * Tin K M p + Ein K M p = rhs44 K M p" using TE_spec[OF p H] by (simp add: m_def)
  also have "int (Nof K - Nof K div p) = int (Nof K) - int (Nof K div p)" by (simp add: of_nat_diff)
  finally show "(\<Sum> a \<le> mHalf p. Lin K M p a) = int (hof K)" by (simp add: rhs44_def m_def)
qed

lemma length_inner_idx: "prime p \<Longrightarrow> InnerHyp K M p \<Longrightarrow>
  length (inner_idx K M p) = hof K"
proof -
  assume p: "prime p" and H: "InnerHyp K M p"
  have "length (inner_idx K M p) = (\<Sum> a \<in> set [0..<mHalf p + 1]. nat (Lin K M p a))"
    unfolding inner_idx_def length_concat map_map
      by (simp add: o_def sum_list_distinct_conv_sum_set)
  also have "set [0..<mHalf p + 1] = {..mHalf p}" by auto
  also have "(\<Sum> a \<le> mHalf p. nat (Lin K M p a)) = hof K"
  proof -
    have "int (\<Sum> a \<le> mHalf p. nat (Lin K M p a)) = (\<Sum> a \<le> mHalf p. Lin K M p a)"
      unfolding of_nat_sum by (rule sum.cong) (use Lin_nonneg[OF p H] in auto)
    also have "\<dots> = int (hof K)" by (rule sum_Lin[OF p H])
    finally show ?thesis by (simp only: of_nat_eq_iff)
  qed
  finally show "length (inner_idx K M p) = hof K" .
qed

text \<open>(4.5): the inner basis is @{text "\<int>_p"}-unimodular: the coefficient matrix of the
  basis
  polynomials has a determinant that is a @{text p}-adic unit (CRT basis lemma over
    @{text "\<int>/p\<int>"}).\<close>
text \<open>The index list is lexicographically ordered: an earlier position has a smaller class,
  or the same class
  and a smaller exponent.\<close>
lemma inner_idx_sorted:
  "sorted_wrt (\<lambda>u v. fst u < fst v \<or> (fst u = fst v \<and> snd u < snd v))
     (concat (map (\<lambda>a. map (\<lambda>i. (a, i)) [0..<f a]) [0..<n]))"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "sorted_wrt (\<lambda>u v. fst u < fst v \<or> (fst u = fst v \<and>
    snd u < snd v)) (map (\<lambda>i. (n, i)) [0..<f n])"
    unfolding sorted_wrt_map by (simp add: sorted_wrt_upt)
  with Suc show ?case by (auto simp: sorted_wrt_append)
qed

lemma inner_idx_lex:
  assumes "y < x" "x < length (inner_idx K M p)"
  shows "fst (inner_idx K M p ! y) < fst (inner_idx K M p ! x) \<or>
         (fst (inner_idx K M p ! y) = fst (inner_idx K M p ! x) \<and>
           snd (inner_idx K M p ! y) < snd (inner_idx K M p ! x))"
  using sorted_wrt_nth_less[OF inner_idx_sorted assms(1) assms(2)[unfolded inner_idx_def]]
    unfolding inner_idx_def .

lemma vpGge_innerBasis: "prime p \<Longrightarrow> vpGge p (innerBasis K M p x) 0"
proof -
  assume p: "prime p"
  have f: "vpGge p (pX + [:of_nat c ^ 2:]) 0" for c
  proof -
    have "vge p (of_nat c ^ 2) 0" using vge_pow[OF p vge_of_int[OF p, of "int c"]] by simp
    thus ?thesis by (intro vpGge_add[OF p vpGge_pX vpGge_C])
  qed
  have fp: "vpGge p ((pX + [:of_nat c ^ 2:]) ^ n) 0" for c n using vpGge_pow[OF p f[of c], of n]
    by simp
  have pr: "vpGge p (\<Prod> c \<in> {0..mHalf p} - {fst x}. (pX +
    [:of_nat c ^ 2:]) ^ nat (Lin K M p c)) 0"
    using vpGge_prod[OF p, of "{0..mHalf p} - {fst x}" "\<lambda>c. (pX +
      [:of_nat c ^ 2:]) ^ nat (Lin K M p c)" "\<lambda>_. 0"] fp
    by simp
  show ?thesis unfolding innerBasis_def using vpGge_mul[OF p pr fp] by simp
qed

text \<open>Shapes of pulled-back numerators (Lean: @{text FarGood}, @{text Decomp}).\<close>
definition FarGood :: "nat \<Rightarrow> rat poly \<Rightarrow> bool" where
  "FarGood p F \<longleftrightarrow> vpGge p F 0 \<and> (\<forall>d. 1 \<le> d \<longrightarrow>
    vge p (Polynomial.coeff F d) 1)"

definition Decomp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat poly \<Rightarrow>
  bool" where
  "Decomp p e n Q \<longleftrightarrow> (\<exists>N F. Q = [:of_nat p ^ e:] * N * F \<and>
    vpGge p N 0 \<and> degree N \<le> n \<and> FarGood p F)"

text \<open>The number of @{text p}'s in
  @{text "j^2 - (c + p z)^2 = (j - c - p z)(j + c + p z)"}.\<close>
definition omg :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "omg p c j = (if int p dvd (int j - int c) then 1 else 0) + (if int p dvd (int j +
    int c) then 1 else 0)"

text \<open>The exponent of @{text p} extracted from the pulled-back numerator at the class
  @{text c}.\<close>
definition eNum :: "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> (nat \<Rightarrow>
  nat) \<Rightarrow> nat" where
  "eNum p c J k = 5 * (if int p dvd int c then 1 else 0) + (\<Sum> j \<in> J. k j * omg p c j)"

text \<open>The near poles of the class @{text c}: @{text "r \<in> \<plusminus>[1, K]"} with
  @{text "r \<equiv> c (mod p)"}.\<close>
definition nearCount :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nearCount p K c = card {r \<in> signedPoles {1..K}. int p dvd (r - int c)}"

subsection \<open>Extracting powers of @{text p} from @{text "g(c + p z)"}\<close>

lemma FarGood_one: "FarGood p 1"
  unfolding FarGood_def by (auto simp: vpGge_one vge_zero)

lemma FarGood_mult: "prime p \<Longrightarrow> FarGood p F \<Longrightarrow>
  FarGood p G \<Longrightarrow> FarGood p (F * G)"
proof -
  assume p: "prime p" and F: "FarGood p F" and G: "FarGood p G"
  have F0: "\<And>i. vge p (Polynomial.coeff F i) 0" and G0: "\<And>i. vge p (Polynomial.coeff G i)
    0"
    using F G unfolding FarGood_def vpGge_iff by auto
  have F1: "\<And>i. 1 \<le> i \<Longrightarrow> vge p (Polynomial.coeff F i) 1"
    and G1: "\<And>i. 1 \<le> i \<Longrightarrow> vge p (Polynomial.coeff G i) 1"
    using F G unfolding FarGood_def by auto
  have "vpGge p (F * G) 0" using vpGge_mul[OF p, of F 0 G 0] F G unfolding FarGood_def by simp
  moreover have "vge p (Polynomial.coeff (F * G) d) 1" if d: "1 \<le> d" for d
    unfolding coeff_mult
  proof (rule vge_sum[OF p])
    show "finite {..d}" by simp
  next
    fix i assume i: "i \<in> {..d}"
    show "vge p (Polynomial.coeff F i * Polynomial.coeff G (d - i)) 1"
    proof (cases "i = 0")
      case True
      have "vge p (Polynomial.coeff F i * Polynomial.coeff G (d - i)) (0 + 1)"
        by (rule vge_mul[OF p F0 G1]) (use True d in simp)
      thus ?thesis by simp
    next
      case False
      have "vge p (Polynomial.coeff F i * Polynomial.coeff G (d - i)) (1 + 0)"
        by (rule vge_mul[OF p F1 G0]) (use False in simp)
      thus ?thesis by simp
    qed
  qed
  ultimately show ?thesis unfolding FarGood_def by blast
qed

lemma Decomp_one: "Decomp p 0 0 1"
  unfolding Decomp_def by (rule exI[of _ 1], rule exI[of _ 1]) (simp add: vpGge_one FarGood_one)

lemma Decomp_mult:
  "prime p \<Longrightarrow> Decomp p e n Q \<Longrightarrow> Decomp p e' n' Q' \<Longrightarrow>
    Decomp p (e + e') (n + n') (Q * Q')"
proof -
  assume p: "prime p" and D1: "Decomp p e n Q" and D2: "Decomp p e' n' Q'"
  obtain N F where Q: "Q = [:of_nat p ^ e:] * N * F" and N: "vpGge p N 0" and dN: "degree N \<le> n"
    and F: "FarGood p F" using D1 unfolding Decomp_def by blast
  obtain N' F' where Q': "Q' = [:of_nat p ^ e':] * N' *
    F'" and N': "vpGge p N' 0" and dN': "degree N' \<le> n'"
    and F': "FarGood p F'" using D2 unfolding Decomp_def by blast
  have "Q * Q' = [:of_nat p ^ (e + e'):] * (N * N') * (F * F')"
    unfolding Q Q' power_add by (simp add: mult_ac)
  moreover have "vpGge p (N * N') 0" using vpGge_mul[OF p N N'] by simp
  moreover have "degree (N * N') \<le> n + n'" using degree_mult_le[of N N'] dN dN' by linarith
  moreover have "FarGood p (F * F')" by (rule FarGood_mult[OF p F F'])
  ultimately show ?thesis unfolding Decomp_def by blast
qed

lemma Decomp_pow: "prime p \<Longrightarrow> Decomp p e n Q \<Longrightarrow>
  Decomp p (k * e) (k * n) (Q ^ k)"
proof (induction k)
  case 0
  show ?case using Decomp_one by simp
next
  case (Suc k)
  have "Decomp p (k * e + e) (k * n + n) (Q ^ k * Q)"
    by (rule Decomp_mult[OF Suc.prems(1) Suc.IH[OF Suc.prems] Suc.prems(2)])
  thus ?case by (simp add: ac_simps)
qed

lemma Decomp_C_unit: "prime p \<Longrightarrow> Decomp p e n Q \<Longrightarrow>
  vge p u 0 \<Longrightarrow> Decomp p e n ([:u:] * Q)"
proof -
  assume p: "prime p" and D: "Decomp p e n Q" and u: "vge p u 0"
  obtain N F where Q: "Q = [:of_nat p ^ e:] * N * F" and N: "vpGge p N 0" and dN: "degree N \<le> n"
    and F: "FarGood p F" using D unfolding Decomp_def by blast
  have e: "[:u:] * Q = [:of_nat p ^ e:] * N * ([:u:] * F)" unfolding Q by (simp add: mult_ac)
  have "vpGge p ([:u:] * F) 0" using vpGge_mul[OF p vpGge_C[OF u], of F 0] F unfolding FarGood_def
    by simp
  moreover have "vge p (Polynomial.coeff ([:u:] * F) d) 1" if d: "1 \<le> d" for d
  proof -
    have "vge p (u * Polynomial.coeff F d) (0 + 1)"
      by (rule vge_mul[OF p u]) (use F d in \<open>simp add: FarGood_def\<close>)
    thus ?thesis by simp
  qed
  ultimately have "FarGood p ([:u:] * F)" unfolding FarGood_def by blast
  thus ?thesis using e N dN unfolding Decomp_def by blast
qed

text \<open>A linear factor @{text "\<alpha> + \<sigma> p z"} (@{text "\<sigma> = \<plusminus>1"})
  is @{text "p \<cdot> (near)"} if @{text "p | \<alpha>"}, and far-good otherwise.\<close>
lemma Decomp_linear:
  assumes "prime p" "\<sigma> = 1 \<or> \<sigma> = - 1"
  shows "Decomp p (if int p dvd \<alpha> then 1 else 0) (if int p dvd \<alpha> then 1 else 0)
           [:of_int \<alpha>, of_int (\<sigma> * int p):]"
proof (cases "int p dvd \<alpha>")
  case True
  then obtain \<beta> where b: "\<alpha> = int p * \<beta>" by (elim dvdE)
  have e: "[:of_int \<alpha>, of_int (\<sigma> * int p):] =
    [:of_nat p ^ 1:] * [:of_int \<beta>, of_int \<sigma>:] * (1 :: rat poly)"
    unfolding b by (simp add: mult.commute)
  have N: "vpGge p [:of_int \<beta>, of_int \<sigma> :: rat:] 0" unfolding vpGge_iff
    by (auto simp: coeff_pCons vge_of_int[OF assms(1)] vge_zero split: nat.split)
  have dN: "degree [:of_int \<beta>, of_int \<sigma> :: rat:] \<le> 1"
    using degree_pCons_le[of "of_int \<beta>" "[:of_int \<sigma> :: rat:]"] by simp
  have "Decomp p 1 1 [:of_int \<alpha>, of_int (\<sigma> * int p):]"
    unfolding Decomp_def by (rule exI[of _ "[:of_int \<beta>, of_int \<sigma>:]"],
      rule exI[of _ 1]) (intro conjI e N dN FarGood_one)
  thus ?thesis using True by simp
next
  case False
  have vp1: "vge p (of_nat p) 1" using qmultiplicity_power_int[OF assms(1), of 1]
    by (simp add: vge_def vp_def)
  have vp1': "vge p (- of_nat p) 1" by (rule vge_neg[OF vp1])
  have vp0: "vge p (of_nat p) 0" and vp0': "vge p (- of_nat p) 0"
    by (rule vge_mono[OF vp1], simp, rule vge_mono[OF vp1'], simp)
  have FG: "FarGood p [:of_int \<alpha>, of_int (\<sigma> * int p) :: rat:]"
    unfolding FarGood_def vpGge_iff
    using assms(2) by (auto simp: coeff_pCons vge_of_int[OF assms(1)] vge_zero vp1 vp1' vp0 vp0'
      split: nat.split)
  have e: "[:of_int \<alpha>, of_int (\<sigma> * int p):] =
    [:of_nat p ^ 0:] * 1 * [:of_int \<alpha>, of_int (\<sigma> * int p) :: rat:]"
    by simp
  have "Decomp p 0 0 [:of_int \<alpha>, of_int (\<sigma> * int p):]"
    unfolding Decomp_def by (rule exI[of _ 1], rule exI[of _ "[:of_int \<alpha>,
      of_int (\<sigma> * int p):]"]) (intro conjI e vpGge_one FG, simp)
  thus ?thesis using False by simp
qed

lemma Decomp_prod:
  "prime p \<Longrightarrow> finite J \<Longrightarrow> (\<And>j. j \<in> J \<Longrightarrow>
    Decomp p (e j) (e j) (f j)) \<Longrightarrow>
   Decomp p (\<Sum> j \<in> J. e j) (\<Sum> j \<in> J. e j) (\<Prod> j \<in> J. f j)"
proof -
  assume p: "prime p" and J: "finite J" and D: "\<And>j. j \<in> J \<Longrightarrow>
    Decomp p (e j) (e j) (f j)"
  show ?thesis using J D
  proof (induction J rule: finite_induct)
    case empty
    show ?case using Decomp_one by simp
  next
    case (insert a J)
    have "Decomp p (e a + (\<Sum> j \<in> J. e j)) (e a + (\<Sum> j \<in>
      J. e j)) (f a * (\<Prod> j \<in> J. f j))"
      by (rule Decomp_mult[OF p]) (use insert in auto)
    thus ?case unfolding sum.insert[OF insert.hyps] prod.insert[OF insert.hyps] .
  qed
qed

text \<open>The pulled-back numerator @{text "\<epsilon> x^5 \<Prod>_j (j^2 - x^2)^{k_j}"} at
  @{text "x = c + p z"}: every factor
  @{text "j^2 - (c + p z)^2 = (j - c - p z)(j + c + p z)"} contributes @{text "omg p c j"} powers of
    @{text p}.\<close>
lemma decomp_pullback:
  assumes p: "prime p" and J: "finite J" and \<epsilon>: "vge p \<epsilon> 0"
  shows "Decomp p (eNum p c J k) (eNum p c J k)
           (pcompose ([:\<epsilon>:] * pX ^ 5 * pcompose (\<Prod> j \<in>
             J. (pX + [:of_nat j ^ 2:]) ^ k j) (- (pX ^ 2)))
                     ([:of_nat c:] + [:of_nat p:] * pX))"
proof -
  define L where "L = [:of_nat c:] + [:of_nat p:] * (pX :: rat poly)"
  have Leq: "L = [:of_int (int c), of_int (1 * int p):]"
    unfolding L_def by (simp add: monom_Suc)
  have fac: "\<And>j. pcompose (pcompose (pX + [:of_nat j ^ 2:]) (- (pX ^ 2))) L =
               [:of_int (int j - int c), of_int (- 1 * int p):] * [:of_int (int j + int c),
                 of_int (1 * int p):]"
  proof -
    fix j :: nat
    have e: "poly (pcompose (pcompose (pX + [:of_nat j ^ 2:]) (- (pX ^ 2))) L) x =
        poly ([:of_int (int j - int c), of_int (- 1 * int p):] * [:of_int (int j + int c),
          of_int (1 * int p):]) x" for x :: rat
      unfolding L_def by (simp add: poly_pcompose poly_monom algebra_simps power2_eq_square)
    show "pcompose (pcompose (pX + [:of_nat j ^ 2:]) (- (pX ^ 2))) L =
        [:of_int (int j - int c), of_int (- 1 * int p):] * [:of_int (int j + int c),
          of_int (1 * int p):]"
      by (rule poly_eq_of_eval_nat) (rule e)
  qed
  have Q: "pcompose ([:\<epsilon>:] * pX ^ 5 * pcompose (\<Prod> j \<in>
    J. (pX + [:of_nat j ^ 2:]) ^ k j) (- (pX ^ 2))) L =
           [:\<epsilon>:] * (L ^ 5 * (\<Prod> j \<in>
             J. ([:of_int (int j - int c), of_int (- 1 * int p):] *
                                        [:of_int (int j + int c), of_int (1 * int p):]) ^ k j))"
    unfolding pcompose_mult pcompose_prod pcompose_power_left pcompose_pX pcompose_const fac
      by (simp only: mult.assoc)
  have L5: "Decomp p (5 * (if int p dvd int c then 1 else 0)) (5 *
    (if int p dvd int c then 1 else 0)) (L ^ 5)"
    unfolding Leq by (rule Decomp_pow[OF p Decomp_linear[OF p, of 1 "int c"]]) simp
  have Pr: "Decomp p (\<Sum> j \<in> J. k j * omg p c j) (\<Sum> j \<in> J. k j * omg p c j)
              (\<Prod> j \<in> J. ([:of_int (int j - int c), of_int (- 1 * int p):] *
                            [:of_int (int j + int c), of_int (1 * int p):]) ^ k j)"
  proof (rule Decomp_prod[OF p J])
    fix j assume "j \<in> J"
    show "Decomp p (k j * omg p c j) (k j * omg p c j)
        (([:of_int (int j - int c), of_int (- 1 * int p):] * [:of_int (int j + int c),
          of_int (1 * int p):]) ^ k j)"
      unfolding omg_def by (rule Decomp_pow[OF p Decomp_mult[OF p Decomp_linear[OF p]
        Decomp_linear[OF p]]]) simp_all
  qed
  show ?thesis
    unfolding L_def[symmetric] Q eNum_def
    by (rule Decomp_C_unit[OF p _ \<epsilon>]) (rule Decomp_mult[OF p L5 Pr])
qed

lemma tauExt_tr_C_mul: "tauExt_tr p Y ([:a:] * U) S M = [:a:] * tauExt_tr p Y U S M"
proof -
  have d: "([:a:] * U) div qPoleProd S = Polynomial.smult a (U div qPoleProd S)"
    by (simp add: div_smult_left)
  have t: "tauK (Polynomial.smult a P) = a * tauK P" for P by (simp add: tauK_eq_tau tau_smult)
  have r: "qRes S ([:a:] * U) s = a * qRes S U s" for s by (simp add: qRes_def)
  show ?thesis unfolding tauExt_tr_def d t r by (simp add: smult_add_right smult_sum_right)
qed

lemma vpGge_Yp_tr: "prime p \<Longrightarrow> 7 \<le> p \<Longrightarrow> vpGge p (Yp_tr p M) 0"
proof -
  assume p: "prime p" and p7: "7 \<le> p"
  have v: "vge p (of_nat p) 0" using vge_of_int[OF p, of "int p"] by simp
  have a: "vpGge p ([:of_nat p ^ 5:] * pX) 0"
    using vpGge_mul[OF p vpGge_C[OF vge_pow[OF p v]] vpGge_pX] by simp
  have b: "vpGge p [:Cp_tr p M:] 0" by (rule vpGge_C[OF vge_mono[OF Cp_tr_vge[OF p p7]]]) simp
  show ?thesis unfolding Yp_tr_def by (rule vpGge_add[OF p a b])
qed

lemma coeff_high_vge:
  assumes "prime p" "vpGge p N 0" "FarGood p F" "degree N < d"
  shows "vge p (Polynomial.coeff (N * F) d) 1"
proof -
  have N0: "\<And>i. vge p (Polynomial.coeff N i) 0" using assms(2) unfolding vpGge_iff by blast
  have F1: "\<And>i. 1 \<le> i \<Longrightarrow> vge p (Polynomial.coeff F i) 1" using assms(3)
    unfolding FarGood_def by blast
  have "vge p (\<Sum> i \<le> d. Polynomial.coeff N i * Polynomial.coeff F (d - i)) 1"
  proof (rule vge_sum[OF assms(1)])
    show "finite {..d}" by simp
  next
    fix i assume "i \<in> {..d}"
    show "vge p (Polynomial.coeff N i * Polynomial.coeff F (d - i)) 1"
    proof (cases "degree N < i")
      case True
      thus ?thesis by (simp add: coeff_eq_0 vge_zero)
    next
      case False
      hence "1 \<le> d - i" using assms(4) by linarith
      from vge_mul[OF assms(1) N0 F1[OF this]] show ?thesis by simp
    qed
  qed
  thus ?thesis unfolding coeff_mult .
qed

text \<open>One summand of (3.7).  If @{text "P(c + p z) = p^e N F"} (@{text Decomp}) with
  @{text "e \<le> p + 1"},
  the class-@{text c} summand has valuation @{text "\<ge> e - #{near poles}"},
    for every truncation length
  @{text "M \<ge> deg P"}.\<close>
theorem summand_bound_tr:
  assumes p: "prime p" and p7: "7 \<le> p" and K1: "2 * K < p ^ 2" and K2: "K + p < p ^ 2"
    and S: "finite S" and hS: "\<And>r. r \<in> S \<Longrightarrow>
      \<bar>r\<bar> \<le> int K" and c: "c < p"
    and D: "Decomp p e e (pcompose P ([:of_nat c:] + [:of_nat p:] * pX))" and e: "e \<le> p + 1"
    and dP: "degree P \<le> M"
  shows "vpGge p (tauExt_tr p (Yp_tr p M) (distribNum p S P c) (distribPoles p S c) M)
           (of_int (int e - int (card {r \<in> S. int p dvd (r - int c)})))"
proof -
  define L where "L = [:of_nat c:] + [:of_nat p:] * (pX :: rat poly)"
  obtain N F where Q: "pcompose P L = [:of_nat p ^ e:] * N * F" and N0: "vpGge p N 0"
    and Nd: "degree N \<le> e" and FG: "FarGood p F"
    using D unfolding Decomp_def L_def by blast
  have p0: "(of_nat p :: rat) \<noteq> 0" using p by (simp add: prime_gt_0_nat)
  define Sn where "Sn = {r \<in> S. int p dvd (r - int c)}"
  define Sf where "Sf = {r \<in> S. \<not> int p dvd (r - int c)}"
  define near :: "int set" where "near = (\<lambda>r. (r - int c) div int p) ` Sn"
  define far :: "rat set" where "far = (\<lambda>r. (of_int r - of_nat c) / of_nat p) ` Sf"
  have finSn: "finite Sn" and finSf: "finite Sf" and finnear: "finite near" and finfar: "finite far"
    by (simp_all add: Sn_def Sf_def near_def far_def S)
  have inj: "inj_on (\<lambda>r. (of_int r - of_nat c) / (of_nat p :: rat)) S"
    by (rule inj_on_subset[OF distrib_inj subset_UNIV]) (simp add: prime_gt_0_nat p)
  have cardfar: "card far = card Sf"
    unfolding far_def by (rule card_image) (use inj in \<open>auto simp: Sf_def inj_on_def\<close>)
  have cardS: "card S = card Sn + card Sf"
  proof -
    have SU: "S = Sn \<union> Sf" by (auto simp: Sn_def Sf_def)
    show ?thesis unfolding SU by (rule card_Un_disjoint[OF finSn finSf]) (auto simp: Sn_def Sf_def)
  qed
  have poles: "distribPoles p S c = of_int ` near \<union> far"
  proof -
    have SU: "S = Sn \<union> Sf" by (auto simp: Sn_def Sf_def)
    have e1: "(\<lambda>r. (of_int r - of_nat c) / (of_nat p :: rat)) ` Sn = of_int ` near"
      unfolding near_def image_image
    proof (rule image_cong[OF refl])
      fix r assume "r \<in> Sn"
      hence "int p dvd (r - int c)" by (simp add: Sn_def)
      then obtain q where q: "r - int c = int p * q" by (elim dvdE)
      have qd: "(r - int c) div int p = q" unfolding q using p by (simp add: prime_gt_0_nat)
      have "(of_int r - of_nat c) / (of_nat p :: rat) = of_int (r - int c) / of_nat p" by simp
      also have "\<dots> = of_int q" unfolding q using p0 by simp
      finally show "(of_int r - of_nat c) / of_nat p = (of_int ((r - int c) div int p) :: rat)"
        unfolding qd .
    qed
    show ?thesis unfolding distribPoles_def SU image_Un e1 far_def ..
  qed
  have hT: "\<And>r s. r \<in> near \<Longrightarrow> s \<in> near \<Longrightarrow>
    r \<noteq> s \<Longrightarrow> \<not> int p dvd (r - s)"
  proof -
    fix r s assume r: "r \<in> near" and s: "s \<in> near" and rs: "r \<noteq> s"
    obtain r0 where r0: "r0 \<in> Sn" "r = (r0 - int c) div int p" using r unfolding near_def
      by blast
    obtain s0 where s0: "s0 \<in> Sn" "s = (s0 - int c) div int p" using s unfolding near_def
      by blast
    have r0S: "r0 \<in> S" and s0S: "s0 \<in> S" using r0(1) s0(1) by (simp_all add: Sn_def)
    have "int p dvd (r0 - int c)" using r0(1) by (simp add: Sn_def)
    hence dr: "r0 - int c = int p * r" unfolding r0(2) by simp
    have "int p dvd (s0 - int c)" using s0(1) by (simp add: Sn_def)
    hence ds: "s0 - int c = int p * s" unfolding s0(2) by simp
    have "int (2 * K) < int (p ^ 2)" using K1 by (simp only: of_nat_less_iff)
    hence K1': "2 * int K < int p ^ 2" by simp
    show "\<not> int p dvd (r - s)"
    proof
      assume "int p dvd (r - s)"
      then obtain t where t: "r - s = int p * t" by (elim dvdE)
      have "r0 - s0 = (r0 - int c) - (s0 - int c)" by simp
      also have "\<dots> = int p * (r - s)" unfolding dr ds by (simp add: right_diff_distrib)
      also have "\<dots> = int p ^ 2 * t" unfolding t by (simp add: power2_eq_square)
      finally have e: "r0 - s0 = int p ^ 2 * t" .
      have dv: "int p ^ 2 dvd (r0 - s0)" unfolding e by simp
      have "\<bar>r0 - s0\<bar> \<le> \<bar>r0\<bar> + \<bar>s0\<bar>" by (rule abs_triangle_ineq4)
      hence bnd: "\<bar>r0 - s0\<bar> < int p ^ 2" using hS[OF r0S] hS[OF s0S] K1' by linarith
      have "r0 - s0 = 0"
      proof (rule ccontr)
        assume "r0 - s0 \<noteq> 0"
        from dvd_imp_le_int[OF this dv] bnd show False by simp
      qed
      hence "r = s" using r0(2) s0(2) by simp
      with rs show False ..
    qed
  qed
  have hd: "\<And>r. r \<in> near \<Longrightarrow> dIdx r < p"
  proof -
    fix r assume r: "r \<in> near"
    obtain r0 where r0: "r0 \<in> Sn" "r = (r0 - int c) div int p" using r unfolding near_def
      by blast
    have r0S: "r0 \<in> S" using r0(1) by (simp add: Sn_def)
    have "int p dvd (r0 - int c)" using r0(1) by (simp add: Sn_def)
    hence dr: "r0 - int c = int p * r" unfolding r0(2) by simp
    have ab: "\<bar>r0\<bar> \<le> int K" by (rule hS[OF r0S])
    have "int (K + p) < int (p ^ 2)" using K2 by (simp only: of_nat_less_iff)
    hence K2': "int K + int p < int p * int p" by (simp add: power2_eq_square)
    have pp: "0 < int p" using p by (simp add: prime_gt_0_nat)
    have ci: "int c < int p" using c by simp
    have up: "int p * r < int p * int p" using dr ab K2' ci unfolding abs_le_iff by linarith
    have lo: "int p * (- int p) < int p * r" using dr ab K2' ci unfolding abs_le_iff by linarith
    have "r < int p" using up pp by (simp add: mult_less_cancel_left)
    moreover have "- int p < r"
    proof (rule ccontr)
      assume "\<not> - int p < r"
      hence "r \<le> - int p" by simp
      hence "int p * r \<le> int p * (- int p)" using pp by (intro mult_left_mono) simp_all
      thus False using lo by linarith
    qed
    ultimately show "dIdx r < p" unfolding dIdx_def by (simp add: nat_less_iff)
  qed
  have hFv: "\<And>s. s \<in> far \<Longrightarrow> vp p s = - 1"
  proof -
    fix s assume "s \<in> far"
    then obtain r0 where r0: "r0 \<in> Sf" "s = (of_int r0 - of_nat c) / of_nat p"
      unfolding far_def by blast
    have nd: "\<not> int p dvd (r0 - int c)" using r0(1) by (simp add: Sf_def)
    have "s = of_int (r0 - int c) / of_nat p" unfolding r0(2) by simp
    thus "vp p s = - 1" using vp_int_div_p[OF p nd] by simp
  qed
  have U0: "vpGge p (N * F) 0" using FG
    by (intro vpGge_mul[OF p N0, of _ 0, simplified]) (simp add: FarGood_def)
  have U1: "\<And>d. p + 1 < d \<Longrightarrow> vge p (Polynomial.coeff (N * F) d) 1"
    by (rule coeff_high_vge[OF p N0 FG]) (use Nd e in simp)
  have dU: "degree (N * F) \<le> M"
  proof -
    have Le: "L = [:of_nat c, of_nat p:]" unfolding L_def by (simp add: monom_Suc)
    have "degree L = 1" unfolding Le using p0 by simp
    hence "degree (pcompose P L) = degree P" by (simp add: degree_pcompose)
    moreover have "degree (pcompose P L) = degree (N * F)" unfolding Q using p0
      by (simp add: mult.assoc)
    ultimately show ?thesis using dP by simp
  qed
  have num: "distribNum p S P c = [:of_nat p powi (int e - int (card Sn)) * (- 1) ^ card Sf:] *
               ([:(- of_nat p) powi (- int (card far)):] * (N * F))"
  proof -
    have pp: "(of_nat p :: rat) powi (int e - int (card Sn)) * of_nat p powi (- int (card Sf)) =
        of_nat p powi (- int (card S)) * of_nat p ^ e"
    proof -
      have "(of_nat p :: rat) powi (int e - int (card Sn)) * of_nat p powi (- int (card Sf)) =
          of_nat p powi (int e - int (card Sn) + - int (card Sf))"
        by (rule power_int_add[symmetric]) (use p0 in simp)
      also have "\<dots> = of_nat p powi (- int (card S) + int e)"
        by (rule arg_cong[where f = "\<lambda>k. (of_nat p :: rat) powi k"]) (use cardS in simp)
      also have "\<dots> = of_nat p powi (- int (card S)) * of_nat p powi (int e)"
        by (rule power_int_add) (use p0 in simp)
      also have "\<dots> = of_nat p powi (- int (card S)) * of_nat p ^ e"
        by (simp add: power_int_of_nat)
      finally show ?thesis .
    qed
    have mm: "((- 1 :: rat) ^ card Sf) * (- 1) ^ card Sf = 1"
      by (simp add: power_mult_distrib[symmetric])
    have ng: "(- (of_nat p :: rat)) powi (- int (card Sf)) =
      (- 1) ^ card Sf * of_nat p powi (- int (card Sf))"
    proof -
      have i1: "inverse ((- 1 :: rat) ^ card Sf) = (- 1) ^ card Sf"
        by (cases "even (card Sf)") (simp_all add: neg_one_even_power neg_one_odd_power)
      show ?thesis unfolding power_int_minus power_int_of_nat power_minus[of "of_nat p :: rat"]
        inverse_mult_distrib i1 ..
    qed
    have k: "of_nat p powi (- int (card S)) * of_nat p ^ e =
        (of_nat p powi (int e - int (card Sn)) * (- 1) ^ card Sf) *
          ((- of_nat p) powi (- int (card far)) :: rat)"
    proof -
      have "(of_nat p powi (int e - int (card Sn)) * (- 1) ^ card Sf) *
        ((- of_nat p) powi (- int (card far)) :: rat) =
          ((- 1) ^ card Sf * (- 1) ^ card Sf) * (of_nat p powi (int e - int (card Sn)) *
            of_nat p powi (- int (card Sf)))"
        unfolding cardfar ng by (simp only: mult_ac)
      also have "\<dots> = of_nat p powi (- int (card S)) * of_nat p ^ e" unfolding mm pp by simp
      finally show ?thesis by (rule sym)
    qed
    have g1: "[:x:] * ([:y:] * N * F) = Polynomial.smult (x * y) (N * F)" for x y :: rat
      by (simp add: mult_ac)
    have g2: "[:x:] * ([:y:] * (N * F)) = Polynomial.smult (x * y) (N * F)" for x y :: rat
      by (simp add: mult.commute)
    show ?thesis unfolding distribNum_def L_def[symmetric] Q g1 g2 k ..
  qed
  have ext: "vpGge p (tauExt_tr p (Yp_tr p M) ([:(- of_nat p) powi (- int (card far)):] * (N *
    F)) (of_int ` near \<union> far) M) 0"
    by (rule tauX_far_pole_valuation[OF p p7 finnear finfar hT hd hFv vpGge_Yp_tr[OF p p7] U0 U1
      dU])
  have cv: "vge p (of_nat p powi (int e - int (card Sn)) * (- 1) ^ card Sf) (of_int (int e -
    int (card Sn)))"
  proof -
    have v1: "vge p (of_nat p powi (int e - int (card Sn))) (of_int (int e - int (card Sn)))"
      by (simp add: vge_def vp_def qmultiplicity_power_int[OF p])
    have v2: "vge p ((- 1) ^ card Sf) 0" using vge_of_int[OF p, of "(- 1) ^ card Sf"] by simp
    from vge_mul[OF p v1 v2] show ?thesis by simp
  qed
  show ?thesis
    unfolding poles num tauExt_tr_C_mul[where a =
      "of_nat p powi (int e - int (card Sn)) * (- 1) ^ card Sf"] Sn_def[symmetric]
    using vpGge_mul[OF p vpGge_C[OF cv] ext] by simp
qed

lemma finite_signedPoles: "finite S \<Longrightarrow> finite (signedPoles S)"
  by (simp add: signedPoles_def)

lemma signedPoles_abs_le: "r \<in> signedPoles {1..K} \<Longrightarrow> \<bar>r\<bar> \<le> int K"
  by (auto simp: signedPoles_def)

lemma nearCount_eq_card: "nearCount p K c = card {r \<in>
  signedPoles {1..K}. int p dvd (r - int c)}"
  by (simp add: nearCount_def)

text \<open>The inner-range entry bound, generic form (Lean: @{text entry_generic}):
  if every class @{text c}
  gives @{text "B + 4 \<le> e_c - n_c"} with @{text "e_c \<le> p + 1"}, then
  @{text "v_p^G(mu_X(\<Prod>(t + j^2)^{k_j} / D_K)) \<ge> B"}.  Uses (3.1),
    Lemma 3.2 and the summand bounds.\<close>
theorem entry_generic:
  assumes p: "prime p" and p7: "7 \<le> p" and K1: "2 * K < p ^ 2" and K2: "K + p <
    p ^ 2" and J: "finite J"
    and hB: "\<And>c. c < p \<Longrightarrow>
      B + 4 \<le> of_nat (eNum p c J k) - of_nat (nearCount p K c)"
    and hdeg: "\<And>c. c < p \<Longrightarrow> eNum p c J k \<le> p + 1"
  shows "vpGge p (muX {1..K} (\<Prod> j \<in> J. (pX + [:of_nat j ^ 2:]) ^ k j)) B"
proof -
  define S where "S = signedPoles {1..K}"
  define P where "P = [:(- 1) ^ card {1..K}:] * pX ^ 5 * pcompose (\<Prod> j \<in>
    J. (pX + [:of_nat j ^ 2:]) ^ k j) (- (pX ^ 2))"
  have finS: "finite S" by (simp add: S_def finite_signedPoles)
  have pb: "muX {1..K} (\<Prod> j \<in> J. (pX + [:of_nat j ^ 2:]) ^ k j) = tauX S P"
    unfolding S_def P_def by (rule pullback) auto
  have \<epsilon>: "vge p ((- 1) ^ card {1..K}) 0"
    using vge_of_int[OF p, of "(- 1) ^ card {1..K}"] by simp
  obtain M0 where M0: "\<And>M. M0 \<le> M \<Longrightarrow>
      vpGge p (tauX S P - [:of_nat p powi (- 4):] *
               (\<Sum> a < p. tauExt_tr p (Yp_tr p M) (distribNum p S P a) (distribPoles p S a) M))
                 B"
    using tauX_distribution_formula[OF p p7 finS, of P B] by blast
  define M where "M = max M0 (degree P)"
  have summand: "\<And>c. c < p \<Longrightarrow>
      vpGge p (tauExt_tr p (Yp_tr p M) (distribNum p S P c) (distribPoles p S c) M) (B + 4)"
  proof -
    fix c assume c: "c < p"
    have "vpGge p (tauExt_tr p (Yp_tr p M) (distribNum p S P c) (distribPoles p S c) M)
            (of_int (int (eNum p c J k) - int (card {r \<in> S. int p dvd (r - int c)})))"
      unfolding P_def
      by (rule summand_bound_tr[OF p p7 K1 K2 finS _ c decomp_pullback[OF p J \<epsilon>] hdeg[OF
        c]])
         (use signedPoles_abs_le in \<open>auto simp: S_def M_def P_def\<close>)
    thus "vpGge p (tauExt_tr p (Yp_tr p M) (distribNum p S P c) (distribPoles p S c) M) (B + 4)"
    proof (rule vpGge_mono)
      show "B + 4 \<le> of_int (int (eNum p c J k) - int (card {r \<in> S. int p dvd (r - int c)}))"
        using hB[OF c] unfolding nearCount_eq_card S_def by simp
    qed
  qed
  have sumv: "vpGge p ([:of_nat p powi (- 4):] *
      (\<Sum> a < p. tauExt_tr p (Yp_tr p M) (distribNum p S P a) (distribPoles p S a) M)) B"
  proof -
    have c4: "vpGge p [:of_nat p powi (- 4):] (- 4)"
      by (rule vpGge_C) (simp add: vge_def vp_def qmultiplicity_power_int[OF p])
    have "vpGge p (\<Sum> a < p. tauExt_tr p (Yp_tr p M) (distribNum p S P a) (distribPoles p S a)
      M) (B + 4)"
      by (rule vpGge_sum[OF p]) (use summand in auto)
    from vpGge_mul[OF p c4 this] show ?thesis by simp
  qed
  have "vpGge p (tauX S P) B"
    using vpGge_add[OF p M0[of M] sumv] by (simp add: M_def)
  thus ?thesis by (simp only: pb)
qed

subsection \<open>The inner entry bounds (4.2)/(4.3)\<close>

text \<open>The class of a residue: @{text "cls p j = min(j mod p, p - j mod p)"}.\<close>
definition cls :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "cls p j =
  min (j mod p) (p - j mod p)"

text \<open>Exponent of @{text "t + j^2"} in the inner row @{text "E_x"}.\<close>
definition nu :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times>
  nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nu K M p x j = (if j \<le> mHalf p then (if j = fst x then snd x else nat (Lin K M p j)) else 0)"

text \<open>The index set and the exponents of the numerator @{text "D_N^6 E_x E_y"}.\<close>
definition Jset :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where "Jset K p =
  {1..Nof K} \<union> {..mHalf p}"

definition kexp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times>
  nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "kexp K M p x y j = 6 * (if j \<in> {1..Nof K} then 1 else 0) + nu K M p x j + nu K M p y j"

text \<open>Multiplicity of a class: 2 for the zero class, 1 otherwise.\<close>
definition mult :: "nat \<Rightarrow> nat" where "mult c = (if c = 0 then 2 else 1)"

lemma mem_inner_idx:
  "x \<in> set (inner_idx K M p) \<longleftrightarrow> fst x \<le> mHalf p \<and>
    snd x < nat (Lin K M p (fst x))"
  by (cases x) (auto simp: inner_idx_def image_iff simp del: upt_Suc)

lemma innerBasis_eq_prod:
  assumes "fst x \<le> mHalf p"
  shows "innerBasis K M p x = (\<Prod> j \<le> mHalf p. (pX + [:of_nat j ^ 2:]) ^ nu K M p x j)"
proof -
  have a: "fst x \<in> {..mHalf p}" using assms by simp
  have n: "nu K M p x (fst x) = snd x" using assms by (simp add: nu_def)
  have c: "(\<Prod> j \<in> {..mHalf p} - {fst x}. (pX + [:of_nat j ^ 2:]) ^ nu K M p x j) =
      (\<Prod> c \<in> {0..mHalf p} - {fst x}. (pX + [:of_nat c ^ 2:]) ^ nat (Lin K M p c))"
    by (rule prod.cong) (auto simp: nu_def)
  show ?thesis unfolding innerBasis_def prod.remove[OF finite_atMost a] n c by (rule mult.commute)
qed

lemma numerator_eq:
  assumes "fst x \<le> mHalf p" "fst y \<le> mHalf p"
  shows "Dm (Nof K) ^ 6 * innerBasis K M p x * innerBasis K M p y =
         (\<Prod> j \<in> Jset K p. (pX + [:of_nat j ^ 2:]) ^ kexp K M p x y j)"
proof -
  have fin: "finite (Jset K p)" by (simp add: Jset_def)
  have e1: "(\<Prod> j \<in> Jset K p. (pX + [:of_nat j ^ 2:]) ^ (6 * (if j \<in>
    {1..Nof K} then 1 else 0))) = Dm (Nof K) ^ 6"
  proof -
    have "(\<Prod> j \<in> Jset K p. (pX + [:of_nat j ^ 2:]) ^ (6 * (if j \<in>
      {1..Nof K} then 1 else 0))) =
        (\<Prod> j = 1..Nof K. (pX + [:of_nat j ^ 2:]) ^ 6)"
      by (rule prod.mono_neutral_cong_right[OF fin]) (auto simp: Jset_def)
    also have "\<dots> = Dm (Nof K) ^ 6" unfolding Dm_def by (rule prod_power_distrib[symmetric])
    finally show ?thesis .
  qed
  have e2: "(\<Prod> j \<in> Jset K p. (pX + [:of_nat j ^ 2:]) ^ nu K M p z j) =
    innerBasis K M p z" if "fst z \<le> mHalf p" for z
  proof -
    have "(\<Prod> j \<in> Jset K p. (pX + [:of_nat j ^ 2:]) ^ nu K M p z j) = (\<Prod> j \<le>
      mHalf p. (pX + [:of_nat j ^ 2:]) ^ nu K M p z j)"
      by (rule prod.mono_neutral_cong_right[OF fin]) (auto simp: Jset_def nu_def)
    also have "\<dots> = innerBasis K M p z" by (rule innerBasis_eq_prod[OF that, symmetric])
    finally show ?thesis .
  qed
  have "(\<Prod> j \<in> Jset K p. (pX + [:of_nat j ^ 2:]) ^ kexp K M p x y j) =
      (\<Prod> j \<in> Jset K p. (pX + [:of_nat j ^ 2:]) ^ (6 * (if j \<in>
        {1..Nof K} then 1 else 0))) *
      (\<Prod> j \<in> Jset K p. (pX + [:of_nat j ^ 2:]) ^ nu K M p x j) * (\<Prod> j \<in>
        Jset K p. (pX + [:of_nat j ^ 2:]) ^ nu K M p y j)"
    unfolding kexp_def power_add prod.distrib ..
  thus ?thesis unfolding e1 e2[OF assms(1)] e2[OF assms(2)] by (rule sym)
qed

lemma cls_le: "odd p \<Longrightarrow> cls p j \<le> mHalf p"
proof -
  assume "odd p"
  then obtain m where pm: "p = 2 * m + 1" by (elim oddE)
  have "j mod p < p" using pm by simp
  thus ?thesis unfolding cls_def mHalf_def pm by (auto simp: min_def)
qed

lemma cls_small: "odd p \<Longrightarrow> j \<le> mHalf p \<Longrightarrow> cls p j = j"
proof -
  assume "odd p" and j: "j \<le> mHalf p"
  then obtain m where pm: "p = 2 * m + 1" by (elim oddE)
  have "j \<le> m" using j unfolding mHalf_def pm by simp
  thus ?thesis unfolding cls_def pm by (simp add: min_def)
qed

lemma mod_add_zero_iff_aux:
  fixes r c p :: nat
  assumes "r < p" "c < p"
  shows "(r + c) mod p = 0 \<longleftrightarrow> r + c = 0 \<or> r + c = p"
proof (cases "r + c < p")
  case True
  thus ?thesis by simp
next
  case False
  hence "(r + c) mod p = (r + c - p) mod p" by (simp add: le_mod_geq)
  also have "\<dots> = r + c - p" using assms by simp
  finally show ?thesis using False by auto
qed

lemma cls_eq_iff:
  assumes "odd p" "a \<le> mHalf p"
  shows "cls p j = a \<longleftrightarrow> j mod p = a \<or> j mod p + a = p"
proof -
  obtain m where pm: "p = 2 * m + 1" using assms(1) by (elim oddE)
  have "j mod p < p" using pm by simp
  moreover have "a \<le> m" using assms(2) unfolding mHalf_def pm by simp
  ultimately show ?thesis unfolding cls_def pm by (auto simp: min_def)
qed

lemma omg_eq:
  assumes "odd p" "c < p"
  shows "omg p c j = (if cls p j = cls p c then mult c else 0)"
proof -
  have p0: "0 < p" using assms(2) by simp
  define r where "r = j mod p"
  have r: "r < p" using p0 by (simp add: r_def)
  have d1: "int p dvd (int j - int c) \<longleftrightarrow> r = c"
  proof -
    have "int p dvd (int j - int c) \<longleftrightarrow> int j mod int p = int c mod int p"
      by (simp add: mod_eq_dvd_iff)
    also have "\<dots> \<longleftrightarrow> j mod p = c mod p"
      by (simp only: of_nat_mod[symmetric] of_nat_eq_iff)
    finally show ?thesis using assms(2) by (simp add: r_def)
  qed
  have d2: "int p dvd (int j + int c) \<longleftrightarrow> r + c = 0 \<or> r + c = p"
  proof -
    have "int p dvd (int j + int c) \<longleftrightarrow> p dvd (j + c)"
      by (metis int_dvd_int_iff of_nat_add)
    also have "\<dots> \<longleftrightarrow> (r + c) mod p = 0"
      by (simp add: r_def dvd_eq_mod_eq_0 mod_add_left_eq)
    also have "\<dots> \<longleftrightarrow> r + c = 0 \<or> r + c = p"
      by (rule mod_add_zero_iff_aux[OF r assms(2)])
    finally show ?thesis .
  qed
  have np: "c + c \<noteq> p" using assms(1) by presburger
  have cj: "cls p j = min r (p - r)" by (simp add: cls_def r_def)
  have cc: "cls p c = min c (p - c)" using assms(2) by (simp add: cls_def)
  show ?thesis unfolding omg_def d1 d2 cj cc mult_def using r assms(2) np by (auto simp: min_def)
qed

lemma sum_omg:
  assumes "odd p" "c < p"
  shows "(\<Sum> j = 1..A. omg p c j) = mult c * ell p A (cls p c)"
proof -
  have p0: "0 < p" using assms(2) by simp
  define a where "a = cls p c"
  have am: "a \<le> mHalf p" unfolding a_def by (rule cls_le[OF assms(1)])
  have ap: "a < p" using am p0 by (simp add: mHalf_def)
  have m2: "(j + a) mod p = 0 \<longleftrightarrow> j mod p + a = 0 \<or> j mod p + a = p" for j
    using mod_add_zero_iff_aux[OF _ ap, of "j mod p"] p0 by (simp add: mod_add_left_eq)
  have S: "{j \<in> {1..A}. cls p j = a} = {j \<in> {1..A}. j mod p = a mod p \<or>
    (j + a) mod p = 0}"
    using cls_eq_iff[OF assms(1) am] m2 ap by auto
  have "(\<Sum> j = 1..A. omg p c j) = (\<Sum> j \<in> {j \<in> {1..A}. cls p j = a}. mult c)"
    unfolding omg_eq[OF assms] a_def sum.inter_filter[OF finite_atLeastAtMost] ..
  also have "\<dots> = mult c * card {j \<in> {1..A}. cls p j = a}" by simp
  also have "\<dots> = mult c * ell p A (cls p c)" unfolding S unfolding ell_def a_def ..
  finally show ?thesis .
qed

lemma nearCount_eq:
  assumes "prime p"
  shows "nearCount p K c = (\<Sum> j = 1..K. omg p c j)"
proof -
  have n: "int p dvd (- int j - int c) \<longleftrightarrow> int p dvd (int j + int c)" for j
  proof -
    have eq: "- int j - int c = - (int j + int c)" by simp
    show ?thesis unfolding eq dvd_minus_iff ..
  qed
  have U: "{r \<in> int ` {1..K} \<union> (\<lambda>j. - int j) ` {1..K}. int p dvd (r - int c)} =
      int ` {j \<in> {1..K}. int p dvd (int j - int c)} \<union> (\<lambda>j. - int j) ` {j \<in>
        {1..K}. int p dvd (int j + int c)}"
    using n by auto
  have c1: "card (int ` {j \<in> {1..K}. P j}) = card {j \<in> {1..K}. P j}" for P
    by (rule card_image) (simp add: inj_on_def)
  have c2: "card ((\<lambda>j. - int j) ` {j \<in> {1..K}. P j}) = card {j \<in> {1..K}. P j}" for P
    by (rule card_image) (simp add: inj_on_def)
  have ind: "(\<Sum> j \<in> {1..K}. (if P j then 1 else 0 :: nat)) = card {j \<in> {1..K}. P j}"
    for P
    by (simp add: sum.inter_filter[OF finite_atLeastAtMost, symmetric])
  have "nearCount p K c = card (int ` {j \<in> {1..K}. int p dvd (int j - int c)} \<union>
      (\<lambda>j. - int j) ` {j \<in> {1..K}. int p dvd (int j + int c)})"
    unfolding nearCount_def signedPoles_def U ..
  also have "\<dots> = card (int ` {j \<in> {1..K}. int p dvd (int j - int c)}) +
      card ((\<lambda>j. - int j) ` {j \<in> {1..K}. int p dvd (int j + int c)})"
    by (rule card_Un_disjoint; force+)
  also have "\<dots> = card {j \<in> {1..K}. int p dvd (int j - int c)} + card {j \<in>
    {1..K}. int p dvd (int j + int c)}"
    unfolding c1 c2 ..
  also have "\<dots> = (\<Sum> j = 1..K. omg p c j)" unfolding omg_def sum.distrib ind ..
  finally show ?thesis .
qed

lemma cls_zero: "cls p 0 = 0"
  by (simp add: cls_def)

lemma cls_pos: "c \<noteq> 0 \<Longrightarrow> c < p \<Longrightarrow> 1 \<le> cls p c"
  by (simp add: cls_def)

lemma ell_zero_eq: "0 < p \<Longrightarrow> ell p A 0 = A div p"
proof -
  assume p: "0 < p"
  have e: "{j \<in> {1..A}. j mod p = 0 mod p \<or> (j + 0) mod p = 0} = {j \<in> {1..A}. p dvd j}"
    by (auto simp: dvd_eq_mod_eq_0)
  show ?thesis unfolding ell_def e by (rule card_multiples_upto[OF p])
qed

lemma eNum_eq:
  assumes "odd p" "c < p"
  shows "eNum p c (Jset K p) (kexp K M p x y) =
         5 * (if c = 0 then 1 else 0) +
         mult c * (6 * ell p (Nof K) (cls p c) + nu K M p x (cls p c) + nu K M p y (cls p c))"
proof -
  have fin: "finite (Jset K p)" by (simp add: Jset_def)
  have dc: "int p dvd int c \<longleftrightarrow> c = 0" using assms(2) by (auto dest: dvd_imp_le)
  have s1: "(\<Sum> j \<in> Jset K p. (if j \<in> {1..Nof K} then 1 else 0) * omg p c j) =
    mult c * ell p (Nof K) (cls p c)"
  proof -
    have "(\<Sum> j \<in> Jset K p. (if j \<in> {1..Nof K} then 1 else 0) * omg p c j) = (\<Sum> j =
      1..Nof K. omg p c j)"
      by (rule sum.mono_neutral_cong_right[OF fin]) (auto simp: Jset_def)
    also have "\<dots> = mult c * ell p (Nof K) (cls p c)" by (rule sum_omg[OF assms])
    finally show ?thesis .
  qed
  have s2: "(\<Sum> j \<in> Jset K p. nu K M p z j * omg p c j) = nu K M p z (cls p c) * mult c"
    for z
  proof -
    have "(\<Sum> j \<in> Jset K p. nu K M p z j * omg p c j) = (\<Sum> j \<le> mHalf p.
      if j = cls p c then nu K M p z j * mult c else 0)"
      by (rule sum.mono_neutral_cong_right[OF fin]) (auto simp: Jset_def nu_def omg_eq[OF assms]
        cls_small[OF assms(1)])
    also have "\<dots> = nu K M p z (cls p c) * mult c" using cls_le[OF assms(1), of c] by simp
    finally show ?thesis .
  qed
  have "eNum p c (Jset K p) (kexp K M p x y) = 5 * (if int p dvd int c then 1 else 0) +
      (6 * (\<Sum> j \<in> Jset K p. (if j \<in> {1..Nof K} then 1 else 0) * omg p c j) +
       (\<Sum> j \<in> Jset K p. nu K M p x j * omg p c j) + (\<Sum> j \<in>
         Jset K p. nu K M p y j * omg p c j))"
    unfolding eNum_def kexp_def by (simp add: sum.distrib sum_distrib_left algebra_simps)
  also have "\<dots> = 5 * (if c = 0 then 1 else 0) +
      mult c * (6 * ell p (Nof K) (cls p c) + nu K M p x (cls p c) + nu K M p y (cls p c))"
    unfolding s1 s2 dc by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma count_mod_ge: "0 < p \<Longrightarrow> 1 \<le> r \<Longrightarrow> r < p \<Longrightarrow>
  A div p \<le> card {j \<in> {1..A}. j mod p = r}"
proof -
  assume p: "0 < p" and r1: "1 \<le> r" and rp: "r < p"
  have sub: "(\<lambda>t. t * p + r) ` {..<A div p} \<subseteq> {j \<in> {1..A}. j mod p = r}"
  proof
    fix j assume "j \<in> (\<lambda>t. t * p + r) ` {..<A div p}"
    then obtain t where t: "t < A div p" "j = t * p + r" by blast
    have "Suc t * p \<le> A div p * p" using t(1) by (intro mult_le_mono1) simp
    also have "\<dots> \<le> A" by (rule div_times_less_eq_dividend)
    finally have "t * p + p \<le> A" by simp
    thus "j \<in> {j \<in> {1..A}. j mod p = r}" using t r1 rp by simp
  qed
  have inj: "inj_on (\<lambda>t. t * p + r) {..<A div p}" using p by (auto intro: inj_onI)
  have "card ((\<lambda>t. t * p + r) ` {..<A div p}) \<le> card {j \<in> {1..A}. j mod p = r}"
    by (rule card_mono[OF _ sub]) simp
  thus ?thesis using card_image[OF inj] by simp
qed

lemma count_mod_le: "0 < p \<Longrightarrow> 1 \<le> r \<Longrightarrow> r < p \<Longrightarrow>
  card {j \<in> {1..A}. j mod p = r} \<le> A div p + 1"
proof -
  assume p: "0 < p"
  show ?thesis by (rule card_cong_class_le[OF p]) auto
qed

lemma ell_bounds:
  assumes "odd p" "1 \<le> a" "a \<le> mHalf p"
  shows "2 * (A div p) \<le> ell p A a \<and> ell p A a \<le> 2 * (A div p) + 2"
proof -
  have p0: "0 < p" using assms(1) by (rule odd_pos)
  have ap: "a < p" using assms(3) p0 by (simp add: mHalf_def)
  have np: "a \<noteq> p - a" using assms(1) ap by presburger
  have m: "(j + a) mod p = 0 \<longleftrightarrow> j mod p = p - a" for j
  proof -
    have r: "j mod p < p" using p0 by simp
    have "(j + a) mod p = 0 \<longleftrightarrow> j mod p + a = 0 \<or> j mod p + a = p"
      using mod_add_zero_iff_aux[OF r ap] by (simp add: mod_add_left_eq)
    thus ?thesis using assms(2) ap r by auto
  qed
  have e: "{j \<in> {1..A}. j mod p = a mod p \<or> (j + a) mod p = 0} =
      {j \<in> {1..A}. j mod p = a} \<union> {j \<in> {1..A}. j mod p = p - a}"
    using m ap by auto
  have "ell p A a = card {j \<in> {1..A}. j mod p = a} + card {j \<in> {1..A}. j mod p = p - a}"
    unfolding ell_def e by (rule card_Un_disjoint) (use np in auto)
  moreover have "A div p \<le> card {j \<in> {1..A}. j mod p = a}"
    by (rule count_mod_ge[OF p0 assms(2) ap])
  moreover have "A div p \<le> card {j \<in> {1..A}. j mod p = p - a}"
    by (rule count_mod_ge[OF p0]) (use assms(2) ap in auto)
  moreover have "card {j \<in> {1..A}. j mod p = a} \<le> A div p + 1"
    by (rule count_mod_le[OF p0 assms(2) ap])
  moreover have "card {j \<in> {1..A}. j mod p = p - a} \<le> A div p + 1"
    by (rule count_mod_le[OF p0]) (use assms(2) ap in auto)
  ultimately show ?thesis by linarith
qed

lemma hyp_facts:
  assumes "prime p" "InnerHyp K M p"
  shows "7 \<le> p \<and> odd p \<and> 2 * mHalf p + 1 = p \<and> K div p < M \<and>
    Nof K div p < M"
proof -
  have b: "200 * M < p" using innerHyp_bounds[OF assms(2)] by blast
  have H: "40 \<le> M" "K < p * M" using assms(2) by (auto simp: InnerHyp_def)
  have p7: "7 \<le> p" using b H by linarith
  have o: "odd p" using prime_odd_nat[OF assms(1)] p7 by simp
  have mp: "2 * mHalf p + 1 = p" using o unfolding mHalf_def by (auto elim: oddE)
  have kd: "K div p < M" using H(2) p7 by (simp add: div_less_iff_less_mult mult.commute)
  have "Nof K div p \<le> K div p" by (rule div_le_mono) (simp add: Nof_def)
  hence "Nof K div p < M" using kd by linarith
  with p7 o mp kd show ?thesis by simp
qed

lemma Tin_le:
  assumes "prime p" "InnerHyp K M p"
  shows "Tin K M p \<le> 4 * int M"
proof -
  have T0: "0 \<le> Ein K M p" and Em: "int (mHalf p) * Tin K M p + Ein K M p = rhs44 K M p"
    using TE_spec[OF assms] by blast+
  have H: "40 \<le> M" "40 dvd K" "200 * M ^ 2 \<le> K" "K < p * M" using assms(2)
    by (auto simp: InnerHyp_def)
  obtain k where Kk: "K = 40 * k" using H(2) by (elim dvdE)
  have hk: "hof K = 37 * k" and Nk: "Nof K = 3 * k" unfolding Kk hof_def Nof_def by simp_all
  have r44: "rhs44 K M p \<le> 46 * int k" unfolding rhs44_def hk Nk L0_def by simp
  have mp: "2 * mHalf p + 1 = p" using hyp_facts[OF assms] by blast
  define m where "m = int (mHalf p)"
  have m0: "0 \<le> m" by (simp add: m_def)
  have ip: "int p = 2 * m + 1" unfolding m_def using mp by linarith
  have pM: "int p * int M = 2 * (m * int M) + int M" unfolding ip by (simp add: algebra_simps)
  have "int K < int (p * M)" using H(4) by (simp only: of_nat_less_iff)
  hence KpM: "40 * int k < int p * int M" unfolding Kk by simp
  have "M \<le> M * M" by (rule le_square)
  hence "M \<le> k" using H(3) Kk unfolding power2_eq_square by linarith
  hence kM: "int M \<le> int k" by simp
  show ?thesis
  proof (rule ccontr)
    assume "\<not> Tin K M p \<le> 4 * int M"
    hence "4 * int M + 1 \<le> Tin K M p" by simp
    hence "m * (4 * int M + 1) \<le> m * Tin K M p" using m0 by (rule mult_left_mono)
    hence "4 * (m * int M) + m \<le> m * Tin K M p" by (simp add: algebra_simps)
    moreover have "m * Tin K M p \<le> 46 * int k" using Em T0 r44 unfolding m_def by linarith
    ultimately show False using pM KpM kM m0 by linarith
  qed
qed

lemma Lin_le:
  assumes "prime p" "InnerHyp K M p" "a \<le> mHalf p"
  shows "Lin K M p a \<le> 4 * int M + 10"
proof (cases "a = 0")
  case True
  thus ?thesis by (simp add: Lin_def L0_def)
next
  case False
  have "epsIn K M p a \<le> 1" by (simp add: epsIn_def)
  moreover have "0 \<le> bIn K p a" by (simp add: bIn_def)
  moreover have "Lin K M p a = Tin K M p - bIn K p a + epsIn K M p a" using False
    by (simp add: Lin_def)
  ultimately show ?thesis using Tin_le[OF assms(1,2)] by linarith
qed

lemma nu_le:
  assumes "prime p" "InnerHyp K M p" "x \<in> set (inner_idx K M p)"
  shows "nu K M p x j \<le> 4 * M + 10"
proof -
  have m: "fst x \<le> mHalf p" "snd x < nat (Lin K M p (fst x))" using assms(3)
    by (simp_all add: mem_inner_idx)
  have l: "nat (Lin K M p a) \<le> 4 * M + 10" if "a \<le> mHalf p" for a
    using Lin_le[OF assms(1,2) that] by (simp add: nat_le_iff)
  show ?thesis unfolding nu_def using m l[of "fst x"] l[of j] by auto
qed

lemma ellN_le:
  assumes "prime p" "InnerHyp K M p" "1 \<le> a" "a \<le> mHalf p"
  shows "ell p (Nof K) a \<le> M"
proof -
  have o: "odd p" using hyp_facts[OF assms(1,2)] by blast
  have b: "ell p (Nof K) a \<le> 2 * (Nof K div p) + 2"
    using ell_bounds[OF o assms(3,4), of "Nof K"] by blast
  have H: "40 \<le> M" "K < p * M" using assms(2) by (auto simp: InnerHyp_def)
  have N: "40 * Nof K \<le> 3 * K" by (simp add: Nof_def)
  have q: "Nof K div p * p \<le> Nof K" by (rule div_times_less_eq_dividend)
  have "p * (40 * (Nof K div p)) < p * (3 * M)"
  proof -
    have "p * (40 * (Nof K div p)) = 40 * (Nof K div p * p)" by (simp add: ac_simps)
    also have "\<dots> \<le> 40 * Nof K" using q by simp
    also have "\<dots> \<le> 3 * K" by (rule N)
    also have "\<dots> < 3 * (p * M)" using H(2) by simp
    also have "\<dots> = p * (3 * M)" by (simp add: ac_simps)
    finally show ?thesis .
  qed
  hence "0 < p \<and> 40 * (Nof K div p) < 3 * M" by (simp only: mult_less_cancel1)
  hence "40 * (Nof K div p) < 3 * M" by simp
  thus ?thesis using b H(1) by linarith
qed

lemma eps_key:
  assumes "prime p" "InnerHyp K M p" "a \<in> {1..mHalf p}" "b \<in> {1..mHalf p}"
  shows "2 * (epsIn K M p a - epsIn K M p b) \<le> 2 + int (ell p K a) - int (ell p K b)"
proof -
  define r where "r = (\<lambda>x y. ell p K y < ell p K x \<or> (ell p K x = ell p K y \<and>
    x < y))"
  have rk: "defaultPos K p x = card {c \<in> {1..mHalf p}. r c x}" for x
    by (simp add: defaultPos_def r_def)
  have irr: "\<And>x. \<not> r x x" by (simp add: r_def)
  have tr: "\<And>x y z. r x y \<Longrightarrow> r y z \<Longrightarrow> r x z" unfolding r_def
    by auto
  have tot: "\<And>x y. x \<in> {1..mHalf p} \<Longrightarrow>
    y \<in> {1..mHalf p} \<Longrightarrow> x \<noteq> y \<Longrightarrow> r x y \<or> r y x"
    unfolding r_def by auto
  have iff: "defaultPos K p x < defaultPos K p y \<longleftrightarrow> r x y"
    if "x \<in> {1..mHalf p}" "y \<in> {1..mHalf p}" for x y
    unfolding rk using rank_props(1)[OF finite_atLeastAtMost irr tr tot that] .
  have cnt: "card {c \<in> {1..mHalf p}. defaultPos K p c < defaultPos K p x} = defaultPos K p x"
    if "x \<in> {1..mHalf p}" for x
  proof -
    have "{c \<in> {1..mHalf p}. defaultPos K p c < defaultPos K p x} = {c \<in>
      {1..mHalf p}. r c x}" using iff that by auto
    thus ?thesis using rk[of x] by simp
  qed
  have ea: "epsIn K M p a = (if int (defaultPos K p a) < Ein K M p then 1 else 0)"
    unfolding epsIn_def cnt[OF assms(3)] ..
  have eb: "epsIn K M p b = (if int (defaultPos K p b) < Ein K M p then 1 else 0)"
    unfolding epsIn_def cnt[OF assms(4)] ..
  have o: "odd p" using hyp_facts[OF assms(1,2)] by blast
  have ba: "2 * (K div p) \<le> ell p K a \<and> ell p K a \<le> 2 * (K div p) + 2"
    using ell_bounds[OF o, of a K] assms(3) by auto
  have bb: "2 * (K div p) \<le> ell p K b \<and> ell p K b \<le> 2 * (K div p) + 2"
    using ell_bounds[OF o, of b K] assms(4) by auto
  show ?thesis
  proof (cases "int (defaultPos K p a) < Ein K M p \<and>
    \<not> int (defaultPos K p b) < Ein K M p")
    case True
    hence "defaultPos K p a < defaultPos K p b" by linarith
    hence "r a b" using iff assms(3,4) by blast
    hence "ell p K b \<le> ell p K a" unfolding r_def by auto
    hence "int (ell p K b) \<le> int (ell p K a)" by simp
    thus ?thesis unfolding ea eb using True by simp
  next
    case False
    thus ?thesis unfolding ea eb using ba bb by auto
  qed
qed

text \<open>Half-weight at an ordinary source @{text b}.\<close>
lemma half_ord:
  assumes "prime p" "InnerHyp K M p" "x \<in> set (inner_idx K M p)" "1 \<le> b" "b \<le> mHalf p"
  shows "wInIdx K M p x \<le> of_nat (nu K M p x b) + 3 * of_nat (ell p (Nof K) b) -
    (of_nat (ell p K b) + 4) / 2"
proof -
  obtain a i where x: "x = (a, i)" by (cases x)
  have m: "a \<le> mHalf p" "i < nat (Lin K M p a)" using assms(3) unfolding x
    by (simp_all add: mem_inner_idx)
  have bnz: "b \<noteq> 0" using assms(4) by simp
  have "Lin K M p b = Tin K M p - bIn K p b + epsIn K M p b" using bnz by (simp add: Lin_def)
  moreover have "0 \<le> Lin K M p b" by (rule Lin_nonneg[OF assms(1,2,5)])
  ultimately have ratLb: "(of_nat (nat (Lin K M p b)) :: rat) =
      of_int (Tin K M p) - 3 * of_nat (ell p (Nof K) b) + of_int (epsIn K M p b)"
    by (simp add: bIn_def)
  show ?thesis
  proof (cases "a = 0")
    case True
    have "wInIdx K M p x \<le> of_int (Zin K M p b) - (of_nat (ell p K b) + 4) / 2"
      unfolding wInIdx_def x fst_conv snd_conv wIn_def if_P[OF True]
        by (rule Min_le) (use assms(4,5) in auto)
    moreover have "(of_nat (nu K M p x b) :: rat) =
      of_int (Tin K M p) - 3 * of_nat (ell p (Nof K) b) + of_int (epsIn K M p b)"
      unfolding x nu_def using True assms(5) bnz ratLb by simp
    moreover have "(of_int (Zin K M p b) :: rat) = of_int (Tin K M p) + of_int (epsIn K M p b)"
      by (simp add: Zin_def)
    ultimately show ?thesis by linarith
  next
    case False
    show ?thesis
    proof (cases "a = b")
      case True
      show ?thesis unfolding wInIdx_def x fst_conv snd_conv wIn_def using True bnz
        by (simp add: bIn_def nu_def assms(5))
    next
      case ab: False
      have a1: "a \<in> {1..mHalf p}" using False m(1) by simp
      have b1: "b \<in> {1..mHalf p}" using assms(4,5) by simp
      have La: "Lin K M p a = Tin K M p - bIn K p a + epsIn K M p a" using False
        by (simp add: Lin_def)
      have "int i + 1 \<le> Lin K M p a" using m(2) by arith
      hence r1: "rat_of_int (int i + 1) \<le> rat_of_int (Tin K M p - bIn K p a + epsIn K M p a)"
        unfolding La by (simp only: of_int_le_iff)
      have "2 * (epsIn K M p a - epsIn K M p b) \<le> 2 + int (ell p K a) - int (ell p K b)"
        by (rule eps_key[OF assms(1,2) a1 b1])
      hence r2: "rat_of_int (2 * (epsIn K M p a - epsIn K M p b)) \<le>
        rat_of_int (2 + int (ell p K a) - int (ell p K b))"
        by (simp only: of_int_le_iff)
      have w: "wInIdx K M p x = of_nat i + 3 * of_nat (ell p (Nof K) a) - (of_nat (ell p K a) + 4) /
        2"
        unfolding wInIdx_def x fst_conv snd_conv wIn_def using False by (simp add: bIn_def)
      have nb: "(of_nat (nu K M p x b) :: rat) =
        of_int (Tin K M p) - 3 * of_nat (ell p (Nof K) b) + of_int (epsIn K M p b)"
        unfolding x nu_def using ab assms(5) ratLb by simp
      have "of_nat i + 1 \<le> (of_int (Tin K M p) - 3 * of_nat (ell p (Nof K) a) +
        of_int (epsIn K M p a) :: rat)"
        using r1 by (simp add: bIn_def)
      moreover have "2 * (of_int (epsIn K M p a) - of_int (epsIn K M p b)) \<le>
        (2 + of_nat (ell p K a) - of_nat (ell p K b) :: rat)"
        using r2 by simp
      ultimately show ?thesis unfolding w nb
        by (simp only: distrib_left right_diff_distrib add_divide_distrib diff_divide_distrib;
        linarith)
    qed
  qed
qed

text \<open>Half-weight at the zero source.\<close>
lemma half_zero:
  assumes "prime p" "InnerHyp K M p" "x \<in> set (inner_idx K M p)"
  shows "wInIdx K M p x \<le> 2 * of_nat (nu K M p x 0) + 6 * of_nat (Nof K div p) -
    of_nat (K div p) + 1 / 2"
proof -
  obtain a i where x: "x = (a, i)" by (cases x)
  have m: "a \<le> mHalf p" "i < nat (Lin K M p a)" using assms(3) unfolding x
    by (simp_all add: mem_inner_idx)
  show ?thesis
  proof (cases "a = 0")
    case True
    have w: "wInIdx K M p x \<le> 2 * of_nat i + 6 * of_nat (Nof K div p) - of_nat (K div p) + 1 /
      2"
      unfolding wInIdx_def x fst_conv snd_conv wIn_def if_P[OF True] by (rule Min_le) auto
    have n: "nu K M p x 0 = i" unfolding x nu_def using True by simp
    show ?thesis using w unfolding n .
  next
    case False
    have Tl: "Tin K M p \<le> 4 * int M" by (rule Tin_le[OF assms(1,2)])
    have e: "epsIn K M p a \<le> 1" by (simp add: epsIn_def)
    have L: "Lin K M p a = Tin K M p - bIn K p a + epsIn K M p a" using False by (simp add: Lin_def)
    have iL: "int i + 1 \<le> Lin K M p a" using m(2) by arith
    have n0: "nu K M p x 0 = 4 * M + 10" unfolding x nu_def using False
      by (simp add: Lin_def L0_def)
    have Kq: "K div p < M" using hyp_facts[OF assms(1,2)] by blast
    have w: "wInIdx K M p x = of_nat i + of_int (bIn K p a) - (of_nat (ell p K a) + 4) / 2"
      unfolding wInIdx_def x fst_conv snd_conv wIn_def using False by simp
    have r1: "rat_of_int (int i + 1) \<le> rat_of_int (Tin K M p - bIn K p a + epsIn K M p a)"
      using iL unfolding L by (simp only: of_int_le_iff)
    have r2: "rat_of_int (Tin K M p) \<le> rat_of_int (4 * int M)" using Tl
      by (simp only: of_int_le_iff)
    have r3: "rat_of_int (epsIn K M p a) \<le> rat_of_int 1" using e by (simp only: of_int_le_iff)
    have r4: "(of_nat (K div p) :: rat) \<le> of_nat M" using Kq by simp
    have r5: "(0 :: rat) \<le> of_nat (ell p K a)" "(0 :: rat) \<le> of_nat (Nof K div p)"
      by simp_all
    have c4: "(of_nat (4 * M + 10) :: rat) = 4 * of_nat M + 10" by simp
    have r6: "(0 :: rat) \<le> of_nat M" "(0 :: rat) \<le> of_nat i" by simp_all
    show ?thesis unfolding w n0 c4 using r1 r2 r3 r4 r5 r6
      by (simp only: of_int_add of_int_diff of_int_mult of_int_of_nat_eq of_int_1 of_int_numeral
          distrib_left right_diff_distrib add_divide_distrib diff_divide_distrib; linarith)
  qed
qed

text \<open>(4.2)/(4.3): every entry of the inner Gram matrix satisfies the weights.\<close>
theorem innerGram_entry_bound:
  assumes p: "prime p" and H: "InnerHyp K M p" and x: "x < length (inner_idx K M p)" and y: "y <
    length (inner_idx K M p)"
  shows "vpGge p (innerGram K M p $$ (x, y))
           (wInIdx K M p (inner_idx K M p ! x) + wInIdx K M p (inner_idx K M p ! y))"
proof -
  define ix where "ix = inner_idx K M p ! x"
  define iy where "iy = inner_idx K M p ! y"
  have ixs: "ix \<in> set (inner_idx K M p)" and iys: "iy \<in> set (inner_idx K M p)"
    by (simp_all add: ix_def iy_def x y)
  obtain p7: "7 \<le> p" and oddp: "odd p" and NpM: "Nof K div p < M"
    using hyp_facts[OF p H] by blast
  have K1: "2 * K < p ^ 2" and K2: "K + p < p ^ 2"
  proof -
    have b: "200 * M < p \<and> 5 * K < p ^ 2" by (rule innerHyp_bounds[OF H])
    have KM: "K < p * M" using H by (simp add: InnerHyp_def)
    have "p * (M + 1) \<le> p * p" using b by (intro mult_le_mono2) linarith
    moreover have "p * (M + 1) = p * M + p" by simp
    ultimately have "K + p < p * p" using KM by linarith
    thus "K + p < p ^ 2" by (simp add: power2_eq_square)
    show "2 * K < p ^ 2" using b by linarith
  qed
  have entry: "innerGram K M p $$ (x, y) = muX {1..K} (\<Prod> j \<in>
    Jset K p. (pX + [:of_nat j ^ 2:]) ^ kexp K M p ix iy j)"
    using x y numerator_eq[of ix p iy K M] mem_inner_idx[of ix K M p] mem_inner_idx[of iy K M p] ixs
      iys
    by (simp add: innerGram_def Let_def ix_def iy_def mult.assoc)
  define B where "B = wInIdx K M p ix + wInIdx K M p iy"
  have hB: "\<And>c. c < p \<Longrightarrow>
    B + 4 \<le> of_nat (eNum p c (Jset K p) (kexp K M p ix iy)) - of_nat (nearCount p K c)"
  proof -
    fix c assume c: "c < p"
    have nc: "nearCount p K c = mult c * ell p K (cls p c)"
      by (simp only: nearCount_eq[OF p] sum_omg[OF oddp c])
    show "B + 4 \<le> of_nat (eNum p c (Jset K p) (kexp K M p ix iy)) - of_nat (nearCount p K c)"
    proof (cases "c = 0")
      case True
      have hx: "wInIdx K M p ix \<le> 2 * of_nat (nu K M p ix 0) + 6 * of_nat (Nof K div p) -
        of_nat (K div p) + 1 / 2"
        and hy: "wInIdx K M p iy \<le> 2 * of_nat (nu K M p iy 0) + 6 * of_nat (Nof K div p) -
          of_nat (K div p) + 1 / 2"
        by (rule half_zero[OF p H ixs]) (rule half_zero[OF p H iys])
      have e: "of_nat (eNum p c (Jset K p) (kexp K M p ix iy)) - of_nat (nearCount p K c) =
          (5 + 2 * (6 * of_nat (Nof K div p) + of_nat (nu K M p ix 0) + of_nat (nu K M p iy 0)) -
            2 * of_nat (K div p) :: rat)"
        unfolding eNum_eq[OF oddp c] nc using True
          by (simp add: cls_zero mult_def ell_zero_eq[OF prime_gt_0_nat[OF p]])
      show ?thesis unfolding B_def e using hx hy
        by (simp only: distrib_left right_diff_distrib add_divide_distrib diff_divide_distrib;
        linarith)
    next
      case False
      have cls_ge1: "1 \<le> cls p c" using cls_pos[OF False c] .
      have cls_le_half: "cls p c \<le> mHalf p" using cls_le[OF oddp] .
      have hx: "wInIdx K M p ix \<le> of_nat (nu K M p ix (cls p c)) + 3 *
        of_nat (ell p (Nof K) (cls p c)) - (of_nat (ell p K (cls p c)) + 4) / 2"
        and hy: "wInIdx K M p iy \<le> of_nat (nu K M p iy (cls p c)) + 3 *
          of_nat (ell p (Nof K) (cls p c)) - (of_nat (ell p K (cls p c)) + 4) / 2"
        by (rule half_ord[OF p H ixs cls_ge1 cls_le_half]) (rule half_ord[OF p H iys cls_ge1
          cls_le_half])
      have e: "of_nat (eNum p c (Jset K p) (kexp K M p ix iy)) - of_nat (nearCount p K c) =
          (6 * of_nat (ell p (Nof K) (cls p c)) + of_nat (nu K M p ix (cls p c)) +
            of_nat (nu K M p iy (cls p c))
            - of_nat (ell p K (cls p c)) :: rat)"
        unfolding eNum_eq[OF oddp c] nc using False by (simp add: mult_def)
      show ?thesis unfolding B_def e using hx hy
        by (simp only: distrib_left right_diff_distrib add_divide_distrib diff_divide_distrib;
        linarith)
    qed
  qed
  have hdeg: "\<And>c. c < p \<Longrightarrow> eNum p c (Jset K p) (kexp K M p ix iy) \<le> p + 1"
  proof -
    fix c assume c: "c < p"
    have b: "200 * M < p" using innerHyp_bounds[OF H] by blast
    have M40: "40 \<le> M" using H by (simp add: InnerHyp_def)
    have nx: "nu K M p ix (cls p c) \<le> 4 * M + 10" by (rule nu_le[OF p H ixs])
    have ny: "nu K M p iy (cls p c) \<le> 4 * M + 10" by (rule nu_le[OF p H iys])
    have el: "ell p (Nof K) (cls p c) \<le> M"
    proof (cases "c = 0")
      case True
      thus ?thesis using NpM by (simp add: cls_zero ell_zero_eq[OF prime_gt_0_nat[OF p]])
    next
      case False
      show ?thesis by (rule ellN_le[OF p H cls_pos[OF False c] cls_le[OF oddp]])
    qed
    show "eNum p c (Jset K p) (kexp K M p ix iy) \<le> p + 1"
    proof (cases "c = 0")
      case True
      have "eNum p c (Jset K p) (kexp K M p ix iy) =
          5 + 2 * (6 * ell p (Nof K) (cls p c) + nu K M p ix (cls p c) + nu K M p iy (cls p c))"
        unfolding eNum_eq[OF oddp c] using True by (simp add: mult_def)
      thus ?thesis using nx ny el b M40 by fastforce
    next
      case False
      have "eNum p c (Jset K p) (kexp K M p ix iy) =
          6 * ell p (Nof K) (cls p c) + nu K M p ix (cls p c) + nu K M p iy (cls p c)"
        unfolding eNum_eq[OF oddp c] using False by (simp add: mult_def)
      thus ?thesis using nx ny el b M40 by arith
    qed
  qed
  show ?thesis
    unfolding entry ix_def[symmetric] iy_def[symmetric] B_def[symmetric]
    by (rule entry_generic[OF p p7 K1 K2 _ hB hdeg]) (simp add: Jset_def)
qed

text \<open>Multiplying by a @{text p}-adic unit does not change Gauss-valuation bounds.\<close>
lemma vpGge_of_unit_mul:
  assumes "prime p" "u \<noteq> 0" "vp p u = 0" "vpGge p ([:u:] * P) b"
  shows "vpGge p P b"
proof -
  have "prime (int p)" using assms(1) by (simp add: prime_nat_int_transfer)
  hence pr: "prime_elem (int p)" by (rule prime_imp_prime_elem)
  show ?thesis unfolding vpGge_def
  proof (intro allI impI)
    fix i assume c: "Polynomial.coeff P i \<noteq> 0"
    have ne: "u * Polynomial.coeff P i \<noteq> 0" using assms(2) c by simp
    have co: "Polynomial.coeff ([:u:] * P) i = u * Polynomial.coeff P i" by simp
    have l: "b \<le> of_int (vp p (u * Polynomial.coeff P i))" using assms(4) ne
      unfolding vpGge_def co[symmetric] by blast
    have e: "vp p (u * Polynomial.coeff P i) = vp p (Polynomial.coeff P i)"
      using qmultiplicity_mult[OF pr assms(2) c] assms(3) by (simp add: vp_def)
    show "b \<le> of_int (vp p (Polynomial.coeff P i))" using l unfolding e .
  qed
qed

text \<open>@{text "\<Sum>_i (w (\<sigma> i) + w i) = 2 \<Sum>_i w i"}
  for a permutation @{text \<sigma>} of @{text "{0..<n}"}.\<close>
lemma sum_permute_add:
  assumes "\<sigma> permutes {0..<n}"
  shows "(\<Sum> i = 0..<n. w (\<sigma> i) + w i) = 2 * (\<Sum> i = 0..<n. (w i :: rat))"
proof -
  have "(\<Sum> i = 0..<n. w (\<sigma> i)) = (\<Sum> i = 0..<n. w i)"
    using sum.permute[OF assms, of w] unfolding o_def by (rule sym)
  thus ?thesis unfolding sum.distrib mult_2 by simp
qed

text \<open>The Gram matrix of a basis @{text B} (rows =
  coefficient vectors) is @{text "B G B^T"}, and its
  determinant is @{text "det(B)^2 det(G)"};
    a Gauss bound on the Gram determinant transfers to @{text "det G"}
  when @{text "det B"} is a @{text p}-adic unit.\<close>
lemma det_gram_transfer:
  assumes p: "prime p" and G: "G \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
    and dB: "Determinant.det B \<noteq> 0" "vp p (Determinant.det B) = 0"
    and gram: "vpGge p (Determinant.det (map_mat (\<lambda>q. [:q:]) B * G *
      transpose_mat (map_mat (\<lambda>q. [:q:]) B))) b"
  shows "vpGge p (Determinant.det G) b"
proof -
  have "Determinant.det (map_mat (\<lambda>q. [:q:]) B * G *
    transpose_mat (map_mat (\<lambda>q. [:q:]) B)) =
        [:Determinant.det B ^ 2:] * Determinant.det G"
  proof -
    have Bp: "map_mat (\<lambda>q. [:q:]) B \<in> carrier_mat n n" using B by simp
    have Tc: "transpose_mat (map_mat (\<lambda>q. [:q:]) B) \<in> carrier_mat n n" using Bp by simp
    have BG: "map_mat (\<lambda>q. [:q:]) B * G \<in> carrier_mat n n" using Bp G
      by (rule mult_carrier_mat)
    show ?thesis unfolding det_mult[OF BG Tc] det_mult[OF Bp G] det_transpose[OF Bp]
      det_map_mat_C[OF B]
      by (simp add: power2_eq_square mult_ac)
  qed
  thus ?thesis using gram vpGge_of_unit_mul[OF p, of "Determinant.det B ^ 2"] dB
    by (metis power_not_zero dB(1) dB(2) vp_power_rat[OF p dB(1), of 2] mult_zero_right)
qed

text \<open>@{text "\<gamma>_p^in = 2 \<Sum>_{x \<in> idx} w_x"},
  the double sum written over the index list.\<close>
lemma sum_list_concat_aux: "sum_list (concat xss) =
  sum_list (map sum_list (xss :: 'a :: monoid_add list list))"
  by (induction xss) simp_all

lemma gammaIn_eq_sum_idx:
  "gammaIn K M p = 2 * (\<Sum> x < length (inner_idx K M p). wInIdx K M p (inner_idx K M p ! x))"
proof -
  have "sum_list (map (wInIdx K M p) (inner_idx K M p)) =
      (\<Sum> x < length (inner_idx K M p). wInIdx K M p (inner_idx K M p ! x))"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  moreover have "sum_list (map (wInIdx K M p) (inner_idx K M p)) = (\<Sum> a \<le>
    mHalf p. \<Sum> i < nat (Lin K M p a). wIn K M p a i)"
    unfolding inner_idx_def map_concat sum_list_concat_aux map_map
    by (simp add: o_def wInIdx_def interv_sum_list_conv_sum_set_nat atLeast0LessThan
      lessThan_Suc_atMost del: upt_Suc)
  ultimately show ?thesis unfolding gammaIn_def by simp
qed

lemma degree_innerBasis_lt:
  assumes "prime p" "InnerHyp K M p" "x \<in> set (inner_idx K M p)"
  shows "degree (innerBasis K M p x) < hof K"
proof -
  obtain a i where x: "x = (a, i)" by (cases x)
  have a: "a \<le> mHalf p" and i: "i < nat (Lin K M p a)" using assms(3) unfolding x
    by (simp_all add: mem_inner_idx)
  have tot: "(\<Sum> c \<le> mHalf p. nat (Lin K M p c)) = hof K"
  proof -
    have "int (\<Sum> c \<le> mHalf p. nat (Lin K M p c)) = (\<Sum> c \<le> mHalf p. Lin K M p c)"
      unfolding of_nat_sum by (rule sum.cong) (use Lin_nonneg[OF assms(1,2)] in auto)
    also have "\<dots> = int (hof K)" by (rule sum_Lin[OF assms(1,2)])
    finally show ?thesis by (simp only: of_nat_eq_iff)
  qed
  have rem: "(\<Sum> c \<le> mHalf p. nat (Lin K M p c)) = nat (Lin K M p a) + (\<Sum> c \<in>
    {0..mHalf p} - {a}. nat (Lin K M p c))"
  proof -
    have e: "{..mHalf p} = {0..mHalf p}" by auto
    show ?thesis unfolding e using a by (simp add: sum.remove)
  qed
  have d1: "degree (\<Prod> c \<in> {0..mHalf p} - {a}. (pX +
    [:of_nat c ^ 2:]) ^ nat (Lin K M p c)) \<le>
      (\<Sum> c \<in> {0..mHalf p} - {a}. nat (Lin K M p c))"
  proof -
    have "degree (\<Prod> c \<in> {0..mHalf p} - {a}. (pX +
      [:of_nat c ^ 2:]) ^ nat (Lin K M p c)) \<le>
        (\<Sum> c \<in> {0..mHalf p} - {a}. degree ((pX + [:of_nat c ^ 2:]) ^ nat (Lin K M p c)))"
      using degree_prod_sum_le[of "{0..mHalf p} - {a}" "\<lambda>c. (pX +
        [:of_nat c ^ 2:]) ^ nat (Lin K M p c)"]
      by (simp add: o_def)
    also have "\<dots> \<le> (\<Sum> c \<in> {0..mHalf p} - {a}. nat (Lin K M p c))"
    proof (rule sum_mono)
      fix c
      show "degree ((pX + [:of_nat c ^ 2:]) ^ nat (Lin K M p c)) \<le> nat (Lin K M p c)"
        using degree_power_le[of "pX + [:of_nat c ^ 2:]" "nat (Lin K M p c)"]
          unfolding degree_pX_plus_const by simp
    qed
    finally show ?thesis .
  qed
  have d2: "degree ((pX + [:of_nat a ^ 2:]) ^ i) \<le> i"
    using degree_power_le[of "pX + [:of_nat a ^ 2:]" i] unfolding degree_pX_plus_const by simp
  have "degree (innerBasis K M p x) \<le> (\<Sum> c \<in>
    {0..mHalf p} - {a}. nat (Lin K M p c)) + i"
    unfolding innerBasis_def x fst_conv snd_conv using degree_mult_le d1 d2
      by (meson add_le_mono order_trans)
  thus ?thesis using tot rem i by linarith
qed

text \<open>The inner Gram matrix is @{text "B G_K B^T"}
  for the coefficient matrix @{text B} of the inner basis.\<close>
lemma innerGram_eq_conj:
  assumes p: "prime p" and H: "InnerHyp K M p"
  defines "B \<equiv> Matrix.mat (hof K) (hof K) (\<lambda>(x,
    d). Polynomial.coeff (innerBasis K M p (inner_idx K M p ! x)) d)"
  shows "innerGram K M p = map_mat (\<lambda>q. [:q:]) B * GK K *
    transpose_mat (map_mat (\<lambda>q. [:q:]) B)"
proof -
  let ?h = "hof K" and ?idx = "inner_idx K M p"
  let ?Q = "map_mat (\<lambda>q. [:q:]) B"
  have len: "length ?idx = ?h" by (rule length_inner_idx[OF p H])
  have dB: "dim_row B = ?h" "dim_col B = ?h" by (simp_all add: B_def)
  have dG: "dim_row (GK K) = ?h" "dim_col (GK K) = ?h" by (simp_all add: GK_def)
  have sm: "muX S (Polynomial.smult a P) = Polynomial.smult a (muX S P)" for S a P
    using muX_C_mul[of S a P] by simp
  have qe: "innerBasis K M p (?idx ! x) = (\<Sum> k < ?h. Polynomial.smult (B $$ (x, k)) (pX ^ k))"
    if x: "x < ?h" for x
  proof -
    have dg: "degree (innerBasis K M p (?idx ! x)) \<le> ?h - 1"
      using degree_innerBasis_lt[OF p H, of "?idx ! x"] x len by simp
    have e: "{..?h - 1} = {..<?h}" using x by auto
    have "innerBasis K M p (?idx ! x) =
        (\<Sum> k \<le> ?h - 1. Polynomial.monom (Polynomial.coeff (innerBasis K M p (?idx ! x)) k)
          k)"
      by (rule sym[OF poly_as_sum_of_monoms'[OF dg]])
    also have "\<dots> = (\<Sum> k < ?h. Polynomial.monom (Polynomial.coeff (innerBasis K M p (?idx
      ! x)) k) k)"
      unfolding e ..
    also have "\<dots> = (\<Sum> k < ?h. Polynomial.smult (B $$ (x, k)) (pX ^ k))"
      by (rule sum.cong[OF refl]) (use x in \<open>unfold pX_pow_monom smult_monom,
        simp add: B_def\<close>)
    finally show ?thesis .
  qed
  have pq: "Dm (Nof K) ^ 6 * innerBasis K M p (?idx ! x) * innerBasis K M p (?idx ! y) =
      (\<Sum> k < ?h. \<Sum> l < ?h. Polynomial.smult (B $$ (x, k) * B $$ (y,
        l)) (Dm (Nof K) ^ 6 * pX ^ (k + l)))"
    if x: "x < ?h" and y: "y < ?h" for x y
  proof -
    have pq0: "innerBasis K M p (?idx ! x) * innerBasis K M p (?idx ! y) = (\<Sum> k <
      ?h. \<Sum> l < ?h.
        Polynomial.smult (B $$ (x, k)) (pX ^ k) * Polynomial.smult (B $$ (y, l)) (pX ^ l))"
      unfolding qe[OF x] qe[OF y] by (rule sum_product)
    have "Dm (Nof K) ^ 6 * innerBasis K M p (?idx ! x) * innerBasis K M p (?idx ! y) =
        Dm (Nof K) ^ 6 * (innerBasis K M p (?idx ! x) * innerBasis K M p (?idx ! y))"
          by (simp only: mult.assoc)
    also have "\<dots> = (\<Sum> k < ?h. \<Sum> l <
      ?h. Polynomial.smult (B $$ (x, k) * B $$ (y, l)) (Dm (Nof K) ^ 6 * pX ^ (k + l)))"
      unfolding pq0 sum_distrib_left by (intro sum.cong refl) (simp add: power_add mult_ac)
    finally show ?thesis .
  qed
  have entry: "innerGram K M p $$ (x, y) = (?Q * GK K * transpose_mat ?Q) $$ (x, y)"
    if x: "x < ?h" and y: "y < ?h" for x y
  proof -
    have "innerGram K M p $$ (x, y) =
        muX {1..K} (Dm (Nof K) ^ 6 * innerBasis K M p (?idx ! x) * innerBasis K M p (?idx ! y))"
      using x y len by (simp add: innerGram_def Let_def)
    also have "\<dots> = (\<Sum> k < ?h. \<Sum> l <
      ?h. [:B $$ (x, k):] * GK K $$ (k, l) * [:B $$ (y, l):])"
      unfolding pq[OF x y] muX_sum sm by (intro sum.cong refl) (simp add: GK_def mult_ac)
    also have "\<dots> = (?Q * GK K * transpose_mat ?Q) $$ (x, y)"
    proof -
      have m: "(?Q * GK K * transpose_mat ?Q) $$ (x, y) =
          (\<Sum> l < ?h. (\<Sum> k < ?h. [:B $$ (x, k):] * GK K $$ (k, l)) * [:B $$ (y, l):])"
        using x y by (simp add: scalar_prod_def dB dG atLeast0LessThan)
      show ?thesis unfolding m sum_distrib_right by (rule sum.swap)
    qed
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule eq_matI)
    fix x y
    assume x: "x < dim_row (?Q * GK K * transpose_mat ?Q)" and y: "y <
      dim_col (?Q * GK K * transpose_mat ?Q)"
    have xh: "x < ?h" and yh: "y < ?h" using x y by (simp_all add: dB)
    show "innerGram K M p $$ (x, y) = (?Q * GK K * transpose_mat ?Q) $$ (x, y)"
      by (rule entry[OF xh yh])
  qed (simp_all add: innerGram_def Let_def len dB dG)
qed

text \<open>(4.5): the inner basis is @{text "\<int>_p"}-unimodular: the coefficient matrix of the
  basis
  polynomials has a determinant that is a @{text p}-adic unit.  Proof by the Taylor-matrix criterion
  (@{text "unimodular_criterion"}): expanding row @{text "E_{a,j}"} at the point @{text "-c^2"} to
    order @{text i}
  gives an upper triangular matrix with the units @{text "\<Prod>_{c \<noteq> a} (c^2 - a^2)^{L_c}"}
    on the diagonal.\<close>
theorem innerBasis_unimodular:
  assumes p: "prime p" and H: "InnerHyp K M p"
  defines "B \<equiv> Matrix.mat (hof K) (hof K) (\<lambda>(x,
    d). Polynomial.coeff (innerBasis K M p (inner_idx K M p ! x)) d)"
  shows "Determinant.det B \<noteq> 0 \<and> vp p (Determinant.det B) = 0"
proof -
  define h where "h = hof K"
  define idx where "idx = inner_idx K M p"
  define rt where "rt = (\<lambda>y. - (of_nat (fst (idx ! y)) ^ 2) :: rat)"
  define od where "od = (\<lambda>y. snd (idx ! y))"
  define V where "V = Matrix.mat h h (\<lambda>(d, y). tay (pX ^ d) (rt y) (od y))"
  define T where "T = B * V"
  have len: "length idx = h" by (simp add: idx_def h_def length_inner_idx[OF p H])
  have Bc: "B \<in> carrier_mat h h" and Vc: "V \<in> carrier_mat h h"
    by (simp_all add: B_def V_def h_def)
  have mp: "2 * mHalf p + 1 = p" using hyp_facts[OF p H] by blast
  have mem: "\<And>x. x < h \<Longrightarrow> idx ! x \<in> set idx" by (simp add: len)
  have cls_le: "\<And>x. x < h \<Longrightarrow> fst (idx ! x) \<le> mHalf p"
    using mem_inner_idx mem by (auto simp: idx_def)
  have Tentry: "\<And>x y. x < h \<Longrightarrow> y < h \<Longrightarrow>
    T $$ (x, y) = tay (innerBasis K M p (idx ! x)) (rt y) (od y)"
  proof -
    fix x y assume x: "x < h" and y: "y < h"
    have dg: "degree (innerBasis K M p (idx ! x)) < h"
      using degree_innerBasis_lt[OF p H, of "idx ! x"] mem[OF x] by (simp add: idx_def h_def)
    have "dim_row B = h" "dim_col B = h" "dim_row V = h" "dim_col V = h" using Bc Vc by auto
    with x y have "T $$ (x, y) = (\<Sum> d \<in> {0..<h}. B $$ (x, d) * V $$ (d, y))"
      by (simp add: T_def scalar_prod_def)
    also have "\<dots> = (\<Sum> d < h. Polynomial.coeff (innerBasis K M p (idx ! x)) d *
      tay (pX ^ d) (rt y) (od y))"
      by (rule sum.cong) (use x y in \<open>auto simp: B_def V_def idx_def h_def\<close>)
    also have "\<dots> = tay (innerBasis K M p (idx ! x)) (rt y) (od y)"
      by (rule tay_eq_sum[OF dg, symmetric])
    finally show "T $$ (x, y) = tay (innerBasis K M p (idx ! x)) (rt y) (od y)" .
  qed
  have below: "\<And>x y. y < x \<Longrightarrow> x < h \<Longrightarrow> T $$ (x, y) = 0"
  proof -
    fix x y assume yx: "y < x" and x: "x < h"
    have y: "y < h" using yx x by simp
    obtain a j where ax: "idx ! x = (a, j)" by (cases "idx ! x")
    obtain c i where cy: "idx ! y = (c, i)" by (cases "idx ! y")
    have my: "c \<le> mHalf p" "i < nat (Lin K M p c)" using mem[OF y] cy
      by (simp_all add: idx_def mem_inner_idx)
    have mx: "a \<le> mHalf p" using mem[OF x] ax by (simp add: idx_def mem_inner_idx)
    have lex: "c < a \<or> (c = a \<and> i < j)"
      using inner_idx_lex[of y x K M p] yx x len ax cy by (simp add: idx_def)
    have rr: "pX + [:of_nat c ^ 2:] = pX - [:rt y:]" unfolding rt_def cy by simp
    have T: "T $$ (x, y) = tay (innerBasis K M p (a, j)) (rt y) i"
      using Tentry[OF x y] unfolding ax by (simp add: od_def cy)
    show "T $$ (x, y) = 0"
    proof (cases "c < a")
      case True
      have cin: "c \<in> {0..mHalf p} - {a}" using True mx by simp
      have E: "innerBasis K M p (a, j) = (pX - [:rt y:]) ^ nat (Lin K M p c) *
          ((\<Prod> c' \<in> {0..mHalf p} - {a} - {c}. (pX +
            [:of_nat c' ^ 2:]) ^ nat (Lin K M p c')) * (pX + [:of_nat a ^ 2:]) ^ j)"
        unfolding innerBasis_def fst_conv snd_conv prod.remove[OF finite_Diff[OF
          finite_atLeastAtMost] cin] rr
        by (simp only: mult.assoc)
      show ?thesis unfolding T E by (rule tay_pow_mult_lt[OF my(2)])
    next
      case False
      hence ca: "c = a" and ij: "i < j" using lex by auto
      have E: "innerBasis K M p (a, j) = (pX - [:rt y:]) ^ j *
          (\<Prod> c' \<in> {0..mHalf p} - {a}. (pX + [:of_nat c' ^ 2:]) ^ nat (Lin K M p c'))"
        unfolding innerBasis_def fst_conv snd_conv rr[unfolded ca] by (rule mult.commute)
      show ?thesis unfolding T E by (rule tay_pow_mult_lt[OF ij])
    qed
  qed
  have diag: "\<And>x. x < h \<Longrightarrow> T $$ (x, x) =
      (\<Prod> c \<in> {0..mHalf p} - {fst (idx ! x)}. (of_nat c ^ 2 -
        of_nat (fst (idx ! x)) ^ 2) ^ nat (Lin K M p c))"
  proof -
    fix x assume x: "x < h"
    obtain a j where ax: "idx ! x = (a, j)" by (cases "idx ! x")
    have rr: "pX + [:of_nat a ^ 2:] = pX - [:rt x:]" unfolding rt_def ax by simp
    have E: "innerBasis K M p (a, j) = (pX - [:rt x:]) ^ j *
        (\<Prod> c \<in> {0..mHalf p} - {a}. (pX + [:of_nat c ^ 2:]) ^ nat (Lin K M p c))"
      unfolding innerBasis_def fst_conv snd_conv rr by (rule mult.commute)
    have "T $$ (x, x) = tay (innerBasis K M p (a, j)) (rt x) j"
      using Tentry[OF x x] unfolding ax by (simp add: od_def ax)
    also have "\<dots> = tay (\<Prod> c \<in>
      {0..mHalf p} - {a}. (pX + [:of_nat c ^ 2:]) ^ nat (Lin K M p c)) (rt x) 0"
      unfolding E using tay_pow_mult[of "rt x" j "\<Prod> c \<in>
        {0..mHalf p} - {a}. (pX + [:of_nat c ^ 2:]) ^ nat (Lin K M p c)" 0]
      by simp
    also have "\<dots> = poly (\<Prod> c \<in>
      {0..mHalf p} - {a}. (pX + [:of_nat c ^ 2:]) ^ nat (Lin K M p c)) (rt x)"
      by (rule tay_0_eq_poly)
    also have "\<dots> = (\<Prod> c \<in>
      {0..mHalf p} - {fst (idx ! x)}. (of_nat c ^ 2 -
      of_nat (fst (idx ! x)) ^ 2) ^ nat (Lin K M p c))"
      unfolding ax rt_def by (simp add: poly_prod poly_monom)
    finally show "T $$ (x, x) =
        (\<Prod> c \<in> {0..mHalf p} - {fst (idx ! x)}. (of_nat c ^ 2 -
          of_nat (fst (idx ! x)) ^ 2) ^ nat (Lin K M p c))" .
  qed
  have unit: "\<And>x. x < h \<Longrightarrow> T $$ (x, x) \<noteq> 0 \<and> vp p (T $$ (x, x)) = 0"
  proof -
    fix x assume x: "x < h"
    define a where "a = fst (idx ! x)"
    have am: "a \<le> mHalf p" using cls_le[OF x] by (simp add: a_def)
    have pr: "prime (int p)" using p by (simp add: prime_nat_int_transfer)
    have fac: "(of_nat c ^ 2 - of_nat a ^ 2 :: rat) \<noteq> 0 \<and>
      vp p (of_nat c ^ 2 - of_nat a ^ 2) = 0"
      if c: "c \<in> {0..mHalf p} - {a}" for c
    proof -
      have cm: "c \<le> mHalf p" "c \<noteq> a" using c by auto
      define z :: int where "z = (int c - int a) * (int c + int a)"
      have zq: "(of_nat c ^ 2 - of_nat a ^ 2 :: rat) = of_int z"
        by (simp add: z_def power2_eq_square algebra_simps)
      have "\<not> int p dvd (int c - int a)"
      proof
        assume d: "int p dvd (int c - int a)"
        have "int c - int a \<noteq> 0" using cm by simp
        from dvd_imp_le_int[OF this d] have "int p \<le> \<bar>int c - int a\<bar>" by simp
        thus False using cm am mp by arith
      qed
      moreover have "\<not> int p dvd (int c + int a)"
      proof
        assume d: "int p dvd (int c + int a)"
        have "int c + int a \<noteq> 0" using cm by simp
        from dvd_imp_le_int[OF this d] have "int p \<le> \<bar>int c + int a\<bar>" by simp
        thus False using cm am mp by arith
      qed
      ultimately have nz: "\<not> int p dvd z" unfolding z_def using prime_dvd_mult_iff[OF pr]
        by blast
      hence "z \<noteq> 0" by auto
      thus ?thesis unfolding zq using nz
        by (simp add: vp_def qmultiplicity_of_int not_dvd_imp_multiplicity_0)
    qed
    have d: "T $$ (x, x) = (\<Prod> c \<in>
      {0..mHalf p} - {a}. (of_nat c ^ 2 - of_nat a ^ 2) ^ nat (Lin K M p c))"
      using diag[OF x] by (simp add: a_def)
    have ne: "(\<Prod> c \<in> {0..mHalf p} - {a}. (of_nat c ^ 2 -
      of_nat a ^ 2 :: rat) ^ nat (Lin K M p c)) \<noteq> 0"
      using fac by (simp add: prod_zero_iff)
    have "vp p (\<Prod> c \<in> {0..mHalf p} - {a}. (of_nat c ^ 2 -
      of_nat a ^ 2 :: rat) ^ nat (Lin K M p c)) =
        (\<Sum> c \<in> {0..mHalf p} - {a}. vp p ((of_nat c ^ 2 -
          of_nat a ^ 2) ^ nat (Lin K M p c)))"
      by (rule vp_prod_rat[OF p]) (use fac in auto)
    also have "\<dots> = 0" using fac by (simp add: vp_power_rat[OF p])
    finally show "T $$ (x, x) \<noteq> 0 \<and> vp p (T $$ (x, x)) = 0" unfolding d using ne by simp
  qed
  have Bi: "\<And>x d. x < h \<Longrightarrow> d < h \<Longrightarrow> vge p (B $$ (x, d)) 0"
    using vpGge_innerBasis[OF p] by (auto simp: B_def h_def vpGge_iff)
  have Vi: "\<And>d y. d < h \<Longrightarrow> y < h \<Longrightarrow> vge p (V $$ (d, y)) 0"
  proof -
    fix d y assume d: "d < h" and y: "y < h"
    have P: "vpGge p (pX ^ d) 0" using vpGge_pow[OF p vpGge_pX, of d] by simp
    have "vge p (of_nat (fst (idx ! y)) ^ 2) 0"
      using vge_pow[OF p vge_of_int[OF p, of "int (fst (idx ! y))"]] by simp
    hence r: "vge p (rt y) 0" unfolding rt_def by (rule vge_neg)
    show "vge p (V $$ (d, y)) 0" using vge_tay[OF p P r, of "od y"] d y by (simp add: V_def)
  qed
  show ?thesis
    unfolding h_def[symmetric]
    by (rule unimodular_criterion[OF p Bc Vc Bi Vi])
       (use below unit in \<open>simp_all add: T_def[symmetric] vge_zero\<close>)
qed

text \<open>Proposition 4.1 from the entry bounds (unimodular change of basis +
  @{text "vpGge_det_of_terms"}).\<close>
theorem DeltaK_vpGge_inner_of_entries:
  assumes p: "prime p" and H: "InnerHyp K M p"
    and ent: "\<And>x y. x < length (inner_idx K M p) \<Longrightarrow>
      y < length (inner_idx K M p) \<Longrightarrow>
           vpGge p (innerGram K M p $$ (x, y))
             (wInIdx K M p (inner_idx K M p ! x) + wInIdx K M p (inner_idx K M p ! y))"
  shows "vpGge p (DeltaK K) (gammaIn K M p)"
proof -
  define h where "h = hof K"
  define B where "B = Matrix.mat (hof K) (hof K) (\<lambda>(x,
    d). Polynomial.coeff (innerBasis K M p (inner_idx K M p ! x)) d)"
  define w where "w = (\<lambda>x. wInIdx K M p (inner_idx K M p ! x))"
  have len: "length (inner_idx K M p) = h" by (simp add: h_def length_inner_idx[OF p H])
  have Bc: "B \<in> carrier_mat h h" and Gc: "GK K \<in>
    carrier_mat h h" and IGc: "innerGram K M p \<in> carrier_mat h h"
    by (simp_all add: B_def GK_def innerGram_def h_def len Let_def)
  have uni: "Determinant.det B \<noteq> 0 \<and> vp p (Determinant.det B) = 0"
    unfolding B_def by (rule innerBasis_unimodular[OF p H])
  have gramv: "vpGge p (Determinant.det (innerGram K M p)) (2 * (\<Sum> i = 0..<h. w i))"
  proof (rule vpGge_det_of_terms[OF p IGc])
    fix \<sigma> assume \<sigma>: "\<sigma> permutes {0..<h}"
    have "vpGge p (\<Prod> i = 0..<h. innerGram K M p $$ (i, \<sigma> i)) (\<Sum> i =
      0..<h. w i + w (\<sigma> i))"
    proof (rule vpGge_prod[OF p])
      show "finite {0..<h}" by simp
    next
      fix i assume i: "i \<in> {0..<h}"
      have si: "\<sigma> i < h" using permutes_in_image[OF \<sigma>] i by simp
      show "vpGge p (innerGram K M p $$ (i, \<sigma> i)) (w i + w (\<sigma> i))"
        unfolding w_def by (rule ent) (use i si len in auto)
    qed
    thus "vpGge p (\<Prod> i = 0..<h. innerGram K M p $$ (i, \<sigma> i)) (2 * (\<Sum> i =
      0..<h. w i))"
      using sum_permute_add[OF \<sigma>, of w] by (simp add: add.commute)
  qed
  have "vpGge p (DeltaK K) (2 * (\<Sum> i = 0..<h. w i))"
    unfolding DeltaK_def
    by (rule det_gram_transfer[OF p Gc Bc conjunct1[OF uni] conjunct2[OF uni]])
       (use gramv innerGram_eq_conj[OF p H] in \<open>simp add: B_def\<close>)
  thus ?thesis
    using gammaIn_eq_sum_idx[of K M p] by (simp add: w_def len atLeast0LessThan)
qed

text \<open>Proposition 4.1: under (4.1), @{text "v_p^G(\<Delta>_K) \<ge> \<gamma>_p^in"}.\<close>
theorem DeltaK_vpGge_inner: "prime p \<Longrightarrow> InnerHyp K M p \<Longrightarrow>
  vpGge p (DeltaK K) (gammaIn K M p)"
  by (rule DeltaK_vpGge_inner_of_entries, assumption+, rule innerGram_entry_bound)

end





