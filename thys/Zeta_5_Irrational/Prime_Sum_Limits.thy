(*  Title:   Prime_Sum_Limits.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Prime_Sum_Limits
  imports Rational_Padic_Valuations "Prime_Number_Theorem.Prime_Number_Theorem"
    "HOL-Real_Asymp.Real_Asymp"
begin

section \<open>Riemann-sum limits of sums over primes from the prime number theorem\<close>

text \<open>From the prime number theorem in the form \<open>\<theta>(x) \<sim> x\<close> (the AFP's
  @{text \<theta>_asymptotics}):
  for a bounded function \<open>\<phi>\<close> on \<open>[a,
    b]\<close> that is continuous off a countable set,
  \<open>\<Sum>\<^sub>a\<^sub>K\<^sub><\<^sub>p\<^sub>\<le>\<^sub>b\<^sub>K \<phi>(p/K) ln p \<le>
    (\<integral>\<^sub>a\<^sup>b \<phi> + \<epsilon>) K\<close>
    for all large \<open>K\<close>, and the version in the variable
  \<open>x = K/p\<close>.  The proof uses Chebyshev's \<open>\<theta>\<close> over the cells of a
    uniform partition, step majorants
  of \<open>\<phi>\<close> and dominated convergence as the mesh goes to zero.  Also the bookkeeping
  \<open>\<psi> - \<theta>\<close> for the valuations of small primes.\<close>

text \<open>The prime number theorem in the form used (from
  @{text "Prime_Number_Theorem.\<theta>_asymptotics"}).\<close>
lemma pnt_theta: "((\<lambda>x. primes_theta x / x) \<longlongrightarrow> 1) at_top"
  using \<theta>_asymptotics
  by (rule asymp_equivD_strong[OF _ eventually_mono[OF eventually_gt_at_top[of 0]]]) auto


subsection \<open>Chebyshev's @{text \<theta>} over cells\<close>

text \<open>@{text "\<theta>(x) = \<Sum>_{p \<le> x} log p"} as a sum over a set of
  naturals.\<close>
lemma theta_eq_sum: "0 \<le> x \<Longrightarrow> primes_theta x = (\<Sum> p \<in> {p. prime p \<and>
  real p \<le> x}. ln (real p))"
  by (simp add: primes_theta_def prime_sum_upto_def)

lemma finite_primes_le: "finite {p. prime p \<and> real p \<le> x}"
proof (rule finite_subset[of _ "{..nat \<lfloor>x\<rfloor>}"])
  show "{p. prime p \<and> real p \<le> x} \<subseteq> {..nat \<lfloor>x\<rfloor>}"
    by (auto intro: le_nat_floor)
qed simp

text \<open>The sum of @{text "log p"} over the primes in @{text "(c, d]"} is
  @{text "\<theta>(d) - \<theta>(c)"}.\<close>
lemma sum_cell:
  assumes "0 \<le> c" "c \<le> d"
  shows "(\<Sum> p \<in> {p. prime p \<and> c < real p \<and>
    real p \<le> d}. ln (real p)) = primes_theta d - primes_theta c"
proof -
  have "{p. prime p \<and> real p \<le> d} = {p. prime p \<and>
    real p \<le> c} \<union> {p. prime p \<and> c < real p \<and> real p \<le> d}"
    using assms by auto
  moreover have "{p. prime p \<and> real p \<le> c} \<inter> {p. prime p \<and> c < real p \<and>
    real p \<le> d} = {}" by auto
  ultimately show ?thesis
    unfolding theta_eq_sum[OF assms(1)] theta_eq_sum[OF order_trans[OF assms]]
    using sum.union_disjoint[of "{p. prime p \<and> real p \<le> c}" "{p. prime p \<and>
      c < real p \<and> real p \<le> d}" "\<lambda>p. ln (real p)"]
      finite_primes_le[of c] finite_subset[OF _ finite_primes_le[of d], of "{p. prime p \<and>
        c < real p \<and> real p \<le> d}"]
    by fastforce
qed

lemma theta_ratio_eq: "0 < c \<Longrightarrow> 0 < K \<Longrightarrow>
  c * (primes_theta (c * real K) / (c * real K)) = primes_theta (c * real K) / real K"
  by (simp add: field_simps)

text \<open>@{text "\<theta>(cK)/K \<longrightarrow> c"} along @{text "K \<in> \<nat>"}.\<close>
lemma theta_tendsto:
  assumes "0 \<le> c"
  shows "((\<lambda>K :: nat. primes_theta (c * real K) / real K) \<longlongrightarrow> c) at_top"
proof (cases "c = 0")
  case True
  thus ?thesis by (simp add: primes_theta_def prime_sum_upto_def)
next
  case False
  hence c0: "0 < c" using assms by simp
  have lim: "((\<lambda>K :: nat. primes_theta (c * real K) / (c *
    real K)) \<longlongrightarrow> 1) at_top"
  proof -
    have cK: "filterlim (\<lambda>K :: nat. c * real K) at_top at_top"
      by (rule filterlim_tendsto_pos_mult_at_top[OF tendsto_const c0 filterlim_real_sequentially])
    show ?thesis using filterlim_compose[OF pnt_theta cK] by simp
  qed
  have "((\<lambda>K :: nat. c * (primes_theta (c * real K) / (c *
    real K))) \<longlongrightarrow> c * 1) at_top"
    by (rule tendsto_mult_left[OF lim])
  thus ?thesis
    using Lim_transform_eventually[OF _ eventually_mono[OF eventually_gt_at_top[of "0::nat"]
      theta_ratio_eq[OF c0]]] by auto
qed

lemma cell_tendsto:
  assumes "0 \<le> c" "0 \<le> d"
  shows "((\<lambda>K :: nat. (primes_theta (d * real K) - primes_theta (c * real K)) /
    real K) \<longlongrightarrow> d - c) at_top"
  using tendsto_diff[OF theta_tendsto[OF assms(2)] theta_tendsto[OF assms(1)]]
    by (simp add: diff_divide_distrib)

text \<open>Eventually @{text "\<theta>(dK) - \<theta>(cK) \<le> (d - c + \<delta>) K"} resp.
  @{text "\<ge> (d - c - \<delta>) K"}.\<close>
lemma cell_upper:
  assumes "0 \<le> c" "0 \<le> d" "0 < \<delta>"
  shows "\<forall>\<^sub>F K :: nat in at_top. primes_theta (d * real K) - primes_theta (c *
    real K) \<le> (d - c + \<delta>) * real K"
proof -
  have "\<forall>\<^sub>F K :: nat in at_top. (primes_theta (d * real K) - primes_theta (c *
    real K)) / real K < d - c + \<delta>"
    using order_tendstoD(2)[OF cell_tendsto[OF assms(1,2)], of "d - c + \<delta>"] assms(3) by simp
  moreover have "\<forall>\<^sub>F K :: nat in at_top. 0 < K" by (rule eventually_gt_at_top)
  ultimately show ?thesis
    by eventually_elim (simp add: divide_less_eq)
qed

lemma cell_lower:
  assumes "0 \<le> c" "0 \<le> d" "0 < \<delta>"
  shows "\<forall>\<^sub>F K :: nat in at_top. (d - c - \<delta>) * real K \<le>
    primes_theta (d * real K) - primes_theta (c * real K)"
proof -
  have "\<forall>\<^sub>F K :: nat in at_top. d - c - \<delta> <
    (primes_theta (d * real K) - primes_theta (c * real K)) / real K"
    using order_tendstoD(1)[OF cell_tendsto[OF assms(1,2)], of "d - c - \<delta>"] assms(3) by simp
  moreover have "\<forall>\<^sub>F K :: nat in at_top. 0 < K" by (rule eventually_gt_at_top)
  ultimately show ?thesis
    by eventually_elim (simp add: less_divide_eq)
qed


subsection \<open>Small primes: @{text "\<psi> - \<theta>"} and the valuation of 24\<close>

text \<open>@{text "\<psi>(n) = \<Sum>_{p \<le> n} \<lfloor>log_p n\<rfloor> log p"}
  (@{text "nat_log p n = floorlog p n - 1 = \<lfloor>log_p n\<rfloor>"}).\<close>
lemma card_powers_le: "prime p \<Longrightarrow> 0 < n \<Longrightarrow> card {i. 0 < i \<and>
  p ^ i \<le> n} = nat_log p n"
proof -
  assume p: "prime p" and n: "0 < n"
  have p1: "1 < p" using p by (rule prime_gt_1_nat)
  have "{i. 0 < i \<and> p ^ i \<le> n} = {1..floorlog p n - 1}"
  proof (intro equalityI subsetI)
    fix i assume "i \<in> {i. 0 < i \<and> p ^ i \<le> n}"
    hence i: "0 < i" "p ^ i \<le> n" by auto
    have "Suc i \<le> floorlog p n" by (rule floorlog_ge_SucI[OF i(2) p1])
    thus "i \<in> {1..floorlog p n - 1}" using i(1) by auto
  next
    fix i assume "i \<in> {1..floorlog p n - 1}"
    hence i: "1 \<le> i" "i + 1 \<le> floorlog p n" by auto
    have "p ^ (i + 1 - 1) \<le> n" by (rule floorlog_geD[OF i(2)]) simp
    thus "i \<in> {i. 0 < i \<and> p ^ i \<le> n}" using i(1) by simp
  qed
  thus ?thesis by (simp add: nat_log_def)
qed

lemma psi_eq_sum:
  "0 < n \<Longrightarrow> primes_psi (real n) = (\<Sum> p \<in> {p. prime p \<and>
    p \<le> n}. real (nat_log p n) * ln (real p))"
proof -
  assume n: "0 < n"
  define P where "P = {p. prime p \<and> p \<le> n}"
  define I where "I p = {i. 0 < i \<and> p ^ i \<le> n}" for p
  have fP: "finite P" unfolding P_def by simp
  have fI: "finite (I p)" if p: "p \<in> P" for p
  proof (rule finite_subset[of _ "{..n}"])
    have p2: "2 \<le> p" using p by (simp add: P_def prime_ge_2_nat)
    show "I p \<subseteq> {..n}"
    proof
      fix i assume "i \<in> I p"
      hence i: "p ^ i \<le> n" by (simp add: I_def)
      have "i < 2 ^ i" by simp
      also have "2 ^ i \<le> p ^ i" using p2 by (rule power_mono) simp
      finally show "i \<in> {..n}" using i by simp
    qed
  qed simp
  have "primes_psi (real n) = (\<Sum> (p, i) | prime p \<and> i > 0 \<and>
    real (p ^ i) \<le> real n. ln (real p))"
    unfolding primes_psi_def by (rule sum_upto_primepows) (simp_all add: mangoldt_non_primepow)
  also have "{(p, i). prime p \<and> i > 0 \<and> real (p ^ i) \<le> real n} = Sigma P I"
  proof (intro equalityI subsetI)
    fix x assume "x \<in> {(p, i). prime p \<and> i > 0 \<and> real (p ^ i) \<le> real n}"
    then obtain p i where x: "x = (p, i)" "prime p" "0 < i" "p ^ i \<le> n" by auto
    have "p \<le> p ^ i" using x(2,3) prime_ge_1_nat[OF x(2)] by (intro self_le_power) simp_all
    thus "x \<in> Sigma P I" using x by (simp add: P_def I_def)
  next
    fix x assume "x \<in> Sigma P I"
    thus "x \<in> {(p, i). prime p \<and> i > 0 \<and> real (p ^ i) \<le> real n}"
      by (force simp: P_def I_def)
  qed
  also have "(\<Sum> (p, i) \<in> Sigma P I. ln (real p)) = (\<Sum> p \<in> P. \<Sum> i \<in>
    I p. ln (real p))"
    by (rule sum.Sigma[symmetric, OF fP]) (use fI in blast)
  also have "\<dots> = (\<Sum> p \<in> P. real (nat_log p n) * ln (real p))"
  proof (rule sum.cong[OF refl])
    fix p assume p: "p \<in> P"
    have "card (I p) = nat_log p n" unfolding I_def using p n
      by (intro card_powers_le) (simp_all add: P_def)
    thus "(\<Sum> i \<in> I p. ln (real p)) = real (nat_log p n) * ln (real p)" by simp
  qed
  finally show ?thesis unfolding P_def .
qed

text \<open>@{text "\<Sum>_{p \<le> N} (\<lfloor>log_p N\<rfloor> - 1) log p =
  \<psi>(N) - \<theta>(N) \<le> 2 log N \<surd>N"}.\<close>
lemma psi_minus_theta_sum:
  assumes "2 \<le> N"
  shows "(\<Sum> p \<in> {p. prime p \<and>
    p \<le> N}. (real (nat_log p N) - 1) * ln (real p)) \<le> 2 * ln (real N) * sqrt (real N)"
proof -
  have "(\<Sum> p \<in> {p. prime p \<and>
    p \<le> N}. (real (nat_log p N) - 1) * ln (real p)) =
    primes_psi (real N) - primes_theta (real N)"
    unfolding psi_eq_sum[of N] theta_eq_sum[of "real N"] using assms
    by (simp add: sum_subtractf left_diff_distrib psi_eq_sum theta_eq_sum)
  also have "\<dots> \<le> 2 * ln (real N) * sqrt (real N)" using assms
    by (intro \<psi>_minus_\<theta>_bound) simp
  finally show ?thesis .
qed

lemma eventually_psi_theta_small:
  assumes "0 < \<delta>"
  shows "\<forall>\<^sub>F K :: nat in at_top. 2 * ln (real (5 * K)) * sqrt (real (5 * K)) \<le>
    \<delta> * real K"
proof -
  have "((\<lambda>K :: nat. 2 * ln (5 * real K) * sqrt (5 * real K) /
    real K) \<longlongrightarrow> 0) at_top"
    by real_asymp
  hence "\<forall>\<^sub>F K :: nat in at_top. 2 * ln (5 * real K) * sqrt (5 * real K) / real K <
    \<delta>"
    using assms by (rule order_tendstoD)
  moreover have "\<forall>\<^sub>F K :: nat in at_top. 0 < K" by (rule eventually_gt_at_top)
  ultimately show ?thesis by eventually_elim (simp add: divide_less_eq)
qed

lemma mult24_log_le:
  "prime p \<Longrightarrow> real (multiplicity p (24::nat)) * ln (real p) \<le> (if p \<le>
    24 then ln 24 else 0)"
proof -
  assume p: "prime p"
  have pos: "0 < p" using p by (rule prime_gt_0_nat)
  show ?thesis
  proof (cases "p \<le> 24")
    case True
    have "p ^ multiplicity p 24 dvd (24::nat)" by (rule multiplicity_dvd)
    hence "p ^ multiplicity p 24 \<le> (24::nat)" by (rule dvd_imp_le) simp
    hence le': "real (p ^ multiplicity p 24) \<le> 24" by linarith
    have pp: "0 < real (p ^ multiplicity p 24)" using pos by simp
    have "real (multiplicity p (24::nat)) * ln (real p) = ln (real (p ^ multiplicity p 24))"
      using pos by (simp add: ln_realpow)
    also have "\<dots> \<le> ln 24" using le' pp by (simp add: ln_le_cancel_iff)
    finally show ?thesis using True by simp
  next
    case False
    have "\<not> p dvd (24::nat)" using False by (fastforce dest: dvd_imp_le)
    thus ?thesis using False by (simp add: not_dvd_imp_multiplicity_0)
  qed
qed


subsection \<open>Step majorants on a uniform partition\<close>

text \<open>Grid points of the uniform partition of @{text "[a, b]"} into @{text n} cells.\<close>
definition cx :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
  where
  "cx a b n i = a + (b - a) * real i / real n"

text \<open>The supremum of @{text \<phi>} over the closed @{text i}-th cell.\<close>
definition cM :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat
  \<Rightarrow> nat \<Rightarrow> real" where
  "cM \<phi> a b n i = Sup (\<phi> ` ({cx a b n i..cx a b n (i + 1)} \<inter> {a..b}))"

text \<open>The step majorant of @{text "\<phi> + B"}.\<close>
definition cG :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
  \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "cG \<phi> a b B n y = (\<Sum> i < n. indicator {cx a b n i<..cx a b n (i + 1)} y *
    (cM \<phi> a b n i + B))"

lemma cx_mono: "a \<le> b \<Longrightarrow> i \<le> j \<Longrightarrow> cx a b n i \<le> cx a b n j"
  unfolding cx_def by (intro add_left_mono divide_right_mono mult_left_mono) simp_all

lemma cx_zero: "cx a b n 0 = a" by (simp add: cx_def)
lemma cx_self: "0 < n \<Longrightarrow> cx a b n n = b" by (simp add: cx_def)
lemma cx_succ_sub: "0 < n \<Longrightarrow> cx a b n (i + 1) - cx a b n i = (b - a) / real n"
  by (simp add: cx_def field_simps)
lemma cx_ge: "a \<le> b \<Longrightarrow> a \<le> cx a b n i" using cx_mono[of a b 0 i n]
  by (simp add: cx_zero)
lemma cx_le: "a \<le> b \<Longrightarrow> 0 < n \<Longrightarrow> i \<le> n \<Longrightarrow>
  cx a b n i \<le> b" using cx_mono[of a b i n n] by (simp add: cx_self)

lemma cell_unique:
  assumes "a \<le> b" "y \<in> {cx a b n i<..cx a b n (i + 1)}" "y \<in>
    {cx a b n j<..cx a b n (j + 1)}"
  shows "i = j"
proof (rule ccontr)
  assume ne: "i \<noteq> j"
  show False
  proof (cases "i < j")
    case True
    have "cx a b n (i + 1) \<le> cx a b n j" using True by (intro cx_mono[OF assms(1)]) simp
    thus False using assms(2,3) by auto
  next
    case False
    hence "j < i" using ne by simp
    hence "cx a b n (j + 1) \<le> cx a b n i" by (intro cx_mono[OF assms(1)]) simp
    thus False using assms(2,3) by force
  qed
qed

lemma cell_exists:
  assumes "a < b" "0 < n" "y \<in> {a<..b}"
  shows "\<exists>i < n. y \<in> {cx a b n i<..cx a b n (i + 1)}"
proof -
  have w: "0 < b - a" using assms(1) by simp
  have nr: "0 < real n" using assms(2) by simp
  have y: "a < y" "y \<le> b" using assms(3) by auto
  define t where "t = (y - a) * real n / (b - a)"
  have t0: "0 < t" unfolding t_def using y w nr by simp
  have tn: "t \<le> real n" unfolding t_def using y w nr by (simp add: field_simps)
  define k where "k = nat \<lceil>t\<rceil>"
  have k1: "1 \<le> k" unfolding k_def using t0 by linarith
  have kn: "k \<le> n" unfolding k_def using tn by simp
  have kt1: "real k - 1 < t" unfolding k_def using t0 by linarith
  have kt2: "t \<le> real k" unfolding k_def using t0 by simp
  have e: "real (k - 1) = real k - 1" using k1 by simp
  have e2: "k - 1 + 1 = k" using k1 by simp
  have lo: "cx a b n (k - 1) < y" unfolding cx_def e using kt1 w nr by (simp add: t_def field_simps)
  have hi: "y \<le> cx a b n (k - 1 + 1)" unfolding cx_def e2 using kt2 w nr
    by (simp add: t_def field_simps)
  have "k - 1 < n" using k1 kn by linarith
  thus ?thesis using lo hi by auto
qed

lemma cM_bdd:
  fixes \<phi> :: "real \<Rightarrow> real"
  assumes "\<And>y. y \<in> {a..b} \<Longrightarrow> \<bar>\<phi> y\<bar> \<le> B"
  shows "bdd_above (\<phi> ` ({cx a b n i..cx a b n (i + 1)} \<inter> {a..b}))"
proof (rule bdd_aboveI[of _ B])
  fix z assume "z \<in> \<phi> ` ({cx a b n i..cx a b n (i + 1)} \<inter> {a..b})"
  then obtain y where y: "y \<in> {a..b}" "z = \<phi> y" by auto
  show "z \<le> B" using assms[OF y(1)] y(2) abs_ge_self[of "\<phi> y"] by linarith
qed

lemma cM_le:
  assumes "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> B" "0 \<le> B" "a \<le> b" "0 < n" "i < n"
  shows "cM \<phi> a b n i \<le> B"
proof -
  have mem: "cx a b n i \<in> {cx a b n i..cx a b n (i + 1)} \<inter> {a..b}"
    using cx_mono[OF assms(3), of i "i + 1" n] cx_ge[OF assms(3), of n i] cx_le[OF assms(3,4),
      of i] assms(5) by auto
  have "Sup (\<phi> ` ({cx a b n i..cx a b n (i + 1)} \<inter> {a..b})) \<le> B"
  proof (rule cSup_least)
    show "\<phi> ` ({cx a b n i..cx a b n (i + 1)} \<inter> {a..b}) \<noteq> {}" using mem by blast
    fix x assume "x \<in> \<phi> ` ({cx a b n i..cx a b n (i + 1)} \<inter> {a..b})"
    then obtain y where y: "y \<in> {a..b}" "x = \<phi> y" by auto
    show "x \<le> B" using assms(1)[OF y(1)] y(2) by linarith
  qed
  thus ?thesis unfolding cM_def .
qed

lemma cM_ge:
  assumes "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> B" "a \<le> b" "0 < n" "i < n"
  shows "- B \<le> cM \<phi> a b n i"
proof -
  have mem: "cx a b n i \<in> {cx a b n i..cx a b n (i + 1)} \<inter> {a..b}"
    using cx_mono[OF assms(2), of i "i + 1" n] cx_ge[OF assms(2), of n i] cx_le[OF assms(2,3),
      of i] assms(4) by auto
  have "\<phi> (cx a b n i) \<le> cM \<phi> a b n i" unfolding cM_def
    by (rule cSup_upper[OF imageI[OF mem] cM_bdd[OF assms(1)]])
  moreover have "- B \<le> \<phi> (cx a b n i)" using assms(1)[of "cx a b n i"] mem by fastforce
  ultimately show ?thesis by linarith
qed

lemma le_cM:
  assumes "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> B" "y \<in> {cx a b n i..cx a b n (i + 1)} \<inter> {a..b}"
  shows "\<phi> y \<le> cM \<phi> a b n i"
  unfolding cM_def by (rule cSup_upper[OF _ cM_bdd[OF assms(1)]]) (use assms(2) in auto)

lemma cG_eval:
  assumes "a < b" "0 < n" "y \<in> {a<..b}"
  shows "\<exists>i < n. y \<in> {cx a b n i<..cx a b n (i + 1)} \<and>
    cG \<phi> a b B n y = cM \<phi> a b n i + B"
proof -
  obtain i where i: "i < n" "y \<in> {cx a b n i<..cx a b n (i + 1)}" using cell_exists[OF assms]
    by blast
  have "cG \<phi> a b B n y = cM \<phi> a b n i + B"
    unfolding cG_def
  proof -
    have z: "indicator {cx a b n j<..cx a b n (j + 1)} y * (cM \<phi> a b n j + B) = 0"
      if j: "j \<in> {..<n} - {i}" for j
    proof -
      have "y \<notin> {cx a b n j<..cx a b n (j + 1)}"
      proof
        assume "y \<in> {cx a b n j<..cx a b n (j + 1)}"
        hence "j = i" by (rule cell_unique[OF less_imp_le[OF assms(1)] _ i(2)])
        thus False using j by simp
      qed
      thus ?thesis by simp
    qed
    have "(\<Sum> j < n. indicator {cx a b n j<..cx a b n (j + 1)} y * (cM \<phi> a b n j + B)) =
        indicator {cx a b n i<..cx a b n (i + 1)} y * (cM \<phi> a b n i + B) + (\<Sum> j \<in>
          {..<n} - {i}. indicator {cx a b n j<..cx a b n (j + 1)} y * (cM \<phi> a b n j + B))"
      by (rule sum.remove) (use i in auto)
    also have "(\<Sum> j \<in> {..<n} - {i}. indicator {cx a b n j<..cx a b n (j + 1)} y *
      (cM \<phi> a b n j + B)) = 0"
      by (rule sum.neutral) (use z in blast)
    also have "indicator {cx a b n i<..cx a b n (i + 1)} y * (cM \<phi> a b n i + B) =
      cM \<phi> a b n i + B" using i(2) by simp
    finally show "(\<Sum> j < n. indicator {cx a b n j<..cx a b n (j + 1)} y * (cM \<phi> a b n j +
      B)) = cM \<phi> a b n i + B" by simp
  qed
  thus ?thesis using i by blast
qed

lemma cG_bounds:
  assumes "a < b" "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> B" "0 \<le> B" "0 < n" "y \<in> {a<..b}"
  shows "\<phi> y + B \<le> cG \<phi> a b B n y \<and> 0 \<le> cG \<phi> a b B n y \<and>
    cG \<phi> a b B n y \<le> 2 * B"
proof -
  obtain i where i: "i < n" "y \<in> {cx a b n i<..cx a b n (i + 1)}" and e: "cG \<phi> a b B n y =
    cM \<phi> a b n i + B"
    using cG_eval[OF assms(1,4,5)] by blast
  have "\<phi> y \<le> cM \<phi> a b n i" using i assms(5) by (intro le_cM[OF assms(2)]) auto
  moreover have "cM \<phi> a b n i \<le> B"
    by (rule cM_le[OF assms(2,3) less_imp_le[OF assms(1)] assms(4) i(1)])
  moreover have "- B \<le> cM \<phi> a b n i"
    by (rule cM_ge[OF assms(2) less_imp_le[OF assms(1)] assms(4) i(1)])
  ultimately show ?thesis unfolding e by linarith
qed

lemma cG_measurable [measurable]: "cG \<phi> a b B n \<in> borel_measurable borel"
  unfolding cG_def by measurable

text \<open>At a continuity point of @{text \<phi>} inside @{text "(a, b)"},
  the majorants converge to @{text "\<phi> y + B"}.\<close>
lemma cG_tendsto:
  assumes "a < b" "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> B" "y \<in> {a<..<b}" "isCont \<phi> y"
  shows "((\<lambda>n. cG \<phi> a b B n y) \<longlongrightarrow> \<phi> y + B) at_top"
proof (rule tendstoI)
  fix \<eta> :: real assume \<eta>: "0 < \<eta>"
  obtain \<delta> where \<delta>: "0 < \<delta>" "\<And>u. dist u y < \<delta> \<Longrightarrow>
    dist (\<phi> u) (\<phi> y) < \<eta> / 2"
  proof -
    have h: "\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> y \<and>
      dist x y < s \<longrightarrow> dist (\<phi> x) (\<phi> y) < r"
      using assms(4) unfolding isCont_def LIM_eq dist_norm .
    have "\<exists>s>0. \<forall>x. x \<noteq> y \<and> dist x y < s \<longrightarrow>
      dist (\<phi> x) (\<phi> y) < \<eta> / 2"
      by (rule h[rule_format]) (use \<eta> in simp)
    then obtain s where s: "0 < s" "\<And>x. x \<noteq> y \<Longrightarrow>
      dist x y < s \<Longrightarrow> dist (\<phi> x) (\<phi> y) < \<eta> / 2" by blast
    have "dist (\<phi> u) (\<phi> y) < \<eta> / 2" if "dist u y < s" for u
    proof (cases "u = y")
      case True thus ?thesis using \<eta> by simp
    next
      case False thus ?thesis using s(2) that by blast
    qed
    thus ?thesis using s(1) that by blast
  qed
  obtain N :: nat where N: "(b - a) / \<delta> < real N" using reals_Archimedean2 by blast
  show "\<forall>\<^sub>F n in at_top. dist (cG \<phi> a b B n y) (\<phi> y + B) < \<eta>"
  proof (rule eventually_at_top_linorderI[of "N + 1"])
    fix n :: nat assume n: "N + 1 \<le> n"
    have n0: "0 < n" using n by simp
    obtain i where i: "i < n" "y \<in> {cx a b n i<..cx a b n (i +
      1)}" and e: "cG \<phi> a b B n y = cM \<phi> a b n i + B"
      using cG_eval[OF assms(1) n0, of y \<phi> B] assms(3) by auto
    have low: "\<phi> y \<le> cM \<phi> a b n i" using i assms(3) by (intro le_cM[OF assms(2)]) auto
    have width: "cx a b n (i + 1) - cx a b n i < \<delta>"
    proof -
      have "b - a < real N * \<delta>" using N \<delta>(1) by (simp add: divide_less_eq)
      moreover have "real N * \<delta> \<le> real n * \<delta>" using n \<delta>(1) by simp
      ultimately have "b - a < real n * \<delta>" by linarith
      thus ?thesis unfolding cx_succ_sub[OF n0] using n0
        by (simp add: pos_divide_less_eq mult.commute)
    qed
    have up: "cM \<phi> a b n i \<le> \<phi> y + \<eta> / 2"
      unfolding cM_def
    proof (rule cSup_least)
      show "\<phi> ` ({cx a b n i..cx a b n (i + 1)} \<inter> {a..b}) \<noteq> {}"
        using i(2) assms(3) by force
      fix z assume "z \<in> \<phi> ` ({cx a b n i..cx a b n (i + 1)} \<inter> {a..b})"
      then obtain u where u: "u \<in> {cx a b n i..cx a b n (i + 1)} \<inter> {a..b}" "z =
        \<phi> u" by auto
      have "dist u y < \<delta>" using u(1) i(2) width by (fastforce simp: dist_real_def)
      hence "dist (\<phi> u) (\<phi> y) < \<eta> / 2" by (rule \<delta>(2))
      thus "z \<le> \<phi> y + \<eta> / 2" using u(2) abs_ge_self[of "\<phi> u - \<phi> y"]
        unfolding dist_real_def by linarith
    qed
    show "dist (cG \<phi> a b B n y) (\<phi> y + B) < \<eta>" unfolding e dist_real_def
      using low up \<eta> by simp
  qed
qed

lemma set_integral_sum_nat:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes "\<And>i. i \<in> I \<Longrightarrow> set_integrable lborel A (f i)"
  shows "set_integrable lborel A (\<lambda>x. \<Sum> i \<in> I. f i x) \<and>
         set_lebesgue_integral lborel A (\<lambda>x. \<Sum> i \<in> I. f i x) = (\<Sum> i \<in>
           I. set_lebesgue_integral lborel A (f i))"
proof -
  have i: "\<And>i. i \<in> I \<Longrightarrow>
    integrable lborel (\<lambda>x. indicator A x *\<^sub>R f i x)" using assms
    unfolding set_integrable_def .
  have e: "(\<lambda>x. indicator A x *\<^sub>R (\<Sum> i \<in> I. f i x)) =
    (\<lambda>x. \<Sum> i \<in> I. indicator A x *\<^sub>R f i x)"
    by (simp add: sum_distrib_left)
  show ?thesis unfolding set_integrable_def set_lebesgue_integral_def e
    using Bochner_Integration.integrable_sum[OF i] Bochner_Integration.integral_sum[OF i]
      by (rule conjI)
qed

lemma integral_cG:
  assumes "a < b" "0 < n"
  shows "interval_lebesgue_integral lborel (ereal a) (ereal b) (cG \<phi> a b B n) = (\<Sum> i <
    n. (cM \<phi> a b n i + B) * ((b - a) / real n))"
proof -
  have ab: "a \<le> b" using assms(1) by simp
  define C where "C i = {cx a b n i<..cx a b n (i + 1)}" for i
  define c where "c i = cM \<phi> a b n i + B" for i
  have cx3: "a \<le> cx a b n i \<and> cx a b n (i + 1) \<le> b \<and>
    cx a b n i \<le> cx a b n (i + 1)" if "i < n" for i
    using cx_ge[OF ab, of n i] cx_le[OF ab assms(2), of "i + 1"] cx_mono[OF ab,
      of i "i + 1" n] that by auto
  have nb: "{b} \<in> null_sets lborel" by (simp add: finite_imp_null_set_lborel)
  have meas: "measure lborel (C i \<inter> {a<..<b}) = (b - a) / real n" if i: "i < n" for i
  proof -
    have "C i \<inter> {a<..<b} = C i - {b}" using cx3[OF i] unfolding C_def by fastforce
    hence "measure lborel (C i \<inter> {a<..<b}) = measure lborel (C i - {b})" by simp
    also have "\<dots> = measure lborel (C i)" unfolding C_def
      by (rule measure_Diff_null_set[OF _ nb]) simp
    also have "\<dots> = cx a b n (i + 1) - cx a b n i" unfolding C_def using cx3[OF i] by simp
    also have "\<dots> = (b - a) / real n" by (rule cx_succ_sub[OF assms(2)])
    finally show ?thesis .
  qed
  have one: "set_lebesgue_integral lborel {a<..<b} (\<lambda>y. indicator (C i) y * c i) =
    c i * ((b - a) / real n)" if i: "i < n" for i
  proof -
    have "(\<lambda>y. indicator {a<..<b} y *\<^sub>R (indicator (C i) y * c i)) =
      (\<lambda>y. c i * indicator (C i \<inter> {a<..<b}) y)"
      by (auto simp: fun_eq_iff indicator_def)
    hence "set_lebesgue_integral lborel {a<..<b} (\<lambda>y. indicator (C i) y * c i) =
      c i * measure lborel (C i \<inter> {a<..<b})"
      unfolding set_lebesgue_integral_def by simp
    thus ?thesis unfolding meas[OF i] .
  qed
  have ints: "set_integrable lborel {a<..<b} (\<lambda>y. indicator (C i) y * c i)"
    if i: "i \<in> {..<n}" for i
  proof -
    have "(\<lambda>y. indicator {a<..<b} y *\<^sub>R (indicator (C i) y * c i)) =
      (\<lambda>y. c i * indicator (C i \<inter> {a<..<b}) y)"
      by (auto simp: fun_eq_iff indicator_def)
    moreover have "integrable lborel (indicator (C i \<inter> {a<..<b}) :: real \<Rightarrow> real)"
    proof -
      have "emeasure lborel (C i \<inter> {a<..<b}) \<le> emeasure lborel {a<..<b}"
        by (rule emeasure_mono) (simp_all add: C_def)
      also have "\<dots> = ennreal (b - a)" using ab by simp
      finally have "emeasure lborel (C i \<inter> {a<..<b}) < \<infinity>"
        using ennreal_less_top[of "b - a"] by (auto intro: order.strict_trans1)
      thus ?thesis by (simp add: integrable_indicator_iff C_def)
    qed
    ultimately show ?thesis unfolding set_integrable_def by simp
  qed
  have "interval_lebesgue_integral lborel (ereal a) (ereal b) (cG \<phi> a b B n) =
      set_lebesgue_integral lborel {a<..<b} (\<lambda>y. \<Sum> i < n. indicator (C i) y * c i)"
    using ab unfolding cG_def C_def c_def by (simp add: interval_lebesgue_integral_le_eq)
  also have "\<dots> = (\<Sum> i < n. set_lebesgue_integral lborel {a<..<b} (\<lambda>y. indicator
    (C i) y * c i))"
    by (rule conjunct2[OF set_integral_sum_nat[OF ints]])
  also have "\<dots> = (\<Sum> i < n. c i * ((b - a) / real n))"
    by (rule sum.cong[OF refl]) (rule one, simp)
  finally show ?thesis unfolding c_def .
qed


subsection \<open>Dominated convergence for the majorants\<close>

lemma ae_cG_tendsto:
  assumes "a < b" "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> B" "countable D"
    and "\<And>y. y \<in> {a<..<b} \<Longrightarrow> y \<notin> D \<Longrightarrow> isCont \<phi> y"
  shows "AE y in lborel. y \<in> {a<..<b} \<longrightarrow>
    ((\<lambda>n. cG \<phi> a b B n y) \<longlongrightarrow> \<phi> y + B) at_top"
proof -
  have "AE y in lborel. y \<notin> D" by (rule AE_not_in[OF countable_imp_null_set_lborel[OF
    assms(3)]])
  thus ?thesis
  proof eventually_elim
    case (elim y)
    show ?case using cG_tendsto[of a b \<phi> B y, OF assms(1,2)] assms(4) elim by blast
  qed
qed

text \<open>@{text "\<phi>"} (restricted to @{text "(a, b)"}) is Borel measurable and
  integrable.\<close>
lemma phi_measurable:
  fixes \<phi> :: "real \<Rightarrow> real"
  assumes "countable D" "\<And>y. y \<in> {a<..<b} \<Longrightarrow> y \<notin> D \<Longrightarrow>
    isCont \<phi> y"
  shows "(\<lambda>y. indicator {a<..<b} y * \<phi> y) \<in> borel_measurable borel"
proof (rule borel_measurable_continuous_countable_exceptions[of "D \<union> {a, b}"])
  show "countable (D \<union> {a, b})" using assms(1) by simp
  show "continuous_on (- (D \<union> {a, b})) (\<lambda>y. indicator {a<..<b} y * \<phi> y)"
  proof (rule continuous_at_imp_continuous_on, rule ballI)
    fix x assume x: "x \<in> - (D \<union> {a, b})"
    show "isCont (\<lambda>y. indicator {a<..<b} y * \<phi> y) x"
    proof (cases "x \<in> {a<..<b}")
      case True
      have "eventually (\<lambda>y. y \<in> {a<..<b}) (nhds x)"
        by (rule eventually_nhds_in_open) (use True in auto)
      hence e: "eventually (\<lambda>y. indicator {a<..<b} y * \<phi> y = \<phi> y) (nhds x)"
        by eventually_elim simp
      have "isCont \<phi> x" using assms(2) True x by auto
      thus ?thesis using isCont_cong[OF e] by simp
    next
      case False
      hence "x \<in> {..<a} \<union> {b<..}" using x by force
      hence "eventually (\<lambda>y. y \<in> {..<a} \<union> {b<..}) (nhds x)"
        by (intro eventually_nhds_in_open) auto
      hence e: "eventually (\<lambda>y. indicator {a<..<b} y * \<phi> y = 0) (nhds x)"
        by eventually_elim auto
      have "isCont (\<lambda>y. 0::real) x" by simp
      thus ?thesis using isCont_cong[OF e] by simp
    qed
  qed
qed

lemma phi_integrable:
  fixes \<phi> :: "real \<Rightarrow> real"
  assumes "a < b" "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> B" "countable D"
    and "\<And>y. y \<in> {a<..<b} \<Longrightarrow> y \<notin> D \<Longrightarrow> isCont \<phi> y"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal b) \<phi>"
proof -
  have "integrable lborel (\<lambda>y. indicator {a<..<b} y *\<^sub>R \<phi> y)"
  proof (rule Bochner_Integration.integrable_bound)
    show "integrable lborel (\<lambda>y. indicator {a<..<b} y *\<^sub>R B)"
      using interval_integral_const(1)[of a b B] assms(1)
      unfolding interval_lebesgue_integrable_def set_integrable_def by force
    show "(\<lambda>y. indicator {a<..<b} y *\<^sub>R \<phi> y) \<in> borel_measurable lborel"
      using phi_measurable[of D a b \<phi>, OF assms(3,4)] by fastforce
    show "AE y in lborel. norm (indicator {a<..<b} y *\<^sub>R \<phi> y) \<le>
      norm (indicator {a<..<b} y *\<^sub>R B)"
    proof (rule AE_I2)
      fix y :: real
      show "norm (indicator {a<..<b} y *\<^sub>R \<phi> y) \<le>
        norm (indicator {a<..<b} y *\<^sub>R B)"
        using assms(2)[of y] by (force simp: indicator_def)
    qed
  qed
  thus ?thesis unfolding interval_lebesgue_integrable_def set_integrable_def using assms(1) by force
qed

lemma integral_cG_tendsto:
  assumes "a < b" "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> B" "0 \<le> B" "countable D"
    and "\<And>y. y \<in> {a<..<b} \<Longrightarrow> y \<notin> D \<Longrightarrow> isCont \<phi> y"
  shows "((\<lambda>n. interval_lebesgue_integral lborel (ereal a) (ereal b) (cG \<phi> a b B n))
            \<longlongrightarrow> interval_lebesgue_integral lborel (ereal a) (ereal b) (\<lambda>y.
              \<phi> y + B)) at_top"
proof -
  have ab: "ereal a \<le> ereal b" using assms(1) by simp
  define s where "s n y = indicator {a<..<b} y *\<^sub>R cG \<phi> a b B n y" for n y
  define g where "g y = indicator {a<..<b} y *\<^sub>R (\<phi> y + B)" for y
  define w where "w y = indicator {a<..<b} y *\<^sub>R (2 * B)" for y
  have gm: "g \<in> borel_measurable lborel"
  proof -
    have "(\<lambda>y. indicator {a<..<b} y * \<phi> y) \<in> borel_measurable borel"
      by (rule phi_measurable[of D a b \<phi>, OF assms(4,5)])
    moreover have "(\<lambda>y. indicator {a<..<b} y * B :: real) \<in> borel_measurable borel"
      by measurable
    ultimately have "(\<lambda>y. indicator {a<..<b} y * \<phi> y + indicator {a<..<b} y * B) \<in>
      borel_measurable borel" by measurable
    thus ?thesis unfolding g_def by (simp add: distrib_left)
  qed
  have sm: "s n \<in> borel_measurable lborel" for n unfolding s_def by measurable
  have wi: "integrable lborel w"
    using interval_integral_const(1)[of a b "2 * B"] assms(1)
    unfolding interval_lebesgue_integrable_def set_integrable_def w_def by simp
  have "AE y in lborel. y \<in> {a<..<b} \<longrightarrow>
    ((\<lambda>n. cG \<phi> a b B n y) \<longlongrightarrow> \<phi> y + B) at_top"
    using assms(1,2,4,5) by (rule ae_cG_tendsto)
  hence lim: "AE y in lborel. (\<lambda>n. s n y) \<longlonglongrightarrow> g y"
  proof (eventually_elim)
    case (elim y)
    show ?case
    proof (cases "y \<in> {a<..<b}")
      case True thus ?thesis using elim by (simp add: s_def g_def)
    next
      case False thus ?thesis by (simp add: s_def g_def)
    qed
  qed
  have bound: "AE y in lborel. norm (s n y) \<le> w y" for n
  proof (rule AE_I2)
    fix y :: real
    show "norm (s n y) \<le> w y"
    proof (cases "y \<in> {a<..<b} \<and> 0 < n")
      case True
      have "0 \<le> cG \<phi> a b B n y \<and> cG \<phi> a b B n y \<le> 2 * B"
        using cG_bounds[of a b \<phi> B n y, OF assms(1,2,3)] True by auto
      thus ?thesis using True by (simp add: s_def w_def)
    next
      case False
      thus ?thesis using assms(3) by (auto simp: s_def w_def cG_def)
    qed
  qed
  have "(\<lambda>n. integral\<^sup>L lborel (s n)) \<longlonglongrightarrow> integral\<^sup>L
    lborel g"
    by (rule integral_dominated_convergence[OF gm sm wi lim bound])
  thus ?thesis unfolding interval_lebesgue_integral_le_eq[OF ab] einterval_eq_Icc
    set_lebesgue_integral_def s_def g_def .
qed

text \<open>The change of variables @{text "x = 1/y"}:
  @{text "\<integral>_{1/M}^{1/3} y f(1/y) dy = \<integral>_3^M f(x)/x^3 dx"}.\<close>
lemma integral_inv_subst:
  fixes f :: "real \<Rightarrow> real"
  assumes "3 \<le> M" "(\<lambda>x. indicator {3<..<M} x * f x) \<in>
    borel_measurable borel" "\<And>x. x \<in> {3..M} \<Longrightarrow> \<bar>f x\<bar> \<le> Bd"
  shows "interval_lebesgue_integral lborel (ereal (1 / M)) (ereal (1 / 3)) (\<lambda>y. y * f (1 /
    y))
           = interval_lebesgue_integral lborel (ereal 3) (ereal M) (\<lambda>x. f x / x ^ 3)"
proof (cases "M = 3")
  case True
  show ?thesis using True by simp
next
  case False
  note M = assms(1) and hm = assms(2) and Bnd = assms(3)
  have M0: "0 < M" using M by simp
  have M3: "3 < M" using M False by simp
  have iM: "0 < 1 / M" using M0 by simp
  define h where "h x = indicator {3<..<M} x * f x" for x :: real
  have hm': "h \<in> borel_measurable borel" using hm unfolding h_def[abs_def] .
  define F where "F u = - u * f (- 1 / u)" for u :: real
  define g where "g x = - 1 / x" for x :: real
  define g' where "g' x = 1 / x ^ 2" for x :: real
  define c where "c = - (1 / 3 :: real)"
  define d where "d = - (1 / M)"
  have cd: "c < d" unfolding c_def d_def using M3 by (simp add: field_simps)
  have gc: "g 3 = c" "g M = d" unfolding g_def c_def d_def by simp_all
  \<comment> \<open>reflection\<close>
  have r: "interval_lebesgue_integral lborel (ereal (1 / M)) (ereal (1 / 3)) (\<lambda>y. y * f (1 /
    y))
      = interval_lebesgue_integral lborel (ereal c) (ereal d) F"
    using interval_integral_reflect[of "ereal (1 / M)" "ereal (1 / 3)" "\<lambda>y. y * f (1 / y)"]
    unfolding F_def c_def d_def by simp
  \<comment> \<open>integrability of F on the closed interval\<close>
  have Fo: "set_integrable lborel {c<..<d} F"
  proof -
    have eq: "(\<lambda>u. indicator {c<..<d} u *\<^sub>R F u) =
      (\<lambda>u. indicator {c<..<d} u * (- u * h (- 1 / u)))"
    proof (rule ext)
      fix u :: real
      show "indicator {c<..<d} u *\<^sub>R F u = indicator {c<..<d} u * (- u * h (- 1 / u))"
      proof (cases "u \<in> {c<..<d}")
        case True
        hence ud: "u < - (1 / M)" unfolding d_def by simp
        hence u0: "u < 0" using iM by linarith
        have "3 < - 1 / u" "- 1 / u < M" using True u0 M0 unfolding c_def d_def
          by (auto simp: field_simps)
        thus ?thesis unfolding F_def h_def using True by simp
      qed simp
    qed
    have mm: "(\<lambda>u. indicator {c<..<d} u * (- u * h (- 1 / u))) \<in>
      borel_measurable lborel"
      using hm' by simp
    show ?thesis unfolding set_integrable_def eq
    proof (rule Bochner_Integration.integrable_bound)
      show "integrable lborel (\<lambda>u. indicator {c<..<d} u *\<^sub>R Bd)"
        using interval_integral_const(1)[of c d Bd] cd
          unfolding interval_lebesgue_integrable_def set_integrable_def by simp
      show "(\<lambda>u. indicator {c<..<d} u * (- u * h (- 1 / u))) \<in> borel_measurable lborel"
        by (rule mm)
      show "AE u in lborel. norm (indicator {c<..<d} u * (- u * h (- 1 / u))) \<le>
        norm (indicator {c<..<d} u *\<^sub>R Bd)"
      proof (rule AE_I2)
        fix u :: real
        show "norm (indicator {c<..<d} u * (- u * h (- 1 / u))) \<le>
          norm (indicator {c<..<d} u *\<^sub>R Bd)"
        proof (cases "u \<in> {c<..<d}")
          case True
          hence ud: "u < - (1 / M)" "- (1 / 3) < u" unfolding c_def d_def by simp_all
          hence u0: "u < 0" "- 1 \<le> u" using iM by linarith+
          have i: "3 < - 1 / u" "- 1 / u < M" using True u0 M0 unfolding c_def d_def
            by (auto simp: field_simps)
          have fb: "\<bar>f (- 1 / u)\<bar> \<le> Bd" using Bnd i by simp
          have "\<bar>- u * h (- 1 / u)\<bar> = \<bar>u\<bar> * \<bar>f (- 1 / u)\<bar>"
            unfolding h_def using i by (simp add: abs_mult)
          also have "\<dots> \<le> 1 * Bd" by (rule mult_mono) (use u0 fb in auto)
          finally show ?thesis using True by fastforce
        qed simp
      qed
    qed
  qed
  have Fc: "set_integrable lborel {g 3..g M} F"
  proof -
    have "{g 3..g M} = {c<..<d} \<union> {c} \<union> {d}" unfolding gc using cd by force
    moreover have "set_integrable lborel ({c<..<d} \<union> {c} \<union> {d}) F"
      by (intro set_integrable_Un Fo set_borel_integrable_singleton) simp_all
    ultimately show ?thesis by simp
  qed
  have derivg: "(g has_real_derivative g' x) (at x)" if "x \<in> {3..M}" for x
  proof -
    have "x \<noteq> 0" using that by simp
    thus ?thesis unfolding g_def g'_def
      by (fastforce simp: power2_eq_square intro: derivative_eq_intros)
  qed
  have contg': "continuous_on {3..M} g'" unfolding g'_def by (fastforce intro: continuous_intros)
  have nn: "0 \<le> g' x" if "x \<in> {3..M}" for x unfolding g'_def by simp
  have "interval_lebesgue_integral lborel (ereal (g 3)) (ereal (g M)) F =
    interval_lebesgue_integral lborel (ereal 3) (ereal M) (\<lambda>x. F (g x) * g' x)"
    by (rule interval_integral_substitution(2)[OF Fc derivg contg' nn M])
  moreover have "interval_lebesgue_integral lborel (ereal 3) (ereal M) (\<lambda>x. F (g x) *
    g' x) = interval_lebesgue_integral lborel (ereal 3) (ereal M) (\<lambda>x. f x / x ^ 3)"
  proof (rule interval_integral_cong)
    fix x assume "x \<in> einterval (min (ereal 3) (ereal M)) (max (ereal 3) (ereal M))"
    hence x: "3 < x" using M by simp
    show "F (g x) * g' x = f x / x ^ 3" unfolding F_def g_def g'_def using x
      by (simp add: field_simps power2_eq_square power3_eq_cube)
  qed
  ultimately show ?thesis unfolding r unfolding gc by simp
qed


subsection \<open>The Riemann-sum bounds\<close>

lemma split2_aux: "c * ((x + d) * k) = c * x * k + d * k * (c :: real)"
  by (simp add: algebra_simps)

text \<open>Outer range, variable @{text "y = p/K"}: Riemann-sum upper bound
  for a bounded, almost-everywhere
  continuous @{text \<phi>} (step majorants + the PNT cell estimates).\<close>
theorem outer_prime_sum_bound:
  assumes a: "0 < a" and ab: "a \<le> b" and Bd: "\<And>y. y \<in> {a..b} \<Longrightarrow>
    \<bar>\<phi> y\<bar> \<le> Bd" and D: "countable D"
    and cont: "\<And>y. y \<in> {a<..<b} \<Longrightarrow> y \<notin> D \<Longrightarrow>
      isCont \<phi> y" and e: "0 < \<epsilon>"
  shows "\<forall>\<^sub>F K in at_top.
    (\<Sum> p \<in> {p. p \<le> nat (floor (b * real K)) \<and> prime p \<and>
      a * real K < real p \<and> real p \<le> b * real K}.
        \<phi> (real p / real K) * ln (real p))
      \<le> (interval_lebesgue_integral lborel (ereal a) (ereal b) \<phi> + \<epsilon>) * real K"
proof (cases "a = b")
  case True
  show ?thesis
  proof (rule always_eventually, rule allI)
    fix K :: nat
    have e0: "{p. p \<le> nat (floor (b * real K)) \<and> prime p \<and> a * real K < real p \<and>
      real p \<le> b * real K} = {}"
      using True by simp
    show "(\<Sum> p \<in> {p. p \<le> nat (floor (b * real K)) \<and> prime p \<and>
      a * real K < real p \<and> real p \<le> b * real K}.
        \<phi> (real p / real K) * ln (real p)) \<le>
          (interval_lebesgue_integral lborel (ereal a) (ereal b) \<phi> + \<epsilon>) * real K"
      unfolding e0 using True e by auto
  qed
next
  case False
  hence ab': "a < b" using ab by simp
  have B0: "0 \<le> Bd" using Bd[of a] ab by auto
  define I where "I = interval_lebesgue_integral lborel (ereal a) (ereal b) \<phi>"
  have IB: "interval_lebesgue_integral lborel (ereal a) (ereal b) (\<lambda>y. \<phi> y + Bd) =
    I + (b - a) * Bd"
    unfolding I_def
  proof -
    have phiI: "interval_lebesgue_integrable lborel (ereal a) (ereal b) \<phi>" using ab' Bd D cont
      by (rule phi_integrable)
    show "interval_lebesgue_integral lborel (ereal a) (ereal b) (\<lambda>y. \<phi> y + Bd) =
      interval_lebesgue_integral lborel (ereal a) (ereal b) \<phi> + (b - a) * Bd"
      using interval_lebesgue_integral_add(2)[OF phiI interval_integral_const(1)[of a b Bd]]
        interval_integral_const(2)[of a b Bd] by simp
  qed
  obtain n where n0: "0 < n" and n1: "interval_lebesgue_integral lborel (ereal a) (ereal b) (cG
    \<phi> a b Bd n) < I + (b - a) * Bd + \<epsilon> / 2"
  proof -
    have "((\<lambda>n. interval_lebesgue_integral lborel (ereal a) (ereal b) (cG \<phi> a b Bd n))
        \<longlongrightarrow> interval_lebesgue_integral lborel (ereal a) (ereal b) (\<lambda>y.
          \<phi> y + Bd)) at_top"
      using ab' Bd B0 D cont by (rule integral_cG_tendsto)
    hence lim: "((\<lambda>n. interval_lebesgue_integral lborel (ereal a) (ereal b) (cG \<phi> a b
      Bd n)) \<longlongrightarrow> I + (b - a) * Bd) at_top"
      unfolding IB .
    have "\<forall>\<^sub>F n in at_top. interval_lebesgue_integral lborel (ereal a) (ereal b) (cG
      \<phi> a b Bd n) < I + (b - a) * Bd + \<epsilon> / 2"
      using order_tendstoD(2)[OF lim, of "I + (b - a) * Bd + \<epsilon> / 2"] e by auto
    moreover have "\<forall>\<^sub>F n :: nat in at_top. 0 < n" by (rule eventually_gt_at_top)
    ultimately have "\<forall>\<^sub>F n in at_top. 0 < n \<and>
      interval_lebesgue_integral lborel (ereal a) (ereal b) (cG \<phi> a b Bd n) <
      I + (b - a) * Bd + \<epsilon> / 2"
      by eventually_elim simp
    then obtain n where "0 < n" "interval_lebesgue_integral lborel (ereal a) (ereal b) (cG \<phi> a
      b Bd n) < I + (b - a) * Bd + \<epsilon> / 2"
      by (auto simp: eventually_at_top_linorder)
    thus ?thesis using that by blast
  qed
  define T where "T = (\<Sum> i < n. cM \<phi> a b n i + Bd)"
  define \<delta> where "\<delta> = \<epsilon> / (2 * ((2 * real n + 1) * Bd + 1))"
  have d0: "0 < \<delta>"
  proof -
    have "0 \<le> (2 * real n + 1) * Bd" by (intro mult_nonneg_nonneg B0) simp
    hence "0 < 2 * ((2 * real n + 1) * Bd + 1)" by simp
    thus ?thesis unfolding \<delta>_def using e by simp
  qed
  have dB: "(2 * real n + 1) * Bd * \<delta> \<le> \<epsilon> / 2"
  proof -
    have "0 \<le> (2 * real n + 1) * Bd" by (intro mult_nonneg_nonneg B0) simp
    hence "0 < 2 * ((2 * real n + 1) * Bd + 1)" by simp
    hence eq: "\<delta> * (2 * ((2 * real n + 1) * Bd + 1)) = \<epsilon>" unfolding \<delta>_def
      by simp
    have "(2 * real n + 1) * Bd * \<delta> \<le> ((2 * real n + 1) * Bd + 1) * \<delta>" using d0
      by simp
    also have "\<dots> = \<epsilon> / 2" using eq by force
    finally show ?thesis .
  qed
  have "\<forall>\<^sub>F K :: nat in at_top. \<forall>i < n.
      primes_theta (cx a b n (i + 1) * real K) - primes_theta (cx a b n i * real K) \<le>
        ((b - a) / real n + \<delta>) * real K"
  proof -
    have "\<forall>i\<in>{..<n}. \<forall>\<^sub>F K :: nat in at_top.
        primes_theta (cx a b n (i + 1) * real K) - primes_theta (cx a b n i * real K) \<le>
          ((b - a) / real n + \<delta>) * real K"
    proof
      fix i assume i: "i \<in> {..<n}"
      have "0 \<le> cx a b n i" "0 \<le> cx a b n (i + 1)"
        using cx_ge[OF ab, of n i] cx_ge[OF ab, of n "i + 1"] a by linarith+
      hence "\<forall>\<^sub>F K :: nat in at_top. primes_theta (cx a b n (i + 1) * real K) -
        primes_theta (cx a b n i * real K)
          \<le> (cx a b n (i + 1) - cx a b n i + \<delta>) * real K" by (rule cell_upper[OF _ _ d0])
      thus "\<forall>\<^sub>F K :: nat in at_top. primes_theta (cx a b n (i + 1) * real K) -
        primes_theta (cx a b n i * real K)
          \<le> ((b - a) / real n + \<delta>) * real K" unfolding cx_succ_sub[OF n0] .
    qed
    hence "\<forall>\<^sub>F K :: nat in at_top. \<forall>i\<in>{..<n}.
        primes_theta (cx a b n (i + 1) * real K) - primes_theta (cx a b n i * real K) \<le>
          ((b - a) / real n + \<delta>) * real K"
      by (rule eventually_ball_finite[OF finite_lessThan])
    thus ?thesis by (rule eventually_mono) simp
  qed
  moreover have "\<forall>\<^sub>F K :: nat in at_top. (b - a - \<delta>) * real K \<le>
    primes_theta (b * real K) - primes_theta (a * real K)"
    by (rule cell_lower) (use a ab d0 in auto)
  ultimately show ?thesis
    using eventually_gt_at_top[of "0 :: nat"]
  proof (eventually_elim)
    case (elim K)
    have Kr: "0 < real K" using elim(3) by simp
    let ?s = "{p. p \<le> nat (floor (b * real K)) \<and> prime p \<and> a * real K < real p \<and>
      real p \<le> b * real K}"
    have fin: "finite ?s" by simp
    have seq: "?s = {p. prime p \<and> a * real K < real p \<and> real p \<le> b * real K}"
      by (auto intro: le_nat_floor)
    have tot: "(\<Sum> p \<in> ?s. ln (real p)) =
      primes_theta (b * real K) - primes_theta (a * real K)"
      unfolding seq by (rule sum_cell) (use a ab Kr in \<open>auto intro: mult_right_mono\<close>)
    have mem: "\<And>p. p \<in> ?s \<Longrightarrow> real p / real K \<in> {a<..b}"
      using Kr by (auto simp: less_divide_eq divide_le_eq)
    have maj: "(\<Sum> p \<in> ?s. (\<phi> (real p / real K) + Bd) * ln (real p)) \<le>
      (\<Sum> p \<in> ?s. cG \<phi> a b Bd n (real p / real K) * ln (real p))"
    proof (rule sum_mono)
      fix p assume p: "p \<in> ?s"
      have "\<phi> (real p / real K) + Bd \<le> cG \<phi> a b Bd n (real p / real K)"
        using ab' Bd B0 n0 mem[OF p] by (rule cG_bounds[THEN conjunct1])
      moreover have "0 \<le> ln (real p)" using p prime_ge_1_nat[of p] by (intro ln_ge_zero) auto
      ultimately show "(\<phi> (real p / real K) + Bd) * ln (real p) \<le>
        cG \<phi> a b Bd n (real p / real K) * ln (real p)"
        by (rule mult_right_mono)
    qed
    have cGsum: "(\<Sum> p \<in> ?s. cG \<phi> a b Bd n (real p / real K) * ln (real p)) \<le>
      (\<Sum> i < n. (cM \<phi> a b n i + Bd) * (((b - a) / real n + \<delta>) * real K))"
    proof -
      have "(\<Sum> p \<in> ?s. cG \<phi> a b Bd n (real p / real K) * ln (real p))
              = (\<Sum> i < n. (cM \<phi> a b n i + Bd) * (\<Sum> p \<in> {p \<in>
                ?s. real p / real K \<in> {cx a b n i<..cx a b n (i + 1)}}. ln (real p)))"
      proof -
        have "(\<Sum> p \<in> ?s. cG \<phi> a b Bd n (real p / real K) * ln (real p)) =
            (\<Sum> p \<in> ?s. \<Sum> i <
              n. indicator {cx a b n i<..cx a b n (i + 1)} (real p / real K) * (cM \<phi> a b n i +
              Bd) * ln (real p))"
          unfolding cG_def sum_distrib_right ..
        also have "\<dots> = (\<Sum> i < n. \<Sum> p \<in>
          ?s. indicator {cx a b n i<..cx a b n (i + 1)} (real p / real K) * (cM \<phi> a b n i +
          Bd) * ln (real p))"
          by (rule sum.swap)
        also have "\<dots> = (\<Sum> i < n. (cM \<phi> a b n i + Bd) * (\<Sum> p \<in> {p \<in>
          ?s. real p / real K \<in> {cx a b n i<..cx a b n (i + 1)}}. ln (real p)))"
        proof (rule sum.cong[OF refl])
          fix i assume "i \<in> {..<n}"
          have "(\<Sum> p \<in> ?s. indicator {cx a b n i<..cx a b n (i + 1)} (real p / real K) *
            (cM \<phi> a b n i + Bd) * ln (real p)) =
              (\<Sum> p \<in> ?s. if real p / real K \<in>
                {cx a b n i<..cx a b n (i + 1)} then (cM \<phi> a b n i + Bd) * ln (real p) else 0)"
            by (rule sum.cong[OF refl]) (simp add: indicator_def)
          also have "\<dots> = (\<Sum> p \<in> {p \<in> ?s. real p / real K \<in>
            {cx a b n i<..cx a b n (i + 1)}}. (cM \<phi> a b n i + Bd) * ln (real p))"
            by (rule sum.inter_filter[OF fin, symmetric])
          also have "\<dots> = (cM \<phi> a b n i + Bd) * (\<Sum> p \<in> {p \<in>
            ?s. real p / real K \<in> {cx a b n i<..cx a b n (i + 1)}}. ln (real p))"
            by (rule sum_distrib_left[symmetric])
          finally show "(\<Sum> p \<in> ?s. indicator {cx a b n i<..cx a b n (i + 1)} (real p /
            real K) * (cM \<phi> a b n i + Bd) * ln (real p)) =
              (cM \<phi> a b n i + Bd) * (\<Sum> p \<in> {p \<in> ?s. real p / real K \<in>
                {cx a b n i<..cx a b n (i + 1)}}. ln (real p))" .
        qed
        finally show ?thesis .
      qed
      also have "\<dots> \<le> (\<Sum> i <
        n. (cM \<phi> a b n i + Bd) * (((b - a) / real n + \<delta>) * real K))"
      proof (rule sum_mono, rule mult_left_mono)
        fix i assume i: "i \<in> {..<n}"
        show "0 \<le> cM \<phi> a b n i + Bd"
        proof -
          have "- Bd \<le> cM \<phi> a b n i"
            using Bd less_imp_le[OF ab'] n0 i[unfolded lessThan_iff] by (rule cM_ge)
          thus ?thesis by linarith
        qed
          \<comment> \<open>chained facts instead of @{text OF}: @{text OF} with the
            @{text "\<And>y"}-premise unifies higher-order and fails\<close>
        have "(\<Sum> p \<in> {p \<in> ?s. real p / real K \<in>
          {cx a b n i<..cx a b n (i + 1)}}. ln (real p))
                \<le> (\<Sum> p \<in> {p. prime p \<and> cx a b n i * real K < real p \<and>
                  real p \<le> cx a b n (i + 1) * real K}. ln (real p))"
        proof (rule sum_mono2)
          show "finite {p. prime p \<and> cx a b n i * real K < real p \<and>
            real p \<le> cx a b n (i + 1) * real K}"
            by (rule finite_subset[OF _ finite_primes_le[of "cx a b n (i + 1) * real K"]]) auto
          show "{p \<in> ?s. real p / real K \<in> {cx a b n i<..cx a b n (i + 1)}} \<subseteq>
              {p. prime p \<and> cx a b n i * real K < real p \<and>
                real p \<le> cx a b n (i + 1) * real K}"
            using Kr by (auto simp: less_divide_eq divide_le_eq)
          fix p assume "p \<in> {p. prime p \<and> cx a b n i * real K < real p \<and>
            real p \<le> cx a b n (i + 1) * real K} -
              {p \<in> ?s. real p / real K \<in> {cx a b n i<..cx a b n (i + 1)}}"
          hence "prime p" by simp
          thus "0 \<le> ln (real p)" using prime_ge_1_nat[of p] by (intro ln_ge_zero) auto
        qed
        also have "\<dots> = primes_theta (cx a b n (i + 1) * real K) - primes_theta (cx a b n i *
          real K)"
        proof (rule sum_cell)
          show "0 \<le> cx a b n i * real K" using cx_ge[OF ab, of n i] a Kr by auto
          show "cx a b n i * real K \<le> cx a b n (i + 1) * real K"
            using cx_mono[OF ab, of i "i + 1" n] Kr by simp
        qed
        also have "\<dots> \<le> ((b - a) / real n + \<delta>) * real K" using elim(1) i by auto
        finally show "(\<Sum> p \<in> {p \<in> ?s. real p / real K \<in>
          {cx a b n i<..cx a b n (i + 1)}}. ln (real p)) \<le>
          ((b - a) / real n + \<delta>) * real K" .
      qed
      finally show ?thesis .
    qed
    have split: "(\<Sum> p \<in> ?s. \<phi> (real p / real K) * ln (real p))
        = (\<Sum> p \<in> ?s. (\<phi> (real p / real K) + Bd) * ln (real p)) - Bd * (\<Sum> p \<in>
          ?s. ln (real p))"
      by (simp add: sum_subtractf sum_distrib_left sum.distrib algebra_simps)
    have split2: "(\<Sum> i < n. (cM \<phi> a b n i + Bd) * (((b - a) / real n + \<delta>) *
      real K))
        = interval_lebesgue_integral lborel (ereal a) (ereal b) (cG \<phi> a b Bd n) * real K +
          \<delta> * real K * T"
      unfolding integral_cG[OF ab' n0] T_def
    proof -
      have "(\<Sum> i < n. (cM \<phi> a b n i + Bd) * (((b - a) / real n + \<delta>) * real K)) =
          (\<Sum> i < n. (cM \<phi> a b n i + Bd) * ((b - a) / real n) * real K + \<delta> *
            real K * (cM \<phi> a b n i + Bd))"
        by (rule sum.cong[OF refl]) (rule split2_aux)
      also have "\<dots> = (\<Sum> i < n. (cM \<phi> a b n i + Bd) * ((b - a) / real n) * real K) +
        (\<Sum> i < n. \<delta> * real K * (cM \<phi> a b n i + Bd))"
        by (rule sum.distrib)
      also have "(\<Sum> i < n. (cM \<phi> a b n i + Bd) * ((b - a) / real n) * real K) =
        (\<Sum> i < n. (cM \<phi> a b n i + Bd) * ((b - a) / real n)) * real K"
        by (rule sum_distrib_right[symmetric])
      also have "(\<Sum> i < n. \<delta> * real K * (cM \<phi> a b n i + Bd)) =
        \<delta> * real K * (\<Sum> i < n. cM \<phi> a b n i + Bd)"
        by (rule sum_distrib_left[symmetric])
      finally show "(\<Sum> i < n. (cM \<phi> a b n i + Bd) * (((b - a) / real n + \<delta>) *
        real K)) =
          (\<Sum> i < n. (cM \<phi> a b n i + Bd) * ((b - a) / real n)) * real K + \<delta> *
            real K * (\<Sum> i < n. cM \<phi> a b n i + Bd)" .
    qed
    have "T \<le> real n * (2 * Bd)"
      unfolding T_def
    proof -
      have "(\<Sum> i < n. cM \<phi> a b n i + Bd) \<le> (\<Sum> i < n. 2 * Bd)"
      proof (rule sum_mono)
        fix i assume i: "i \<in> {..<n}"
        have "cM \<phi> a b n i \<le> Bd"
          using Bd B0 less_imp_le[OF ab'] n0 i[unfolded lessThan_iff] by (rule cM_le)
        thus "cM \<phi> a b n i + Bd \<le> 2 * Bd" by linarith
      qed
      thus "(\<Sum> i < n. cM \<phi> a b n i + Bd) \<le> real n * (2 * Bd)" by fastforce
    qed
    hence m1: "\<delta> * real K * T \<le> \<delta> * real K * (real n * (2 * Bd))"
      by (rule mult_left_mono) (use d0 Kr in simp)
    have m2: "Bd * ((b - a - \<delta>) * real K) \<le>
      Bd * (primes_theta (b * real K) - primes_theta (a * real K))"
      by (rule mult_left_mono[OF elim(2) B0])
    have m3: "interval_lebesgue_integral lborel (ereal a) (ereal b) (cG \<phi> a b Bd n) *
      real K \<le> (I + (b - a) * Bd + \<epsilon> / 2) * real K"
      by (rule mult_right_mono[OF less_imp_le[OF n1]]) (use Kr in simp)
    have m4: "(2 * real n + 1) * Bd * \<delta> * real K \<le> \<epsilon> / 2 * real K"
      by (rule mult_right_mono[OF dB]) (use Kr in simp)
    show ?case
      unfolding split tot I_def[symmetric]
      using maj cGsum split2 m1 m2 m3 m4
      by (simp only: algebra_simps) argo
      \<comment> \<open>@{text "\<Sum> \<phi> ln p \<le>
        (I + (b-a)B + \<epsilon>/2) K + \<delta> K n 2B - B (b - a - \<delta>) K =
        (I + \<epsilon>/2) K + (2n+1) B \<delta> K \<le> (I + \<epsilon>) K"}\<close>
  qed
qed

text \<open>Inner range, variable @{text "x = K/p"}: substitute @{text "y = 1/x"} in the outer
  bound.\<close>
theorem inner_prime_sum_bound:
  assumes M: "3 < M" and Bd: "\<And>x. x \<in> {3..real M} \<Longrightarrow>
    \<bar>f x\<bar> \<le> Bd" and D: "countable D"
    and cont: "\<And>x. x \<in> {3<..<real M} \<Longrightarrow> x \<notin> D \<Longrightarrow>
      isCont f x" and e: "0 < \<epsilon>"
  shows "\<forall>\<^sub>F K in at_top.
    (\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and>
      3 * p \<le> K}. real p * f (real K / real p) * ln (real p))
      \<le> (interval_lebesgue_integral lborel (ereal 3) (ereal (real M)) (\<lambda>x. f x /
        x ^ 3) + \<epsilon>) * real K ^ 2"
proof -
  have Mr: "3 < real M" using M by simp
  have M0: "0 < real M" using Mr by simp
  let ?\<phi> = "\<lambda>y. y * f (1 / y)"
  have B0: "0 \<le> Bd" using Bd[of 3] Mr by auto
  have phiB: "\<And>y. y \<in> {1 / real M..1 / 3} \<Longrightarrow> \<bar>?\<phi> y\<bar> \<le> Bd"
  proof -
    fix y assume y: "y \<in> {1 / real M..1 / 3}"
    have iM: "0 < 1 / real M" using M0 by simp
    have "1 / real M \<le> y" using y by simp
    hence y0: "0 < y" using iM by linarith
    have y1: "y \<le> 1" using y by simp
    have "3 \<le> 1 / y" using y y0 by (simp add: le_divide_eq)
    moreover have "1 / y \<le> real M" using y y0 M0 by (simp add: field_simps)
    ultimately have fb: "\<bar>f (1 / y)\<bar> \<le> Bd" using Bd by simp
    have "\<bar>y * f (1 / y)\<bar> = y * \<bar>f (1 / y)\<bar>" using y0 by (simp add: abs_mult)
    also have "\<dots> \<le> 1 * Bd" by (rule mult_mono[OF y1 fb]) (use B0 in simp_all)
    finally show "\<bar>?\<phi> y\<bar> \<le> Bd" by simp
  qed
  have phiC: "\<And>y. y \<in> {1 / real M<..<1 / 3} \<Longrightarrow>
    y \<notin> (\<lambda>x. 1 / x) ` D \<Longrightarrow> isCont ?\<phi> y"
  proof -
    fix y assume y: "y \<in> {1 / real M<..<1 / 3}" and yD: "y \<notin> (\<lambda>x. 1 / x) ` D"
    have iM: "0 < 1 / real M" using M0 by simp
    have "1 / real M < y" using y by simp
    hence y0: "0 < y" using iM by linarith
    have "3 < 1 / y" using y y0 by (simp add: less_divide_eq)
    moreover have "1 / y < real M" using y y0 M0 by (simp add: field_simps)
    moreover have "1 / y \<notin> D"
    proof
      assume "1 / y \<in> D"
      hence "1 / (1 / y) \<in> (\<lambda>x. 1 / x) ` D" by (rule imageI)
      thus False using yD by simp
    qed
    ultimately have c2: "isCont f (1 / y)" using cont by simp
    have c1: "isCont (\<lambda>y. 1 / y) y" using y0 by (auto intro: continuous_intros)
    have "isCont (\<lambda>y. f (1 / y)) y" using isCont_o2[OF c1 c2] by simp
    thus "isCont ?\<phi> y" by (auto intro: continuous_intros)
  qed
  have ho: "\<forall>\<^sub>F K in at_top.
      (\<Sum> p \<in> {p. p \<le> nat (floor (1 / 3 * real K)) \<and> prime p \<and>
        1 / real M * real K < real p \<and> real p \<le> 1 / 3 * real K}.
          ?\<phi> (real p / real K) * ln (real p))
        \<le> (interval_lebesgue_integral lborel (ereal (1 / real M)) (ereal (1 / 3)) ?\<phi> +
          \<epsilon>) * real K"
    by (rule outer_prime_sum_bound[OF _ _ phiB countable_image[OF D] phiC e]) (use M0 Mr in
      \<open>auto simp: divide_le_eq\<close>)
  have subst: "interval_lebesgue_integral lborel (ereal (1 / real M)) (ereal (1 / 3)) ?\<phi>
      = interval_lebesgue_integral lborel (ereal 3) (ereal (real M)) (\<lambda>x. f x / x ^ 3)"
  proof -
    have m: "(\<lambda>x. indicator {3<..<real M} x * f x) \<in> borel_measurable borel"
      using D cont by (rule phi_measurable)
    show ?thesis using less_imp_le[OF Mr] m Bd by (rule integral_inv_subst)
  qed
  show ?thesis
    using ho eventually_gt_at_top[of "0 :: nat"]
  proof (eventually_elim)
    case (elim K)
    have Kr: "0 < real K" using elim(2) by simp
    have seq: "{p. p \<le> nat (floor (1 / 3 * real K)) \<and> prime p \<and>
      1 / real M * real K < real p \<and> real p \<le> 1 / 3 * real K}
             = {p. p \<le> K \<and> prime p \<and> K < p * M \<and> 3 * p \<le> K}"
    proof (intro equalityI subsetI)
      fix p assume "p \<in> {p. p \<le> nat (floor (1 / 3 * real K)) \<and> prime p \<and>
        1 / real M * real K < real p \<and> real p \<le> 1 / 3 * real K}"
      hence p: "prime p" "1 / real M * real K < real p" "real p \<le> 1 / 3 * real K" by auto
      have "real K < real p * real M" using p(2) M0 by (simp add: field_simps)
      hence b1: "K < p * M" by (metis of_nat_mult of_nat_less_iff)
      have "3 * real p \<le> real K" using p(3) by simp
      hence b2: "3 * p \<le> K" by simp
      show "p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and> 3 * p \<le> K}"
        using p(1) b1 b2 by simp
    next
      fix p assume "p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and> 3 * p \<le> K}"
      hence p: "prime p" "K < p * M" "3 * p \<le> K" by auto
      have a1: "real K < real p * real M" using p(2) by (metis of_nat_mult of_nat_less_iff)
      have a2: "3 * real p \<le> real K" using p(3) by simp
      have c1: "1 / real M * real K < real p" using a1 M0 by (simp add: field_simps)
      have c2: "real p \<le> 1 / 3 * real K" using a2 by simp
      have c3: "p \<le> nat (floor (1 / 3 * real K))" using c2 by (rule le_nat_floor)
      show "p \<in> {p. p \<le> nat (floor (1 / 3 * real K)) \<and> prime p \<and>
        1 / real M * real K < real p \<and> real p \<le> 1 / 3 * real K}"
        using p(1) c1 c2 c3 by simp
    qed
    have trm: "\<And>p. prime p \<Longrightarrow>
      real p * f (real K / real p) * ln (real p) =
      real K * (?\<phi> (real p / real K) * ln (real p))"
    proof -
      fix p :: nat assume p: "prime p"
      have e1: "1 / (real p / real K) = real K / real p" by simp
      have e2: "real K * (real p / real K) = real p" using Kr by simp
      show "real p * f (real K / real p) * ln (real p) =
        real K * (?\<phi> (real p / real K) * ln (real p))"
        unfolding e1 using e2 by (auto simp: mult.assoc[symmetric])
    qed
    have "(\<Sum> p \<in> {p. p \<le> K \<and> prime p \<and> K < p * M \<and>
      3 * p \<le> K}. real p * f (real K / real p) * ln (real p))
          = real K * (\<Sum> p \<in> {p. p \<le> nat (floor (1 / 3 * real K)) \<and> prime p \<and>
            1 / real M * real K < real p \<and> real p \<le> 1 / 3 * real K}.
                ?\<phi> (real p / real K) * ln (real p))"
      unfolding seq sum_distrib_left
      by (rule sum.cong[OF refl]) (rule trm, simp)
      \<comment> \<open>by rule, not simp: simp normalises @{text "1/(p/K)"} back to @{text "K/p"}
        and loops\<close>
    also have "\<dots> \<le> real K * ((interval_lebesgue_integral lborel (ereal (1 /
      real M)) (ereal (1 / 3)) ?\<phi> + \<epsilon>) * real K)"
      by (rule mult_left_mono[OF elim(1)]) (use Kr in simp)
    finally show ?case unfolding subst
      by (simp add: power2_eq_square mult_ac)
  qed
qed

end
