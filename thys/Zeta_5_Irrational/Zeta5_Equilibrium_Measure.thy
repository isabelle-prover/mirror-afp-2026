(*  Title:   Zeta5_Equilibrium_Measure.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Equilibrium_Measure
  imports Zeta5_Asymptotics "HOL-Complex_Analysis.Complex_Analysis"
    "HOL-Decision_Procs.Approximation"
begin

section \<open>The comparison measure \<open>\<rho>\<close> and its logarithmic potential\<close>

text \<open>Appendix A of the paper: the measure \<open>\<rho> =
  \<Sum> c\<^sub>j \<omega>\<^sub>[\<^sub>a\<^sub>j\<^sub>,\<^sub>b\<^sub>j\<^sub>]\<close> of Table
  1 as a single density, its
  logarithmic potential and energy in closed form ((A.1), (A.2)), the analytic half of the potential
  inequality (A.9) (the tail \<open>[2, \<infinity>)\<close>),
    and the bounds on the mass of short intervals used in
  Section 6.  Lean theories @{text AppendixA}, @{text Lemma61}, @{text Lemma61Pot}.\<close>
(* NOTE: HOL-Complex_Analysis is part of the Zeta5_Base heap (ROOT), so importing it here is free;
   it provides Cauchy_integral_circlepath for circle_log_gt. *)

subsection \<open>Table 1\<close>

text \<open>@{text "\<Sum> c_j = 37/40 \<cdot> 10^1^2"}: the mass of @{text \<rho>} is
  @{text \<lambda>}.  Trivial (simp/eval).\<close>
lemma table1_sum_c: "(\<Sum> e \<leftarrow> table1. snd (snd e)) = 37 * 10 ^ 12 div 40"
  by (simp add: table1_def)

text \<open>Nesting @{text "0 < a_1_6 < \<cdots> < a_1 < b_1 < \<cdots> < b_1_6 < 2"} and
  @{text "b_j - a_j > 1/225"}.  Trivial.\<close>
lemma table1_nested:
  "sorted_wrt (\<lambda>x y. y < x) (map fst table1) \<and>
    sorted_wrt (<) (map (fst \<circ> snd) table1) \<and>
   (\<forall>e \<in> set table1. 0 < fst e \<and> fst e < fst (snd e) \<and>
     fst (snd e) < 2 * 10 ^ 12 \<and>
                     10 ^ 12 < 225 * (fst (snd e) - fst e))"
  by (simp add: table1_def)


lemma sum_list_dens_measurable [measurable]:
  "(\<lambda>t. \<Sum> e \<leftarrow> xs. tC e * arcsine_dens (tA e) (tB e) t) \<in>
    borel_measurable borel"
  by (induction xs) auto

lemma sum_list_map_zero: "(\<And>e. e \<in> set xs \<Longrightarrow> f e = 0) \<Longrightarrow>
  (\<Sum> e \<leftarrow> xs. f e) = (0 :: real)"
  by (induction xs) auto

lemma nn_integral_sum_list_dens:
  assumes "\<forall>e \<in> set xs. 0 \<le> tC e \<and> tA e < tB e"
  shows "(\<integral>\<^sup>+ t. ennreal (\<Sum> e \<leftarrow> xs. tC e *
    arcsine_dens (tA e) (tB e) t) \<partial>lborel)
           = ennreal (\<Sum> e \<leftarrow> xs. tC e)"
  using assms
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons e xs)
  have c: "0 \<le> tC e" "tA e < tB e" using Cons.prems by auto
  have r0: "0 \<le> (\<Sum> e \<leftarrow> xs. tC e * arcsine_dens (tA e) (tB e) t)" for t
    using Cons.prems by (intro sum_list_nonneg) (auto intro!: mult_nonneg_nonneg
      arcsine_dens_nonneg)
  have s0: "0 \<le> (\<Sum> e \<leftarrow> xs. tC e)" using Cons.prems
    by (intro sum_list_nonneg) auto
  have "(\<integral>\<^sup>+ t. ennreal (\<Sum> e' \<leftarrow> e # xs. tC e' *
    arcsine_dens (tA e') (tB e') t) \<partial>lborel)
      = (\<integral>\<^sup>+ t. ennreal (tC e) * ennreal (arcsine_dens (tA e) (tB e) t)
                + ennreal (\<Sum> e \<leftarrow> xs. tC e *
                  arcsine_dens (tA e) (tB e) t) \<partial>lborel)"
    using c r0 by (intro nn_integral_cong) (simp add: ennreal_plus[symmetric] ennreal_mult
      arcsine_dens_nonneg)
  also have "\<dots> = ennreal (tC e) * (\<integral>\<^sup>+ t. ennreal (arcsine_dens (tA e) (tB e)
    t) \<partial>lborel)
                  + (\<integral>\<^sup>+ t. ennreal (\<Sum> e \<leftarrow> xs. tC e *
                    arcsine_dens (tA e) (tB e) t) \<partial>lborel)"
    by (subst nn_integral_add) (auto simp: nn_integral_cmult)
  also have "\<dots> = ennreal (tC e) + ennreal (\<Sum> e \<leftarrow> xs. tC e)"
    using Cons by (simp add: arcsine_dens_integral[OF c(2)])
  also have "\<dots> = ennreal (\<Sum> e' \<leftarrow> e # xs. tC e')" using c s0
    by (simp add: ennreal_plus)
  finally show ?case .
qed

lemma table1_props: "\<forall>e \<in> set table1. 0 \<le> tC e \<and> tA e < tB e \<and>
  0 < tA e \<and> tB e < 2"
  by (simp add: table1_def tA_def tB_def tC_def)

lemma table1_sum_tC: "(\<Sum> e \<leftarrow> table1. tC e) = lam_r"
  by (simp add: table1_def tC_def lam_r_def)

theorem rho_univ: "emeasure rho UNIV = ennreal lam_r"
proof -
  have "emeasure rho UNIV = (\<integral>\<^sup>+ t. ennreal (\<Sum> e \<leftarrow> table1. tC e *
    arcsine_dens (tA e) (tB e) t) \<partial>lborel)"
    unfolding rho_def by (subst emeasure_density) auto
  also have "\<dots> = ennreal lam_r"
    using table1_props by (subst nn_integral_sum_list_dens) (auto simp: table1_sum_tC)
  finally show ?thesis .
qed

theorem rho_compl: "emeasure rho (- {0<..<2}) = 0"
proof -
  have z: "(\<Sum> e \<leftarrow> table1. tC e * arcsine_dens (tA e) (tB e) t) = 0"
    if t: "t \<notin> {0<..<2}" for t
  proof (rule sum_list_map_zero)
    fix e assume e: "e \<in> set table1"
    have "\<not> (tA e < t \<and> t < tB e)" using table1_props e t by fastforce
    thus "tC e * arcsine_dens (tA e) (tB e) t = 0" by (auto simp: arcsine_dens_def)
  qed
  have "emeasure rho (- {0<..<2})
      = (\<integral>\<^sup>+ t. ennreal (\<Sum> e \<leftarrow> table1. tC e *
        arcsine_dens (tA e) (tB e) t) * indicator (- {0<..<2}) t \<partial>lborel)"
    unfolding rho_def by (subst emeasure_density) auto
  also have "\<dots> = (\<integral>\<^sup>+ t. 0 \<partial>lborel)"
  proof (subst nn_integral_cong[where v = "\<lambda>t. 0"])
    fix t :: real
    show "ennreal (\<Sum> e \<leftarrow> table1. tC e * arcsine_dens (tA e) (tB e) t) *
      indicator (- {0<..<2}) t = 0"
      by (cases "t \<in> {0<..<2}") (simp_all add: z)
  qed simp
  finally show ?thesis by simp
qed

text \<open>(A.2): @{text "I(\<rho>) = \<Sum>_j (S_j^2 - S_{j-1}^2) log((b_j - a_j)/4)"} (nesting
  makes the @{text j}-th
  potential constant on every earlier interval).\<close>
text \<open>The sixteen arcsine potentials @{text "U_k"} and their constant values @{text "L_k"} on
  their intervals.\<close>
definition Uk :: "nat \<Rightarrow> real \<Rightarrow> real" where "Uk k t =
  logPot (arcsine (tA (table1 ! k)) (tB (table1 ! k))) t"
definition Lk :: "nat \<Rightarrow> real" where "Lk k =
  ln ((tB (table1 ! k) - tA (table1 ! k)) / 4)"
definition cK :: "nat \<Rightarrow> real" where "cK k = tC (table1 ! k)"

lemma table1_nth: "k < 16 \<Longrightarrow> 0 < tA (table1 ! k) \<and>
  tA (table1 ! k) < tB (table1 ! k) \<and> tB (table1 ! k) < 2 \<and> 0 \<le> cK k"
proof -
  assume k: "k < 16"
  have l: "length table1 = 16" by (simp add: table1_def)
  have m: "table1 ! k \<in> set table1" using nth_mem[of k table1] k l by simp
  show ?thesis using table1_props m unfolding cK_def by blast
qed

lemma table1_nested_nth: "j \<le> k \<Longrightarrow> k < 16 \<Longrightarrow>
  tA (table1 ! k) \<le> tA (table1 ! j) \<and> tB (table1 ! j) \<le> tB (table1 ! k)"
proof -
  assume jk: "j \<le> k" and k: "k < 16"
  have l: "length table1 = 16" by (simp add: table1_def)
  have s1: "sorted_wrt (\<lambda>x y. y < x) (map fst table1)"
    using table1_nested
    by meson
  have s2: "sorted_wrt (<) (map (fst \<circ> snd) table1)"
    using table1_nested
    by meson
  show ?thesis
  proof (cases "j = k")
    case True
    thus ?thesis
      by simp
  next
    case False
    hence jk': "j < k" using jk
      by linarith
    have "fst (table1 ! k) < fst (table1 ! j)" using sorted_wrt_nth_less[OF s1 jk'] k l
      using jk'
      by (simp add: l)
    moreover have "fst (snd (table1 ! j)) < fst (snd (table1 ! k))"
      using sorted_wrt_nth_less[OF s2 jk'] k l
      using jk'
      by (simp add: l)
    ultimately show ?thesis unfolding tA_def tB_def
      by simp
  qed
qed

lemma Uk_eq: "k < 16 \<Longrightarrow> Uk k t = (if tA (table1 ! k) \<le> t \<and>
  t \<le> tB (table1 ! k) then Lk k
     else ln ((\<bar>t - (tA (table1 ! k) + tB (table1 ! k)) / 2\<bar> + sqrt ((t -
       tA (table1 ! k)) * (t - tB (table1 ! k)))) / 2))"
  unfolding Uk_def Lk_def using table1_nth by (intro arcsine_potential) simp

lemma Uk_const: "k < 16 \<Longrightarrow> tA (table1 ! k) \<le> t \<Longrightarrow>
  t \<le> tB (table1 ! k) \<Longrightarrow> Uk k t = Lk k"
  by (simp add: Uk_eq)

lemma Uk_bounds: "k < 16 \<Longrightarrow> 0 < t \<Longrightarrow> t < 2 \<Longrightarrow>
  Lk k \<le> Uk k t \<and> Uk k t \<le> ln 2"
proof -
  assume k: "k < 16" and t0: "0 < t" and t2: "t < 2"
  define a where "a = tA (table1 ! k)"
  define b where "b = tB (table1 ! k)"
  have ab1: "0 < a" using table1_nth[OF k] unfolding a_def b_def
    by blast
  have ab2: "a < b" using table1_nth[OF k] unfolding a_def b_def
    by blast
  have ab3: "b < 2" using table1_nth[OF k] unfolding a_def b_def
    by blast
  note ab = ab1 ab2 ab3
  have L: "Lk k = ln ((b - a) / 4)" unfolding Lk_def a_def b_def
    by meson
  have ba: "0 < (b - a) / 4" using ab
    by simp
  have L2: "Lk k \<le> ln 2" unfolding L using ab ba ln_le_cancel_iff[of "(b - a) / 4" 2]
    by simp
  show ?thesis
  proof (cases "a \<le> t \<and> t \<le> b")
    case True
    have "Uk k t = Lk k" using Uk_const[OF k] True unfolding a_def b_def
      by blast
    thus ?thesis using L2
      by auto
  next
    case False
    define X where "X = (\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2"
    have U: "Uk k t = ln X" using Uk_eq[OF k, of t] False unfolding X_def a_def b_def
      by presburger
    have far: "(b - a) / 2 \<le> \<bar>t - (a + b) / 2\<bar>" using False
      by argo
    have near: "\<bar>t - (a + b) / 2\<bar> < 2" using ab t0 t2
      by argo
    have pr: "(t - a) * (t - b) = (t - (a + b) / 2) ^ 2 - ((b - a) / 2) ^ 2"
      by (simp add: power2_eq_square field_simps)
    have p0: "0 \<le> (t - a) * (t - b)"
    proof (cases "t < a")
      case True
      thus ?thesis using ab
        by (fastforce intro: mult_nonpos_nonpos)
    next
      case False
      hence "b < t" using \<open>\<not> (a \<le> t \<and> t \<le> b)\<close>
        by linarith
      thus ?thesis using ab
        by (auto intro: mult_nonneg_nonneg)
    qed
    have sq: "sqrt ((t - a) * (t - b)) \<le> \<bar>t - (a + b) / 2\<bar>"
      using real_sqrt_le_mono[of "(t - a) * (t - b)" "(t - (a + b) / 2) ^ 2"] pr real_sqrt_abs
      by simp
    have "(b - a) / 4 \<le> X" unfolding X_def using far real_sqrt_ge_zero[OF p0]
      by argo
    moreover have "X \<le> 2" unfolding X_def using sq near
      by simp
    ultimately show ?thesis unfolding U L using ba ln_le_cancel_iff
      by simp
  qed
qed

lemma Uk_measurable [measurable]: "k < 16 \<Longrightarrow> Uk k \<in> borel_measurable borel"
proof -
  assume k: "k < 16"
  have e: "Uk k = (\<lambda>t. if tA (table1 ! k) \<le> t \<and>
    t \<le> tB (table1 ! k) then Lk k else ln ((\<bar>t - (tA (table1 ! k) + tB (table1 ! k)) /
    2\<bar> + sqrt ((t - tA (table1 ! k)) * (t - tB (table1 ! k)))) / 2))" using Uk_eq[OF k]
    by (simp add: fun_eq_iff)
  show ?thesis unfolding e by measurable
qed

lemma Uk_integrable: "j < 16 \<Longrightarrow> k < 16 \<Longrightarrow>
  integrable (arcsine (tA (table1 ! j)) (tB (table1 ! j))) (Uk k)"
proof -
  assume j: "j < 16" and k: "k < 16"
  define a where "a = tA (table1 ! j)"
  define b where "b = tB (table1 ! j)"
  have ab: "0 < a" "a < b" "b < 2" using table1_nth[OF j] unfolding a_def b_def by auto
  have pw: "norm (Uk k x) \<le> \<bar>Lk k\<bar> + ln 2" if "a < x" "x < b" for x
  proof -
    have x0: "0 < x" "x < 2" using that ab by auto
    have bb: "Lk k \<le> Uk k x" "Uk k x \<le> ln 2" using Uk_bounds[OF k x0] by auto
    show ?thesis using bb ln_gt_zero[of "2::real"] unfolding real_norm_def
      by linarith
  qed
  have bd: "AE x in arcsine a b. norm (Uk k x) \<le> \<bar>Lk k\<bar> + ln 2"
    using arcsine_AE[of a b] pw
    by (fast elim: AE_mp)
  have mU: "Uk k \<in> borel_measurable (arcsine a b)" using Uk_measurable[OF k]
    unfolding arcsine_def by simp
  show ?thesis using finite_measure.integrable_const_bound[OF arcsine_finite[OF ab(2)] bd mU]
    unfolding a_def b_def .
qed


text \<open>@{text "\<integral> U_k d\<omega>_j = L_{max(j,k)}"}:
  by nesting the outer potential is constant on the inner interval; otherwise swap (Fubini).\<close>
lemma Uk_integral:
  assumes "j < 16" "k < 16"
  shows "integral\<^sup>L (arcsine (tA (table1 ! j)) (tB (table1 ! j))) (Uk k) = Lk (max j k)"
proof (cases "j \<le> k")
  case True
  have const: "AE t in arcsine (tA (table1 ! j)) (tB (table1 ! j)). Uk k t = Lk k"
    using arcsine_AE[of "tA (table1 ! j)" "tB (table1 ! j)"] table1_nested_nth[OF True assms(2)]
      Uk_const[OF assms(2)]
    by (force elim: AE_mp)
  show ?thesis
    using integral_cong_AE[OF _ _ const] Uk_measurable[OF assms(2)] arcsine_univ[of "tA (table1 !
      j)" "tB (table1 ! j)"] table1_nth[OF assms(1)] max_absorb2[OF True]
    unfolding arcsine_def
    by (simp add: measure_def)
next
  case False
  have bj: "tA (table1 ! j) < tB (table1 ! j)" "0 < tA (table1 ! j)" "tB (table1 ! j) < 2"
    using table1_nth[OF assms(1)] by auto
  have bk: "tA (table1 ! k) < tB (table1 ! k)" "0 < tA (table1 ! k)" "tB (table1 ! k) < 2"
    using table1_nth[OF assms(2)] by auto
  have bnd: "Lk k \<le> logPot (arcsine (tA (table1 ! k)) (tB (table1 ! k))) x" if "0 < x" "x < 2"
    for x
    using Uk_bounds[OF assms(2) that] unfolding Uk_def by simp
  have swap: "integral\<^sup>L (arcsine (tA (table1 ! j)) (tB (table1 ! j))) (Uk k) =
    integral\<^sup>L (arcsine (tA (table1 ! k)) (tB (table1 ! k))) (Uk j)"
    unfolding Uk_def[abs_def] using arcsine_swap[OF bj bk bnd]
    by simp
  have kj: "k \<le> j" using False by simp
  have const: "AE t in arcsine (tA (table1 ! k)) (tB (table1 ! k)). Uk j t = Lk j"
    using arcsine_AE[of "tA (table1 ! k)" "tB (table1 ! k)"] table1_nested_nth[OF kj assms(1)]
      Uk_const[OF assms(1)]
    by (force elim: AE_mp)
  have "integral\<^sup>L (arcsine (tA (table1 ! k)) (tB (table1 ! k))) (Uk j) = Lk j"
    using integral_cong_AE[OF _ _ const] Uk_measurable[OF assms(1)] arcsine_univ[of "tA (table1 !
      k)" "tB (table1 ! k)"] table1_nth[OF assms(2)]
    unfolding arcsine_def
    by (simp add: measure_def)
  thus ?thesis using swap max_absorb1[OF kj]
    by simp
qed

text \<open>@{text "U^\<rho>(t) = \<Sum>_k c_k U_k(t)"} and
  @{text "I(\<rho>) = \<Sum>_{j,k} c_j c_k L_{max(j,k)}"}.\<close>
lemma logPot_rho: "logPot rho t = (\<Sum> k < 16. cK k * Uk k t)"
proof -
  have nnr0: "0 \<le> (\<Sum> e \<leftarrow> table1. tC e * arcsine_dens (tA e) (tB e) u)" for u
    using table1_props
    by (fastforce intro: sum_list_nonneg mult_nonneg_nonneg arcsine_dens_nonneg)
  have nnr: "AE u in lborel. 0 \<le> (\<Sum> e \<leftarrow> table1. tC e *
    arcsine_dens (tA e) (tB e) u)" using nnr0 by simp
  have "logPot rho t = (\<integral> u. (\<Sum> e \<leftarrow> table1. tC e *
    arcsine_dens (tA e) (tB e) u) * ln \<bar>t - u\<bar> \<partial>lborel)"
    unfolding logPot_def rho_def
    using nnr0 integral_density[of "\<lambda>u. ln \<bar>t -
      u\<bar>" lborel "(\<lambda>u. \<Sum> e \<leftarrow> table1. tC e *
      arcsine_dens (tA e) (tB e) u)"] dens_ln_meas[of t] sum_list_dens_measurable
    nnr
    by simp
  also have "\<dots> = (\<Sum> k < 16. cK k *
    (\<integral> u. arcsine_dens (tA (table1 ! k)) (tB (table1 ! k)) u * ln \<bar>t -
    u\<bar> \<partial>lborel))"
  proof -
    have l: "length table1 = 16" by (simp add: table1_def)
    have sl: "(\<Sum> e \<leftarrow> table1. tC e * arcsine_dens (tA e) (tB e) u) = (\<Sum> k <
      16. cK k * arcsine_dens (tA (table1 ! k)) (tB (table1 ! k)) u)" for u
      using sum_list_sum_nth[of "map (\<lambda>e. tC e * arcsine_dens (tA e) (tB e) u) table1"] l
        unfolding cK_def
      by (simp add: atLeast0LessThan)
    have ik: "integrable lborel (\<lambda>u. cK k *
      (arcsine_dens (tA (table1 ! k)) (tB (table1 ! k)) u * ln \<bar>t - u\<bar>))"
      if "k \<in> {..<16}" for k
      using dens_ln_integrable[of "tA (table1 ! k)" "tB (table1 ! k)" t] table1_nth[of k] that
      by fast
    show ?thesis unfolding sl sum_distrib_right
      using Bochner_Integration.integral_sum[of "{..<16}" lborel "\<lambda>k u. cK k *
      (arcsine_dens (tA (table1 ! k)) (tB (table1 ! k)) u * ln \<bar>t - u\<bar>)", OF ik]
      by (fastforce simp: mult.assoc)
  qed
  also have "\<dots> = (\<Sum> k < 16. cK k * Uk k t)"
    by (simp add: Uk_def dens_ln_integral)
  finally show ?thesis .
qed

lemma dens_Uk_integrable:
  assumes j: "j < 16" and k: "k < 16"
  shows "integrable lborel (\<lambda>t. arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t *
    Uk k t)"
proof -
  have md: "(\<lambda>t. arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t) \<in>
    borel_measurable borel" unfolding arcsine_dens_def by measurable
  have nn: "AE t in lborel. 0 \<le> arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t"
    by (simp add: arcsine_dens_def)
  show ?thesis using Uk_integrable[OF j k] integrable_density[of "Uk k" lborel "arcsine_dens (tA
    (table1 ! j)) (tB (table1 ! j))"] Uk_measurable[OF k] md nn
    unfolding arcsine_def
    by auto
qed

lemma dens_Uk_integral:
  assumes j: "j < 16" and k: "k < 16"
  shows "(\<integral> t. arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t *
    Uk k t \<partial>lborel) = Lk (max j k)"
proof -
  have md: "(\<lambda>t. arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t) \<in>
    borel_measurable borel" unfolding arcsine_dens_def by measurable
  have nn: "AE t in lborel. 0 \<le> arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t"
    by (simp add: arcsine_dens_def)
  show ?thesis using Uk_integral[OF j k] integral_density[of "Uk k" lborel "arcsine_dens (tA (table1
    ! j)) (tB (table1 ! j))"] Uk_measurable[OF k] md nn
    unfolding arcsine_def
    by force
qed

lemma logEnergy_rho: "logEnergy rho = (\<Sum> j < 16. \<Sum> k < 16. cK j * cK k * Lk (max j k))"
proof -
  have fe: "logPot rho = (\<lambda>t. \<Sum> k < 16. cK k * Uk k t)" by (rule ext, rule logPot_rho)
  have mf: "(\<lambda>t. \<Sum> k < 16. cK k * Uk k t) \<in> borel_measurable borel"
    by (force intro: borel_measurable_sum borel_measurable_times Uk_measurable)
  have nnr0: "0 \<le> (\<Sum> e \<leftarrow> table1. tC e * arcsine_dens (tA e) (tB e) u)" for u
    using table1_props by (fastforce intro: sum_list_nonneg mult_nonneg_nonneg arcsine_dens_nonneg)
  have nnr: "AE u in lborel. 0 \<le> (\<Sum> e \<leftarrow> table1. tC e *
    arcsine_dens (tA e) (tB e) u)" using nnr0 by simp
  have A: "logEnergy rho = (\<integral> t. (\<Sum> e \<leftarrow> table1. tC e *
    arcsine_dens (tA e) (tB e) t) * (\<Sum> k < 16. cK k * Uk k t) \<partial>lborel)"
    unfolding logEnergy_def fe unfolding rho_def
      using integral_density[of "\<lambda>t. \<Sum> k <
      16. cK k * Uk k t" lborel "(\<lambda>u. \<Sum> e \<leftarrow> table1. tC e *
      arcsine_dens (tA e) (tB e) u)"] mf sum_list_dens_measurable nnr
    by fastforce
  have l: "length table1 = 16" by (simp add: table1_def)
  have sl: "(\<Sum> e \<leftarrow> table1. tC e * arcsine_dens (tA e) (tB e) t) = (\<Sum> j <
    16. cK j * arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t)" for t
    using sum_list_sum_nth[of "map (\<lambda>e. tC e * arcsine_dens (tA e) (tB e) t) table1"] l
      unfolding cK_def
    by (simp add: atLeast0LessThan)
  have B: "(\<Sum> e \<leftarrow> table1. tC e * arcsine_dens (tA e) (tB e) t) * (\<Sum> k <
    16. cK k * Uk k t) = (\<Sum> j < 16. \<Sum> k <
    16. cK j * cK k * (arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t * Uk k t))" for t
    unfolding sl sum_product
    by (simp add: algebra_simps)
  have C: "(\<integral> t. (\<Sum> j < 16. \<Sum> k <
    16. cK j * cK k * (arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t *
    Uk k t)) \<partial>lborel) = (\<Sum> j < 16. \<Sum> k < 16. cK j * cK k * Lk (max j k))"
  proof -
    have ij: "integrable lborel (\<lambda>t. \<Sum> k <
      16. cK j * cK k * (arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t * Uk k t))"
      if "j \<in> {..<16}" for j
      using dens_Uk_integrable that
      by (fast intro: Bochner_Integration.integrable_sum integrable_mult_right)
    have c2: "(\<integral> t. (\<Sum> k <
      16. cK j * cK k * (arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t *
      Uk k t)) \<partial>lborel) = (\<Sum> k < 16. cK j * cK k * Lk (max j k))"
      if "j \<in> {..<16}" for j
      using Bochner_Integration.integral_sum[of "{..<16}" lborel "\<lambda>k t. cK j * cK k *
        (arcsine_dens (tA (table1 ! j)) (tB (table1 ! j)) t *
        Uk k t)"] dens_Uk_integrable dens_Uk_integral that
      by auto
    show ?thesis using Bochner_Integration.integral_sum[of "{..<16}" lborel, OF ij] c2
      by fastforce
  qed
  show ?thesis unfolding A B C ..
qed

lemma sum_max_regroup:
  fixes c L :: "nat \<Rightarrow> real"
  shows "(\<Sum> j < n. \<Sum> k < n. c j * c k * L (max j k)) = (\<Sum> j < n. ((\<Sum> i \<le>
    j. c i) ^ 2 - (\<Sum> i < j. c i) ^ 2) * L j)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  define S where "S = (\<Sum> i < n. c i)"
  have g: "(\<Sum> j < Suc n. \<Sum> k < Suc n. F j k) = (\<Sum> j < n. \<Sum> k <
    n. F j k) + (\<Sum> j < n. F j n) + (\<Sum> k < n. F n k) + F n n"
    for F :: "nat \<Rightarrow> nat \<Rightarrow> real"
    by (simp add: sum.distrib)
  have r1a: "(\<Sum> j < n. c j * c n * L (max j n)) = (\<Sum> j < n. c n * L n * c j)"
  proof (rule sum.cong[OF refl])
    fix j assume "j \<in> {..<n}"
    thus "c j * c n * L (max j n) = c n * L n * c j"
      by simp
  qed
  have r2a: "(\<Sum> k < n. c n * c k * L (max n k)) = (\<Sum> k < n. c n * L n * c k)"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<n}"
    thus "c n * c k * L (max n k) = c n * L n * c k"
      by simp
  qed
  have r3: "(\<Sum> k < n. c n * L n * c k) = c n * L n * S" unfolding S_def
    by (metis sum_distrib_left)
  have s: "(\<Sum> i \<le> n. c i) = S + c n" unfolding S_def
    by (simp add: lessThan_Suc_atMost[symmetric])
  have "(\<Sum> j < Suc n. \<Sum> k < Suc n. c j * c k * L (max j k)) = (\<Sum> j < n. \<Sum> k <
    n. c j * c k * L (max j k)) + 2 * (c n * L n * S) + c n * c n * L n"
    using g[of "\<lambda>j k. c j * c k * L (max j k)"] r1a r2a r3
    by linarith
  also have "\<dots> = (\<Sum> j < n. ((\<Sum> i \<le> j. c i) ^ 2 - (\<Sum> i <
    j. c i) ^ 2) * L j) + ((S + c n) ^ 2 - S ^ 2) * L n"
    using Suc.IH
    by (simp add: power2_eq_square algebra_simps)
  also have "\<dots> = (\<Sum> j < Suc n. ((\<Sum> i \<le> j. c i) ^ 2 - (\<Sum> i <
    j. c i) ^ 2) * L j)"
    using s unfolding S_def
    by simp
  finally show ?case .
qed

lemma Spart_eq: "j \<le> 16 \<Longrightarrow> Spart j = (\<Sum> i < j. cK i)"
proof -
  assume j: "j \<le> 16"
  have l: "length table1 = 16" by (simp add: table1_def)
  have "Spart j = (\<Sum> i = 0..<length (map tC (take j table1)). map tC (take j table1) ! i)"
    unfolding Spart_def using sum_list_sum_nth[of "map tC (take j table1)"]
    by meson
  also have "\<dots> = (\<Sum> i < j. cK i)"
  proof (rule sum.cong)
    show "{0..<length (map tC (take j table1))} = {..<j}" using j l
      by auto
    fix i assume "i \<in> {..<j}"
    thus "map tC (take j table1) ! i = cK i" using j l unfolding cK_def
      by simp
  qed
  finally show ?thesis .
qed

text \<open>(A.2): @{text "I(\<rho>) = \<Sum>_j (S_j^2 - S_{j-1}^2) log((b_j - a_j)/4)"}.\<close>
theorem energy_A2:
  "logEnergy rho = (\<Sum> j < 16. (Spart (j + 1) ^ 2 - Spart j ^ 2) * ln ((tB (table1 ! j) -
    tA (table1 ! j)) / 4))"
  unfolding logEnergy_rho sum_max_regroup Lk_def[symmetric]
  by (rule sum.cong[OF refl]) (simp add: Spart_eq Lk_def lessThan_Suc_atMost)

subsection \<open>Elementary enclosures\<close>

text \<open>Partial sums of the atanh series.\<close>
definition atS :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "atS z m = (\<Sum> k < m. 2 * (1 / (2 * real k + 1)) * z ^ (2 * k + 1))"

text \<open>(A.3): @{text "S_m(z) \<le> log((1+z)/(1-z)) \<le> S_m(z) + 2z^{2m+1}/((2m+1)(1-z^2))"}
  for @{text "0 \<le> z < 1"}.\<close>
lemma log_series_bounds:
  assumes "0 \<le> z" "z < 1"
  shows "atS z m \<le> ln ((1 + z) / (1 - z)) \<and>
         ln ((1 + z) / (1 - z)) \<le> atS z m + 2 * z ^ (2 * m + 1) / ((2 * real m + 1) * (1 -
           z ^ 2))"
proof -
  define x where "x = (1 + z) / (1 - z)"
  define f where "f n = 2 * z ^ (2 * n + 1) / real (2 * n + 1)" for n
  have z1: "0 < 1 - z" using assms by simp
  have x0: "0 < x" using assms by (simp add: x_def)
  have xz: "(x - 1) / (x + 1) = z" using z1 by (simp add: x_def field_simps)
  have S: "f sums ln x" using ln_series_quadratic[OF x0] unfolding xz f_def .
  have sf: "summable f" using S by (rule sums_summable)
  have L: "ln x = suminf f" using S by (simp add: sums_iff)
  have f0: "0 \<le> f n" for n using assms by (simp add: f_def)
  have atS_eq: "atS z m = (\<Sum> k < m. f k)" unfolding atS_def f_def by (simp add: field_simps)
  have low: "(\<Sum> k < m. f k) \<le> suminf f" by (rule sum_le_suminf[OF sf]) (simp_all add: f0)
  define c where "c = 2 * z ^ (2 * m + 1) / (2 * real m + 1)"
  define g where "g n = c * (z ^ 2) ^ n" for n
  have zz0: "0 \<le> z ^ 2" by simp
  have zz: "z ^ 2 < 1" using assms by (simp add: power_less_one_iff)
  have G: "g sums (c * (1 / (1 - z ^ 2)))"
    unfolding g_def by (rule sums_mult) (rule geometric_sums, use zz zz0 in simp)
  have fg: "f (n + m) \<le> g n" for n
  proof -
    have e: "z ^ (2 * (n + m) + 1) = z ^ (2 * m + 1) * (z ^ 2) ^ n"
      by (simp add: power_add[symmetric] power_mult[symmetric] algebra_simps)
    have "f (n + m) = 2 * z ^ (2 * m + 1) * (z ^ 2) ^ n / real (2 * (n + m) + 1)"
      unfolding f_def e by simp
    also have "\<dots> \<le> 2 * z ^ (2 * m + 1) * (z ^ 2) ^ n / (2 * real m + 1)"
      using assms by (intro divide_left_mono) auto
    also have "\<dots> = g n" by (simp add: g_def c_def)
    finally show ?thesis .
  qed
  have tail: "suminf (\<lambda>n. f (n + m)) = suminf f - (\<Sum> k < m. f k)"
    by (rule suminf_minus_initial_segment[OF sf])
  have "suminf (\<lambda>n. f (n + m)) \<le> suminf g"
    by (rule suminf_le[OF fg]) (use sf G in \<open>auto simp: summable_iff_shift sums_summable[OF
      G]\<close>)
  also have "suminf g = c * (1 / (1 - z ^ 2))" using G by (simp add: sums_iff)
  finally have up: "suminf f \<le> (\<Sum> k < m. f k) + c * (1 / (1 - z ^ 2))" using tail by simp
  have cc: "c * (1 / (1 - z ^ 2)) = 2 * z ^ (2 * m + 1) / ((2 * real m + 1) * (1 - z ^ 2))"
    by (simp add: c_def)
  show ?thesis unfolding x_def[symmetric] L atS_eq using low up cc by simp
qed

text \<open>(A.10): the enclosures of @{text "I(\<rho>)"} and @{text "C*"} (18 logarithms to 25
  digits; in Isabelle
  either @{text approximation} or (A.3) evaluated
    by @{text simp}).  The endpoints combine to exactly
  @{text "-1366995564511/10^1^2"}, so (6.4) rests on the strict enclosures.\<close>
text \<open>The explicit value of @{text "I(\<rho>)"} as a combination of sixteen logarithms of
  rationals.\<close>
lemma logEnergy_explicit:
  "logEnergy rho = (\<Sum> j < 16. (Spart (j + 1) ^ 2 - Spart j ^ 2) * ln ((tB (table1 ! j) -
    tA (table1 ! j)) / 4))"
  by (rule energy_A2)

text \<open>A finite sum over sixteen indices, unfolded.\<close>
lemma sum16: "(\<Sum> j < 16. f j) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 +
  f 10 + f 11 + f 12 + f 13 + f 14 + f 15"
  for f :: "nat \<Rightarrow> real"
      by (simp add: eval_nat_numeral)

subsection \<open>(A.9): the potential inequality on the half-line\<close>

text \<open>The certified-checker part.  Lean defines computable rational upper/lower bounds for
  @{text "\<surd>"}, @{text log}, @{text arctan} (soundness lemmas), a checker
  @{text "chk l r = (2\<cdot>Ubnd l r - VL l r \<le> Bd)"} with @{text "Bd = -66451/10^4"},
    and checks a chain of
  1,052 intervals covering @{text "[0, 2]"}
    by kernel evaluation.  In Isabelle the bound functions can be
  @{text "lb_ln/ub_ln"}, @{text "lb_sqrt/ub_sqrt"}, @{text "lb_arctan/ub_arctan"} from
  HOL-Decision\_Procs.Approximation\_Bounds (soundness: @{text bnds_ln}, @{text bnds_sqrt},
  @{text bnds_arctan}); the evaluation is
    by @{text eval} (oracle) or @{text code_simp} (kernel).\<close>
text \<open>Closed forms: @{text "\<integral>_0^c log(t + u^2) du =
  c log(t + c^2) - 2c + 2\<surd>t arctan(c/\<surd>t)"}
  for @{text "t > 0"}, and @{text "2(c log c - c)"} at @{text "t = 0"}.\<close>
lemma Ic_closed:
  assumes "0 < t" "0 < c"
  shows "integral {0..c} (\<lambda>u. ln (t + u ^ 2)) =
    c * ln (t + c ^ 2) - 2 * c + 2 * sqrt t * arctan (c / sqrt t)"
proof -
  define F where "F u = u * ln (t + u ^ 2) - 2 * u + 2 * sqrt t * arctan (u / sqrt t)" for u
  have st: "0 < sqrt t" using assms
    by auto
  have D: "(F has_real_derivative ln (t + u ^ 2)) (at u)" for u
  proof -
    have tu: "0 < t + u ^ 2" using assms
      by (smt (verit, ccfv_SIG) not_sum_power2_lt_zero)
    have q1: "sqrt t * sqrt t = t" using assms
      by simp
    have q4: "sqrt t * (2 * sqrt t) = 2 * t" using q1
      by simp
    have q5: "inverse ((t + u\<^sup>2) / t) = t / (t + u\<^sup>2)"
      by simp
    have q2: "(u / sqrt t)\<^sup>2 = u\<^sup>2 / t" using assms
      by (simp add: power_divide)
    have q3: "1 + u\<^sup>2 / t = (t + u\<^sup>2) / t" using assms
      by (simp add: field_simps)
    have h1: "inverse (1 + (u / sqrt t)\<^sup>2) * sqrt t * (2 * sqrt t) / t =
      2 * t / (t + u\<^sup>2)" using tu assms
      unfolding q2 q3
      using q1
      by (simp add: q4 q5 mult.assoc)
    have h2: "2 * u * u / (t + u\<^sup>2) + (2 * t / (t + u\<^sup>2) - 2) = 0" using tu
      by (simp add: field_simps power2_eq_square)
    show ?thesis unfolding F_def[abs_def] using tu st assms
      by (intro derivative_eq_intros) (auto, use h1 h2 in presburger)
  qed
  have Dv: "\<And>u. u \<in> {0..c} \<Longrightarrow>
    (F has_vector_derivative ln (t + u ^ 2)) (at u within {0..c})"
    using D has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within by blast
  have "((\<lambda>u. ln (t + u ^ 2)) has_integral (F c - F 0)) {0..c}"
    using fundamental_theorem_of_calculus[OF _ Dv] assms by linarith
  hence "integral {0..c} (\<lambda>u. ln (t + u ^ 2)) = F c - F 0" by blast
  thus ?thesis unfolding F_def by simp
qed

lemma Ic_zero:
  assumes "0 < c"
  shows "integral {0..c} (\<lambda>(u::real). ln (0 + u ^ 2)) = 2 * (c * ln c - c)"
proof -
  define F where "F u = 2 * (u * ln u - (u::real))" for u
  have lim0: "((\<lambda>u::real. 2 * (u * ln u - u)) \<longlongrightarrow> 0) (at_right 0)"
    by real_asymp
  have cont: "continuous_on {0..c} F"
  proof (rule continuous_on_IccI)
    show "(F \<longlongrightarrow> F 0) (at_right 0)" using lim0 unfolding F_def
      by simp
    show "(F \<longlongrightarrow> F c) (at_left c)" using assms unfolding F_def
      by (force intro: tendsto_intros)
    show "0 < c" by (rule assms)
    fix x assume "0 < x" "x < c"
    thus "F \<midarrow>x\<rightarrow> F x" unfolding F_def
      by (fast intro: tendsto_intros)
  qed
  have Dv: "\<And>x. x \<in> {0<..<c} \<Longrightarrow>
    (F has_vector_derivative ln (0 + x ^ 2)) (at x)"
  proof -
    fix x :: real assume x: "x \<in> {0<..<c}"
    have x0: "0 < x" using x
      by auto
    have "(F has_real_derivative 2 * (1 * ln x + x * (1 / x) - 1)) (at x)" unfolding F_def[abs_def]
      using x0
      by (intro derivative_eq_intros) auto
    moreover have "2 * (1 * ln x + x * (1 / x) - 1) = ln (0 + x ^ 2)" using x0 ln_realpow[of x 2]
      by simp
    ultimately show "(F has_vector_derivative ln (0 + x ^ 2)) (at x)"
      using has_real_derivative_iff_has_vector_derivative
      by algebra
  qed
  have "((\<lambda>u. ln (0 + u ^ 2)) has_integral (F c - F 0)) {0..c}"
    using fundamental_theorem_of_calculus_interior[OF _ cont Dv] assms
    by linarith
  hence "integral {0..c} (\<lambda>u. ln (0 + u ^ 2)) = F c - F 0"
    by (fast intro: integral_unique)
  thus ?thesis unfolding F_def
    by argo
qed


lemma Vf_closed:
  assumes "0 < t"
  shows "Vf t = 2 * pi * sqrt t + (ln (t + 1) - 2 + 2 * sqrt t * arctan (1 / sqrt t))
                - 6 * (3 / 40 * ln (t + (3 / 40) ^ 2) - 2 * (3 / 40) + 2 * sqrt t * arctan (3 / 40 /
                  sqrt t))"
  unfolding Vf_def using Ic_closed[OF assms, of 1] Ic_closed[OF assms, of "3 / 40"] by simp

lemma Vf_zero: "Vf 0 = - 2 - 6 * (2 * (3 / 40 * ln (3 / 40) - 3 / 40))"
proof -
  have h1: "integral {0..1} (\<lambda>(u::real). ln (0 + u ^ 2)) = 2 * (1 * ln 1 - 1)"
    using Ic_zero by simp
  have h2: "integral {0..3 / 40} (\<lambda>(u::real). ln (0 + u ^ 2)) =
    2 * (3 / 40 * ln (3 / 40) - 3 / 40)" by (rule Ic_zero) simp
  show ?thesis unfolding Vf_def h1 h2 by force
qed

text \<open>(6.8) on @{text "[2, \<infinity>)"},
  by hand: @{text "2U^\<rho>(t) - V(t) \<le>
    (13/10) log t + 6\<alpha>^3/t - 2\<pi>\<surd>t"}.\<close>
lemma Uk_le_log: "k < 16 \<Longrightarrow> 2 \<le> t \<Longrightarrow> Uk k t \<le> ln t"
proof -
  assume k: "k < 16" and t: "2 \<le> t"
  define a where "a = tA (table1 ! k)"
  define b where "b = tB (table1 ! k)"
  have ab: "0 < a" "a < b" "b < 2" using table1_nth[OF k] unfolding a_def b_def by force+
  have nb: "\<not> (a \<le> t \<and> t \<le> b)" using ab t by linarith
  have U: "Uk k t = ln ((\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2)"
    using Uk_eq[OF k, of t] nb unfolding a_def b_def by presburger
  have sq: "sqrt ((t - a) * (t - b)) \<le> t"
  proof -
    have "(t - a) * (t - b) \<le> t * t" using ab t by (simp add: mult_mono)
    hence "sqrt ((t - a) * (t - b)) \<le> sqrt (t * t)" using real_sqrt_le_mono by presburger
    thus ?thesis using t by auto
  qed
  have m: "\<bar>t - (a + b) / 2\<bar> = t - (a + b) / 2" using ab t by force
  have p8: "0 \<le> (t - a) * (t - b)" using ab t
    by simp
  have pos: "0 < (\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2"
    using ab t m real_sqrt_ge_zero[OF p8]
    by argo
  have le: "(\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2 \<le> t" using ab t m sq
    by argo
  show ?thesis unfolding U using pos le t ln_le_cancel_iff by simp
qed

lemma sum_cK: "(\<Sum> k < 16. cK k) = lam_r"
proof -
  have l: "length table1 = 16" by (simp add: table1_def)
  have "(\<Sum> e \<leftarrow> table1. tC e) = (\<Sum> k < length table1. tC (table1 ! k))"
    using sum_list_sum_nth[of "map tC table1"] by (simp add: atLeast0LessThan)
  thus ?thesis using table1_sum_tC l unfolding cK_def by simp
qed

lemma logPot_le_of_two_le: "2 \<le> t \<Longrightarrow> logPot rho t \<le> lam_r * ln t"
proof -
  assume t: "2 \<le> t"
  have "logPot rho t = (\<Sum> k < 16. cK k * Uk k t)" by (rule logPot_rho)
  also have "\<dots> \<le> (\<Sum> k < 16. cK k * ln t)"
  proof (rule sum_mono)
    fix k assume "(k::nat) \<in> {..<16}"
    hence k: "k < 16" by blast
    have c: "0 \<le> cK k" using table1_nth[OF k] by satx
    show "cK k * Uk k t \<le> cK k * ln t" using mult_left_mono[OF Uk_le_log[OF k t] c] by satx
  qed
  also have "\<dots> = lam_r * ln t" using sum_cK sum_distrib_right[of cK "{..<16}" "ln t"]
    by presburger
  finally show ?thesis .
qed

lemma Ic1_ge: "0 < t \<Longrightarrow> ln t \<le>
  integral {0..1} (\<lambda>(u::real). ln (t + u ^ 2))"
proof -
  assume t: "0 < t"
  have tq: "t + u ^ 2 \<noteq> 0" for u using add_pos_nonneg[OF t, of "u ^ 2"]
    by simp
  have cont: "continuous_on {0..1} (\<lambda>u. ln (t + u ^ 2))"
    by (force simp: tq intro: continuous_intros)
  have i1: "(\<lambda>u. ln (t + u ^ 2)) integrable_on {0..1}"
    using integrable_continuous_interval cont by blast
  have i0: "(\<lambda>u. ln t) integrable_on {0..(1::real)}" by blast
  have pw: "\<And>u. u \<in> {0..1} \<Longrightarrow> ln t \<le> ln (t + u ^ 2)" using t
    using less_eq_real_def ln_mono by auto
  have "integral {0..1} (\<lambda>(u::real). ln t) \<le>
    integral {0..1} (\<lambda>u. ln (t + u ^ 2))"
    using  integral_le[OF i0 i1 pw] by presburger
  thus ?thesis by fastforce
qed

lemma Icalpha_le: "0 < (t::real) \<Longrightarrow>
  integral {0..3 / 40} (\<lambda>u. ln (t + u ^ 2)) \<le> 3 / 40 * ln (t + (3 / 40) ^ 2)"
proof -
  assume t: "0 < t"
  have tq: "t + u ^ 2 \<noteq> 0" for u using add_pos_nonneg[OF t, of "u ^ 2"]
    by simp
  have cont: "continuous_on {0..3 / 40} (\<lambda>u. ln (t + u ^ 2))"
    using tq by (fast intro: continuous_intros)
  have i1: "(\<lambda>u. ln (t + u ^ 2)) integrable_on {0..3 / 40}"
    using integrable_continuous_interval[OF cont]
    by fast
  have i0: "(\<lambda>u. ln (t + (3 / 40) ^ 2)) integrable_on {0..(3 / 40 :: real)}"
    by blast
  have pw: "\<And>u. u \<in> {0..3 / 40} \<Longrightarrow>
    ln (t + u ^ 2) \<le> ln (t + (3 / 40) ^ 2)"
  proof -
    fix u :: real assume u: "u \<in> {0..3 / 40}"
    have "u ^ 2 \<le> (3 / 40) ^ 2" using u power_mono[of u "3 / 40" 2] by presburger
    moreover have "0 < t + u ^ 2" using t by (simp add: add_pos_nonneg)
    ultimately show "ln (t + u ^ 2) \<le> ln (t + (3 / 40) ^ 2)" using ln_le_cancel_iff by simp
  qed
  have "integral {0..3 / 40} (\<lambda>u. ln (t + u ^ 2)) \<le>
    integral {0..3 / 40} (\<lambda>(u::real). ln (t + (3 / 40) ^ 2))"
    using integral_le[OF i1 i0 pw] by presburger
  thus ?thesis by auto
qed

text \<open>(6.8) on @{text "[2, \<infinity>)"}, by hand.\<close>
lemma tail_bound: "2 \<le> t \<Longrightarrow> 2 * logPot rho t - Vf t < - 6645002 / 10 ^ 6"
proof -
  assume t: "2 \<le> t"
  have t0: "0 < t" using t by simp
  have "logPot rho t \<le> lam_r * ln t"
    by (rule logPot_le_of_two_le[OF t])
  moreover have "2 * pi * sqrt t + ln t - 6 * (3 / 40 * ln (t + (3 / 40) ^ 2)) \<le> Vf t"
    unfolding Vf_def using Ic1_ge[OF t0] Icalpha_le[OF t0] by linarith
  moreover have "2 * lam_r * ln t - (2 * pi * sqrt t + ln t - 6 * (3 / 40 * ln (t + (3 /
    40) ^ 2))) < - 6645002 / 10 ^ 6"
  proof -
    define s where "s = sqrt t"
    have s0: "0 < s" using t0 unfolding s_def
      by simp
    have s2: "sqrt 2 \<le> s" unfolding s_def using t real_sqrt_le_mono
      by blast
    have r2: "1.4 \<le> sqrt (2::real)" using real_le_rsqrt[of "1.4" 2]
      by (simp add: power2_eq_square)
    have lt: "ln t \<le> 2 * (s - 1)"
    proof -
      have "ln t = 2 * ln s" unfolding s_def using ln_sqrt[of t] t0
        by linarith
      moreover have "ln s \<le> s - 1" using ln_le_minus_one[OF s0] .
      ultimately show ?thesis
        by simp
    qed
    have la: "ln (t + (3 / 40) ^ 2) \<le> ln t + (3 / 40) ^ 2 / 2"
    proof -
      have m6: "t * (1 + (3 / 40) ^ 2 / t) = t + (3 / 40) ^ 2" using t0
        by (simp add: distrib_left)
      have p6: "1 + (3 / 40) ^ 2 / t \<noteq> 0" using add_pos_nonneg[of 1 "(3 / 40) ^ 2 / t"] t0
        by simp
      have e: "ln (t + (3 / 40) ^ 2) = ln t + ln (1 + (3 / 40) ^ 2 / t)"
        using t0 ln_mult[of t "1 + (3 / 40) ^ 2 / t"] m6 p6
        by simp
      have "ln (1 + (3 / 40) ^ 2 / t) \<le> (3 / 40) ^ 2 / t"
        using ln_le_minus_one[of "1 + (3 / 40) ^ 2 / t"] t0
        using add_pos_nonneg[of 1 "(3 / 40) ^ 2 / t"] t0
        by simp
      moreover have "(3 / 40) ^ 2 / t \<le> (3 / 40) ^ 2 / 2" using t
        by (fastforce intro: divide_left_mono)
      ultimately show ?thesis using e
        by linarith
    qed
    have pis: "3 * s \<le> pi * s" using pi_gt3 s0
      by simp
    have c2: "(3 / 40 :: real) ^ 2 = 9 / 1600"
      by (simp add: power2_eq_square)
    have key: "2 * (37 / 40) * ln t - (2 * pi * s + ln t - 6 * (3 / 40 * ln (t + (3 /
      40) ^ 2))) \<le> - 7"
      using lt la pis s2 r2 c2
      by argo
    show ?thesis unfolding lam_r_def s_def[symmetric] using lt la pis key
      by simp
  qed
  ultimately show ?thesis by linarith
qed

subsection \<open>Ingredients of (6.9) that live here\<close>

text \<open>The circle average of @{text "log|z - a|"} (@{text "circ_log"}) is proved in the
  circle-average section above
  (a second copy of the statement here was a duplicate fact declaration).\<close>

text \<open>The mass bound for @{text \<rho>}: @{text "\<rho>([x - r, x + r]) \<le> 40\<surd>r"}
  (from the density).\<close>


lemma table1_gap: "\<forall>e \<in> set table1. 1 / 225 < tB e - tA e"
  by (simp add: table1_def tA_def tB_def)


lemma rho_Icc_aux:
  assumes "\<forall>e \<in> set xs. 0 \<le> tC e \<and> tA e < tB e \<and>
    1 / 225 < tB e - tA e" and r: "0 \<le> r"
  shows "(\<integral>\<^sup>+ t. ennreal (\<Sum> e \<leftarrow> xs. tC e *
    arcsine_dens (tA e) (tB e) t) * indicator {x - r..x + r} t \<partial>lborel)
           \<le> ennreal ((\<Sum> e \<leftarrow> xs. tC e) * (40 * sqrt r))"
  using assms(1)
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons e xs)
  have c: "0 \<le> tC e" "tA e < tB e" "1 / 225 < tB e - tA e" using Cons.prems by auto
  have r0: "0 \<le> (\<Sum> e \<leftarrow> xs. tC e * arcsine_dens (tA e) (tB e) t)" for t
    using Cons.prems by (intro sum_list_nonneg) (auto intro!: mult_nonneg_nonneg
      arcsine_dens_nonneg)
  have s0: "0 \<le> (\<Sum> e \<leftarrow> xs. tC e)" using Cons.prems
    by (intro sum_list_nonneg) auto
  have md: "(\<lambda>t. ennreal (arcsine_dens (tA e) (tB e) t)) \<in> borel_measurable lborel"
    unfolding arcsine_dens_def by measurable
  have "(\<integral>\<^sup>+ t. ennreal (\<Sum> e' \<leftarrow> e # xs. tC e' *
    arcsine_dens (tA e') (tB e') t) * indicator {x - r..x + r} t \<partial>lborel)
      = (\<integral>\<^sup>+ t. ennreal (tC e) * (ennreal (arcsine_dens (tA e) (tB e) t) *
        indicator {x - r..x + r} t)
                + ennreal (\<Sum> e \<leftarrow> xs. tC e * arcsine_dens (tA e) (tB e) t) *
                  indicator {x - r..x + r} t \<partial>lborel)"
    using c r0
    by (force simp: ennreal_plus[symmetric] ennreal_mult arcsine_dens_nonneg distrib_right
      mult.assoc intro: nn_integral_cong)
  also have "\<dots> = ennreal (tC e) * (\<integral>\<^sup>+ t. ennreal (arcsine_dens (tA e) (tB e)
    t) * indicator {x - r..x + r} t \<partial>lborel)
                  + (\<integral>\<^sup>+ t. ennreal (\<Sum> e \<leftarrow> xs. tC e *
                    arcsine_dens (tA e) (tB e) t) * indicator {x - r..x + r} t \<partial>lborel)"
    using md
    by (force simp: nn_integral_add nn_integral_cmult)
  also have "\<dots> \<le> ennreal (tC e) * ennreal (40 * sqrt r) +
    ennreal ((\<Sum> e \<leftarrow> xs. tC e) * (40 * sqrt r))"
  proof -
    have "(\<integral>\<^sup>+ t. ennreal (arcsine_dens (tA e) (tB e) t) * indicator {x - r..x +
      r} t \<partial>lborel) = emeasure (arcsine (tA e) (tB e)) {x - r..x + r}"
      unfolding arcsine_def using md by (simp add: emeasure_density)
    also have "\<dots> \<le> ennreal (40 * sqrt r)" by (rule arcsine_Icc_le40[OF c(2) c(3) r])
    finally show ?thesis using Cons.IH Cons.prems
      by (force intro: add_mono mult_left_mono)
  qed
  also have "\<dots> = ennreal ((\<Sum> e' \<leftarrow> e # xs. tC e') * (40 * sqrt r))"
    using c s0 r
    using ennreal_mult[of "tC e" "40 * sqrt r"] ennreal_plus[of "tC e * (40 *
      sqrt r)" "(\<Sum> e \<leftarrow> xs. tC e) * (40 * sqrt r)"] real_sqrt_ge_zero[OF r]
    by (auto simp: distrib_right)
  finally show ?case .
qed

lemma rho_Icc_le: "0 \<le> r \<Longrightarrow>
  emeasure rho {x - r..x + r} \<le> ennreal (40 * sqrt r)"
proof -
  assume r: "0 \<le> r"
  have pr: "\<forall>e \<in> set table1. 0 \<le> tC e \<and> tA e < tB e \<and>
    1 / 225 < tB e - tA e" using table1_props table1_gap by auto
  have e: "emeasure rho {x - r..x + r} =
    (\<integral>\<^sup>+ t. ennreal (\<Sum> e \<leftarrow> table1. tC e *
    arcsine_dens (tA e) (tB e) t) * indicator {x - r..x + r} t \<partial>lborel)"
    unfolding rho_def by (subst emeasure_density) auto
  have l: "lam_r * (40 * sqrt r) \<le> 40 * sqrt r" using real_sqrt_ge_zero[OF r]
    unfolding lam_r_def by simp
  show ?thesis unfolding e using rho_Icc_aux[OF pr r, of x] table1_sum_tC l
    by (force intro: order_trans ennreal_leI)
qed

text \<open>(6.7): @{text "2U^\<rho>(t) - V(t) + \<surd>t/K \<le> M_0 + \<surd>2/K"}
  for @{text "t \<ge> 0"}, @{text "K \<ge> 40"}.\<close>
lemma V_lower: "2 \<le> t \<Longrightarrow>
  2 * pi * sqrt t + (1 - 6 * alpha_r) * ln t - 2 * alpha_r ^ 3 / t \<le> Vf t"
proof -
  assume t: "2 \<le> t"
  have t0: "0 < t" using t
    by simp
  have I1: "ln t \<le> integral {0..1} (\<lambda>u. ln (t + u ^ 2))" by (rule Ic1_ge[OF t0])
  have tp: "0 < t + u ^ 2" for u using add_pos_nonneg[OF t0, of "u ^ 2"]
    by simp
  have tq: "t + u ^ 2 \<noteq> 0" for u using tp[of u]
    by simp
  have cont: "continuous_on {0..3 / 40} (\<lambda>u. ln (t + u ^ 2))"
    using tq by (fast intro: continuous_intros)
  have i1: "(\<lambda>u. ln (t + u ^ 2)) integrable_on {0..3 / 40}"
    using integrable_continuous_interval[OF cont]
    by meson
  have cont2: "continuous_on {0..3 / 40} (\<lambda>u. ln t + u ^ 2 / t)"
    using t0
    by (fastforce intro: continuous_intros)
  have i2: "(\<lambda>u. ln t + u ^ 2 / t) integrable_on {0..3 / 40}"
    using integrable_continuous_interval[OF cont2]
    by meson
  have pw: "\<And>u. u \<in> {0..3 / 40} \<Longrightarrow> ln (t + u ^ 2) \<le> ln t + u ^ 2 / t"
  proof -
    fix u :: real
    have m6: "t * (1 + u ^ 2 / t) = t + u ^ 2" using t0
      by (simp add: field_simps)
    have p6: "1 + u ^ 2 / t \<noteq> 0" using add_pos_nonneg[of 1 "u ^ 2 / t"] t0
      by simp
    have e: "ln (t + u ^ 2) = ln t + ln (1 + u ^ 2 / t)"
      using t0 ln_mult[of t "1 + u ^ 2 / t"] m6 p6
      by simp
    have "ln (1 + u ^ 2 / t) \<le> u ^ 2 / t" using ln_le_minus_one[of "1 + u ^ 2 / t"] t0
      using add_pos_nonneg[of 1 "u ^ 2 / t"] t0
      by simp
    thus "ln (t + u ^ 2) \<le> ln t + u ^ 2 / t" using e
      by simp
  qed
  have Ia: "integral {0..3 / 40} (\<lambda>u. ln (t + u ^ 2)) \<le>
    integral {0..3 / 40} (\<lambda>u. ln t + u ^ 2 / t)" by (rule integral_le[OF i1 i2 pw])
  have Ib: "integral {0..3 / 40} (\<lambda>u. ln t + u ^ 2 / t) =
    3 / 40 * ln t + (3 / 40) ^ 3 / (3 * t)"
  proof -
    define G where "G u = u * ln t + u ^ 3 / (3 * t)" for u
    have Dv: "\<And>u. u \<in> {0..3 / 40} \<Longrightarrow>
      (G has_vector_derivative (ln t + u ^ 2 / t)) (at u within {0..3 / 40})"
    proof -
      fix u :: real
      have "(G has_real_derivative (ln t + u ^ 2 / t)) (at u)" unfolding G_def[abs_def] using t0
        by (intro derivative_eq_intros) auto
      thus "(G has_vector_derivative (ln t + u ^ 2 / t)) (at u within {0..3 / 40})"
        using has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within
        by blast
    qed
    have "((\<lambda>u. ln t + u ^ 2 / t) has_integral (G (3 / 40) - G 0)) {0..3 / 40}"
      using fundamental_theorem_of_calculus[OF _ Dv]
      by linarith
    hence "integral {0..3 / 40} (\<lambda>u. ln t + u ^ 2 / t) = G (3 / 40) - G 0"
      by (blast intro: integral_unique)
    thus ?thesis unfolding G_def
      by simp
  qed
  have six: "6 * ((3 / 40) ^ 3 / (3 * t)) = 2 * (3 / 40) ^ 3 / t" using t0
    by (simp add: field_simps)
  show ?thesis unfolding Vf_def alpha_r_def using I1 Ia Ib six
    by argo
qed


end


