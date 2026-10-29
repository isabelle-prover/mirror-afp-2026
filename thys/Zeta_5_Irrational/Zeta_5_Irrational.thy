(*  Title:   Zeta_5_Irrational.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta_5_Irrational
  imports Zeta5_Archimedean_Bound Zeta5_Exact_Constants "HOL-Real_Asymp.Real_Asymp"
    "Liouville_Numbers.Liouville_Numbers_Misc"
begin

section \<open>The main theorem: \<open>\<zeta>(5)\<close> is irrational\<close>

text \<open>Section 7 of the paper: Theorem 2.1 (\<open>Q\<^sub>K\<^sub>,\<^sub>M \<in>
  \<int>[X]\<close> of degree \<open>h\<close> with \<open>Q\<^sub>K\<^sub>,\<^sub>M(\<zeta>(5)) >
  0\<close>), the limit
  (7.1), the decay (2.7) for \<open>M = 200\<close>, the elementary irrationality criterion
  (@{text irrational_of_int_poly_approx}: integer polynomials \<open>Q\<^sub>n\<close> of degree
    \<open>\<le> d n\<close> with
  \<open>0 < Q\<^sub>n(x) < exp(-c n\<^sup>2)\<close> force \<open>x \<notin> \<rat>\<close>),
    and the main theorem @{text zeta5_irrational}.  Lean theories
  @{text Section7}, @{text Main}, @{text Claim}.\<close>


lemma real_eval_smult: "real_eval (Polynomial.smult c P) x = of_rat c * real_eval P x"
  by (simp add: real_eval_def map_poly_smult of_rat_mult)

lemma real_eval_QKM: "real_eval (QKM K M) zeta5 = of_rat (mKM K M) * real_eval (FK K) zeta5"
  by (simp add: QKM_def real_eval_smult)

lemma real_eval_FK: "real_eval (FK K) zeta5 = of_rat (SK K) * real_eval (DeltaK K) zeta5"
  by (simp add: FK_def real_eval_smult)

text \<open>Theorem 2.1, first part: @{text "Q_{K,M} \<in> \<int>[X]"}, @{text "deg Q_{K,M} = h"},
  @{text "Q_{K,M}(\<zeta>(5)) > 0"}.\<close>
theorem QKM_int_degree_pos:
  assumes "StdHyp K M"
  shows "(\<exists>P :: int poly. map_poly of_int P = QKM K M) \<and>
    degree (QKM K M) = hof K \<and>
         0 < real_eval (QKM K M) zeta5"
proof (intro conjI)
  show "\<exists>P :: int poly. map_poly of_int P = QKM K M" by (rule QKM_int_poly[OF assms])
  have hK: "40 dvd K" using assms by (simp add: StdHyp_def)
  have "QKM K M = Polynomial.smult (mKM K M * SK K) (DeltaK K)"
    by (simp add: QKM_def FK_def mult_ac)
  thus "degree (QKM K M) = hof K"
    using mKM_pos[of K M] SK_pos[of K] Delta_degree_lead_coeff[OF hK]
      by (auto simp: degree_smult_eq)
  show "0 < real_eval (QKM K M) zeta5"
    using mKM_pos SK_pos Delta_zeta5_pos by (simp add: real_eval_QKM real_eval_FK)
qed

text \<open>@{text "(24 K log K + 200 K)/K^2 \<rightarrow> 0"} along @{text "K = 40n"}
  (@{text real_asymp}).\<close>
lemma error_term_small:
  assumes "0 < \<epsilon>"
  shows "\<forall>\<^sub>F n in at_top.
     (24 * real (40 * n) * ln (real (40 * n)) + 200 * real (40 * n)) / real (40 * n) ^ 2 \<le>
       \<epsilon>"
proof -
  define f where "f = (\<lambda>n. (24 * real (40 * n) * ln (real (40 * n)) + 200 * real (40 * n)) /
    real (40 * n) ^ 2)"
  have "(f \<longlongrightarrow> 0) at_top" unfolding f_def by real_asymp
  from tendstoD[OF this assms] have "\<forall>\<^sub>F n in at_top. f n \<le> \<epsilon>"
    by (elim eventually_mono) (auto simp: dist_real_def abs_less_iff)
  thus ?thesis by (simp add: f_def)
qed

text \<open>(7.1): @{text "limsup K^-^2 log Q_{K,M}(\<zeta>(5)) \<le> A_M + Ubar"}
  for @{text "M \<in> 40\<int>"}, @{text "M \<ge> 40"}.\<close>
theorem log_QKM_zeta5_limsup:
  assumes "40 \<le> M" "40 dvd M" "0 < \<epsilon>"
  shows "\<forall>\<^sub>F n in at_top.
    ln (real_eval (QKM (40 * n) M) zeta5) / real (40 * n) ^ 2 \<le>
      of_rat (AM M) + of_rat Ubar + \<epsilon>"
proof -
  have A: "\<forall>\<^sub>F n in at_top. ln (of_rat (mKM (40 * n) M)) / real (40 * n) ^ 2 \<le>
    of_rat (AM M) + \<epsilon> / 2"
    by (rule log_mKM_limsup_AM) (use assms in simp_all)
  have B: "\<forall>\<^sub>F n in at_top.
      (24 * real (40 * n) * ln (real (40 * n)) + 200 * real (40 * n)) / real (40 * n) ^ 2 \<le>
        \<epsilon> / 2"
    by (rule error_term_small) (use assms in simp)
  have C: "\<forall>\<^sub>F n in at_top. (0 :: nat) < n" by (rule eventually_gt_at_top)
  from A B C show ?thesis
  proof eventually_elim
    case (elim n)
    have hK: "40 dvd 40 * n" "0 < 40 * n" using elim by simp_all
    have K0: "0 < real (40 * n)" using elim by simp
    have Fpos: "0 < real_eval (FK (40 * n)) zeta5"
      and Flog: "ln (real_eval (FK (40 * n)) zeta5)
        \<le> of_rat Ubar * real (40 * n) ^ 2 + 24 * real (40 * n) * ln (real (40 * n)) + 200 *
          real (40 * n)"
      using log_FK_zeta5_bound[OF hK] by blast+
    have ne: "mKM (40 * n) M \<noteq> 0" "real_eval (FK (40 * n)) zeta5 \<noteq> 0"
      using mKM_pos[of "40 * n" M] Fpos by auto
    have "ln (real_eval (QKM (40 * n) M) zeta5) =
      ln (of_rat (mKM (40 * n) M)) + ln (real_eval (FK (40 * n)) zeta5)"
      unfolding real_eval_QKM by (simp add: ln_mult ne)
    hence eq1: "ln (real_eval (QKM (40 * n) M) zeta5) / real (40 * n) ^ 2 =
            ln (of_rat (mKM (40 * n) M)) / real (40 * n) ^ 2 + ln (real_eval (FK (40 * n)) zeta5) /
              real (40 * n) ^ 2"
      by (simp add: add_divide_distrib)
    have "ln (real_eval (FK (40 * n)) zeta5) / real (40 * n) ^ 2
        \<le> (of_rat Ubar * real (40 * n) ^ 2 + 24 * real (40 * n) * ln (real (40 * n)) + 200 *
          real (40 * n)) / real (40 * n) ^ 2"
      by (intro divide_right_mono Flog) simp
    also have "\<dots> = of_rat Ubar + (24 * real (40 * n) * ln (real (40 * n)) + 200 * real (40 *
      n)) / real (40 * n) ^ 2"
      using K0 by (simp add: add_divide_distrib)
    finally show ?case using elim eq1 by linarith
  qed
qed

text \<open>(2.7): @{text "0 < Q_{40n,200}(\<zeta>(5)) < exp(-139n^2/5)"}
  for all large @{text n}.\<close>
theorem QKM_zeta5_decay:
  "\<forall>\<^sub>F n in at_top.
     0 < real_eval (QKM (40 * n) 200) zeta5 \<and>
     real_eval (QKM (40 * n) 200) zeta5 < exp (- (139 / 5 * real n ^ 2))"
proof -
  define dq :: rat where "dq = 3089837638249482469 / 58872425992515135000"
  have dpos: "0 < (of_rat dq :: real)" by (simp add: dq_def of_rat_divide)
  have A: "\<forall>\<^sub>F n in at_top. ln (real_eval (QKM (40 * n) 200) zeta5) / real (40 *
    n) ^ 2
             \<le> of_rat (AM 200) + of_rat Ubar + of_rat dq / 3200"
    by (rule log_QKM_zeta5_limsup) (use dpos in simp_all)
  from A eventually_ge_at_top[of "200000 :: nat"] show ?thesis
  proof eventually_elim
    case (elim n)
    have h: "StdHyp (40 * n) 200" using elim by (auto simp: StdHyp_def)
    have pos: "0 < real_eval (QKM (40 * n) 200) zeta5" using QKM_int_degree_pos[OF h] by blast
    have n0: "0 < real n" using elim by simp
    have K2: "real (40 * n) ^ 2 = 1600 * real n ^ 2" by (simp add: power_mult_distrib)
    have "ln (real_eval (QKM (40 * n) 200) zeta5)
            \<le> (of_rat (AM 200) + of_rat Ubar + of_rat dq / 3200) * real (40 * n) ^ 2"
      using elim by (subst (asm) pos_divide_le_eq) simp_all
    also have "\<dots> = (of_rat (AM 200) + of_rat Ubar + of_rat dq / 3200) * (1600 * real n ^ 2)"
      by (simp add: K2)
    also have "\<dots> = (- (139 / 5) - of_rat dq / 2) * real n ^ 2"
    proof -
      have c: "(of_rat (AM 200) + of_rat Ubar + of_rat dq / 3200) * 1600 =
        - (139 / 5) - (of_rat dq :: real) / 2"
        unfolding dq_def AM_def Astar_def lam_q_def Ubar_def
        by (simp add: of_rat_divide of_rat_add of_rat_diff of_rat_minus of_rat_mult)
      show ?thesis by (subst mult.assoc[symmetric], subst c, rule refl)
    qed
    also have "\<dots> < - (139 / 5 * real n ^ 2)"
    proof -
      have "0 < of_rat dq / 2 * real n ^ 2" using dpos n0 by simp
      thus ?thesis by (simp add: algebra_simps)
    qed
    finally have "ln (real_eval (QKM (40 * n) 200) zeta5) < - (139 / 5 * real n ^ 2)" .
    hence "real_eval (QKM (40 * n) 200) zeta5 < exp (- (139 / 5 * real n ^ 2))"
      using pos by (metis exp_less_cancel_iff exp_ln)
    thus ?case using pos by simp
  qed
qed



text \<open>The abstract top-level argument:
  if integer polynomials @{text "Q_n"} of degree at most @{text "dn"}
  satisfy @{text "0 < Q_n(x) < exp(-cn^2)"} for large @{text n}, then @{text x} is irrational
  (@{text "b^{dn} Q_n(a/b)"} is a positive integer that is eventually @{text "< 1"}).\<close>
theorem irrational_of_int_poly_approx:
  fixes x c :: real and Qs :: "nat \<Rightarrow> int poly"
  assumes c: "0 < c" and deg: "\<And>n. degree (Qs n) \<le> d * n"
    and ev: "\<forall>\<^sub>F n in at_top. 0 < poly (map_poly of_int (Qs n)) x \<and>
                            poly (map_poly of_int (Qs n)) x < exp (- (c * real n ^ 2))"
  shows "x \<notin> \<rat>"
proof
  assume "x \<in> \<rat>"
  then obtain a b where b: "b > 0" and x: "x = of_int a / of_int b" by (rule Rats_cases')
  have b1: "(1::real) \<le> of_int b" using b by simp
  define N where "N = nat \<lceil>real d * ln (of_int b) / c\<rceil>"
  have "\<forall>\<^sub>F n in at_top. N \<le> n" by (rule eventually_ge_at_top)
  from this ev have "\<forall>\<^sub>F n in at_top. N \<le> n \<and>
    (0 < poly (map_poly of_int (Qs n)) x \<and>
      poly (map_poly of_int (Qs n)) x < exp (- (c * real n ^ 2)))" by (rule eventually_conj)
  then obtain M where M: "\<forall>n \<ge> M. N \<le> n \<and>
    (0 < poly (map_poly of_int (Qs n)) x \<and>
      poly (map_poly of_int (Qs n)) x < exp (- (c * real n ^ 2)))"
    by (auto simp: eventually_at_top_linorder)
  define n where "n = M"
  have n: "N \<le> n" and pos: "0 < poly (map_poly of_int (Qs n)) x"
    and lt: "poly (map_poly of_int (Qs n)) x < exp (- (c * real n ^ 2))"
    using M by (auto simp: n_def)
  define Q where "Q = (map_poly of_int (Qs n) :: real poly)"
  have Qcoeff: "Polynomial.coeff Q i \<in> \<int>" for i by (simp add: Q_def coeff_map_poly)
  have ne: "poly Q (of_int a / of_int b) \<noteq> 0" using pos by (simp add: Q_def x)
  have "1 / of_int b ^ degree Q \<le> \<bar>poly Q (of_int a / of_int b)\<bar>"
    using int_poly_rat_no_root_ge[OF Qcoeff b ne] by simp
  also have "\<bar>poly Q (of_int a / of_int b)\<bar> = poly Q x" using pos by (simp add: Q_def x)
  finally have lower: "1 / of_int b ^ degree Q \<le> poly Q x" .
  have "(of_int b :: real) ^ degree Q \<le> of_int b ^ (d * n)"
    using b1 deg[of n] by (intro power_increasing) (simp_all add: Q_def degree_map_poly)
  hence lower': "(1 :: real) / of_int b ^ (d * n) \<le> 1 / of_int b ^ degree Q"
    using b by (intro divide_left_mono) (auto intro!: mult_pos_pos)
  have "real d * ln (of_int b) / c \<le> real N" by (simp add: N_def real_nat_ceiling_ge)
  also have "\<dots> \<le> real n" using n by simp
  finally have "real d * ln (of_int b) \<le> c * real n" using c by (simp add: field_simps)
  hence "real d * ln (of_int b) * real n \<le> c * real n * real n"
    by (intro mult_right_mono) simp_all
  hence "exp (- (c * real n ^ 2)) \<le> exp (- (real d * ln (of_int b) * real n))"
    by (simp add: power2_eq_square)
  also have e: "exp (real d * ln (of_int b) * real n) = (of_int b :: real) ^ (d * n)"
  proof -
    have "exp (real d * ln (of_int b) * real n) = exp (real (d * n) * ln (of_int b))"
      by (simp add: algebra_simps)
    also have "\<dots> = exp (ln (of_int b)) ^ (d * n)" by (rule exp_of_nat_mult)
    also have "\<dots> = of_int b ^ (d * n)" using b by simp
    finally show ?thesis .
  qed
  have "exp (- (real d * ln (of_int b) * real n)) = (1 :: real) / of_int b ^ (d * n)"
    by (simp add: exp_minus e inverse_eq_divide)
  finally have upper: "exp (- (c * real n ^ 2)) \<le> (1 :: real) / of_int b ^ (d * n)" .
  show False using lower lower' lt upper unfolding Q_def by linarith
qed

text \<open>@{text "\<zeta>(5)"} is real: its Dirichlet series has real terms
  (@{text "Zeta_Function.sums_zeta_nat"}).\<close>
lemma zeta5_real: "zeta 5 \<in> \<real>"
proof -
  have "(\<lambda>k. Im (1 / of_nat (Suc k) ^ 5 :: complex)) sums Im (zeta 5)"
    using sums_zeta_nat[of 5] by (intro sums_Im) simp
  moreover have "Im (1 / of_nat (Suc k) ^ 5 :: complex) = 0" for k
  proof -
    have "(1 / of_nat (Suc k) ^ 5 :: complex) = of_real (1 / real (Suc k) ^ 5)" by simp
    thus ?thesis by (simp only:) simp
  qed
  ultimately have "(\<lambda>k. 0 :: real) sums Im (zeta 5)" by simp
  hence "Im (zeta 5) = 0" using sums_unique2 sums_zero by blast
  thus ?thesis by (simp add: complex_is_Real_iff)
qed

lemma zeta5_eq: "zeta 5 = of_real zeta5"
  unfolding zeta5_def using zeta5_real by simp

text \<open>The integer polynomials @{text "Q_{40n,200}"} (and @{text 0}
  for small @{text n}).\<close>
definition Qint :: "nat \<Rightarrow> int poly" where
  "Qint n = (if StdHyp (40 * n) 200 then (SOME P. map_poly of_int P = QKM (40 * n) 200) else 0)"

lemma Qint_spec:
  assumes "StdHyp (40 * n) 200"
  shows "map_poly of_int (Qint n) = QKM (40 * n) 200"
  using assms someI_ex[OF conjunct1[OF QKM_int_degree_pos[OF assms]]] by (simp add: Qint_def)

text \<open>Theorem 1.1 for the real number zeta5.\<close>
theorem zeta5_irrational_real: "zeta5 \<notin> \<rat>"
proof (rule irrational_of_int_poly_approx[where c = "139 / 5" and d = 37 and Qs = Qint])
  show "0 < (139 / 5 :: real)" by simp
  show "degree (Qint n) \<le> 37 * n" for n
  proof (cases "StdHyp (40 * n) 200")
    case True
    have "degree (QKM (40 * n) 200) = hof (40 * n)" using QKM_int_degree_pos[OF True] by blast
    moreover have "degree (map_poly of_int (Qint n) :: rat poly) = degree (Qint n)"
      by (rule degree_map_poly) simp
    ultimately show ?thesis using Qint_spec[OF True] by (simp add: hof_def)
  next
    case False
    thus ?thesis by (simp add: Qint_def)
  qed
  show "\<forall>\<^sub>F n in at_top. 0 < poly (map_poly of_int (Qint n)) zeta5 \<and>
          poly (map_poly of_int (Qint n)) zeta5 < exp (- (139 / 5 * real n ^ 2))"
  proof -
    have "\<forall>\<^sub>F n in at_top. (200000 :: nat) \<le> n" by (rule eventually_ge_at_top)
    with QKM_zeta5_decay show ?thesis
    proof eventually_elim
      case (elim n)
      hence h: "StdHyp (40 * n) 200" by (auto simp: StdHyp_def)
      have "real_eval (QKM (40 * n) 200) zeta5 = poly (map_poly of_int (Qint n)) zeta5"
        unfolding Qint_spec[OF h, symmetric] real_eval_def
        by (simp add: map_poly_map_poly o_def)
      thus ?case using elim by simp
    qed
  qed
qed

text \<open>Theorem 1.1, stated for the AFP's zeta: @{text "\<zeta>(5) \<notin> \<rat>"}.\<close>
theorem zeta5_irrational: "zeta 5 \<notin> \<rat>"
  using zeta5_irrational_real by (simp add: zeta5_eq)

corollary Re_zeta5_irrational: "Re (zeta 5) \<notin> \<rat>"
  using zeta5_irrational_real by (simp add: zeta5_def)

text \<open>Sanity check of the statement: @{text "zeta 5"} is the familiar series
  @{text "\<Sum>_{n\<ge>1} n^{-5}"}.\<close>
lemma zeta5_series: "zeta 5 = (\<Sum>n. 1 / of_nat (Suc n) ^ 5)"
  using zeta_nat_conv_suminf[of 5] by simp

end
