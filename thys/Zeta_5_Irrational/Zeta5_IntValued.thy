(*  Title:   Zeta5_IntValued.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_IntValued
  imports Zeta5_Functionals
begin

section \<open>Integer-valued polynomials and the bound (3.9)\<close>

text \<open>Binomial polynomials, forward differences and Newton interpolation,
  used as a self-contained
  replacement for the \<open>\<int>\<^sub>p\<close>-analytic arguments of Section 3.3 of the paper:
    values at integers with
  valuation bounds give coefficient bounds ((3.8) and (3.9), @{text tau_vge_of_values},
  @{text diffQuot_vge}).  Lean theory @{text IntValued}.\<close>

lemma IntValuedAt_vge: "IntValuedAt p A \<Longrightarrow> vge p (poly A (of_int x)) 0"
  by (simp add: IntValuedAt_def vge_def)

subsection \<open>Binomial polynomials\<close>

text \<open>@{text "binom(x, k) = x(x-1)\<cdots>(x-k+1)/k!"}.\<close>
definition bp :: "nat \<Rightarrow> rat poly" where
  "bp k = Polynomial.smult (1 / fact k) (\<Prod> i < k. pX - [:of_nat i:])"

lemma bp_0: "bp 0 = 1"
  by (simp add: bp_def)

lemma bp_Suc: "bp (Suc k) = Polynomial.smult (1 / (of_nat k + 1)) (bp k * (pX - [:of_nat k:]))"
  unfolding bp_def prod.lessThan_Suc
  by (simp add: fact_Suc smult_smult mult_smult_left mult.commute add.commute)

lemma degree_bp_le: "degree (bp k) \<le> k"
proof (induction k)
  case 0
  thus ?case by (simp add: bp_0)
next
  case (Suc k)
  have "degree (bp (Suc k)) \<le> degree (bp k * (pX - [:of_nat k:]))"
    unfolding bp_Suc by (rule degree_smult_le)
  also have "\<dots> \<le> degree (bp k) + degree (pX - [:of_nat k:])" by (rule degree_mult_le)
  also have "\<dots> \<le> Suc k" unfolding degree_pX_minus_const using Suc.IH by simp
  finally show ?case .
qed

text \<open>@{text "binom(x, k)"} is HOL's @{const gbinomial}.\<close>
lemma poly_bp: "poly (bp k) a = a gchoose k"
  by (simp add: bp_def poly_prod gbinomial_prod_rev atLeast0LessThan poly_monom)

text \<open>@{text "binom(n, k)"} at naturals.\<close>
lemma bp_eval_nat: "poly (bp k) (of_nat n) = of_nat (n choose k)"
  by (simp add: poly_bp binomial_gbinomial)

text \<open>@{text "binom(-(t+1), k) = (-1)^k binom(t+k, k)"}.\<close>
lemma bp_eval_neg: "poly (bp k) (- (of_nat t + 1)) = (-1) ^ k * of_nat ((t + k) choose k)"
  unfolding poly_bp gbinomial_minus by (simp add: binomial_gbinomial)

text \<open>Binomial polynomials are integer-valued on @{text \<int>}.\<close>
lemma bp_eval_int: "\<exists>z::int. poly (bp k) (of_int m) = of_int z"
proof (cases "0 \<le> m")
  case True
  then obtain n where n: "m = int n" by (metis nonneg_int_cases)
  have "poly (bp k) (of_int m) = of_int (int (n choose k))" unfolding n by (simp add: bp_eval_nat)
  thus ?thesis by blast
next
  case False
  then obtain t where t: "m = - (int t + 1)" by (intro that[of "nat (- m - 1)"]) simp
  have "poly (bp k) (of_int m) = of_int ((-1) ^ k * int ((t + k) choose k))"
    unfolding t using bp_eval_neg[of k t] by simp
  thus ?thesis by blast
qed

text \<open>Two polynomials agreeing on all naturals are equal.\<close>
lemma poly_eq_of_eval_nat:
  fixes P Q :: "rat poly"
  assumes "\<And>n::nat. poly P (of_nat n) = poly Q (of_nat n)"
  shows "P = Q"
proof (rule ccontr)
  assume "P \<noteq> Q"
  hence "P - Q \<noteq> 0" by simp
  hence fin: "finite {x. poly (P - Q) x = 0}" by (rule poly_roots_finite)
  have "range (of_nat :: nat \<Rightarrow> rat) \<subseteq> {x. poly (P - Q) x = 0}" using assms
    by auto
  hence "finite (range (of_nat :: nat \<Rightarrow> rat))" using fin finite_subset by blast
  moreover have "inj (of_nat :: nat \<Rightarrow> rat)" by (simp add: inj_on_def)
  ultimately show False using finite_imageD infinite_UNIV_nat by blast
qed

text \<open>Pascal: @{text "\<Delta> binom(x, k+1) = binom(x, k)"}.\<close>
lemma bp_fwd: "pcompose (bp (Suc k)) (pX + 1) - bp (Suc k) = bp k"
  by (rule poly_eq_of_eval_nat) (simp add: poly_pcompose poly_bp poly_monom gbinomial_Suc_Suc)

text \<open>@{text "binom(x, k+1) = (x/(k+1)) binom(x-1, k)"}.\<close>
lemma bp_shift: "bp (Suc k) = Polynomial.smult (1 / (of_nat k + 1)) (pX * pcompose (bp k) (pX - 1))"
  by (rule poly_eq_of_eval_nat)
    (simp add: poly_pcompose poly_bp poly_monom gbinomial_absorption'[of "Suc k"] add.commute)

text \<open>@{text "\<tau>(binom(x, k)) = [x^4] binom(x, k+1)"}.\<close>
lemma tau_bp: "tau (bp k) = Polynomial.coeff (bp (Suc k)) 4"
  using tau_fwd[of "bp (Suc k)"] unfolding bp_fwd .

subsection \<open>The coefficients of @{text "binom(x, n)"}\<close>

text \<open>Weighted Gauss bound: @{text "v_p(coeff_m P) \<ge> -m c"}.\<close>
definition WB :: "nat \<Rightarrow> rat \<Rightarrow> rat poly \<Rightarrow> bool" where
  "WB p c P \<longleftrightarrow> (\<forall>m. vge p (Polynomial.coeff P m) (- of_nat m * c))"

lemma WB_mul: "prime p \<Longrightarrow> WB p c P \<Longrightarrow> WB p c Q \<Longrightarrow>
  WB p c (P * Q)"
proof -
  assume p: "prime p" and hP: "WB p c P" and hQ: "WB p c Q"
  show "WB p c (P * Q)" unfolding WB_def
  proof
    fix m
    have "vge p (\<Sum>i\<le>m. Polynomial.coeff P i * Polynomial.coeff Q (m - i)) (- of_nat m * c)"
    proof (rule vge_sum[OF p])
      fix i assume "i \<in> {..m}"
      hence eq: "- of_nat i * c + - of_nat (m - i) * c = - of_nat m * c"
        by (simp add: of_nat_diff algebra_simps)
      have "vge p (Polynomial.coeff P i * Polynomial.coeff Q (m - i)) (- of_nat i * c + -
        of_nat (m - i) * c)"
        using hP hQ unfolding WB_def by (intro vge_mul[OF p]) auto
      thus "vge p (Polynomial.coeff P i * Polynomial.coeff Q (m - i)) (- of_nat m * c)"
        by (simp only: eq)
    qed simp
    thus "vge p (Polynomial.coeff (P * Q) m) (- of_nat m * c)" by (simp add: coeff_mult)
  qed
qed

lemma WB_one: "WB p c 1"
  by (auto simp: WB_def coeff_1 vge_one vge_zero)

lemma WB_prod:
  "prime p \<Longrightarrow> finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow>
    WB p c (f i)) \<Longrightarrow> WB p c (\<Prod> i \<in> I. f i)"
proof -
  assume p: "prime p" and fin: "finite I" and h: "\<And>i. i \<in> I \<Longrightarrow> WB p c (f i)"
  show "WB p c (\<Prod> i \<in> I. f i)"
    using fin h by (induction I rule: finite_induct) (auto intro: WB_one WB_mul[OF p])
qed

text \<open>@{text "u X - v"} with @{text "v_p(u) \<ge> -c"}, @{text "v_p(v) \<ge> 0"}.\<close>
lemma WB_linear: "prime p \<Longrightarrow> vge p u (- c) \<Longrightarrow>
  vge p v 0 \<Longrightarrow> WB p c [:- v, u:]"
  by (auto simp: WB_def coeff_pCons vge_neg vge_zero split: nat.split)

lemma poly_bp_factor:
  fixes a :: rat
  shows "poly ([:0, 1 / (of_nat m + 1):] * (\<Prod> i < m. [:- 1, 1 / (of_nat i + 1):])) a =
    a gchoose Suc m"
proof (induction m)
  case 0
  thus ?case by simp
next
  case (Suc m)
  define P where "P = poly (\<Prod> i < m. [:- 1, 1 / (of_nat i + 1):]) a"
  have IH: "a / (of_nat m + 1) * P = a gchoose Suc m" using Suc.IH by (simp add: P_def)
  have h1: "(1 + of_nat m :: rat) \<noteq> 0" and h2: "(of_nat m + 2 :: rat) \<noteq> 0"
    and h3: "(2 + of_nat m :: rat) \<noteq> 0" and h4: "(of_nat m + 1 :: rat) \<noteq> 0"
      by simp_all
  have e: "(of_nat (Suc m) + 1 :: rat) = of_nat m + 2" by simp
  have "poly ([:0, 1 / (of_nat (Suc m) + 1):] * (\<Prod> i < Suc m. [:- 1, 1 / (of_nat i + 1):])) a
      = poly [:0, 1 / (of_nat (Suc m) + 1):] a * (P * poly [:- 1, 1 / (of_nat m + 1):] a)"
    by (simp only: prod.lessThan_Suc poly_mult P_def)
  also have "\<dots> = a / (of_nat m + 2) * (P * (a / (of_nat m + 1) - 1))"
    unfolding e by simp
  also have "\<dots> = (a / (of_nat m + 1) * P) * ((a - of_nat (Suc m)) / (of_nat (Suc m) + 1))"
    unfolding e using h1 h2 h3 h4 by (simp add: field_simps)
  also have "\<dots> = a gchoose Suc (Suc m)" unfolding IH by (rule gbinomial_Suc_rec[symmetric])
  finally show ?case .
qed

text \<open>@{text "binom(x, m+1) = (x/(m+1)) \<Prod>_{i<m} (x/(i+1) - 1)"}.\<close>
lemma bp_factor: "bp (Suc m) = [:0, 1 / (of_nat m + 1):] * (\<Prod> i <
  m. [:- 1, 1 / (of_nat i + 1):])"
  by (rule poly_eq_of_eval_nat) (simp only: poly_bp poly_bp_factor)

text \<open>@{text "v_p([x^4] binom(x, n)) \<ge> -4\<lfloor>log_p n\<rfloor>"}.\<close>
lemma bp_coeff4:
  assumes p: "prime p"
  shows "vge p (Polynomial.coeff (bp n) 4) (- 4 * of_nat (nat_log p n))"
proof (cases n)
  case 0
  thus ?thesis by (simp add: bp_0 vge_zero)
next
  case (Suc m)
  have "WB p (of_nat (nat_log p (Suc m))) (bp (Suc m))"
    unfolding bp_factor
  proof (intro WB_mul[OF p] WB_prod[OF p])
    have u: "vge p (1 / (of_nat m + 1)) (- of_nat (nat_log p (Suc m)))"
      using vge_inv_nat[OF p, of "Suc m"] by (simp add: add.commute)
    show "WB p (of_nat (nat_log p (Suc m))) [:0, 1 / (of_nat m + 1):]"
      using WB_linear[OF p u vge_zero[of p 0]] by simp
    show "finite {..<m}" by simp
    fix i assume "i \<in> {..<m}"
    have u: "vge p (1 / (of_nat i + 1)) (- of_nat (nat_log p (Suc i)))"
      using vge_inv_nat[OF p, of "Suc i"] by (simp add: add.commute)
    have "nat_log p (Suc i) \<le> nat_log p (Suc m)" using \<open>i \<in> {..<m}\<close>
      by (intro nat_log_mono) simp
    hence u': "vge p (1 / (of_nat i + 1)) (- of_nat (nat_log p (Suc m)))"
      by (intro vge_mono[OF u]) simp
    show "WB p (of_nat (nat_log p (Suc m))) [:- 1, 1 / (of_nat i + 1):]"
      using WB_linear[OF p u' vge_one] .
  qed
  thus ?thesis unfolding Suc WB_def
    by (auto dest: spec[of _ 4])
qed

subsection \<open>Newton interpolation\<close>

text \<open>Forward differences @{text "\<Delta>^k f(y)"} with step 1.\<close>
fun fd :: "rat poly \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> rat" where
  "fd f y 0 = poly f y"
| "fd f y (Suc k) = fd f (y + 1) k - fd f y k"

lemma fd_vge:
  assumes "prime p" "\<And>i. i \<le> k \<Longrightarrow> vge p (poly f (y + of_nat i)) b"
  shows "vge p (fd f y k) b"
  using assms(2)
proof (induction k arbitrary: y)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have 1: "vge p (fd f (y + 1) k) b"
  proof (rule Suc.IH)
    fix i assume "i \<le> k"
    hence "vge p (poly f (y + of_nat (Suc i))) b" by (intro Suc.prems) simp
    thus "vge p (poly f (y + 1 + of_nat i)) b" by (simp add: add_ac)
  qed
  have 2: "vge p (fd f y k) b"
    by (rule Suc.IH) (use Suc.prems in simp)
  show ?case using vge_add[OF assms(1) 1 vge_neg[OF 2]] by simp
qed

text \<open>@{text "f(y + n) = \<Sum>_{k \<le> n} C(n, k) \<Delta>^k f(y)"}.\<close>
lemma newton_eval: "poly f (y + of_nat n) = (\<Sum> k \<le> n. of_nat (n choose k) * fd f y k)"
proof (induction n arbitrary: y)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have "poly f (y + of_nat (Suc n)) = poly f ((y + 1) + of_nat n)" by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum> k \<le> n. of_nat (n choose k) * fd f (y + 1) k)" by (rule Suc.IH)
  also have "\<dots> = (\<Sum> k \<le> n. of_nat (n choose k) * (fd f y (Suc k) + fd f y k))"
    by simp
  also have "\<dots> = (\<Sum> k \<le> Suc n. of_nat (Suc n choose k) * fd f y k)"
  proof -
    have "(\<Sum>k\<le>Suc n. of_nat (n choose k) * fd f y k)
        = fd f y 0 + (\<Sum>k\<le>n. of_nat (n choose Suc k) * fd f y (Suc k))"
      by (subst sum.atMost_Suc_shift) (simp del: fd.simps)
    moreover have "(\<Sum>k\<le>Suc n. of_nat (n choose k) * fd f y k) =
      (\<Sum>k\<le>n. of_nat (n choose k) * fd f y k)"
      by (simp add: binomial_eq_0 del: fd.simps)
    moreover have "(\<Sum>k\<le>Suc n. of_nat (Suc n choose k) * fd f y k)
        = fd f y 0 + (\<Sum>k\<le>n. of_nat (n choose k) * fd f y (Suc k))
            + (\<Sum>k\<le>n. of_nat (n choose Suc k) * fd f y (Suc k))"
      by (subst sum.atMost_Suc_shift) (simp add: sum.distrib algebra_simps del: fd.simps)
    moreover have "(\<Sum> k \<le> n. of_nat (n choose k) * (fd f y (Suc k) + fd f y k))
        = (\<Sum>k\<le>n. of_nat (n choose k) * fd f y (Suc k)) +
          (\<Sum>k\<le>n. of_nat (n choose k) * fd f y k)"
      unfolding distrib_left sum.distrib ..
    ultimately show ?thesis by linarith
  qed
  finally show ?case .
qed

text \<open>Newton's forward-difference formula as a polynomial identity.\<close>
lemma newton:
  assumes "degree f \<le> D"
  shows "f = (\<Sum> k \<le> D. [:fd f y k:] * pcompose (bp k) (pX - [:y:]))"
proof -
  let ?g = "(\<Sum> k \<le> D. [:fd f y k:] * pcompose (bp k) (pX - [:y:]))"
  have dg: "degree ?g \<le> D"
  proof (rule degree_sum_le)
    fix k assume kD: "k \<in> {..D}"
    have "degree ([:fd f y k:] * pcompose (bp k) (pX - [:y:]))
        \<le> degree [:fd f y k:] + degree (pcompose (bp k) (pX - [:y:]))" by (rule degree_mult_le)
    also have "\<dots> = degree (bp k)" unfolding degree_pcompose degree_pX_minus_const by simp
    also have "\<dots> \<le> D" using degree_bp_le[of k] kD by simp
    finally show "degree ([:fd f y k:] * pcompose (bp k) (pX - [:y:])) \<le> D" .
  qed simp
  have agree: "\<And>n. n \<le> D \<Longrightarrow> poly ?g (y + of_nat n) = poly f (y + of_nat n)"
  proof -
    fix n assume nD: "n \<le> D"
    have "poly ?g (y + of_nat n) = (\<Sum>k\<le>D. of_nat (n choose k) * fd f y k)"
      by (simp add: poly_sum poly_pcompose poly_monom bp_eval_nat mult.commute)
    also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * fd f y k)"
      by (rule sum.mono_neutral_right) (use nD in \<open>auto simp: binomial_eq_0\<close>)
    also have "\<dots> = poly f (y + of_nat n)" by (rule newton_eval[symmetric])
    finally show "poly ?g (y + of_nat n) = poly f (y + of_nat n)" .
  qed
  have "f - ?g = 0"
  proof (rule poly_eq_0_of_roots)
    show "finite ((\<lambda>n. y + of_nat n) ` {..D})" by simp
    have "inj_on (\<lambda>n::nat. y + of_nat n) {..D}" by (simp add: inj_on_def)
    hence "card ((\<lambda>n. y + of_nat n) ` {..D}) = Suc D" by (simp add: card_image)
    moreover have "degree (f - ?g) \<le> D" using degree_diff_le[OF assms dg] .
    ultimately show "degree (f - ?g) < card ((\<lambda>n. y + of_nat n) ` {..D})" by simp
  next
    fix s assume "s \<in> (\<lambda>n. y + of_nat n) ` {..D}"
    then obtain n where "n \<le> D" "s = y + of_nat n" by auto
    thus "poly (f - ?g) s = 0" using agree by simp
  qed
  thus ?thesis by simp
qed

lemma pcompose_pX_minus_0: "pcompose P (pX - [:0:]) = P"
  unfolding pX_minus_const by (simp add: pcompose_idR)

subsection \<open>(3.9) and (3.8)\<close>

text \<open>(3.9), in the form used: if @{text "deg f \<le> D"} and @{text f} is
  @{text "p^{-a}"}-integral at
  @{text "D+1"} consecutive integers, then
    @{text "v_p(\<tau>(f)) \<ge> -a - 4\<lfloor>log_p(D+1)\<rfloor>"}
  (Lean: @{text tau_vge_of_values}; the paper's @{text "-v_p(24)"} term is not needed).\<close>
theorem tau_vge_of_values:
  assumes p: "prime p" and dfD: "degree f \<le> D"
    and hv: "\<And>i. i \<le> D \<Longrightarrow> vge p (poly f (of_int y + of_nat i)) (- a)"
  shows "vge p (tau f) (- a - 4 * of_nat (nat_log p (D + 1)))"
proof -
  \<comment> \<open>the bound spreads from @{text "D + 1"} consecutive integers to all
    integers\<close>
  have hall: "\<And>m::int. vge p (poly f (of_int m)) (- a)"
  proof -
    fix m :: int
    have fdv: "\<And>k. k \<le> D \<Longrightarrow> vge p (fd f (of_int y) k) (- a)"
      by (rule fd_vge[OF p]) (use hv in simp)
    have "poly f (of_int m) = (\<Sum> k \<le> D. fd f (of_int y) k * poly (bp k) (of_int (m - y)))"
    proof -
      have N: "f = (\<Sum> k \<le> D. [:fd f (of_int y) k:] * pcompose (bp k) (pX - [:of_int y:]))"
        by (rule newton[OF dfD])
      have "poly f (of_int m)
          = poly (\<Sum> k \<le> D. [:fd f (of_int y) k:] * pcompose (bp k) (pX -
            [:of_int y:])) (of_int m)"
        by (rule arg_cong[where f = "\<lambda>P. poly P (of_int m)", OF N])
      also have "\<dots> = (\<Sum> k \<le> D. fd f (of_int y) k * poly (bp k) (of_int (m - y)))"
        by (simp add: poly_sum poly_pcompose poly_monom)
      finally show ?thesis .
    qed
    also have "vge p \<dots> (- a)"
    proof (rule vge_sum[OF p])
      fix k assume "k \<in> {..D}"
      obtain z :: int where z: "poly (bp k) (of_int (m - y)) = of_int z" using bp_eval_int by blast
      have "k \<le> D" using \<open>k \<in> {..D}\<close> by simp
      from vge_mul[OF p fdv[OF this] vge_of_int[OF p, of z]]
      show "vge p (fd f (of_int y) k * poly (bp k) (of_int (m - y))) (- a)" unfolding z by simp
    qed simp
    finally show "vge p (poly f (of_int m)) (- a)" .
  qed
  \<comment> \<open>Newton at 0, and @{text "\<tau>(binom(x, k)) = [x^4] binom(x, k+1)"}\<close>
  have f0: "f = (\<Sum> k \<le> D. [:fd f 0 k:] * bp k)"
    using newton[OF dfD, of 0] by (simp only: pcompose_pX_minus_0)
  have tf: "tau f = (\<Sum> k \<le> D. fd f 0 k * Polynomial.coeff (bp (Suc k)) 4)"
  proof -
    have "tau f = tau (\<Sum> k \<le> D. [:fd f 0 k:] * bp k)"
      by (rule arg_cong[where f = tau, OF f0])
    also have "\<dots> = (\<Sum> k \<le> D. tau ([:fd f 0 k:] * bp k))" by (rule tau_sum)
    also have "\<dots> = (\<Sum> k \<le> D. fd f 0 k * Polynomial.coeff (bp (Suc k)) 4)"
      by (simp add: tau_smult tau_bp)
    finally show ?thesis .
  qed
  have trm: "\<And>k. k \<le> D \<Longrightarrow>
      vge p (fd f 0 k * Polynomial.coeff (bp (Suc k)) 4) (- a - 4 * of_nat (nat_log p (D + 1)))"
  proof -
    fix k assume kD: "k \<le> D"
    have 1: "vge p (fd f 0 k) (- a)"
      by (rule fd_vge[OF p]) (use hall[of "int i" for i] in simp)
    have 2: "vge p (Polynomial.coeff (bp (Suc k)) 4) (- 4 * of_nat (nat_log p (Suc k)))"
      by (rule bp_coeff4[OF p])
    have "nat_log p (Suc k) \<le> nat_log p (D + 1)" using kD by (intro nat_log_mono) simp
    hence "- a - 4 * of_nat (nat_log p (D + 1)) \<le> - a + - 4 * of_nat (nat_log p (Suc k))"
      by simp
    thus "vge p (fd f 0 k * Polynomial.coeff (bp (Suc k)) 4) (- a - 4 * of_nat (nat_log p (D + 1)))"
      by (rule vge_mono[OF vge_mul[OF p 1 2]])
  qed
  show ?thesis unfolding tf by (rule vge_sum[OF p]) (use trm in auto)
qed

text \<open>(3.8): difference quotients of integer-valued polynomials of degree @{text "\<le> d"}
  lose at most
  @{text "\<lfloor>log_p max(1, d)\<rfloor>"} (Lean: @{text diffQuot_vge}).\<close>
theorem diffQuot_vge:
  assumes p: "prime p" and A: "IntValuedAt p A" and dA: "degree A \<le> d" and nr: "n \<noteq> r"
  shows "vge p ((poly A (of_int n) - poly A (of_int r)) / (of_int n - of_int r))
             (- of_nat (nat_log p (max 1 d)))"
proof -
  define A' where "A' = pcompose A (pX + [:of_int r:])"
  have dA': "degree A' \<le> d"
    unfolding A'_def degree_pcompose degree_pX_plus_const using dA by simp
  have valA': "\<And>m::int. vge p (poly A' (of_int m)) 0"
  proof -
    fix m :: int
    have "poly A' (of_int m) = poly A (of_int (m + r))"
      by (simp add: A'_def poly_pcompose poly_monom)
    thus "vge p (poly A' (of_int m)) 0" using IntValuedAt_vge[OF A, of "m + r"] by simp
  qed
  define u where "u = of_int n - (of_int r :: rat)"
  have u0: "u \<noteq> 0" using nr by (simp add: u_def)
  have An: "poly A (of_int n) = poly A' u" and Ar: "poly A (of_int r) = poly A' 0"
    by (simp_all add: A'_def u_def poly_pcompose poly_monom)
  have N: "A' = (\<Sum> k \<le> d. [:fd A' 0 k:] * bp k)"
    using newton[OF dA', of 0] by (simp only: pcompose_pX_minus_0)
  have split: "(poly A' u - poly A' 0) / u =
      (\<Sum> k \<le> d. fd A' 0 k * ((poly (bp k) u - poly (bp k) 0) / u))"
  proof -
    have h: "poly A' x = (\<Sum>k\<le>d. fd A' 0 k * poly (bp k) x)" for x
    proof -
      have "poly A' x = poly (\<Sum> k \<le> d. [:fd A' 0 k:] * bp k) x"
        by (rule arg_cong[where f = "\<lambda>P. poly P x", OF N])
      thus ?thesis by (simp add: poly_sum)
    qed
    show ?thesis unfolding h[of u] h[of 0]
      by (simp add: sum_subtractf sum_divide_distrib right_diff_distrib diff_divide_distrib)
  qed
  have trm: "\<And>k. k \<le> d \<Longrightarrow>
      vge p (fd A' 0 k * ((poly (bp k) u - poly (bp k) 0) / u)) (- of_nat (nat_log p (max 1 d)))"
  proof -
    fix k assume kd: "k \<le> d"
    show "vge p (fd A' 0 k * ((poly (bp k) u - poly (bp k) 0) /
      u)) (- of_nat (nat_log p (max 1 d)))"
    proof (cases k)
      case 0
      thus ?thesis by (simp add: bp_0 vge_zero)
    next
      case (Suc j)
      have s: "poly (bp (Suc j)) x = 1 / (of_nat j + 1) * (x * poly (bp j) (x - 1))" for x
        by (subst bp_shift) (simp add: poly_pcompose poly_monom)
      have e: "(poly (bp (Suc j)) u - poly (bp (Suc j)) 0) / u =
        1 / (of_nat j + 1) * poly (bp j) (u - 1)"
        unfolding s using u0 by simp
      obtain z :: int where z: "poly (bp j) (u - 1) = of_int z"
        using bp_eval_int[of j "n - r - 1"] by (auto simp: u_def)
      have 1: "vge p (fd A' 0 (Suc j)) 0"
        by (rule fd_vge[OF p]) (use valA'[of "int i" for i] in simp)
      have 2: "vge p (1 / (of_nat j + 1)) (- of_nat (nat_log p (Suc j)))"
        using vge_inv_nat[OF p, of "Suc j"] by (simp add: add.commute)
      have 3: "nat_log p (Suc j) \<le> nat_log p (max 1 d)" using kd Suc
        by (intro nat_log_mono) simp
      show ?thesis unfolding Suc e z
        by (rule vge_mono[OF vge_mul[OF p 1 vge_mul[OF p 2 vge_of_int[OF p,
          of z]]]]) (use 3 in simp)
    qed
  qed
  have "vge p ((poly A' u - poly A' 0) / u) (- of_nat (nat_log p (max 1 d)))"
    unfolding split by (rule vge_sum[OF p]) (use trm in auto)
  thus ?thesis unfolding An Ar u_def .
qed

end

