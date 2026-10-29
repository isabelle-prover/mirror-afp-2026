(*  Title:   Zeta5_Small_Primes.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Small_Primes
  imports Zeta5_Far_Poles
begin

section \<open>The small-prime bound (3.12)\<close>

text \<open>Section 3.3 of the paper: the basis polynomials \<open>f\<^sub>i(-x\<^sup>2)\<close> are
  integer-valued, the determinant
  identity (3.11), and the small-prime bound (3.12) derived from Lemma 3.3.  Lean theory
  @{text SmallPrimes}.\<close>

subsection \<open>Section 3.3 Integer-valued basis polynomials\<close>

text \<open>@{text A} takes integer values at integers.\<close>
definition IntEval :: "rat poly \<Rightarrow> bool" where
  "IntEval A \<longleftrightarrow> (\<forall>x::int. \<exists>z::int. poly A (of_int x) = of_int z)"

lemma IntEval_IntValuedAt: "prime p \<Longrightarrow> IntEval A \<Longrightarrow> IntValuedAt p A"
proof -
  assume "prime p" and A: "IntEval A"
  show ?thesis unfolding IntValuedAt_def vp_def
  proof (intro allI impI)
    fix x :: int
    obtain z :: int where z: "poly A (of_int x) = of_int z" using A unfolding IntEval_def by blast
    show "0 \<le> qmultiplicity (int p) (poly A (of_int x))" unfolding z qmultiplicity_of_int
      by simp
  qed
qed

lemma IntEval_mult: "IntEval A \<Longrightarrow> IntEval B \<Longrightarrow> IntEval (A * B)"
proof -
  assume A: "IntEval A" and B: "IntEval B"
  show ?thesis unfolding IntEval_def
  proof
    fix x :: int
    obtain a b :: int where "poly A (of_int x) = of_int a" "poly B (of_int x) = of_int b"
      using A B unfolding IntEval_def by blast
    thus "\<exists>z::int. poly (A * B) (of_int x) = of_int z" by (intro exI[of _ "a * b"]) simp
  qed
qed

lemma IntEval_power: "IntEval A \<Longrightarrow> IntEval (A ^ n)"
proof (induction n)
  case 0
  have "IntEval 1" unfolding IntEval_def by (auto intro!: exI[of _ 1])
  thus ?case by simp
next
  case (Suc n)
  have "IntEval (A ^ n)" using Suc by simp
  thus ?case unfolding power_Suc by (rule IntEval_mult[OF Suc.prems])
qed

lemma IntEval_add: "IntEval A \<Longrightarrow> IntEval B \<Longrightarrow> IntEval (A + B)"
proof -
  assume A: "IntEval A" and B: "IntEval B"
  show ?thesis unfolding IntEval_def
  proof
    fix x :: int
    obtain a b :: int where "poly A (of_int x) = of_int a" "poly B (of_int x) = of_int b"
      using A B unfolding IntEval_def by blast
    thus "\<exists>z::int. poly (A + B) (of_int x) = of_int z" by (intro exI[of _ "a + b"]) simp
  qed
qed

lemma IntEval_C_int: "IntEval [:of_int z:]"
  by (simp add: IntEval_def)

lemma IntEval_pX: "IntEval pX"
  unfolding IntEval_def by (simp add: poly_monom)

text \<open>@{text "binom(s x + m, k)"} is integer-valued (@{text "s, m \<in> \<int>"}).\<close>
lemma IntEval_bp_pcompose: "IntEval (pcompose (bp k) [:of_int m, of_int s:])"
  unfolding IntEval_def
proof
  fix x :: int
  have e: "poly [:of_int m, of_int s:] (of_int x) = (of_int (m + x * s) :: rat)" by simp
  obtain z :: int where "poly (bp k) (of_int (m + x * s)) = of_int z" using bp_eval_int by blast
  thus "\<exists>z::int. poly (pcompose (bp k) [:of_int m, of_int s:]) (of_int x) = of_int z"
    unfolding poly_pcompose e by blast
qed

lemma poly_bp: "poly (bp k) y = (\<Prod> i < k. y - of_nat i) / fact k"
  unfolding bp_def by (simp add: poly_prod poly_monom)

text \<open>@{text "\<Prod>_{j=1}^N (j^2 - x^2) = \<Prod>_{k<N} (N - k - x)(x + N - k)"}.\<close>
lemma prod_Icc_sq_sub:
  "(\<Prod> j = 1..N. - (x ^ 2) + of_nat j ^ 2) = (\<Prod> k <
    N. (of_nat N - x - of_nat k) * (x + of_nat N - of_nat k) :: rat)"
proof -
  have "(\<Prod> j = 1..N. - (x ^ 2) + of_nat j ^ 2) = (\<Prod> k <
    N. - (x ^ 2) + of_nat (N - k) ^ 2)"
    by (rule prod.reindex_bij_witness[where i = "\<lambda>k. N - k" and j =
      "\<lambda>j. N - j"]) auto
  also have "\<dots> = (\<Prod> k < N. (of_nat N - x - of_nat k) * (x + of_nat N - of_nat k))"
    by (intro prod.cong refl) (simp add: of_nat_diff power2_eq_square algebra_simps)
  finally show ?thesis .
qed

text \<open>@{text "D_N(-x^2)/(N!)^2 = binom(N - x, N) binom(N + x, N)"}.\<close>
lemma Dm_pcompose_eq:
  "Polynomial.smult (1 / fact N ^ 2) (pcompose (Dm N) (- (pX ^ 2))) =
     pcompose (bp N) [:of_nat N, - 1:] * pcompose (bp N) [:of_nat N, 1:]"
proof -
  have l: "poly (Dm N) y = (\<Prod> j = 1..N. y + of_nat j ^ 2)" for y
    unfolding Dm_def poly_prod by (rule prod.cong) (simp_all add: poly_monom)
  have e: "poly (Polynomial.smult (1 / fact N ^ 2) (pcompose (Dm N) (- (pX ^ 2)))) x =
      poly (pcompose (bp N) [:of_nat N, - 1:] * pcompose (bp N) [:of_nat N, 1:]) x" for x :: rat
  proof -
    have r: "(\<Prod> k < N. of_nat N + x - of_nat k) = (\<Prod> k < N. x + of_nat N - of_nat k)"
      by (simp add: add.commute)
    have "poly (Polynomial.smult (1 / fact N ^ 2) (pcompose (Dm N) (- (pX ^ 2)))) x =
        1 / fact N ^ 2 * poly (Dm N) (- (x ^ 2))"
      by (simp add: poly_pcompose poly_monom)
    also have "\<dots> = 1 / fact N ^ 2 * (\<Prod> k <
      N. (of_nat N - x - of_nat k) * (x + of_nat N - of_nat k))"
      unfolding l prod_Icc_sq_sub ..
    also have "\<dots> = (\<Prod> k < N. of_nat N - x - of_nat k) / fact N * ((\<Prod> k <
      N. x + of_nat N - of_nat k) / fact N)"
      by (simp add: prod.distrib power2_eq_square)
    also have "\<dots> = poly (bp N) (of_nat N - x) * poly (bp N) (of_nat N + x)"
      unfolding poly_bp r ..
    also have "\<dots> = poly (pcompose (bp N) [:of_nat N, - 1:] * pcompose (bp N) [:of_nat N,
      1:]) x"
      by (simp add: poly_pcompose)
    finally show ?thesis .
  qed
  show ?thesis by (rule poly_eq_of_eval_nat) (rule e)
qed

lemma IntEval_Dm_pcompose: "IntEval (Polynomial.smult (1 /
  fact N ^ 2) (pcompose (Dm N) (- (pX ^ 2))))"
  unfolding Dm_pcompose_eq
  by (intro IntEval_mult IntEval_bp_pcompose[of N "int N" "- 1",
    simplified] IntEval_bp_pcompose[of N "int N" 1, simplified])

lemma E1_eq:
  "(\<Prod> k < 2 * m + 2. x + (of_nat m + 1) - of_nat k) = (x + of_nat m + 1) * x * (\<Prod> j =
    1..m. x ^ 2 - of_nat j ^ 2 :: rat)"
proof (induction m)
  case 0
  show ?case by (simp add: numeral_2_eq_2 algebra_simps)
next
  case (Suc m)
  have e: "2 * Suc m + 2 = Suc (Suc (2 * m + 2))" by simp
  have mid: "(\<Prod> i < 2 * m + 2. x + (of_nat (Suc m) + 1) - of_nat (Suc i)) =
      (\<Prod> k < 2 * m + 2. x + (of_nat m + 1) - of_nat k)"
    by (rule prod.cong[OF refl]) (simp add: algebra_simps)
  show ?case
    by (subst e, subst prod.lessThan_Suc, subst prod.lessThan_Suc_shift,
      unfold mid Suc.IH prod.cl_ivl_Suc)
      (simp add: algebra_simps power2_eq_square)
qed

lemma E2_eq:
  "(\<Prod> k < 2 * m + 2. x + of_nat m - of_nat k) = x * (x - of_nat m - 1) * (\<Prod> j =
    1..m. x ^ 2 - of_nat j ^ 2 :: rat)"
proof (induction m)
  case 0
  show ?case by (simp add: numeral_2_eq_2 algebra_simps)
next
  case (Suc m)
  have e: "2 * Suc m + 2 = Suc (Suc (2 * m + 2))" by simp
  have mid: "(\<Prod> i < 2 * m + 2. x + of_nat (Suc m) - of_nat (Suc i)) =
      (\<Prod> k < 2 * m + 2. x + of_nat m - of_nat k)"
    by (rule prod.cong[OF refl]) (simp add: algebra_simps)
  show ?case
    by (subst e, subst prod.lessThan_Suc, subst prod.lessThan_Suc_shift,
      unfold mid Suc.IH prod.cl_ivl_Suc)
      (simp add: algebra_simps power2_eq_square)
qed

text \<open>@{text "q_{m+1}(-x^2) = binom(x + m + 1, 2m + 2) + binom(x + m, 2m + 2)"}.\<close>
lemma qBasis_pcompose_eq:
  "pcompose (qBasis (Suc m)) (- (pX ^ 2)) =
     pcompose (bp (2 * m + 2)) [:of_nat m + 1, 1:] + pcompose (bp (2 * m + 2)) [:of_nat m, 1:]"
proof -
  have l: "poly (Dm m) y = (\<Prod> j = 1..m. y + of_nat j ^ 2)" for y
    unfolding Dm_def poly_prod by (rule prod.cong) (simp_all add: poly_monom)
  have e: "poly (pcompose (qBasis (Suc m)) (- (pX ^ 2))) x =
      poly (pcompose (bp (2 * m + 2)) [:of_nat m + 1, 1:] + pcompose (bp (2 * m + 2)) [:of_nat m,
        1:]) x" for x :: rat
  proof -
    define F :: rat where "F = fact (2 * Suc m)"
    define P :: rat where "P = (\<Prod> j = 1..m. x ^ 2 - of_nat j ^ 2)"
    have F2: "(fact (2 * m + 2) :: rat) = F"
    proof -
      have "2 * m + 2 = 2 * Suc m" by simp
      thus ?thesis unfolding F_def by simp
    qed
    have q: "poly (qBasis (Suc m)) y = (-1) ^ Suc m * 2 / F * y * poly (Dm m) y" for y
      unfolding F_def by (simp add: qBasis_def poly_monom)
    have neg: "(\<Prod> j = 1..m. - (x ^ 2) + of_nat j ^ 2) = (-1) ^ m * P"
    proof -
      have "(\<Prod> j = 1..m. - (x ^ 2) + of_nat j ^ 2) = (\<Prod> j =
        1..m. (-1) * (x ^ 2 - of_nat j ^ 2))"
        by (rule prod.cong) simp_all
      also have "\<dots> = (-1) ^ m * P" unfolding P_def by (subst prod.distrib) simp
      finally show ?thesis .
    qed
    have z: "poly (- (pX ^ 2)) x = - (x ^ 2)" by (simp add: poly_monom)
    have y1: "poly [:of_nat m + 1, 1:] x = x + (of_nat m + 1)" by simp
    have y2: "poly [:of_nat m, 1:] x = x + of_nat m" by simp
    have key: "(x + of_nat m + 1) * x * P + x * (x - of_nat m - 1) * P = 2 * x ^ 2 * P"
      by (simp add: algebra_simps power2_eq_square)
    have L: "(-1) ^ Suc m * 2 / F * (- (x ^ 2)) * ((-1) ^ m * P) = 2 * x ^ 2 * P / F"
      by (cases "even m") (simp_all add: neg_one_even_power neg_one_odd_power)
    have "poly (pcompose (qBasis (Suc m)) (- (pX ^ 2))) x =
      (-1) ^ Suc m * 2 / F * (- (x ^ 2)) * ((-1) ^ m * P)"
      unfolding poly_pcompose z q l neg ..
    also have "\<dots> = 2 * x ^ 2 * P / F" by (rule L)
    also have "\<dots> = (x + of_nat m + 1) * x * P / F + x * (x - of_nat m - 1) * P / F"
      unfolding add_divide_distrib[symmetric] key ..
    also have "\<dots> = poly (pcompose (bp (2 * m + 2)) [:of_nat m + 1,
      1:] + pcompose (bp (2 * m + 2)) [:of_nat m, 1:]) x"
      unfolding poly_add poly_pcompose y1 y2 poly_bp E1_eq E2_eq P_def[symmetric] F2 ..
    finally show ?thesis .
  qed
  show ?thesis by (rule poly_eq_of_eval_nat) (rule e)
qed

lemma IntEval_qBasis: "IntEval (pcompose (qBasis i) (- (pX ^ 2)))"
proof (cases i)
  case 0
  have "IntEval 1" unfolding IntEval_def by (auto intro!: exI[of _ 1])
  thus ?thesis using 0 by (simp add: qBasis_def pcompose_1)
next
  case (Suc m)
  have a: "IntEval (pcompose (bp (2 * m + 2)) [:of_nat m + 1, 1:])"
    using IntEval_bp_pcompose[of "2 * m + 2" "int m + 1" 1] by simp
  have b: "IntEval (pcompose (bp (2 * m + 2)) [:of_nat m, 1:])"
    using IntEval_bp_pcompose[of "2 * m + 2" "int m" 1] by simp
  show ?thesis unfolding Suc qBasis_pcompose_eq by (rule IntEval_add[OF a b])
qed

lemma IntEval_fBasis: "IntEval (pcompose (fBasis K i) (- (pX ^ 2)))"
proof -
  have e: "pcompose (fBasis K i) (- (pX ^ 2)) =
      (Polynomial.smult (1 / fact (Nof K) ^ 2) (pcompose (Dm (Nof K)) (- (pX ^ 2)))) ^ 3 *
        pcompose (qBasis i) (- (pX ^ 2))"
    unfolding fBasis_def pcompose_mult pcompose_power_left by (simp add: pcompose_smult)
  show ?thesis unfolding e by (intro IntEval_mult IntEval_power IntEval_Dm_pcompose IntEval_qBasis)
qed

text \<open>@{text "f_i(-x^2)"} is integer-valued (binomial identities
  @{text "q_i(-x^2) = C(x+i, 2i) + C(x+i-1, 2i)"},
    @{text "D_N(-x^2)/(N!)^2 = C(N-x, N) C(N+x, N)"}).\<close>
theorem fBasis_intValued: "prime p \<Longrightarrow>
  IntValuedAt p (pcompose (fBasis K i) (- (pX ^ 2)))"
  by (rule IntEval_IntValuedAt, assumption, rule IntEval_fBasis)

subsection \<open>The determinant identity (3.11)\<close>

lemma degree_Dm: "degree (Dm m) = m"
proof -
  have "degree (Dm m) = (\<Sum> j = 1..m. degree (pX + [:of_nat j ^ 2:]))"
    unfolding Dm_def by (rule degree_prod_eq_sum_degree) (use pX_plus_const_nonzero in blast)
  also have "\<dots> = (\<Sum> j = 1..m. 1)" by (rule sum.cong[OF refl]) (rule degree_pX_plus_const)
  also have "\<dots> = m" by simp
  finally show ?thesis .
qed

lemma lead_coeff_Dm: "lead_coeff (Dm m) = 1"
proof -
  have l: "lead_coeff (pX + [:of_nat j ^ 2:]) = 1" for j :: nat
    unfolding degree_pX_plus_const by (simp add: coeff_monom)
  show ?thesis unfolding Dm_def lead_coeff_prod l by simp
qed

lemma Dm_nonzero: "Dm m \<noteq> 0"
  using lead_coeff_Dm[of m] by auto

text \<open>The leading coefficient @{text "(-1)^i 2/(2i)!"} of @{text "q_i"} (and 1
  for @{text "i = 0"}).\<close>
definition qLead :: "nat \<Rightarrow> rat" where
  "qLead i = (if i = 0 then 1 else (-1) ^ i * 2 / fact (2 * i))"

lemma degree_qBasis_le: "degree (qBasis i) \<le> i"
proof (cases i)
  case 0
  thus ?thesis by (simp add: qBasis_def)
next
  case (Suc m)
  have q: "qBasis i = [:(-1) ^ i * 2 / fact (2 * i):] * pX * Dm m" unfolding qBasis_def using Suc
    by simp
  have "degree ([:(-1) ^ i * 2 / fact (2 * i):] * pX * Dm m) \<le>
      degree ([:(-1) ^ i * 2 / fact (2 * i):] * pX) + degree (Dm m)" by (rule degree_mult_le)
  moreover have "degree ([:(-1) ^ i * 2 / fact (2 * i):] * pX) \<le> 1"
    by (simp add: degree_monom_le)
  ultimately show ?thesis unfolding q using degree_Dm[of m] Suc by linarith
qed

lemma coeff_qBasis_self: "Polynomial.coeff (qBasis i) i = qLead i"
proof (cases i)
  case 0
  thus ?thesis by (simp add: qBasis_def qLead_def)
next
  case (Suc m)
  have "Polynomial.coeff (Dm m) m = 1" using lead_coeff_Dm[of m] unfolding degree_Dm .
  hence "Polynomial.coeff (Polynomial.monom a (Suc 0) * Dm m) (Suc m) = a" for a
    by (simp add: coeff_monom_mult)
  with Suc show ?thesis unfolding qBasis_def qLead_def by simp
qed

lemma qBasis_eq_sum:
  "i < h \<Longrightarrow> qBasis i = (\<Sum> k <
    h. Polynomial.smult (Polynomial.coeff (qBasis i) k) (pX ^ k))"
proof -
  assume ih: "i < h"
  have d: "degree (qBasis i) \<le> h - 1" using degree_qBasis_le[of i] ih by linarith
  have e: "{..h - 1} = {..<h}" using ih by auto
  have "qBasis i = (\<Sum> k \<le> h - 1. Polynomial.monom (Polynomial.coeff (qBasis i) k) k)"
    by (rule sym[OF poly_as_sum_of_monoms'[OF d]])
  also have "\<dots> = (\<Sum> k < h. Polynomial.monom (Polynomial.coeff (qBasis i) k) k)"
    unfolding e ..
  also have "\<dots> = (\<Sum> k < h. Polynomial.smult (Polynomial.coeff (qBasis i) k) (pX ^ k))"
    by (rule sum.cong[OF refl]) (unfold pX_pow_monom smult_monom, simp)
  finally show ?thesis .
qed

text \<open>The coefficient matrix of the @{text "q_i"}, lower triangular.\<close>
definition Qc :: "nat \<Rightarrow> rat mat" where
  "Qc h = Matrix.mat h h (\<lambda>(i, k). Polynomial.coeff (qBasis i) k)"

lemma Qc_carrier: "Qc h \<in> carrier_mat h h"
  by (simp add: Qc_def)

lemma det_Qc: "Determinant.det (Qc h) = (\<Prod> i < h. qLead i)"
proof -
  have "Determinant.det (Qc h) = prod_list (diag_mat (Qc h))"
  proof (rule det_lower_triangular[OF _ Qc_carrier])
    fix i j assume ij: "i < j" and jh: "j < h"
    have "degree (qBasis i) < j" using degree_qBasis_le[of i] ij by linarith
    thus "Qc h $$ (i, j) = 0" using ij jh by (simp add: Qc_def coeff_eq_0)
  qed
  also have "\<dots> = (\<Prod> i = 0..<dim_row (Qc h). Qc h $$ (i, i))"
    by (rule prod_list_diag_prod)
  also have "\<dots> = (\<Prod> i \<in> {..<h}. qLead i)"
    by (rule prod.cong) (auto simp: Qc_def coeff_qBasis_self)
  finally show ?thesis .
qed

lemma qLead_sq_prod: "(\<Prod> i < h. qLead i) ^ 2 = 4 ^ (h - 1) / (\<Prod> i =
  1..h - 1. fact (2 * i) ^ 2)"
proof (cases h)
  case 0
  thus ?thesis by simp
next
  case (Suc m)
  have sq: "qLead (Suc i) ^ 2 = 4 / fact (2 * Suc i) ^ 2" for i
    by (cases "even i") (simp_all add: qLead_def power_divide neg_one_even_power neg_one_odd_power)
  have r: "(\<Prod> i < m. fact (2 * Suc i) ^ 2) = (\<Prod> i = 1..m. fact (2 * i) ^ 2 :: rat)"
    using prod.atLeast1_atMost_eq[of "\<lambda>i. fact (2 * i) ^ 2 :: rat" m] by simp
  have "(\<Prod> i < h. qLead i) ^ 2 = (\<Prod> i < m. qLead (Suc i)) ^ 2"
    unfolding Suc prod.lessThan_Suc_shift by (simp add: qLead_def)
  also have "\<dots> = (\<Prod> i < m. qLead (Suc i) ^ 2)" by (rule prod_power_distrib)
  also have "\<dots> = (\<Prod> i < m. 4 / fact (2 * Suc i) ^ 2)" unfolding sq ..
  also have "\<dots> = 4 ^ m / (\<Prod> i < m. fact (2 * Suc i) ^ 2)" by (simp add: prod_dividef)
  also have "\<dots> = 4 ^ m / (\<Prod> i = 1..m. fact (2 * i) ^ 2)" unfolding r ..
  finally show ?thesis using Suc by simp
qed

lemma fBasis_mult:
  "fBasis K i * fBasis K j = Polynomial.smult ((1 / fact (Nof K) ^ 2) ^ 6) (Dm (Nof K) ^ 6 *
    (qBasis i * qBasis j))"
proof -
  define c :: rat where "c = 1 / fact (Nof K) ^ 2"
  define D where "D = Dm (Nof K)"
  have e1: "c ^ 6 = c ^ 3 * c ^ 3" and e2: "D ^ 6 = D ^ 3 * D ^ 3"
    by (simp_all add: power_add[symmetric])
  show ?thesis unfolding fBasis_def c_def[symmetric] D_def[symmetric] e1 e2
    by (simp add: smult_power mult_ac)
qed

lemma muX_fBasis:
  assumes "i < hof K" "j < hof K"
  shows "muX {1..K} (fBasis K i * fBasis K j) =
         Polynomial.smult ((1 / fact (Nof K) ^ 2) ^ 6)
           (\<Sum> k < hof K. \<Sum> l <
             hof K. [:Qc (hof K) $$ (i, k) * Qc (hof K) $$ (j, l):] * GK K $$ (k, l))"
proof -
  let ?h = "hof K" and ?c = "(1 / fact (Nof K) ^ 2) ^ 6 :: rat" and ?D = "Dm (Nof K) ^ 6"
  let ?Q = "Qc (hof K)"
  have sm: "muX S (Polynomial.smult a P) = Polynomial.smult a (muX S P)" for S a P
    using muX_C_mul[of S a P] by simp
  have qe: "qBasis a = (\<Sum> k < ?h. Polynomial.smult (?Q $$ (a, k)) (pX ^ k))" if "a < ?h" for a
  proof -
    have "qBasis a = (\<Sum> k < ?h. Polynomial.smult (Polynomial.coeff (qBasis a) k) (pX ^ k))"
      by (rule qBasis_eq_sum[OF that])
    also have "\<dots> = (\<Sum> k < ?h. Polynomial.smult (?Q $$ (a, k)) (pX ^ k))"
      using that by (intro sum.cong refl) (simp add: Qc_def)
    finally show ?thesis .
  qed
  have pq0: "qBasis i * qBasis j = (\<Sum> k < ?h. \<Sum> l < ?h.
      Polynomial.smult (?Q $$ (i, k)) (pX ^ k) * Polynomial.smult (?Q $$ (j, l)) (pX ^ l))"
    unfolding qe[OF assms(1)] qe[OF assms(2)] by (rule sum_product)
  have pq: "?D * (qBasis i * qBasis j) =
      (\<Sum> k < ?h. \<Sum> l < ?h. Polynomial.smult (?Q $$ (i, k) * ?Q $$ (j,
        l)) (?D * pX ^ (k + l)))"
    unfolding pq0 sum_distrib_left
    by (intro sum.cong refl) (simp add: power_add mult_ac)
  have "muX {1..K} (fBasis K i * fBasis K j) =
    Polynomial.smult ?c (muX {1..K} (?D * (qBasis i * qBasis j)))"
    unfolding fBasis_mult sm ..
  also have "\<dots> = Polynomial.smult ?c (\<Sum> k < ?h. \<Sum> l <
    ?h. [:?Q $$ (i, k) * ?Q $$ (j, l):] * GK K $$ (k, l))"
    unfolding pq muX_sum sm
    by (intro arg_cong[where f = "Polynomial.smult ?c"] sum.cong refl) (simp add: GK_def)
  finally show ?thesis .
qed

lemma SK_eq_lead:
  "SK K = (fact K ^ 2 * (1 / fact (Nof K) ^ 2) ^ 6) ^ hof K * (\<Prod> i < hof K. qLead i) ^ 2"
  unfolding SK_def qLead_sq_prod
  by (simp add: power_mult_distrib power_one_over power_divide power_mult[symmetric] mult_ac)

text \<open>The matrix of (3.11) is @{text "c \<cdot> Q G Q^T"} with
  @{text "c = (K!)^2 / (N!)^{12}"}.\<close>
lemma fBasis_matrix_eq:
  "Matrix.mat (hof K) (hof K) (\<lambda>(i,
    j). [:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j)) =
     [:fact K ^ 2 * (1 / fact (Nof K) ^ 2) ^ 6:] \<cdot>\<^sub>m
       (map_mat (\<lambda>q. [:q:]) (Qc (hof K)) * GK K *
         transpose_mat (map_mat (\<lambda>q. [:q:]) (Qc (hof K))))"
proof -
  let ?h = "hof K" and ?c = "fact K ^ 2 * (1 / fact (Nof K) ^ 2) ^ 6 :: rat"
  let ?Q = "map_mat (\<lambda>q. [:q:]) (Qc (hof K))"
  have dQ: "dim_row (Qc n) = n" "dim_col (Qc n) = n" for n by (simp_all add: Qc_def)
  have dG: "dim_row (GK K) = ?h" "dim_col (GK K) = ?h" by (simp_all add: GK_def)
  have entry: "[:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j) =
    [:?c:] * (?Q * GK K * transpose_mat ?Q) $$ (i, j)"
    if ih: "i < ?h" and jh: "j < ?h" for i j
  proof -
    have m: "(?Q * GK K * transpose_mat ?Q) $$ (i, j) =
        (\<Sum> l < ?h. (\<Sum> k < ?h. [:Qc ?h $$ (i, k):] * GK K $$ (k, l)) * [:Qc ?h $$ (j,
          l):])"
      using ih jh by (simp add: scalar_prod_def dQ dG atLeast0LessThan)
    have "[:?c:] * (\<Sum> l < ?h. (\<Sum> k <
      ?h. [:Qc ?h $$ (i, k):] * GK K $$ (k, l)) * [:Qc ?h $$ (j, l):]) =
        (\<Sum> l < ?h. \<Sum> k < ?h. [:?c:] * ([:Qc ?h $$ (i, k):] * GK K $$ (k,
          l) * [:Qc ?h $$ (j, l):]))"
      by (simp add: sum_distrib_left sum_distrib_right smult_sum_right)
    also have "\<dots> = (\<Sum> k < ?h. \<Sum> l <
      ?h. [:?c:] * ([:Qc ?h $$ (i, k):] * GK K $$ (k, l) * [:Qc ?h $$ (j, l):]))"
      by (rule sum.swap)
    also have "\<dots> = [:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j)"
      unfolding muX_fBasis[OF ih jh] by (simp add: smult_sum_right mult_ac)
    finally show ?thesis unfolding m by (rule sym)
  qed
  show ?thesis
  proof (rule eq_matI)
    fix i j
    assume i: "i < dim_row ([:?c:] \<cdot>\<^sub>m (?Q * GK K * transpose_mat ?Q))"
      and j: "j < dim_col ([:?c:] \<cdot>\<^sub>m (?Q * GK K * transpose_mat ?Q))"
    have ih: "i < ?h" and jh: "j < ?h" using i j by (simp_all add: dQ dG)
    have a: "i < dim_row (?Q * GK K * transpose_mat ?Q)" "j <
      dim_col (?Q * GK K * transpose_mat ?Q)"
      using ih jh by (simp_all add: dQ dG)
    show "Matrix.mat ?h ?h (\<lambda>(i,
      j). [:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j)) $$ (i, j) =
        ([:?c:] \<cdot>\<^sub>m (?Q * GK K * transpose_mat ?Q)) $$ (i, j)"
      unfolding index_mat(1)[OF ih jh] index_smult_mat(1)[OF a] prod.case by (rule entry[OF ih jh])
  qed (simp_all add: dQ dG)
qed

lemma comm_ring_hom_pCons: "comm_ring_hom (\<lambda>q :: 'a :: comm_ring_1. [:q:])"
  by unfold_locales simp_all

lemma det_map_mat_C:
  "M \<in> carrier_mat n n \<Longrightarrow>
    Determinant.det (map_mat (\<lambda>q. [:q:]) M) = [:Determinant.det M:]"
  by (rule comm_ring_hom.hom_det[OF comm_ring_hom_pCons])

text \<open>(3.11): @{text "F_K = det[(K!)^2 mu_X(f_i f_j / D_K)]"}.\<close>
theorem F_eq_det_fBasis:
  assumes "40 dvd K"
  shows "FK K = Determinant.det (Matrix.mat (hof K) (hof K)
                  (\<lambda>(i, j). [:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j)))"
proof -
  define h where "h = hof K"
  define c :: rat where "c = fact K ^ 2 * (1 / fact (Nof K) ^ 2) ^ 6"
  define Qp where "Qp = map_mat (\<lambda>q. [:q:]) (Qc h)"
  have Qpc: "Qp \<in> carrier_mat h h" and Gc: "GK K \<in> carrier_mat h h"
    by (simp_all add: Qp_def Qc_def GK_def h_def)
  have "Determinant.det (Matrix.mat h h (\<lambda>(i,
    j). [:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j)))
        = [:c:] ^ h * (Determinant.det Qp * Determinant.det (GK K) * Determinant.det Qp)"
  proof -
    have e: "Matrix.mat h h (\<lambda>(i,
      j). [:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j)) =
        [:c:] \<cdot>\<^sub>m (Qp * GK K * transpose_mat Qp)"
      unfolding h_def c_def Qp_def by (rule fBasis_matrix_eq)
    have Tc: "transpose_mat Qp \<in> carrier_mat h h" using Qpc by simp
    have QGc: "Qp * GK K \<in> carrier_mat h h" using Qpc Gc by (rule mult_carrier_mat)
    have dc: "dim_col (Qp * GK K * transpose_mat Qp) = h" using Qpc by simp
    show ?thesis unfolding e det_smult dc det_mult[OF QGc Tc] det_mult[OF Qpc Gc] det_transpose[OF
      Qpc] ..
  qed
  also have "\<dots> = [:c ^ h * (\<Prod> i < h. qLead i) ^ 2:] * DeltaK K"
    unfolding Qp_def det_map_mat_C[OF Qc_carrier] det_Qc DeltaK_def const_poly_power
    by (simp add: power2_eq_square mult_ac)
  also have "\<dots> = FK K"
    unfolding FK_def SK_eq_lead c_def h_def ..
  finally show ?thesis unfolding h_def ..
qed

subsection \<open>The small-prime bound (3.12)\<close>

lemma degree_fBasis_le: "degree (fBasis K i) \<le> 3 * Nof K + i"
proof -
  have "degree ([:1 / fact (Nof K) ^ 2:] * Dm (Nof K)) \<le> Nof K"
    using degree_mult_le[of "[:1 / fact (Nof K) ^ 2:]" "Dm (Nof K)"] degree_Dm[of "Nof K"] by simp
  with degree_power_le[of "[:1 / fact (Nof K) ^ 2:] * Dm (Nof K)" 3]
  have "degree (([:1 / fact (Nof K) ^ 2:] * Dm (Nof K)) ^ 3) \<le> 3 * Nof K" by linarith
  moreover have "degree (([:1 / fact (Nof K) ^ 2:] * Dm (Nof K)) ^ 3 * qBasis i) \<le>
      degree (([:1 / fact (Nof K) ^ 2:] * Dm (Nof K)) ^ 3) + degree (qBasis i)"
        by (rule degree_mult_le)
  ultimately show ?thesis unfolding fBasis_def using degree_qBasis_le[of i] by linarith
qed

lemma signedPoles_Icc: "signedPoles {1..K} = symPoles K"
  unfolding signedPoles_def symPoles_def
proof
  show "int ` {1..K} \<union> (\<lambda>j. - int j) ` {1..K} \<subseteq> {r. - int K \<le> r \<and>
    r \<le> int K \<and> r \<noteq> 0}" by auto
next
  show "{r. - int K \<le> r \<and> r \<le> int K \<and>
    r \<noteq> 0} \<subseteq> int ` {1..K} \<union> (\<lambda>j. - int j) ` {1..K}"
  proof
    fix r assume r: "r \<in> {r. - int K \<le> r \<and> r \<le> int K \<and> r \<noteq> 0}"
    show "r \<in> int ` {1..K} \<union> (\<lambda>j. - int j) ` {1..K}"
    proof (cases "0 < r")
      case True
      hence "r = int (nat r)" "nat r \<in> {1..K}" using r by auto
      thus ?thesis by blast
    next
      case False
      hence "r = - int (nat (- r))" "nat (- r) \<in> {1..K}" using r by auto
      thus ?thesis by blast
    qed
  qed
qed

text \<open>Each entry of the matrix in (3.11) satisfies the Lemma 3.3 bound.\<close>
lemma fBasis_entry_vge:
  assumes p: "prime p" and K: "40 dvd K" and i: "i < hof K" and j: "j < hof K"
  shows "vpGge p ([:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j))
           (- 6 * of_nat (nat_log p (5 * K)) - of_nat (multiplicity p (24::nat)))"
proof -
  obtain n where Kn: "K = 40 * n" using K by (elim dvdE)
  have n1: "1 \<le> n" using i by (auto simp: Kn hof_def)
  have hN: "Nof K = 3 * n" and hh: "hof K = 37 * n" by (simp_all add: Kn Nof_def hof_def)
  define A where "A = [:(-1) ^ card {1..K}:] * pX ^ 5 * pcompose (fBasis K i *
    fBasis K j) (- (pX ^ 2))"
  have pb: "[:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j) =
    tauX (symPoles K) ([:fact K ^ 2:] * A)"
  proof -
    have "muX {1..K} (fBasis K i * fBasis K j) = tauX (symPoles K) A"
      unfolding A_def signedPoles_Icc[symmetric] by (rule pullback) auto
    thus ?thesis unfolding tauX_C_mul by simp
  qed
  have Aint: "IntValuedAt p A"
  proof -
    have c: "IntEval [:(-1) ^ card {1..K} :: rat:]" using IntEval_C_int[of "(-1) ^ card {1..K}"]
      by simp
    have "IntEval A" unfolding A_def pcompose_mult
      by (intro IntEval_mult c IntEval_power IntEval_pX IntEval_fBasis)
    thus ?thesis by (rule IntEval_IntValuedAt[OF p])
  qed
  have dA: "degree A \<le> 5 + 184 * n"
  proof -
    have d1: "degree (fBasis K i * fBasis K j) \<le> 92 * n"
      using degree_mult_le[of "fBasis K i" "fBasis K j"] degree_fBasis_le[of K i]
        degree_fBasis_le[of K j] i j hN hh
      by linarith
    have d2: "degree (- (pX ^ 2) :: rat poly) = 2" unfolding degree_minus pX_pow_monom
      by (rule degree_monom_eq) simp
    have "degree (pcompose (fBasis K i * fBasis K j) (- (pX ^ 2))) \<le> 184 * n"
      unfolding degree_pcompose d2 using d1 by linarith
    moreover have "degree ([:(-1) ^ card {1..K}:] * pX ^ 5 :: rat poly) \<le> 5"
      unfolding pX_pow_monom by (simp add: degree_monom_le)
    ultimately show ?thesis unfolding A_def
      using degree_mult_le[of "[:(-1) ^ card {1..K}:] * pX ^ 5" "pcompose (fBasis K i *
        fBasis K j) (- (pX ^ 2))"]
      by linarith
  qed
  have log: "nat_log p (max (2 * K) (5 + 184 * n + 1)) \<le> nat_log p (5 * K)"
    by (rule nat_log_mono) (use n1 in \<open>simp add: Kn\<close>)
  show ?thesis
    unfolding pb
    by (rule vpGge_mono[OF far_pole_valuation_bound[OF p Aint dA]]) (use log in \<open>simp add:
      of_nat_le_iff\<close>)
qed

text \<open>(3.12): @{text "v_p^G(F_K) \<ge> -6h \<lfloor>log_p(5K)\<rfloor> - h v_p(24)"}
  for every prime @{text p}.\<close>
theorem vpG_F_ge:
  assumes p: "prime p" and K: "40 dvd K"
  shows "vpGge p (FK K) (- 6 * of_nat (hof K) * of_nat (nat_log p (5 * K))
                         - of_nat (hof K) * of_nat (multiplicity p (24::nat)))"
proof -
  define h where "h = hof K"
  define M where "M = Matrix.mat h h (\<lambda>(i,
    j). [:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j))"
  define b where "b = (- 6 * of_nat (nat_log p (5 * K)) - of_nat (multiplicity p (24::nat)) :: rat)"
  have Mc: "M \<in> carrier_mat h h" by (simp add: M_def)
  have entry: "\<And>i j. i < h \<Longrightarrow> j < h \<Longrightarrow> vpGge p (M $$ (i, j)) b"
  proof -
    fix i j assume ih: "i < h" and jh: "j < h"
    have e: "M $$ (i, j) = [:fact K ^ 2:] * muX {1..K} (fBasis K i * fBasis K j)"
      unfolding M_def using ih jh by (subst index_mat) simp_all
    show "vpGge p (M $$ (i, j)) b"
      unfolding e b_def by (rule fBasis_entry_vge[OF p K]) (use ih jh in \<open>simp_all add:
        h_def\<close>)
  qed
  have "vpGge p (Determinant.det M) (\<Sum> i = 0..<h. b)"
  proof (rule vpGge_det_of_terms[OF p Mc])
    fix \<sigma> assume "\<sigma> permutes {0..<h}"
    thus "vpGge p (\<Prod> i = 0..<h. M $$ (i, \<sigma> i)) (\<Sum> i = 0..<h. b)"
      by (intro vpGge_prod[OF p] entry) (auto simp: permutes_in_image)
  qed
  moreover have "FK K = Determinant.det M" unfolding M_def h_def by (rule F_eq_det_fBasis[OF K])
  moreover have "(\<Sum> i = 0..<h. b) = - 6 * of_nat (hof K) * of_nat (nat_log p (5 * K))
                                     - of_nat (hof K) * of_nat (multiplicity p (24::nat))"
    by (simp add: b_def h_def algebra_simps)
  ultimately show ?thesis by simp
qed

end
