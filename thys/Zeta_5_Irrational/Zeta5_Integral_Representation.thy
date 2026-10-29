(*  Title:   Zeta5_Integral_Representation.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Integral_Representation
  imports Zeta5_Outer_Range Vandermonde_Gram_Determinants Laplace_Sin_Cot_Series
    "HOL-Real_Asymp.Real_Asymp"
begin

section \<open>The determinant construction and the moment representation of
  \<open>\<zeta>(5)\<close>\<close>

text \<open>Section 2 of the paper: degree and leading coefficient of
  \<open>\<Delta>\<^sub>K\<close> (2.9) through the Vandermonde
  determinant, the positive integral representation
    \<open>\<mu>\<^sub>\<zeta>\<^sub>(\<^sub>5\<^sub>)(P) =
    \<integral> P w\<close> of Proposition 2.2
  (@{text muX_zeta5_integral}: moments from Euler's formula
    for \<open>\<zeta>(2e + 2)\<close> and the pole values from the Laplace
  transform of \<open>sin\<close> and the cotangent expansion),
    and the positivity \<open>\<Delta>\<^sub>K(\<zeta>(5)) > 0\<close>.  Lean theories
  @{text Section2}, @{text Degree29}, @{text Prop22}.\<close>

text \<open>@{text "G_K"} may be computed with the cancelled denominator @{text "D_K/D_N"} and
  numerator @{text "D_N^5"}.\<close>
lemma G_eq_cancelled:
  "i < hof K \<Longrightarrow> j < hof K \<Longrightarrow>
     GK K $$ (i, j) = muX {Nof K + 1..K} (Dm (Nof K) ^ 5 * pX ^ (i + j))"
proof -
  assume i: "i < hof K" and j: "j < hof K"
  define N where "N = Nof K"
  have "N \<le> K" unfolding N_def Nof_def by linarith
  hence U: "{1..K} = {1..N} \<union> {N + 1..K}" by auto
  have D: "Dm N = sqPoleProd {1..N}" by (simp add: Dm_def sqPoleProd_def)
  have e: "Dm N ^ 6 * pX ^ (i + j) = (Dm N ^ 5 * pX ^ (i + j)) * sqPoleProd {1..N}"
    unfolding D by (simp add: power_Suc ac_simps numeral_eq_Suc)
  have "GK K $$ (i, j) = muX {1..K} (Dm N ^ 6 * pX ^ (i + j))"
    using i j by (simp add: GK_def N_def)
  also have "\<dots> = muX ({1..N} \<union> {N + 1..K}) ((Dm N ^ 5 * pX ^ (i + j)) *
    sqPoleProd {1..N})"
    unfolding U e ..
  also have "\<dots> = muX {N + 1..K} (Dm N ^ 5 * pX ^ (i + j))"
    by (rule muX_mul_cancel_set) auto
  finally show ?thesis by (simp add: N_def)
qed

text \<open>@{text "G_K(X)"} has entries affine in @{text X}.\<close>
lemma degree_muPole_le: "degree (muPole j) \<le> 1"
  unfolding muPole_def
  by (force simp: degree_monom_le intro: degree_add_le degree_diff_le order_trans[OF
    degree_smult_le])

lemma muX_degree_le:
  assumes "finite S"
  shows "degree (muX S P) \<le> 1"
proof -
  have "degree (\<Sum> j \<in> S. [:sqResidue S P j:] * muPole j) \<le> 1"
  proof (rule degree_sum_le[OF assms])
    fix j
    have "degree ([:sqResidue S P j:] * muPole j) \<le> degree (muPole j)"
      by (simp add: degree_smult_le)
    thus "degree ([:sqResidue S P j:] * muPole j) \<le> 1" using degree_muPole_le[of j] by simp
  qed
  thus ?thesis unfolding muX_def by (intro degree_add_le) simp_all
qed

subsection \<open>(2.9): degree and leading coefficient of @{text "\<Delta>_K"}\<close>

text \<open>A product of polynomials of degree @{text "\<le> 1"} has degree @{text "\<le> card I"},
  and its
  top coefficient is the product of the @{text X}-coefficients.\<close>
lemma coeff_prod_degree_le_1:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> degree (f i) \<le> 1"
  shows "degree (\<Prod> i \<in> I. f i) \<le> card I \<and>
         Polynomial.coeff (\<Prod> i \<in> I. f i) (card I) = (\<Prod> i \<in>
           I. Polynomial.coeff (f i) 1)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert a I)
  have IH: "degree (\<Prod> i \<in> I. f i) \<le> card I"
    "Polynomial.coeff (\<Prod> i \<in> I. f i) (card I) = (\<Prod> i \<in>
      I. Polynomial.coeff (f i) 1)"
    using insert.IH insert.prems by auto
  have da: "degree (f a) \<le> 1" using insert.prems by simp
  have deg: "degree (f a * (\<Prod> i \<in> I. f i)) \<le> Suc (card I)"
    using degree_mult_le[of "f a" "\<Prod> i \<in> I. f i"] da IH(1) by linarith
  have top: "Polynomial.coeff (f a * (\<Prod> i \<in> I. f i)) (Suc (card I)) =
             Polynomial.coeff (f a) 1 * Polynomial.coeff (\<Prod> i \<in> I. f i) (card I)"
  proof -
    have "Polynomial.coeff (f a * (\<Prod> i \<in> I. f i)) (Suc (card I)) =
        (\<Sum> k \<le> Suc (card I). Polynomial.coeff (f a) k * Polynomial.coeff (\<Prod> i \<in>
          I. f i) (Suc (card I) - k))"
      by (rule coeff_mult)
    also have "\<dots> = (\<Sum> k \<in>
      {1}. Polynomial.coeff (f a) k * Polynomial.coeff (\<Prod> i \<in> I. f i) (Suc (card I) - k))"
    proof (rule sum.mono_neutral_right)
      show "\<forall>k \<in> {..Suc (card I)} - {1}.
          Polynomial.coeff (f a) k * Polynomial.coeff (\<Prod> i \<in> I. f i) (Suc (card I) - k) =
            0"
      proof
        fix k assume k: "k \<in> {..Suc (card I)} - {1}"
        show "Polynomial.coeff (f a) k * Polynomial.coeff (\<Prod> i \<in>
          I. f i) (Suc (card I) - k) = 0"
        proof (cases "k = 0")
          case True
          have "degree (\<Prod> i \<in> I. f i) < Suc (card I)" using IH(1) by linarith
          hence "Polynomial.coeff (\<Prod> i \<in> I. f i) (Suc (card I)) = 0" by (rule coeff_eq_0)
          thus ?thesis using True by simp
        next
          case False
          hence "degree (f a) < k" using k da by auto
          hence "Polynomial.coeff (f a) k = 0" by (rule coeff_eq_0)
          thus ?thesis by simp
        qed
      qed
    qed auto
    finally show ?thesis by simp
  qed
  show ?case using insert.hyps deg top IH by simp
qed

text \<open>@{text "A + X B"} as a matrix of affine polynomials.\<close>
definition affine_mat :: "rat mat \<Rightarrow> rat mat \<Rightarrow> rat poly mat" where
  "affine_mat A B = Matrix.mat (dim_row A) (dim_col A) (\<lambda>(i, j). [:A $$ (i, j), B $$ (i,
    j):])"

lemma affine_mat_carrier: "A \<in> carrier_mat n n \<Longrightarrow>
  affine_mat A B \<in> carrier_mat n n"
  by (simp add: affine_mat_def)

text \<open>@{text "det(A + X B)"} has degree @{text "\<le> n"} and @{text "X^n"}-coefficient
  @{text "det B"}.\<close>
lemma det_affine_mat:
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  shows "degree (Determinant.det (affine_mat A B)) \<le> n \<and>
         Polynomial.coeff (Determinant.det (affine_mat A B)) n = Determinant.det B"
proof -
  let ?M = "affine_mat A B"
  have Mc: "?M \<in> carrier_mat n n" using A by (rule affine_mat_carrier)
  have trm: "\<And>\<sigma>. \<sigma> permutes {0..<n} \<Longrightarrow>
      degree (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i)) \<le> n \<and>
      Polynomial.coeff (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i)) n = (\<Prod> i =
        0..<n. B $$ (i, \<sigma> i))"
  proof -
    fix \<sigma> :: "nat \<Rightarrow> nat"
    assume \<sigma>: "\<sigma> permutes {0..<n}"
    have e: "?M $$ (i, \<sigma> i) = [:A $$ (i, \<sigma> i), B $$ (i, \<sigma> i):]"
      if i: "i \<in> {0..<n}" for i
    proof -
      have "\<sigma> i \<in> {0..<n}" using permutes_in_image[OF \<sigma>] i by simp
      thus ?thesis using i A by (simp add: affine_mat_def)
    qed
    have dl: "degree [:a, b:] \<le> 1" for a b :: rat
      using degree_pCons_le[of a "[:b:]"] by simp
    have "degree (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i)) \<le> card {0..<n} \<and>
        Polynomial.coeff (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i)) (card {0..<n}) =
          (\<Prod> i = 0..<n. Polynomial.coeff (?M $$ (i, \<sigma> i)) 1)"
      by (rule coeff_prod_degree_le_1) (simp_all add: e dl)
    moreover have "(\<Prod> i = 0..<n. Polynomial.coeff (?M $$ (i, \<sigma> i)) 1) = (\<Prod> i =
      0..<n. B $$ (i, \<sigma> i))"
      by (rule prod.cong) (simp_all add: e)
    ultimately show "degree (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i)) \<le> n \<and>
      Polynomial.coeff (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i)) n = (\<Prod> i =
        0..<n. B $$ (i, \<sigma> i))"
      by simp
  qed
  have det_expand: "Determinant.det ?M =
      (\<Sum> \<sigma> \<in> {\<sigma>. \<sigma> permutes {0..<n}}. signof \<sigma> * (\<Prod> i =
        0..<n. ?M $$ (i, \<sigma> i)))"
    using Mc by (simp add: Determinant.det_def')
  have detB: "Determinant.det B =
      (\<Sum> \<sigma> \<in> {\<sigma>. \<sigma> permutes {0..<n}}. signof \<sigma> * (\<Prod> i =
        0..<n. B $$ (i, \<sigma> i)))"
    using B by (simp add: Determinant.det_def')
  have "degree (Determinant.det ?M) \<le> n"
    unfolding det_expand
  proof (rule degree_sum_le)
    show "finite {\<sigma>. \<sigma> permutes {0..<n}}" by (simp add: finite_permutations)
  next
    fix \<sigma> assume "\<sigma> \<in> {\<sigma>. \<sigma> permutes {0..<n}}"
    hence \<sigma>: "\<sigma> permutes {0..<n}" by simp
    have "degree (signof \<sigma> * (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i))) \<le>
      degree (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i))"
      unfolding of_int_poly by (simp add: degree_smult_le)
    thus "degree (signof \<sigma> * (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i))) \<le> n"
      using trm[OF \<sigma>] by linarith
  qed
  moreover have "Polynomial.coeff (Determinant.det ?M) n = Determinant.det B"
  proof -
    have "Polynomial.coeff (Determinant.det ?M) n =
        (\<Sum> \<sigma> \<in> {\<sigma>. \<sigma> permutes {0..<n}}. Polynomial.coeff (signof
          \<sigma> * (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i))) n)"
      unfolding det_expand by (rule coeff_sum)
    also have "\<dots> = (\<Sum> \<sigma> \<in>
      {\<sigma>. \<sigma> permutes {0..<n}}. signof \<sigma> * (\<Prod> i =
      0..<n. B $$ (i, \<sigma> i)))"
    proof (rule sum.cong[OF refl])
      fix \<sigma> assume "\<sigma> \<in> {\<sigma>. \<sigma> permutes {0..<n}}"
      hence \<sigma>: "\<sigma> permutes {0..<n}" by simp
      show "Polynomial.coeff (signof \<sigma> * (\<Prod> i = 0..<n. ?M $$ (i, \<sigma> i))) n =
          signof \<sigma> * (\<Prod> i = 0..<n. B $$ (i, \<sigma> i))"
        unfolding of_int_poly using trm[OF \<sigma>] by simp
    qed
    also have "\<dots> = Determinant.det B" using detB by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
qed

text \<open>The constant and @{text X}-coefficient matrices of @{text "G_K"}.\<close>
definition GA :: "nat \<Rightarrow> rat mat" where
  "GA K = Matrix.mat (hof K) (hof K) (\<lambda>(i, j). Polynomial.coeff (GK K $$ (i, j)) 0)"
definition GB :: "nat \<Rightarrow> rat mat" where
  "GB K = Matrix.mat (hof K) (hof K) (\<lambda>(i, j). Polynomial.coeff (GK K $$ (i, j)) 1)"

lemma degree_le_1_pCons:
  assumes d: "degree p \<le> 1"
  shows "p = [:Polynomial.coeff p 0, Polynomial.coeff p 1:]"
proof (rule poly_eqI)
  fix n
  show "Polynomial.coeff p n = Polynomial.coeff [:Polynomial.coeff p 0, Polynomial.coeff p 1:] n"
  proof (cases "n \<le> 1")
    case True
    thus ?thesis by (cases n) auto
  next
    case False
    hence n: "n = Suc (Suc (n - 2))" by arith
    have "degree p < n" using d False by linarith
    hence "Polynomial.coeff p n = 0" by (rule coeff_eq_0)
    moreover have "Polynomial.coeff [:Polynomial.coeff p 0, Polynomial.coeff p 1:] n = 0"
      by (subst n) simp
    ultimately show ?thesis by simp
  qed
qed

lemma GK_eq_affine: "GK K = affine_mat (GA K) (GB K)"
proof (rule eq_matI)
  fix i j
  assume "i < dim_row (affine_mat (GA K) (GB K))" "j < dim_col (affine_mat (GA K) (GB K))"
  hence ij: "i < hof K" "j < hof K" by (simp_all add: affine_mat_def GA_def)
  have e: "GK K $$ (i, j) = muX {1..K} (Dm (Nof K) ^ 6 * pX ^ (i + j))" using ij
    by (simp add: GK_def)
  have "degree (GK K $$ (i, j)) \<le> 1" unfolding e by (rule muX_degree_le) simp
  hence "GK K $$ (i, j) = [:Polynomial.coeff (GK K $$ (i, j)) 0, Polynomial.coeff (GK K $$ (i,
    j)) 1:]"
    by (rule degree_le_1_pCons)
  thus "GK K $$ (i, j) = affine_mat (GA K) (GB K) $$ (i, j)"
    using ij by (simp add: affine_mat_def GA_def GB_def)
qed (simp_all add: affine_mat_def GA_def GK_def)

lemma muPole_coeff_one: "Polynomial.coeff (muPole j) 1 = of_nat j ^ 4"
  unfolding muPole_def by simp

text \<open>The residue weight at the pole @{text j}.\<close>
definition wt :: "nat \<Rightarrow> nat \<Rightarrow> rat" where
  "wt K j = of_nat j ^ 4 * poly (Dm (Nof K)) (- (of_nat j ^ 2)) ^ 5 /
            (\<Prod> k \<in> {Nof K + 1..K} - {j}. of_nat k ^ 2 - of_nat j ^ 2)"

lemma GB_apply:
  assumes "i < hof K" "j < hof K"
  shows "GB K $$ (i, j) =
         (\<Sum> l \<in> {Nof K + 1..K}. (- (of_nat l ^ 2)) ^ i * (- (of_nat l ^ 2)) ^ j * wt K l)"
proof -
  have "GB K $$ (i, j) = Polynomial.coeff (muX {Nof K + 1..K} (Dm (Nof K) ^ 5 * pX ^ (i + j))) 1"
    using assms by (simp add: GB_def G_eq_cancelled)
  also have "\<dots> = (\<Sum> l \<in> {Nof K + 1..K}.
      sqResidue {Nof K + 1..K} (Dm (Nof K) ^ 5 * pX ^ (i + j)) l * of_nat l ^ 4)"
    unfolding muX_def by (simp add: coeff_sum muPole_coeff_one[unfolded One_nat_def])
  also have "\<dots> = (\<Sum> l \<in> {Nof K + 1..K}. (- (of_nat l ^ 2)) ^ i *
    (- (of_nat l ^ 2)) ^ j * wt K l)"
    by (intro sum.cong refl) (simp add: sqResidue_def wt_def poly_monom power_add mult_ac)
  finally show ?thesis .
qed

text \<open>The Vandermonde sign identity
  @{text "\<Prod>_t \<Prod>_{s \<noteq> t} (v t - v s) =
    (-1)^{n(n-1)/2} (\<Prod>_{i<j} (v j - v i))^2"}.\<close>
lemma prod_erase_sub:
  fixes v :: "nat \<Rightarrow> rat"
  shows "(\<Prod> t < n. \<Prod> s \<in> {..<n} - {t}. v t - v s) =
         (-1) ^ (n * (n - 1) div 2) * (\<Prod> i < n. \<Prod> j \<in> {j. i < j \<and>
           j < n}. v j - v i) ^ 2"
proof -
  have split: "\<And>t. t < n \<Longrightarrow> {..<n} - {t} = {..<t} \<union> {j. t < j \<and>
    j < n}" by auto
  have e1: "(\<Prod> t < n. \<Prod> s \<in> {..<n} - {t}. v t - v s) =
            (\<Prod> t < n. \<Prod> s < t. v t - v s) * (\<Prod> t < n. \<Prod> s \<in> {j. t <
              j \<and> j < n}. v t - v s)"
    unfolding prod.distrib[symmetric]
  proof (rule prod.cong[OF refl])
    fix t assume "t \<in> {..<n}"
    hence t: "t < n" by simp
    have fin: "finite {j. t < j \<and> j < n}" by (rule finite_subset[of _ "{..<n}"]) auto
    show "(\<Prod> s \<in> {..<n} - {t}. v t - v s) = (\<Prod> s < t. v t - v s) * (\<Prod> s \<in>
      {j. t < j \<and> j < n}. v t - v s)"
      unfolding split[OF t] by (rule prod.union_disjoint) (auto simp: fin)
  qed
  have e2: "(\<Prod> t < n. \<Prod> s < t. v t - v s) = (\<Prod> i < n. \<Prod> j \<in> {j. i <
    j \<and> j < n}. v j - v i)"
  proof -
    have L1: "(\<Prod> t < n. \<Prod> s < t. v t - v s) = (\<Prod> (t, s) \<in>
      Sigma {..<n} (\<lambda>t. {..<t}). v t - v s)"
      by (rule prod.Sigma) auto
    have L2: "(\<Prod> i < n. \<Prod> j \<in> {j. i < j \<and> j < n}. v j - v i) =
        (\<Prod> (i, j) \<in> Sigma {..<n} (\<lambda>i. {j. i < j \<and> j < n}). v j - v i)"
      by (rule prod.Sigma) auto
    have L3: "(\<Prod> (t, s) \<in> Sigma {..<n} (\<lambda>t. {..<t}). v t - v s) =
        (\<Prod> (i, j) \<in> Sigma {..<n} (\<lambda>i. {j. i < j \<and> j < n}). v j - v i)"
      by (rule prod.reindex_bij_witness[where i = prod.swap and j = prod.swap]) auto
    show ?thesis unfolding L1 L2 L3 ..
  qed
  have e3: "(\<Prod> t < n. \<Prod> s \<in> {j. t < j \<and> j < n}. v t - v s) =
            (-1) ^ (n * (n - 1) div 2) * (\<Prod> i < n. \<Prod> j \<in> {j. i < j \<and>
              j < n}. v j - v i)"
  proof -
    have card: "card {j. t < j \<and> j < n} = n - Suc t" for t
    proof -
      have "{j. t < j \<and> j < n} = {t<..<n}" by auto
      thus ?thesis by simp
    qed
    have inner: "(\<Prod> s \<in> {j. t < j \<and> j < n}. v t - v s) =
        (-1) ^ (n - Suc t) * (\<Prod> j \<in> {j. t < j \<and> j < n}. v j - v t)" for t
    proof -
      have "(\<Prod> s \<in> {j. t < j \<and> j < n}. v t - v s) = (\<Prod> s \<in> {j. t < j \<and>
        j < n}. (-1) * (v s - v t))"
        by simp
      also have "\<dots> = (-1) ^ (n - Suc t) * (\<Prod> j \<in> {j. t < j \<and>
        j < n}. v j - v t)"
        by (subst prod.distrib) (simp add: card)
      finally show ?thesis .
    qed
    have sum: "(\<Sum> t < n. n - Suc t) = n * (n - 1) div 2"
    proof -
      have "(\<Sum> t < n. n - Suc t) = (\<Sum> t < n. t)"
        using sum.nat_diff_reindex[of "\<lambda>x. x" n] by simp
      also have "\<dots> = \<Sum> {0..<n}" by (simp add: lessThan_atLeast0)
      also have "\<dots> = n * (n - 1) div 2" by (simp add: Sum_Ico_nat)
      finally show ?thesis .
    qed
    have "(\<Prod> t < n. \<Prod> s \<in> {j. t < j \<and> j < n}. v t - v s) =
        (\<Prod> t < n. (-1) ^ (n - Suc t)) * (\<Prod> i < n. \<Prod> j \<in> {j. i < j \<and>
          j < n}. v j - v i)"
      unfolding inner by (rule prod.distrib)
    also have "(\<Prod> t < n. (-1 :: rat) ^ (n - Suc t)) = (-1) ^ (\<Sum> t < n. n - Suc t)"
      by (rule power_sum[symmetric])
    finally show ?thesis unfolding sum .
  qed
  show ?thesis unfolding e1 e2 e3 by (simp add: power2_eq_square)
qed

lemma Dm_eval_ne_zero: "Nof K < j \<Longrightarrow> poly (Dm (Nof K)) (- (of_nat j ^ 2)) \<noteq> 0"
proof -
  assume j: "Nof K < j"
  have fac: "poly (pX + [:of_nat k ^ 2:]) (- (of_nat j ^ 2)) \<noteq> 0" if k: "k \<in> {1..Nof K}"
    for k
  proof -
    have "k < j" using k j by auto
    hence lt: "(of_nat k :: rat) ^ 2 < of_nat j ^ 2" by (intro power_strict_mono) auto
    have "poly (pX + [:of_nat k ^ 2:]) (- (of_nat j ^ 2)) = (of_nat k ^ 2 - of_nat j ^ 2 :: rat)"
      by (simp add: poly_monom)
    thus ?thesis using lt \<open>k < j\<close> by simp
  qed
  show ?thesis unfolding Dm_def poly_prod prod_zero_iff[OF finite_atLeastAtMost] using fac by blast
qed

lemma hof_eq_diff: "40 dvd K \<Longrightarrow> hof K = K - Nof K"
  by (auto simp: hof_def Nof_def elim!: dvdE)

lemma field_cancel_aux:
  fixes d c P :: rat
  assumes d: "d \<noteq> 0" and c: "c * c = 1"
  shows "d * (P / (c * d ^ 2)) * d = c * P"
proof -
  have c0: "c \<noteq> 0" using c by auto
  have "d * (P / (c * d ^ 2)) * d = P / c" using d c0 by (simp add: field_simps power2_eq_square)
  also have "\<dots> = c * (c * P) / c" using c by (simp add: mult.assoc[symmetric])
  also have "\<dots> = c * P" by (rule nonzero_mult_div_cancel_left[OF c0])
  finally show ?thesis .
qed

lemma det_GB:
  assumes "40 dvd K"
  shows "Determinant.det (GB K) = (-1) ^ (hof K * (hof K - 1) div 2) *
           (\<Prod> j = Nof K + 1..K. of_nat j ^ 4 * poly (Dm (Nof K)) (- (of_nat j ^ 2)) ^ 5)"
proof -
  define h N where "h = hof K" and "N = Nof K"
  have hN: "h = K - N" using hof_eq_diff[OF assms] by (simp add: h_def N_def)
  have NK: "N \<le> K" by (simp add: N_def Nof_def)
  define xp where "xp t = N + 1 + t" for t   \<comment> \<open>the poles, indexed
    by @{text "t < h"}\<close>
  define x where "x t = - (of_nat (xp t) ^ 2 :: rat)" for t
  define V where "V = Matrix.mat h h (\<lambda>(t, i). x t ^ i)"
  define D where "D = Matrix.mat h h (\<lambda>(t, s). if t = s then wt K (xp t) else 0)"
  have img: "{N + 1..K} = xp ` {..<h}" and inj: "inj_on xp {..<h}"
  proof -
    show "{N + 1..K} = xp ` {..<h}"
    proof
      show "xp ` {..<h} \<subseteq> {N + 1..K}" using hN NK by (auto simp: xp_def)
      show "{N + 1..K} \<subseteq> xp ` {..<h}"
      proof
        fix k assume k: "k \<in> {N + 1..K}"
        hence "k = xp (k - (N + 1))" "k - (N + 1) \<in> {..<h}" using hN by (auto simp: xp_def)
        thus "k \<in> xp ` {..<h}" by (rule image_eqI)
      qed
    qed
    show "inj_on xp {..<h}" by (rule inj_onI) (simp add: xp_def)
  qed
  have x_inj: "inj_on x {..<h}"
  proof (rule inj_onI)
    fix a b assume "a \<in> {..<h}" "b \<in> {..<h}" and e: "x a = x b"
    from e have "xp a = xp b" by (simp add: x_def)
    thus "a = b" by (simp add: xp_def)
  qed
  have Vc: "V \<in> carrier_mat h h" and Dc: "D \<in> carrier_mat h h"
    by (simp_all add: V_def D_def)
  have GB_eq: "GB K = transpose_mat V * D * V"
  proof -
    have VD: "transpose_mat V * D = Matrix.mat h h (\<lambda>(i, t). x t ^ i * wt K (xp t))"
    proof (rule eq_matI)
      fix a b assume a: "a < dim_row (Matrix.mat h h (\<lambda>(i, t). x t ^ i * wt K (xp t)))"
        and b: "b < dim_col (Matrix.mat h h (\<lambda>(i, t). x t ^ i * wt K (xp t)))"
      have "(transpose_mat V * D) $$ (a, b) = (\<Sum> s \<in> {0..<h}. V $$ (s, a) * D $$ (s, b))"
        using a b Vc Dc by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum> s \<in> {0..<h}. if s = b then x b ^ a * wt K (xp b) else 0)"
        using a b by (intro sum.cong refl) (simp add: V_def D_def)
      also have "\<dots> = x b ^ a * wt K (xp b)" using b by simp
      finally show "(transpose_mat V * D) $$ (a, b) =
        Matrix.mat h h (\<lambda>(i, t). x t ^ i * wt K (xp t)) $$ (a, b)"
        using a b by simp
    qed (use Vc Dc in simp_all)
    show ?thesis
    proof (rule eq_matI)
      fix i j assume i: "i < dim_row (transpose_mat V * D * V)" and j: "j <
        dim_col (transpose_mat V * D * V)"
      have ih: "i < h" and jh: "j < h" using i j Vc Dc by auto
      have "(transpose_mat V * D * V) $$ (i, j) = (\<Sum> t \<in>
        {0..<h}. x t ^ i * wt K (xp t) * x t ^ j)"
        unfolding VD using ih jh Vc by (simp add: scalar_prod_def V_def)
      also have "\<dots> = (\<Sum> t \<in>
        {..<h}. (- (of_nat (xp t) ^ 2)) ^ i * (- (of_nat (xp t) ^ 2)) ^ j * wt K (xp t))"
        unfolding lessThan_atLeast0 by (intro sum.cong refl) (simp add: x_def mult_ac)
      also have "\<dots> = (\<Sum> l \<in>
        {N + 1..K}. (- (of_nat l ^ 2)) ^ i * (- (of_nat l ^ 2)) ^ j * wt K l)"
        unfolding img sum.reindex[OF inj] by (simp add: o_def)
      also have "\<dots> = GB K $$ (i, j)" using GB_apply[of i K j] ih jh by (simp add: h_def N_def)
      finally show "GB K $$ (i, j) = (transpose_mat V * D * V) $$ (i, j)" by (rule sym)
    qed (use Vc Dc in \<open>simp_all add: GB_def h_def\<close>)
  qed
  have detV: "Determinant.det V = (\<Prod> i < h. \<Prod> j \<in> {j. i < j \<and>
    j < h}. x j - x i)"
    unfolding V_def by (rule det_vandermonde_jnf)
  have detV_ne: "Determinant.det V \<noteq> 0"
  proof -
    have nz: "x j - x i \<noteq> 0" if "i < h" "i < j" "j < h" for i j
    proof
      assume "x j - x i = 0"
      hence "x j = x i" by simp
      hence "j = i" using inj_onD[OF x_inj] that by simp
      thus False using that by simp
    qed
    have fin: "finite {j. i < j \<and> j < h}" for i by (rule finite_subset[of _ "{..<h}"]) auto
    show ?thesis unfolding detV prod_zero_iff[OF finite_lessThan] prod_zero_iff[OF fin] using nz
      by auto
  qed
  have detD: "Determinant.det D = (\<Prod> t < h. wt K (xp t))"
  proof -
    have ut: "upper_triangular D" unfolding upper_triangular_def D_def by auto
    have "Determinant.det D = prod_list (diag_mat D)" by (rule det_upper_triangular[OF ut Dc])
    also have "\<dots> = (\<Prod> i = 0..<dim_row D. D $$ (i, i))" by (rule prod_list_diag_prod)
    also have "\<dots> = (\<Prod> t \<in> {0..<h}. wt K (xp t))" using Dc
      by (intro prod.cong) (auto simp: D_def)
    also have "\<dots> = (\<Prod> t < h. wt K (xp t))" by (simp add: lessThan_atLeast0)
    finally show ?thesis .
  qed
  have den: "\<And>t. t < h \<Longrightarrow>
      (\<Prod> k \<in> {N + 1..K} - {xp t}. of_nat k ^ 2 - of_nat (xp t) ^ 2) = (\<Prod> s \<in>
        {..<h} - {t}. x t - x s)"
  proof -
    fix t assume t: "t < h"
    have e: "{N + 1..K} - {xp t} = xp ` ({..<h} - {t})"
      unfolding img using t by (subst inj_on_image_set_diff[OF inj]) auto
    have i2: "inj_on xp ({..<h} - {t})" using inj by (rule inj_on_subset) auto
    show "(\<Prod> k \<in> {N + 1..K} - {xp t}. of_nat k ^ 2 - of_nat (xp t) ^ 2) = (\<Prod> s \<in>
      {..<h} - {t}. x t - x s)"
      unfolding e prod.reindex[OF i2] by (intro prod.cong refl) (simp add: x_def)
  qed
  have prod_wt: "(\<Prod> t < h. wt K (xp t)) =
      (\<Prod> t < h. of_nat (xp t) ^ 4 * poly (Dm N) (- (of_nat (xp t) ^ 2)) ^ 5) /
        ((-1) ^ (h * (h - 1) div 2) * Determinant.det V ^ 2)"
  proof -
    have w: "wt K (xp t) = (of_nat (xp t) ^ 4 * poly (Dm N) (- (of_nat (xp t) ^ 2)) ^ 5) /
        (\<Prod> s \<in> {..<h} - {t}. x t - x s)" if "t < h" for t
      unfolding wt_def N_def[symmetric] den[OF that] by (rule refl)
    have "(\<Prod> t < h. wt K (xp t)) = (\<Prod> t <
      h. (of_nat (xp t) ^ 4 * poly (Dm N) (- (of_nat (xp t) ^ 2)) ^ 5) /
        (\<Prod> s \<in> {..<h} - {t}. x t - x s))"
      by (rule prod.cong[OF refl]) (simp add: w)
    also have "\<dots> = (\<Prod> t < h. of_nat (xp t) ^ 4 *
      poly (Dm N) (- (of_nat (xp t) ^ 2)) ^ 5) /
        (\<Prod> t < h. \<Prod> s \<in> {..<h} - {t}. x t - x s)"
      by (rule prod_dividef)
    also have "(\<Prod> t < h. \<Prod> s \<in> {..<h} - {t}. x t - x s) =
      (-1) ^ (h * (h - 1) div 2) * Determinant.det V ^ 2"
      unfolding detV by (rule prod_erase_sub)
    finally show ?thesis .
  qed
  have num: "(\<Prod> t < h. of_nat (xp t) ^ 4 * poly (Dm N) (- (of_nat (xp t) ^ 2)) ^ 5) =
      (\<Prod> j = N + 1..K. of_nat j ^ 4 * poly (Dm N) (- (of_nat j ^ 2)) ^ 5)"
    unfolding img prod.reindex[OF inj] by (simp add: o_def)
  have "Determinant.det (GB K) = Determinant.det V * Determinant.det D * Determinant.det V"
  proof -
    have Tc: "transpose_mat V \<in> carrier_mat h h" using Vc by simp
    have TDc: "transpose_mat V * D \<in> carrier_mat h h" using Tc Dc by (rule mult_carrier_mat)
    show ?thesis unfolding GB_eq det_mult[OF TDc Vc] det_mult[OF Tc Dc] det_transpose[OF Vc] ..
  qed
  also have "\<dots> = (-1) ^ (h * (h - 1) div 2) *
      (\<Prod> j = N + 1..K. of_nat j ^ 4 * poly (Dm N) (- (of_nat j ^ 2)) ^ 5)"
  proof -
    have s: "((-1 :: rat) ^ (h * (h - 1) div 2)) * (-1) ^ (h * (h - 1) div 2) = 1"
      by (simp add: power_mult_distrib[symmetric])
    show ?thesis unfolding detD prod_wt num by (rule field_cancel_aux[OF detV_ne s])
  qed
  finally show ?thesis by (simp add: h_def N_def)
qed

text \<open>(2.9): @{text "\<Delta>_K"} has degree @{text h} and leading coefficient
  @{text "(-1)^{h(h-1)/2} \<Prod>_{j=N+1}^K j^4 D_N(-j^2)^5"}.  The @{text X}-part of @{text "G_K"}
    is
  @{text "V^T diag(w) V"} with @{text V} Vandermonde.\<close>
theorem Delta_degree_lead_coeff:
  assumes "40 dvd K"
  shows "degree (DeltaK K) = hof K \<and>
         lead_coeff (DeltaK K) = (-1) ^ (hof K * (hof K - 1) div 2) *
           (\<Prod> j = Nof K + 1..K. of_nat j ^ 4 * poly (Dm (Nof K)) (- (of_nat j ^ 2)) ^ 5)"
proof -
  have Ac: "GA K \<in> carrier_mat (hof K) (hof K)" and Bc: "GB K \<in> carrier_mat (hof K) (hof K)"
    by (simp_all add: GA_def GB_def)
  have D: "DeltaK K = Determinant.det (affine_mat (GA K) (GB K))"
    by (simp add: DeltaK_def GK_eq_affine)
  have deg: "degree (DeltaK K) \<le> hof K"
    and cf: "Polynomial.coeff (DeltaK K) (hof K) = Determinant.det (GB K)"
    using det_affine_mat[OF Ac Bc] by (simp_all add: D)
  have ne: "Determinant.det (GB K) \<noteq> 0"
    unfolding det_GB[OF assms]
    using Dm_eval_ne_zero[of K] by auto
  have "degree (DeltaK K) = hof K"
    using deg le_degree[of "DeltaK K" "hof K"] cf ne by simp
  thus ?thesis using cf det_GB[OF assms] by simp
qed

lemma SK_pos: "0 < SK K"
  unfolding SK_def
  by (force intro: divide_pos_pos mult_pos_pos prod_pos zero_less_power fact_gt_zero)

subsection \<open>Proposition 2.2: the positive integral representation\<close>

lemma weight_summable:
  assumes "0 < y"
  shows "summable (\<lambda>l. real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) * y))"
proof -
  define s where "s = exp (- pi * y)"
  have s0: "0 < s" and s1: "s < 1" using assms by (auto simp: s_def)
  define C where "C = 256 / (pi * y) ^ 4"
  have C0: "0 < C" using assms by (simp add: C_def)
  have bound: "real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) * y) \<le> C * s ^ (l + 1)" for l
  proof -
    define x where "x = pi * y * real (l + 1)"
    have x0: "0 \<le> x" using assms by (simp add: x_def)
    have "(x / 4) ^ 4 \<le> (1 + x / 4) ^ 4" using x0 by (intro power_mono) simp_all
    also have "\<dots> \<le> exp (x / 4) ^ 4"
      by (intro power_mono exp_ge_add_one_self) (simp add: x0)
    also have "\<dots> = exp x" by (simp add: exp_of_nat_mult[symmetric])
    finally have e: "(x / 4) ^ 4 \<le> exp x" .
    have "real (l + 1) ^ 4 = C * (x / 4) ^ 4" using assms unfolding C_def x_def
      by (auto simp: power_mult_distrib power_divide pi_gt_zero)
    also have "\<dots> \<le> C * exp x" using C0 e by (intro mult_left_mono) simp_all
    finally have A: "real (l + 1) ^ 4 \<le> C * exp x" .
    have B: "exp (- 2 * pi * real (l + 1) * y) = s ^ (l + 1) * exp (- x)"
    proof -
      have e1: "s ^ (l + 1) = exp (real (l + 1) * (- pi * y))"
        unfolding s_def by (rule exp_of_nat_mult[symmetric])
      have "s ^ (l + 1) * exp (- x) = exp (real (l + 1) * (- pi * y) + - x)"
        by (subst e1) (simp add: exp_add[symmetric])
      also have "real (l + 1) * (- pi * y) + - x = - 2 * pi * real (l + 1) * y"
        by (simp add: x_def algebra_simps)
      finally show ?thesis ..
    qed
    have "real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) * y) =
      (real (l + 1) ^ 4 * exp (- x)) * s ^ (l + 1)"
      by (subst B) (simp add: mult_ac)
    also have "\<dots> \<le> (C * exp x * exp (- x)) * s ^ (l + 1)"
      using A s0 by (intro mult_right_mono mult_right_mono[OF A]) simp_all
    also have "\<dots> = C * s ^ (l + 1)" by (simp add: exp_minus)
    finally show ?thesis .
  qed
  have "summable (\<lambda>l. s ^ Suc l)" using summable_geometric[of s] s0 s1
    by (simp add: summable_Suc_iff)
  hence "summable (\<lambda>l. C * s ^ (l + 1))" by (intro summable_mult) simp
  thus ?thesis
    by (rule summable_comparison_test'[of _ 0]) (use bound assms in \<open>auto intro!:
      mult_nonneg_nonneg\<close>)
qed

text \<open>The weight is positive on @{text "(0, \<infinity>)"}.\<close>
theorem weight_pos: "0 < y \<Longrightarrow> 0 < weight y"
proof -
  assume y: "0 < y"
  have "0 < suminf (\<lambda>l. real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) * y))"
    by (rule suminf_pos[OF weight_summable[OF y]]) simp
  thus "0 < weight y" using y unfolding weight_def by simp
qed

lemma weight_eq: "weight y = (2 * pi) ^ 4 * y ^ 5 / 12 * (\<Sum> l. real (l + 1) ^ 4 * exp (- 2 *
  pi * real (l + 1) * y))"
  by (simp add: weight_def)


text \<open>@{text "\<integral>_0^\<infinity> w(y)/(y^2 + a^2) dy =
  1/(2a) - 1/4 + a^4 \<Sum>_{n\<ge>0} (a + n + 1)^{-5}"}.\<close>
lemma pole:
  assumes "0 < a" "(\<lambda>n. 1 / (a + (real n + 1)) ^ 5) sums Z"
  shows "set_integrable lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + a ^ 2)) \<and>
         set_lebesgue_integral lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + a ^ 2)) =
           1 / (2 * a) - 1 / 4 + a ^ 4 * Z"
proof -
  note a = assms(1) and Z = assms(2)
  define c where "c l = 2 * pi * (real l + 1)" for l
  have cp: "0 < c l" for l by (simp add: c_def)
  define F where "F u = u ^ 4 * exp (- (a * u)) * (1 / 4 + 1 / (2 * (exp u - 1)) - 1 / (2 * u))"
    for u
  have UI: "set_integrable lborel {0<..} F \<and>
    set_lebesgue_integral lborel {0<..} F = 6 / a ^ 5 - 3 / a ^ 4 + 12 * Z"
    unfolding F_def by (rule u_integral[OF a Z])
  define h where "h = (\<lambda>l u. u ^ 5 * exp (- (a * u)) / (u ^ 2 + c l ^ 2))"
  have hi: "set_integrable lborel {0<..} (h l)" for l unfolding h_def
    by (rule phi_integrable[OF cp a])
  have hnn: "0 \<le> h l u" if "0 < u" for l u using that by (simp add: h_def)
  have hsum: "(\<lambda>l. h l u) sums F u" if u: "0 < u" for u
  proof -
    have s: "(\<lambda>l. u ^ 4 * exp (- (a * u)) * (u / (u ^ 2 + (2 * pi * (real l +
      1)) ^ 2))) sums
             (u ^ 4 * exp (- (a * u)) * (1 / 4 + 1 / (2 * (exp u - 1)) - 1 / (2 * u)))"
      by (rule sums_mult[OF S_series[OF u]])
    have e: "(\<lambda>l. u ^ 4 * exp (- (a * u)) * (u / (u ^ 2 + (2 * pi * (real l + 1)) ^ 2))) =
      (\<lambda>l. h l u)"
      by (rule ext) (simp add: h_def c_def eval_nat_numeral mult_ac)
    show ?thesis using s unfolding e F_def .
  qed
  have hs: "summable (\<lambda>l. h l u)" if "0 < u" for u using hsum[OF that]
    by (rule sums_summable)
  have hS: "set_integrable lborel {0<..} (\<lambda>u. \<Sum> l. h l u)"
    by (rule set_integrable_cong_Ioi[OF conjunct1[OF UI]]) (rule sums_unique[OF hsum])
  have hV: "set_lebesgue_integral lborel {0<..} (\<lambda>u. \<Sum> l. h l u) =
    6 / a ^ 5 - 3 / a ^ 4 + 12 * Z"
  proof -
    have "set_lebesgue_integral lborel {0<..} (\<lambda>u. \<Sum> l. h l u) =
      set_lebesgue_integral lborel {0<..} F"
      by (rule set_integral_cong_Ioi) (rule sums_unique[OF hsum, symmetric])
    thus ?thesis using conjunct2[OF UI] by simp
  qed
  have uS: "(\<lambda>l. set_lebesgue_integral lborel {0<..} (h l)) sums (6 / a ^ 5 - 3 / a ^ 4 +
    12 * Z)"
    using suminf_integral_nn[OF hi hnn hs hS] unfolding hV .
  define g where "g = (\<lambda>l y. c l ^ 4 / 12 * (y ^ 5 * exp (- (c l * y)) / (y ^ 2 + a ^ 2)))"
  have gi: "set_integrable lborel {0<..} (g l)" for l
    unfolding g_def by (intro set_integrable_mult_right phi_integrable[OF a cp])
  have gv: "set_lebesgue_integral lborel {0<..} (g l) =
    a ^ 4 / 12 * set_lebesgue_integral lborel {0<..} (h l)" for l
  proof -
    have "set_lebesgue_integral lborel {0<..} (g l) = c l ^ 4 / 12 * Phi a (c l)"
      unfolding g_def Phi_def set_integral_mult_right ..
    also have "\<dots> = a ^ 4 / 12 * Phi (c l) a" using phi_symm[OF a cp[of l]] by simp
    also have "Phi (c l) a = set_lebesgue_integral lborel {0<..} (h l)" unfolding Phi_def h_def ..
    finally show ?thesis .
  qed
  have gsum: "(\<lambda>l. set_lebesgue_integral lborel {0<..} (g l)) sums (a ^ 4 / 12 * (6 /
    a ^ 5 - 3 / a ^ 4 + 12 * Z))"
    unfolding gv by (rule sums_mult[OF uS])
  have gnn: "0 \<le> g l y" if "0 < y" for l y using that cp[of l] by (simp add: g_def)
  have c4: "c l ^ 4 = (2 * pi) ^ 4 * real (l + 1) ^ 4" for l
    by (simp add: c_def power_mult_distrib add.commute)
  have wpt: "weight y / (y ^ 2 + a ^ 2) = (\<Sum> l. g l y)" if y: "0 < y" for y
  proof -
    have s: "summable (\<lambda>l. real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) * y))"
      by (rule weight_summable[OF y])
    have "weight y / (y ^ 2 + a ^ 2) = ((2 * pi) ^ 4 * y ^ 5 / 12 / (y ^ 2 + a ^ 2)) *
      (\<Sum> l. real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) * y))"
      unfolding weight_eq by simp
    also have "\<dots> = (\<Sum> l. ((2 * pi) ^ 4 * y ^ 5 / 12 / (y ^ 2 + a ^ 2)) * (real (l +
      1) ^ 4 * exp (- 2 * pi * real (l + 1) * y)))"
      by (rule suminf_mult[OF s, symmetric])
    also have "(\<lambda>l. ((2 * pi) ^ 4 * y ^ 5 / 12 / (y ^ 2 + a ^ 2)) * (real (l + 1) ^ 4 *
      exp (- 2 * pi * real (l + 1) * y))) = (\<lambda>l. g l y)"
      unfolding g_def c4 by (rule ext) (simp add: c_def mult_ac)
    finally show ?thesis .
  qed
  have gs: "summable (\<lambda>l. g l y)" if y: "0 < y" for y
  proof -
    have "summable (\<lambda>l. ((2 * pi) ^ 4 * y ^ 5 / 12 / (y ^ 2 + a ^ 2)) * (real (l + 1) ^ 4 *
      exp (- 2 * pi * real (l + 1) * y)))"
      by (rule summable_mult[OF weight_summable[OF y]])
    also have "(\<lambda>l. ((2 * pi) ^ 4 * y ^ 5 / 12 / (y ^ 2 + a ^ 2)) * (real (l + 1) ^ 4 *
      exp (- 2 * pi * real (l + 1) * y))) = (\<lambda>l. g l y)"
      unfolding g_def c4 by (rule ext) (simp add: c_def mult_ac)
    finally show ?thesis .
  qed
  have GI: "set_integrable lborel {0<..} (\<lambda>y. \<Sum> l. g l y) \<and>
      set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> l. g l y) =
        (\<Sum> l. set_lebesgue_integral lborel {0<..} (g l))"
    by (rule integral_suminf_nn[OF gi gnn gs sums_summable[OF gsum]])
  have val: "a ^ 4 / 12 * (6 / a ^ 5 - 3 / a ^ 4 + 12 * Z) = 1 / (2 * a) - 1 / 4 + a ^ 4 * Z"
    using a by (simp add: field_simps eval_nat_numeral)
  show ?thesis
  proof
    show "set_integrable lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + a ^ 2))"
      by (rule set_integrable_cong_Ioi[OF conjunct1[OF GI]]) (rule wpt[symmetric])
    have "set_lebesgue_integral lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + a ^ 2)) =
      set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> l. g l y)"
      by (rule set_integral_cong_Ioi) (rule wpt)
    also have "\<dots> = 1 / (2 * a) - 1 / 4 + a ^ 4 * Z"
      using conjunct2[OF GI] sums_unique[OF gsum] val by simp
    finally show "set_lebesgue_integral lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + a ^ 2)) =
      1 / (2 * a) - 1 / 4 + a ^ 4 * Z" .
  qed
qed

subsection \<open>Moments and the pole values\<close>

lemma re_map_add: "map_poly (of_rat :: rat \<Rightarrow> real) (P + Q) =
  map_poly of_rat P + map_poly of_rat Q"
  by (rule poly_eqI) (simp add: coeff_map_poly of_rat_add)

lemma re_map_diff: "map_poly (of_rat :: rat \<Rightarrow> real) (P - Q) =
  map_poly of_rat P - map_poly of_rat Q"
  by (rule poly_eqI) (simp add: coeff_map_poly of_rat_diff)

lemma re_map_mult: "map_poly (of_rat :: rat \<Rightarrow> real) (P * Q) =
  map_poly of_rat P * map_poly of_rat Q"
  by (rule poly_eqI) (simp add: coeff_map_poly coeff_mult of_rat_sum of_rat_mult)

lemma real_eval_add: "real_eval (P + Q) x = real_eval P x + real_eval Q x"
  by (simp add: real_eval_def re_map_add)

lemma real_eval_diff: "real_eval (P - Q) x = real_eval P x - real_eval Q x"
  by (simp add: real_eval_def re_map_diff)

lemma real_eval_mult: "real_eval (P * Q) x = real_eval P x * real_eval Q x"
  by (simp add: real_eval_def re_map_mult)

lemma real_eval_const: "real_eval [:c:] x = of_rat c"
  by (simp add: real_eval_def map_poly_pCons)

lemma real_eval_zero: "real_eval 0 x = 0"
  by (simp add: real_eval_def)

lemma real_eval_one: "real_eval 1 x = 1"
  by (simp add: real_eval_def)

lemma real_eval_pX: "real_eval pX x = x"
  by (simp add: real_eval_def map_poly_monom poly_monom)

lemma real_eval_monom: "real_eval (Polynomial.monom c n) x = of_rat c * x ^ n"
  by (simp add: real_eval_def map_poly_monom poly_monom)

lemma real_eval_smult: "real_eval (Polynomial.smult c P) x = of_rat c * real_eval P x"
proof -
  have e: "Polynomial.smult c P = [:c:] * P" by simp
  show ?thesis unfolding e real_eval_mult real_eval_const ..
qed

lemma real_eval_sum: "real_eval (\<Sum> i \<in> I. f i) x = (\<Sum> i \<in> I. real_eval (f i) x)"
  by (induction I rule: infinite_finite_induct) (simp_all add: real_eval_zero real_eval_add)

lemma real_eval_prod: "real_eval (\<Prod> i \<in> I. f i) x = (\<Prod> i \<in>
  I. real_eval (f i) x)"
  by (induction I rule: infinite_finite_induct) (simp_all add: real_eval_one real_eval_mult)

lemma real_eval_power: "real_eval (P ^ n) x = real_eval P x ^ n"
  by (induction n) (simp_all add: real_eval_one real_eval_mult)

lemmas real_eval_simps = real_eval_add real_eval_diff real_eval_mult real_eval_const real_eval_pX
  real_eval_monom
  real_eval_smult real_eval_sum real_eval_prod real_eval_power real_eval_zero real_eval_one

lemma val2_aux:
  fixes W Q P F a s B :: real
  assumes "W \<noteq> 0" "Q \<noteq> 0" "P \<noteq> 0" "F \<noteq> 0"
  shows "W / 12 * (a * F) / (W * (2 * Q * P)) * (s * Q * P * B / F) = s * B * a / 24"
  using assms by (simp add: field_simps)

lemma moment_term:
  "(2 * pi) ^ 4 / 12 * real (l + 1) ^ 4 * (y ^ (2 * e + 5) * exp (- ((2 * pi * real (l + 1)) *
    y))) =
   (y ^ (2 * e) * ((2 * pi) ^ 4 * y ^ 5 / 12)) * (real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) *
     y))"
  by (simp add: power_add mult_ac)

text \<open>Moments: @{text "\<integral>_0^\<infinity> y^{2e} w(y) dy = mu(t^e)"} (Euler's formula
  for @{text "\<zeta>(2e+2)"}:
  @{text "Zeta_Function.zeta_even_nat"}; Gamma integrals: @{text "Gamma_integral_real"}).\<close>
lemma moment:
  "set_integrable lborel {0<..} (\<lambda>y. y ^ (2 * e) * weight y) \<and>
   set_lebesgue_integral lborel {0<..} (\<lambda>y. y ^ (2 * e) * weight y) = of_rat (muMono e)"
proof -
  define g where "g = (\<lambda>l y. (2 * pi) ^ 4 / 12 * real (l + 1) ^ 4 * (y ^ (2 * e + 5) *
    exp (- ((2 * pi * real (l + 1)) * y))) :: real)"
  have pt: "\<And>y. 0 < y \<Longrightarrow> y ^ (2 * e) * weight y = (\<Sum> l. g l y)"
  proof -
    fix y :: real assume y: "0 < y"
    have s: "summable (\<lambda>l. real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) * y))"
      by (rule weight_summable[OF y])
    have "y ^ (2 * e) * weight y = (y ^ (2 * e) * ((2 * pi) ^ 4 * y ^ 5 / 12)) *
      (\<Sum> l. real (l + 1) ^ 4 * exp (- 2 * pi * real (l + 1) * y))"
      unfolding weight_eq by (simp only: mult.assoc)
    also have "\<dots> = (\<Sum> l. (y ^ (2 * e) * ((2 * pi) ^ 4 * y ^ 5 / 12)) * (real (l +
      1) ^ 4 * exp (- 2 * pi * real (l + 1) * y)))"
      by (rule suminf_mult[OF s, symmetric])
    also have "\<dots> = (\<Sum> l. g l y)" unfolding g_def moment_term ..
    finally show "y ^ (2 * e) * weight y = (\<Sum> l. g l y)" .
  qed
  have int: "\<And>l. set_integrable lborel {0<..} (g l)"
    unfolding g_def by (intro set_integrable_mult_right gam_integrable) simp
  have val: "\<And>l. set_lebesgue_integral lborel {0<..} (g l) =
      ((2 * pi) ^ 4 / 12 * fact (2 * e + 5) / (2 * pi) ^ (2 * e + 6)) * (1 / real (l + 1) ^ (2 *
        (e + 1)))"
  proof -
    fix l :: nat
    define X where "X = real (l + 1)"
    have X0: "0 < X" by (simp add: X_def)
    have c: "0 < 2 * pi * X" using X0 by simp
    have "set_lebesgue_integral lborel {0<..} (g l) =
      (2 * pi) ^ 4 / 12 * X ^ 4 * (fact (2 * e + 5) / (2 * pi * X) ^ (2 * e + 5 + 1))"
      unfolding g_def X_def[symmetric] set_integral_mult_right gam[OF c] ..
    also have "(2 * pi * X) ^ (2 * e + 5 + 1) =
      (2 * pi) ^ (2 * e + 6) * (X ^ 4 * X ^ (2 * (e + 1)))"
    proof -
      have e6: "2 * e + 5 + 1 = 2 * e + 6" by simp
      have "2 * e + 5 + 1 = 4 + 2 * (e + 1)" by simp
      hence "X ^ (2 * e + 5 + 1) = X ^ 4 * X ^ (2 * (e + 1))" by (simp only: power_add)
      moreover have "(2 * pi) ^ (2 * e + 5 + 1) = (2 * pi) ^ (2 * e + 6)" unfolding e6 ..
      ultimately show ?thesis by (simp only: power_mult_distrib)
    qed
    also have "(2 * pi) ^ 4 / 12 * X ^ 4 * (fact (2 * e + 5) / ((2 * pi) ^ (2 * e + 6) * (X ^ 4 *
      X ^ (2 * (e + 1))))) =
        ((2 * pi) ^ 4 / 12 * fact (2 * e + 5) / (2 * pi) ^ (2 * e + 6)) * (1 / X ^ (2 * (e + 1)))"
      using X0 by (simp add: field_simps)
    finally show "set_lebesgue_integral lborel {0<..} (g l) =
      ((2 * pi) ^ 4 / 12 * fact (2 * e + 5) / (2 * pi) ^ (2 * e + 6)) * (1 / real (l + 1) ^ (2 *
        (e + 1)))"
      unfolding X_def .
  qed
  have zeta: "(\<lambda>l. 1 / real (l + 1) ^ (2 * (e + 1))) sums
      ((- 1) ^ (e + 2) * 2 ^ (2 * e + 1) * pi ^ (2 * (e + 1)) * of_rat (bernoulli (2 * (e + 1))) /
        fact (2 * (e + 1)))"
  proof -
    have n: "1 < 2 * (e + 1)" by simp
    have s0: "(\<lambda>k. 1 / of_nat (Suc k) ^ (2 * (e + 1)) :: complex) sums zeta (of_nat (2 *
      (e + 1)))"
      by (rule sums_zeta_nat[OF n])
    have z: "zeta (of_nat (2 * (e + 1))) =
      complex_of_real ((-1) ^ Suc (e + 1) * bernoulli (2 * (e + 1)) * (2 * pi) ^ (2 * (e + 1)) /
      (2 * fact (2 * (e + 1))))"
      using zeta_even_nat[of "e + 1"] by (simp only: of_nat_mult of_nat_numeral)
    have f: "(\<lambda>k. 1 / of_nat (Suc k) ^ (2 * (e + 1)) :: complex) =
      (\<lambda>k. complex_of_real (1 / real (k + 1) ^ (2 * (e + 1))))"
      by (simp add: fun_eq_iff)
    have s: "(\<lambda>l. 1 / real (l + 1) ^ (2 * (e + 1))) sums ((-1) ^ Suc (e + 1) *
      bernoulli (2 * (e + 1)) * (2 * pi) ^ (2 * (e + 1)) / (2 * fact (2 * (e + 1))))"
      using s0 unfolding f z sums_of_real_iff .
    have t2: "(2::real) ^ (2 * (e + 1)) = 2 * 2 ^ (2 * e + 1)"
    proof -
      have "2 * (e + 1) = Suc (2 * e + 1)" by simp
      thus ?thesis by (simp only: power_Suc)
    qed
    have m1: "(-1::real) ^ Suc (e + 1) = (-1) ^ e" by simp
    have m2: "(-1::real) ^ (e + 2) = (-1) ^ e" by simp
    have v: "(-1) ^ Suc (e + 1) * bernoulli (2 * (e + 1)) * (2 * pi) ^ (2 * (e + 1)) / (2 *
      fact (2 * (e + 1))) =
        (- 1) ^ (e + 2) * 2 ^ (2 * e + 1) * pi ^ (2 * (e + 1)) * of_rat (bernoulli (2 * (e + 1))) /
          fact (2 * (e + 1))"
      unfolding of_rat_bernoulli power_mult_distrib[of 2 pi] t2 m1 m2 using field_simps by argo
    show ?thesis using s unfolding v .
  qed
  have sums: "(\<lambda>l. set_lebesgue_integral lborel {0<..} (g l)) sums
      (((2 * pi) ^ 4 / 12 * fact (2 * e + 5) / (2 * pi) ^ (2 * e + 6)) *
       ((- 1) ^ (e + 2) * 2 ^ (2 * e + 1) * pi ^ (2 * (e + 1)) * of_rat (bernoulli (2 * (e + 1))) /
         fact (2 * (e + 1))))"
    unfolding val by (rule sums_mult[OF zeta])
  have ps: "\<And>y. 0 < y \<Longrightarrow> summable (\<lambda>l. g l y)"
  proof -
    fix y :: real assume y: "0 < y"
    have "summable (\<lambda>l. (y ^ (2 * e) * ((2 * pi) ^ 4 * y ^ 5 / 12)) * (real (l + 1) ^ 4 *
      exp (- 2 * pi * real (l + 1) * y)))"
      by (rule summable_mult[OF weight_summable[OF y]])
    thus "summable (\<lambda>l. g l y)" unfolding g_def moment_term .
  qed
  have nn: "\<And>l y. 0 < y \<Longrightarrow> 0 \<le> g l y" by (simp add: g_def)
  obtain I V where IV: "set_integrable lborel {0<..} (\<lambda>y. \<Sum> l. g l y)"
      "set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> l. g l y) =
        (\<Sum> l. set_lebesgue_integral lborel {0<..} (g l))"
    using integral_suminf_nn[OF int nn ps sums_summable[OF sums]] by blast
  have eq: "set_lebesgue_integral lborel {0<..} (\<lambda>y. y ^ (2 * e) * weight y) =
    set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> l. g l y)"
    by (rule set_integral_cong_Ioi) (rule pt)
  have int2: "set_integrable lborel {0<..} (\<lambda>y. y ^ (2 * e) * weight y)"
    by (rule set_integrable_cong_Ioi[OF IV(1)]) (rule pt[symmetric])
  have val2: "(\<Sum> l. set_lebesgue_integral lborel {0<..} (g l)) = of_rat (muMono e)"
  proof -
    have F: "fact (2 * e + 5) = (2 * real e + 5) * (2 * real e + 4) * (2 * real e + 3) * (fact (2 *
      (e + 1)) :: real)"
    proof -
      have "2 * e + 5 = Suc (Suc (Suc (2 * (e + 1))))" by simp
      hence "fact (2 * e + 5) = (real (Suc (Suc (Suc (2 * (e + 1)))))) * real (Suc (Suc (2 * (e +
        1)))) * real (Suc (2 * (e + 1))) * (fact (2 * (e + 1)) :: real)"
        by (simp only: fact_Suc of_nat_mult mult.assoc)
      thus ?thesis by (simp add: algebra_simps)
    qed
    have T: "(2 * pi) ^ (2 * e + 6) = (2 * pi) ^ 4 * (2 * 2 ^ (2 * e + 1) * pi ^ (2 * (e + 1)))"
    proof -
      have "2 * e + 6 = 4 + 2 * (e + 1)" by simp
      hence "(2 * pi) ^ (2 * e + 6) = (2 * pi) ^ 4 * (2 * pi) ^ (2 * (e + 1))"
        by (simp only: power_add)
      moreover have "(2::real) ^ (2 * (e + 1)) = 2 * 2 ^ (2 * e + 1)"
      proof -
        have "2 * (e + 1) = Suc (2 * e + 1)" by simp
        thus ?thesis by (simp only: power_Suc)
      qed
      ultimately show ?thesis by (simp only: power_mult_distrib mult.assoc)
    qed
    have m: "(-1 :: real) ^ (e + 2) = (-1) ^ e" by simp
    have nz1: "(2 * pi) ^ 4 \<noteq> (0::real)" by simp
    have nz2: "(2::real) ^ (2 * e + 1) \<noteq> 0" by simp
    have nz3: "pi ^ (2 * (e + 1)) \<noteq> (0::real)" by simp
    have nz4: "fact (2 * (e + 1)) \<noteq> (0::real)" by simp
    have "(\<Sum> l. set_lebesgue_integral lborel {0<..} (g l)) =
      ((2 * pi) ^ 4 / 12 * fact (2 * e + 5) / (2 * pi) ^ (2 * e + 6)) *
       ((- 1) ^ (e + 2) * 2 ^ (2 * e + 1) * pi ^ (2 * (e + 1)) * of_rat (bernoulli (2 * (e + 1))) /
         fact (2 * (e + 1)))"
      by (rule sums_unique[OF sums, symmetric])
    also have "\<dots> = (-1) ^ e * of_rat (bernoulli (2 * (e + 1))) * ((2 * real e + 5) * (2 *
      real e + 4) * (2 * real e + 3)) / 24"
      unfolding F T m by (rule val2_aux[OF nz1 nz2 nz3 nz4])
    also have "\<dots> = of_rat (muMono e)"
      by (simp add: muMono_def of_rat_mult of_rat_divide of_rat_power of_rat_add of_rat_minus
        mult_ac)
    finally show ?thesis .
  qed
  show ?thesis using int2 eq IV(2) val2 by simp
qed

text \<open>Polynomial part: @{text "\<integral>_0^\<infinity> A(y^2) w(y) dy = mu(A)"}.\<close>
lemma poly_moment:
  "set_integrable lborel {0<..} (\<lambda>y. real_eval A (y ^ 2) * weight y) \<and>
   set_lebesgue_integral lborel {0<..} (\<lambda>y. real_eval A (y ^ 2) * weight y) =
     of_rat (muPoly A)"
proof -
  define D where "D = degree A"
  have ev: "real_eval A x = (\<Sum> e \<le> D. of_rat (Polynomial.coeff A e) * x ^ e)" for x
  proof -
    have "real_eval A x = real_eval (\<Sum> e \<le> D. Polynomial.monom (Polynomial.coeff A e) e) x"
      unfolding D_def by (simp only: poly_as_sum_of_monoms)
    thus ?thesis by (simp only: real_eval_sum real_eval_monom)
  qed
  have e: "(\<lambda>y. real_eval A (y ^ 2) * weight y) = (\<lambda>y. \<Sum> e \<le>
    D. of_rat (Polynomial.coeff A e) * (y ^ (2 * e) * weight y))"
  proof (rule ext)
    fix y :: real
    show "real_eval A (y ^ 2) * weight y = (\<Sum> e \<le>
      D. of_rat (Polynomial.coeff A e) * (y ^ (2 * e) * weight y))"
      unfolding ev sum_distrib_right power_mult[symmetric] mult.assoc ..
  qed
  have ij: "set_integrable lborel {0<..} (\<lambda>y. of_rat (Polynomial.coeff A e) * (y ^ (2 * e) *
    weight y))" if "e \<in> {..D}" for e
    by (rule set_integrable_mult_right) (rule conjunct1[OF moment])
  have "set_lebesgue_integral lborel {0<..} (\<lambda>y. real_eval A (y ^ 2) * weight y) =
      set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> e \<le>
        D. of_rat (Polynomial.coeff A e) * (y ^ (2 * e) * weight y))"
    by (simp only: e)
  also have "\<dots> = (\<Sum> e \<le> D. set_lebesgue_integral lborel {0<..} (\<lambda>y. of_rat
    (Polynomial.coeff A e) * (y ^ (2 * e) * weight y)))"
    by (rule conjunct2[OF set_integral_sum_fin[OF ij]])
  also have "\<dots> = (\<Sum> e \<le> D. of_rat (Polynomial.coeff A e) * of_rat (muMono e))"
    by (simp only: set_integral_mult_right conjunct2[OF moment])
  also have "\<dots> = of_rat (muPoly A)" by (simp add: muPoly_def D_def of_rat_sum of_rat_mult)
  finally have v: "set_lebesgue_integral lborel {0<..} (\<lambda>y. real_eval A (y ^ 2) *
    weight y) = of_rat (muPoly A)" .
  have i: "set_integrable lborel {0<..} (\<lambda>y. real_eval A (y ^ 2) * weight y)"
    unfolding e by (rule conjunct1[OF set_integral_sum_fin[OF ij]])
  show ?thesis using i v by (rule conjI)
qed


text \<open>Pole part: @{text "\<integral>_0^\<infinity> w(y)/(y^2 + j^2) dy =
  j^4(\<zeta>(5) - H_j) - 1/4 + 1/(2j)"}, via the symmetry
  @{text "c^4\<Phi>(a,c) = a^4\<Phi>(c,a)"} of
    @{text "\<Phi>(a,c) = \<integral> y^5e^{-cy}/(y^2+a^2) dy"} (Fubini) and
    @{text "coth_series"}.\<close>
text \<open>@{text "\<zeta>(5) = \<Sum>_{n \<ge> 1} n^{-5}"} as a real series,
  and its tails @{text "\<zeta>(5) - H_j = \<Sum>_{n \<ge> 0} (j + n + 1)^{-5}"}.\<close>
lemma zeta5_sums: "(\<lambda>n. 1 / (real n + 1) ^ 5) sums zeta5"
proof -
  have s0: "(\<lambda>k. 1 / of_nat (Suc k) ^ 5 :: complex) sums zeta (of_nat 5)"
    by (rule sums_zeta_nat) simp
  have f: "(\<lambda>k. 1 / of_nat (Suc k) ^ 5 :: complex) =
    (\<lambda>k. complex_of_real (1 / (real k + 1) ^ 5))"
    by (simp add: fun_eq_iff add.commute)
  have "zeta 5 \<in> \<real>" using zeta_real[of 5] by simp
  hence z: "zeta (of_nat 5) = complex_of_real zeta5" by (simp add: zeta5_def)
  show ?thesis using s0 unfolding f z sums_of_real_iff .
qed

lemma H5_eq_sum: "of_rat (H5 j) = (\<Sum> i < j. 1 / (real i + 1) ^ 5)"
  unfolding H5_def image_Suc_lessThan[symmetric] sum.reindex[OF inj_Suc] o_def of_rat_sum
  by (simp add: of_rat_divide of_rat_power of_rat_add add.commute)

lemma zeta_tail: "(\<lambda>n. 1 / (real j + (real n + 1)) ^ 5) sums (zeta5 - of_rat (H5 j))"
proof -
  have "(\<lambda>i. 1 / (real (i + j) + 1) ^ 5) sums (zeta5 - (\<Sum> i <
    j. 1 / (real i + 1) ^ 5))"
    using sums_split_initial_segment[OF zeta5_sums, of j] by simp
  thus ?thesis unfolding H5_eq_sum by (simp add: algebra_simps)
qed

lemma pole_val:
  "j \<noteq> 0 \<Longrightarrow>
   set_integrable lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + real j ^ 2)) \<and>
   set_lebesgue_integral lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + real j ^ 2)) =
     real_eval (muPole j) zeta5"
proof -
  assume j: "j \<noteq> 0"
  have jpos: "0 < real j" using j by simp
  have "set_integrable lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + real j ^ 2)) \<and>
      set_lebesgue_integral lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + real j ^ 2)) =
        1 / (2 * real j) - 1 / 4 + real j ^ 4 * (zeta5 - of_rat (H5 j))"
    by (rule pole[OF jpos zeta_tail])
  moreover have "real_eval (muPole j) zeta5 =
    real j ^ 4 * (zeta5 - of_rat (H5 j)) - 1 / 4 + 1 / (2 * real j)"
    unfolding muPole_def
    by (simp add: real_eval_simps of_rat_power of_rat_divide of_rat_mult of_rat_diff algebra_simps)
  ultimately show ?thesis by (simp add: algebra_simps)
qed

lemma real_eval_sqPoleProd_pos:
  assumes "finite S" "0 \<notin> S" "0 \<le> t"
  shows "0 < real_eval (sqPoleProd S) t"
proof -
  have "0 < (\<Prod> j \<in> S. real_eval (pX + [:of_nat j ^ 2:]) t)"
  proof (rule prod_pos)
    fix j assume j: "j \<in> S"
    hence "j \<noteq> 0" using assms(2) by metis
    thus "0 < real_eval (pX + [:of_nat j ^ 2:]) t"
      using assms(3) by (simp add: real_eval_simps of_rat_power add_nonneg_pos)
  qed
  thus ?thesis unfolding sqPoleProd_def real_eval_prod .
qed

text \<open>Partial fractions for @{text "P(t)/\<Prod>_{j\<in>S}(t + j^2)"} at real
  @{text "t \<ge> 0"}.\<close>
lemma partial_fractions_real:
  assumes "finite S" "0 \<notin> S" "0 \<le> t"
  shows "real_eval P t / real_eval (sqPoleProd S) t =
         real_eval (P div sqPoleProd S) t + (\<Sum> j \<in>
           S. of_rat (sqResidue S P j) / (t + real j ^ 2))"
proof -
  note S = assms(1)
  define E where "E T = real_eval (sqPoleProd T) t" for T
  define Q where "Q = P div sqPoleProd S"
  define r where "r j = sqResidue S P j" for j
  have Epos: "0 < E T" if "T \<subseteq> S" for T
    unfolding E_def using that by (intro real_eval_sqPoleProd_pos) (use assms finite_subset in auto)
  have Erem: "E S = (t + real j ^ 2) * E (S - {j})" if j: "j \<in> S" for j
    unfolding E_def sqPoleProd_def real_eval_prod prod.remove[OF S j]
    by (simp add: real_eval_simps of_rat_power)
  have "real_eval P t = real_eval (sqPoleProd S * (P div sqPoleProd S) + (\<Sum> j \<in>
    S. [:sqResidue S P j:] * sqPoleProd (S - {j}))) t"
    by (rule arg_cong[where f = "\<lambda>R. real_eval R t", OF sq_lagrange[OF S]])
  hence L: "real_eval P t = E S * real_eval Q t + (\<Sum> j \<in> S. of_rat (r j) * E (S - {j}))"
    by (simp add: E_def Q_def r_def real_eval_simps)
  have "real_eval P t / E S = real_eval Q t + (\<Sum> j \<in> S. of_rat (r j) * E (S - {j}) / E S)"
    unfolding L using Epos[of S] by (simp add: add_divide_distrib sum_divide_distrib)
  also have "(\<Sum> j \<in> S. of_rat (r j) * E (S - {j}) / E S) = (\<Sum> j \<in>
    S. of_rat (r j) / (t + real j ^ 2))"
  proof (rule sum.cong[OF refl])
    fix j assume j: "j \<in> S"
    have "0 < E (S - {j})" by (rule Epos) auto
    hence E0: "E (S - {j}) \<noteq> 0" by simp
    have "of_rat (r j) * E (S - {j}) / ((t + real j ^ 2) * E (S - {j})) =
      of_rat (r j) / (t + real j ^ 2)"
      by (rule nonzero_mult_divide_mult_cancel_right[OF E0])
    thus "of_rat (r j) * E (S - {j}) / E S = of_rat (r j) / (t + real j ^ 2)"
      unfolding Erem[OF j] .
  qed
  finally show ?thesis unfolding E_def Q_def r_def .
qed

lemma rat_decomp:
  assumes "finite S" "0 \<notin> S"
  shows "real_eval P (y ^ 2) / real_eval (sqPoleProd S) (y ^ 2) * weight y =
         real_eval (P div sqPoleProd S) (y ^ 2) * weight y + (\<Sum> j \<in>
           S. of_rat (sqResidue S P j) * (weight y / (y ^ 2 + real j ^ 2)))"
  unfolding partial_fractions_real[OF assms zero_le_power2]
    by (simp add: distrib_right sum_distrib_right)

lemma rat_integrable:
  assumes "finite S" "0 \<notin> S"
  shows "set_integrable lborel {0<..} (\<lambda>y. real_eval P (y ^ 2) /
    real_eval (sqPoleProd S) (y ^ 2) * weight y)"
proof -
  have e: "(\<lambda>y. real_eval P (y ^ 2) / real_eval (sqPoleProd S) (y ^ 2) * weight y) =
    (\<lambda>y. real_eval (P div sqPoleProd S) (y ^ 2) * weight y + (\<Sum> j \<in>
      S. of_rat (sqResidue S P j) * (weight y / (y ^ 2 + real j ^ 2))))"
    by (rule ext) (rule rat_decomp[OF assms])
  have j0: "j \<noteq> 0" if "j \<in> S" for j using assms(2) that by metis
  have ij: "set_integrable lborel {0<..} (\<lambda>y. of_rat (sqResidue S P j) * (weight y /
    (y ^ 2 + real j ^ 2)))" if "j \<in> S" for j
    by (rule set_integrable_mult_right) (rule conjunct1[OF pole_val[OF j0[OF that]]])
  show ?thesis unfolding e
    by (rule set_integral_add(1)[OF conjunct1[OF poly_moment] conjunct1[OF set_integral_sum_fin[OF
      ij]]])
qed

text \<open>Proposition 2.2, (2.10): @{text "mu_{\<zeta>(5)}(R) =
  \<integral>_0^\<infinity> R(y^2) w(y) dy"} for every @{text R} in the domain.\<close>
theorem muX_zeta5_integral:
  assumes S: "finite S" and S0: "0 \<notin> S"
  shows "real_eval (muX S P) zeta5 =
         set_lebesgue_integral lborel {0<..}
           (\<lambda>y. real_eval P (y ^ 2) / real_eval (sqPoleProd S) (y ^ 2) * weight y)"
proof -
  have j0: "\<And>j. j \<in> S \<Longrightarrow> j \<noteq> 0" using S0 by metis
  have "set_lebesgue_integral lborel {0<..} (\<lambda>y. real_eval P (y ^ 2) /
    real_eval (sqPoleProd S) (y ^ 2) * weight y) =
        set_lebesgue_integral lborel {0<..} (\<lambda>y. real_eval (P div sqPoleProd S) (y ^ 2) *
          weight y)
        + (\<Sum> j \<in> S. of_rat (sqResidue S P j) *
          set_lebesgue_integral lborel {0<..} (\<lambda>y. weight y / (y ^ 2 + real j ^ 2)))"
  proof -
    have e: "(\<lambda>y. real_eval P (y ^ 2) / real_eval (sqPoleProd S) (y ^ 2) * weight y) =
      (\<lambda>y. real_eval (P div sqPoleProd S) (y ^ 2) * weight y + (\<Sum> j \<in>
        S. of_rat (sqResidue S P j) * (weight y / (y ^ 2 + real j ^ 2))))"
      by (rule ext) (rule rat_decomp[OF S S0])
    have ij: "set_integrable lborel {0<..} (\<lambda>y. of_rat (sqResidue S P j) * (weight y /
      (y ^ 2 + real j ^ 2)))" if "j \<in> S" for j
      by (rule set_integrable_mult_right) (rule conjunct1[OF pole_val[OF j0[OF that]]])
    have "set_lebesgue_integral lborel {0<..} (\<lambda>y. real_eval P (y ^ 2) /
      real_eval (sqPoleProd S) (y ^ 2) * weight y) =
        set_lebesgue_integral lborel {0<..} (\<lambda>y. real_eval (P div sqPoleProd S) (y ^ 2) *
          weight y + (\<Sum> j \<in> S. of_rat (sqResidue S P j) * (weight y / (y ^ 2 +
          real j ^ 2))))"
      by (simp only: e)
    also have "\<dots> = set_lebesgue_integral lborel {0<..} (\<lambda>y. real_eval (P div
      sqPoleProd S) (y ^ 2) * weight y) +
        set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> j \<in>
          S. of_rat (sqResidue S P j) * (weight y / (y ^ 2 + real j ^ 2)))"
      by (rule set_integral_add(2)[OF conjunct1[OF poly_moment] conjunct1[OF set_integral_sum_fin[OF
        ij]]])
    also have "set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> j \<in>
      S. of_rat (sqResidue S P j) * (weight y / (y ^ 2 + real j ^ 2))) =
        (\<Sum> j \<in> S. set_lebesgue_integral lborel {0<..} (\<lambda>y. of_rat (sqResidue S P j)
          * (weight y / (y ^ 2 + real j ^ 2))))"
      by (rule conjunct2[OF set_integral_sum_fin[OF ij]])
    also have "\<dots> = (\<Sum> j \<in>
      S. of_rat (sqResidue S P j) * set_lebesgue_integral lborel {0<..} (\<lambda>y. weight y /
      (y ^ 2 + real j ^ 2)))"
      by (simp only: set_integral_mult_right)
    finally show ?thesis .
  qed
  also have "\<dots> = of_rat (muPoly (P div sqPoleProd S)) + (\<Sum> j \<in>
    S. of_rat (sqResidue S P j) * real_eval (muPole j) zeta5)"
    using poly_moment pole_val[OF j0] by (simp cong: sum.cong)
  also have "\<dots> = real_eval (muX S P) zeta5"
    by (simp add: muX_def real_eval_simps)
  finally show ?thesis ..
qed

text \<open>Proposition 2.2: @{text "G_K(\<zeta>(5))"} is positive definite (stated with coefficient
  vectors).\<close>
theorem G_zeta5_posdef:
  assumes c: "\<exists>i<hof K. c i \<noteq> 0"
  shows "0 < (\<Sum> i < hof K. \<Sum> j < hof K. c i * real_eval (GK K $$ (i, j)) zeta5 * c j)"
proof -
  define h where "h = hof K"
  define f where "f = (\<lambda>n y. real_eval (Dm (Nof K) ^ 6 * pX ^ n) (y ^ 2) /
    real_eval (sqPoleProd {1..K}) (y ^ 2) * weight y :: real)"
  define q where "q = (\<lambda>y. \<Sum> i < h. c i * y ^ (2 * i) :: real)"
  have S0: "0 \<notin> {1..K}" by simp
  have entry: "\<And>i j. i < h \<Longrightarrow> j < h \<Longrightarrow>
    real_eval (GK K $$ (i, j)) zeta5 = set_lebesgue_integral lborel {0<..} (f (i + j))"
  proof -
    fix i j assume "i < h" "j < h"
    hence "GK K $$ (i, j) = muX {1..K} (Dm (Nof K) ^ 6 * pX ^ (i + j))" by (simp add: GK_def h_def)
    thus "real_eval (GK K $$ (i, j)) zeta5 = set_lebesgue_integral lborel {0<..} (f (i + j))"
      unfolding f_def by (simp only: muX_zeta5_integral[OF finite_atLeastAtMost S0])
  qed
  have fn: "\<And>n y. f n y = (y ^ 2) ^ n * f 0 y"
  proof -
    fix n :: nat and y :: real
    have a: "real_eval (Dm (Nof K) ^ 6 * pX ^ n) (y ^ 2) =
      real_eval (Dm (Nof K) ^ 6) (y ^ 2) * (y ^ 2) ^ n"
      by (simp only: real_eval_mult real_eval_power real_eval_pX)
    have b: "real_eval (Dm (Nof K) ^ 6 * pX ^ 0) (y ^ 2) = real_eval (Dm (Nof K) ^ 6) (y ^ 2)"
      by (simp only: power_0 mult_1_right)
    show "f n y = (y ^ 2) ^ n * f 0 y" unfolding f_def a b by (simp add: mult_ac)
  qed
  have f0pos: "\<And>y. 0 < y \<Longrightarrow> 0 < f 0 y"
  proof -
    fix y :: real assume y: "0 < y"
    have D: "Dm (Nof K) = sqPoleProd {1..Nof K}" by (simp add: Dm_def sqPoleProd_def)
    have "0 < real_eval (Dm (Nof K)) (y ^ 2)" unfolding D by (rule real_eval_sqPoleProd_pos) auto
    moreover have "0 < real_eval (sqPoleProd {1..K}) (y ^ 2)"
      by (rule real_eval_sqPoleProd_pos) auto
    ultimately show "0 < f 0 y" unfolding f_def using weight_pos[OF y]
      by (simp add: real_eval_mult real_eval_power real_eval_one)
  qed
  have int: "\<And>n. set_integrable lborel {0<..} (f n)" unfolding f_def
    by (rule rat_integrable[OF finite_atLeastAtMost S0])
  have pt: "\<And>y. (\<Sum> i < h. \<Sum> j < h. c i * c j * f (i + j) y) = q y ^ 2 * f 0 y"
  proof -
    fix y :: real
    have s: "c i * c j * f (i + j) y = (c i * y ^ (2 * i)) * (c j * y ^ (2 * j)) * f 0 y" for i j
    proof -
      have p: "(y ^ 2) ^ (i + j) = y ^ (2 * i) * y ^ (2 * j)" by (simp only: power_add power_mult)
      show ?thesis unfolding fn[of "i + j" y] p by (simp add: mult_ac)
    qed
    have "q y ^ 2 = (\<Sum> i < h. \<Sum> j < h. (c i * y ^ (2 * i)) * (c j * y ^ (2 * j)))"
      unfolding q_def power2_eq_square by (rule sum_product)
    hence "q y ^ 2 * f 0 y = (\<Sum> i < h. \<Sum> j <
      h. (c i * y ^ (2 * i)) * (c j * y ^ (2 * j)) * f 0 y)"
      by (simp only: sum_distrib_right)
    also have "\<dots> = (\<Sum> i < h. \<Sum> j < h. c i * c j * f (i + j) y)" by (simp only: s)
    finally show "(\<Sum> i < h. \<Sum> j < h. c i * c j * f (i + j) y) = q y ^ 2 * f 0 y" ..
  qed
  have quad: "(\<Sum> i < h. \<Sum> j < h. c i * real_eval (GK K $$ (i, j)) zeta5 * c j) =
    set_lebesgue_integral lborel {0<..} (\<lambda>y. q y ^ 2 * f 0 y)"
  proof -
    have ii: "set_integrable lborel {0<..} (\<lambda>y. c i * c j * f (i + j) y)" for i j
      by (rule set_integrable_mult_right) (rule int)
    have "(\<Sum> i < h. \<Sum> j < h. c i * real_eval (GK K $$ (i, j)) zeta5 * c j) =
          (\<Sum> i < h. \<Sum> j < h. set_lebesgue_integral lborel {0<..} (\<lambda>y. c i * c j *
            f (i + j) y))"
      by (intro sum.cong refl) (simp add: entry set_integral_mult_right mult_ac)
    also have "\<dots> = (\<Sum> i < h. set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> j <
      h. c i * c j * f (i + j) y))"
      by (intro sum.cong refl) (rule conjunct2[OF set_integral_sum_fin[OF ii], symmetric])
    also have "\<dots> = set_lebesgue_integral lborel {0<..} (\<lambda>y. \<Sum> i < h. \<Sum> j <
      h. c i * c j * f (i + j) y)"
      by (rule conjunct2[OF set_integral_sum_fin,
        symmetric]) (rule conjunct1[OF set_integral_sum_fin[OF ii]])
    also have "\<dots> = set_lebesgue_integral lborel {0<..} (\<lambda>y. q y ^ 2 * f 0 y)"
      by (simp only: pt)
    finally show ?thesis .
  qed
  have Fint: "set_integrable lborel {0<..} (\<lambda>y. q y ^ 2 * f 0 y)"
  proof -
    have ii: "set_integrable lborel {0<..} (\<lambda>y. c i * c j * f (i + j) y)" for i j
      by (rule set_integrable_mult_right) (rule int)
    have "set_integrable lborel {0<..} (\<lambda>y. \<Sum> i < h. \<Sum> j <
      h. c i * c j * f (i + j) y)"
      by (rule conjunct1[OF set_integral_sum_fin]) (rule conjunct1[OF set_integral_sum_fin[OF ii]])
    thus ?thesis by (simp only: pt)
  qed
  have qne: "finite {y. q y = 0}"
  proof -
    define Q where "Q = (\<Sum> i < h. Polynomial.monom (c i) (2 * i))"
    have pq: "poly Q y = q y" for y by (simp add: Q_def q_def poly_sum poly_monom)
    obtain i0 where i0: "i0 < h" "c i0 \<noteq> 0" using c unfolding h_def by blast
    have "Polynomial.coeff Q (2 * i0) = c i0" using i0(1) by (simp add: Q_def coeff_sum coeff_monom)
    hence "Q \<noteq> 0" using i0(2) by auto
    hence "finite {y. poly Q y = 0}" by (rule poly_roots_finite)
    thus ?thesis unfolding pq .
  qed
  have "0 < set_lebesgue_integral lborel {0<..} (\<lambda>y. q y ^ 2 * f 0 y)"
  proof -
    define G where "G y = indicator {0<..} y *\<^sub>R (q y ^ 2 * f 0 y)" for y :: real
    have Gi: "integrable lborel G" using Fint unfolding set_integrable_def G_def .
    have Gnn: "0 \<le> G y" for y using f0pos[of y] by (cases "0 < y") (simp_all add: G_def)
    have Gpos: "0 < G y" if "0 < y" "q y \<noteq> 0" for y using that f0pos[of y]
      by (simp add: G_def)
    have "0 \<le> integral\<^sup>L lborel G" by (rule integral_nonneg_AE) (simp add: Gnn)
    moreover have "integral\<^sup>L lborel G \<noteq> 0"
    proof
      assume "integral\<^sup>L lborel G = 0"
      hence "AE x in lborel. G x = 0" using integral_nonneg_eq_0_iff_AE[OF Gi] Gnn by blast
      then obtain N where N: "{x \<in> space lborel. G x \<noteq> 0} \<subseteq>
        N" "emeasure lborel N = 0" "N \<in> sets lborel" by (rule AE_E)
      have Nn: "N \<in> null_sets lborel" using N(2,3) by blast
      have Zn: "{y. q y = 0} \<in> null_sets lborel" by (rule finite_imp_null_set_lborel[OF qne])
      have sub: "{1..2::real} \<subseteq> N \<union> {y. q y = 0}"
      proof
        fix y :: real assume y: "y \<in> {1..2}"
        show "y \<in> N \<union> {y. q y = 0}"
        proof (cases "q y = 0")
          case False
          hence "G y \<noteq> 0" using Gpos[of y] y by force
          thus ?thesis using N(1) by auto
        qed simp
      qed
      have "{1..2::real} \<in> null_sets lborel"
        by (rule null_sets_subset[OF null_sets.Un[OF Nn Zn] _ sub]) simp
      thus False by (simp add: null_sets_def)
    qed
    ultimately show ?thesis unfolding set_lebesgue_integral_def G_def by linarith
  qed
  thus ?thesis unfolding quad[symmetric] h_def .
qed


text \<open>Consequence: @{text "\<Delta>_K(\<zeta>(5)) > 0"} (positive definite
  \<open>\<Rightarrow>\<close> positive determinant; alternatively
  from Andreief with a positive integrand).\<close>
lemma real_eval_hom: "comm_ring_hom (\<lambda>P. real_eval P x)"
  by unfold_locales (simp_all add: real_eval_def re_map_add re_map_mult)

theorem Delta_zeta5_pos_aux: "0 < real_eval (DeltaK K) zeta5"
proof -
  define G where "G = map_mat (\<lambda>P. real_eval P zeta5) (GK K)"
  have Gc: "G \<in> carrier_mat (hof K) (hof K)" by (simp add: G_def GK_def)
  have "real_eval (DeltaK K) zeta5 = Determinant.det G"
    unfolding DeltaK_def G_def by (rule comm_ring_hom.hom_det[OF real_eval_hom, symmetric])
  also have "0 < Determinant.det G"
  proof (rule posdef_det_pos[OF Gc])
    fix c :: "nat \<Rightarrow> real" assume c: "\<exists>i<hof K. c i \<noteq> 0"
    have "(\<Sum> i < hof K. \<Sum> j < hof K. c i * G $$ (i, j) * c j)
        = (\<Sum> i < hof K. \<Sum> j < hof K. c i * real_eval (GK K $$ (i, j)) zeta5 * c j)"
      by (intro sum.cong refl) (simp add: G_def GK_def)
    also have "0 < \<dots>" by (rule G_zeta5_posdef[OF c])
    finally show "0 < (\<Sum> i < hof K. \<Sum> j < hof K. c i * G $$ (i, j) * c j)" .
  qed
  finally show ?thesis .
qed

theorem Delta_zeta5_pos: "0 < real_eval (DeltaK K) zeta5"
  by (rule Delta_zeta5_pos_aux)

end


