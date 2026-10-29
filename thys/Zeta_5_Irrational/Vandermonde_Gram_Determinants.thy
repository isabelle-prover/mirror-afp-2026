(*  Title:   Vandermonde_Gram_Determinants.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Vandermonde_Gram_Determinants
  imports "Jordan_Normal_Form.Determinant"
begin

section \<open>Vandermonde and Gram determinants for JNF matrices\<close>

text \<open>The Vandermonde determinant \<open>det (x\<^sub>i\<^sup>j) =
  \<Prod>\<^sub>i\<^sub><\<^sub>j (x\<^sub>j - x\<^sub>i)\<close> for the matrices of the
  Jordan\_Normal\_Form library (HOL-Analysis has it only for its own matrix type, and the AFP not
  at all), the factorisation of row scalings out of a determinant, and the positivity of the
  determinant of a positive definite (Gram) matrix, proved by a homotopy to the identity.\<close>

text \<open>Vandermonde determinant for Jordan\_Normal\_Form matrices (absent from HOL and the
  AFP).\<close>
lemma det_diag_scale_rows:
  fixes d y :: "nat \<Rightarrow> 'a :: comm_ring_1"
  shows "Determinant.det (Matrix.mat n n (\<lambda>(i, j). d i * y i ^ j))
           = (\<Prod> i < n. d i) * Determinant.det (Matrix.mat n n (\<lambda>(i, j). y i ^ j))"
proof -
  define D where "D = Matrix.mat n n (\<lambda>(i, j). if i = j then d i else (0 :: 'a))"
  define V where "V = Matrix.mat n n (\<lambda>(i, j). y i ^ j)"
  have Dc: "D \<in> carrier_mat n n" and Vc: "V \<in> carrier_mat n n"
    by (simp_all add: D_def V_def)
  have "Matrix.mat n n (\<lambda>(i, j). d i * y i ^ j) = D * V"
  proof (rule eq_matI)
    fix i j assume ij: "i < dim_row (D * V)" "j < dim_col (D * V)"
    hence i: "i < n" and j: "j < n" by (simp_all add: D_def V_def)
    have "(D * V) $$ (i, j) = (\<Sum> k \<in> {0..<n}. (if i = k then d i else 0) * y k ^ j)"
      using i j by (simp add: D_def V_def scalar_prod_def)
    also have "\<dots> = d i * y i ^ j" using i
      by (simp add: if_distrib[where f = "\<lambda>z. z * _"] cong: if_cong)
    finally show "Matrix.mat n n (\<lambda>(i, j). d i * y i ^ j) $$ (i, j) = (D * V) $$ (i, j)"
      using i j by simp
  qed (simp_all add: D_def V_def)
  hence "Determinant.det (Matrix.mat n n (\<lambda>(i, j). d i * y i ^ j)) =
    Determinant.det D * Determinant.det V"
    using det_mult[OF Dc Vc] by simp
  also have "Determinant.det D = (\<Prod> i < n. d i)"
  proof -
    have "upper_triangular D" by (auto simp: D_def upper_triangular_def)
    hence "Determinant.det D = prod_list (diag_mat D)" by (rule det_upper_triangular[OF _ Dc])
    also have "\<dots> = (\<Prod> i < n. d i)"
      unfolding prod_list_diag_prod by (rule prod.cong) (auto simp: D_def)
    finally show ?thesis .
  qed
  finally show ?thesis by (simp add: V_def)
qed

lemma det_vandermonde_step:
  fixes x :: "nat \<Rightarrow> 'a :: comm_ring_1"
  shows "Determinant.det (Matrix.mat (Suc n) (Suc n) (\<lambda>(i, j). x i ^ j))
           = (\<Prod> i < n. x (Suc i) - x 0) * Determinant.det (Matrix.mat n n (\<lambda>(i,
             j). x (Suc i) ^ j))"
proof -
  define m where "m = Suc n"
  define V where "V = Matrix.mat m m (\<lambda>(i, j). x i ^ j)"
  define U where "U = Matrix.mat m m (\<lambda>(i, j). (if i = j then 1 else 0) + (if Suc i =
    j then - x 0 else (0 :: 'a)))"
  define W where "W = V * U"
  have Vc: "V \<in> carrier_mat m m" and Uc: "U \<in> carrier_mat m m"
    by (simp_all add: V_def U_def)
  have Wc: "W \<in> carrier_mat m m" using Vc Uc by (simp add: W_def)
  have dU: "Determinant.det U = 1"
  proof -
    have "upper_triangular U" by (auto simp: U_def upper_triangular_def)
    hence "Determinant.det U = prod_list (diag_mat U)" by (rule det_upper_triangular[OF _ Uc])
    also have "\<dots> = 1" unfolding prod_list_diag_prod by (rule prod.neutral) (auto simp: U_def)
    finally show ?thesis .
  qed
  have dW: "Determinant.det W = Determinant.det V" unfolding W_def det_mult[OF Vc Uc] dU by simp
  have Wij: "W $$ (i, j) = (if j = 0 then 1 else x i ^ j - x 0 * x i ^ (j - 1))"
    if i: "i < m" and j: "j < m" for i j
  proof -
    have "W $$ (i, j) = (\<Sum> k \<in> {0..<m}. x i ^ k * ((if k = j then 1 else 0) + (if Suc k =
      j then - x 0 else 0)))"
      using i j by (simp add: W_def V_def U_def scalar_prod_def)
    also have "\<dots> = (\<Sum> k \<in> {0..<m}.
      if k = j then x i ^ k else 0) + (\<Sum> k \<in> {0..<m}.
      if Suc k = j then - (x 0 * x i ^ k) else 0)"
      by (simp add: sum.distrib distrib_left if_distrib[where f =
        "\<lambda>z. _ * z"] mult.commute cong: if_cong)
    also have "\<dots> = (if j = 0 then 1 else x i ^ j - x 0 * x i ^ (j - 1))"
    proof (cases j)
      case 0 thus ?thesis using j by simp
    next
      case (Suc j')
      thus ?thesis using j by simp
    qed
    finally show ?thesis .
  qed
  have "Determinant.det W = (\<Sum> j < m. W $$ (0, j) * cofactor W 0 j)"
    by (rule laplace_expansion_row[OF Wc]) (simp add: m_def)
  also have "\<dots> = cofactor W 0 0"
    unfolding m_def sum.lessThan_Suc_shift using Wij[of 0] by (simp add: m_def power_Suc)
  also have "\<dots> = Determinant.det (mat_delete W 0 0)" by (simp add: cofactor_def)
  also have "mat_delete W 0 0 = Matrix.mat n n (\<lambda>(i, j). (x (Suc i) - x 0) * x (Suc i) ^ j)"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (Matrix.mat n n (\<lambda>(i,
      j). (x (Suc i) - x 0) * x (Suc i) ^ j))"
      "j < dim_col (Matrix.mat n n (\<lambda>(i, j). (x (Suc i) - x 0) * x (Suc i) ^ j))"
    hence ij: "i < n" "j < n" by simp_all
    have "mat_delete W 0 0 $$ (i, j) = W $$ (Suc i, Suc j)"
      using ij Wc by (simp add: mat_delete_def m_def)
    also have "\<dots> = (x (Suc i) - x 0) * x (Suc i) ^ j" using ij
      by (simp add: Wij m_def algebra_simps)
    finally show "mat_delete W 0 0 $$ (i, j) =
      Matrix.mat n n (\<lambda>(i, j). (x (Suc i) - x 0) * x (Suc i) ^ j) $$ (i, j)"
      using ij by simp
  qed (use Wc in \<open>simp_all add: m_def\<close>)
  also have "Determinant.det \<dots> = (\<Prod> i <
    n. x (Suc i) - x 0) * Determinant.det (Matrix.mat n n (\<lambda>(i, j). x (Suc i) ^ j))"
    by (rule det_diag_scale_rows)
  finally show ?thesis using dW by (simp add: V_def m_def)
qed

lemma det_vandermonde_jnf:
  "Determinant.det (Matrix.mat n n (\<lambda>(i, j). (x i :: 'a :: comm_ring_1) ^ j))
     = (\<Prod> i < n. \<Prod> j \<in> {j. i < j \<and> j < n}. x j - x i)"
proof (induction n arbitrary: x)
  case 0
  thus ?case by (simp add: det_def'[of _ 0])
next
  case (Suc n)
  have s1: "{j. 0 < j \<and> j < Suc n} = Suc ` {..<n}"
    by (auto simp: image_iff) (metis Suc_pred lessThan_iff less_Suc_eq_0_disj not_less_eq)
  have s2: "{j. Suc i < j \<and> j < Suc n} = Suc ` {j. i < j \<and> j < n}" for i
    by (auto simp: image_iff) (metis Suc_lessE less_Suc_eq_0_disj not_less_eq)
  have "(\<Prod> i < Suc n. \<Prod> j \<in> {j. i < j \<and> j < Suc n}. x j - x i)
      = (\<Prod> j \<in> {j. 0 < j \<and>
        j < Suc n}. x j - x 0) * (\<Prod> i < n. \<Prod> j \<in> {j. Suc i < j \<and>
        j < Suc n}. x j - x (Suc i))"
    by (simp only: prod.lessThan_Suc_shift)
  also have "\<dots> = (\<Prod> i < n. x (Suc i) - x 0) * (\<Prod> i < n. \<Prod> j \<in> {j. i <
    j \<and> j < n}. x (Suc j) - x (Suc i))"
    unfolding s1 s2 by (simp add: prod.reindex)
  finally show ?case unfolding det_vandermonde_step Suc[of "\<lambda>i. x (Suc i)"] by simp
qed

text \<open>A Gram matrix of linearly independent functions has positive determinant (used for
  @{text "\<Delta>_K(\<zeta>(5)) > 0"} unless the Andreief route is taken).\<close>
lemma posdef_det_nonzero:
  fixes B :: "real mat"
  assumes B: "B \<in> carrier_mat n n"
    and pd: "\<And>c :: nat \<Rightarrow> real. (\<exists>i<n. c i \<noteq> 0) \<Longrightarrow>
      0 < (\<Sum> i < n. \<Sum> j < n. c i * B $$ (i, j) * c j)"
  shows "Determinant.det B \<noteq> 0"
proof
  assume "Determinant.det B = 0"
  then obtain v where v: "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" "B *\<^sub>v v =
    0\<^sub>v n"
    using det_0_iff_vec_prod_zero[OF B] by blast
  define c where "c i = (if i < n then v $ i else 0)" for i
  have "\<exists>i<n. c i \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>i<n. c i \<noteq> 0)"
    hence "v = 0\<^sub>v n" using v(1) by (intro eq_vecI) (auto simp: c_def)
    thus False using v(2) by simp
  qed
  hence pos: "0 < (\<Sum> i < n. \<Sum> j < n. c i * B $$ (i, j) * c j)" by (rule pd)
  have row: "(\<Sum> j < n. B $$ (i, j) * c j) = 0" if i: "i < n" for i
  proof -
    have "(B *\<^sub>v v) $ i = 0" using v(3) i by simp
    moreover have "(B *\<^sub>v v) $ i = (\<Sum> j < n. B $$ (i, j) * c j)"
      using i B v(1) by (simp add: index_mult_mat_vec scalar_prod_def c_def lessThan_atLeast0)
    ultimately show ?thesis by simp
  qed
  have "(\<Sum> i < n. \<Sum> j < n. c i * B $$ (i, j) * c j) = (\<Sum> i < n. c i * (\<Sum> j <
    n. B $$ (i, j) * c j))"
    by (simp add: sum_distrib_left mult.assoc)
  also have "\<dots> = 0" by (simp add: row)
  finally show False using pos by simp
qed

lemma posdef_det_pos:
  assumes "A \<in> carrier_mat n n"
    and "\<And>c :: nat \<Rightarrow> real. (\<exists>i<n. c i \<noteq> 0) \<Longrightarrow>
      0 < (\<Sum> i < n. \<Sum> j < n. c i * A $$ (i, j) * c j)"
  shows "0 < Determinant.det A"
proof (rule ccontr)
  assume neg: "\<not> 0 < Determinant.det A"
  define B where "B t = Matrix.mat n n (\<lambda>(i, j). t * A $$ (i, j) + (1 - t) * (if i =
    j then 1 else 0))" for t :: real
  define f where "f t = Determinant.det (B t)" for t
  have Bc: "B t \<in> carrier_mat n n" for t by (simp add: B_def)
  have B0: "B 0 = 1\<^sub>m n" by (rule eq_matI) (auto simp: B_def)
  have B1: "B 1 = A" by (rule eq_matI) (use assms(1) in \<open>auto simp: B_def\<close>)
  have f0: "f 0 = 1" by (simp add: f_def B0)
  have f1: "f 1 \<le> 0" using neg by (simp add: f_def B1)
  have fne: "f t \<noteq> 0" if t: "0 \<le> t" "t \<le> 1" for t
    unfolding f_def
  proof (rule posdef_det_nonzero[OF Bc])
    fix c :: "nat \<Rightarrow> real" assume c: "\<exists>i<n. c i \<noteq> 0"
    define QA where "QA = (\<Sum> i < n. \<Sum> j < n. c i * A $$ (i, j) * c j)"
    define S where "S = (\<Sum> i < n. c i * c i)"
    have QA: "0 < QA" unfolding QA_def by (rule assms(2)[OF c])
    have S: "0 < S"
    proof -
      obtain i where i: "i < n" "c i \<noteq> 0" using c by blast
      have "c i * c i \<le> S" unfolding S_def using i(1)
        by (intro member_le_sum) auto
      moreover have "0 < c i * c i" using i(2) not_real_square_gt_zero by blast
      ultimately show ?thesis by linarith
    qed
    have "(\<Sum> i < n. \<Sum> j < n. c i * B t $$ (i, j) * c j)
        = (\<Sum> i < n. \<Sum> j < n. t * (c i * A $$ (i, j) * c j) + (if i =
          j then (1 - t) * (c i * c j) else 0))"
      by (intro sum.cong refl) (auto simp: B_def algebra_simps)
    also have "\<dots> = t * QA + (1 - t) * S"
      by (simp add: sum.distrib sum_distrib_left QA_def S_def sum.delta')
    finally have e: "(\<Sum> i < n. \<Sum> j < n. c i * B t $$ (i, j) * c j) =
      t * QA + (1 - t) * S" .
    have "0 < t * QA + (1 - t) * S"
    proof (cases "t = 0")
      case True thus ?thesis using S by simp
    next
      case False
      hence "0 < t * QA" using t QA by simp
      moreover have "0 \<le> (1 - t) * S" using t S by simp
      ultimately show ?thesis by linarith
    qed
    thus "0 < (\<Sum> i < n. \<Sum> j < n. c i * B t $$ (i, j) * c j)" unfolding e .
  qed
  have fdef: "f t = (\<Sum> p | p permutes {0..<n}. of_int (Permutations.sign p) *
                 (\<Prod> i = 0..<n. t * A $$ (i, p i) + (1 - t) * (if i = p i then 1 else 0)))"
                   for t
    unfolding f_def det_def'[OF Bc]
  proof (intro sum.cong refl arg_cong[where f = "\<lambda>x. _ * x"] prod.cong)
    fix p i assume "p \<in> {p. p permutes {0..<n}}" "i \<in> {0..<n}"
    hence "p i < n" "i < n" by (auto simp: permutes_in_image)
    thus "B t $$ (i, p i) = t * A $$ (i, p i) + (1 - t) * (if i = p i then 1 else 0)"
      by (simp add: B_def)
  qed
  have cont: "continuous_on {0..1} f"
    unfolding fdef[abs_def] by (intro continuous_intros)
  obtain x where "0 \<le> x" "x \<le> 1" "f x = 0"
    using IVT2'[of f 1 0 0, OF f1 _ _ cont] f0 by auto
  thus False using fne by blast
qed

end
