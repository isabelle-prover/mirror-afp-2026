(*  Title:   Unimodular_Determinants.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Unimodular_Determinants
  imports Rational_Padic_Valuations
begin

section \<open>Determinants of \<open>p\<close>-integral matrices and a unimodularity
  criterion\<close>

text \<open>The determinant of a matrix with \<open>p\<close>-integral entries is
  \<open>p\<close>-integral; modulo \<open>p\<close> the
  determinant of a matrix that is lower triangular modulo \<open>p\<close> is the product of its
    diagonal;
  hence if \<open>M V = T\<close> with \<open>M\<close>,
    \<open>V\<close> \<open>p\<close>-integral and \<open>T\<close> lower triangular modulo
    \<open>p\<close> with unit
  diagonal, then \<open>det M\<close> is a \<open>p\<close>-adic unit.  This is the tool behind the
    unimodularity of the
  inner and outer bases of the irrationality proof, but it is stated for arbitrary matrices.\<close>

text \<open>The determinant of a matrix with @{text p}-integral entries is
  @{text p}-integral.\<close>
lemma vge_det_integral:
  assumes "prime p" "A \<in> carrier_mat n n" "\<And>i j. i < n \<Longrightarrow>
    j < n \<Longrightarrow> vge p (A $$ (i, j)) 0"
  shows "vge p (Determinant.det A) 0"
proof -
  have p: "prime p" and A: "A \<in> carrier_mat n n" and Ai: "\<And>i j. i < n \<Longrightarrow>
    j < n \<Longrightarrow> vge p (A $$ (i, j)) 0"
    using assms  by auto
  have d: "Determinant.det A = (\<Sum> \<sigma> \<in>
    {\<sigma>. \<sigma> permutes {0..<n}}. signof \<sigma> * (\<Prod> i =
    0..<n. A $$ (i, \<sigma> i)))"
    using det_def'[OF A]  by simp
  have "vge p (\<Sum> \<sigma> \<in> {\<sigma>. \<sigma> permutes {0..<n}}. signof \<sigma> *
    (\<Prod> i = 0..<n. A $$ (i, \<sigma> i))) 0"
  proof (rule vge_sum[OF p])
    show "finite {\<sigma>. \<sigma> permutes {0..<n}}" using finite_permutations  by blast
    fix \<sigma> assume "\<sigma> \<in> {\<sigma>. \<sigma> permutes {0..<n}}"
    hence s: "\<sigma> permutes {0..<n}"  by simp
    have sg: "vge p (signof \<sigma>) 0" using vge_of_int[OF p]  by simp
    have pr: "vge p (\<Prod> i = 0..<n. A $$ (i, \<sigma> i)) 0"
      using vge_prod0[OF p, of "{0..<n}" "\<lambda>i. A $$ (i,
        \<sigma> i)"] Ai permutes_in_image[OF s]  by simp
    show "vge p (signof \<sigma> * (\<Prod> i = 0..<n. A $$ (i, \<sigma> i))) 0"
      using vge_mul[OF p sg pr]  by simp
  qed
  thus ?thesis using d  by simp
qed

text \<open>A permutation of @{text "{0..<n}"} that is not the identity moves some @{text i}
  downwards
  (stated for @{text nat}; a version with an unaxiomatised @{text ord} type would be false).\<close>
lemma permutes_not_id_exists_lt_nat:
  fixes \<sigma> :: "nat \<Rightarrow> nat"
  assumes "\<sigma> permutes {0..<n}" "\<sigma> \<noteq> id"
  shows "\<exists>i < n. \<sigma> i < i"
proof (rule ccontr)
  assume nl: "\<not> (\<exists>i < n. \<sigma> i < i)"
  have s: "\<sigma> permutes {0..<n}" using assms(1) .
  have le: "\<forall>i \<in> {0..<n}. i \<le> \<sigma> i" using nl by force
  have sm: "(\<Sum> i \<in> {0..<n}. i) = (\<Sum> i \<in> {0..<n}. \<sigma> i)"
    using sum.permute[OF s, of "\<lambda>i. i"] by (simp add: o_def)
  have eq: "\<forall>i \<in> {0..<n}. \<sigma> i = i"
  proof (rule ccontr)
    assume "\<not> (\<forall>i \<in> {0..<n}. \<sigma> i = i)"
    then obtain j where j: "j \<in> {0..<n}" "\<sigma> j \<noteq> j" by blast
    have "\<exists>a \<in> {0..<n}. a < \<sigma> a" using j le by force
    hence "(\<Sum> i \<in> {0..<n}. i) < (\<Sum> i \<in> {0..<n}. \<sigma> i)"
      using sum_strict_mono_ex1[of "{0..<n}" "\<lambda>i. i" \<sigma>] le by blast
    thus False using sm by linarith
  qed
  have "\<sigma> = id"
  proof (rule ext)
    fix i
    show "\<sigma> i = id i" using eq permutes_not_in[OF s, of i] by auto
  qed
  thus False using assms(2) by simp
qed

text \<open>Modulo @{text p}, the determinant of a matrix whose entries below the diagonal are
  divisible by @{text p}
  is the product of the diagonal.\<close>
lemma det_cong_diag:
  assumes p: "prime p" and T: "T \<in> carrier_mat n n"
    and int: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> vge p (T $$ (i, j)) 0"
    and low: "\<And>i j. j < i \<Longrightarrow> i < n \<Longrightarrow> vge p (T $$ (i, j)) 1"
  shows "vge p (Determinant.det T - (\<Prod> i < n. T $$ (i, i))) 1"
proof -
  let ?S = "{\<sigma>. \<sigma> permutes {0..<n}}"
  let ?f = "\<lambda>\<sigma>. signof \<sigma> * (\<Prod> i = 0..<n. T $$ (i, \<sigma> i))"
  have fS: "finite ?S" using finite_permutations  by blast
  have idS: "id \<in> ?S" using permutes_id  by simp
  have "Determinant.det T = ?f id + (\<Sum> \<sigma> \<in> ?S - {id}. ?f \<sigma>)"
    using det_def'[OF T] sum.remove[OF fS idS, of ?f]  by simp
  moreover have "?f id = (\<Prod> i < n. T $$ (i, i))" using sign_id atLeast0LessThan
    by (simp add: atLeast0LessThan)
  moreover have "vge p (\<Sum> \<sigma> \<in> ?S - {id}. ?f \<sigma>) 1"
  proof (rule vge_sum[OF p])
    show "finite (?S - {id})" using fS  by simp
    fix \<sigma> assume "\<sigma> \<in> ?S - {id}"
    hence s: "\<sigma> permutes {0..<n}" and ns: "\<sigma> \<noteq> id"  by auto
    obtain i where i: "i < n" "\<sigma> i < i" using permutes_not_id_exists_lt_nat[OF s ns] by blast
    have si: "\<And>j. j < n \<Longrightarrow> \<sigma> j < n" using permutes_in_image[OF s]
      by simp
    have pr: "(\<Prod> j = 0..<n. T $$ (j, \<sigma> j)) = T $$ (i, \<sigma> i) * (\<Prod> j \<in>
      {0..<n} - {i}. T $$ (j, \<sigma> j))"
      using prod.remove[of "{0..<n}" i "\<lambda>j. T $$ (j, \<sigma> j)"] i  by simp
    have v1: "vge p (T $$ (i, \<sigma> i)) 1" using low[OF i(2) i(1)]  by simp
    have "vge p (\<Prod> j \<in> {0..<n} - {i}. T $$ (j, \<sigma> j)) 0"
      using vge_prod0[OF p, of "{0..<n} - {i}" "\<lambda>j. T $$ (j, \<sigma> j)"] int si  by simp
    hence v: "vge p (T $$ (i, \<sigma> i) * (\<Prod> j \<in>
      {0..<n} - {i}. T $$ (j, \<sigma> j))) (1 + 0)" by (rule vge_mul[OF p v1])
    have sg: "vge p (signof \<sigma>) 0" using vge_of_int[OF p]  by simp
    have "vge p (signof \<sigma> * (\<Prod> j = 0..<n. T $$ (j, \<sigma> j))) (0 + (1 + 0))"
      unfolding pr by (rule vge_mul[OF p sg v])
    thus "vge p (signof \<sigma> * (\<Prod> i = 0..<n. T $$ (i, \<sigma> i))) 1"  by simp
  qed
  ultimately show ?thesis  by simp
qed

text \<open>The unimodularity criterion:
  if @{text "M V = T"} with @{text M}, @{text V} @{text p}-integral and @{text T} upper triangular
  modulo @{text p} with unit diagonal, then @{text "det M"} is a @{text p}-adic unit.\<close>
lemma unimodular_criterion:
  assumes p: "prime p" and M: "M \<in> carrier_mat n n" and V: "V \<in> carrier_mat n n"
    and Mi: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> vge p (M $$ (i, j)) 0"
    and Vi: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> vge p (V $$ (i, j)) 0"
    and low: "\<And>i j. j < i \<Longrightarrow> i < n \<Longrightarrow>
      vge p ((M * V) $$ (i, j)) 1"
    and diag: "\<And>i. i < n \<Longrightarrow> (M * V) $$ (i, i) \<noteq> 0 \<and>
      vp p ((M * V) $$ (i, i)) = 0"
  shows "Determinant.det M \<noteq> 0 \<and> vp p (Determinant.det M) = 0"
proof -
  define T where "T = M * V"
  have Tc: "T \<in> carrier_mat n n" using M V by (simp add: T_def)
  have Ti: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> vge p (T $$ (i, j)) 0"
  proof -
    fix i j assume i: "i < n" and j: "j < n"
    have e: "T $$ (i, j) = (\<Sum> k \<in> {0..<n}. M $$ (i, k) * V $$ (k, j))"
      using i j M V unfolding T_def  by (simp add: index_mult_mat scalar_prod_def)
    have "vge p (\<Sum> k \<in> {0..<n}. M $$ (i, k) * V $$ (k, j)) 0"
    proof (rule vge_sum[OF p])
      show "finite {0..<n}"  by simp
      fix k assume "k \<in> {0..<n}"
      hence k: "k < n"  by simp
      have "vge p (M $$ (i, k) * V $$ (k, j)) (0 + 0)" by (rule vge_mul[OF p Mi[OF i k] Vi[OF k j]])
      thus "vge p (M $$ (i, k) * V $$ (k, j)) 0"  by simp
    qed
    thus "vge p (T $$ (i, j)) 0" using e  by simp
  qed
  have detT: "Determinant.det T = Determinant.det M * Determinant.det V"
    unfolding T_def by (rule det_mult[OF M V])
  have dprod: "(\<Prod> i < n. T $$ (i, i)) \<noteq> 0 \<and> vp p (\<Prod> i < n. T $$ (i, i)) = 0"
  proof -
    have dg: "\<And>i. i < n \<Longrightarrow> T $$ (i, i) \<noteq> 0 \<and>
      vp p (T $$ (i, i)) = 0" using diag unfolding T_def  by simp
    have ne: "(\<Prod> i < n. T $$ (i, i)) \<noteq> 0" using dg  by simp
    have "vp p (\<Prod> i < n. T $$ (i, i)) = (\<Sum> i < n. vp p (T $$ (i, i)))"
      using vp_prod_rat[OF p, of "{..<n}" "\<lambda>i. T $$ (i, i)"] dg  by simp
    also have "\<dots> = 0" using dg  by simp
    finally show ?thesis using ne  by simp
  qed
  have cong: "vge p (Determinant.det T - (\<Prod> i < n. T $$ (i, i))) 1"
    using det_cong_diag[OF p Tc Ti] T_def low by blast
  have dT: "Determinant.det T \<noteq> 0 \<and> vp p (Determinant.det T) = 0"
  proof -
    define w where "w = (\<Prod> i < n. T $$ (i, i))"
    define u where "u = Determinant.det T - w"
    have du: "Determinant.det T = w + u" unfolding u_def  by simp
    have w: "w \<noteq> 0" "vp p w = 0" using dprod unfolding w_def  by auto
    show ?thesis
    proof (cases "u = 0")
      case True
      thus ?thesis using du w  by simp
    next
      case False
      have "1 \<le> vp p u" using cong False unfolding u_def w_def vge_def  by simp
      hence "vp p w < vp p u" using w  by simp
      hence "w + u \<noteq> 0 \<and> vp p (w + u) = vp p w"
        by (rule vp_add_eq_of_lt[OF p w(1) False])
      thus ?thesis using du w  by simp
    qed
  qed
  have vM: "vge p (Determinant.det M) 0" by (rule vge_det_integral[OF p M Mi])
  have vV: "vge p (Determinant.det V) 0" by (rule vge_det_integral[OF p V Vi])
  have dM: "Determinant.det M \<noteq> 0" and dV: "Determinant.det V \<noteq> 0" using dT detT
    by auto
  have pe: "prime_elem (int p)" using p prime_nat_int_transfer  by simp
  have s: "vp p (Determinant.det T) = vp p (Determinant.det M) + vp p (Determinant.det V)"
    unfolding detT vp_def using qmultiplicity_mult[OF pe dM dV]  by simp
  have gM: "0 \<le> vp p (Determinant.det M)" using vM dM unfolding vge_def  by simp
  have gV: "0 \<le> vp p (Determinant.det V)" using vV dV unfolding vge_def  by simp
  show ?thesis using dM s gM gV dT  by simp
qed

end
