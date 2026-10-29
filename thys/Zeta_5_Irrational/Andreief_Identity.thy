(*  Title:   Andreief_Identity.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Andreief_Identity
  imports "Jordan_Normal_Form.Determinant" "HOL-Analysis.Analysis"
begin

section \<open>Andreief's identity (continuous Cauchy--Binet)\<close>

text \<open>For a \<open>\<sigma>\<close>-finite measure \<open>\<mu>\<close> and functions
  \<open>\<phi>\<^sub>i, \<psi>\<^sub>j\<close> with \<open>\<phi>\<^sub>i \<psi>\<^sub>j\<close>
  integrable,
  \<open>det [\<integral> \<phi>\<^sub>i \<psi>\<^sub>j d\<mu>] =
    (1/n!) \<integral> det [\<phi>\<^sub>a(x\<^sub>b)] det [\<psi>\<^sub>a(x\<^sub>b)]
    d\<mu>\<^sup>\<otimes>\<^sup>n\<close>, with the determinants of the
  Jordan\_Normal\_Form library and the product measure @{const PiM}; also the transposition and
  column-scaling rules for determinants used with it.\<close>


text \<open>The general continuous Cauchy-Binet (Andreief) identity:
  @{text "det[\<integral> \<phi>_i \<psi>_j dmu] =
    (1/n!) \<integral> det[\<phi>_a(x_b)] det[\<psi>_a(x_b)] dmu^{\<otimes>n}"}.  Proof: Leibniz
    expansion,
  symmetrisation over permutations, Fubini on @{text "PiM"}.\<close>
theorem andreief:
  fixes \<mu> :: "real measure" and \<phi> \<psi> :: "nat \<Rightarrow> real \<Rightarrow> real" and
    n :: nat
  assumes sf: "sigma_finite_measure \<mu>"
    and integ: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
      integrable \<mu> (\<lambda>x. \<phi> i x * \<psi> j x)"
  shows "Determinant.det (Matrix.mat n n (\<lambda>(i,
    j). integral\<^sup>L \<mu> (\<lambda>x. \<phi> i x * \<psi> j x))) =
         1 / fact n * integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>))
           (\<lambda>x. Determinant.det (Matrix.mat n n (\<lambda>(a, b). \<phi> a (x b))) *
                Determinant.det (Matrix.mat n n (\<lambda>(a, b). \<psi> a (x b))))"
proof -
  define G :: "nat \<Rightarrow> nat \<Rightarrow> real" where "G =
    (\<lambda>i j. integral\<^sup>L \<mu> (\<lambda>x. \<phi> i x * \<psi> j x))"
  define P :: "(nat \<Rightarrow> nat) set" where "P = {p. p permutes {0..<n}}"
  interpret product_sigma_finite "\<lambda>_::nat. \<mu>"
    by (rule product_sigma_finite.intro) (rule sf)
  have cardP: "card P = fact n"
    unfolding P_def by (simp add: card_permutations)
  have inP: "\<And>\<sigma> a. \<sigma> \<in> P \<Longrightarrow> a < n \<Longrightarrow>
    \<sigma> a < n"
    by (simp add: P_def permutes_in_image)
  have permP: "\<And>\<sigma>. \<sigma> \<in> P \<Longrightarrow> \<sigma> permutes {..<n}"
    by (simp add: P_def atLeast0LessThan)
  have permutationP: "\<And>\<sigma>. \<sigma> \<in> P \<Longrightarrow> permutation \<sigma>"
    by (auto simp: P_def permutes_imp_permutation intro: permutes_imp_permutation)

  text \<open>Leibniz formula in column form:
    @{text "det (f a b)_{a,b} = \<Sum>_\<sigma> sgn \<sigma> \<Prod>_a f (\<sigma> a) a"}.\<close>
  have colform: "Determinant.det (Matrix.mat n n (\<lambda>(a, b). f a b)) = (\<Sum> \<sigma> \<in>
    P. signof \<sigma> * (\<Prod> a < n. f (\<sigma> a) a))"
    for f :: "nat \<Rightarrow> nat \<Rightarrow> real"
  proof -
    have "Determinant.det (Matrix.mat n n (\<lambda>(a, b). f a b)) =
      Determinant.det (transpose_mat (Matrix.mat n n (\<lambda>(a, b). f a b)))"
      by (simp add: Determinant.det_transpose[OF mat_carrier])
    also have "\<dots> = (\<Sum> \<sigma> \<in> P. signof \<sigma> * (\<Prod> a =
      0..<n. transpose_mat (Matrix.mat n n (\<lambda>(a, b). f a b)) $$ (a, \<sigma> a)))"
      by (simp add: det_def'[of _ n] P_def)
    also have "\<dots> = (\<Sum> \<sigma> \<in> P. signof \<sigma> * (\<Prod> a <
      n. f (\<sigma> a) a))"
      by (simp add: inP atLeast0LessThan)
    finally show ?thesis .
  qed
  have detA: "\<And>x. Determinant.det (Matrix.mat n n (\<lambda>(a, b). \<phi> a (x b))) =
    (\<Sum> \<sigma> \<in> P. signof \<sigma> * (\<Prod> a < n. \<phi> (\<sigma> a) (x a)))"
    by (simp add: colform)
  have detB: "\<And>x. Determinant.det (Matrix.mat n n (\<lambda>(a, b). \<psi> a (x b))) =
    (\<Sum> \<tau> \<in> P. signof \<tau> * (\<Prod> a < n. \<psi> (\<tau> a) (x a)))"
    by (simp add: colform)
  have leib: "\<And>x. Determinant.det (Matrix.mat n n (\<lambda>(a,
    b). \<phi> a (x b))) * Determinant.det (Matrix.mat n n (\<lambda>(a, b). \<psi> a (x b)))
      = (\<Sum> \<sigma> \<in> P. \<Sum> \<tau> \<in>
        P. signof \<sigma> * signof \<tau> * (\<Prod> a <
        n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a)))"
    unfolding detA detB sum_product prod.distrib by (simp add: mult_ac)

  text \<open>Integrate each term with Fubini on the finite product.\<close>
  have integ_a: "\<And>\<sigma> \<tau> a. \<sigma> \<in> P \<Longrightarrow>
    \<tau> \<in> P \<Longrightarrow> a < n \<Longrightarrow>
    integrable \<mu> (\<lambda>x. \<phi> (\<sigma> a) x * \<psi> (\<tau> a) x)"
    using integ inP by simp
  have intg: "\<And>\<sigma> \<tau>. \<sigma> \<in> P \<Longrightarrow>
    \<tau> \<in> P \<Longrightarrow> integrable (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x.
    \<Prod> a < n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a))"
  proof -
    fix \<sigma> \<tau> assume s: "\<sigma> \<in> P" and t: "\<tau> \<in> P"
    show "integrable (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. \<Prod> a <
      n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a))"
      using product_integrable_prod[of "{..<n}" "\<lambda>a x. \<phi> (\<sigma> a) x *
        \<psi> (\<tau> a) x"] integ_a[OF s t] by simp
  qed
  have int: "\<And>\<sigma> \<tau>. \<sigma> \<in> P \<Longrightarrow>
    \<tau> \<in> P \<Longrightarrow>
      integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. \<Prod> a <
        n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a)) = (\<Prod> a <
        n. G (\<sigma> a) (\<tau> a))"
  proof -
    fix \<sigma> \<tau> assume s: "\<sigma> \<in> P" and t: "\<tau> \<in> P"
    show "integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. \<Prod> a <
      n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a)) = (\<Prod> a <
      n. G (\<sigma> a) (\<tau> a))"
      using product_integral_prod[of "{..<n}" "\<lambda>a x. \<phi> (\<sigma> a) x *
        \<psi> (\<tau> a) x"] integ_a[OF s t] by (simp add: G_def)
  qed
  have E: "integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. Determinant.det
    (Matrix.mat n n (\<lambda>(a, b). \<phi> a (x b))) *
    Determinant.det (Matrix.mat n n (\<lambda>(a, b). \<psi> a (x b))))
      = (\<Sum> \<sigma> \<in> P. \<Sum> \<tau> \<in>
        P. signof \<sigma> * signof \<tau> * (\<Prod> a < n. G (\<sigma> a) (\<tau> a)))"
  proof -
    have i1: "\<And>\<sigma> \<tau>. \<sigma> \<in> P \<Longrightarrow>
      \<tau> \<in> P \<Longrightarrow> integrable (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x.
      signof \<sigma> * signof \<tau> * (\<Prod> a <
      n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a)))"
      using intg by simp
    have i2: "\<And>\<sigma>. \<sigma> \<in> P \<Longrightarrow>
      integrable (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. \<Sum> \<tau> \<in>
      P. signof \<sigma> * signof \<tau> * (\<Prod> a <
      n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a)))"
      using i1 by (auto intro: Bochner_Integration.integrable_sum)
    have "integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. Determinant.det (Matrix.mat
      n n (\<lambda>(a, b). \<phi> a (x b))) * Determinant.det (Matrix.mat n n (\<lambda>(a,
      b). \<psi> a (x b))))
        = integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. \<Sum> \<sigma> \<in>
          P. \<Sum> \<tau> \<in> P. signof \<sigma> * signof \<tau> * (\<Prod> a <
          n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a)))"
      by (simp add: leib)
    also have "\<dots> = (\<Sum> \<sigma> \<in> P. \<Sum> \<tau> \<in>
      P. integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. signof \<sigma> *
      signof \<tau> * (\<Prod> a < n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a))))"
    proof -
      have "integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. \<Sum> \<sigma> \<in>
        P. \<Sum> \<tau> \<in> P. signof \<sigma> * signof \<tau> * (\<Prod> a <
        n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a)))
          = (\<Sum> \<sigma> \<in> P. integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x.
            \<Sum> \<tau> \<in> P. signof \<sigma> * signof \<tau> * (\<Prod> a <
            n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a))))"
        using i2 by (auto intro: Bochner_Integration.integral_sum)
      also have "\<dots> = (\<Sum> \<sigma> \<in> P. \<Sum> \<tau> \<in>
        P. integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. signof \<sigma> *
        signof \<tau> * (\<Prod> a < n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a))))"
        using i1 by (simp add: Bochner_Integration.integral_sum)
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum> \<sigma> \<in> P. \<Sum> \<tau> \<in>
      P. signof \<sigma> * signof \<tau> * (\<Prod> a < n. G (\<sigma> a) (\<tau> a)))"
    proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
      fix \<sigma> \<tau> assume s: "\<sigma> \<in> P" and t: "\<tau> \<in> P"
      show "integral\<^sup>L (PiM {..<n} (\<lambda>_. \<mu>)) (\<lambda>x. signof \<sigma> *
        signof \<tau> * (\<Prod> a < n. \<phi> (\<sigma> a) (x a) * \<psi> (\<tau> a) (x a))) =
        signof \<sigma> * signof \<tau> * (\<Prod> a < n. G (\<sigma> a) (\<tau> a))"
        using int[OF s t] by simp
    qed
    finally show ?thesis .
  qed

  text \<open>For fixed @{text \<tau>}, substitute
    @{text "\<rho> = \<sigma> \<circ> Hilbert_Choice.inv \<tau>"}: the inner sum is
    @{text "det G"}.\<close>
  have reidx: "\<And>\<sigma> \<tau>. \<sigma> \<in> P \<Longrightarrow>
    \<tau> \<in> P \<Longrightarrow> (\<Prod> a < n. G (\<sigma> a) (\<tau> a)) = (\<Prod> b <
    n. G ((\<sigma> \<circ> Hilbert_Choice.inv \<tau>) b) b)"
  proof -
    fix \<sigma> \<tau> assume s: "\<sigma> \<in> P" and t: "\<tau> \<in> P"
    show "(\<Prod> a < n. G (\<sigma> a) (\<tau> a)) = (\<Prod> b <
      n. G ((\<sigma> \<circ> Hilbert_Choice.inv \<tau>) b) b)"
      using prod.permute[OF permP[OF t],
        of "\<lambda>b. G ((\<sigma> \<circ> Hilbert_Choice.inv \<tau>) b) b"] permutes_inverses[OF
        permP[OF t]] by (simp add: o_def)
  qed
  have signmul: "\<And>\<sigma> \<tau>. \<sigma> \<in> P \<Longrightarrow>
    \<tau> \<in> P \<Longrightarrow> (signof \<sigma> :: real) * signof \<tau> =
    signof (\<sigma> \<circ> Hilbert_Choice.inv \<tau>)"
  proof -
    fix \<sigma> \<tau> assume s: "\<sigma> \<in> P" and t: "\<tau> \<in> P"
    show "(signof \<sigma> :: real) * signof \<tau> =
      signof (\<sigma> \<circ> Hilbert_Choice.inv \<tau>)"
      using sign_compose[OF permutationP[OF s] permutation_inverse[OF permutationP[OF t]]]
        sign_inverse[OF permutationP[OF t]] by simp
  qed
  have bij: "\<And>\<tau>. \<tau> \<in> P \<Longrightarrow>
    bij_betw (\<lambda>\<sigma>. \<sigma> \<circ> Hilbert_Choice.inv \<tau>) P P"
  proof -
    fix \<tau> assume t: "\<tau> \<in> P"
    have tp: "\<tau> permutes {0..<n}" using t by (simp add: P_def)
    have h1: "(\<lambda>\<sigma>. \<sigma> \<circ> Hilbert_Choice.inv \<tau>) \<in>
      P \<rightarrow> P"
      using permutes_compose[OF permutes_inv[OF tp]] by (simp add: P_def)
    have h2: "(\<lambda>\<rho>. \<rho> \<circ> \<tau>) \<in> P \<rightarrow> P"
      using permutes_compose[OF tp] by (simp add: P_def)
    have h3: "\<And>\<sigma>. \<sigma> \<in> P \<Longrightarrow>
      \<sigma> \<circ> Hilbert_Choice.inv \<tau> \<circ> \<tau> = \<sigma>"
      by (simp add: o_assoc[symmetric] permutes_inv_o[OF tp])
    have h4: "\<And>\<rho>. \<rho> \<in> P \<Longrightarrow>
      \<rho> \<circ> \<tau> \<circ> Hilbert_Choice.inv \<tau> = \<rho>"
      by (simp add: o_assoc[symmetric] permutes_inv_o[OF tp])
    show "bij_betw (\<lambda>\<sigma>. \<sigma> \<circ> Hilbert_Choice.inv \<tau>) P P"
      using bij_betwI[OF h1 h2] h3 h4 by simp
  qed
  have inner: "\<And>\<tau>. \<tau> \<in> P \<Longrightarrow>
    (\<Sum> \<sigma> \<in> P. signof \<sigma> * signof \<tau> * (\<Prod> a <
    n. G (\<sigma> a) (\<tau> a))) = Determinant.det (Matrix.mat n n (\<lambda>(i, j). G i j))"
  proof -
    fix \<tau> assume t: "\<tau> \<in> P"
    have "(\<Sum> \<sigma> \<in> P. signof \<sigma> * signof \<tau> * (\<Prod> a <
      n. G (\<sigma> a) (\<tau> a))) = (\<Sum> \<sigma> \<in>
      P. signof (\<sigma> \<circ> Hilbert_Choice.inv \<tau>) * (\<Prod> b <
      n. G ((\<sigma> \<circ> Hilbert_Choice.inv \<tau>) b) b))"
      by (simp add: reidx[OF _ t] signmul[OF _ t])
    also have "\<dots> = (\<Sum> \<rho> \<in> P. signof \<rho> * (\<Prod> b < n. G (\<rho> b) b))"
      using sum.reindex_bij_betw[OF bij[OF t], of "\<lambda>\<rho>. signof \<rho> * (\<Prod> b <
        n. G (\<rho> b) b)"] by simp
    also have "\<dots> = Determinant.det (Matrix.mat n n (\<lambda>(i, j). G i j))"
      using colform[of G] by simp
    finally show "(\<Sum> \<sigma> \<in> P. signof \<sigma> * signof \<tau> * (\<Prod> a <
      n. G (\<sigma> a) (\<tau> a))) = Determinant.det (Matrix.mat n n (\<lambda>(i, j). G i j))" .
  qed
  have comb: "(\<Sum> \<sigma> \<in> P. \<Sum> \<tau> \<in>
    P. signof \<sigma> * signof \<tau> * (\<Prod> a < n. G (\<sigma> a) (\<tau> a))) =
    fact n * Determinant.det (Matrix.mat n n (\<lambda>(i, j). G i j))"
  proof -
    have "(\<Sum> \<sigma> \<in> P. \<Sum> \<tau> \<in>
      P. signof \<sigma> * signof \<tau> * (\<Prod> a < n. G (\<sigma> a) (\<tau> a))) =
      (\<Sum> \<tau> \<in> P. \<Sum> \<sigma> \<in>
      P. signof \<sigma> * signof \<tau> * (\<Prod> a < n. G (\<sigma> a) (\<tau> a)))"
      using sum.swap by fast
    also have "\<dots> = (\<Sum> \<tau> \<in>
      P. Determinant.det (Matrix.mat n n (\<lambda>(i, j). G i j)))"
      by (simp add: inner)
    also have "\<dots> = fact n * Determinant.det (Matrix.mat n n (\<lambda>(i, j). G i j))"
      by (simp add: cardP)
    finally show ?thesis .
  qed
  have fn: "(fact n :: real) \<noteq> 0" by simp
  show ?thesis
    unfolding G_def [symmetric] E comb using fn by simp
qed

text \<open>(6.10): @{text "\<Delta>_K(\<zeta>(5)) =
  (1/h!) \<integral>_{(0,\<infinity>)^h} \<Prod>_{i<j}(y_i^2 -
  y_j^2)^2 \<Prod>_i D_N(y_i^2)^6/D_K(y_i^2) w(y_i) dy"}.\<close>
lemma andreief_det_swap:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: comm_ring_1"
  shows "Determinant.det (Matrix.mat n n (\<lambda>(a, b). f b a)) =
    Determinant.det (Matrix.mat n n (\<lambda>(a, b). f a b))"
proof -
  have "Matrix.mat n n (\<lambda>(a, b). f b a) =
    transpose_mat (Matrix.mat n n (\<lambda>(a, b). f a b))"
    by (auto intro: eq_matI)
  thus ?thesis
    using Determinant.det_transpose[OF mat_carrier] by auto
qed

lemma andreief_det_scale_cols:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: comm_ring_1" and c :: "nat \<Rightarrow> 'a"
  shows "Determinant.det (Matrix.mat n n (\<lambda>(a, b). f a b * c b)) = (\<Prod> b <
    n. c b) * Determinant.det (Matrix.mat n n (\<lambda>(a, b). f a b))"
proof -
  have inP: "\<And>p j. p permutes {0..<n} \<Longrightarrow> j < n \<Longrightarrow> p j < n"
    by (simp add: permutes_in_image)
  have d1: "Determinant.det (Matrix.mat n n (\<lambda>(a, b). f a b * c b)) =
    (\<Sum> p | p permutes {0..<n}. signof p * (\<Prod> j < n. f (p j) j * c j))"
    by (simp add: det_col[OF mat_carrier] inP)
  have d2: "Determinant.det (Matrix.mat n n (\<lambda>(a, b). f a b)) =
    (\<Sum> p | p permutes {0..<n}. signof p * (\<Prod> j < n. f (p j) j))"
    by (simp add: det_col[OF mat_carrier] inP)
  show ?thesis
    unfolding d1 d2 prod.distrib sum_distrib_left
    by (simp add: mult_ac)
qed
end
