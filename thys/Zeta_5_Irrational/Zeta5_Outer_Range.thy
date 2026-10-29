(*  Title:   Zeta5_Outer_Range.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Outer_Range
  imports Zeta5_Inner_Range "BenOr_Kozen_Reif.More_Matrix"
begin

section \<open>The outer range: Lemma 4.2 and Proposition 4.3\<close>

text \<open>Section 4.2 of the paper: the decomposition (4.10), the outer basis (4.11) and its
  unimodularity, the arithmetic of the pole classes, the entry bound (4.12), the closed form (4.14)
  of \<open>\<gamma>\<^sub>p\<^sup>o\<^sup>u\<^sup>t\<close>,
    Lemma 4.2 (@{text det_vpGge_of_weighted_entries}) and Proposition 4.3
    (@{text DeltaK_vpGge_outer},
  @{text DeltaK_vpGge_large_prime}).  Lean theories @{text MuMod}, @{text CRTBasis},
    @{text OuterCount},
  @{text OuterEntries}, @{text Lemma42}, @{text Prop43}, @{text Prop43Large}.\<close>

subsection \<open>Section 4.2 The outer range\<close>

text \<open>(4.9) holds when @{text "K \<ge> 200M^2"} and @{text "K/3 < p \<le> K"}.\<close>
lemma outer_hyp_of_range:
  assumes "40 \<le> M" "40 dvd K" "200 * M ^ 2 \<le> K" "prime p" "K < 3 * p" "p \<le> K"
  shows "OuterHyp K p"
proof -
  have "200 * 40 ^ 2 \<le> 200 * M ^ 2" using assms(1) by (intro mult_le_mono2 power_mono) simp_all
  hence K: "320000 \<le> K" using assms(3) by simp
  have N: "40 * Nof K \<le> 3 * K" by (simp add: Nof_def)
  have p: "106666 < p" using K assms(5) by simp
  have "2 * K < 3 * p * 2" using assms(5) by simp
  also have "\<dots> \<le> p * p" using p by (auto intro: mult_le_mono)
  finally have "2 * K < p ^ 2" by (simp add: power2_eq_square)
  show ?thesis unfolding OuterHyp_def
  proof (intro conjI)
    show "7 \<le> p" using p by simp
    show "p \<le> K" by fact
    show "K < 3 * p" by fact
    show "2 * K < p ^ 2" by fact
    show "2 * Nof K < p" using N assms(5) by linarith
    show "5 * Nof K \<le> 2 * p - 2" using N assms(5) p by linarith
  qed
qed

text \<open>(4.10): @{text "G_K = A + p^-^1L"} with @{text L} constant, integral,
  of rank @{text "\<le> r_p"}
  (rank over @{text \<rat>}, @{text "vec_space.rank"} of Jordan\_Normal\_Form).\<close>
lemma cCorr_vge: "prime p \<Longrightarrow> vge p (cCorr p e) 0"
  by (auto simp: cCorr_def vge_zero vge_of_int)

lemma cCorr_of_lt: "e < 2 * p - 3 \<Longrightarrow> cCorr p e = 0"
  by (simp add: cCorr_def)

text \<open>@{text "mu_X = mu^0_X + p^-1 \<Sum>_e q_e c_e"}: the two functionals differ
  by the correction of the polynomial part.\<close>
lemma muX_eq_muXmod_add:
  "prime p \<Longrightarrow> muX S P = muXmod p S P +
     [:(\<Sum> e \<le> degree (P div sqPoleProd S). Polynomial.coeff (P div sqPoleProd S) e *
       cCorr p e) / of_nat p:]"
proof -
  assume "prime p"
  define Q where "Q = P div sqPoleProd S"
  define Sg where "Sg = (\<Sum> j \<in> S. [:sqResidue S P j:] * muPole j)"
  define X where "X = (\<Sum> e \<le> degree Q. Polynomial.coeff Q e * (muMono e - cCorr p e /
    of_nat p))"
  define Y where "Y = (\<Sum> e \<le> degree Q. Polynomial.coeff Q e * cCorr p e) / of_nat p"
  have e: "muPoly Q = X + Y"
    by (simp add: muPoly_def X_def Y_def right_diff_distrib sum_subtractf sum_divide_distrib)
  have "muX S P = [:X + Y:] + Sg" by (simp only: muX_def Q_def[symmetric] Sg_def[symmetric] e)
  also have "\<dots> = ([:X:] + Sg) + [:Y:]" by (simp add: add_ac)
  also have "[:X:] + Sg = muXmod p S P" by (simp add: muXmod_def Q_def Sg_def X_def)
  finally show ?thesis by (simp add: Y_def Q_def)
qed

lemma pX_plus_const_pCons: "pX + [:c:] = [:c, 1:]"
  by (simp add: monom_Suc)

lemma vpGge_mul0': "prime p \<Longrightarrow> vpGge p A 0 \<Longrightarrow>
  vpGge p B 0 \<Longrightarrow> vpGge p (A * B) 0"
  using vpGge_mul[of p A 0 B 0] by simp

lemma vpGge_pow0': "prime p \<Longrightarrow> vpGge p A 0 \<Longrightarrow> vpGge p (A ^ n) 0"
  by (induction n) (auto simp: vpGge_one vpGge_mul0')

lemma vpGge_pX_plus_sq0: "prime p \<Longrightarrow> vpGge p (pX + [:of_nat n ^ 2:]) 0"
proof -
  assume p: "prime p"
  show ?thesis by (rule vpGge_add[OF p vpGge_pX vpGge_C[OF vge_pow[OF p vge_of_nat[OF p]]]])
qed

lemma lead_coeff_sqPoleProd0: "lead_coeff (sqPoleProd S) = 1"
  unfolding sqPoleProd_def lead_coeff_prod pX_plus_const_pCons by simp

lemma vpGge_sqPoleProd0: "prime p \<Longrightarrow> vpGge p (sqPoleProd S) 0"
proof -
  assume p: "prime p"
  show ?thesis
  proof (cases "finite S")
    case True
    have "vpGge p (\<Prod> j \<in> S. pX + [:of_nat j ^ 2:]) (\<Sum> j \<in> S. 0)"
      by (rule vpGge_prod[OF p True]) (rule vpGge_pX_plus_sq0[OF p])
    thus ?thesis by (simp add: sqPoleProd_def)
  next
    case False
    thus ?thesis by (simp add: sqPoleProd_def vpGge_one)
  qed
qed

lemma vpGge_Dm0: "prime p \<Longrightarrow> vpGge p (Dm m) 0"
proof -
  assume p: "prime p"
  have "Dm m = sqPoleProd {1..m}" by (simp add: Dm_def sqPoleProd_def)
  thus ?thesis using vpGge_sqPoleProd0[OF p] by simp
qed
lemma degree_div_sub:
  fixes P Q :: "rat poly"
  assumes "Q \<noteq> 0"
  shows "degree (P div Q) \<le> degree P - degree Q"
proof (cases "P div Q = 0")
  case True
  thus ?thesis by simp
next
  case False
  have dm: "degree (Q * (P div Q)) = degree Q + degree (P div Q)" using assms False
    by (rule degree_mult_eq)
  have "P mod Q = 0 \<or> degree (P mod Q) < degree (Q * (P div Q))"
    using degree_mod_less[OF assms, of P] dm by auto
  hence "degree (Q * (P div Q) + P mod Q) = degree (Q * (P div Q))"
  proof
    assume "P mod Q = 0"
    thus ?thesis by (simp only: add_0_right)
  next
    assume "degree (P mod Q) < degree (Q * (P div Q))"
    thus ?thesis by (rule degree_add_eq_left)
  qed
  hence "degree P = degree Q + degree (P div Q)" using dm by simp
  thus ?thesis by simp
qed

lemma blocks_lex:
  fixes f :: "nat \<Rightarrow> nat"
  defines "B n \<equiv> concat (map (\<lambda>a. map (\<lambda>i. (a, i)) [0..<f a]) [0..<n])"
  shows "y < x \<Longrightarrow> x < length (B n) \<Longrightarrow>
         fst (B n ! y) < fst (B n ! x) \<or> (fst (B n ! y) = fst (B n ! x) \<and>
           snd (B n ! y) < snd (B n ! x))"
proof (induction n arbitrary: x y)
  case 0
  thus ?case by (simp add: B_def)
next
  case (Suc n)
  define C where "C = map (\<lambda>i. (n, i)) [0..<f n]"
  have BS: "B (Suc n) = B n @ C" by (simp add: B_def C_def)
  have mem: "fst z < n" if "z \<in> set (B n)" for z using that by (auto simp: B_def)
  have Cn: "C ! k = (n, k)" if "k < length C" for k using that by (simp add: C_def)
  show ?case
  proof (cases "x < length (B n)")
    case True
    thus ?thesis using Suc.IH[OF Suc.prems(1) True] Suc.prems(1) by (simp add: BS nth_append)
  next
    case False
    have xC: "x - length (B n) < length C" using Suc.prems(2) False by (simp add: BS)
    show ?thesis
    proof (cases "y < length (B n)")
      case True
      have "fst (B n ! y) < n" using mem[OF nth_mem[OF True]] .
      thus ?thesis using True False xC by (simp add: BS nth_append Cn)
    next
      case False2: False
      have "y - length (B n) < x - length (B n)" using Suc.prems(1) False2 by simp
      thus ?thesis using False False2 xC Suc.prems by (simp add: BS nth_append Cn)
    qed
  qed
qed
text \<open>The polynomial quotients @{text "Q_{ij} = D_N^6 t^{i+j} div D_K"} are integral.\<close>
lemma vpGge_quot: "prime p \<Longrightarrow>
  vpGge p ((Dm (Nof K) ^ 6 * pX ^ n) div sqPoleProd {1..K}) 0"
proof -
  assume p: "prime p"
  have num: "vpGge p (Dm (Nof K) ^ 6 * pX ^ n) 0"
    by (rule vpGge_mul0'[OF p vpGge_pow0'[OF p vpGge_Dm0[OF p]] vpGge_pow0'[OF p vpGge_pX]])
  show ?thesis by (rule vpGge_div_monic[OF p num lead_coeff_sqPoleProd0 vpGge_sqPoleProd0[OF p]])
qed

text \<open>A matrix whose rows outside a set of @{text k} indices vanish has rank
  @{text "\<le> k"}.\<close>
lemma rank_le_card_nonzero_rows:
  assumes "L \<in> carrier_mat n n" "T \<subseteq> {0..<n}" "\<And>i j. i < n \<Longrightarrow>
    i \<notin> T \<Longrightarrow> j < n \<Longrightarrow> L $$ (i, j) = 0"
  shows "vec_space.rank n L \<le> card T"
proof -
  have finT: "finite T" using finite_subset[OF assms(2)] by blast
  define xs where "xs = sorted_list_of_set T"
  define k where "k = card T"
  have dxs: "distinct xs" unfolding xs_def by auto
  have sxs: "set xs = T" unfolding xs_def using finT by force
  have lxs: "length xs = k" unfolding xs_def k_def using finT by force
  define E :: "'a mat" where "E = Matrix.mat n k (\<lambda>(i, t). if xs ! t = i then 1 else 0)"
  define G where "G = Matrix.mat k n (\<lambda>(t, j). L $$ (xs ! t, j))"
  have Ec: "E \<in> carrier_mat n k" unfolding E_def by force
  have Gc: "G \<in> carrier_mat k n" unfolding G_def by simp
  have EG: "E * G = L"
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row L" and j: "j < dim_col L"
    have i': "i < n" and j': "j < n" using i j assms(1) by auto
    have e: "(E * G) $$ (i, j) = (\<Sum> t = 0..<k. (if xs ! t =
      i then 1 else 0) * L $$ (xs ! t, j))"
      using i' j' Ec Gc unfolding E_def G_def by (auto simp: scalar_prod_def index_mult_mat)
    show "(E * G) $$ (i, j) = L $$ (i, j)"
    proof (cases "i \<in> T")
      case True
      then obtain t0 where t0: "t0 < k" "xs ! t0 = i" using sxs lxs by (meson in_set_conv_nth)
      have u: "xs ! t = i \<longleftrightarrow> t = t0" if "t < k" for t
        using that t0(1) t0(2)[symmetric] dxs lxs by (auto simp: nth_eq_iff_index_eq)
      have "(\<Sum> t = 0..<k. (if xs ! t = i then 1 else 0) * L $$ (xs ! t, j)) = (\<Sum> t =
        0..<k. if t = t0 then L $$ (i, j) else 0)"
      proof (rule sum.cong[OF refl])
        fix t assume t: "t \<in> {0..<k}"
        show "(if xs ! t = i then 1 else 0) * L $$ (xs ! t, j) = (if t =
          t0 then L $$ (i, j) else 0)"
          using u[of t] t t0 by auto
      qed
      also have "\<dots> = L $$ (i, j)" using t0 by fastforce
      finally show ?thesis using e by argo
    next
      case False
      have "xs ! t \<noteq> i" if "t < k" for t using that False sxs lxs by force
      hence "(\<Sum> t = 0..<k. (if xs ! t = i then 1 else 0) * L $$ (xs ! t, j)) = 0" by force
      thus ?thesis using e assms(3)[OF i' False j'] by argo
    qed
  next
    show "dim_row (E * G) = dim_row L" using Ec Gc assms(1) by fastforce
    show "dim_col (E * G) = dim_col L" using Ec Gc assms(1) by fastforce
  qed
  have "vec_space.rank n L = vec_space.rank n (E * G)" using EG by meson
  also have "\<dots> \<le> vec_space.rank n E" by (rule vec_space.rank_mat_mul_right[OF Ec Gc])
  also have "\<dots> \<le> k" by (rule vec_space.rank_le_nc[OF Ec])
  finally show ?thesis unfolding k_def .
qed

text \<open>(4.10): @{text "G_K = A + p^-^1L"} with @{text L} constant, integral,
  of rank @{text "\<le> r_p"}
  (rank over @{text \<rat>}, @{text "vec_space.rank"} of Jordan\_Normal\_Form).\<close>
theorem GK_outer_decomposition:
  assumes p: "prime p" and K: "40 dvd K" and H: "OuterHyp K p"
  shows "\<exists>L :: rat mat. L \<in> carrier_mat (hof K) (hof K) \<and>
           GK K = Aout K p + map_mat (\<lambda>c. [:c / of_nat p:]) L \<and>
           (\<forall>i<hof K. \<forall>j<hof K. L $$ (i, j) \<noteq> 0 \<longrightarrow>
             0 \<le> vp p (L $$ (i, j))) \<and>
           vec_space.rank (hof K) L \<le> rOut K p"
proof -
  define h where "h = hof K"
  define Q where "Q = (\<lambda>i j. (Dm (Nof K) ^ 6 * pX ^ (i + j)) div sqPoleProd {1..K})"
  define L where "L = Matrix.mat h h (\<lambda>(i, j). \<Sum> e \<le>
    degree (Q i j). Polynomial.coeff (Q i j) e * cCorr p e)"
  obtain n where Kn: "K = 40 * n" using K by (elim dvdE)
  have hN: "Nof K = 3 * n" and hh: "h = 37 * n" by (simp_all add: Kn Nof_def hof_def h_def)
  have Lc: "L \<in> carrier_mat h h" by (simp add: L_def)
  have GL: "GK K = Aout K p + map_mat (\<lambda>c. [:c / of_nat p:]) L"
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row (Aout K p + map_mat (\<lambda>c. [:c / of_nat p:]) L)"
      and j: "j < dim_col (Aout K p + map_mat (\<lambda>c. [:c / of_nat p:]) L)"
    show "GK K $$ (i, j) = (Aout K p + map_mat (\<lambda>c. [:c / of_nat p:]) L) $$ (i, j)"
      using i j by (simp add: GK_def Aout_def L_def Q_def h_def muX_eq_muXmod_add[OF p])
  qed (simp_all add: GK_def Aout_def L_def h_def)
  have Lint: "\<And>i j. i < h \<Longrightarrow> j < h \<Longrightarrow>
    L $$ (i, j) \<noteq> 0 \<Longrightarrow> 0 \<le> vp p (L $$ (i, j))"
  proof -
    fix i j assume i: "i < h" and j: "j < h" and nz: "L $$ (i, j) \<noteq> 0"
    have Qi: "vpGge p (Q i j) 0" unfolding Q_def by (rule vpGge_quot[OF p])
    have "vge p (\<Sum> e \<le> degree (Q i j). Polynomial.coeff (Q i j) e * cCorr p e) 0"
    proof (rule vge_sum[OF p])
      fix e
      show "vge p (Polynomial.coeff (Q i j) e * cCorr p e) 0"
        using vge_mul[OF p Qi[unfolded vpGge_iff, rule_format] cCorr_vge[OF p]] by simp
    qed simp
    hence "vge p (L $$ (i, j)) 0" using i j by (simp add: L_def)
    thus "0 \<le> vp p (L $$ (i, j))" using nz by (simp add: vge_def)
  qed
  define m0 where "m0 = 2 * p - 2 - 5 * (3 * n)"
  have zero_rows: "\<And>i j. i < h \<Longrightarrow> i < m0 \<Longrightarrow>
    j < h \<Longrightarrow> L $$ (i, j) = 0"
  proof -
    fix i j assume i: "i < h" and im: "i < m0" and j: "j < h"
    have p7: "7 \<le> p" and N5: "5 * Nof K \<le> 2 * p - 2" using H by (simp_all add: OuterHyp_def)
    have dS: "degree (sqPoleProd {1..K}) = K"
    proof -
      have "sqPoleProd {1..K} = Dm K" by (simp add: Dm_def sqPoleProd_def)
      thus ?thesis by (simp add: degree_Dm)
    qed
    have dN: "degree (Dm (Nof K) ^ 6 * pX ^ (i + j)) \<le> 6 * Nof K + (i + j)"
    proof -
      have "degree (Dm (Nof K) ^ 6 * pX ^ (i + j)) \<le>
        degree (Dm (Nof K) ^ 6) + degree (pX ^ (i + j))" by (rule degree_mult_le)
      also have "degree (Dm (Nof K) ^ 6) \<le> degree (Dm (Nof K)) * 6" by (rule degree_power_le)
      also have "degree ((pX :: rat poly) ^ (i + j)) \<le> degree (pX :: rat poly) * (i + j)"
        by (rule degree_power_le)
      finally show ?thesis by (simp add: degree_Dm degree_monom_eq)
    qed
    have dq: "degree (Q i j) \<le> degree (Dm (Nof K) ^ 6 * pX ^ (i + j)) -
      degree (sqPoleProd {1..K})"
      unfolding Q_def by (rule degree_div_sub[OF sqPoleProd_nonzero]) simp
    have "degree (Q i j) < 2 * p - 3" using dq dN dS im j hN hh Kn p7 N5 by (simp add: m0_def h_def)
    hence z: "\<And>e. e \<in> {..degree (Q i j)} \<Longrightarrow>
      Polynomial.coeff (Q i j) e * cCorr p e = 0"
      by (auto simp: cCorr_of_lt)
    have "L $$ (i, j) = (\<Sum> e \<le> degree (Q i j). Polynomial.coeff (Q i j) e * cCorr p e)"
      using i j by (simp add: L_def)
    also have "\<dots> = 0" by (rule sum.neutral) (use z in blast)
    finally show "L $$ (i, j) = 0" .
  qed
  have rank: "vec_space.rank h L \<le> rOut K p"
  proof -
    have N5: "5 * Nof K \<le> 2 * p - 2" and p7: "7 \<le> p" using H by (simp_all add: OuterHyp_def)
    have "vec_space.rank h L \<le> card {m0..<h}"
      by (rule rank_le_card_nonzero_rows[OF Lc]) (auto intro: zero_rows)
    also have "card {m0..<h} \<le> rOut K p" using N5 p7 hN hh Kn by (simp add: rOut_def m0_def)
    finally show ?thesis .
  qed
  show ?thesis unfolding h_def[symmetric] using Lc GL Lint rank by blast
qed

lemma mod_add_eq_0_iff:
  fixes j a p :: nat
  assumes "0 < a" "a < p"
  shows "(j + a) mod p = 0 \<longleftrightarrow> j mod p = p - a"
proof -
  from assms have "0 < p" by simp
  hence r: "j mod p < p" by simp
  have "(j + a) mod p = (j mod p + a) mod p" by (simp add: mod_add_left_eq)
  also have "\<dots> = 0 \<longleftrightarrow> j mod p + a = p"
  proof
    assume h: "(j mod p + a) mod p = 0"
    have "j mod p + a < 2 * p" using r assms by linarith
    moreover have "p dvd j mod p + a" using h by (simp add: mod_eq_0_iff_dvd)
    then obtain t where t: "j mod p + a = p * t" by (elim dvdE)
    ultimately have "t < 2" by simp
    moreover have "t \<noteq> 0"
    proof
      assume "t = 0"
      hence "j mod p + a = 0" using t by simp
      thus False using assms by simp
    qed
    ultimately show "j mod p + a = p" using t by (cases t) auto
  qed simp
  finally show ?thesis using assms by linarith
qed

lemma sum_classes_card:
  assumes "prime p" "2 < p" "finite X"
  shows "(\<Sum> a \<le> mHalf p. card {j \<in> X. j mod p = a mod p \<or>
    (j + a) mod p = 0}) = card X"
proof -
  define m where "m = mHalf p"
  have p0: "0 < p" using assms by simp
  from assms have "odd p" by (metis prime_odd_nat)
  hence m2: "2 * m = p - 1" unfolding m_def mHalf_def by (auto elim!: oddE)
  define C where "C a = {j \<in> X. j mod p = a \<or> j mod p = p - a}" for a
  have Ceq: "{j \<in> X. j mod p = a mod p \<or> (j + a) mod p = 0} = C a" if a: "a \<in> {..m}"
    for a
  proof (cases "a = 0")
    case True
    have "j mod p \<noteq> p" for j using p0 by (metis mod_less_divisor less_irrefl)
    thus ?thesis using True by (auto simp: C_def)
  next
    case False
    hence ap: "0 < a" "a < p" using a m2 by auto
    thus ?thesis using mod_add_eq_0_iff[OF ap] by (auto simp: C_def)
  qed
  have "(\<Sum> a \<le> m. card {j \<in> X. j mod p = a mod p \<or>
    (j + a) mod p = 0}) = (\<Sum> a \<le> m. card (C a))"
  proof (rule sum.cong)
    fix a assume a: "a \<in> {..m}"
    show "card {j \<in> X. j mod p = a mod p \<or> (j + a) mod p = 0} = card (C a)"
      unfolding Ceq[OF a] ..
  qed simp
  also have "\<dots> = card (\<Union> a \<in> {..m}. C a)"
  proof (rule card_UN_disjoint[symmetric])
    show "\<forall>i \<in> {..m}. \<forall>j \<in> {..m}. i \<noteq> j \<longrightarrow>
      C i \<inter> C j = {}"
      using m2 by (auto simp: C_def)
  qed (use assms(3) in \<open>auto simp: C_def\<close>)
  also have "(\<Union> a \<in> {..m}. C a) = X"
  proof (intro equalityI subsetI)
    fix j assume "j \<in> (\<Union> a \<in> {..m}. C a)"
    thus "j \<in> X" by (auto simp: C_def)
  next
    fix j assume j: "j \<in> X"
    have rp: "j mod p < p" using p0 by simp
    show "j \<in> (\<Union> a \<in> {..m}. C a)"
    proof (cases "j mod p \<le> m")
      case True
      thus ?thesis using j by (auto simp: C_def intro!: bexI[of _ "j mod p"])
    next
      case False
      hence "p - j mod p \<in> {..m}" using rp m2 by auto
      moreover have "j \<in> C (p - j mod p)" using j rp by (auto simp: C_def)
      ultimately show ?thesis by blast
    qed
  qed
  finally show ?thesis by (simp add: m_def)
qed

lemma length_outer_idx: "prime p \<Longrightarrow> 40 dvd K \<Longrightarrow>
  OuterHyp K p \<Longrightarrow> length (outer_idx K p) = hof K"
proof -
  assume p: "prime p" and K: "40 dvd K" and H: "OuterHyp K p"
  have p2: "2 < p" using H by (simp add: OuterHyp_def)
  obtain k where k: "K = 40 * k" using K by (elim dvdE)
  have hk: "hof K = 37 * k" and Nk: "Nof K = 3 * k" unfolding k hof_def Nof_def by simp_all
  have "length (outer_idx K p) = (\<Sum> a \<in> set [0..<mHalf p + 1]. outerCount K p a)"
    unfolding outer_idx_def length_concat map_map
      by (simp add: o_def sum_list_distinct_conv_sum_set)
  also have "set [0..<mHalf p + 1] = {..mHalf p}" by auto
  also have "(\<Sum> a \<le> mHalf p. outerCount K p a) = card {Nof K + 1..K}"
    unfolding outerCount_def outerClassPoles_def by (rule sum_classes_card[OF p p2]) simp
  also have "\<dots> = hof K" using hk Nk k by simp
  finally show ?thesis .
qed

text \<open>(4.11): the outer basis is @{text "\<int>_p"}-unimodular.\<close>
lemma outer_idx_lex:
  assumes "y < x" "x < length (outer_idx K p)"
  shows "fst (outer_idx K p ! y) < fst (outer_idx K p ! x) \<or>
         (fst (outer_idx K p ! y) = fst (outer_idx K p ! x) \<and>
           snd (outer_idx K p ! y) < snd (outer_idx K p ! x))"
  using blocks_lex[where f = "outerCount K p" and n =
    "mHalf p + 1", OF assms[unfolded outer_idx_def]]
  unfolding outer_idx_def .

lemma mem_outer_idx: "x \<in> set (outer_idx K p) \<longleftrightarrow> fst x \<le> mHalf p \<and>
  snd x < outerCount K p (fst x)"
  by (cases x) (auto simp: outer_idx_def image_iff simp del: upt_Suc)

lemma vpGge_outerBasis: "prime p \<Longrightarrow> vpGge p (outerBasis K p x) 0"
proof -
  assume p: "prime p"
  have a: "vpGge p (sqPoleProd S * (pX + [:of_nat n ^ 2:]) ^ i) 0" for S n i
    by (rule vpGge_mul0'[OF p vpGge_sqPoleProd0[OF p] vpGge_pow0'[OF p vpGge_pX_plus_sq0[OF p]]])
  have b: "vpGge p (sqPoleProd S * sqPoleProd T * (pX + [:of_nat n ^ 2:]) ^ i) 0" for S T n i
    by (rule vpGge_mul0'[OF p vpGge_mul0'[OF p vpGge_sqPoleProd0[OF p] vpGge_sqPoleProd0[OF p]]
      vpGge_pow0'[OF p vpGge_pX_plus_sq0[OF p]]])
  show ?thesis unfolding outerBasis_def Let_def by (simp only: a b if_cancel split: if_split) simp
qed

text \<open>In the outer range every class @{text "a \<ge> 1"} contains exactly the two poles
  @{text "a, p - a"} below @{text p},
  so @{text "#{j \<in> C_a. p < j} + 2 = ell p K a"} (Lean: @{text card_E_add_two}).\<close>
lemma res_class0:
  assumes "a \<le> mHalf p" "2 * mHalf p + 1 = p" "j mod p = a mod p \<or> (j + a) mod p = 0"
  shows "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
proof (cases "a = 0")
  case True
  thus ?thesis using assms(3) by auto
next
  case False
  hence ap: "0 < a" "a < p" using assms(1,2) by auto
  thus ?thesis using assms(3) mod_add_eq_0_iff[OF ap, of j] by auto
qed
lemma card_class_high_add_two:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p"
  shows "card {j \<in> outerClassPoles K p a. p < j} + 2 = ell p K a"
proof -
  have h: "7 \<le> p" "p \<le> K" "2 * Nof K < p" using assms(2) by (auto simp: OuterHyp_def)
  have "odd p" using prime_odd_nat[OF assms(1)] h(1) by simp
  then obtain t where t: "p = 2 * t + 1" by (elim oddE)
  have m: "2 * mHalf p + 1 = p" by (simp add: mHalf_def t)
  have ap: "a < p" "2 * a < p" using m assms(4) by linarith+
  have ane: "a \<noteq> p - a" using ap by linarith
  define P where "P j \<longleftrightarrow> j mod p = a mod p \<or> (j + a) mod p = 0" for j
  define X where "X = {j \<in> outerClassPoles K p a. p < j}"
  have E: "{j \<in> {1..K}. P j} = {a, p - a} \<union> X"
  proof (intro equalityI subsetI)
    fix j assume j: "j \<in> {j \<in> {1..K}. P j}"
    have r: "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
      by (rule res_class0[OF assms(4) m]) (use j in \<open>simp add: P_def\<close>)
    show "j \<in> {a, p - a} \<union> X"
    proof (cases "j < p")
      case True
      thus ?thesis using r by auto
    next
      case False
      have "j \<noteq> p"
      proof
        assume "j = p"
        hence "j mod p = 0" by simp
        thus False using r ap assms(3) by auto
      qed
      hence "p < j" using False by simp
      thus ?thesis using j h by (auto simp: X_def outerClassPoles_def P_def)
    qed
  next
    fix j assume "j \<in> {a, p - a} \<union> X"
    thus "j \<in> {j \<in> {1..K}. P j}" using assms(3) ap h
      by (auto simp: X_def outerClassPoles_def P_def)
  qed
  have fin: "finite X" by (simp add: X_def outerClassPoles_def)
  have "ell p K a = card ({a, p - a} \<union> X)" unfolding ell_def P_def[symmetric] E ..
  also have "\<dots> = card {a, p - a} + card X"
    by (rule card_Un_disjoint) (use ap fin in \<open>auto simp: X_def\<close>)
  also have "card {a, p - a} = 2" using ane by simp
  finally show ?thesis unfolding X_def by simp
qed

text \<open>Modulo @{text p}, a pole @{text "j \<in> C_a"} with @{text "p < j"} satisfies
  @{text "j^2 \<equiv> a^2"}: the factor @{text "t + j^2"} is
  @{text "(t + a^2) + (j^2 - a^2)"} with @{text "p | j^2 - a^2"}.\<close>
lemma class_sq_cong:
  assumes "prime p" "1 \<le> a" "a \<le> mHalf p" "j \<in> outerClassPoles K p a"
  shows "vge p (of_nat j ^ 2 - of_nat a ^ 2) 1"
proof -
  have p: "prime p" using assms(1) .
  have j: "j mod p = a mod p \<or> (j + a) mod p = 0" using assms(4)
    by (simp add: outerClassPoles_def)
  have "int p dvd (int j - int a) * (int j + int a)"
  proof (cases "j mod p = a mod p")
    case True
    hence "int j mod int p = int a mod int p" by (metis of_nat_mod)
    hence "int p dvd int j - int a" by (simp add: mod_eq_dvd_iff)
    thus ?thesis by simp
  next
    case False
    hence "(j + a) mod p = 0" using j by simp
    hence "p dvd j + a" by (rule mod_0_imp_dvd)
    hence "int p dvd int j + int a" by (simp flip: of_nat_add)
    thus ?thesis by simp
  qed
  then obtain w where w: "(int j - int a) * (int j + int a) = int p * w" by (elim dvdE)
  have e: "(of_nat j ^ 2 - of_nat a ^ 2 :: rat) = of_nat p * of_int w"
  proof -
    have "(of_nat j ^ 2 - of_nat a ^ 2 :: rat) = of_int ((int j - int a) * (int j + int a))"
      by (simp add: power2_eq_square algebra_simps)
    thus ?thesis unfolding w by simp
  qed
  have "vge p (of_nat p * of_int w) (1 + 0)"
    by (rule vge_mul[OF p vge_p_self[OF p] vge_of_int[OF p]])
  thus ?thesis unfolding e by simp
qed


subsection \<open>The modified functional @{text "mu^0_X"} and the structure of the outer
  basis\<close>

definition tailPoles :: "nat \<Rightarrow> nat set" where "tailPoles K = {Nof K + 1..K}"

text \<open>@{text "mu^0"} on polynomials.\<close>
definition muModPoly :: "nat \<Rightarrow> rat poly \<Rightarrow> rat" where
  "muModPoly p Q = (\<Sum> e \<le> degree Q. Polynomial.coeff Q e * (muMono e - cCorr p e /
    of_nat p))"

lemma muXmod_eq:
  "muXmod p S P = [:muModPoly p (P div sqPoleProd S):] + (\<Sum> j \<in>
    S. [:sqResidue S P j:] * muPole j)"
  by (simp add: muXmod_def muModPoly_def)

lemma muModPoly_vge: "prime p \<Longrightarrow> 7 \<le> p \<Longrightarrow>
  vpGge p Q 0 \<Longrightarrow> vge p (muModPoly p Q) 0"
proof -
  assume p: "prime p" and p7: "7 \<le> p" and Q: "vpGge p Q 0"
  show ?thesis unfolding muModPoly_def
  proof (rule vge_sum[OF p])
    fix e
    have "vge p (Polynomial.coeff Q e * (muMono e - cCorr p e / of_nat p)) (0 + 0)"
      by (rule vge_mul[OF p Q[unfolded vpGge_iff, rule_format] muMod_vge[OF p p7]])
    thus "vge p (Polynomial.coeff Q e * (muMono e - cCorr p e / of_nat p)) 0" by simp
  qed simp
qed

lemma muModPoly_sub_muPoly:
  "muModPoly p Q = muPoly Q - (\<Sum> e \<le>
    degree Q. Polynomial.coeff Q e * (cCorr p e / of_nat p))"
  by (simp add: muModPoly_def muPoly_def right_diff_distrib sum_subtractf)

lemma muXmod_as_muX:
  "muXmod p S P = muX S P - [:\<Sum> e \<le>
    degree (P div sqPoleProd S). Polynomial.coeff (P div sqPoleProd S) e * (cCorr p e / of_nat p):]"
proof -
  define Q where "Q = P div sqPoleProd S"
  define Sg where "Sg = (\<Sum> j \<in> S. [:sqResidue S P j:] * muPole j)"
  define Y where "Y = (\<Sum> e \<le> degree Q. Polynomial.coeff Q e * (cCorr p e / of_nat p))"
  have "muXmod p S P = [:muPoly Q - Y:] + Sg"
    by (simp add: muXmod_eq muModPoly_sub_muPoly Q_def Sg_def Y_def)
  also have "\<dots> = ([:muPoly Q:] + Sg) - [:Y:]" by (simp add: algebra_simps)
  also have "[:muPoly Q:] + Sg = muX S P" by (simp add: muX_def Q_def Sg_def)
  finally show ?thesis by (simp add: Y_def Q_def)
qed

lemma lead_coeff_sqPoleProd: "finite S \<Longrightarrow> lead_coeff (sqPoleProd S) = 1"
  by (rule lead_coeff_sqPoleProd0)

lemma vpGge_sqPoleProd: "prime p \<Longrightarrow> vpGge p (sqPoleProd S) 0"
  by (rule vpGge_sqPoleProd0)

lemma vpGge_mul0: "prime p \<Longrightarrow> vpGge p A 0 \<Longrightarrow>
  vpGge p B 0 \<Longrightarrow> vpGge p (A * B) 0"
  using vpGge_mul[of p A 0 B 0] by simp

lemma vpGge_pow0: "prime p \<Longrightarrow> vpGge p A 0 \<Longrightarrow> vpGge p (A ^ n) 0"
  by (induction n) (auto simp: vpGge_one vpGge_mul0)

lemma vpGge_pX_plus_sq: "prime p \<Longrightarrow> vpGge p (pX + [:of_nat n ^ 2:]) 0"
  by (rule vpGge_pX_plus_sq0)

lemma vpGge_Dm: "prime p \<Longrightarrow> vpGge p (Dm m) 0"
  by (rule vpGge_Dm0)

lemma wOut_nonpos: "wOut K p x \<le> 0"
  by (auto simp: wOut_def Let_def)

lemma wOut_halfInt: "\<exists>k::int. 2 * wOut K p x = of_int k"
proof -
  have m: "2 * min 0 t = min 0 (2 * t)" for t :: rat by (simp add: min_def)
  have mi: "min 0 t \<in> \<int>" if "t \<in> \<int>" for t :: rat using that by (simp add: min_def)
  have "2 * wOut K p x \<in> \<int>"
  proof (cases "fst x = 0")
    case True
    thus ?thesis by (auto simp: wOut_def Let_def)
  next
    case False
    define l where "l = ell p K (fst x)"
    define d where "d = (if fst x \<le> Nof K then 1 else 0 :: rat)"
    have d: "d \<in> \<int>" by (simp add: d_def)
    have w: "wOut K p x = (if snd x < l - 2 then min 0 (of_nat (snd x) + 3 * d - (of_nat l + 4) /
      2) else 0)"
      using False by (simp add: wOut_def Let_def l_def d_def)
    have e: "2 * (of_nat (snd x) + 3 * d - (of_nat l + 4) / 2) =
      2 * of_nat (snd x) + 6 * d - of_nat l - (4 :: rat)"
      by (simp add: field_simps)
    have "2 * of_nat (snd x) + 6 * d - of_nat l - (4 :: rat) \<in> \<int>"
      using d by (intro Ints_diff Ints_add Ints_mult) simp_all
    hence mm: "min 0 (2 * (of_nat (snd x) + 3 * d - (of_nat l + 4) / 2)) \<in> \<int>" unfolding e
      by (rule mi)
    show ?thesis
    proof (cases "snd x < l - 2")
      case True
      have "2 * wOut K p x = min 0 (2 * (of_nat (snd x) + 3 * d - (of_nat l + 4) / 2))"
        by (simp only: w if_P[OF True] m)
      thus ?thesis using mm by simp
    next
      case False
      thus ?thesis by (simp add: w)
    qed
  qed
  thus ?thesis by (auto elim: Ints_cases)
qed

text \<open>@{text "mu^0_X"} also depends only on the rational function.\<close>
lemma muXmod_mul_cancel_set:
  "finite T \<Longrightarrow> finite S \<Longrightarrow> T \<inter> S = {} \<Longrightarrow>
    muXmod p (T \<union> S) (P * sqPoleProd T) = muXmod p S P"
proof -
  assume T: "finite T" and S: "finite S" and d: "T \<inter> S = {}"
  have u: "sqPoleProd (T \<union> S) = sqPoleProd T * sqPoleProd S" using T S d
    by (simp add: sqPoleProd_def prod.union_disjoint)
  have "sqPoleProd T * P div (sqPoleProd T * sqPoleProd S) = P div sqPoleProd S"
    by (rule div_mult_mult1[OF sqPoleProd_nonzero[OF T]])
  hence q: "(P * sqPoleProd T) div sqPoleProd (T \<union> S) = P div sqPoleProd S" unfolding u
    by (simp add: mult.commute)
  show ?thesis by (simp only: muXmod_as_muX q muX_mul_cancel_set[OF S T d])
qed

lemma muXmod_empty: "muXmod p {} P = [:muModPoly p P:]"
  by (simp add: muXmod_eq sqPoleProd_def)

lemma sqPoleProd_union: "finite s \<Longrightarrow> finite t \<Longrightarrow>
  s \<inter> t = {} \<Longrightarrow> sqPoleProd (s \<union> t) = sqPoleProd s * sqPoleProd t"
  by (simp add: sqPoleProd_def prod.union_disjoint)

lemma sqPoleProd_Icc_split: "sqPoleProd {1..K} = Dm (Nof K) * sqPoleProd (tailPoles K)"
proof -
  have "Nof K \<le> K" by (simp add: Nof_def)
  hence u: "{1..K} = {1..Nof K} \<union> tailPoles K" by (auto simp: tailPoles_def)
  have "sqPoleProd ({1..Nof K} \<union> tailPoles K) =
    sqPoleProd {1..Nof K} * sqPoleProd (tailPoles K)"
    by (rule sqPoleProd_union) (auto simp: tailPoles_def)
  moreover have "Dm (Nof K) = sqPoleProd {1..Nof K}" by (simp add: Dm_def sqPoleProd_def)
  ultimately show ?thesis unfolding u by simp
qed

text \<open>The @{text q}-part of an outer basis row: @{text "outerBasis = P_a \<cdot> oq"}.\<close>
definition oq :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> rat poly" where
  "oq K p x = (let a = fst x; i = snd x in
     if a = 0 then (pX + [:of_nat p ^ 2:]) ^ i
     else if i < ell p K a - 2 then (pX + [:of_nat a ^ 2:]) ^ i
     else sqPoleProd {j \<in> outerClassPoles K p a. p <
       j} * (pX + [:of_nat a ^ 2:]) ^ (i - (ell p K a - 2)))"

lemma outerBasis_eq: "outerBasis K p x =
  sqPoleProd (tailPoles K - outerClassPoles K p (fst x)) * oq K p x"
  by (simp add: outerBasis_def oq_def tailPoles_def Let_def mult.assoc)

lemma oq_vge: "prime p \<Longrightarrow> vpGge p (oq K p x) 0"
proof -
  assume p: "prime p"
  have a: "vpGge p ((pX + [:of_nat n ^ 2:]) ^ i) 0" for n i
    by (rule vpGge_pow0[OF p vpGge_pX_plus_sq[OF p]])
  have b: "vpGge p (sqPoleProd S * (pX + [:of_nat n ^ 2:]) ^ i) 0" for S n i
    by (rule vpGge_mul0[OF p vpGge_sqPoleProd[OF p] a])
  show ?thesis unfolding oq_def Let_def by (simp only: a b if_cancel split: if_split) simp
qed

lemma outerGram_apply:
  "x < length (outer_idx K p) \<Longrightarrow> y < length (outer_idx K p) \<Longrightarrow>
   outerGram K p $$ (x, y) = muXmod p {1..K} (Dm (Nof K) ^ 6 * outerBasis K p (outer_idx K p ! x) *
     outerBasis K p (outer_idx K p ! y))"
  by (simp add: outerGram_def Let_def)

subsection \<open>Arithmetic of the pole classes\<close>

lemma mem_class: "j \<in> outerClassPoles K p a \<longleftrightarrow> Nof K + 1 \<le> j \<and>
  j \<le> K \<and> (j mod p = a mod p \<or> (j + a) mod p = 0)"
  by (auto simp: outerClassPoles_def)

text \<open>Facts implied by (4.9).\<close>
lemma outer_facts:
  assumes "prime p" "OuterHyp K p"
  shows "7 \<le> p \<and> odd p \<and> 2 * mHalf p + 1 = p \<and> p \<le> K \<and> K < 3 * p \<and>
    2 * Nof K < p \<and>
         (K < 2 * p \<longrightarrow> K mod p = K - p) \<and> (2 * p \<le> K \<longrightarrow>
           K mod p = K - 2 * p)"
proof -
  have h: "7 \<le> p" "p \<le> K" "K < 3 * p" "2 * Nof K < p" using assms(2)
    by (auto simp: OuterHyp_def)
  have o: "odd p" using prime_odd_nat[OF assms(1)] h(1) by simp
  then obtain k where k: "p = 2 * k + 1" by (elim oddE)
  have m: "2 * mHalf p + 1 = p" by (simp add: mHalf_def k)
  have k1: "K < 2 * p \<longrightarrow> K mod p = K - p"
  proof
    assume "K < 2 * p"
    hence lt: "K - p < p" using h by linarith
    have "K mod p = (K - p) mod p" using h(2) by (simp add: le_mod_geq)
    also have "\<dots> = K - p" using lt by simp
    finally show "K mod p = K - p" .
  qed
  have k2: "2 * p \<le> K \<longrightarrow> K mod p = K - 2 * p"
  proof
    assume a: "2 * p \<le> K"
    hence lt: "K - 2 * p < p" using h by linarith
    have "K mod p = (K - p) mod p" using h(2) by (simp add: le_mod_geq)
    also have "\<dots> = (K - p - p) mod p" using a by (simp add: le_mod_geq)
    also have "K - p - p = K - 2 * p" by simp
    also have "(K - 2 * p) mod p = K - 2 * p" using lt by simp
    finally show "K mod p = K - 2 * p" .
  qed
  show ?thesis using h o m k1 k2 by blast
qed

lemma res_class:
  assumes "a \<le> mHalf p" "2 * mHalf p + 1 = p" "j mod p = a mod p \<or> (j + a) mod p = 0"
  shows "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
proof (cases "a = 0")
  case True
  thus ?thesis using assms(3) by auto
next
  case False
  hence ap: "0 < a" "a < p" using assms(1,2) by auto
  thus ?thesis using assms(3) mod_add_eq_0_iff[OF ap, of j] by auto
qed
lemma class_disjoint:
  assumes "prime p" "OuterHyp K p" "a \<le> mHalf p" "c \<le> mHalf p" "a \<noteq> c"
  shows "outerClassPoles K p a \<inter> outerClassPoles K p c = {}"
proof -
  have m: "2 * mHalf p + 1 = p" using outer_facts[OF assms(1,2)] by blast
  { fix j assume ja: "j \<in> outerClassPoles K p a" and jc: "j \<in> outerClassPoles K p c"
    have "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
      by (rule res_class[OF assms(3) m]) (use ja in \<open>simp add: mem_class\<close>)
    moreover have "j mod p = c \<or> (1 \<le> c \<and> j mod p = p - c)"
      by (rule res_class[OF assms(4) m]) (use jc in \<open>simp add: mem_class\<close>)
    ultimately have False using assms(3,4,5) m by (elim disjE conjE; linarith) }
  thus ?thesis by blast
qed

lemma class_small:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p" "j \<in>
    outerClassPoles K p a" "j < p"
  shows "j = a \<or> j = p - a"
proof -
  have m: "2 * mHalf p + 1 = p" using outer_facts[OF assms(1,2)] by blast
  have "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
    by (rule res_class[OF assms(4) m]) (use assms(5) in \<open>simp add: mem_class\<close>)
  thus ?thesis using assms(6) by auto
qed

lemma class_not_dvd:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p" "j \<in> outerClassPoles K p a"
  shows "\<not> p dvd j"
proof
  assume d: "p dvd j"
  have m: "2 * mHalf p + 1 = p" using outer_facts[OF assms(1,2)] by blast
  have "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
    by (rule res_class[OF assms(4) m]) (use assms(5) in \<open>simp add: mem_class\<close>)
  moreover have "j mod p = 0" using d by simp
  ultimately show False using assms(3,4) m by auto
qed

lemma pa_mem:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p"
  shows "p - a \<in> outerClassPoles K p a"
proof -
  obtain m: "2 * mHalf p + 1 = p" and pK: "p \<le> K" and N: "2 * Nof K < p"
    using outer_facts[OF assms(1,2)] by blast
  have "Nof K + 1 \<le> p - a" using N m assms(4) by linarith
  moreover have "p - a \<le> K" using pK by simp
  moreover have "(p - a + a) mod p = 0" using assms(4) m by simp
  ultimately show ?thesis by (simp add: mem_class)
qed

lemma a_mem_iff:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p"
  shows "a \<in> outerClassPoles K p a \<longleftrightarrow> Nof K < a"
proof -
  obtain m: "2 * mHalf p + 1 = p" and pK: "p \<le> K" using outer_facts[OF assms(1,2)] by blast
  have "a \<le> K" using m pK assms(4) by linarith
  thus ?thesis by (auto simp: mem_class)
qed

lemma card_outerClass:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p"
  shows "card (outerClassPoles K p a) + (if a \<le> Nof K then 1 else 0) = ell p K a"
proof -
  obtain m: "2 * mHalf p + 1 = p" and N: "2 * Nof K < p" using outer_facts[OF assms(1,2)] by blast
  define P where "P j \<longleftrightarrow> j mod p = a mod p \<or> (j + a) mod p = 0" for j
  have NK: "Nof K \<le> K" by (simp add: Nof_def)
  have E: "{j \<in> {1..K}. P j} = outerClassPoles K p a \<union> {j \<in> {1..Nof K}. P j}"
    using NK by (auto simp: outerClassPoles_def P_def)
  have L1: "j = a" if j: "j \<in> {1..Nof K}" "P j" for j
  proof -
    have jp: "j < p" using j N by auto
    have "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
      by (rule res_class[OF assms(4) m]) (use j in \<open>simp add: P_def\<close>)
    hence "j = a \<or> j = p - a" using jp by auto
    moreover have "j \<noteq> p - a" using j N m assms(4) by auto
    ultimately show ?thesis by blast
  qed
  have L2: "P a" by (simp add: P_def)
  have L: "{j \<in> {1..Nof K}. P j} = (if a \<le> Nof K then {a} else {})"
  proof (cases "a \<le> Nof K")
    case True
    have "{j \<in> {1..Nof K}. P j} \<subseteq> {a}" using L1 by blast
    moreover have "a \<in> {j \<in> {1..Nof K}. P j}" using True assms(3) L2 by simp
    ultimately have "{j \<in> {1..Nof K}. P j} = {a}" by blast
    thus ?thesis using True by simp
  next
    case False
    have "{j \<in> {1..Nof K}. P j} = {}"
    proof (rule equals0I)
      fix j assume j: "j \<in> {j \<in> {1..Nof K}. P j}"
      hence "j = a" using L1 by blast
      moreover have "j \<le> Nof K" using j by simp
      ultimately show False using False by simp
    qed
    thus ?thesis using False by simp
  qed
  have "ell p K a = card (outerClassPoles K p a) + card {j \<in> {1..Nof K}. P j}"
    unfolding ell_def P_def[symmetric] E by (rule card_Un_disjoint) (auto simp: outerClassPoles_def)
  thus ?thesis unfolding L by simp
qed

lemma zero_class:
  assumes "prime p" "OuterHyp K p"
  shows "outerClassPoles K p 0 = (if 2 * p \<le> K then {p, 2 * p} else {p})"
proof -
  obtain pK: "p \<le> K" and K3: "K < 3 * p" and N: "2 * Nof K < p" using outer_facts[OF assms]
    by blast
  have "j \<in> outerClassPoles K p 0 \<longleftrightarrow> j = p \<or> (2 * p \<le> K \<and>
    j = 2 * p)" for j
  proof
    assume "j \<in> outerClassPoles K p 0"
    hence j: "Nof K + 1 \<le> j" "j \<le> K" "p dvd j" by (auto simp: mem_class)
    then obtain t where t: "j = p * t" by (elim dvdE)
    have "p * t < p * 3" using t j K3 by linarith
    hence "t < 3" by simp
    moreover have "t \<noteq> 0"
    proof
      assume "t = 0"
      thus False using t j(1) by simp
    qed
    ultimately have "t = 1 \<or> t = 2" by auto
    thus "j = p \<or> (2 * p \<le> K \<and> j = 2 * p)" using t j by (auto simp: mult.commute)
  next
    assume "j = p \<or> (2 * p \<le> K \<and> j = 2 * p)"
    thus "j \<in> outerClassPoles K p 0" using pK N by (auto simp: mem_class)
  qed
  thus ?thesis by auto
qed

subsection \<open>Valuations at the poles\<close>

lemma vge_inv_two_mul: "prime p \<Longrightarrow> \<not> p dvd j \<Longrightarrow>
  p \<noteq> 2 \<Longrightarrow> vge p (1 / (2 * of_nat j)) 0"
proof -
  assume p: "prime p" and nd: "\<not> p dvd j" and p2: "p \<noteq> 2"
  have "\<not> p dvd 2"
  proof
    assume "p dvd 2"
    hence "p \<le> 2" by (rule dvd_imp_le) simp
    thus False using prime_ge_2_nat[OF p] p2 by simp
  qed
  hence "\<not> p dvd 2 * j" using nd prime_dvd_mult_iff[OF p] by auto
  from vge_inverse_unit[OF p this] show ?thesis by (simp add: inverse_eq_divide)
qed

text \<open>@{text "mu_X(1/(t+j^2))"} has coefficients of valuation @{text "\<ge> \<beta>"} when
  @{text "j^4 H_j"} and @{text "1/(2j)"} do.\<close>
lemma muPole_coeff0: "Polynomial.coeff (muPole j) n =
    (if n = 1 then of_nat j ^ 4 else if n =
      0 then - (of_nat j ^ 4 * H5 j) - 1 / 4 + 1 / (2 * of_nat j) else 0)"
  unfolding muPole_def pX_minus_const by (auto simp: coeff_pCons split: nat.split)

lemma vge_pow_mul: "prime p \<Longrightarrow> vge p x b \<Longrightarrow>
  vge p (x ^ n) (of_nat n * b)"
proof -
  assume p: "prime p" and h: "vge p x b"
  show ?thesis
  proof (induction n)
    case 0
    show ?case by (simp add: vge_one)
  next
    case (Suc n)
    have "vge p (x * x ^ n) (b + of_nat n * b)" by (rule vge_mul[OF p h Suc.IH])
    thus ?case by (simp add: algebra_simps)
  qed
qed

lemma nat_log_le_one_sq: "prime p \<Longrightarrow> K < p ^ 2 \<Longrightarrow> nat_log p K \<le> 1"
proof -
  assume p: "prime p" and K: "K < p ^ 2"
  have "floorlog p K \<le> 2" by (rule floorlog_leI[OF K]) (use prime_gt_1_nat[OF p] in simp_all)
  thus ?thesis by (simp add: nat_log_def)
qed

lemma vge_of_int_dvd: "prime p \<Longrightarrow> int p dvd z \<Longrightarrow> vge p (of_int z) 1"
proof -
  assume p: "prime p" and "int p dvd z"
  then obtain w where w: "z = int p * w" by (elim dvdE)
  have "vge p (of_nat p * of_int w) (1 + 0)"
    by (rule vge_mul[OF p vge_p_self[OF p] vge_of_int[OF p]])
  thus ?thesis by (simp add: w)
qed
lemma muPole_vge:
  assumes "prime p" "\<beta> \<le> 0" "p \<noteq>
    2" "vge p (of_nat j ^ 4 * H5 j) \<beta>" "vge p (1 / (2 * of_nat j)) \<beta>"
  shows "vpGge p (muPole j) \<beta>"
proof -
  have p: "prime p" and b0: "\<beta> \<le> 0" and p2: "p \<noteq> 2" using assms(1-3) .
  have n4: "\<not> p dvd 4"
  proof
    assume "p dvd 4"
    hence "p dvd 2 * 2" by simp
    hence "p dvd 2" using prime_dvd_mult_iff[OF p, of 2 2] by simp
    hence "p \<le> 2" by (rule dvd_imp_le) simp
    thus False using prime_ge_2_nat[OF p] p2 by simp
  qed
  have "vge p (inverse (of_nat 4)) 0" by (rule vge_inverse_unit[OF p n4])
  hence "vge p (1 / 4) 0" by (simp add: inverse_eq_divide)
  hence q: "vge p (1 / 4) \<beta>" by (rule vge_mono) (rule b0)
  have c0v: "vge p (- (of_nat j ^ 4 * H5 j) - 1 / 4 + 1 / (2 * of_nat j)) \<beta>"
    by (rule vge_add[OF p vge_diff[OF p vge_neg[OF assms(4)] q] assms(5)])
  have j4: "vge p (of_nat j ^ 4) \<beta>"
    by (rule vge_mono[OF vge_pow[OF p vge_of_nat[OF p]]]) (use b0 in simp)
  show ?thesis unfolding vpGge_iff muPole_coeff0 by (simp add: c0v j4 vge_zero)
qed

lemma muPole_vge_small: "prime p \<Longrightarrow> 1 \<le> j \<Longrightarrow>
  j < p \<Longrightarrow> p \<noteq> 2 \<Longrightarrow> vpGge p (muPole j) 0"
proof -
  assume p: "prime p" and j1: "1 \<le> j" and jp: "j < p" and p2: "p \<noteq> 2"
  have nd: "\<not> p dvd j" using j1 jp by (auto dest: dvd_imp_le)
  have a: "vge p (of_nat j ^ 4 * H5 j) (0 + 0)"
    by (rule vge_mul[OF p vge_pow[OF p vge_of_nat[OF p]] vge_H5_small[OF p jp]])
  show ?thesis by (rule muPole_vge[OF p order.refl p2]) (use a vge_inv_two_mul[OF p nd p2] in
    simp_all)
qed

lemma muPole_vge_mult: "prime p \<Longrightarrow> 7 \<le> p \<Longrightarrow>
  1 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow> vpGge p (muPole (t * p)) (- 1)"
proof -
  assume p: "prime p" and p7: "7 \<le> p" and t1: "1 \<le> t" and t2: "t \<le> 2"
  have p2: "p \<noteq> 2" using p7 by simp
  have tp: "t * p < p ^ 2" using t2 p7 by (simp add: power2_eq_square)
  have v1: "vge p (of_nat (t * p)) 1" by (rule vge_dvd_nat[OF p]) simp
  have v4: "vge p (of_nat (t * p) ^ 4) (of_nat 4 * 1)" by (rule vge_pow_mul[OF p v1])
  have h: "vge p (H5 (t * p)) (- 5 * of_nat (nat_log p (t * p)))" by (rule vge_H5[OF p order.refl])
  have nl: "nat_log p (t * p) \<le> 1" by (rule nat_log_le_one_sq[OF p tp])
  have h': "vge p (H5 (t * p)) (- 5)" by (rule vge_mono[OF h]) (use nl in simp)
  have a: "vge p (of_nat (t * p) ^ 4 * H5 (t * p)) (of_nat 4 * 1 + - 5)"
    by (rule vge_mul[OF p v4 h'])
  have z0: "int (2 * t * p) \<noteq> 0" using t1 p7 by simp
  have nd: "\<not> int p ^ (1 + 1) dvd int (2 * t * p)"
  proof
    assume "int p ^ (1 + 1) dvd int (2 * t * p)"
    hence "p * p dvd (2 * t) * p" by (simp add: power2_eq_square mult_ac flip: of_nat_mult
      of_nat_power)
    hence "p dvd 2 * t" using p7 by simp
    hence "p \<le> 2 * t" by (rule dvd_imp_le) (use t1 in simp)
    thus False using t2 p7 by simp
  qed
  have b: "vge p (1 / of_int (int (2 * t * p))) (- of_nat 1)" by (rule vge_inv_int[OF p z0 nd])
  show ?thesis
    by (rule muPole_vge[OF p _ p2]) (use a b in \<open>simp_all add: mult.assoc\<close>)
qed

lemma nat_log_le_one_of_lt_sq: "prime p \<Longrightarrow> K < p ^ 2 \<Longrightarrow>
  nat_log p K \<le> 1"
proof -
  assume p: "prime p" and K: "K < p ^ 2"
  have "floorlog p K \<le> 2" by (rule floorlog_leI[OF K]) (use prime_gt_1_nat[OF p] in simp_all)
  thus ?thesis by (simp add: nat_log_def)
qed

lemma muPole_vge_class:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p" "j \<in> outerClassPoles K p a"
  shows "vpGge p (muPole j) (- 5)"
proof -
  have p: "prime p" using assms(1) .
  have p7: "7 \<le> p" using outer_facts[OF assms(1,2)] by blast
  have p2: "p \<noteq> 2" using p7 by simp
  have "j \<le> K" using assms(5) by (simp add: mem_class)
  moreover have "2 * K < p ^ 2" using assms(2) by (simp add: OuterHyp_def)
  ultimately have jp: "j < p ^ 2" by linarith
  have h: "vge p (H5 j) (- 5 * of_nat (nat_log p j))" by (rule vge_H5[OF p order.refl])
  have nl: "nat_log p j \<le> 1" by (rule nat_log_le_one_sq[OF p jp])
  have h': "vge p (H5 j) (- 5)" by (rule vge_mono[OF h]) (use nl in simp)
  have a: "vge p (of_nat j ^ 4 * H5 j) (0 + - 5)"
    by (rule vge_mul[OF p vge_pow[OF p vge_of_nat[OF p]] h'])
  have b: "vge p (1 / (2 * of_nat j)) 0" by (rule vge_inv_two_mul[OF p class_not_dvd[OF assms] p2])
  show ?thesis by (rule muPole_vge[OF p _ p2]) (use a vge_mono[OF b] in simp_all)
qed

text \<open>@{text "mu^0_X(R / \<Prod>_{j\<in>S}(t+j^2))"} is bounded by its residue terms,
  for integral @{text R}.\<close>
lemma muXmod_vge_of_residues:
  assumes "prime p" "7 \<le> p" "finite S" "vpGge p R 0" "B \<le> 0"
    and "\<And>j. j \<in> S \<Longrightarrow> vpGge p ([:sqResidue S R j:] * muPole j) B"
  shows "vpGge p (muXmod p S R) B"
proof -
  have p: "prime p" and p7: "7 \<le> p" and S: "finite S" and R: "vpGge p R 0" and B: "B \<le> 0"
    using assms(1-5) .
  have q: "vpGge p (R div sqPoleProd S) 0"
    by (rule vpGge_div_monic[OF p R lead_coeff_sqPoleProd[OF S] vpGge_sqPoleProd[OF p]])
  have c: "vpGge p [:muModPoly p (R div sqPoleProd S):] B"
    by (rule vpGge_mono[OF vpGge_C[OF muModPoly_vge[OF p p7 q]] B])
  show ?thesis unfolding muXmod_eq by (rule vpGge_add[OF p c vpGge_sum[OF p S assms(6)]])
qed

lemma sq_sub_vge:
  assumes "prime p" "OuterHyp K p" "j \<in> outerClassPoles K p a"
  shows "vge p (of_nat a ^ 2 - of_nat j ^ 2) 1"
proof -
  have p: "prime p" using assms(1) .
  have j: "j mod p = a mod p \<or> (j + a) mod p = 0" using assms(3) by (simp add: mem_class)
  have d: "int p dvd (int a - int j) * (int a + int j)"
  proof (cases "j mod p = a mod p")
    case True
    hence "int j mod int p = int a mod int p" by (metis of_nat_mod)
    hence "int p dvd int a - int j" by (simp add: mod_eq_dvd_iff dvd_diff_commute)
    thus ?thesis by simp
  next
    case False
    hence "(j + a) mod p = 0" using j by simp
    hence "p dvd j + a" by (rule mod_0_imp_dvd)
    hence "int p dvd int a + int j" by (simp add: add.commute flip: of_nat_add)
    thus ?thesis by simp
  qed
  have e: "(of_nat a ^ 2 - of_nat j ^ 2 :: rat) = of_int ((int a - int j) * (int a + int j))"
    by (simp add: power2_eq_square algebra_simps)
  show ?thesis unfolding e by (rule vge_of_int_dvd[OF p d])
qed

lemma eval_vge0: "prime p \<Longrightarrow> vpGge p P 0 \<Longrightarrow>
  vge p x 0 \<Longrightarrow> vge p (poly P x) 0"
  using vge_poly_eval .

lemma vge_neg_sq: "prime p \<Longrightarrow> vge p (- (of_nat j ^ 2)) 0"
proof -
  assume p: "prime p"
  show ?thesis by (rule vge_neg[OF vge_pow[OF p vge_of_nat[OF p]]])
qed

lemma vge_pow': "prime p \<Longrightarrow> vge p x b \<Longrightarrow> vge p (x ^ n) (of_nat n * b)"
proof -
  assume p: "prime p" and h: "vge p x b"
  show ?thesis
  proof (induction n)
    case 0
    show ?case by (simp add: vge_one)
  next
    case (Suc n)
    have "vge p (x * x ^ n) (b + of_nat n * b)" by (rule vge_mul[OF p h Suc.IH])
    thus ?case by (simp add: algebra_simps)
  qed
qed

lemma vge_div_of_le: "prime p \<Longrightarrow> vge p x b \<Longrightarrow>
  y \<noteq> 0 \<Longrightarrow> of_int (vp p y) \<le> U \<Longrightarrow> vge p (x / y) (b - U)"
proof -
  assume p: "prime p" and hx: "vge p x b" and y: "y \<noteq> 0" and U: "of_int (vp p y) \<le> U"
  have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer prime_imp_prime_elem)
  show ?thesis unfolding vge_def
  proof
    assume "x / y \<noteq> 0"
    hence x0: "x \<noteq> 0" by auto
    have v: "vp p (x / y) = vp p x - vp p y" unfolding vp_def
      by (rule qmultiplicity_divide[OF pe x0 y])
    have "b \<le> of_int (vp p x)" using hx x0 by (simp add: vge_def)
    thus "b - U \<le> of_int (vp p (x / y))" unfolding v of_int_diff using U by linarith
  qed
qed

lemma vp_int_le_one_of_lt_sq: "prime p \<Longrightarrow> z \<noteq> 0 \<Longrightarrow>
  nat \<bar>z\<bar> < p ^ 2 \<Longrightarrow> vp p (of_int z) \<le> 1"
proof -
  assume p: "prime p" and z: "z \<noteq> 0" and l: "nat \<bar>z\<bar> < p ^ 2"
  have "vp p (of_int z) \<le> int (nat_log p (p ^ 2 - 1))"
    by (rule vp_int_le_nat_log[OF p z]) (use l in linarith)
  also have "nat_log p (p ^ 2 - 1) \<le> 1"
    by (rule nat_log_le_one_of_lt_sq[OF p]) (use prime_gt_1_nat[OF p] in simp)
  finally show ?thesis by simp
qed

lemma D_eval_vge:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "j \<in> outerClassPoles K p a"
  shows "vge p (poly (Dm (Nof K)) (- (of_nat j ^ 2))) (if a \<le> Nof K then 1 else 0)"
proof -
  have p: "prime p" using assms(1) .
  have e: "poly (Dm (Nof K)) x = (\<Prod> k \<in> {1..Nof K}. poly (pX + [:of_nat k ^ 2:]) x)" for x
    by (simp add: Dm_def poly_prod)
  have r: "vge p (\<Prod> k \<in> I. poly (pX + [:of_nat k ^ 2:]) (- (of_nat j ^ 2))) 0"
    if "finite I" for I
    by (rule vge_prod0[OF p that], rule eval_vge0[OF p vpGge_pX_plus_sq[OF p] vge_neg_sq[OF p]])
  show ?thesis
  proof (cases "a \<le> Nof K")
    case True
    have aI: "a \<in> {1..Nof K}" using True assms(3) by simp
    have eq: "poly (Dm (Nof K)) (- (of_nat j ^ 2)) =
      poly (pX + [:of_nat a ^ 2:]) (- (of_nat j ^ 2)) *
        (\<Prod> k \<in> {1..Nof K} - {a}. poly (pX + [:of_nat k ^ 2:]) (- (of_nat j ^ 2)))"
      unfolding e by (rule prod.remove[OF _ aI]) simp
    have f: "vge p (poly (pX + [:of_nat a ^ 2:]) (- (of_nat j ^ 2))) 1"
      using sq_sub_vge[OF assms(1,2,4)] by (simp add: poly_monom algebra_simps)
    have "vge p (poly (pX + [:of_nat a ^ 2:]) (- (of_nat j ^ 2)) *
        (\<Prod> k \<in> {1..Nof K} - {a}. poly (pX + [:of_nat k ^ 2:]) (- (of_nat j ^ 2)))) (1 +
          0)"
      by (rule vge_mul[OF p f r]) simp
    thus ?thesis using True unfolding eq by simp
  next
    case False
    have "vge p (\<Prod> k \<in> {1..Nof K}. poly (pX + [:of_nat k ^ 2:]) (- (of_nat j ^ 2))) 0"
      by (rule r) simp
    thus ?thesis using False unfolding e by simp
  qed
qed

lemma node_factor_le:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p" "j \<in>
    outerClassPoles K p a" "k \<in> outerClassPoles K p a" "j \<noteq> k"
  shows "vp p (of_nat k ^ 2 - of_nat j ^ 2) \<le> 1"
proof -
  have p: "prime p" using assms(1) .
  have p7: "7 \<le> p" using outer_facts[OF assms(1,2)] by blast
  have KK: "2 * K < p ^ 2" using assms(2) by (simp add: OuterHyp_def)
  have jK: "j \<le> K" and kK: "k \<le> K" using assms(5,6) by (simp_all add: mem_class)
  define u where "u = int k - int j"
  define v where "v = int k + int j"
  have u0: "u \<noteq> 0" using assms(7) by (simp add: u_def)
  have v0: "v \<noteq> 0" using assms(5) by (auto simp: v_def mem_class)
  have e: "(of_nat k ^ 2 - of_nat j ^ 2 :: rat) = of_int u * of_int v"
    by (simp add: u_def v_def power2_eq_square algebra_simps)
  have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer prime_imp_prime_elem)
  have vs: "vp p (of_int u * of_int v) = vp p (of_int u) + vp p (of_int v)"
    unfolding vp_def by (rule qmultiplicity_mult[OF pe]) (simp_all add: u0 v0)
  have au: "\<bar>u\<bar> \<le> int K" using jK kK by (simp add: u_def abs_le_iff)
  have av: "\<bar>v\<bar> \<le> int (2 * K)" using jK kK by (simp add: v_def)
  have nu: "nat \<bar>u\<bar> < p ^ 2" using au KK by (simp only: nat_le_iff[symmetric])
  have nv: "nat \<bar>v\<bar> < p ^ 2" using av KK by (simp only: nat_le_iff[symmetric])
  have bu: "vp p (of_int u) \<le> 1" by (rule vp_int_le_one_of_lt_sq[OF p u0 nu])
  have bv: "vp p (of_int v) \<le> 1" by (rule vp_int_le_one_of_lt_sq[OF p v0 nv])
  have nd: "\<not> (int p dvd u \<and> int p dvd v)"
  proof
    assume "int p dvd u \<and> int p dvd v"
    hence "int p dvd u + v" by auto
    moreover have "u + v = int (2 * k)" by (simp add: u_def v_def)
    ultimately have "p dvd 2 * k" by (simp only: int_dvd_int_iff)
    hence "p dvd 2 \<or> p dvd k" using prime_dvd_mult_iff[OF p] by auto
    moreover have "\<not> p dvd 2" using p7 by (auto dest: dvd_imp_le)
    moreover have "\<not> p dvd k" by (rule class_not_dvd[OF assms(1-4,6)])
    ultimately show False by blast
  qed
  have z: "vp p (of_int u) = 0 \<or> vp p (of_int v) = 0"
    using nd by (auto simp: vp_def qmultiplicity_of_int not_dvd_imp_multiplicity_0)
  have nn: "0 \<le> vp p (of_int u)" "0 \<le> vp p (of_int v)"
    by (simp_all add: vp_def qmultiplicity_of_int)
  show ?thesis unfolding e vs using z bu bv nn by auto
qed

lemma node_prod_le:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p" "j \<in> outerClassPoles K p a"
  shows "(\<Prod> k \<in> outerClassPoles K p a - {j}. of_nat k ^ 2 - of_nat j ^ 2) \<noteq>
    (0 :: rat) \<and>
         of_int (vp p (\<Prod> k \<in> outerClassPoles K p a - {j}. of_nat k ^ 2 -
           of_nat j ^ 2)) \<le> of_nat (card (outerClassPoles K p a)) - (1 :: rat)"
proof -
  have p: "prime p" using assms(1) .
  have finC: "finite (outerClassPoles K p a)" by (simp add: outerClassPoles_def)
  have fin: "finite (outerClassPoles K p a - {j})" using finC by simp
  have nz: "(of_nat k ^ 2 - of_nat j ^ 2 :: rat) \<noteq> 0"
    if "k \<in> outerClassPoles K p a - {j}" for k
    using that by (simp add: power2_eq_iff_nonneg)
  have pz: "(\<Prod> k \<in> outerClassPoles K p a - {j}. of_nat k ^ 2 - of_nat j ^ 2) \<noteq>
    (0 :: rat)"
    using fin nz by (simp add: prod_zero_iff)
  have "vp p (\<Prod> k \<in> outerClassPoles K p a - {j}. of_nat k ^ 2 - of_nat j ^ 2 :: rat)
      = (\<Sum> k \<in> outerClassPoles K p a - {j}. vp p (of_nat k ^ 2 - of_nat j ^ 2 :: rat))"
    by (rule vp_prod_rat[OF p fin nz])
  also have "\<dots> \<le> (\<Sum> k \<in> outerClassPoles K p a - {j}. 1)"
    by (rule sum_mono) (use node_factor_le[OF assms(1-5)] in auto)
  also have "\<dots> = int (card (outerClassPoles K p a) - 1)" using assms(5)
    by (simp add: card_Diff_singleton)
  finally have v: "vp p (\<Prod> k \<in>
    outerClassPoles K p a - {j}. of_nat k ^ 2 - of_nat j ^ 2 :: rat) \<le>
    int (card (outerClassPoles K p a) - 1)" .
  have c1: "1 \<le> card (outerClassPoles K p a)" using assms(5) finC
    by (auto simp: card_gt_0_iff Suc_le_eq)
  have "(of_int (vp p (\<Prod> k \<in> outerClassPoles K p a - {j}. of_nat k ^ 2 -
    of_nat j ^ 2 :: rat)) :: rat)
      \<le> of_int (int (card (outerClassPoles K p a) - 1))" using v by (simp only: of_int_le_iff)
  hence "(of_int (vp p (\<Prod> k \<in> outerClassPoles K p a - {j}. of_nat k ^ 2 -
    of_nat j ^ 2 :: rat)) :: rat)
      \<le> of_nat (card (outerClassPoles K p a)) - 1" using c1 by (simp add: of_nat_diff)
  thus ?thesis using pz by simp
qed

text \<open>The class-@{text a} factor @{text \<delta>}.\<close>
definition dlt :: "nat \<Rightarrow> nat \<Rightarrow> rat" where "dlt K a = (if a \<le>
  Nof K then 1 else 0)"

text \<open>(4.12), ordinary rows: a same-class entry between rows @{text "i, i' < l - 2"}.\<close>
lemma entry_ord:
  assumes p: "prime p" and H: "OuterHyp K p" and a1: "1 \<le> a" and am: "a \<le> mHalf p"
  shows "vpGge p (muXmod p (outerClassPoles K p a)
           (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - outerClassPoles K p a) * (pX +
             [:of_nat a ^ 2:]) ^ i * (pX + [:of_nat a ^ 2:]) ^ i'))
           (min 0 (of_nat i + of_nat i' + 6 * dlt K a - of_nat (ell p K a) - 4))"
proof -
  have p7: "7 \<le> p" using H by (simp add: OuterHyp_def)
  have finC: "finite (outerClassPoles K p a)" by (simp add: outerClassPoles_def)
  define R where "R = Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - outerClassPoles K p a) * (pX +
    [:of_nat a ^ 2:]) ^ i * (pX + [:of_nat a ^ 2:]) ^ i'"
  have R0: "vpGge p R 0"
    unfolding R_def by (intro vpGge_mul0[OF p] vpGge_pow0[OF p] vpGge_Dm[OF p] vpGge_sqPoleProd[OF
      p] vpGge_pX_plus_sq[OF p])
  have cardC: "of_nat (card (outerClassPoles K p a)) = of_nat (ell p K a) - dlt K a"
    using card_outerClass[OF p H a1 am] by (auto simp: dlt_def)
  show ?thesis unfolding R_def[symmetric]
  proof (rule muXmod_vge_of_residues[OF p p7 finC R0 min.cobounded1])
    fix j assume j: "j \<in> outerClassPoles K p a"
    have num: "vge p (poly R (- (of_nat j ^ 2))) (5 * dlt K a + of_nat i + of_nat i')"
    proof -
      have x: "vge p (- (of_nat j ^ 2)) 0" by (rule vge_neg_sq[OF p])
      have d: "vge p (poly (Dm (Nof K)) (- (of_nat j ^ 2))) (dlt K a)"
        using D_eval_vge[OF p H a1 j] by (simp add: dlt_def)
      have s: "vge p (poly (sqPoleProd (tailPoles K - outerClassPoles K p a)) (- (of_nat j ^ 2))) 0"
        by (rule eval_vge0[OF p vpGge_sqPoleProd[OF p] x])
      have f: "vge p (poly (pX + [:of_nat a ^ 2:]) (- (of_nat j ^ 2))) 1"
        using sq_sub_vge[OF p H j] by (simp add: poly_monom algebra_simps)
      have "vge p (poly (Dm (Nof K)) (- (of_nat j ^ 2)) ^ 5 * poly (sqPoleProd (tailPoles K -
        outerClassPoles K p a)) (- (of_nat j ^ 2)) *
          poly (pX + [:of_nat a ^ 2:]) (- (of_nat j ^ 2)) ^ i * poly (pX +
            [:of_nat a ^ 2:]) (- (of_nat j ^ 2)) ^ i')
          (of_nat 5 * dlt K a + 0 + of_nat i * 1 + of_nat i' * 1)"
        by (rule vge_mul[OF p vge_mul[OF p vge_mul[OF p vge_pow'[OF p d] s] vge_pow'[OF p f]]
          vge_pow'[OF p f]])
      thus ?thesis unfolding R_def poly_mult poly_power by simp
    qed
    have res: "vge p (sqResidue (outerClassPoles K p a) R j) (5 * dlt K a + of_nat i + of_nat i' -
      (of_nat (card (outerClassPoles K p a)) - 1))"
      unfolding sqResidue_def using node_prod_le[OF p H a1 am j]
        by (intro vge_div_of_le[OF p num]) auto
    show "vpGge p ([:sqResidue (outerClassPoles K p a) R j:] * muPole j) (min 0 (of_nat i +
      of_nat i' + 6 * dlt K a - of_nat (ell p K a) - 4))"
      by (rule vpGge_mono[OF vpGge_mul[OF p vpGge_C[OF res] muPole_vge_class[OF p H a1 am j]]])
        (use cardC min.cobounded2[of 0 "of_nat i + of_nat i' + 6 * dlt K a - of_nat (ell p K a) -
          4 :: rat"] in linarith)
  qed
qed

lemma small_poles:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p"
  shows "{j \<in> outerClassPoles K p a. j < p} = (if a \<le> Nof K then {p - a} else {a, p - a})"
proof -
  obtain m: "2 * mHalf p + 1 = p" using outer_facts[OF assms(1,2)] by blast
  have ap: "a < p" and pap: "p - a < p" using m assms(3,4) by auto
  have "j \<in> {j \<in> outerClassPoles K p a. j < p} \<longleftrightarrow> j = p - a \<or>
    (\<not> a \<le> Nof K \<and> j = a)" for j
    using class_small[OF assms, of j] pa_mem[OF assms] a_mem_iff[OF assms] ap pap by auto
  thus ?thesis by auto
qed

subsection \<open>The two small poles @{text a}, @{text "p - a"}\<close>

text \<open>@{text "\<Sum>_{v=a}^{p-a} v^{-5} \<equiv> 0 (mod p)"},
  by pairing @{text "v \<leftrightarrow> p - v"}.\<close>
lemma pair_sum_vge:
  assumes "prime p" "p \<noteq> 2" "1 \<le> a" "2 * a < p"
  shows "vge p (\<Sum> v = a..p - a. 1 / of_nat v ^ 5) 1"
proof -
  have p: "prime p" using assms(1) .
  define S where "S = (\<Sum> v = a..p - a. 1 / of_nat v ^ 5 :: rat)"
  have bij: "bij_betw (\<lambda>v. p - v) {a..p - a} {a..p - a}"
    by (rule bij_betw_byWitness[where f' = "\<lambda>v. p - v"]) (use assms(4) in auto)
  have "S = (\<Sum> v = a..p - a. 1 / of_nat (p - v) ^ 5 :: rat)"
    unfolding S_def using sum.reindex_bij_betw[OF bij, of "\<lambda>v. 1 / of_nat v ^ 5 :: rat"]
      by order
  hence two: "2 * S = (\<Sum> v = a..p - a. 1 / of_nat v ^ 5 + 1 / of_nat (p - v) ^ 5 :: rat)"
    unfolding S_def by fastforce
  have n2: "\<not> p dvd 2" using p assms(2) prime_ge_2_nat[OF p] dvd_imp_le[of p 2] by auto
  have trm: "vge p (1 / of_nat v ^ 5 + 1 / of_nat (p - v) ^ 5 :: rat) 1" if v: "v \<in> {a..p - a}"
    for v
  proof -
    have v1: "1 \<le> v" "v < p" using v assms(3,4) by auto
    have "\<not> p dvd v" using v1 by force
    moreover have "\<not> p dvd (p - v)" using v1 dvd_imp_le[of p "p - v"] by linarith
    ultimately have nvw: "\<not> p dvd (v * (p - v)) ^ 5"
      using p prime_dvd_power prime_dvd_mult_iff by blast
    define x where "x = (of_nat v :: rat)"
    define y where "y = (of_nat (p - v) :: rat)"
    have xy: "x + y = of_nat p" unfolding x_def y_def using v1 by simp
    have x0: "x \<noteq> 0" and y0: "y \<noteq> 0" unfolding x_def y_def using v1 by auto
    have fac: "x ^ 5 + y ^ 5 = (x + y) * (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4)"
      by (auto simp: algebra_simps eval_nat_numeral)
    have q: "x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 =
        of_int (int v ^ 4 - int v ^ 3 * int (p - v) + int v ^ 2 * int (p - v) ^ 2 - int v * int (p -
          v) ^ 3 + int (p - v) ^ 4)"
      unfolding x_def y_def by force
    have e: "1 / x ^ 5 + 1 / y ^ 5 = (x ^ 5 + y ^ 5) * inverse (of_nat ((v * (p - v)) ^ 5))"
      unfolding x_def y_def using x0 y0 unfolding x_def y_def
        by (auto simp: field_simps power_mult_distrib)
    have numv: "vge p (x ^ 5 + y ^ 5) 1"
    proof -
      have "vge p (of_nat p * of_int (int v ^ 4 - int v ^ 3 * int (p - v) + int v ^ 2 * int (p -
        v) ^ 2 - int v * int (p - v) ^ 3 + int (p - v) ^ 4)) (1 + 0)"
        by (rule vge_mul[OF p vge_p_self[OF p] vge_of_int[OF p]])
      thus ?thesis unfolding fac xy[symmetric] q by auto
    qed
    have "vge p ((x ^ 5 + y ^ 5) * inverse (of_nat ((v * (p - v)) ^ 5))) (1 + 0)"
      by (rule vge_mul[OF p numv vge_inverse_unit[OF p nvw]])
    thus ?thesis using e unfolding x_def y_def by algebra
  qed
  have "vge p (2 * S) 1" unfolding two by (rule vge_sum[OF p]) (use trm in auto)
  hence "vge p (inverse (of_nat 2) * (2 * S)) (0 + 1)"
    by (rule vge_mul[OF p vge_inverse_unit[OF p n2]])
  thus ?thesis unfolding S_def by fastforce
qed

text \<open>The constant term of @{text "mu_X(1/(t+j^2))"}.\<close>
definition c0 :: "nat \<Rightarrow> rat" where "c0 j =
  - (of_nat j ^ 4 * H5 j) - 1 / 4 + 1 / (2 * of_nat j)"

lemma muPole_eq: "muPole j = [:c0 j, of_nat j ^ 4:]"
  unfolding muPole_def c0_def pX_minus_const by simp

lemma muPole_coeff: "Polynomial.coeff (muPole j) n = (if n = 1 then of_nat j ^ 4 else
  if n = 0 then c0 j else 0)"
  by (auto simp: muPole_eq coeff_pCons split: nat.split)

lemma H5_split: "1 \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow>
  H5 b = H5 (a - 1) + (\<Sum> v = a..b. 1 / of_nat v ^ 5)"
proof -
  assume a1: "1 \<le> a" and ab: "a \<le> b"
  have u: "{1..b} = {1..a - 1} \<union> {a..b}" using a1 ab by auto
  show ?thesis unfolding H5_def u by (rule sum.union_disjoint) auto
qed

text \<open>The two-node congruence @{text "mu_X(1/(t+a^2)) \<equiv> mu_X(1/(t+(p-a)^2)) (mod p)"}
  coefficientwise.\<close>
lemma pole_congr:
  assumes "prime p" "p \<noteq> 2" "1 \<le> a" "2 * a < p"
  shows "vge p (Polynomial.coeff (muPole a) n - Polynomial.coeff (muPole (p - a)) n) 1"
proof -
  have p: "prime p" using assms(1) .
  define b where "b = p - a"
  have ab: "a \<le> b" "a + b = p" "1 \<le> b" "b < p" "a < p" using assms(3,4) unfolding b_def
    by auto
  have pb: "(of_nat p :: rat) = of_nat a + of_nat b" using ab(2) by force
  have d4: "(of_nat b ^ 4 - of_nat a ^ 4 :: rat) =
    of_nat p * of_int ((int b - int a) * (int b ^ 2 + int a ^ 2))"
    using pb by (auto simp: algebra_simps eval_nat_numeral)
  have "vge p (Polynomial.coeff (muPole a) n - Polynomial.coeff (muPole b) n) 1"
  proof (cases "n = 1")
    case True
    have e: "Polynomial.coeff (muPole a) n - Polynomial.coeff (muPole b) n =
      - (of_nat b ^ 4 - of_nat a ^ 4)"
      using True unfolding muPole_coeff by fastforce
    have "vge p (of_nat p * of_int ((int b - int a) * (int b ^ 2 + int a ^ 2))) (1 + 0)"
      by (rule vge_mul[OF p vge_p_self[OF p] vge_of_int[OF p]])
    hence "vge p (of_nat b ^ 4 - of_nat a ^ 4) 1" using d4 by fastforce
    thus ?thesis unfolding e by (rule vge_neg)
  next
    case n1: False
    show ?thesis
    proof (cases "n = 0")
      case True
      have e: "Polynomial.coeff (muPole a) n - Polynomial.coeff (muPole b) n = c0 a - c0 b"
        using True unfolding muPole_coeff by fastforce
      define S where "S = (\<Sum> v = a..b. 1 / of_nat v ^ 5 :: rat)"
      define H where "H = H5 (a - 1)"
      have hb: "H5 b = H + S" unfolding H_def S_def using H5_split[of a b] ab assms(3) by fastforce
      have ha: "H5 a = H + 1 / of_nat a ^ 5" unfolding H_def using H5_split[of a a] assms(3)
        by fastforce
      have a0: "(of_nat a :: rat) \<noteq> 0" and b0: "(of_nat b :: rat) \<noteq> 0"
        using ab assms(3) by auto
      have ce: "c0 a - c0 b = (of_nat b ^ 4 - of_nat a ^ 4) * H + of_nat b ^ 4 * S - of_nat p *
        inverse (of_nat (2 * a * b))"
      proof -
        have i: "of_nat p * inverse (of_nat (2 * a * b)) =
          1 / (2 * of_nat a) + 1 / (2 * (of_nat b :: rat))"
          using pb a0 b0 by (fastforce simp: field_simps)
        have j: "of_nat a ^ 4 * (1 / of_nat a ^ 5) = 1 / (of_nat a :: rat)" using a0
          by (force simp: eval_nat_numeral)
        show ?thesis unfolding c0_def ha hb i using j by (simp add: algebra_simps)
      qed
      have hv: "vge p H 0" unfolding H_def using vge_H5_small[OF p] ab by auto
      have v1: "vge p ((of_nat b ^ 4 - of_nat a ^ 4) * H) 1"
      proof -
        have "vge p (of_nat p * of_int ((int b - int a) * (int b ^ 2 + int a ^ 2))) (1 + 0)"
          by (rule vge_mul[OF p vge_p_self[OF p] vge_of_int[OF p]])
        hence "vge p (of_nat b ^ 4 - of_nat a ^ 4) 1" using d4 by force
        from vge_mul[OF p this hv] show ?thesis by simp
      qed
      have sv: "vge p S 1" unfolding S_def b_def by (rule pair_sum_vge[OF assms])
      have v2: "vge p (of_nat b ^ 4 * S) 1" using vge_mul[OF p vge_pow[OF p vge_of_nat[OF p]] sv]
        by force
      have "\<not> p dvd 2" using p assms(2) prime_ge_2_nat[OF p] dvd_imp_le[of p 2] by force
      moreover have "\<not> p dvd a" using ab assms(3) dvd_imp_le[of p a] by linarith
      moreover have "\<not> p dvd b" using ab dvd_imp_le[of p b] by linarith
      ultimately have nd: "\<not> p dvd 2 * a * b" using prime_dvd_mult_iff[OF p] by presburger
      have v3: "vge p (of_nat p * inverse (of_nat (2 * a * b))) 1"
        using vge_mul[OF p vge_p_self[OF p] vge_inverse_unit[OF p nd]] by fastforce
      show ?thesis unfolding e ce by (rule vge_diff[OF p vge_add[OF p v1 v2] v3])
    next
      case False
      have e: "Polynomial.coeff (muPole a) n - Polynomial.coeff (muPole b) n = 0"
        using n1 False unfolding muPole_coeff by algebra
      show ?thesis unfolding e by (rule vge_zero)
    qed
  qed
  thus ?thesis unfolding b_def .
qed

lemma eval_sub_vge:
  assumes "prime p" "vpGge p R 0" "vge p x 0" "vge p y 0" "vge p (x - y) b"
  shows "vge p (poly R x - poly R y) b"
proof -
  have p: "prime p" and R: "vpGge p R 0" and x: "vge p x 0" and y: "vge p y 0" and xy: "vge p (x -
    y) b" using assms .
  have e: "poly R x - poly R y = (\<Sum> i \<le> degree R. Polynomial.coeff R i * (x ^ i - y ^ i))"
    by (simp add: poly_altdef sum_subtractf right_diff_distrib)
  show ?thesis unfolding e
  proof (rule vge_sum[OF p])
    fix i
    have s: "vge p (\<Sum> k < i. y ^ (i - Suc k) * x ^ k) 0"
    proof (rule vge_sum[OF p])
      fix k
      show "vge p (y ^ (i - Suc k) * x ^ k) 0" using vge_mul[OF p vge_pow[OF p y] vge_pow[OF p x]]
        by simp
    qed simp
    have "vge p (Polynomial.coeff R i * ((x - y) * (\<Sum> k <
      i. y ^ (i - Suc k) * x ^ k))) (0 + (b + 0))"
      by (rule vge_mul[OF p R[unfolded vpGge_iff, rule_format] vge_mul[OF p xy s]])
    thus "vge p (Polynomial.coeff R i * (x ^ i - y ^ i)) b" unfolding power_diff_sumr2 by simp
  qed simp
qed

text \<open>The divided difference at the two nodes @{text a}, @{text "p - a"} is integral.\<close>
lemma two_pole_vge:
  assumes p: "prime p" and p7: "7 \<le> p" and a1: "1 \<le> a" and a2: "2 * a <
    p" and R: "vpGge p R 0"
  shows "vpGge p (muXmod p {a, p - a} R) 0"
proof -
  define b where "b = p - a"
  have ab: "a \<noteq> b" using a2 by (simp add: b_def)
  have p2: "p \<noteq> 2" using p7 by simp
  define d where "d = (of_nat b ^ 2 - of_nat a ^ 2 :: rat)"
  have d0: "d \<noteq> 0" using ab by (simp add: d_def power2_eq_iff)
  have dv: "of_int (vp p d) \<le> (1 :: rat)"
  proof -
    have ba: "a < b" "b + a = p" using a2 by (simp_all add: b_def)
    have e: "d = of_nat (b - a) * of_nat p"
    proof -
      have "d = (of_nat b - of_nat a) * (of_nat b + of_nat a)"
        by (simp add: d_def power2_eq_square algebra_simps)
      also have "of_nat b + of_nat a = (of_nat p :: rat)" by (metis ba(2) of_nat_add)
      also have "of_nat b - of_nat a = (of_nat (b - a) :: rat)" using ba(1)
        by (simp add: of_nat_diff)
      finally show ?thesis .
    qed
    have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer prime_imp_prime_elem)
    have g0: "0 < b - a" and gp: "b - a < p" using ba a1 by (auto simp: b_def)
    have nd: "\<not> p dvd (b - a)"
    proof
      assume "p dvd b - a"
      hence "p \<le> b - a" by (rule dvd_imp_le) (rule g0)
      thus False using gp by simp
    qed
    have v1: "vp p (of_nat (b - a)) = 0" unfolding vp_def qmultiplicity_of_nat multiplicity_int
      using not_dvd_imp_multiplicity_0[OF nd] by simp
    have v2: "vp p (of_nat p) = 1" unfolding vp_def qmultiplicity_of_nat multiplicity_int
      using prime_multiplicity_prime[OF p p] by simp
    have "vp p d = vp p (of_nat (b - a)) + vp p (of_nat p)"
      unfolding e vp_def by (rule qmultiplicity_mult[OF pe]) (use g0 prime_gt_0_nat[OF p] in
        simp_all)
    thus ?thesis using v1 v2 by simp
  qed
  have res: "muXmod p {a, b} R = [:muModPoly p (R div sqPoleProd {a, b}):] +
      [:poly R (- (of_nat a ^ 2)) / d:] * muPole a + [:poly R (- (of_nat b ^ 2)) / (- d):] *
        muPole b"
    using ab by (simp add: muXmod_eq sqResidue_def d_def insert_Diff_if add.assoc)
  have c: "vge p (muModPoly p (R div sqPoleProd {a, b})) 0"
    by (rule muModPoly_vge[OF p p7 vpGge_div_monic[OF p R lead_coeff_sqPoleProd vpGge_sqPoleProd[OF
      p]]]) simp
  have cf: "\<And>n. vge p (poly R (- (of_nat a ^ 2)) / d * Polynomial.coeff (muPole a) n +
    poly R (- (of_nat b ^ 2)) / (- d) * Polynomial.coeff (muPole b) n) 0"
  proof -
    fix n
    have x: "vge p (poly R (- (of_nat a ^ 2))) 0" by (rule eval_vge0[OF p R vge_neg_sq[OF p]])
    have xy: "vge p (poly R (- (of_nat a ^ 2)) - poly R (- (of_nat b ^ 2))) 1"
    proof -
      have ba: "a < b" "b + a = p" using a2 by (simp_all add: b_def)
      have e: "d = of_nat (b - a) * of_nat p"
      proof -
        have "d = (of_nat b - of_nat a) * (of_nat b + of_nat a)"
          by (simp add: d_def power2_eq_square algebra_simps)
        also have "of_nat b + of_nat a = (of_nat p :: rat)" by (metis ba(2) of_nat_add)
        also have "of_nat b - of_nat a = (of_nat (b - a) :: rat)" using ba(1)
          by (simp add: of_nat_diff)
        finally show ?thesis .
      qed
      have "vge p (of_nat (b - a) * of_nat p) (0 + 1)"
        by (rule vge_mul[OF p vge_of_nat[OF p] vge_p_self[OF p]])
      hence dd: "vge p d 1" by (simp add: e)
      have "- (of_nat a ^ 2) - - (of_nat b ^ 2) = d" by (simp add: d_def)
      hence "vge p (- (of_nat a ^ 2) - - (of_nat b ^ 2)) 1" using dd by simp
      thus ?thesis by (rule eval_sub_vge[OF p R vge_neg_sq[OF p] vge_neg_sq[OF p]])
    qed
    have "vge p (Polynomial.coeff (muPole a) n) 0" and yb: "vge p (Polynomial.coeff (muPole b) n) 0"
      using muPole_vge_small[OF p a1 _ p2] muPole_vge_small[OF p _ _ p2, of b] a1 a2
        by (auto simp: vpGge_iff b_def)
    have yy: "vge p (Polynomial.coeff (muPole a) n - Polynomial.coeff (muPole b) n) 1"
      unfolding b_def by (rule pole_congr[OF p p2 a1 a2])
    have num: "vge p (poly R (- (of_nat a ^ 2)) * Polynomial.coeff (muPole a) n -
      poly R (- (of_nat b ^ 2)) * Polynomial.coeff (muPole b) n) 1"
    proof -
      have eq: "poly R (- (of_nat a ^ 2)) * Polynomial.coeff (muPole a) n -
        poly R (- (of_nat b ^ 2)) * Polynomial.coeff (muPole b) n =
          poly R (- (of_nat a ^ 2)) * (Polynomial.coeff (muPole a) n -
            Polynomial.coeff (muPole b) n) +
          (poly R (- (of_nat a ^ 2)) - poly R (- (of_nat b ^ 2))) * Polynomial.coeff (muPole b) n"
            by (simp add: algebra_simps)
      have A: "vge p (poly R (- (of_nat a ^ 2)) * (Polynomial.coeff (muPole a) n -
        Polynomial.coeff (muPole b) n)) 1"
        using vge_mul[OF p x yy] by simp
      have B: "vge p ((poly R (- (of_nat a ^ 2)) - poly R (- (of_nat b ^ 2))) *
        Polynomial.coeff (muPole b) n) 1"
        using vge_mul[OF p xy yb] by simp
      show ?thesis unfolding eq by (rule vge_add[OF p A B])
    qed
    have e: "poly R (- (of_nat a ^ 2)) / d * Polynomial.coeff (muPole a) n +
      poly R (- (of_nat b ^ 2)) / (- d) * Polynomial.coeff (muPole b) n =
             (poly R (- (of_nat a ^ 2)) * Polynomial.coeff (muPole a) n -
               poly R (- (of_nat b ^ 2)) * Polynomial.coeff (muPole b) n) / d"
      using d0 by (simp add: field_simps)
    show "vge p (poly R (- (of_nat a ^ 2)) / d * Polynomial.coeff (muPole a) n +
      poly R (- (of_nat b ^ 2)) / (- d) * Polynomial.coeff (muPole b) n) 0"
      unfolding e using vge_div_of_le[OF p num d0 dv] by simp
  qed
  show ?thesis unfolding b_def[symmetric] res
    unfolding vpGge_iff
  proof
    fix n
    have "vge p (Polynomial.coeff [:muModPoly p (R div sqPoleProd {a, b}):] n +
        (poly R (- (of_nat a ^ 2)) / d * Polynomial.coeff (muPole a) n + poly R (- (of_nat b ^ 2)) /
          (- d) * Polynomial.coeff (muPole b) n)) 0"
      by (rule vge_add[OF p _ cf]) (simp add: coeff_pCons c vge_zero split: nat.split)
    thus "vge p (Polynomial.coeff ([:muModPoly p (R div sqPoleProd {a,
      b}):] + [:poly R (- (of_nat a ^ 2)) / d:] * muPole a +
        [:poly R (- (of_nat b ^ 2)) / (- d):] * muPole b) n) 0" by (simp add: algebra_simps)
  qed
qed

text \<open>(4.12), rows @{text "i \<ge> l - 2"}: once @{text "E_a"} is a factor,
  the entry is integral.\<close>
lemma entry_large:
  assumes p: "prime p" and H: "OuterHyp K p" and a1: "1 \<le> a" and am: "a \<le>
    mHalf p" and R: "vpGge p R 0"
  shows "vpGge p (muXmod p (outerClassPoles K p a) (R * sqPoleProd {j \<in>
    outerClassPoles K p a. p < j})) 0"
proof -
  have p7: "7 \<le> p" using H by (simp add: OuterHyp_def)
  have split: "{j \<in> outerClassPoles K p a. p < j} \<union> {j \<in> outerClassPoles K p a. j <
    p} = outerClassPoles K p a"
  proof -
    have "j \<noteq> p" if "j \<in> outerClassPoles K p a" for j
      using class_not_dvd[OF p H a1 am that] by auto
    hence "p < j \<or> j < p" if "j \<in> outerClassPoles K p a" for j using that
      by (meson linorder_neqE_nat)
    thus ?thesis by auto
  qed
  have cancel: "muXmod p (outerClassPoles K p a) (R * sqPoleProd {j \<in> outerClassPoles K p a. p <
    j}) = muXmod p {j \<in> outerClassPoles K p a. j < p} R"
  proof -
    have fin: "finite {j \<in> outerClassPoles K p a. P j}" for P
      by (rule finite_subset[of _ "{Nof K + 1..K}"]) (auto simp: outerClassPoles_def)
    have "muXmod p ({j \<in> outerClassPoles K p a. p < j} \<union> {j \<in>
      outerClassPoles K p a. j < p})
        (R * sqPoleProd {j \<in> outerClassPoles K p a. p < j}) = muXmod p {j \<in>
          outerClassPoles K p a. j < p} R"
      by (rule muXmod_mul_cancel_set[OF fin fin]) auto
    thus ?thesis unfolding split .
  qed
  show ?thesis unfolding cancel small_poles[OF p H a1 am]
  proof (cases "a \<le> Nof K")
    case True
    obtain m: "2 * mHalf p + 1 = p" using outer_facts[OF p H] by blast
    have b1: "1 \<le> p - a" and bp: "p - a < p" and p2: "p \<noteq> 2" using m am a1 p7 by auto
    show "vpGge p (muXmod p (if a \<le> Nof K then {p - a} else {a, p - a}) R) 0"
      unfolding if_P[OF True]
    proof (rule muXmod_vge_of_residues[OF p p7 _ R order.refl])
      show "finite {p - a}" by simp
      fix j assume "j \<in> {p - a}"
      hence j: "j = p - a" by simp
      have "vge p (sqResidue {p - a} R (p - a)) 0"
        unfolding sqResidue_def by (simp add: eval_vge0[OF p R vge_neg_sq[OF p]])
      from vpGge_mul[OF p vpGge_C[OF this] muPole_vge_small[OF p b1 bp p2]]
      show "vpGge p ([:sqResidue {p - a} R j:] * muPole j) 0" unfolding j by simp
    qed
  next
    case False
    obtain m: "2 * mHalf p + 1 = p" using outer_facts[OF p H] by blast
    hence a2: "2 * a < p" using am by linarith
    show "vpGge p (muXmod p (if a \<le> Nof K then {p - a} else {a, p - a}) R) 0"
      unfolding if_not_P[OF False]
      by (rule two_pole_vge[OF p p7 a1 a2 R])
  qed
qed


subsection \<open>The zero class\<close>

lemma vp_three_sq: "prime p \<Longrightarrow> 7 \<le> p \<Longrightarrow>
  vp p (3 * of_nat p ^ 2) \<le> 2"
proof -
  assume p: "prime p" and p7: "7 \<le> p"
  have pe: "prime_elem (int p)" using p by (simp add: prime_nat_int_transfer prime_imp_prime_elem)
  have n3: "\<not> p dvd 3" using p7 by (auto dest: dvd_imp_le)
  have m3: "multiplicity p (3::nat) = 0" by (rule not_dvd_imp_multiplicity_0[OF n3])
  have "vp p (of_nat 3) = 0" unfolding vp_def qmultiplicity_of_nat multiplicity_int m3 by simp
  hence v3: "vp p (3 :: rat) = 0" by simp
  have "vp p (of_nat p) = 1" unfolding vp_def qmultiplicity_of_nat multiplicity_int
    using prime_multiplicity_prime[OF p p] by simp
  hence vp1: "vp p (of_nat p :: rat) = 1" .
  have p0: "(of_nat p :: rat) \<noteq> 0" using p by (simp add: prime_gt_0_nat)
  have "vp p (3 * of_nat p ^ 2 :: rat) = vp p (3 :: rat) + vp p (of_nat p ^ 2 :: rat)"
    unfolding vp_def by (rule qmultiplicity_mult[OF pe]) (simp_all add: p0 prime_gt_0_nat[OF p])
  also have "vp p (of_nat p ^ 2 :: rat) = 2" by (simp add: vp_power_rat[OF p p0] vp1)
  finally show ?thesis using v3 by simp
qed

text \<open>The zero class with a single pole @{text p}.\<close>
lemma entry_zero_one:
  assumes "prime p" "OuterHyp K p" "K < 2 * p" "vpGge p R 0"
  shows "vpGge p (muXmod p (outerClassPoles K p 0) R) (- 1)"
proof -
  have p: "prime p" and p7: "7 \<le> p" using assms(1,2) by (simp_all add: OuterHyp_def)
  have C: "outerClassPoles K p 0 = {p}" using zero_class[OF assms(1,2)] assms(3) by simp
  show ?thesis unfolding C
  proof (rule muXmod_vge_of_residues[OF p p7 _ assms(4)])
    show "finite {p}" by simp
    show "(- 1 :: rat) \<le> 0" by simp
    fix j assume "j \<in> {p}"
    hence j: "j = p" by simp
    have "vge p (sqResidue {p} R p) 0"
      unfolding sqResidue_def by (simp add: eval_vge0[OF p assms(4) vge_neg_sq[OF p]])
    from vpGge_mul[OF p vpGge_C[OF this] muPole_vge_mult[OF p p7, of 1]]
    show "vpGge p ([:sqResidue {p} R j:] * muPole j) (- 1)" unfolding j by simp
  qed
qed

text \<open>The zero class with two poles @{text "p, 2p"}.\<close>
lemma entry_zero_two:
  assumes "prime p" "OuterHyp K p" "2 * p \<le> K" "vpGge p A 0"
  shows "vpGge p (muXmod p (outerClassPoles K p 0) (A * (pX + [:of_nat p ^ 2:]) ^ i * (pX +
    [:of_nat p ^ 2:]) ^ i'))
           (min 0 (2 * (of_nat i + of_nat i') - 3))"
proof -
  have p: "prime p" using assms(1) .
  have p7: "7 \<le> p" using assms(2) by (simp add: OuterHyp_def)
  have C: "outerClassPoles K p 0 = {p, 2 * p}" using zero_class[OF assms(1,2)] assms(3) by simp
  have Yi: "vpGge p ((pX + [:of_nat p ^ 2:]) ^ n) 0" for n
    by (rule vpGge_pow0[OF p vpGge_pX_plus_sq[OF p]])
  have R0: "vpGge p (A * (pX + [:of_nat p ^ 2:]) ^ i * (pX + [:of_nat p ^ 2:]) ^ i') 0"
    by (rule vpGge_mul0[OF p vpGge_mul0[OF p assms(4) Yi] Yi])
  have ev: "poly (pX + [:of_nat p ^ 2:]) (- (of_nat (t * p) ^ 2)) =
    (of_nat p ^ 2 * of_int (1 - int t ^ 2) :: rat)" for t
    by (simp add: poly_monom algebra_simps power_mult_distrib)
  have v2: "vge p (of_nat p ^ 2 * of_int z) 2" for z :: int
    using vge_mul[OF p vge_pow_mul[OF p vge_p_self[OF p], of 2] vge_of_int[OF p, of z]] by simp
  have key: "vpGge p ([:sqResidue {p, 2 * p} (A * (pX + [:of_nat p ^ 2:]) ^ i * (pX +
    [:of_nat p ^ 2:]) ^ i') (t * p):] * muPole (t * p))
      (min 0 (2 * (of_nat i + of_nat i') - 3))" if t: "t = 1 \<or> t = 2" for t
  proof -
    have x: "vge p (- (of_nat (t * p) ^ 2)) 0" by (rule vge_neg_sq[OF p])
    have Yv: "vge p (poly (pX + [:of_nat p ^ 2:]) (- (of_nat (t * p) ^ 2))) 2" unfolding ev
      by (rule v2)
    have num: "vge p (poly (A * (pX + [:of_nat p ^ 2:]) ^ i * (pX +
      [:of_nat p ^ 2:]) ^ i') (- (of_nat (t * p) ^ 2)))
        (0 + of_nat i * 2 + of_nat i' * 2)"
      unfolding poly_mult poly_power
      by (rule vge_mul[OF p vge_mul[OF p eval_vge0[OF p assms(4) x] vge_pow_mul[OF p Yv]]
        vge_pow_mul[OF p Yv]])
    define D where "D = (\<Prod> k \<in>
      {p, 2 * p} - {t * p}. of_nat k ^ 2 - of_nat (t * p) ^ 2 :: rat)"
    have S: "{p, 2 * p} - {t * p} = (if t = 1 then {2 * p} else {p})" using t p7 by auto
    have D: "D = 3 * of_nat p ^ 2 \<or> D = - (3 * of_nat p ^ 2)"
      unfolding D_def S using t by (auto simp: algebra_simps power2_eq_square)
    have D0: "D \<noteq> 0" using D p7 by auto
    have Dv: "of_int (vp p D) \<le> (2 :: rat)"
      using D vp_three_sq[OF p p7] by (auto simp: vp_def qmultiplicity_minus)
    have r: "vge p (sqResidue {p, 2 * p} (A * (pX + [:of_nat p ^ 2:]) ^ i * (pX +
      [:of_nat p ^ 2:]) ^ i') (t * p))
        (0 + of_nat i * 2 + of_nat i' * 2 - 2)"
      unfolding sqResidue_def D_def[symmetric] by (rule vge_div_of_le[OF p num D0 Dv])
    have "vpGge p ([:sqResidue {p, 2 * p} (A * (pX + [:of_nat p ^ 2:]) ^ i * (pX +
      [:of_nat p ^ 2:]) ^ i') (t * p):] * muPole (t * p))
        ((0 + of_nat i * 2 + of_nat i' * 2 - 2) + - 1)"
      by (rule vpGge_mul[OF p vpGge_C[OF r] muPole_vge_mult[OF p p7]]) (use t in auto)
    moreover have "min 0 (2 * (of_nat i + of_nat i') - 3) \<le>
      (0 + of_nat i * 2 + of_nat i' * 2 - 2 + - 1 :: rat)"
      by (simp add: min_def)
    ultimately show ?thesis by (rule vpGge_mono)
  qed
  show ?thesis unfolding C
  proof (rule muXmod_vge_of_residues[OF p p7 _ R0 min.cobounded1])
    show "finite {p, 2 * p}" by simp
    fix j assume "j \<in> {p, 2 * p}"
    hence "j = 1 * p \<or> j = 2 * p" by auto
    thus "vpGge p ([:sqResidue {p, 2 * p} (A * (pX + [:of_nat p ^ 2:]) ^ i * (pX +
      [:of_nat p ^ 2:]) ^ i') j:] * muPole j)
        (min 0 (2 * (of_nat i + of_nat i') - 3))" using key[of 1] key[of 2] by auto
  qed
qed

subsection \<open>The entry bound (4.12)\<close>

lemma min_add_le_min: "min 0 A + min 0 B \<le> min 0 (A + B)" for A B :: rat
  by (simp add: min_def)

text \<open>The cancellation behind a same-class entry.\<close>
lemma same_class_cancel:
  assumes "finite Ca" "Ca \<subseteq> tailPoles K"
  shows "muXmod p {1..K} (Dm (Nof K) ^ 6 * (sqPoleProd (tailPoles K - Ca) * A) *
    (sqPoleProd (tailPoles K - Ca) * B)) =
         muXmod p Ca (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - Ca) * A * B)"
proof -
  define T where "T = {1..Nof K} \<union> (tailPoles K - Ca)"
  have "Nof K \<le> K" by (simp add: Nof_def)
  with assms(2) have u: "{1..K} = T \<union> Ca" by (auto simp: T_def tailPoles_def)
  have fT: "finite T" by (simp add: T_def tailPoles_def)
  have dTC: "T \<inter> Ca = {}" using assms(2) by (auto simp: T_def tailPoles_def)
  have sT: "sqPoleProd T = Dm (Nof K) * sqPoleProd (tailPoles K - Ca)"
    unfolding T_def by (subst sqPoleProd_union) (auto simp: tailPoles_def Dm_def sqPoleProd_def)
  have d6: "Dm (Nof K) ^ 6 = Dm (Nof K) ^ 5 * Dm (Nof K)" using power_Suc2[of "Dm (Nof K)" 5]
    by simp
  have n: "Dm (Nof K) ^ 6 * (sqPoleProd (tailPoles K - Ca) * A) * (sqPoleProd (tailPoles K - Ca) *
    B) =
      (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - Ca) * A * B) * sqPoleProd T"
    unfolding sT d6 by (simp add: mult_ac)
  show ?thesis unfolding u n by (rule muXmod_mul_cancel_set[OF fT assms(1) dTC])
qed

text \<open>The cancellation behind a cross-class entry.\<close>
lemma cross_class_cancel:
  assumes "finite Ca" "finite Cc" "Ca \<inter> Cc = {}" "Ca \<subseteq> tailPoles K" "Cc \<subseteq>
    tailPoles K"
  shows "muXmod p {1..K} (Dm (Nof K) ^ 6 * (sqPoleProd (tailPoles K - Ca) * A) *
    (sqPoleProd (tailPoles K - Cc) * B)) =
         [:muModPoly p (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - (Ca \<union> Cc)) * A * B):]"
proof -
  define g where "g = (\<lambda>j. pX + [:of_nat j ^ 2:] :: rat poly)"
  have ft: "finite (tailPoles K - X)" for X by (simp add: tailPoles_def)
  have U: "(tailPoles K - Ca) \<union> (tailPoles K - Cc) = tailPoles K" using assms(3) by auto
  have I: "(tailPoles K - Ca) \<inter> (tailPoles K - Cc) = tailPoles K - (Ca \<union> Cc)" by auto
  have ui: "sqPoleProd (tailPoles K - Ca) * sqPoleProd (tailPoles K - Cc) =
      sqPoleProd (tailPoles K) * sqPoleProd (tailPoles K - (Ca \<union> Cc))"
  proof -
    have sg: "sqPoleProd S = prod g S" for S by (simp add: sqPoleProd_def g_def)
    have "prod g ((tailPoles K - Ca) \<union> (tailPoles K - Cc)) * prod g ((tailPoles K -
      Ca) \<inter> (tailPoles K - Cc)) =
        prod g (tailPoles K - Ca) * prod g (tailPoles K - Cc)" by (rule prod.union_inter[OF ft ft])
    thus ?thesis unfolding sg U I by (rule sym)
  qed
  have d6: "Dm (Nof K) ^ 6 = Dm (Nof K) ^ 5 * Dm (Nof K)" using power_Suc2[of "Dm (Nof K)" 5]
    by simp
  define X where "X = Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - (Ca \<union> Cc)) * A * B"
  have "Dm (Nof K) ^ 6 * (sqPoleProd (tailPoles K - Ca) * A) * (sqPoleProd (tailPoles K - Cc) * B) =
      Dm (Nof K) ^ 5 * Dm (Nof K) * (sqPoleProd (tailPoles K - Ca) * sqPoleProd (tailPoles K -
        Cc)) * A * B"
    unfolding d6 by (simp add: mult_ac)
  also have "\<dots> = Dm (Nof K) ^ 5 * Dm (Nof K) * (sqPoleProd (tailPoles K) *
    sqPoleProd (tailPoles K - (Ca \<union> Cc))) * A * B"
    by (simp only: ui)
  also have "\<dots> = X * (Dm (Nof K) * sqPoleProd (tailPoles K))" by (simp add: X_def mult_ac)
  also have "\<dots> = X * sqPoleProd {1..K}" by (simp only: sqPoleProd_Icc_split)
  finally have n: "Dm (Nof K) ^ 6 * (sqPoleProd (tailPoles K - Ca) * A) * (sqPoleProd (tailPoles K -
    Cc) * B) = X * sqPoleProd {1..K}" .
  have "muXmod p ({1..K} \<union> {}) (X * sqPoleProd {1..K}) = muXmod p {} X"
    by (rule muXmod_mul_cancel_set) simp_all
  thus ?thesis unfolding n X_def[symmetric] by (simp add: muXmod_empty)
qed

text \<open>(4.12) and the zero-class weights: entries of @{text A} in the outer basis satisfy the
  weights.
  The longest Lean file of the proof (OuterEntries.lean, 1,045 lines): cross-class, ordinary and
  @{text "E_a"} rows, the two-node congruence @{text "H_{p-a} \<equiv> H_{a-1} (mod p)"},
    the zero class.\<close>
theorem outerGram_entry_bound:
  assumes p: "prime p" and K: "40 dvd K" and H: "OuterHyp K p" and x: "x <
    length (outer_idx K p)" and y: "y < length (outer_idx K p)"
  shows "vpGge p (outerGram K p $$ (x, y)) (wOut K p (outer_idx K p ! x) +
    wOut K p (outer_idx K p ! y))"
proof -
  define ix where "ix = outer_idx K p ! x"
  define iy where "iy = outer_idx K p ! y"
  define a where "a = fst ix"
  define c where "c = fst iy"
  have p7: "7 \<le> p" using H by (simp add: OuterHyp_def)
  have ixs: "ix \<in> set (outer_idx K p)" and iys: "iy \<in> set (outer_idx K p)"
    by (simp_all add: ix_def iy_def x y)
  have am: "a \<le> mHalf p" and xi: "snd ix < outerCount K p a" and cm: "c \<le>
    mHalf p" and yi: "snd iy < outerCount K p c"
    using mem_outer_idx ixs iys by (auto simp: a_def c_def)
  have w0: "wOut K p ix + wOut K p iy \<le> 0" using wOut_nonpos[of K p ix] wOut_nonpos[of K p iy]
    by linarith
  have finC: "\<And>a. finite (outerClassPoles K p a)" and subC: "\<And>a. outerClassPoles K p a
    \<subseteq> tailPoles K"
    by (auto simp: outerClassPoles_def tailPoles_def)
  have entry: "outerGram K p $$ (x, y) =
    muXmod p {1..K} (Dm (Nof K) ^ 6 * (sqPoleProd (tailPoles K - outerClassPoles K p a) *
    oq K p ix) * (sqPoleProd (tailPoles K - outerClassPoles K p c) * oq K p iy))"
    using outerGram_apply[OF x y] outerBasis_eq[of K p ix] outerBasis_eq[of K p iy]
      by (simp add: ix_def iy_def a_def c_def)
  have int0: "vpGge p (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - outerClassPoles K p a)) 0"
    by (intro vpGge_mul0[OF p] vpGge_pow0[OF p] vpGge_Dm[OF p] vpGge_sqPoleProd[OF p])
  show ?thesis
  proof (cases "a = c")
    case False
    \<comment> \<open>cross-class: the entry is a constant polynomial with an integral value\<close>
    have "outerGram K p $$ (x, y) = [:muModPoly p (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K -
      (outerClassPoles K p a \<union> outerClassPoles K p c)) * oq K p ix * oq K p iy):]"
      unfolding entry by (rule cross_class_cancel[OF finC finC class_disjoint[OF p H am cm False]
        subC subC])
    thus ?thesis
      unfolding ix_def[symmetric] iy_def[symmetric]
      using vpGge_mono[OF vpGge_C[OF muModPoly_vge[OF p p7
          vpGge_mul0[OF p vpGge_mul0[OF p vpGge_mul0[OF p vpGge_pow0[OF p vpGge_Dm[OF p]]
            vpGge_sqPoleProd[OF p]] oq_vge[OF p]] oq_vge[OF p]]]] w0]
      by simp
  next
    case True
    \<comment> \<open>same class\<close>
    have same: "outerGram K p $$ (x, y) =
      muXmod p (outerClassPoles K p a) (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K -
      outerClassPoles K p a) * oq K p ix * oq K p iy)"
      unfolding entry True[symmetric] by (rule same_class_cancel[OF finC subC])
    show ?thesis
    proof (cases "a = 0")
      case a0: True
      \<comment> \<open>the zero class\<close>
      have oqx: "oq K p ix = (pX + [:of_nat p ^ 2:]) ^ snd ix" and oqy: "oq K p iy =
        (pX + [:of_nat p ^ 2:]) ^ snd iy"
        using a0 True by (simp_all add: oq_def Let_def a_def c_def)
      have cnt: "outerCount K p 0 = (if 2 * p \<le> K then 2 else 1)"
        using p7 by (simp add: outerCount_def zero_class[OF p H])
      show ?thesis
      proof (cases "2 * p \<le> K")
        case True2: True
        have bnd: "vpGge p (outerGram K p $$ (x,
          y)) (min 0 (2 * (of_nat (snd ix) + of_nat (snd iy)) - 3))"
          unfolding same oqx oqy a0 by (rule entry_zero_two[OF p H True2 int0[unfolded a0]])
        have wx: "wOut K p ix = (if snd ix = 0 then - 2 else 0)" and wy: "wOut K p iy = (if snd iy =
          0 then - 2 else 0)"
          using a0 True cnt True2 by (simp_all add: wOut_def Let_def a_def c_def)
        have "snd ix < 2" "snd iy < 2" using xi yi cnt True2 a0 True by simp_all
        thus ?thesis unfolding ix_def[symmetric] iy_def[symmetric]
          by (intro vpGge_mono[OF bnd]) (auto simp: wx wy)
      next
        case False2: False
        have bnd: "vpGge p (outerGram K p $$ (x, y)) (- 1)"
          unfolding same a0 oqx oqy
          by (rule entry_zero_one[OF p H _ vpGge_mul0[OF p vpGge_mul0[OF p int0[unfolded a0]
            vpGge_pow0[OF p vpGge_pX_plus_sq[OF p]]]
              vpGge_pow0[OF p vpGge_pX_plus_sq[OF p]]]]) (use False2 in simp)
        have wx: "wOut K p ix = - 1 / 2" and wy: "wOut K p iy = - 1 / 2"
          using a0 True cnt False2 by (simp_all add: wOut_def Let_def a_def c_def)
        show ?thesis unfolding ix_def[symmetric] iy_def[symmetric] wx wy
          by (rule vpGge_mono[OF bnd]) simp
      qed
    next
      case a1': False
      \<comment> \<open>an ordinary class\<close>
      have a1: "1 \<le> a" using a1' by simp
      define l where "l = ell p K a"
      show ?thesis
      proof (cases "snd ix < l - 2 \<and> snd iy < l - 2")
        case both: True
        have oqx: "oq K p ix = (pX + [:of_nat a ^ 2:]) ^ snd ix" and oqy: "oq K p iy =
          (pX + [:of_nat a ^ 2:]) ^ snd iy"
          using both a1' True by (simp_all add: oq_def Let_def a_def c_def l_def)
        have bnd: "vpGge p (outerGram K p $$ (x,
          y)) (min 0 (of_nat (snd ix) + of_nat (snd iy) + 6 * dlt K a - of_nat (ell p K a) - 4))"
          unfolding same oqx oqy by (rule entry_ord[OF p H a1 am])
        have wx: "wOut K p ix = min 0 (of_nat (snd ix) + 3 * dlt K a - (of_nat (ell p K a) + 4) /
          2)"
          and wy: "wOut K p iy = min 0 (of_nat (snd iy) + 3 * dlt K a - (of_nat (ell p K a) + 4) /
            2)"
          using both a1' True by (simp_all add: wOut_def Let_def a_def c_def l_def dlt_def)
        show ?thesis unfolding ix_def[symmetric] iy_def[symmetric] wx wy
          by (rule vpGge_mono[OF bnd]) (rule order_trans[OF min_add_le_min],
            simp add: algebra_simps)
      next
        case False
        \<comment> \<open>one of the rows has the factor @{text "E_a"}: the entry is
          integral\<close>
        have "vpGge p (outerGram K p $$ (x, y)) 0"
          unfolding same
        proof -
          define E where "E = sqPoleProd {j \<in> outerClassPoles K p a. p < j}"
          have Q: "vpGge p ((pX + [:of_nat a ^ 2:]) ^ n) 0" for n
            by (rule vpGge_pow0[OF p vpGge_pX_plus_sq[OF p]])
          show "vpGge p (muXmod p (outerClassPoles K p a) (Dm (Nof K) ^ 5 *
            sqPoleProd (tailPoles K - outerClassPoles K p a) * oq K p ix * oq K p iy)) 0"
          proof (cases "snd ix < l - 2")
            case big: False
            have o: "oq K p ix = E * (pX + [:of_nat a ^ 2:]) ^ (snd ix - (l - 2))"
              using big a1' by (simp add: oq_def Let_def E_def l_def a_def)
            have r: "Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - outerClassPoles K p a) * oq K p ix *
              oq K p iy =
                (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - outerClassPoles K p a) * (pX +
                  [:of_nat a ^ 2:]) ^ (snd ix - (l - 2)) * oq K p iy) * E"
              unfolding o by (simp add: mult_ac)
            show ?thesis unfolding r E_def
              by (rule entry_large[OF p H a1 am vpGge_mul0[OF p vpGge_mul0[OF p int0 Q] oq_vge[OF
              p]]])
          next
            case small: True
            hence big: "\<not> snd iy < l - 2" using False by simp
            have o: "oq K p iy = E * (pX + [:of_nat a ^ 2:]) ^ (snd iy - (l - 2))"
              using big a1' True by (simp add: oq_def Let_def E_def l_def c_def)
            have r: "Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - outerClassPoles K p a) * oq K p ix *
              oq K p iy =
                (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - outerClassPoles K p a) * oq K p ix *
                  (pX + [:of_nat a ^ 2:]) ^ (snd iy - (l - 2))) * E"
              unfolding o by (simp add: mult_ac)
            show ?thesis unfolding r E_def
              by (rule entry_large[OF p H a1 am vpGge_mul0[OF p vpGge_mul0[OF p int0 oq_vge[OF p]]
              Q]])
          qed
        qed
        thus ?thesis unfolding ix_def[symmetric] iy_def[symmetric] by (rule vpGge_mono) (rule w0)
      qed
    qed
  qed
qed

subsection \<open>The closed form (4.14) of @{text "\<gamma>_p^out"}\<close>

definition ind :: "bool \<Rightarrow> nat" where "ind P = (if P then 1 else 0)"

lemma ind_le_one: "ind P \<le> 1" by (simp add: ind_def)
lemma ind_True: "P \<Longrightarrow> ind P = 1" by (simp add: ind_def)
lemma ind_False: "\<not> P \<Longrightarrow> ind P = 0" by (simp add: ind_def)
lemma ind_mult: "ind P * ind Q = ind (P \<and> Q)" by (simp add: ind_def)

text \<open>Membership in a class @{text "\<plusminus>a (mod p)"} for @{text "j < 3p"}.\<close>
lemma class_char:
  fixes j a p :: nat
  assumes "1 \<le> a" "a < p" "j < 3 * p"
  shows "(j mod p = a mod p \<or> (j + a) mod p = 0) \<longleftrightarrow>
         (j = a \<or> j = p + a \<or> j = 2 * p + a \<or> j + a = p \<or> j + a = 2 * p \<or>
           j + a = 3 * p)"
proof -
  have p0: "0 < p" using assms by simp
  define r where "r = j mod p"
  define q where "q = j div p"
  have e: "j = q * p + r" by (simp add: q_def r_def)
  have rp: "r < p" using p0 by (simp add: r_def)
  have q3: "q < 3" using assms(3) p0 by (simp add: q_def div_less_iff_less_mult)
  have L: "(j mod p = a mod p \<or> (j + a) mod p = 0) \<longleftrightarrow> (r = a \<or>
    r = p - a)"
    using mod_add_eq_0_iff[of a p j] assms by (simp add: r_def)
  have "q = 0 \<or> q = 1 \<or> q = 2" using q3 by auto
  thus ?thesis unfolding L using e rp assms
  proof (elim disjE)
    assume q: "q = 0"
    have "j = r" using e q by auto
    moreover have "r = p - a \<longleftrightarrow> r + a = p" using assms rp by linarith
    moreover have "r \<noteq> p + a" "r \<noteq> 2 * p + a" "r + a \<noteq> 2 * p" "r + a \<noteq>
      3 * p" using assms rp by auto
    ultimately show "(r = a \<or> r = p - a) = (j = a \<or> j = p + a \<or> j = 2 * p + a \<or>
      j + a = p \<or> j + a = 2 * p \<or> j + a = 3 * p)" by fast
  next
    assume q: "q = 1"
    have "j = p + r" using e q by simp
    moreover have "r = p - a \<longleftrightarrow> r + a = p" using assms rp by linarith
    moreover have "p + r \<noteq> a" "p + r = p + a \<longleftrightarrow>
      r = a" "p + r \<noteq> 2 * p + a" "p + r + a \<noteq> p"
      "p + r + a = 2 * p \<longleftrightarrow> r + a = p" "p + r + a \<noteq> 3 * p" using assms rp
        by auto
    ultimately show "(r = a \<or> r = p - a) = (j = a \<or> j = p + a \<or> j = 2 * p + a \<or>
      j + a = p \<or> j + a = 2 * p \<or> j + a = 3 * p)" by fast
  next
    assume q: "q = 2"
    have "j = 2 * p + r" using e q by simp
    moreover have "r = p - a \<longleftrightarrow> r + a = p" using assms rp by linarith
    moreover have "2 * p + r \<noteq> a" "2 * p + r \<noteq> p + a" "2 * p + r =
      2 * p + a \<longleftrightarrow> r = a" "2 * p + r + a \<noteq> p"
      "2 * p + r + a \<noteq> 2 * p" "2 * p + r + a = 3 * p \<longleftrightarrow> r + a = p"
        using assms rp by auto
    ultimately show "(r = a \<or> r = p - a) = (j = a \<or> j = p + a \<or> j = 2 * p + a \<or>
      j + a = p \<or> j + a = 2 * p \<or> j + a = 3 * p)" by fast
  qed
qed

lemma sum6:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "distinct [x1, x2, x3, x4, x5, x6]"
  shows "(\<Sum> x \<in> {x1, x2, x3, x4, x5, x6}. f x) = f x1 + f x2 + f x3 + f x4 + f x5 + f x6"
  using assms by simp
text \<open>The class @{text "\<plusminus>a"} in @{text "{L..K}"}, as six indicators.\<close>
lemma card_class:
  fixes L K a p :: nat
  assumes "1 \<le> a" "2 * a < p" "K < 3 * p"
  shows "card {j \<in> {L..K}. j mod p = a mod p \<or> (j + a) mod p = 0} =
         ind (L \<le> a \<and> a \<le> K) + ind (L \<le> p - a \<and>
           p - a \<le> K) + ind (L \<le> p + a \<and> p + a \<le> K) +
         ind (L \<le> 2 * p - a \<and> 2 * p - a \<le> K) + ind (L \<le> 2 * p + a \<and>
           2 * p + a \<le> K) + ind (L \<le> 3 * p - a \<and> 3 * p - a \<le> K)"
proof -
  define A where "A = {a, p - a, p + a, 2 * p - a, 2 * p + a, 3 * p - a}"
  have ap: "a < p" using assms(2) by linarith
  have conv: "(j + a = p) = (j = p - a)" "(j + a = 2 * p) = (j = 2 * p - a)" "(j + a = 3 * p) = (j =
    3 * p - a)" for j
    using ap by auto
  have S: "{j \<in> {L..K}. j mod p = a mod p \<or>
    (j + a) mod p = 0} = {j \<in> A. L \<le> j \<and> j \<le> K}"
  proof (intro equalityI subsetI)
    fix j assume j: "j \<in> {j \<in> {L..K}. j mod p = a mod p \<or> (j + a) mod p = 0}"
    have j3: "j < 3 * p" using j assms(3) by auto
    have "j = a \<or> j = p + a \<or> j = 2 * p + a \<or> j + a = p \<or> j + a = 2 * p \<or>
      j + a = 3 * p"
      using class_char[OF assms(1) ap j3] j by force
    thus "j \<in> {j \<in> A. L \<le> j \<and> j \<le> K}" using j conv unfolding A_def by force
  next
    fix j assume j: "j \<in> {j \<in> A. L \<le> j \<and> j \<le> K}"
    have j3: "j < 3 * p" using j assms(1,2,3) unfolding A_def by force
    have "j = a \<or> j = p + a \<or> j = 2 * p + a \<or> j + a = p \<or> j + a = 2 * p \<or>
      j + a = 3 * p"
      using j assms(1,2) conv unfolding A_def by blast
    thus "j \<in> {j \<in> {L..K}. j mod p = a mod p \<or> (j + a) mod p = 0}"
      using class_char[OF assms(1) ap j3] j by force
  qed
  have C: "card {j \<in> A. L \<le> j \<and> j \<le> K} = (\<Sum> x \<in> A. ind (L \<le> x \<and>
    x \<le> K))"
  proof -
    have fA: "finite A" unfolding A_def by simp
    show ?thesis unfolding ind_def
      using sum.inter_filter[OF fA, of "\<lambda>_. 1::nat" "\<lambda>x. L \<le> x \<and>
        x \<le> K"] card_eq_sum[of "{j \<in> A. L \<le> j \<and> j \<le> K}"] by linarith
  qed
  have dist: "a \<noteq> p - a" "a \<noteq> p + a" "a \<noteq> 2 * p - a" "a \<noteq>
    2 * p + a" "a \<noteq> 3 * p - a"
    "p - a \<noteq> p + a" "p - a \<noteq> 2 * p - a" "p - a \<noteq> 2 * p + a" "p - a \<noteq>
      3 * p - a"
    "p + a \<noteq> 2 * p - a" "p + a \<noteq> 2 * p + a" "p + a \<noteq> 3 * p - a"
    "2 * p - a \<noteq> 2 * p + a" "2 * p - a \<noteq> 3 * p - a" "2 * p + a \<noteq> 3 * p - a"
    using assms(1,2) by auto
  have D: "(\<Sum> x \<in> A. ind (L \<le> x \<and> x \<le> K)) =
      ind (L \<le> a \<and> a \<le> K) + ind (L \<le> p - a \<and>
        p - a \<le> K) + ind (L \<le> p + a \<and> p + a \<le> K) +
      ind (L \<le> 2 * p - a \<and> 2 * p - a \<le> K) + ind (L \<le> 2 * p + a \<and>
        2 * p + a \<le> K) + ind (L \<le> 3 * p - a \<and> 3 * p - a \<le> K)"
    unfolding A_def by (rule sum6) (use dist in simp)
  show ?thesis unfolding S C D ..
qed

lemma ell_eq:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p"
  shows "ell p K a = (if K < 2 * p then 2 else 4) + ind (a \<le> K mod p) + ind (p \<le>
    K mod p + a)"
proof -
  have of: "2 * mHalf p + 1 = p \<and> p \<le> K \<and> K < 3 * p \<and>
    (K < 2 * p \<longrightarrow> K mod p = K - p) \<and> (2 * p \<le> K \<longrightarrow>
    K mod p = K - 2 * p)"
    using outer_facts[OF assms(1,2)] by (force simp: ind_def)
  have m: "2 * mHalf p + 1 = p" and pK: "p \<le> K" and K3: "K < 3 * p" using of
    by (auto simp: ind_def)
  have a2: "2 * a < p" using m assms(4) by (simp add: ind_def)
  have cc: "ell p K a = ind (1 \<le> a \<and> a \<le> K) + ind (1 \<le> p - a \<and>
    p - a \<le> K) + ind (1 \<le> p + a \<and> p + a \<le> K) +
      ind (1 \<le> 2 * p - a \<and> 2 * p - a \<le> K) + ind (1 \<le> 2 * p + a \<and>
        2 * p + a \<le> K) + ind (1 \<le> 3 * p - a \<and> 3 * p - a \<le> K)"
    unfolding ell_def by (rule card_class[OF assms(3) a2 K3])
  have i1: "ind (1 \<le> a \<and> a \<le> K) = 1" using assms(3) a2 pK by (force simp: ind_def)
  have i2: "ind (1 \<le> p - a \<and> p - a \<le> K) = 1" using assms(3) a2 pK
    by (force simp: ind_def)
  show ?thesis
  proof (cases "K < 2 * p")
    case True
    have v: "K mod p = K - p" using of True by (fastforce simp: ind_def)
    have "(1 \<le> p + a \<and> p + a \<le> K) \<longleftrightarrow> a \<le> K mod p"
      using v pK a2 assms(3) by linarith
    hence i3: "ind (1 \<le> p + a \<and> p + a \<le> K) = ind (a \<le> K mod p)" by presburger
    have i4: "ind (1 \<le> 2 * p - a \<and> 2 * p - a \<le> K) = ind (p \<le> K mod p + a)"
      using v pK a2 by (fastforce simp: ind_def)
    have i5: "ind (1 \<le> 2 * p + a \<and> 2 * p + a \<le> K) = 0" using True
      by (auto simp: ind_def)
    have i6: "ind (1 \<le> 3 * p - a \<and> 3 * p - a \<le> K) = 0" using True a2
      by (force simp: ind_def)
    show ?thesis unfolding cc i1 i2 i3 i4 i5 i6 using True by presburger
  next
    case False
    have v: "K mod p = K - 2 * p" using of False by (auto simp: ind_def)
    have i3: "ind (1 \<le> p + a \<and> p + a \<le> K) = 1" using False a2 by (force simp: ind_def)
    have i4: "ind (1 \<le> 2 * p - a \<and> 2 * p - a \<le> K) = 1" using False a2
      by (auto simp: ind_def)
    have "(1 \<le> 2 * p + a \<and> 2 * p + a \<le> K) \<longleftrightarrow> a \<le> K mod p"
      using v False a2 assms(3) by linarith
    hence i5: "ind (1 \<le> 2 * p + a \<and> 2 * p + a \<le> K) = ind (a \<le> K mod p)"
      by presburger
    have i6: "ind (1 \<le> 3 * p - a \<and> 3 * p - a \<le> K) = ind (p \<le> K mod p + a)"
      using v False a2 by (force simp: ind_def)
    show ?thesis unfolding cc i1 i2 i3 i4 i5 i6 using False by presburger
  qed
qed

lemma outerCount_add:
  assumes "prime p" "OuterHyp K p" "1 \<le> a" "a \<le> mHalf p"
  shows "outerCount K p a + ind (a \<le> Nof K) = ell p K a"
  using card_outerClass[OF assms] by (simp add: outerCount_def ind_def)

lemma outerCount_zero:
  assumes "prime p" "OuterHyp K p"
  shows "outerCount K p 0 = (if K < 2 * p then 1 else 2)"
  using outer_facts[OF assms] by (simp add: outerCount_def zero_class[OF assms])

text \<open>The weight (4.12) of row @{text i} of a class with @{text l} poles and
  @{text "\<delta> = d"}.\<close>
definition Wc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat" where
  "Wc l d i = (if i < l - 2 then min 0 (of_nat i + 3 * of_nat d - (of_nat l + 4) / 2) else 0)"

text \<open>The two finite class computations: classes with @{text "2 + A + B"} and
  @{text "4 + A + B"} poles.\<close>
lemma card_lt_Suc: "card {i. i < Suc n \<and> P i} = card {i. i < n \<and>
  P i} + (if P n then 1 else 0)"
proof -
  have e: "{i. i < Suc n \<and> P i} = (if P n then insert n {i. i < n \<and>
    P i} else {i. i < n \<and> P i})"
    by (auto simp: less_Suc_eq)
  show ?thesis unfolding e by simp
qed
lemma cls2:
  assumes "A \<le> 1" "B \<le> 1" "d \<le> 1"
  shows "2 * (\<Sum> i < 2 + A + B - d. Wc (2 + A + B) d i) =
    - 7 * (of_nat A + of_nat B) + 6 * of_nat d * (of_nat A + of_nat B) \<and>
         card {i. i < 2 + A + B - d \<and> Wc (2 + A + B) d i = 0} = 2 - d + d * A * B"
proof -
  have "A = 0 \<or> A = 1" "B = 0 \<or> B = 1" "d = 0 \<or> d = 1" using assms by auto
  thus ?thesis by (elim disjE) (simp_all add: Wc_def eval_nat_numeral card_lt_Suc lessThan_Suc
    min_def)
qed

lemma cls4:
  assumes "A \<le> 1" "B \<le> 1" "d \<le> 1"
  shows "2 * (\<Sum> i < 4 + A + B - d. Wc (4 + A + B) d i) =
    - 14 - 7 * (of_nat A + of_nat B) + of_nat d * (12 + 5 * (of_nat A + of_nat B)) \<and>
         card {i. i < 4 + A + B - d \<and> Wc (4 + A + B) d i = 0} = 2 + d * A * B"
proof -
  have "A = 0 \<or> A = 1" "B = 0 \<or> B = 1" "d = 0 \<or> d = 1" using assms by auto
  thus ?thesis by (elim disjE) (simp_all add: Wc_def eval_nat_numeral card_lt_Suc lessThan_Suc
    min_def)
qed

text \<open>The weight as a function of naturals.\<close>
definition Wn :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat" where
  "Wn K p a i = (if a = 0 then (if outerCount K p 0 = 1 then - 1 / 2 else if i = 0 then - 2 else 0)
                 else Wc (ell p K a) (ind (a \<le> Nof K)) i)"

lemma wOut_eq: "wOut K p x = Wn K p (fst x) (snd x)"
  by (simp add: wOut_def Wn_def Wc_def ind_def Let_def)

lemma sum_wOut: "(\<Sum> x \<leftarrow> outer_idx K p. wOut K p x) = (\<Sum> a \<le>
  mHalf p. \<Sum> i < outerCount K p a. Wn K p a i)"
  unfolding outer_idx_def
  by (simp add: map_concat sum_list_concat_aux o_def sum_list_distinct_conv_sum_set wOut_eq
    atLeast0LessThan
      lessThan_Suc_atMost del: upt_Suc)

lemma card_zero_wOut:
  "length (filter (\<lambda>x. wOut K p x = 0) (outer_idx K p)) = (\<Sum> a \<le>
    mHalf p. card {i. i < outerCount K p a \<and> Wn K p a i = 0})"
  unfolding outer_idx_def
  by (simp add: filter_concat length_concat o_def filter_map sum_list_distinct_conv_sum_set
    distinct_length_filter
      wOut_eq atLeast0LessThan lessThan_Suc_atMost Int_def conj_commute del: upt_Suc)

lemma class_low:
  assumes "prime p" "OuterHyp K p" "K < 2 * p" "1 \<le> a" "a \<le> mHalf p"
  shows "2 * (\<Sum> i < outerCount K p a. Wn K p a i) =
           - 7 * (of_nat (ind (a \<le> K mod p)) + of_nat (ind (p \<le>
             K mod p + a))) + 6 * of_nat (ind (a \<le> Nof K)) * (of_nat (ind (a \<le>
             K mod p)) + of_nat (ind (p \<le> K mod p + a))) \<and>
         card {i. i < outerCount K p a \<and>
           Wn K p a i = 0} = 2 - ind (a \<le> Nof K) + ind (a \<le> Nof K) * ind (a \<le>
           K mod p) * ind (p \<le> K mod p + a)"
proof -
  have e: "ell p K a = 2 + ind (a \<le> K mod p) + ind (p \<le> K mod p + a)"
    using ell_eq[OF assms(1,2,4,5)] assms(3) by simp
  have oc: "outerCount K p a = 2 + ind (a \<le> K mod p) + ind (p \<le> K mod p + a) - ind (a \<le>
    Nof K)"
    using outerCount_add[OF assms(1,2,4,5)] e by linarith
  have W: "Wn K p a i = Wc (2 + ind (a \<le> K mod p) + ind (p \<le> K mod p + a)) (ind (a \<le>
    Nof K)) i" for i
    using assms(4) e by (simp add: Wn_def)
  show ?thesis unfolding oc W by (rule cls2[OF ind_le_one ind_le_one ind_le_one])
qed

lemma class_high:
  assumes "prime p" "OuterHyp K p" "\<not> K < 2 * p" "1 \<le> a" "a \<le> mHalf p"
  shows "2 * (\<Sum> i < outerCount K p a. Wn K p a i) =
           - 14 - 7 * (of_nat (ind (a \<le> K mod p)) + of_nat (ind (p \<le>
             K mod p + a))) + of_nat (ind (a \<le> Nof K)) * (12 + 5 * (of_nat (ind (a \<le>
             K mod p)) + of_nat (ind (p \<le> K mod p + a)))) \<and>
         card {i. i < outerCount K p a \<and>
           Wn K p a i = 0} = 2 + ind (a \<le> Nof K) * ind (a \<le> K mod p) * ind (p \<le>
           K mod p + a)"
proof -
  have e: "ell p K a = 4 + ind (a \<le> K mod p) + ind (p \<le> K mod p + a)"
    using ell_eq[OF assms(1,2,4,5)] assms(3) by simp
  have oc: "outerCount K p a = 4 + ind (a \<le> K mod p) + ind (p \<le> K mod p + a) - ind (a \<le>
    Nof K)"
    using outerCount_add[OF assms(1,2,4,5)] e by linarith
  have W: "Wn K p a i = Wc (4 + ind (a \<le> K mod p) + ind (p \<le> K mod p + a)) (ind (a \<le>
    Nof K)) i" for i
    using assms(4) e by (simp add: Wn_def)
  show ?thesis unfolding oc W by (rule cls4[OF ind_le_one ind_le_one ind_le_one])
qed

text \<open>The interval counts used in (4.14).\<close>
lemma counts:
  assumes "prime p" "OuterHyp K p"
  shows "card {a \<in> {1..mHalf p}. a \<le> K mod p} + card {a \<in> {1..mHalf p}. p \<le>
    K mod p + a} = K mod p \<and>
         card {a \<in> {1..mHalf p}. a \<le> Nof K \<and>
           a \<le> K mod p} = min (Nof K) (K mod p) \<and>
         card {a \<in> {1..mHalf p}. a \<le> Nof K \<and>
           p \<le> K mod p + a} = Nof K + K mod p + 1 - p \<and>
         card {a \<in> {1..mHalf p}. a \<le> Nof K} = Nof K \<and>
         card {a \<in> {1..mHalf p}. (a \<le> Nof K \<and> a \<le> K mod p) \<and>
           p \<le> K mod p + a} = Nof K + K mod p + 1 - p"
proof -
  obtain m: "2 * mHalf p + 1 = p" and N: "2 * Nof K < p" using outer_facts[OF assms] by blast
  have p0: "0 < p" using m by linarith
  have vp: "K mod p < p" using p0 by simp
  have Nm: "Nof K \<le> mHalf p" using N m by linarith
  have vp1: "Suc 0 \<le> p - K mod p" using vp by linarith
  have e1: "{a \<in> {1..mHalf p}. a \<le> K mod p} = {1..min (mHalf p) (K mod p)}" by auto
  have e2: "{a \<in> {1..mHalf p}. p \<le> K mod p + a} = {p - K mod p..mHalf p}" using vp vp1
    by auto
  have e3: "{a \<in> {1..mHalf p}. a \<le> Nof K \<and>
    a \<le> K mod p} = {1..min (Nof K) (K mod p)}" using Nm by auto
  have e4: "{a \<in> {1..mHalf p}. a \<le> Nof K \<and>
    p \<le> K mod p + a} = {p - K mod p..Nof K}" using Nm vp vp1 by auto
  have e5: "{a \<in> {1..mHalf p}. a \<le> Nof K} = {1..Nof K}" using Nm by auto
  have e6: "{a \<in> {1..mHalf p}. (a \<le> Nof K \<and> a \<le> K mod p) \<and>
    p \<le> K mod p + a} = {p - K mod p..Nof K}"
    using Nm vp N vp1 by auto
  have "min (mHalf p) (K mod p) + (Suc (mHalf p) - (p - K mod p)) = K mod p"
    using vp m by (cases "K mod p \<le> mHalf p"; simp add: min_def; linarith)
  moreover have "Suc (Nof K) - (p - K mod p) = Nof K + K mod p + 1 - p" using vp by linarith
  ultimately show ?thesis unfolding e1 e2 e3 e4 e5 e6 card_atLeastAtMost by simp
qed

text \<open>The table after (4.14): summing (4.12) and applying Lemma 4.2 gives exactly
  @{text "\<gamma>_p^out"}.
  Pure combinatorics of the classes (Lean: OuterCount.lean, 444 lines).\<close>
lemma ind_sum_nat: "finite I \<Longrightarrow>
  (\<Sum> a \<in> I. ind (P a)) = card {a \<in> I. P a}"
  unfolding ind_def using sum.inter_filter[of I "\<lambda>_. 1::nat" P] by simp

lemma ind_sum_rat: "finite I \<Longrightarrow>
  (\<Sum> a \<in> I. (of_nat (ind (P a)) :: rat)) = of_nat (card {a \<in> I. P a})"
  by (simp only: of_nat_sum[symmetric] ind_sum_nat)

lemma two_minus_ind: "2 - ind P + ind P = (2::nat)"
  by (simp add: ind_def)

lemma gamma_arith_low:
  fixes X :: rat
  assumes S: "2 * X = - 7 * (of_nat c1 + of_nat c2) + 6 * (of_nat c3 + of_nat c4)"
    and c12: "c1 + c2 = v" and v: "v = K - p" and pK: "p \<le> K" and c3: "c3 =
      min N v" and c4: "c4 = u"
    and m: "2 * m + 1 = p" and Nm: "N \<le> 2 * m"
  shows "(of_int (- 7 * (int K - int p) + 6 * int (min N v + u) - 1 - min (int r) (int p - 1 -
    int N + int u)) :: rat)
         = 2 * (- 1 / 2 + X) - of_nat (min r (2 * m - N + u))"
proof -
  have k: "int K - int p = int c1 + int c2" using c12 v pK by simp
  have x: "int p - 1 - int N + int u = int (2 * m - N + u)" unfolding m[symmetric] using Nm
    by (simp add: of_nat_diff)
  have mn: "min (int r) (int (2 * m - N + u)) = int (min r (2 * m - N + u))" by (simp add: min_def)
  have e: "(of_int (- 7 * (int K - int p) + 6 * int (min N v + u) - 1 - min (int r) (int p - 1 -
    int N + int u)) :: rat)
      = - 7 * (of_nat c1 + of_nat c2) + 6 * (of_nat c3 + of_nat c4) - 1 - of_nat (min r (2 * m - N +
        u))"
    unfolding k x mn c3 c4 by simp
  have t: "2 * (- 1 / 2 + X) = 2 * X - 1" by simp
  show ?thesis unfolding e t S by simp
qed

lemma gamma_arith_high:
  fixes X :: rat
  assumes S: "2 * X = - 14 * of_nat m - 7 * (of_nat c1 + of_nat c2) + 12 * of_nat c5 + 5 *
    (of_nat c3 + of_nat c4)"
    and c12: "c1 + c2 = v" and v: "v = K - 2 * p" and pK: "2 * p \<le> K" and c3: "c3 =
      min N v" and c4: "c4 = u"
    and c5: "c5 = N" and m: "2 * m + 1 = p"
  shows "(of_int (- 7 * (int K - int p) + 3 + 12 * int N + 5 * int (min N v + u) -
    min (int r) (int p + int u)) :: rat)
         = 2 * (- 2 + X) - of_nat (min r (2 * m + 1 + u))"
proof -
  have k: "int K - int p = int c1 + int c2 + int p" using c12 v pK by simp
  have x: "int p + int u = int (2 * m + 1 + u)" unfolding m[symmetric] by simp
  have mn: "min (int r) (int (2 * m + 1 + u)) = int (min r (2 * m + 1 + u))" by (simp add: min_def)
  have mp: "(of_nat p :: rat) = 2 * of_nat m + 1" unfolding m[symmetric] by simp
  have e: "(of_int (- 7 * (int K - int p) + 3 + 12 * int N + 5 * int (min N v + u) -
    min (int r) (int p + int u)) :: rat)
      = - 7 * (of_nat c1 + of_nat c2 + of_nat p) + 3 + 12 * of_nat c5 + 5 * (of_nat c3 +
        of_nat c4) - of_nat (min r (2 * m + 1 + u))"
    unfolding k x mn c3 c4 c5 by simp
  have t: "2 * (- 2 + X) = 2 * X - 4" by simp
  show ?thesis unfolding e t S mp by (simp add: algebra_simps)
qed
theorem gammaOut_eq_sum:
  assumes p: "prime p" and K: "40 dvd K" and H: "OuterHyp K p"
  shows "of_int (gammaOut K p) =
           2 * (\<Sum> x \<leftarrow> outer_idx K p. wOut K p x)
           - of_nat (min (rOut K p) (length (filter (\<lambda>x. wOut K p x = 0) (outer_idx K p))))"
proof -
  define m where "m = mHalf p"
  define I where "I = {1..m}"
  define u where "u = Nof K + K mod p + 1 - p"
  obtain c12: "card {a \<in> I. a \<le> K mod p} + card {a \<in> I. p \<le> K mod p + a} = K mod p"
    and c3: "card {a \<in> I. a \<le> Nof K \<and> a \<le> K mod p} = min (Nof K) (K mod p)"
    and c4: "card {a \<in> I. a \<le> Nof K \<and> p \<le> K mod p + a} = u"
    and c5: "card {a \<in> I. a \<le> Nof K} = Nof K"
    and c6: "card {a \<in> I. (a \<le> Nof K \<and> a \<le> K mod p) \<and>
      p \<le> K mod p + a} = u"
    using counts[OF p H] unfolding I_def m_def u_def by blast
  have W0: "(\<Sum> x \<leftarrow> outer_idx K p. wOut K p x) = (\<Sum> i <
    outerCount K p 0. Wn K p 0 i) + (\<Sum> a \<in> I. \<Sum> i < outerCount K p a. Wn K p a i)"
  proof -
    have u: "{..mHalf p} = insert 0 I" by (auto simp: I_def m_def)
    show ?thesis unfolding sum_wOut u by (subst sum.insert) (simp_all add: I_def)
  qed
  have Z0: "length (filter (\<lambda>x. wOut K p x = 0) (outer_idx K p)) = card {i. i <
    outerCount K p 0 \<and> Wn K p 0 i = 0} + (\<Sum> a \<in> I. card {i. i <
    outerCount K p a \<and> Wn K p a i = 0})"
  proof -
    have u: "{..mHalf p} = insert 0 I" by (auto simp: I_def m_def)
    show ?thesis unfolding card_zero_wOut u by (subst sum.insert) (simp_all add: I_def)
  qed
  show ?thesis
  proof (cases "K < 2 * p")
    case True
    have v: "K mod p = K - p" using outer_facts[OF p H] True by blast
    have oc0: "outerCount K p 0 = 1" by (simp add: outerCount_zero[OF p H] True)
    have z0: "(\<Sum> i < outerCount K p 0. Wn K p 0 i) = - 1 / 2" and zc: "card {i. i <
      outerCount K p 0 \<and> Wn K p 0 i = 0} = 0"
      by (simp_all add: oc0 Wn_def)
    have S: "2 * (\<Sum> a \<in> I. \<Sum> i < outerCount K p a. Wn K p a i) =
        - 7 * (of_nat (card {a \<in> I. a \<le> K mod p}) + of_nat (card {a \<in> I. p \<le>
          K mod p + a}))
        + 6 * (of_nat (card {a \<in> I. a \<le> Nof K \<and>
          a \<le> K mod p}) + of_nat (card {a \<in> I. a \<le> Nof K \<and> p \<le> K mod p + a}))"
    proof -
      have cl: "2 * (\<Sum> i < outerCount K p a. Wn K p a i) =
          - 7 * (of_nat (ind (a \<le> K mod p)) + of_nat (ind (p \<le> K mod p + a)))
          + 6 * (of_nat (ind (a \<le> Nof K \<and>
            a \<le> K mod p)) + of_nat (ind (a \<le> Nof K \<and> p \<le> K mod p + a)))"
            if a: "a \<in> I" for a
      proof -
        have a1: "1 \<le> a" "a \<le> mHalf p" using a by (simp_all add: I_def m_def)
        have "2 * (\<Sum> i < outerCount K p a. Wn K p a i) =
            - 7 * (of_nat (ind (a \<le> K mod p)) + of_nat (ind (p \<le>
              K mod p + a))) + 6 * of_nat (ind (a \<le> Nof K)) * (of_nat (ind (a \<le>
              K mod p)) + of_nat (ind (p \<le> K mod p + a)))"
          using class_low[OF p H True a1] by blast
        also have "6 * of_nat (ind (a \<le> Nof K)) * (of_nat (ind (a \<le>
          K mod p)) + of_nat (ind (p \<le> K mod p + a))) =
            6 * (of_nat (ind (a \<le> Nof K \<and>
              a \<le> K mod p)) + of_nat (ind (a \<le> Nof K \<and> p \<le> K mod p + a)) :: rat)"
          by (simp only: ind_mult[symmetric] of_nat_mult) (simp add: algebra_simps)
        finally show ?thesis .
      qed
      have "2 * (\<Sum> a \<in> I. \<Sum> i < outerCount K p a. Wn K p a i) = (\<Sum> a \<in>
        I. 2 * (\<Sum> i < outerCount K p a. Wn K p a i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum> a \<in> I. - 7 * (of_nat (ind (a \<le>
        K mod p)) + of_nat (ind (p \<le> K mod p + a)))
          + 6 * (of_nat (ind (a \<le> Nof K \<and>
            a \<le> K mod p)) + of_nat (ind (a \<le> Nof K \<and> p \<le> K mod p + a))))"
        by (rule sum.cong[OF refl]) (rule cl)
      also have "\<dots> = - 7 * (of_nat (card {a \<in> I. a \<le> K mod p}) + of_nat (card {a \<in>
        I. p \<le> K mod p + a}))
          + 6 * (of_nat (card {a \<in> I. a \<le> Nof K \<and>
            a \<le> K mod p}) + of_nat (card {a \<in> I. a \<le> Nof K \<and>
            p \<le> K mod p + a}))"
      proof -
        have fI: "finite I" by (simp add: I_def)
        have "(\<Sum> a \<in> I. - 7 * (of_nat (ind (a \<le> K mod p)) + of_nat (ind (p \<le>
          K mod p + a)))
            + 6 * (of_nat (ind (a \<le> Nof K \<and>
              a \<le> K mod p)) + of_nat (ind (a \<le> Nof K \<and> p \<le> K mod p + a)))) =
            - 7 * ((\<Sum> a \<in> I. of_nat (ind (a \<le> K mod p))) + (\<Sum> a \<in>
              I. of_nat (ind (p \<le> K mod p + a))))
            + 6 * ((\<Sum> a \<in> I. of_nat (ind (a \<le> Nof K \<and>
              a \<le> K mod p))) + (\<Sum> a \<in> I. of_nat (ind (a \<le> Nof K \<and>
              p \<le> K mod p + a))) :: rat)"
          by (simp only: sum.distrib sum_distrib_left[symmetric])
        thus ?thesis by (simp only: ind_sum_rat[OF fI])
      qed
      finally show ?thesis .
    qed
    have Z: "length (filter (\<lambda>x. wOut K p x = 0) (outer_idx K p)) = 2 * m - Nof K + u"
    proof -
      have cl: "card {i. i < outerCount K p a \<and>
        Wn K p a i = 0} = 2 - ind (a \<le> Nof K) + ind ((a \<le> Nof K \<and>
        a \<le> K mod p) \<and> p \<le> K mod p + a)"
        if a: "a \<in> I" for a
      proof -
        have a1: "1 \<le> a" "a \<le> mHalf p" using a by (simp_all add: I_def m_def)
        show ?thesis using class_low[OF p H True a1] by (simp add: ind_mult)
      qed
      have fI: "finite I" by (simp add: I_def)
      have "(\<Sum> a \<in> I. card {i. i < outerCount K p a \<and> Wn K p a i = 0}) =
          (\<Sum> a \<in> I. (2 - ind (a \<le> Nof K)) + ind ((a \<le> Nof K \<and>
            a \<le> K mod p) \<and> p \<le> K mod p + a))"
        by (rule sum.cong[OF refl]) (rule cl)
      also have "\<dots> = (\<Sum> a \<in> I. 2 - ind (a \<le> Nof K)) + u"
        by (simp only: sum.distrib ind_sum_nat[OF fI] c6)
      finally have s: "(\<Sum> a \<in> I. card {i. i < outerCount K p a \<and>
        Wn K p a i = 0}) = (\<Sum> a \<in> I. 2 - ind (a \<le> Nof K)) + u" .
      have "(\<Sum> a \<in> I. 2 - ind (a \<le> Nof K)) + (\<Sum> a \<in> I. ind (a \<le> Nof K)) =
        (\<Sum> a \<in> I. (2::nat))"
        by (simp only: sum.distrib[symmetric] two_minus_ind)
      moreover have "(\<Sum> a \<in> I. ind (a \<le> Nof K)) = Nof K" using c5
        by (simp only: ind_sum_nat[OF fI])
      moreover have "(\<Sum> a \<in> I. (2::nat)) = 2 * m" by (simp add: I_def)
      ultimately have "(\<Sum> a \<in> I. 2 - ind (a \<le> Nof K)) + Nof K = 2 * m" by simp
      hence "(\<Sum> a \<in> I. 2 - ind (a \<le> Nof K)) = 2 * m - Nof K" by linarith
      thus ?thesis unfolding Z0 zc s by simp
    qed
    show ?thesis
      unfolding W0 Z z0 gammaOut_def Let_def
      unfolding u_def[symmetric] if_P[OF True]
    proof (rule gamma_arith_low[OF S c12 v])
      show "p \<le> K" using outer_facts[OF p H] by blast
      show "card {a \<in> I. a \<le> Nof K \<and> a \<le> K mod p} = min (Nof K) (K mod p)"
        by (rule c3)
      show "card {a \<in> I. a \<le> Nof K \<and> p \<le> K mod p + a} = u" by (rule c4)
      show "2 * m + 1 = p" using outer_facts[OF p H] by (simp add: m_def)
      show "Nof K \<le> 2 * m" using outer_facts[OF p H] by (simp add: m_def)
    qed
  next
    case False
    have v: "K mod p = K - 2 * p" using outer_facts[OF p H] False by auto
    have oc0: "outerCount K p 0 = 2" by (simp add: outerCount_zero[OF p H] False)
    have z0: "(\<Sum> i < outerCount K p 0. Wn K p 0 i) = - 2" and zc: "card {i. i <
      outerCount K p 0 \<and> Wn K p 0 i = 0} = 1"
    proof -
      have s01: "{..<outerCount K p 0} = {0, 1}" using oc0 by auto
      show "(\<Sum> i < outerCount K p 0. Wn K p 0 i) = - 2" by (simp add: s01 Wn_def oc0)
      have "{i. i < outerCount K p 0 \<and> Wn K p 0 i = 0} = {1}" using oc0 by (auto simp: Wn_def)
      thus "card {i. i < outerCount K p 0 \<and> Wn K p 0 i = 0} = 1" by simp
    qed
    have S: "2 * (\<Sum> a \<in> I. \<Sum> i < outerCount K p a. Wn K p a i) =
        - 14 * of_nat m - 7 * (of_nat (card {a \<in> I. a \<le> K mod p}) + of_nat (card {a \<in>
          I. p \<le> K mod p + a}))
        + 12 * of_nat (card {a \<in> I. a \<le> Nof K})
        + 5 * (of_nat (card {a \<in> I. a \<le> Nof K \<and>
          a \<le> K mod p}) + of_nat (card {a \<in> I. a \<le> Nof K \<and> p \<le> K mod p + a}))"
    proof -
      have cl: "2 * (\<Sum> i < outerCount K p a. Wn K p a i) =
          - 14 - 7 * (of_nat (ind (a \<le> K mod p)) + of_nat (ind (p \<le> K mod p + a)))
          + 12 * of_nat (ind (a \<le> Nof K))
          + 5 * (of_nat (ind (a \<le> Nof K \<and>
            a \<le> K mod p)) + of_nat (ind (a \<le> Nof K \<and> p \<le> K mod p + a)))"
            if a: "a \<in> I" for a
      proof -
        have a1: "1 \<le> a" "a \<le> mHalf p" using a by (simp_all add: I_def m_def)
        have "2 * (\<Sum> i < outerCount K p a. Wn K p a i) =
            - 14 - 7 * (of_nat (ind (a \<le> K mod p)) + of_nat (ind (p \<le>
              K mod p + a))) + of_nat (ind (a \<le> Nof K)) * (12 + 5 * (of_nat (ind (a \<le>
              K mod p)) + of_nat (ind (p \<le> K mod p + a))))"
          using class_high[OF p H False a1] by blast
        also have "of_nat (ind (a \<le> Nof K)) * (12 + 5 * (of_nat (ind (a \<le>
          K mod p)) + of_nat (ind (p \<le> K mod p + a)))) =
            12 * of_nat (ind (a \<le> Nof K)) + 5 * (of_nat (ind (a \<le> Nof K \<and>
              a \<le> K mod p)) + of_nat (ind (a \<le> Nof K \<and> p \<le> K mod p + a)) :: rat)"
          by (simp only: ind_mult[symmetric] of_nat_mult) (simp add: algebra_simps)
        finally show ?thesis by simp
      qed
      have cI: "card I = m" by (simp add: I_def)
      have "2 * (\<Sum> a \<in> I. \<Sum> i < outerCount K p a. Wn K p a i) = (\<Sum> a \<in>
        I. 2 * (\<Sum> i < outerCount K p a. Wn K p a i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum> a \<in> I. - 14 - 7 * (of_nat (ind (a \<le>
        K mod p)) + of_nat (ind (p \<le> K mod p + a)))
          + 12 * of_nat (ind (a \<le> Nof K))
          + 5 * (of_nat (ind (a \<le> Nof K \<and>
            a \<le> K mod p)) + of_nat (ind (a \<le> Nof K \<and> p \<le> K mod p + a))))"
        by (rule sum.cong[OF refl]) (rule cl)
      also have "\<dots> = - 14 * of_nat m - 7 * (of_nat (card {a \<in> I. a \<le>
        K mod p}) + of_nat (card {a \<in> I. p \<le> K mod p + a}))
          + 12 * of_nat (card {a \<in> I. a \<le> Nof K})
          + 5 * (of_nat (card {a \<in> I. a \<le> Nof K \<and>
            a \<le> K mod p}) + of_nat (card {a \<in> I. a \<le> Nof K \<and>
            p \<le> K mod p + a}))"
        using cI by (simp add: sum.distrib sum_subtractf sum_distrib_left[symmetric] ind_sum_rat
          I_def)
      finally show ?thesis .
    qed
    have Z: "length (filter (\<lambda>x. wOut K p x = 0) (outer_idx K p)) = 2 * m + 1 + u"
    proof -
      have cl: "card {i. i < outerCount K p a \<and>
        Wn K p a i = 0} = 2 + ind ((a \<le> Nof K \<and> a \<le> K mod p) \<and>
        p \<le> K mod p + a)"
        if a: "a \<in> I" for a
      proof -
        have a1: "1 \<le> a" "a \<le> mHalf p" using a by (simp_all add: I_def m_def)
        show ?thesis using class_high[OF p H False a1] by (simp add: ind_mult)
      qed
      have fI: "finite I" by (simp add: I_def)
      have "(\<Sum> a \<in> I. card {i. i < outerCount K p a \<and> Wn K p a i = 0}) =
          (\<Sum> a \<in> I. 2 + ind ((a \<le> Nof K \<and> a \<le> K mod p) \<and>
            p \<le> K mod p + a))"
        by (rule sum.cong[OF refl]) (rule cl)
      also have "\<dots> = (\<Sum> a \<in> I. (2::nat)) + u"
        by (simp only: sum.distrib ind_sum_nat[OF fI] c6)
      also have "\<dots> = 2 * m + u" by (simp add: I_def)
      finally show ?thesis unfolding Z0 zc by simp
    qed
    show ?thesis
      unfolding W0 Z z0 gammaOut_def Let_def
      unfolding u_def[symmetric] if_not_P[OF False]
    proof (rule gamma_arith_high[OF S c12 v])
      show "2 * p \<le> K" using False by simp
      show "card {a \<in> I. a \<le> Nof K \<and> a \<le> K mod p} = min (Nof K) (K mod p)"
        by (rule c3)
      show "card {a \<in> I. a \<le> Nof K \<and> p \<le> K mod p + a} = u" by (rule c4)
      show "card {a \<in> I. a \<le> Nof K} = Nof K" by (rule c5)
      show "2 * m + 1 = p" using outer_facts[OF p H] by (simp add: m_def)
    qed
  qed
qed

subsection \<open>Lemma 4.2\<close>

text \<open>The weight arithmetic behind Lemma 4.2:
  for nonpositive half-integer weights and any @{text U},
  @{text "\<Sum>_{i\<in>U}(w_i + 1/2) \<le> min(|U|, z)/2"},
    @{text z} the number of zero weights.\<close>
lemma weight_loss_nat:
  fixes n :: nat and w :: "nat \<Rightarrow> 'a :: linordered_field"
  assumes "\<And>i. i < n \<Longrightarrow> w i \<le> 0" "\<And>i. i < n \<Longrightarrow>
    \<exists>k::int. 2 * w i = of_int k" "U \<subseteq> {..<n}"
  shows "(\<Sum> i \<in> U. w i + 1 / 2) \<le> of_nat (min (card U) (card {i. i < n \<and>
    w i = 0})) / 2"
proof -
  define Z where "Z = {i. i < n \<and> w i = 0}"
  have U: "finite U" by (rule finite_subset[OF assms(3)]) simp
  have Zf: "finite Z" by (simp add: Z_def)
  have neg: "w i + 1 / 2 \<le> 0" if i: "i \<in> U - Z" for i
  proof -
    have n: "i < n" and w0: "w i \<noteq> 0" using i assms(3) by (auto simp: Z_def)
    obtain k :: int where k: "2 * w i = of_int k" using assms(2)[OF n] by blast
    have "2 * w i \<le> 0" using assms(1)[OF n] by simp
    hence "of_int k \<le> (0 :: 'a)" by (simp only: k)
    hence "k \<le> 0" by simp
    moreover have "k \<noteq> 0" using k w0 by auto
    ultimately have "k \<le> - 1" by simp
    hence "2 * w i \<le> - 1" using k by (metis of_int_le_iff of_int_minus of_int_1)
    thus ?thesis by simp
  qed
  have split: "(\<Sum> i \<in> U. w i + 1 / 2) = (\<Sum> i \<in>
    U \<inter> Z. w i + 1 / 2) + (\<Sum> i \<in> U - Z. w i + 1 / 2)"
    by (rule sum.Int_Diff[OF U])
  have p1: "(\<Sum> i \<in> U \<inter> Z. w i + 1 / 2) = of_nat (card (U \<inter> Z)) / 2"
    by (simp add: Z_def)
  have p2: "(\<Sum> i \<in> U - Z. w i + 1 / 2) \<le> 0" by (rule sum_nonpos) (use neg in blast)
  have "card (U \<inter> Z) \<le> min (card U) (card Z)"
    using U Zf by (simp add: card_mono)
  hence p3: "of_nat (card (U \<inter> Z)) / 2 \<le> of_nat (min (card U) (card Z)) / (2 :: 'a)"
    by (intro divide_right_mono) simp_all
  show ?thesis unfolding Z_def[symmetric] using split p1 p2 p3 by linarith
qed

lemma weight_loss:
  fixes n :: nat and w :: "nat \<Rightarrow> 'a :: linordered_field"
  assumes "\<And>i. i < n \<Longrightarrow> w i \<le> 0" "\<And>i. i < n \<Longrightarrow>
    \<exists>k::int. 2 * w i = of_int k" "U \<subseteq> {..<n}"
  shows "(\<Sum> i \<in> U. w i + 1 / 2) \<le> of_nat (min (card U) (card {i. i < n \<and>
    w i = 0})) / 2"
  using assms by (rule weight_loss_nat)

text \<open>A matrix with a nontrivial linear relation among its rows has determinant zero
  (over an integral domain: multilinearity in the row carrying a nonzero coefficient).\<close>
lemma det_zero_of_row_relation:
  fixes A :: "'a :: idom mat"
  assumes A: "A \<in> carrier_mat n n" and i0: "i0 < n" and c0: "c i0 \<noteq> 0"
    and rel: "\<And>j. j < n \<Longrightarrow> (\<Sum> i = 0..<n. c i * A $$ (i, j)) = 0"
  shows "Determinant.det A = 0"
proof -
  have At: "transpose_mat A \<in> carrier_mat n n" using A by force
  define v where "v = vec n c"
  have v: "v \<in> carrier_vec n" unfolding v_def by simp
  have v0: "v \<noteq> 0\<^sub>v n"
  proof
    assume "v = 0\<^sub>v n"
    hence "v $ i0 = 0" using i0 by simp
    thus False using i0 c0 unfolding v_def by fastforce
  qed
  have Av: "transpose_mat A *\<^sub>v v = 0\<^sub>v n"
  proof (rule eq_vecI)
    fix j assume j: "j < dim_vec (0\<^sub>v n :: 'a vec)"
    have "(\<Sum> i = 0..<n. c i * A $$ (i, j)) = 0" using rel j by force
    moreover have "(transpose_mat A *\<^sub>v v) $ j = (\<Sum> i = 0..<n. A $$ (i, j) * c i)"
      using j A unfolding v_def by (fastforce simp: scalar_prod_def)
    ultimately show "(transpose_mat A *\<^sub>v v) $ j = 0\<^sub>v n $ j" using j
      by (force simp: mult.commute)
  next
    show "dim_vec (transpose_mat A *\<^sub>v v) = dim_vec (0\<^sub>v n :: 'a vec)" using A by auto
  qed
  have "Determinant.det (transpose_mat A) = 0" using det_0_iff_vec_prod_zero[OF At] v v0 Av by blast
  thus ?thesis using det_transpose[OF A] by argo
qed

text \<open>More than @{text "rank L"} rows of a rational matrix @{text L} satisfy a nontrivial
  linear relation.\<close>
lemma rows_dependent:
  assumes L: "L \<in> carrier_mat n n" and T: "T \<subseteq> {0..<n}" and r: "vec_space.rank n L <
    card T"
  shows "\<exists>c :: nat \<Rightarrow> rat. (\<forall>i. i \<notin> T \<longrightarrow>
    c i = 0) \<and> (\<exists>i \<in> T. c i \<noteq> 0) \<and>
           (\<forall>j < n. (\<Sum> i = 0..<n. c i * L $$ (i, j)) = 0)"
proof -
  have finT: "finite T" using finite_subset[OF T] by blast
  define xs where "xs = sorted_list_of_set T"
  define k where "k = card T"
  have dxs: "distinct xs" unfolding xs_def by auto
  have sxs: "set xs = T" unfolding xs_def using finT by force
  have lxs: "length xs = k" unfolding xs_def k_def using finT by force
  have xn: "xs ! t < n" if "t < k" for t using that sxs lxs T by fastforce
  define G :: "rat mat" where "G = Matrix.mat k n (\<lambda>(t, j). L $$ (xs ! t, j))"
  define F :: "rat mat" where "F = Matrix.mat k n (\<lambda>(t, i). if i = xs ! t then 1 else 0)"
  have Gc: "G \<in> carrier_mat k n" unfolding G_def by auto
  have Fc: "F \<in> carrier_mat k n" unfolding F_def by simp
  have FL: "F * L = G"
  proof (rule eq_matI)
    fix t j assume t: "t < dim_row G" and j: "j < dim_col G"
    have t': "t < k" and j': "j < n" using t j Gc by auto
    have "(F * L) $$ (t, j) = (\<Sum> i = 0..<n. (if i = xs ! t then 1 else 0) * L $$ (i, j))"
      using t' j' Fc L unfolding F_def by (auto simp: scalar_prod_def index_mult_mat)
    also have "\<dots> = (\<Sum> i = 0..<n. if i = xs ! t then L $$ (xs ! t, j) else 0)"
      by (fastforce intro: sum.cong)
    also have "\<dots> = L $$ (xs ! t, j)" using xn[OF t'] by (fastforce simp: sum.delta)
    finally show "(F * L) $$ (t, j) = G $$ (t, j)" using t' j' unfolding G_def by auto
  next
    show "dim_row (F * L) = dim_row G" using Fc L Gc by simp
    show "dim_col (F * L) = dim_col G" using Fc L Gc by force
  qed
  have rG: "vec_space.rank k G \<le> vec_space.rank n L" unfolding FL[symmetric]
    by (rule rank_mat_mul_left[OF Fc L])
  define M where "M = G * transpose_mat G"
  have GTc: "transpose_mat G \<in> carrier_mat n k" using Gc by simp
  have Mc: "M \<in> carrier_mat k k" unfolding M_def using Gc GTc by force
  have rM: "vec_space.rank k M \<le> vec_space.rank k G" unfolding M_def
    by (rule vec_space.rank_mat_mul_right[OF Gc GTc])
  have rk: "vec_space.rank k M < k" using rM rG r unfolding k_def by linarith
  have dM: "Determinant.det M = 0" using vec_space.low_rank_det_zero[OF Mc] rk by fastforce
  obtain u where u: "u \<in> carrier_vec k" "u \<noteq> 0\<^sub>v k" "M *\<^sub>v u = 0\<^sub>v k"
    using det_0_iff_vec_prod_zero[OF Mc] dM by blast
  define w where "w = transpose_mat G *\<^sub>v u"
  have wc: "w \<in> carrier_vec n" unfolding w_def using GTc u(1) by simp
  have Gw: "G *\<^sub>v w = 0\<^sub>v k" using u(3) Gc GTc u(1) unfolding M_def w_def by force
  have ww: "w \<bullet> w = 0"
  proof -
    have "w \<bullet> w = u \<bullet> (G *\<^sub>v w)"
      using transpose_vec_mult_scalar[OF Gc wc u(1)] unfolding w_def by meson
    also have "\<dots> = 0" using Gw u(1) by fastforce
    finally show ?thesis .
  qed
  have w0: "w $ j = 0" if j: "j < n" for j
  proof -
    have s: "w \<bullet> w = (\<Sum> i = 0..<n. w $ i * w $ i)" using wc unfolding scalar_prod_def
      by simp
    have "\<forall>i\<in>{0..<n}. w $ i * w $ i = 0"
      using ww s sum_nonneg_eq_0_iff[of "{0..<n}" "\<lambda>i. w $ i * w $ i"] by auto
    thus ?thesis using j by force
  qed
  have wj: "w $ j = (\<Sum> t = 0..<k. u $ t * L $$ (xs ! t, j))" if j: "j < n" for j
    using j Gc u(1) unfolding w_def G_def scalar_prod_def
      by (fastforce simp: scalar_prod_def mult.commute)
  have bij: "bij_betw (\<lambda>t. xs ! t) {0..<k} T" using dxs sxs lxs
    by (simp add: bij_betw_nth atLeast0LessThan)
  define c where "c i = (if i \<in> T then u $ (the_inv_into {0..<k} ((!) xs) i) else 0)" for i
  have c0: "\<forall>i. i \<notin> T \<longrightarrow> c i = 0" unfolding c_def by presburger
  have cne: "\<exists>i\<in>T. c i \<noteq> 0"
  proof -
    obtain t where t: "t < k" "u $ t \<noteq> 0" using u(1,2) by force
    have "xs ! t \<in> T" using t(1) sxs lxs by force
    moreover have "the_inv_into {0..<k} ((!) xs) (xs ! t) = t" using t(1) bij
      by (force simp: the_inv_into_f_f bij_betw_imp_inj_on)
    ultimately show ?thesis using t(2) unfolding c_def by metis
  qed
  have csum: "(\<Sum> i = 0..<n. c i * L $$ (i, j)) = (\<Sum> t = 0..<k. u $ t * L $$ (xs ! t, j))"
    for j
  proof -
    have "(\<Sum> i = 0..<n. c i * L $$ (i, j)) = (\<Sum> i \<in> T. c i * L $$ (i, j))"
      using T c0 finT by (force intro: sum.mono_neutral_right)
    also have "\<dots> = (\<Sum> t = 0..<k. c (xs ! t) * L $$ (xs ! t, j))"
      using sum.reindex_bij_betw[OF bij, symmetric] by fast
    also have "\<dots> = (\<Sum> t = 0..<k. u $ t * L $$ (xs ! t, j))"
    proof (rule sum.cong[OF refl])
      fix t assume "t \<in> {0..<k}"
      hence t: "t < k" by simp
      have "xs ! t \<in> T" using t sxs lxs by force
      moreover have "the_inv_into {0..<k} ((!) xs) (xs ! t) = t" using t bij
        by (force simp: the_inv_into_f_f bij_betw_imp_inj_on)
      ultimately show "c (xs ! t) * L $$ (xs ! t, j) = u $ t * L $$ (xs ! t, j)" unfolding c_def
        by presburger
    qed
    finally show ?thesis .
  qed
  show ?thesis using c0 cne csum wj w0 by auto
qed

text \<open>Multilinear expansion of the determinant of a sum over rows:
  for every subset @{text T} of the rows,
  take the rows in @{text T} from @{text B} and the others from @{text A}.\<close>
lemma det_add_rows_expand:
  fixes A B :: "'a :: comm_ring_1 mat"
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  shows "Determinant.det (A + B) =
         (\<Sum> T \<in> Pow {0..<n}. Determinant.det (Matrix.mat n n (\<lambda>(i, j).
           if i \<in> T then B $$ (i, j) else A $$ (i, j))))"
proof -
  let ?I = "{0..<n}"
  let ?M = "\<lambda>T. Matrix.mat n n (\<lambda>(i, j).
    if i \<in> T then B $$ (i, j) else A $$ (i, j))"
  have AB: "A + B \<in> carrier_mat n n" using A B by force
  have M: "?M T \<in> carrier_mat n n" for T by fastforce
  have e0: "(\<Prod>i = 0..<n. (A + B) $$ (i, p i)) = (\<Prod>i =
    0..<n. B $$ (i, p i) + A $$ (i, p i))"
    if p: "p permutes ?I" for p
  proof (rule prod.cong[OF refl])
    fix i assume i: "i \<in> ?I"
    have pi: "p i < n" using permutes_in_image[OF p] i by simp
    show "(A + B) $$ (i, p i) = B $$ (i, p i) + A $$ (i, p i)" using i pi A B by simp
  qed
  have e1: "(\<Prod>i = 0..<n. B $$ (i, p i) + A $$ (i, p i)) =
      (\<Sum>T\<in>Pow ?I. (\<Prod>i\<in>T. B $$ (i, p i)) * (\<Prod>i\<in>?I - T. A $$ (i, p i)))"
        for p
    using prod_add[of ?I] by fast
  have e2: "(\<Prod>i\<in>T. B $$ (i, p i)) * (\<Prod>i\<in>?I - T. A $$ (i, p i)) = (\<Prod>i =
    0..<n. ?M T $$ (i, p i))"
    if p: "p permutes ?I" and T: "T \<in> Pow ?I" for p T
  proof -
    have TI: "T \<subseteq> ?I" using T by blast
    have "(\<Prod>i = 0..<n. ?M T $$ (i, p i)) =
      (\<Prod>i\<in>?I - T. ?M T $$ (i, p i)) * (\<Prod>i\<in>T. ?M T $$ (i, p i))"
      using prod.subset_diff[OF TI] by blast
    moreover have "(\<Prod>i\<in>T. ?M T $$ (i, p i)) = (\<Prod>i\<in>T. B $$ (i, p i))"
    proof (rule prod.cong[OF refl])
      fix i assume i: "i \<in> T"
      have pi: "p i < n" "i < n" using permutes_in_image[OF p] i TI by auto
      show "?M T $$ (i, p i) = B $$ (i, p i)" using pi i by simp
    qed
    moreover have "(\<Prod>i\<in>?I - T. ?M T $$ (i, p i)) = (\<Prod>i\<in>?I - T. A $$ (i, p i))"
    proof (rule prod.cong[OF refl])
      fix i assume i: "i \<in> ?I - T"
      have pi: "p i < n" "i < n" using permutes_in_image[OF p] i by auto
      show "?M T $$ (i, p i) = A $$ (i, p i)" using pi i by simp
    qed
    ultimately show ?thesis using mult.commute by auto
  qed
  have "Determinant.det (A + B) = (\<Sum>p\<in>{p. p permutes ?I}. signof p * (\<Prod>i =
    0..<n. (A + B) $$ (i, p i)))"
    using det_def'[OF AB] by meson
  also have "\<dots> = (\<Sum>p\<in>{p. p permutes ?I}. \<Sum>T\<in>Pow ?I. signof p * (\<Prod>i =
    0..<n. ?M T $$ (i, p i)))"
  proof (rule sum.cong[OF refl])
    fix p assume "p \<in> {p. p permutes ?I}"
    hence p: "p permutes ?I" by blast
    have "signof p * (\<Prod>i = 0..<n. (A + B) $$ (i, p i)) =
        signof p * (\<Sum>T\<in>Pow ?I. (\<Prod>i\<in>T. B $$ (i,
          p i)) * (\<Prod>i\<in>?I - T. A $$ (i, p i)))"
      using e0[OF p] e1 by presburger
    also have "\<dots> = (\<Sum>T\<in>Pow ?I. signof p * ((\<Prod>i\<in>T. B $$ (i,
      p i)) * (\<Prod>i\<in>?I - T. A $$ (i, p i))))"
      using sum_distrib_left by blast
    also have "\<dots> = (\<Sum>T\<in>Pow ?I. signof p * (\<Prod>i = 0..<n. ?M T $$ (i, p i)))"
      using e2[OF p] by auto
    finally show "signof p * (\<Prod>i = 0..<n. (A + B) $$ (i, p i)) =
        (\<Sum>T\<in>Pow ?I. signof p * (\<Prod>i = 0..<n. ?M T $$ (i, p i)))" .
  qed
  also have "\<dots> = (\<Sum>T\<in>Pow ?I. \<Sum>p\<in>{p. p permutes ?I}. signof p * (\<Prod>i =
    0..<n. ?M T $$ (i, p i)))"
    using sum.swap by fast
  also have "\<dots> = (\<Sum>T\<in>Pow ?I. Determinant.det (?M T))"
    using det_def'[OF M] by presburger
  finally show ?thesis .
qed

text \<open>Lemma 4.2: if @{text "v(A_ij) \<ge> w_i + w_j"} with nonpositive half-integer weights,
  @{text L} is
  integral of rank at most @{text r}, and exactly @{text z} weights are zero, then
  @{text "v(det(A + p^-^1L)) \<ge> 2\<Sum>w_i - min(r, z)"} (Gauss valuation;
    @{text L} constant).  Proof by the
  row-multilinear expansion (@{text "Determinant.det_linear_rows_sum"}), not
    by complementary minors.\<close>
theorem det_vpGge_of_weighted_entries:
  assumes p: "prime p" and A: "A \<in> carrier_mat n n" and L: "L \<in> carrier_mat n n"
    and hw: "\<And>i. i < n \<Longrightarrow>
      w i \<le> 0" and hw2: "\<And>i. i < n \<Longrightarrow> \<exists>k::int. 2 * w i = of_int k"
    and hA: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
      vpGge p (A $$ (i, j)) (w i + w j)"
    and hL: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
      L $$ (i, j) \<noteq> 0 \<Longrightarrow> 0 \<le> vp p (L $$ (i, j))"
    and hr: "vec_space.rank n L \<le> r"
  shows "vpGge p (Determinant.det (A + map_mat (\<lambda>c. [:c / of_nat p:]) L))
           (2 * (\<Sum> i < n. w i) - of_nat (min r (card {i. i < n \<and> w i = 0})))"
proof -
  define L' where "L' = map_mat (\<lambda>c. [:c / of_nat p:]) L"
  define z where "z = card {i. i < n \<and> w i = 0}"
  define bnd where "bnd = 2 * (\<Sum> i < n. w i) - of_nat (min r z)"
  have L'c: "L' \<in> carrier_mat n n" using L by (simp add: L'_def)
  have expand: "Determinant.det (A + L') =
      (\<Sum> T \<in> Pow {0..<n}. Determinant.det (Matrix.mat n n (\<lambda>(i, j).
        if i \<in> T then L' $$ (i, j) else A $$ (i, j))))"
    by (rule det_add_rows_expand[OF A L'c])
  have trm: "\<And>T. T \<subseteq> {0..<n} \<Longrightarrow>
      vpGge p (Determinant.det (Matrix.mat n n (\<lambda>(i, j).
        if i \<in> T then L' $$ (i, j) else A $$ (i, j)))) bnd"
  proof -
    fix T assume T: "T \<subseteq> {0..<n}"
    define P where "P = Matrix.mat n n (\<lambda>(i, j).
      if i \<in> T then L' $$ (i, j) else A $$ (i, j))"
    have Pc: "P \<in> carrier_mat n n" by (simp add: P_def)
    show "vpGge p (Determinant.det P) bnd"
    proof (cases "r < card T")
      case True
      \<comment> \<open>the @{text "p^-1 L"} rows in @{text T} are dependent,
        so this determinant vanishes\<close>
      obtain c :: "nat \<Rightarrow> rat" where c0: "\<And>i. i \<notin> T \<Longrightarrow>
        c i = 0" and cne: "\<exists>i \<in> T. c i \<noteq> 0"
        and rel: "\<And>j. j < n \<Longrightarrow> (\<Sum> i = 0..<n. c i * L $$ (i, j)) = 0"
        using rows_dependent[OF L T] True hr by auto
      have "Determinant.det P = 0"
      proof -
        obtain i0 where i0T: "i0 \<in> T" and ci0: "c i0 \<noteq> 0" using cne by blast
        have i0: "i0 < n" using i0T T by auto
        have csum: "(\<Sum> i \<in> S. [:f i:]) = [:\<Sum> i \<in> S. f i:]"
          for S and f :: "nat \<Rightarrow> rat"
          by (induction S rule: infinite_finite_induct) simp_all
        have rel': "(\<Sum> i = 0..<n. [:c i:] * P $$ (i, j)) = 0" if j: "j < n" for j
        proof -
          have t: "[:c i:] * P $$ (i, j) = [:c i * L $$ (i, j) / of_nat p:]"
            if i: "i \<in> {0..<n}" for i
            using i j L c0[of i] by (cases "i \<in> T") (simp_all add: P_def L'_def)
          have "(\<Sum> i = 0..<n. [:c i:] * P $$ (i, j)) = (\<Sum> i =
            0..<n. [:c i * L $$ (i, j) / of_nat p:])"
            by (rule sum.cong[OF refl]) (rule t)
          also have "\<dots> = [:(\<Sum> i = 0..<n. c i * L $$ (i, j)) / of_nat p:]"
            by (simp only: csum sum_divide_distrib)
          also have "\<dots> = 0" using rel[OF j] by simp
          finally show ?thesis .
        qed
        show ?thesis by (rule det_zero_of_row_relation[OF Pc i0, where c =
          "\<lambda>i. [:c i:]"]) (use ci0 rel' in simp_all)
      qed
      thus ?thesis by (simp add: vpGge_zero)
    next
      case False
      hence Tr: "card T \<le> r" by simp
      show ?thesis
      proof (rule vpGge_det_of_terms[OF p Pc])
        fix \<sigma> assume \<sigma>: "\<sigma> permutes {0..<n}"
        define J where "J = {i \<in> {0..<n}. i \<in> T}"
        have JT: "J = T" unfolding J_def using T by auto
        have fac: "\<And>i. i < n \<Longrightarrow>
          vpGge p (P $$ (i, \<sigma> i)) (if i \<in> T then - 1 else w i + w (\<sigma> i))"
        proof -
          fix i assume i: "i < n"
          have si: "\<sigma> i < n" using permutes_in_image[OF \<sigma>] i by force
          show "vpGge p (P $$ (i, \<sigma> i)) (if i \<in> T then - 1 else w i + w (\<sigma> i))"
          proof (cases "i \<in> T")
            case True
            have vL: "vge p (L $$ (i, \<sigma> i)) 0" using hL[OF i si] unfolding vge_def
              by presburger
            have "vge p (L $$ (i, \<sigma> i) * (1 / of_nat p)) (0 + - 1)"
              by (rule vge_mul[OF p vL vge_inv_p[OF p]])
            moreover have "P $$ (i, \<sigma> i) = [:L $$ (i, \<sigma> i) / of_nat p:]"
              using True i si L unfolding P_def L'_def by force
            ultimately show ?thesis using True vpGge_C by force
          next
            case False
            have e: "P $$ (i, \<sigma> i) = A $$ (i, \<sigma> i)" using False i si unfolding P_def
              by force
            show ?thesis using hA[OF i si] e False by presburger
          qed
        qed
        have "vpGge p (\<Prod> i = 0..<n. P $$ (i, \<sigma> i)) (\<Sum> i = 0..<n. (if i \<in>
          T then - 1 else w i + w (\<sigma> i)))"
          by (rule vpGge_prod[OF p]) (use fac in auto)
        moreover have "(\<Sum> i = 0..<n. (if i \<in> T then - 1 else w i + w (\<sigma> i))) \<ge>
          bnd"
        proof -
          have split: "(\<Sum> i = 0..<n. (if i \<in> T then - 1 else w i + w (\<sigma> i))) =
                2 * (\<Sum> i = 0..<n. w i) - ((\<Sum> i \<in>
                  J. w (\<sigma> i) + 1 / 2) + (\<Sum> i \<in> J. w i + 1 / 2))"
          proof -
            have e: "(if i \<in> T then - 1 else w i + w (\<sigma> i)) =
                (w i + w (\<sigma> i)) - (if i \<in>
                  T then (w (\<sigma> i) + 1 / 2) + (w i + 1 / 2) else 0)" for i
              by simp
            have s1: "(\<Sum> i = 0..<n. w (\<sigma> i)) = (\<Sum> i = 0..<n. w i)"
              using sum.permute[OF \<sigma>, of w] by (simp add: o_def)
            have s2: "(\<Sum> i = 0..<n.
              if i \<in> T then (w (\<sigma> i) + 1 / 2) + (w i + 1 / 2) else 0) =
                (\<Sum> i \<in> J. (w (\<sigma> i) + 1 / 2) + (w i + 1 / 2))"
              unfolding J_def by (rule sum.inter_filter[symmetric]) simp
            have "(\<Sum> i = 0..<n. (if i \<in> T then - 1 else w i + w (\<sigma> i))) =
                (\<Sum> i = 0..<n. w i + w (\<sigma> i)) - (\<Sum> i = 0..<n.
                  if i \<in> T then (w (\<sigma> i) + 1 / 2) + (w i + 1 / 2) else 0)"
              by (simp only: e sum_subtractf)
            also have "\<dots> = 2 * (\<Sum> i = 0..<n. w i) - ((\<Sum> i \<in>
              J. w (\<sigma> i) + 1 / 2) + (\<Sum> i \<in> J. w i + 1 / 2))"
              by (simp only: sum.distrib s1 s2 mult_2)
            finally show ?thesis .
          qed
          have hJT: "(\<Sum> i \<in> J. w (\<sigma> i) + 1 / 2) = (\<Sum> j \<in>
            \<sigma> ` T. w j + 1 / 2)"
            unfolding JT by (subst sum.reindex) (auto simp: permutes_inj_on[OF \<sigma>] o_def)
          have cardJ: "card (\<sigma> ` T) = card T"
            by (rule card_image) (rule permutes_inj_on[OF \<sigma>])
          have l1: "(\<Sum> i \<in> \<sigma> ` T. w i + 1 / 2) \<le> of_nat (min (card T) z) / 2"
            unfolding z_def cardJ[symmetric]
              by (rule weight_loss[OF hw hw2]) (use permutes_in_image[OF \<sigma>] T in auto)
          have l2: "(\<Sum> i \<in> J. w i + 1 / 2) \<le> of_nat (min (card T) z) / 2"
            unfolding z_def JT by (rule weight_loss[OF hw hw2 T[unfolded atLeast0LessThan]])
          have "min (card T) z \<le> min r z" using Tr by simp
          hence mm: "(of_nat (min (card T) z) :: rat) \<le> of_nat (min r z)"
            by (simp only: of_nat_le_iff)
          show ?thesis unfolding split hJT unfolding bnd_def atLeast0LessThan using l1 l2 mm
            by linarith
        qed
        ultimately show "vpGge p (\<Prod> i = 0..<n. P $$ (i, \<sigma> i)) bnd" by (rule vpGge_mono)
      qed
    qed
  qed
  show ?thesis
    unfolding L'_def[symmetric] expand bnd_def[symmetric] z_def[symmetric]
    by (rule vpGge_sum[OF p]) (use trm in auto)
qed

subsection \<open>Proposition 4.3\<close>

lemma degree_outerBasis_lt:
  assumes "prime p" "40 dvd K" "OuterHyp K p" "x \<in> set (outer_idx K p)"
  shows "degree (outerBasis K p x) < hof K"
proof -
  have p: "prime p" and H: "OuterHyp K p" using assms(1,3) .
  define a where "a = fst x"
  define i where "i = snd x"
  have am: "a \<le> mHalf p" and ia: "i < outerCount K p a" using assms(4) mem_outer_idx
    by (auto simp: a_def i_def)
  have dS: "degree (sqPoleProd S) \<le> card S" if "finite S" for S
  proof -
    have "degree (sqPoleProd S) \<le> (\<Sum> j \<in> S. degree (pX + [:of_nat j ^ 2:]))"
      unfolding sqPoleProd_def using degree_prod_sum_le[OF that] by (simp add: o_def)
    also have "\<dots> = card S" using degree_pX_plus_const by simp
    finally show ?thesis .
  qed
  have dP: "degree ((pX + [:of_nat n ^ 2:]) ^ k) \<le> k" for n k
    using degree_power_le[of "pX + [:of_nat n ^ 2:]" k] degree_pX_plus_const by simp
  have dQ: "degree (oq K p x) \<le> i"
  proof (cases "a = 0")
    case True
    thus ?thesis using dP by (simp add: oq_def Let_def a_def i_def)
  next
    case False
    hence a1: "1 \<le> a" by simp
    show ?thesis
    proof (cases "i < ell p K a - 2")
      case True
      thus ?thesis using dP False by (simp add: oq_def Let_def a_def i_def)
    next
      case big: False
      have cE: "card {j \<in> outerClassPoles K p a. p < j} + 2 = ell p K a"
        by (rule card_class_high_add_two[OF p H a1 am])
      have fE: "finite {j \<in> outerClassPoles K p a. p < j}" by (simp add: outerClassPoles_def)
      have "degree (oq K p x) = degree (sqPoleProd {j \<in> outerClassPoles K p a. p <
        j} * (pX + [:of_nat a ^ 2:]) ^ (i - (ell p K a - 2)))"
        using False big by (simp add: oq_def Let_def a_def i_def)
      also have "\<dots> \<le> degree (sqPoleProd {j \<in> outerClassPoles K p a. p <
        j}) + degree ((pX + [:of_nat a ^ 2:]) ^ (i - (ell p K a - 2)))"
        by (rule degree_mult_le)
      also have "\<dots> \<le> card {j \<in> outerClassPoles K p a. p < j} + (i - (ell p K a - 2))"
        using dS[OF fE] dP[of a "i - (ell p K a - 2)"] by linarith
      also have "\<dots> = i" using cE big by linarith
      finally show ?thesis .
    qed
  qed
  obtain k where k: "K = 40 * k" using assms(2) by (elim dvdE)
  have ct: "card (tailPoles K) = hof K" by (simp add: tailPoles_def k hof_def Nof_def)
  have sub: "outerClassPoles K p a \<subseteq> tailPoles K"
    by (auto simp: outerClassPoles_def tailPoles_def)
  have fC: "finite (outerClassPoles K p a)" by (simp add: outerClassPoles_def)
  have fT: "finite (tailPoles K - outerClassPoles K p a)" by (simp add: tailPoles_def)
  have cd: "card (tailPoles K - outerClassPoles K p a) = hof K - card (outerClassPoles K p a)"
    using card_Diff_subset[OF fC sub] ct by simp
  have cle: "card (outerClassPoles K p a) \<le> hof K" using card_mono[OF _ sub] ct
    by (simp add: tailPoles_def)
  have ic: "i < card (outerClassPoles K p a)" using ia by (simp add: outerCount_def)
  have "degree (outerBasis K p x) \<le> degree (sqPoleProd (tailPoles K - outerClassPoles K p a)) +
    degree (oq K p x)"
    unfolding outerBasis_eq a_def by (rule degree_mult_le)
  also have "\<dots> \<le> (hof K - card (outerClassPoles K p a)) + i" using dS[OF fT] dQ cd
    by linarith
  also have "\<dots> < hof K" using ic cle by linarith
  finally show ?thesis .
qed

text \<open>Helpers for the unimodularity of the outer basis: congruences modulo @{text p} of
  polynomials and of
  Taylor coefficients.  @{text "oroot p a"} is the expansion point of class @{text a} (@{text p}
    for the zero class).\<close>
definition oroot :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "oroot p a = (if a =
  0 then p else a)"

lemma oroot_mod: "oroot p a mod p = a mod p"
  by (simp add: oroot_def)

lemma oroot_add_mod: "(k + oroot p a) mod p = (k + a) mod p"
  by (simp add: oroot_def)

lemma vpGge_tay1:
  assumes p: "prime p" and P: "vpGge p P 1" and r: "vge p r 0"
  shows "vge p (tay P r i) 1"
proof -
  define P' where "P' = Polynomial.smult (1 / of_nat p) P"
  have pp: "P = Polynomial.smult (of_nat p) P'" using p by (simp add: P'_def prime_gt_0_nat)
  have P': "vpGge p P' 0"
  proof -
    have "vge p (1 / of_nat p * Polynomial.coeff P k) (- 1 + 1)" for k
      using vge_mul[OF p vge_inv_p[OF p], of "Polynomial.coeff P k" 1] P by (simp add: vpGge_iff)
    thus ?thesis by (simp add: vpGge_iff P'_def)
  qed
  have "vge p (of_nat p * tay P' r i) (1 + 0)"
    by (rule vge_mul[OF p vge_p_self[OF p] vge_tay[OF p P' r]])
  thus ?thesis using pp tay_smult by simp
qed

lemma tay_diff: "tay (P - Q) r i = tay P r i - tay Q r i"
  using tay_add[of "P - Q" Q r i] by simp

lemma vpGge_diff: "prime p \<Longrightarrow> vpGge p A b \<Longrightarrow>
  vpGge p B b \<Longrightarrow> vpGge p (A - B) b"
  using vpGge_add[of p A b "- B"] vpGge_neg[of p B b] by simp

lemma vpGge_prod_diff:
  assumes p: "prime p" and S: "finite S"
    and hf: "\<And>j. j \<in> S \<Longrightarrow>
      vpGge p (f j) 0" and hg: "\<And>j. j \<in> S \<Longrightarrow> vpGge p (g j) 0"
    and hfg: "\<And>j. j \<in> S \<Longrightarrow> vpGge p (f j - g j) 1"
  shows "vpGge p ((\<Prod> j \<in> S. f j) - (\<Prod> j \<in> S. g j)) 1"
  using S hf hg hfg
proof (induction S rule: finite_induct)
  case empty
  show ?case using vpGge_zero by simp
next
  case (insert x F)
  have IH: "vpGge p ((\<Prod> j \<in> F. f j) - (\<Prod> j \<in> F. g j)) 1" using insert by blast
  have fF: "vpGge p (\<Prod> j \<in> F. f j) 0"
    using vpGge_prod[OF p insert(1), of f "\<lambda>_. 0"] insert(4) by force
  have gx: "vpGge p (g x) 0" using insert(5) by blast
  have fgx: "vpGge p (f x - g x) 1" using insert(6) by blast
  have e: "(\<Prod> j \<in> insert x F. f j) - (\<Prod> j \<in> insert x F. g j) =
      (f x - g x) * (\<Prod> j \<in> F. f j) + g x * ((\<Prod> j \<in> F. f j) - (\<Prod> j \<in>
        F. g j))"
    using insert(1,2) by (simp add: algebra_simps)
  have t1: "vpGge p ((f x - g x) * (\<Prod> j \<in> F. f j)) (1 + 0)"
    by (rule vpGge_mul[OF p fgx fF])
  have t2: "vpGge p (g x * ((\<Prod> j \<in> F. f j) - (\<Prod> j \<in> F. g j))) (0 + 1)"
    by (rule vpGge_mul[OF p gx IH])
  show ?case unfolding e using vpGge_add[OF p] t1 t2 by simp
qed

lemma sq_cong_mod:
  assumes "prime p" "j mod p = a mod p \<or> (j + a) mod p = 0"
  shows "vge p (of_nat j ^ 2 - of_nat a ^ 2) 1"
proof -
  have p: "prime p" using assms(1) .
  have j: "j mod p = a mod p \<or> (j + a) mod p = 0" using assms(2) .
  have "int p dvd (int j - int a) * (int j + int a)"
  proof (cases "j mod p = a mod p")
    case True
    hence "int j mod int p = int a mod int p" by (metis of_nat_mod)
    hence "int p dvd int j - int a" by (simp add: mod_eq_dvd_iff)
    thus ?thesis by simp
  next
    case False
    hence "(j + a) mod p = 0" using j by simp
    hence "p dvd j + a" by (rule mod_0_imp_dvd)
    hence "int p dvd int j + int a" by (simp flip: of_nat_add)
    thus ?thesis by simp
  qed
  then obtain w where w: "(int j - int a) * (int j + int a) = int p * w" by (elim dvdE)
  have e: "(of_nat j ^ 2 - of_nat a ^ 2 :: rat) = of_nat p * of_int w"
  proof -
    have "(of_nat j ^ 2 - of_nat a ^ 2 :: rat) = of_int ((int j - int a) * (int j + int a))"
      by (simp add: power2_eq_square algebra_simps)
    thus ?thesis unfolding w by simp
  qed
  have "vge p (of_nat p * of_int w) (1 + 0)"
    by (rule vge_mul[OF p vge_p_self[OF p] vge_of_int[OF p]])
  thus ?thesis unfolding e by simp
qed

lemma sq_unit_mod:
  assumes p: "prime p" and nc: "\<not> (k mod p = s mod p \<or> (k + s) mod p = 0)"
  shows "(of_nat k ^ 2 - of_nat s ^ 2 :: rat) \<noteq> 0 \<and>
    vp p (of_nat k ^ 2 - of_nat s ^ 2) = 0"
proof -
  have pr: "prime (int p)" using p by (simp add: prime_nat_int_transfer)
  define z :: int where "z = (int k - int s) * (int k + int s)"
  have zq: "(of_nat k ^ 2 - of_nat s ^ 2 :: rat) = of_int z"
    by (simp add: z_def power2_eq_square algebra_simps)
  have "\<not> int p dvd (int k - int s)"
  proof
    assume "int p dvd (int k - int s)"
    hence "int k mod int p = int s mod int p" using mod_eq_dvd_iff by blast
    hence "int (k mod p) = int (s mod p)" using zmod_int[of k p] zmod_int[of s p] by simp
    hence "k mod p = s mod p" by simp
    thus False using nc by blast
  qed
  moreover have "\<not> int p dvd (int k + int s)"
  proof
    assume "int p dvd (int k + int s)"
    hence "p dvd k + s" using of_nat_add[symmetric] by presburger
    hence "(k + s) mod p = 0" by simp
    thus False using nc by meson
  qed
  ultimately have nz: "\<not> int p dvd z" unfolding z_def using prime_dvd_mult_iff[OF pr] by blast
  hence "z \<noteq> 0" by auto
  thus ?thesis unfolding zq using nz by (simp add: vp_def qmultiplicity_of_int
    not_dvd_imp_multiplicity_0)
qed

lemma class_disjoint_m:
  assumes m: "2 * mHalf p + 1 = p" and a: "a \<le> mHalf p" and c: "c \<le>
    mHalf p" and ac: "a \<noteq> c"
  shows "outerClassPoles K p a \<inter> outerClassPoles K p c = {}"
proof -
  { fix j assume ja: "j \<in> outerClassPoles K p a" and jc: "j \<in> outerClassPoles K p c"
    have "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
      by (rule res_class[OF a m]) (use ja in \<open>simp add: mem_class\<close>)
    moreover have "j mod p = c \<or> (1 \<le> c \<and> j mod p = p - c)"
      by (rule res_class[OF c m]) (use jc in \<open>simp add: mem_class\<close>)
    ultimately have False using a c ac m by (elim disjE conjE; linarith) }
  thus ?thesis by blast
qed

lemma class_prod_cong:
  assumes p: "prime p" and S: "S \<subseteq> outerClassPoles K p c"
  shows "vpGge p (sqPoleProd S - (pX - [:- (of_nat (oroot p c) ^ 2):]) ^ card S) 1"
proof -
  have fS: "finite S" using S finite_subset by (fastforce simp: outerClassPoles_def)
  have e: "(pX - [:- (of_nat (oroot p c) ^ 2):]) ^ card S = (\<Prod> j \<in>
    S. pX - [:- (of_nat (oroot p c) ^ 2):])"
    using prod_constant by simp
  have r: "vpGge p (pX - [:- (of_nat (oroot p c) ^ 2):]) 0"
    using vpGge_diff[OF p vpGge_pX vpGge_C[OF vge_neg[OF vge_pow[OF p vge_of_nat[OF p]]]]] by simp
  have d: "vpGge p ((pX + [:of_nat j ^ 2:]) - (pX - [:- (of_nat (oroot p c) ^ 2):])) 1"
    if j: "j \<in> S" for j
  proof -
    have jm: "j mod p = oroot p c mod p \<or> (j + oroot p c) mod p = 0"
      using j S oroot_mod oroot_add_mod by (auto simp: outerClassPoles_def)
    have v: "vge p (of_nat j ^ 2 - of_nat (oroot p c) ^ 2) 1" by (rule sq_cong_mod[OF p jm])
    have "(pX + [:of_nat j ^ 2:]) - (pX - [:- (of_nat (oroot p c) ^ 2):]) =
      [:of_nat j ^ 2 - of_nat (oroot p c) ^ 2:]"
      by simp
    thus ?thesis using vpGge_C[OF v] by simp
  qed
  show ?thesis unfolding e sqPoleProd_def using vpGge_prod_diff[OF p fS vpGge_pX_plus_sq[OF p] r d]
    by fast
qed

lemma oq_cong:
  assumes p: "prime p"
    and cH: "1 \<le> fst x \<Longrightarrow>
      card {j \<in> outerClassPoles K p (fst x). p < j} = ell p K (fst x) - 2"
  shows "vpGge p (oq K p x - (pX - [:- (of_nat (oroot p (fst x)) ^ 2):]) ^ snd x) 1"
proof -
  obtain a i where x: "x = (a, i)" by (cases x)
  have ePa: "pX - [:- (of_nat (oroot p a) ^ 2):] = pX + [:of_nat (oroot p a) ^ 2:]" by simp
  show ?thesis
  proof (cases "a = 0 \<or> i < ell p K a - 2")
    case True
    have "oq K p x = (pX + [:of_nat (oroot p a) ^ 2:]) ^ i"
      using True unfolding x oq_def Let_def fst_conv snd_conv by (auto simp: oroot_def)
    thus ?thesis unfolding x fst_conv snd_conv ePa using vpGge_zero by simp
  next
    case False
    hence a1: "1 \<le> a" and il: "ell p K a - 2 \<le> i" by auto
    define H where "H = {j \<in> outerClassPoles K p a. p < j}"
    have cH': "card H = ell p K a - 2" using cH a1 unfolding H_def x fst_conv by blast
    have oqe: "oq K p x = sqPoleProd H * (pX + [:of_nat a ^ 2:]) ^ (i - (ell p K a - 2))"
      using False unfolding x oq_def Let_def H_def fst_conv snd_conv by simp
    have oa: "oroot p a = a" using a1 unfolding oroot_def by simp
    have ePa2: "pX - [:- (of_nat a ^ 2):] = (pX + [:of_nat a ^ 2:] :: rat poly)" by simp
    have ii: "card H + (i - (ell p K a - 2)) = i" using cH' il by fastforce
    have pe: "(pX - [:- (of_nat (oroot p (fst x)) ^ 2):]) ^ snd x =
        (pX - [:- (of_nat (oroot p a) ^ 2):]) ^ card H * (pX + [:of_nat a ^ 2:]) ^ (i - (ell p K a -
          2))"
      unfolding x fst_conv snd_conv oa ePa2
        using power_add[of "pX + [:of_nat a ^ 2:]" "card H" "i - (ell p K a - 2)"] ii by simp
    have HC: "H \<subseteq> outerClassPoles K p a" unfolding H_def by blast
    have d: "vpGge p (sqPoleProd H - (pX - [:- (of_nat (oroot p a) ^ 2):]) ^ card H) 1"
      by (rule class_prod_cong[OF p HC])
    have "vpGge p ((sqPoleProd H - (pX - [:- (of_nat (oroot p a) ^ 2):]) ^ card H) * (pX +
      [:of_nat a ^ 2:]) ^ (i - (ell p K a - 2))) (1 + 0)"
      by (rule vpGge_mul[OF p d vpGge_pow0[OF p vpGge_pX_plus_sq[OF p]]])
    thus ?thesis unfolding oqe pe by (simp add: algebra_simps)
  qed
qed

lemma oq_cong_hyp:
  assumes p: "prime p" and H: "OuterHyp K p" and x: "x \<in> set (outer_idx K p)"
  shows "vpGge p (oq K p x - (pX - [:- (of_nat (oroot p (fst x)) ^ 2):]) ^ snd x) 1"
proof (rule oq_cong[OF p])
  assume a1: "1 \<le> fst x"
  have am: "fst x \<le> mHalf p" using x mem_outer_idx by blast
  show "card {j \<in> outerClassPoles K p (fst x). p < j} = ell p K (fst x) - 2"
    using card_class_high_add_two[OF p H a1 am] by simp
qed

text \<open>Below the diagonal of the Taylor matrix of the outer basis the entries are divisible
  by @{text p}.\<close>
lemma outer_tay_below:
  assumes p: "prime p" and m: "2 * mHalf p + 1 = p"
    and oqc: "vpGge p (oq K p (a, j) - (pX - [:- (of_nat (oroot p a) ^ 2):]) ^ j) 1"
    and a: "a \<le> mHalf p" and c: "c \<le> mHalf p" and ci: "i < outerCount K p c"
    and lex: "c < a \<or> (c = a \<and> i < j)"
  shows "vge p (tay (outerBasis K p (a, j)) (- (of_nat (oroot p c) ^ 2)) i) 1"
proof -
  let ?r = "- (of_nat (oroot p c) ^ 2) :: rat"
  have r0: "vge p ?r 0" by (rule vge_neg[OF vge_pow[OF p vge_of_nat[OF p]]])
  have E: "outerBasis K p (a, j) = sqPoleProd (tailPoles K - outerClassPoles K p a) * oq K p (a, j)"
    using outerBasis_eq[of K p "(a, j)"] by simp
  have "\<exists>E'. vpGge p (outerBasis K p (a, j) - E') 1 \<and> tay E' ?r i = 0"
  proof (cases "c < a")
    case True
    have dj: "outerClassPoles K p c \<subseteq> tailPoles K - outerClassPoles K p a"
      using class_disjoint_m[OF m a c] True unfolding tailPoles_def outerClassPoles_def by fastforce
    define D where "D = tailPoles K - outerClassPoles K p a - outerClassPoles K p c"
    define R where "R = sqPoleProd D * oq K p (a, j)"
    have u: "tailPoles K - outerClassPoles K p a = outerClassPoles K p c \<union> D" using dj
      unfolding D_def by blast
    have fC: "finite (outerClassPoles K p c)" and fD: "finite D"
      unfolding D_def tailPoles_def outerClassPoles_def by auto
    have dD: "outerClassPoles K p c \<inter> D = {}" unfolding D_def by blast
    have sp: "sqPoleProd (tailPoles K - outerClassPoles K p a) =
      sqPoleProd (outerClassPoles K p c) * sqPoleProd D"
      unfolding u using sqPoleProd_union[OF fC fD dD] by blast
    have d: "vpGge p (sqPoleProd (outerClassPoles K p c) - (pX - [:?r:]) ^ outerCount K p c) 1"
      using class_prod_cong[OF p subset_refl, of K c] unfolding outerCount_def by blast
    have R0: "vpGge p R 0" unfolding R_def
      by (rule vpGge_mul0[OF p vpGge_sqPoleProd[OF p] oq_vge[OF p]])
    have "vpGge p ((sqPoleProd (outerClassPoles K p c) - (pX - [:?r:]) ^ outerCount K p c) * R) (1 +
      0)"
      by (rule vpGge_mul[OF p d R0])
    moreover have "outerBasis K p (a, j) - (pX - [:?r:]) ^ outerCount K p c * R =
        (sqPoleProd (outerClassPoles K p c) - (pX - [:?r:]) ^ outerCount K p c) * R"
      unfolding E sp R_def by (simp add: algebra_simps)
    moreover have "tay ((pX - [:?r:]) ^ outerCount K p c * R) ?r i = 0"
      by (rule tay_pow_mult_lt[OF ci])
    ultimately show ?thesis by force
  next
    case False
    hence ca: "c = a" and ij: "i < j" using lex by auto
    define P where "P = sqPoleProd (tailPoles K - outerClassPoles K p a)"
    have P0: "vpGge p P 0" unfolding P_def by (rule vpGge_sqPoleProd[OF p])
    have "vpGge p (P * (oq K p (a, j) - (pX - [:?r:]) ^ j)) (0 + 1)"
      using vpGge_mul[OF p P0 oqc] ca by blast
    moreover have "outerBasis K p (a, j) - (pX - [:?r:]) ^ j * P =
      P * (oq K p (a, j) - (pX - [:?r:]) ^ j)"
      unfolding E P_def by (simp add: algebra_simps)
    moreover have "tay ((pX - [:?r:]) ^ j * P) ?r i = 0" by (rule tay_pow_mult_lt[OF ij])
    ultimately show ?thesis by force
  qed
  then obtain E' where E1: "vpGge p (outerBasis K p (a, j) - E') 1" and E2: "tay E' ?r i = 0"
    by blast
  have "vge p (tay (outerBasis K p (a, j) - E') ?r i) 1" by (rule vpGge_tay1[OF p E1 r0])
  thus ?thesis using E2 tay_diff by simp
qed

text \<open>The diagonal entries of the Taylor matrix of the outer basis are @{text p}-adic
  units.\<close>
lemma outer_tay_diag:
  assumes p: "prime p"
    and oqc: "vpGge p (oq K p (a, j) - (pX - [:- (of_nat (oroot p a) ^ 2):]) ^ j) 1"
  shows "tay (outerBasis K p (a, j)) (- (of_nat (oroot p a) ^ 2)) j \<noteq> 0 \<and>
         vp p (tay (outerBasis K p (a, j)) (- (of_nat (oroot p a) ^ 2)) j) = 0"
proof -
  let ?r = "- (of_nat (oroot p a) ^ 2) :: rat"
  define P where "P = sqPoleProd (tailPoles K - outerClassPoles K p a)"
  have E: "outerBasis K p (a, j) = P * oq K p (a, j)" unfolding P_def
    using outerBasis_eq[of K p "(a, j)"] by simp
  have r0: "vge p ?r 0" by (rule vge_neg[OF vge_pow[OF p vge_of_nat[OF p]]])
  have P0: "vpGge p P 0" unfolding P_def by (rule vpGge_sqPoleProd[OF p])
  have d1: "vpGge p (P * (oq K p (a, j) - (pX - [:?r:]) ^ j)) (0 + 1)"
    by (rule vpGge_mul[OF p P0 oqc])
  have d2: "outerBasis K p (a, j) - (pX - [:?r:]) ^ j * P = P * (oq K p (a, j) - (pX - [:?r:]) ^ j)"
    unfolding E by (simp add: algebra_simps)
  define u where "u = tay (outerBasis K p (a, j) - (pX - [:?r:]) ^ j * P) ?r j"
  have u1: "vge p u 1" unfolding u_def d2 using vpGge_tay1[OF p _ r0] d1 by simp
  have t0: "tay ((pX - [:?r:]) ^ j * P) ?r j = poly P ?r"
    using tay_pow_mult[of ?r j P 0] tay_0_eq_poly[of P ?r] by simp
  have fT: "finite (tailPoles K - outerClassPoles K p a)" unfolding tailPoles_def by blast
  have fac: "?r + of_nat k ^ 2 \<noteq> 0 \<and> vp p (?r + of_nat k ^ 2) = 0"
    if k: "k \<in> tailPoles K - outerClassPoles K p a" for k
  proof -
    have nc: "\<not> (k mod p = oroot p a mod p \<or> (k + oroot p a) mod p = 0)"
      using k oroot_mod oroot_add_mod unfolding tailPoles_def outerClassPoles_def by auto
    have e: "?r + of_nat k ^ 2 = of_nat k ^ 2 - of_nat (oroot p a) ^ 2" by simp
    show ?thesis unfolding e by (rule sq_unit_mod[OF p nc])
  qed
  have pP: "poly P ?r = (\<Prod> k \<in> tailPoles K - outerClassPoles K p a. ?r + of_nat k ^ 2)"
    unfolding P_def sqPoleProd_def using poly_prod poly_monom by (simp add: poly_prod poly_monom)
  have w0: "poly P ?r \<noteq> 0" unfolding pP using fac fT by simp
  have w1: "vp p (poly P ?r) = 0"
  proof -
    have "vp p (poly P ?r) = (\<Sum> k \<in>
      tailPoles K - outerClassPoles K p a. vp p (?r + of_nat k ^ 2))"
      unfolding pP using vp_prod_rat[OF p fT] fac by presburger
    also have "\<dots> = 0" using fac by simp
    finally show ?thesis .
  qed
  have tsum: "tay (outerBasis K p (a, j)) ?r j = poly P ?r + u" unfolding u_def tay_diff t0 by simp
  show ?thesis
  proof (cases "u = 0")
    case True
    thus ?thesis using tsum w0 w1 by simp
  next
    case False
    have lt: "vp p (poly P ?r) < vp p u" using u1 False w1 unfolding vge_def by simp
    have "poly P ?r + u \<noteq> 0 \<and> vp p (poly P ?r + u) = vp p (poly P ?r)"
      by (rule vp_add_eq_of_lt[OF p w0 False lt])
    thus ?thesis using tsum w1 by simp
  qed
qed

text \<open>(4.11): the outer basis is @{text "\<int>_p"}-unimodular,
  by the Taylor-matrix criterion.  Row @{text "(a, i)"} is expanded at
  @{text "-a^2"} (at @{text "-p^2"} for the zero class);
    below the diagonal the entries are divisible by @{text p} (the poles
  @{text "j > p"} of a class satisfy @{text "j^2 \<equiv> a^2"}),
    and the diagonal entries are units.\<close>
theorem outerBasis_unimodular:
  assumes p: "prime p" and K: "40 dvd K" and H: "OuterHyp K p"
  defines "B \<equiv> Matrix.mat (hof K) (hof K) (\<lambda>(x,
    d). Polynomial.coeff (outerBasis K p (outer_idx K p ! x)) d)"
  shows "Determinant.det B \<noteq> 0 \<and> vp p (Determinant.det B) = 0"
proof -
  define h where "h = hof K"
  define idx where "idx = outer_idx K p"
  define rt where "rt = (\<lambda>y. if fst (idx ! y) =
    0 then - (of_nat p ^ 2) else - (of_nat (fst (idx ! y)) ^ 2) :: rat)"
  define od where "od = (\<lambda>y. snd (idx ! y))"
  define V :: "rat mat" where "V = Matrix.mat h h (\<lambda>(d, y). tay (pX ^ d) (rt y) (od y))"
  define T :: "rat mat" where "T = B * V"
  have len: "length idx = h" by (simp add: idx_def h_def length_outer_idx[OF p K H])
  have Bc: "B \<in> carrier_mat h h" and Vc: "V \<in> carrier_mat h h"
    by (simp_all add: B_def V_def h_def)
  have Tentry: "\<And>x y. x < h \<Longrightarrow> y < h \<Longrightarrow>
    T $$ (x, y) = tay (outerBasis K p (idx ! x)) (rt y) (od y)"
  proof -
    fix x y assume x: "x < h" and y: "y < h"
    have mem: "idx ! x \<in> set (outer_idx K p)" using x len unfolding idx_def by fastforce
    have dg: "degree (outerBasis K p (idx ! x)) < h" using degree_outerBasis_lt[OF p K H mem]
      unfolding h_def by meson
    have "dim_row B = h" "dim_col B = h" "dim_row V = h" "dim_col V = h" using Bc Vc by auto
    with x y have "T $$ (x, y) = (\<Sum> d \<in> {0..<h}. B $$ (x, d) * V $$ (d, y))"
      unfolding T_def scalar_prod_def by (auto simp: scalar_prod_def index_mult_mat)
    also have "\<dots> = (\<Sum> d < h. Polynomial.coeff (outerBasis K p (idx ! x)) d *
      tay (pX ^ d) (rt y) (od y))"
    proof (rule sum.cong)
      show "{0..<h} = {..<h}" by fastforce
      fix d assume d: "d \<in> {..<h}"
      show "B $$ (x, d) * V $$ (d, y) = Polynomial.coeff (outerBasis K p (idx ! x)) d *
        tay (pX ^ d) (rt y) (od y)"
        using x y d unfolding B_def V_def idx_def h_def by force
    qed
    also have "\<dots> = tay (outerBasis K p (idx ! x)) (rt y) (od y)"
      by (rule tay_eq_sum[OF dg, symmetric])
    finally show "T $$ (x, y) = tay (outerBasis K p (idx ! x)) (rt y) (od y)" .
  qed
  have below: "\<And>x y. y < x \<Longrightarrow> x < h \<Longrightarrow> vge p (T $$ (x, y)) 1"
  proof -
    fix x y assume yx: "y < x" and x: "x < h"
    have y: "y < h" using yx x by simp
    obtain a j where ax: "idx ! x = (a, j)" by (cases "idx ! x")
    obtain c i where cy: "idx ! y = (c, i)" by (cases "idx ! y")
    have mx: "idx ! x \<in> set (outer_idx K p)" and my: "idx ! y \<in> set (outer_idx K p)"
      using x y len unfolding idx_def by auto
    have am: "a \<le> mHalf p" using mx ax mem_outer_idx by simp
    have cm: "c \<le> mHalf p" and ci: "i < outerCount K p c" using my cy mem_outer_idx by auto
    have lex: "c < a \<or> (c = a \<and> i < j)" using outer_idx_lex[of y x K p] yx x len ax cy
      unfolding idx_def by simp
    have m: "2 * mHalf p + 1 = p" using outer_facts[OF p H] by blast
    have oqc: "vpGge p (oq K p (a, j) - (pX - [:- (of_nat (oroot p a) ^ 2):]) ^ j) 1"
      using oq_cong_hyp[OF p H mx] ax by simp
    have rty: "rt y = - (of_nat (oroot p c) ^ 2)" unfolding rt_def cy oroot_def by simp
    have Te: "T $$ (x, y) = tay (outerBasis K p (a, j)) (- (of_nat (oroot p c) ^ 2)) i"
      using Tentry[OF x y] ax rty cy unfolding od_def by simp
    show "vge p (T $$ (x, y)) 1" unfolding Te by (rule outer_tay_below[OF p m oqc am cm ci lex])
  qed
  have unit: "\<And>x. x < h \<Longrightarrow> T $$ (x, x) \<noteq> 0 \<and> vp p (T $$ (x, x)) = 0"
  proof -
    fix x assume x: "x < h"
    obtain a j where ax: "idx ! x = (a, j)" by (cases "idx ! x")
    have mx: "idx ! x \<in> set (outer_idx K p)" using x len unfolding idx_def by simp
    have oqc: "vpGge p (oq K p (a, j) - (pX - [:- (of_nat (oroot p a) ^ 2):]) ^ j) 1"
      using oq_cong_hyp[OF p H mx] ax by simp
    have rtx: "rt x = - (of_nat (oroot p a) ^ 2)" unfolding rt_def ax oroot_def by simp
    have Te: "T $$ (x, x) = tay (outerBasis K p (a, j)) (- (of_nat (oroot p a) ^ 2)) j"
      using Tentry[OF x x] ax rtx unfolding od_def by simp
    show "T $$ (x, x) \<noteq> 0 \<and> vp p (T $$ (x, x)) = 0" unfolding Te
      by (rule outer_tay_diag[OF p oqc])
  qed
  have Bi: "\<And>x d. x < h \<Longrightarrow> d < h \<Longrightarrow> vge p (B $$ (x, d)) 0"
    using vpGge_outerBasis[OF p] by (auto simp: B_def h_def vpGge_iff)
  have Vi: "\<And>d y. d < h \<Longrightarrow> y < h \<Longrightarrow> vge p (V $$ (d, y)) 0"
  proof -
    fix d y assume d: "d < h" and y: "y < h"
    have sq: "vge p (- (of_nat m ^ 2)) 0" for m by (rule vge_neg[OF vge_pow[OF p vge_of_nat[OF p]]])
    have rt0: "vge p (rt y) 0" by (simp add: rt_def sq)
    have "vge p (of_nat (d choose od y) * rt y ^ (d - od y)) (0 + 0)"
      by (rule vge_mul[OF p vge_of_nat[OF p] vge_pow[OF p rt0]])
    hence vf: "vge p (of_nat (d choose od y) * rt y ^ (d - od y)) 0" by simp
    have "V $$ (d, y) = tay (pX ^ d) (rt y) (od y)" using d y by (simp add: V_def)
    thus "vge p (V $$ (d, y)) 0" unfolding tay_pX_pow using vf by (simp add: vge_zero)
  qed
  show ?thesis
    unfolding h_def[symmetric]
    by (rule unimodular_criterion[OF p Bc Vc Bi Vi]) (use below unit in \<open>simp_all add:
      T_def[symmetric]\<close>)
qed

lemma muModPoly_eq_sum:
  assumes "degree Q \<le> N"
  shows "muModPoly p Q = (\<Sum> e \<le>
    N. Polynomial.coeff Q e * (muMono e - cCorr p e / of_nat p))"
  unfolding muModPoly_def
proof (rule sum.mono_neutral_left)
  show "finite {..N}" by force
  show "{..degree Q} \<subseteq> {..N}" using assms by blast
  show "\<forall>i\<in>{..N} - {..degree Q}. Polynomial.coeff Q i * (muMono i - cCorr p i /
    of_nat p) = 0" by (simp add: coeff_eq_0)
qed

lemma muModPoly_add: "muModPoly p (P + Q) = muModPoly p P + muModPoly p Q"
proof -
  define N where "N = max (degree P) (degree Q)"
  have "degree (P + Q) \<le> N" "degree P \<le> N" "degree Q \<le> N"
    using degree_add_le_max[of P Q] unfolding N_def by auto
  hence "muModPoly p (P + Q) = (\<Sum> e \<le>
    N. Polynomial.coeff (P + Q) e * (muMono e - cCorr p e / of_nat p))"
    "muModPoly p P = (\<Sum> e \<le> N. Polynomial.coeff P e * (muMono e - cCorr p e / of_nat p))"
    "muModPoly p Q = (\<Sum> e \<le> N. Polynomial.coeff Q e * (muMono e - cCorr p e / of_nat p))"
    using muModPoly_eq_sum by auto
  moreover have "(\<Sum> e \<le> N. Polynomial.coeff (P + Q) e * (muMono e - cCorr p e /
    of_nat p)) =
      (\<Sum> e \<le> N. Polynomial.coeff P e * (muMono e - cCorr p e / of_nat p)) + (\<Sum> e \<le>
        N. Polynomial.coeff Q e * (muMono e - cCorr p e / of_nat p))"
    by (simp add: distrib_right sum.distrib)
  ultimately show ?thesis by argo
qed

lemma muModPoly_smult: "muModPoly p (Polynomial.smult c P) = c * muModPoly p P"
proof -
  have "muModPoly p (Polynomial.smult c P) = (\<Sum> e \<le>
    degree P. Polynomial.coeff (Polynomial.smult c P) e * (muMono e - cCorr p e / of_nat p))"
    using degree_smult_le[of c P] muModPoly_eq_sum by blast
  moreover have "muModPoly p P = (\<Sum> e \<le>
    degree P. Polynomial.coeff P e * (muMono e - cCorr p e / of_nat p))"
    using muModPoly_eq_sum by fast
  ultimately show ?thesis by (force simp: sum_distrib_left mult.assoc)
qed

lemma muXmod_add: "muXmod p S (P + Q) = muXmod p S P + muXmod p S Q"
  unfolding muXmod_eq by (force simp: poly_div_add_left muModPoly_add sqResidue_add smult_add_left
    sum.distrib algebra_simps)

lemma muXmod_C_mul: "muXmod p S ([:c:] * P) = [:c:] * muXmod p S P"
  unfolding muXmod_eq by (fastforce simp: div_smult_left muModPoly_smult sqResidue_smult
    smult_add_right smult_smult smult_sum_right)

lemma muXmod_zero: "muXmod p S 0 = 0"
  using muXmod_C_mul[of p S 0 0] by simp

lemma muXmod_sum: "muXmod p S (\<Sum> i \<in> I. f i) = (\<Sum> i \<in> I. muXmod p S (f i))"
proof (induction I rule: infinite_finite_induct)
  case (infinite A)
  thus ?case using muXmod_zero by simp
next
  case empty
  thus ?case using muXmod_zero by auto
next
  case (insert x F)
  thus ?case using muXmod_add by force
qed

text \<open>The Gram identity with the length and degree facts as hypotheses,
  so that it also applies for @{text "p > K"}.\<close>
lemma outerGram_eq_conj_gen:
  assumes lenH: "length (outer_idx K p) = hof K"
    and dgH: "\<And>x. x \<in> set (outer_idx K p) \<Longrightarrow>
      degree (outerBasis K p x) < hof K"
  defines "B \<equiv> Matrix.mat (hof K) (hof K) (\<lambda>(x,
    d). Polynomial.coeff (outerBasis K p (outer_idx K p ! x)) d)"
  shows "outerGram K p = map_mat (\<lambda>q. [:q:]) B * Aout K p *
    transpose_mat (map_mat (\<lambda>q. [:q:]) B)"
proof -
  let ?h = "hof K" and ?idx = "outer_idx K p"
  let ?Q = "map_mat (\<lambda>q. [:q:]) B"
  have len: "length ?idx = ?h" by (rule lenH)
  have dB: "dim_row B = ?h" "dim_col B = ?h" unfolding B_def by auto
  have dG: "dim_row (Aout K p) = ?h" "dim_col (Aout K p) = ?h" unfolding Aout_def by auto
  have sm: "muXmod p S (Polynomial.smult a P) = Polynomial.smult a (muXmod p S P)" for S a P
    using muXmod_C_mul[of p S a P] by fastforce
  have qe: "outerBasis K p (?idx ! x) = (\<Sum> k < ?h. Polynomial.smult (B $$ (x, k)) (pX ^ k))"
    if x: "x < ?h" for x
  proof -
    have mem: "?idx ! x \<in> set ?idx" using x len by fastforce
    have dg: "degree (outerBasis K p (?idx ! x)) \<le> ?h - 1"
      using dgH[OF mem] by force
    have e: "{..?h - 1} = {..<?h}" using x by fastforce
    have "outerBasis K p (?idx ! x) =
        (\<Sum> k \<le> ?h - 1. Polynomial.monom (Polynomial.coeff (outerBasis K p (?idx ! x)) k)
          k)"
      by (rule sym[OF poly_as_sum_of_monoms'[OF dg]])
    also have "\<dots> = (\<Sum> k < ?h. Polynomial.monom (Polynomial.coeff (outerBasis K p (?idx !
      x)) k) k)"
      unfolding e ..
    also have "\<dots> = (\<Sum> k < ?h. Polynomial.smult (B $$ (x, k)) (pX ^ k))"
    proof (rule sum.cong[OF refl])
      fix k assume k: "k \<in> {..<?h}"
      show "Polynomial.monom (Polynomial.coeff (outerBasis K p (?idx ! x)) k) k =
        Polynomial.smult (B $$ (x, k)) (pX ^ k)"
        unfolding pX_pow_monom smult_monom using x k unfolding B_def by force
    qed
    finally show ?thesis .
  qed
  have pq: "Dm (Nof K) ^ 6 * outerBasis K p (?idx ! x) * outerBasis K p (?idx ! y) =
      (\<Sum> k < ?h. \<Sum> l < ?h. Polynomial.smult (B $$ (x, k) * B $$ (y,
        l)) (Dm (Nof K) ^ 6 * pX ^ (k + l)))"
    if x: "x < ?h" and y: "y < ?h" for x y
  proof -
    have pq0: "outerBasis K p (?idx ! x) * outerBasis K p (?idx ! y) = (\<Sum> k < ?h. \<Sum> l <
      ?h.
        Polynomial.smult (B $$ (x, k)) (pX ^ k) * Polynomial.smult (B $$ (y, l)) (pX ^ l))"
      unfolding qe[OF x] qe[OF y] by (rule sum_product)
    have "Dm (Nof K) ^ 6 * outerBasis K p (?idx ! x) * outerBasis K p (?idx ! y) =
        Dm (Nof K) ^ 6 * (outerBasis K p (?idx ! x) * outerBasis K p (?idx ! y))"
          by (simp only: mult.assoc)
    also have "\<dots> = (\<Sum> k < ?h. \<Sum> l <
      ?h. Polynomial.smult (B $$ (x, k) * B $$ (y, l)) (Dm (Nof K) ^ 6 * pX ^ (k + l)))"
      unfolding pq0 sum_distrib_left
    proof (intro sum.cong refl)
      fix k l
      show "Dm (Nof K) ^ 6 * (Polynomial.smult (B $$ (x, k)) (pX ^ k) * Polynomial.smult (B $$ (y,
        l)) (pX ^ l)) =
          Polynomial.smult (B $$ (x, k) * B $$ (y, l)) (Dm (Nof K) ^ 6 * pX ^ (k + l))"
            by (force simp: power_add mult_ac)
    qed
    finally show ?thesis .
  qed
  have entry: "outerGram K p $$ (x, y) = (?Q * Aout K p * transpose_mat ?Q) $$ (x, y)"
    if x: "x < ?h" and y: "y < ?h" for x y
  proof -
    have "outerGram K p $$ (x, y) =
        muXmod p {1..K} (Dm (Nof K) ^ 6 * outerBasis K p (?idx ! x) * outerBasis K p (?idx ! y))"
      using x y len unfolding outerGram_def Let_def by force
    also have "\<dots> = (\<Sum> k < ?h. \<Sum> l <
      ?h. [:B $$ (x, k):] * Aout K p $$ (k, l) * [:B $$ (y, l):])"
      unfolding pq[OF x y] muXmod_sum sm
    proof (intro sum.cong refl)
      fix k l assume "k \<in> {..<?h}" "l \<in> {..<?h}"
      thus "Polynomial.smult (B $$ (x, k) * B $$ (y,
        l)) (muXmod p {1..K} (Dm (Nof K) ^ 6 * pX ^ (k + l))) =
          [:B $$ (x, k):] * Aout K p $$ (k, l) * [:B $$ (y, l):]" unfolding Aout_def
            by (force simp: mult_ac)
    qed
    also have "\<dots> = (?Q * Aout K p * transpose_mat ?Q) $$ (x, y)"
    proof -
      have m: "(?Q * Aout K p * transpose_mat ?Q) $$ (x, y) =
          (\<Sum> l < ?h. (\<Sum> k < ?h. [:B $$ (x, k):] * Aout K p $$ (k, l)) * [:B $$ (y, l):])"
        using x y dB dG unfolding scalar_prod_def by (force simp: scalar_prod_def atLeast0LessThan)
      show ?thesis unfolding m sum_distrib_right by (rule sum.swap)
    qed
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule eq_matI)
    fix x y
    assume x: "x < dim_row (?Q * Aout K p * transpose_mat ?Q)" and y: "y <
      dim_col (?Q * Aout K p * transpose_mat ?Q)"
    have xh: "x < ?h" and yh: "y < ?h" using x y dB by auto
    show "outerGram K p $$ (x, y) = (?Q * Aout K p * transpose_mat ?Q) $$ (x, y)"
      by (rule entry[OF xh yh])
  next
    show "dim_row (outerGram K p) = dim_row (?Q * Aout K p * transpose_mat ?Q)" using len dB dG
      unfolding outerGram_def Let_def by force
    show "dim_col (outerGram K p) = dim_col (?Q * Aout K p * transpose_mat ?Q)" using len dB dG
      unfolding outerGram_def Let_def by force
  qed
qed

lemma outerGram_eq_conj:
  assumes p: "prime p" and K: "40 dvd K" and H: "OuterHyp K p"
  defines "B \<equiv> Matrix.mat (hof K) (hof K) (\<lambda>(x,
    d). Polynomial.coeff (outerBasis K p (outer_idx K p ! x)) d)"
  shows "outerGram K p = map_mat (\<lambda>q. [:q:]) B * Aout K p *
    transpose_mat (map_mat (\<lambda>q. [:q:]) B)"
  unfolding B_def by (rule outerGram_eq_conj_gen[OF length_outer_idx[OF p K H]
    degree_outerBasis_lt[OF p K H]])

lemma gammaOut_eq_sum_idx:
  assumes "prime p" "40 dvd K" "OuterHyp K p"
  shows "of_int (gammaOut K p) =
         2 * (\<Sum> x < length (outer_idx K p). wOut K p (outer_idx K p ! x))
         - of_nat (min (rOut K p) (card {x. x < length (outer_idx K p) \<and>
           wOut K p (outer_idx K p ! x) = 0}))"
  using gammaOut_eq_sum[OF assms] by (simp add: sum_list_sum_nth length_filter_conv_card
    atLeast0LessThan)

text \<open>Proposition 4.3: under (4.9),
  @{text "v_p^G(\<Delta>_K) \<ge> \<gamma>_p^out"}.  Assembly: change to the outer basis,
  split @{text "G = A + p^-^1L"}, bound the entries, apply Lemma 4.2, identify the bound.\<close>
lemma vge_mat_mult0:
  assumes p: "prime p" and A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
    and hA: "\<forall>i<n. \<forall>j<n. vge p (A $$ (i,
      j)) 0" and hB: "\<forall>i<n. \<forall>j<n. vge p (B $$ (i, j)) 0"
    and i: "i < n" and j: "j < n"
  shows "vge p ((A * B) $$ (i, j)) 0"
proof -
  have e: "(A * B) $$ (i, j) = (\<Sum> k = 0..<n. A $$ (i, k) * B $$ (k, j))"
    using A B i j by (simp add: scalar_prod_def)
  show ?thesis unfolding e
  proof (rule vge_sum[OF p])
    fix k assume "k \<in> {0..<n}"
    hence k: "k < n" by simp
    show "vge p (A $$ (i, k) * B $$ (k, j)) 0"
      using vge_mul[OF p _ _, of "A $$ (i, k)" 0 "B $$ (k, j)" 0] hA hB i j k by simp
  qed simp
qed
lemma mat_mult_entry:
  assumes "A \<in> carrier_mat n m" "C \<in> carrier_mat m k" "i < n" "j < k"
  shows "(A * C) $$ (i, j) = (\<Sum> l = 0..<m. A $$ (i, l) * C $$ (l, j))"
  using assms by (auto simp: scalar_prod_def)
theorem DeltaK_vpGge_outer:
  assumes p: "prime p" and K: "40 dvd K" and H: "OuterHyp K p"
  shows "vpGge p (DeltaK K) (of_int (gammaOut K p))"
proof -
  define h where "h = hof K"
  define B where "B = Matrix.mat (hof K) (hof K) (\<lambda>(x,
    d). Polynomial.coeff (outerBasis K p (outer_idx K p ! x)) d)"
  define Bp where "Bp = map_mat (\<lambda>q. [:q:]) B"
  define w where "w = (\<lambda>x. wOut K p (outer_idx K p ! x))"
  have len: "length (outer_idx K p) = h" by (simp add: h_def length_outer_idx[OF p K H])
  have Bc: "B \<in> carrier_mat h h" and Bpc: "Bp \<in> carrier_mat h h" and Gc: "GK K \<in>
    carrier_mat h h"
    and Ac: "Aout K p \<in> carrier_mat h h" and OGc: "outerGram K p \<in> carrier_mat h h"
    by (simp_all add: B_def Bp_def GK_def Aout_def outerGram_def h_def len Let_def)
  have uni: "Determinant.det B \<noteq> 0 \<and> vp p (Determinant.det B) = 0"
    unfolding B_def by (rule outerBasis_unimodular[OF p K H])
  obtain L where Lc: "L \<in> carrier_mat h h"
    and GL: "GK K = Aout K p + map_mat (\<lambda>c. [:c / of_nat p:]) L"
    and Lint: "\<And>i j. i < h \<Longrightarrow> j < h \<Longrightarrow>
      L $$ (i, j) \<noteq> 0 \<Longrightarrow> 0 \<le> vp p (L $$ (i, j))"
    and Lrank: "vec_space.rank h L \<le> rOut K p"
    using GK_outer_decomposition[OF p K H] unfolding h_def by blast
  define L2 where "L2 = B * L * transpose_mat B"
  have L2c: "L2 \<in> carrier_mat h h" using Bc Lc by (simp add: L2_def)
  have conj: "Bp * GK K * transpose_mat Bp =
    outerGram K p + map_mat (\<lambda>c. [:c / of_nat p:]) L2"
  proof -
    define f where "f = (\<lambda>c. [:c / of_nat p:] :: rat poly)"
    have sum_pC: "(\<Sum> i \<in> S. [:g i:]) = [:\<Sum> i \<in> S. g i:]"
      for S and g :: "nat \<Rightarrow> rat"
      by (induction S rule: infinite_finite_induct) simp_all
    have MLc: "map_mat f L \<in> carrier_mat h h" using Lc by auto
    have BTc: "transpose_mat Bp \<in> carrier_mat h h" using Bpc by force
    have OGe: "outerGram K p = Bp * Aout K p * transpose_mat Bp"
      using outerGram_eq_conj[OF p K H] unfolding B_def[symmetric] Bp_def[symmetric] by meson
    have M1: "Bp * map_mat f L * transpose_mat Bp = map_mat f L2"
    proof (rule eq_matI)
      fix x y assume x: "x < dim_row (map_mat f L2)" and y: "y < dim_col (map_mat f L2)"
      have xh: "x < h" and yh: "y < h" using x y L2c by auto
      have e1: "(Bp * map_mat f L * transpose_mat Bp) $$ (x, y) =
          (\<Sum> l = 0..<h. (\<Sum> k =
            0..<h. [:B $$ (x, k):] * [:L $$ (k, l) / of_nat p:]) * [:B $$ (y, l):])"
      proof -
        have BMc: "Bp * map_mat f L \<in> carrier_mat h h" using Bpc MLc by fastforce
        have "(Bp * map_mat f L * transpose_mat Bp) $$ (x, y) = (\<Sum> l =
          0..<h. (Bp * map_mat f L) $$ (x, l) * transpose_mat Bp $$ (l, y))"
          by (rule mat_mult_entry[OF BMc BTc xh yh])
        also have "\<dots> = (\<Sum> l = 0..<h. (\<Sum> k =
          0..<h. Bp $$ (x, k) * map_mat f L $$ (k, l)) * transpose_mat Bp $$ (l, y))"
        proof (rule sum.cong[OF refl])
          fix l assume "l \<in> {0..<h}"
          hence l: "l < h" by simp
          show "(Bp * map_mat f L) $$ (x, l) * transpose_mat Bp $$ (l, y) = (\<Sum> k =
            0..<h. Bp $$ (x, k) * map_mat f L $$ (k, l)) * transpose_mat Bp $$ (l, y)"
            using mat_mult_entry[OF Bpc MLc xh l] by argo
        qed
        also have "\<dots> = (\<Sum> l = 0..<h. (\<Sum> k =
          0..<h. [:B $$ (x, k):] * [:L $$ (k, l) / of_nat p:]) * [:B $$ (y, l):])"
        proof (rule sum.cong[OF refl])
          fix l assume "l \<in> {0..<h}"
          hence l: "l < h" by simp
          have t: "transpose_mat Bp $$ (l, y) = [:B $$ (y, l):]" using l yh Bpc Bc unfolding Bp_def
            by auto
          have s: "(\<Sum> k = 0..<h. Bp $$ (x, k) * map_mat f L $$ (k, l)) = (\<Sum> k =
            0..<h. [:B $$ (x, k):] * [:L $$ (k, l) / of_nat p:])"
          proof (rule sum.cong[OF refl])
            fix k assume "k \<in> {0..<h}"
            hence k: "k < h" by simp
            show "Bp $$ (x, k) * map_mat f L $$ (k, l) =
              [:B $$ (x, k):] * [:L $$ (k, l) / of_nat p:]"
              using k l xh Bc Lc unfolding Bp_def f_def by force
          qed
          show "(\<Sum> k = 0..<h. Bp $$ (x, k) * map_mat f L $$ (k, l)) * transpose_mat Bp $$ (l,
            y) =
              (\<Sum> k = 0..<h. [:B $$ (x, k):] * [:L $$ (k, l) / of_nat p:]) * [:B $$ (y, l):]"
                unfolding s t ..
        qed
        finally show ?thesis .
      qed
      have e2: "map_mat f L2 $$ (x, y) = [:(\<Sum> l = 0..<h. (\<Sum> k =
        0..<h. B $$ (x, k) * L $$ (k, l)) * B $$ (y, l)) / of_nat p:]"
      proof -
        have BLc: "B * L \<in> carrier_mat h h" using Bc Lc by force
        have BTc': "transpose_mat B \<in> carrier_mat h h" using Bc by force
        have "L2 $$ (x, y) = (\<Sum> l = 0..<h. (B * L) $$ (x, l) * transpose_mat B $$ (l, y))"
          unfolding L2_def by (rule mat_mult_entry[OF BLc BTc' xh yh])
        also have "\<dots> = (\<Sum> l = 0..<h. (\<Sum> k =
          0..<h. B $$ (x, k) * L $$ (k, l)) * B $$ (y, l))"
        proof (rule sum.cong[OF refl])
          fix l assume "l \<in> {0..<h}"
          hence l: "l < h" by simp
          show "(B * L) $$ (x, l) * transpose_mat B $$ (l, y) = (\<Sum> k =
            0..<h. B $$ (x, k) * L $$ (k, l)) * B $$ (y, l)"
            using mat_mult_entry[OF Bc Lc xh l] l yh Bc by force
        qed
        finally have "L2 $$ (x, y) = (\<Sum> l = 0..<h. (\<Sum> k =
          0..<h. B $$ (x, k) * L $$ (k, l)) * B $$ (y, l))" .
        thus ?thesis using xh yh L2c unfolding f_def by fastforce
      qed
      have e3: "(\<Sum> l = 0..<h. (\<Sum> k =
        0..<h. [:B $$ (x, k):] * [:L $$ (k, l) / of_nat p:]) * [:B $$ (y, l):]) =
          [:(\<Sum> l = 0..<h. (\<Sum> k =
            0..<h. B $$ (x, k) * L $$ (k, l)) * B $$ (y, l)) / of_nat p:]"
      proof -
        have i: "(\<Sum> k = 0..<h. [:B $$ (x, k):] * [:L $$ (k, l) / of_nat p:]) = [:(\<Sum> k =
          0..<h. B $$ (x, k) * L $$ (k, l)) / of_nat p:]" for l
        proof -
          have m: "[:a:] * [:b / of_nat p:] = [:a * b / of_nat p:]" for a b :: rat by auto
          have "(\<Sum> k = 0..<h. [:B $$ (x, k):] * [:L $$ (k, l) / of_nat p:]) = (\<Sum> k =
            0..<h. [:B $$ (x, k) * L $$ (k, l) / of_nat p:])"
            unfolding m ..
          also have "\<dots> = [:\<Sum> k = 0..<h. B $$ (x, k) * L $$ (k, l) / of_nat p:]"
            by (rule sum_pC)
          also have "\<dots> = [:(\<Sum> k = 0..<h. B $$ (x, k) * L $$ (k, l)) / of_nat p:]"
            unfolding sum_divide_distrib ..
          finally show ?thesis .
        qed
        have "(\<Sum> l = 0..<h. (\<Sum> k =
          0..<h. [:B $$ (x, k):] * [:L $$ (k, l) / of_nat p:]) * [:B $$ (y, l):]) =
            (\<Sum> l = 0..<h. [:(\<Sum> k =
              0..<h. B $$ (x, k) * L $$ (k, l)) / of_nat p * B $$ (y, l):])" unfolding i
              by (simp add: mult.commute)
        also have "\<dots> = [:(\<Sum> l = 0..<h. (\<Sum> k =
          0..<h. B $$ (x, k) * L $$ (k, l)) * B $$ (y, l)) / of_nat p:]"
        proof -
          have "(\<Sum> l = 0..<h. [:(\<Sum> k =
            0..<h. B $$ (x, k) * L $$ (k, l)) / of_nat p * B $$ (y, l):]) =
              [:\<Sum> l = 0..<h. (\<Sum> k =
                0..<h. B $$ (x, k) * L $$ (k, l)) / of_nat p * B $$ (y, l):]" by (rule sum_pC)
          also have "(\<Sum> l = 0..<h. (\<Sum> k =
            0..<h. B $$ (x, k) * L $$ (k, l)) / of_nat p * B $$ (y, l)) =
              (\<Sum> l = 0..<h. (\<Sum> k =
                0..<h. B $$ (x, k) * L $$ (k, l)) * B $$ (y, l)) / of_nat p"
          proof -
            have r: "a / c * b = a * b / c" for a b c :: rat by auto
            show ?thesis unfolding r sum_divide_distrib[symmetric] ..
          qed
          finally show ?thesis .
        qed
        finally show ?thesis .
      qed
      show "(Bp * map_mat f L * transpose_mat Bp) $$ (x, y) = map_mat f L2 $$ (x, y)"
        unfolding e1 e2 e3 ..
    next
      show "dim_row (Bp * map_mat f L * transpose_mat Bp) = dim_row (map_mat f L2)" using Bpc L2c
        by fastforce
      show "dim_col (Bp * map_mat f L * transpose_mat Bp) = dim_col (map_mat f L2)" using BTc L2c
        by fastforce
    qed
    have "Bp * GK K * transpose_mat Bp =
      Bp * Aout K p * transpose_mat Bp + Bp * map_mat f L * transpose_mat Bp"
    proof -
      have d1: "Bp * (Aout K p + map_mat f L) = Bp * Aout K p + Bp * map_mat f L"
        by (rule mult_add_distrib_mat[OF Bpc Ac MLc])
      have d2: "(Bp * Aout K p + Bp * map_mat f L) * transpose_mat Bp =
        Bp * Aout K p * transpose_mat Bp + Bp * map_mat f L * transpose_mat Bp"
        by (rule add_mult_distrib_mat[OF mult_carrier_mat[OF Bpc Ac] mult_carrier_mat[OF Bpc MLc]
          BTc])
      show ?thesis unfolding GL f_def[symmetric] d1 d2 ..
    qed
    also have "\<dots> = outerGram K p + map_mat f L2" unfolding OGe[symmetric] M1 ..
    finally show ?thesis unfolding f_def .
  qed
  have L2int: "\<And>i j. i < h \<Longrightarrow> j < h \<Longrightarrow>
    L2 $$ (i, j) \<noteq> 0 \<Longrightarrow> 0 \<le> vp p (L2 $$ (i, j))"
  proof -
    fix i j assume i: "i < h" and j: "j < h" and nz: "L2 $$ (i, j) \<noteq> 0"
    have vB: "\<forall>i<h. \<forall>j<h. vge p (B $$ (i, j)) 0"
      using vpGge_outerBasis[OF p] by (auto simp: B_def h_def vpGge_iff)
    have vL: "\<forall>i<h. \<forall>j<h. vge p (L $$ (i, j)) 0" using Lint by (auto simp: vge_def)
    have vBT: "\<forall>i<h. \<forall>j<h. vge p (transpose_mat B $$ (i, j)) 0" using vB Bc by auto
    have BL: "\<forall>i<h. \<forall>j<h. vge p ((B * L) $$ (i, j)) 0"
      using vge_mat_mult0[OF p Bc Lc] vB vL by blast
    have "vge p ((B * L * transpose_mat B) $$ (i, j)) 0"
      by (rule vge_mat_mult0[OF p _ _ BL vBT i j]) (use Bc Lc in auto)
    thus "0 \<le> vp p (L2 $$ (i, j))" using nz by (simp add: L2_def vge_def)
  qed
  have L2rank: "vec_space.rank h L2 \<le> rOut K p"
  proof -
    have "vec_space.rank h L2 \<le> vec_space.rank h (B * L)" unfolding L2_def
      by (rule vec_space.rank_mat_mul_right) (use Bc Lc in auto)
    also have "\<dots> \<le> vec_space.rank h L" by (rule rank_mat_mul_left[OF Bc Lc])
    also note Lrank
    finally show ?thesis .
  qed
  have h42: "vpGge p (Determinant.det (outerGram K p + map_mat (\<lambda>c. [:c / of_nat p:]) L2))
               (2 * (\<Sum> i < h. w i) - of_nat (min (rOut K p) (card {i. i < h \<and> w i = 0})))"
    by (rule det_vpGge_of_weighted_entries[OF p OGc L2c])
       (use wOut_nonpos wOut_halfInt outerGram_entry_bound[OF p K H] L2int L2rank in \<open>auto
         simp: w_def len\<close>)
  have "vpGge p (DeltaK K) (2 * (\<Sum> i < h. w i) - of_nat (min (rOut K p) (card {i. i < h \<and>
    w i = 0})))"
    unfolding DeltaK_def
    by (rule det_gram_transfer[OF p Gc Bc conjunct1[OF uni] conjunct2[OF uni]]) (use h42 conj in
      \<open>simp add: Bp_def\<close>)
  thus ?thesis using gammaOut_eq_sum_idx[OF p K H] by (simp add: w_def len)
qed

subsection \<open>Proposition 4.3 for @{text "p > K"}\<close>

lemma muX_eq_muXmod_of_lt:
  assumes "prime p" "degree (P div sqPoleProd S) < 2 * p - 3"
  shows "muX S P = muXmod p S P"
proof -
  have "(\<Sum> e \<le> degree (P div sqPoleProd S). Polynomial.coeff (P div sqPoleProd S) e *
    cCorr p e) = 0"
  proof (rule sum.neutral, intro ballI)
    fix e assume "e \<in> {..degree (P div sqPoleProd S)}"
    hence "e < 2 * p - 3" using assms(2) by simp
    thus "Polynomial.coeff (P div sqPoleProd S) e * cCorr p e = 0" by (simp add: cCorr_of_lt)
  qed
  thus ?thesis using muX_eq_muXmod_add[OF assms(1), of S P] by simp
qed

text \<open>For @{text "p > K \<ge> 40"}: @{text p} is odd and @{text "\<ge> 7"},
  class @{text "a \<ge> 1"} poles are among @{text "a, p - a"}, the zero class is empty.\<close>
lemma large_facts:
  assumes "prime p" "40 dvd K" "0 < K" "K < p"
  shows "7 \<le> p \<and> odd p \<and> 2 * mHalf p + 1 = p \<and> outerCount K p 0 = 0 \<and>
         (\<forall>a j. a \<le> mHalf p \<longrightarrow>
           j \<in> outerClassPoles K p a \<longrightarrow> (j = a \<or> j = p - a) \<and>
           Nof K + 1 \<le> j \<and> j \<le> K) \<and>
         (\<forall>a. a \<le> mHalf p \<longrightarrow> ell p K a \<le> 2) \<and>
           (\<forall>a. {j \<in> outerClassPoles K p a. p < j} = {})"
proof -
  obtain k where k: "K = 40 * k" using assms(2) by (elim dvdE)
  have "40 \<le> K" using assms(3) k by simp
  hence p7: "7 \<le> p" using assms(4) by simp
  have o: "odd p" using prime_odd_nat[OF assms(1)] p7 by simp
  then obtain t where t: "p = 2 * t + 1" by (elim oddE)
  have m: "2 * mHalf p + 1 = p" by (simp add: mHalf_def t)
  have jp: "j < p \<and> Nof K + 1 \<le> j \<and> j \<le> K" if "j \<in> outerClassPoles K p a"
    for a j
    using that assms(4) by (auto simp: outerClassPoles_def)
  have "outerClassPoles K p 0 = {}"
  proof (rule equals0I)
    fix j assume j: "j \<in> outerClassPoles K p 0"
    hence "j mod p = 0" by (auto simp: outerClassPoles_def)
    moreover have "j < p" "1 \<le> j" using jp[OF j] by auto
    ultimately show False by simp
  qed
  hence c0: "outerCount K p 0 = 0" by (simp add: outerCount_def)
  have cl: "\<forall>a j. a \<le> mHalf p \<longrightarrow>
    j \<in> outerClassPoles K p a \<longrightarrow> (j = a \<or> j = p - a) \<and>
    Nof K + 1 \<le> j \<and> j \<le> K"
  proof (intro allI impI)
    fix a j assume a: "a \<le> mHalf p" and j: "j \<in> outerClassPoles K p a"
    have "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
      by (rule res_class[OF a m]) (use j in \<open>simp add: outerClassPoles_def\<close>)
    thus "(j = a \<or> j = p - a) \<and> Nof K + 1 \<le> j \<and> j \<le> K" using jp[OF j] by auto
  qed
  have el: "\<forall>a. a \<le> mHalf p \<longrightarrow> ell p K a \<le> 2"
  proof (intro allI impI)
    fix a assume a: "a \<le> mHalf p"
    have "{j \<in> {1..K}. j mod p = a mod p \<or> (j + a) mod p = 0} \<subseteq> {a, p - a}"
    proof
      fix j assume j: "j \<in> {j \<in> {1..K}. j mod p = a mod p \<or> (j + a) mod p = 0}"
      have "j mod p = a \<or> (1 \<le> a \<and> j mod p = p - a)"
        by (rule res_class[OF a m]) (use j in simp)
      moreover have "j < p" using j assms(4) by auto
      ultimately show "j \<in> {a, p - a}" by auto
    qed
    hence "ell p K a \<le> card {a, p - a}" unfolding ell_def by (rule card_mono[rotated]) simp
    also have "card {a, p - a} \<le> 2" by (simp add: card_insert_if)
    finally show "ell p K a \<le> 2" .
  qed
  have e: "\<forall>a. {j \<in> outerClassPoles K p a. p < j} = {}" using jp by fastforce
  show ?thesis using p7 o m c0 cl el e by blast
qed

text \<open>For @{text "p > K"}: the length of the outer index list,
  the degree bound and the congruence of the class factors.\<close>
lemma length_outer_idx_large:
  assumes p: "prime p" and K: "40 dvd K" and K0: "0 < K" and Kp: "K < p"
  shows "length (outer_idx K p) = hof K"
proof -
  obtain k where k: "K = 40 * k" using K by (elim dvdE)
  have p2: "2 < p" using K0 Kp k by simp
  have hk: "hof K = 37 * k" and Nk: "Nof K = 3 * k" unfolding k hof_def Nof_def by simp_all
  have "length (outer_idx K p) = (\<Sum> a \<in> set [0..<mHalf p + 1]. outerCount K p a)"
    unfolding outer_idx_def length_concat map_map
      by (simp add: o_def sum_list_distinct_conv_sum_set)
  also have "set [0..<mHalf p + 1] = {..mHalf p}" by auto
  also have "(\<Sum> a \<le> mHalf p. outerCount K p a) = card {Nof K + 1..K}"
    unfolding outerCount_def outerClassPoles_def by (rule sum_classes_card[OF p p2]) simp
  also have "\<dots> = hof K" using hk Nk k by simp
  finally show ?thesis .
qed

lemma degree_outerBasis_lt_large:
  assumes p: "prime p" and K: "40 dvd K" and K0: "0 < K" and Kp: "K < p" and x: "x \<in>
    set (outer_idx K p)"
  shows "degree (outerBasis K p x) < hof K"
proof -
  define a where "a = fst x"
  define i where "i = snd x"
  have ia: "i < outerCount K p a" using x mem_outer_idx by (auto simp: a_def i_def)
  have dS: "degree (sqPoleProd S) \<le> card S" if "finite S" for S
  proof -
    have "degree (sqPoleProd S) \<le> (\<Sum> j \<in> S. degree (pX + [:of_nat j ^ 2:]))"
      unfolding sqPoleProd_def using degree_prod_sum_le[OF that] by (simp add: o_def)
    also have "\<dots> = card S" using degree_pX_plus_const by simp
    finally show ?thesis .
  qed
  have dP: "degree ((pX + [:of_nat n ^ 2:]) ^ k) \<le> k" for n k
    using degree_power_le[of "pX + [:of_nat n ^ 2:]" k] degree_pX_plus_const by simp
  have dQ: "degree (oq K p x) \<le> i"
  proof (cases "a = 0")
    case True
    thus ?thesis using dP by (simp add: oq_def Let_def a_def i_def)
  next
    case False
    show ?thesis
    proof (cases "i < ell p K a - 2")
      case True
      thus ?thesis using dP False by (simp add: oq_def Let_def a_def i_def)
    next
      case big: False
      have cE: "{j \<in> outerClassPoles K p a. p < j} = {}" using large_facts[OF p K K0 Kp]
        by blast
      have fE: "finite {j \<in> outerClassPoles K p a. p < j}" by (simp add: outerClassPoles_def)
      have "degree (oq K p x) = degree (sqPoleProd {j \<in> outerClassPoles K p a. p <
        j} * (pX + [:of_nat a ^ 2:]) ^ (i - (ell p K a - 2)))"
        using False big by (simp add: oq_def Let_def a_def i_def)
      also have "\<dots> \<le> degree (sqPoleProd {j \<in> outerClassPoles K p a. p <
        j}) + degree ((pX + [:of_nat a ^ 2:]) ^ (i - (ell p K a - 2)))"
        by (rule degree_mult_le)
      also have "\<dots> \<le> card {j \<in> outerClassPoles K p a. p < j} + (i - (ell p K a - 2))"
        using dS[OF fE] dP[of a "i - (ell p K a - 2)"] by linarith
      also have "\<dots> \<le> i" unfolding cE by simp
      finally show ?thesis .
    qed
  qed
  obtain k where k: "K = 40 * k" using K by (elim dvdE)
  have ct: "card (tailPoles K) = hof K" by (simp add: tailPoles_def k hof_def Nof_def)
  have sub: "outerClassPoles K p a \<subseteq> tailPoles K"
    by (auto simp: outerClassPoles_def tailPoles_def)
  have fC: "finite (outerClassPoles K p a)" by (simp add: outerClassPoles_def)
  have fT: "finite (tailPoles K - outerClassPoles K p a)" by (simp add: tailPoles_def)
  have cd: "card (tailPoles K - outerClassPoles K p a) = hof K - card (outerClassPoles K p a)"
    using card_Diff_subset[OF fC sub] ct by simp
  have cle: "card (outerClassPoles K p a) \<le> hof K" using card_mono[OF _ sub] ct
    by (simp add: tailPoles_def)
  have ic: "i < card (outerClassPoles K p a)" using ia by (simp add: outerCount_def)
  have "degree (outerBasis K p x) \<le> degree (sqPoleProd (tailPoles K - outerClassPoles K p a)) +
    degree (oq K p x)"
    unfolding outerBasis_eq a_def by (rule degree_mult_le)
  also have "\<dots> \<le> (hof K - card (outerClassPoles K p a)) + i" using dS[OF fT] dQ cd
    by linarith
  also have "\<dots> < hof K" using ic cle by linarith
  finally show ?thesis .
qed

lemma oq_cong_large:
  assumes p: "prime p" and K: "40 dvd K" and K0: "0 < K" and Kp: "K < p" and x: "x \<in>
    set (outer_idx K p)"
  shows "vpGge p (oq K p x - (pX - [:- (of_nat (oroot p (fst x)) ^ 2):]) ^ snd x) 1"
proof (rule oq_cong[OF p])
  assume "1 \<le> fst x"
  have am: "fst x \<le> mHalf p" using x mem_outer_idx by blast
  have e: "{j \<in> outerClassPoles K p (fst x). p < j} = {}" and l2: "ell p K (fst x) \<le> 2"
    using large_facts[OF p K K0 Kp] am by auto
  show "card {j \<in> outerClassPoles K p (fst x). p < j} = ell p K (fst x) - 2" using l2
    unfolding e by simp
qed

lemma outerBasis_unimodular_large:
  assumes p: "prime p" and K: "40 dvd K" and K0: "0 < K" and Kp: "K < p"
  defines "B \<equiv> Matrix.mat (hof K) (hof K) (\<lambda>(x,
    d). Polynomial.coeff (outerBasis K p (outer_idx K p ! x)) d)"
  shows "Determinant.det B \<noteq> 0 \<and> vp p (Determinant.det B) = 0"
proof -
  define h where "h = hof K"
  define idx where "idx = outer_idx K p"
  define rt where "rt = (\<lambda>y. if fst (idx ! y) =
    0 then - (of_nat p ^ 2) else - (of_nat (fst (idx ! y)) ^ 2) :: rat)"
  define od where "od = (\<lambda>y. snd (idx ! y))"
  define V :: "rat mat" where "V = Matrix.mat h h (\<lambda>(d, y). tay (pX ^ d) (rt y) (od y))"
  define T :: "rat mat" where "T = B * V"
  have len: "length idx = h" unfolding idx_def h_def by (rule length_outer_idx_large[OF p K K0 Kp])
  have Bc: "B \<in> carrier_mat h h" and Vc: "V \<in> carrier_mat h h"
    by (simp_all add: B_def V_def h_def)
  have Tentry: "\<And>x y. x < h \<Longrightarrow> y < h \<Longrightarrow>
    T $$ (x, y) = tay (outerBasis K p (idx ! x)) (rt y) (od y)"
  proof -
    fix x y assume x: "x < h" and y: "y < h"
    have mem: "idx ! x \<in> set (outer_idx K p)" using x len unfolding idx_def by fastforce
    have dg: "degree (outerBasis K p (idx ! x)) < h"
      using degree_outerBasis_lt_large[OF p K K0 Kp mem] unfolding h_def by meson
    have "dim_row B = h" "dim_col B = h" "dim_row V = h" "dim_col V = h" using Bc Vc by auto
    with x y have "T $$ (x, y) = (\<Sum> d \<in> {0..<h}. B $$ (x, d) * V $$ (d, y))"
      unfolding T_def scalar_prod_def by (auto simp: scalar_prod_def index_mult_mat)
    also have "\<dots> = (\<Sum> d < h. Polynomial.coeff (outerBasis K p (idx ! x)) d *
      tay (pX ^ d) (rt y) (od y))"
    proof (rule sum.cong)
      show "{0..<h} = {..<h}" by fastforce
      fix d assume d: "d \<in> {..<h}"
      show "B $$ (x, d) * V $$ (d, y) = Polynomial.coeff (outerBasis K p (idx ! x)) d *
        tay (pX ^ d) (rt y) (od y)"
        using x y d unfolding B_def V_def idx_def h_def by force
    qed
    also have "\<dots> = tay (outerBasis K p (idx ! x)) (rt y) (od y)"
      by (rule tay_eq_sum[OF dg, symmetric])
    finally show "T $$ (x, y) = tay (outerBasis K p (idx ! x)) (rt y) (od y)" .
  qed
  have below: "\<And>x y. y < x \<Longrightarrow> x < h \<Longrightarrow> vge p (T $$ (x, y)) 1"
  proof -
    fix x y assume yx: "y < x" and x: "x < h"
    have y: "y < h" using yx x by simp
    obtain a j where ax: "idx ! x = (a, j)" by (cases "idx ! x")
    obtain c i where cy: "idx ! y = (c, i)" by (cases "idx ! y")
    have mx: "idx ! x \<in> set (outer_idx K p)" and my: "idx ! y \<in> set (outer_idx K p)"
      using x y len unfolding idx_def by auto
    have am: "a \<le> mHalf p" using mx ax mem_outer_idx by simp
    have cm: "c \<le> mHalf p" and ci: "i < outerCount K p c" using my cy mem_outer_idx by auto
    have lex: "c < a \<or> (c = a \<and> i < j)" using outer_idx_lex[of y x K p] yx x len ax cy
      unfolding idx_def by simp
    have m: "2 * mHalf p + 1 = p" using large_facts[OF p K K0 Kp] by blast
    have oqc: "vpGge p (oq K p (a, j) - (pX - [:- (of_nat (oroot p a) ^ 2):]) ^ j) 1"
      using oq_cong_large[OF p K K0 Kp mx] ax by simp
    have rty: "rt y = - (of_nat (oroot p c) ^ 2)" unfolding rt_def cy oroot_def by simp
    have Te: "T $$ (x, y) = tay (outerBasis K p (a, j)) (- (of_nat (oroot p c) ^ 2)) i"
      using Tentry[OF x y] ax rty cy unfolding od_def by simp
    show "vge p (T $$ (x, y)) 1" unfolding Te by (rule outer_tay_below[OF p m oqc am cm ci lex])
  qed
  have unit: "\<And>x. x < h \<Longrightarrow> T $$ (x, x) \<noteq> 0 \<and> vp p (T $$ (x, x)) = 0"
  proof -
    fix x assume x: "x < h"
    obtain a j where ax: "idx ! x = (a, j)" by (cases "idx ! x")
    have mx: "idx ! x \<in> set (outer_idx K p)" using x len unfolding idx_def by simp
    have oqc: "vpGge p (oq K p (a, j) - (pX - [:- (of_nat (oroot p a) ^ 2):]) ^ j) 1"
      using oq_cong_large[OF p K K0 Kp mx] ax by simp
    have rtx: "rt x = - (of_nat (oroot p a) ^ 2)" unfolding rt_def ax oroot_def by simp
    have Te: "T $$ (x, x) = tay (outerBasis K p (a, j)) (- (of_nat (oroot p a) ^ 2)) j"
      using Tentry[OF x x] ax rtx unfolding od_def by simp
    show "T $$ (x, x) \<noteq> 0 \<and> vp p (T $$ (x, x)) = 0" unfolding Te
      by (rule outer_tay_diag[OF p oqc])
  qed
  have Bi: "\<And>x d. x < h \<Longrightarrow> d < h \<Longrightarrow> vge p (B $$ (x, d)) 0"
    using vpGge_outerBasis[OF p] by (auto simp: B_def h_def vpGge_iff)
  have Vi: "\<And>d y. d < h \<Longrightarrow> y < h \<Longrightarrow> vge p (V $$ (d, y)) 0"
  proof -
    fix d y assume d: "d < h" and y: "y < h"
    have sq: "vge p (- (of_nat m ^ 2)) 0" for m by (rule vge_neg[OF vge_pow[OF p vge_of_nat[OF p]]])
    have rt0: "vge p (rt y) 0" by (simp add: rt_def sq)
    have "vge p (of_nat (d choose od y) * rt y ^ (d - od y)) (0 + 0)"
      by (rule vge_mul[OF p vge_of_nat[OF p] vge_pow[OF p rt0]])
    hence vf: "vge p (of_nat (d choose od y) * rt y ^ (d - od y)) 0" by simp
    have "V $$ (d, y) = tay (pX ^ d) (rt y) (od y)" using d y by (simp add: V_def)
    thus "vge p (V $$ (d, y)) 0" unfolding tay_pX_pow using vf by (simp add: vge_zero)
  qed
  show ?thesis
    unfolding h_def[symmetric]
    by (rule unimodular_criterion[OF p Bc Vc Bi Vi]) (use below unit in \<open>simp_all add:
      T_def[symmetric]\<close>)
qed

lemma G_eq_Aout_large:
  assumes "prime p" "40 dvd K" "0 < K" "K < p"
  shows "GK K = Aout K p"
proof -
  have p: "prime p" using assms(1) .
  obtain n where Kn: "K = 40 * n" using assms(2) by (elim dvdE)
  have hN: "Nof K = 3 * n" and hh: "hof K = 37 * n" by (simp_all add: Kn Nof_def hof_def)
  have dS: "degree (sqPoleProd {1..K}) = K"
  proof -
    have "sqPoleProd {1..K} = Dm K" by (simp add: Dm_def sqPoleProd_def)
    thus ?thesis by (simp add: degree_Dm)
  qed
  show ?thesis
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row (Aout K p)" and j: "j < dim_col (Aout K p)"
    have ih: "i < hof K" "j < hof K" using i j by (simp_all add: Aout_def)
    have dN: "degree (Dm (Nof K) ^ 6 * pX ^ (i + j)) \<le> 6 * Nof K + (i + j)"
    proof -
      have "degree (Dm (Nof K) ^ 6 * pX ^ (i + j)) \<le>
        degree (Dm (Nof K) ^ 6) + degree (pX ^ (i + j))" by (rule degree_mult_le)
      also have "degree (Dm (Nof K) ^ 6) \<le> degree (Dm (Nof K)) * 6" by (rule degree_power_le)
      also have "degree ((pX :: rat poly) ^ (i + j)) \<le> degree (pX :: rat poly) * (i + j)"
        by (rule degree_power_le)
      finally show ?thesis by (simp add: degree_Dm degree_monom_eq)
    qed
    have dd: "degree ((Dm (Nof K) ^ 6 * pX ^ (i + j)) div sqPoleProd {1..K}) \<le>
      degree (Dm (Nof K) ^ 6 * pX ^ (i + j)) - degree (sqPoleProd {1..K})"
      by (rule degree_div_sub[OF sqPoleProd_nonzero]) simp
    have dq: "degree ((Dm (Nof K) ^ 6 * pX ^ (i + j)) div sqPoleProd {1..K}) < 2 * p - 3"
      using dd dN dS ih hN hh Kn assms(3,4) by linarith
    have e: "muX {1..K} (Dm (Nof K) ^ 6 * pX ^ (i + j)) =
      muXmod p {1..K} (Dm (Nof K) ^ 6 * pX ^ (i + j))"
      by (rule muX_eq_muXmod_of_lt[OF p dq])
    show "GK K $$ (i, j) = Aout K p $$ (i, j)" using ih e by (simp add: GK_def Aout_def)
  qed (simp_all add: GK_def Aout_def)
qed

lemma large_class_entry:
  assumes p: "prime p" and K: "40 dvd K" and K0: "0 < K" and Kp: "K < p" and a1: "1 \<le>
    a" and am: "a \<le> mHalf p" and R: "vpGge p R 0"
  shows "vpGge p (muXmod p (outerClassPoles K p a) R) 0"
proof -
  obtain p7: "7 \<le> p" and m: "2 * mHalf p + 1 = p"
    and cl: "\<forall>a j. a \<le> mHalf p \<longrightarrow>
      j \<in> outerClassPoles K p a \<longrightarrow> (j = a \<or> j = p - a) \<and>
      Nof K + 1 \<le> j \<and> j \<le> K"
    using large_facts[OF p K K0 Kp] by blast
  have p2: "p \<noteq> 2" using p7 by simp
  have a2: "2 * a < p" using m am by linarith
  have ap: "a < p" and b1: "1 \<le> p - a" and bp: "p - a < p" using a2 a1 by auto
  have sub: "outerClassPoles K p a \<subseteq> {a, p - a}" using cl am by blast
  have single: "vpGge p (muXmod p {j} R) 0" if j1: "1 \<le> j" and jp: "j < p" for j
  proof (rule muXmod_vge_of_residues[OF p p7 _ R order.refl])
    show "finite {j}" by simp
    fix k assume "k \<in> {j}"
    hence k: "k = j" by simp
    have "vge p (sqResidue {j} R j) 0" unfolding sqResidue_def
      by (simp add: eval_vge0[OF p R vge_neg_sq[OF p]])
    from vpGge_mul[OF p vpGge_C[OF this] muPole_vge_small[OF p j1 jp p2]]
    show "vpGge p ([:sqResidue {j} R k:] * muPole k) 0" unfolding k by simp
  qed
  show ?thesis
  proof (cases "a \<in> outerClassPoles K p a")
    case aC: True
    show ?thesis
    proof (cases "p - a \<in> outerClassPoles K p a")
      case True
      have "outerClassPoles K p a = {a, p - a}" using sub aC True by blast
      thus ?thesis using two_pole_vge[OF p p7 a1 a2 R] by simp
    next
      case False
      have "outerClassPoles K p a = {a}" using sub aC False by blast
      thus ?thesis using single[OF a1 ap] by simp
    qed
  next
    case naC: False
    show ?thesis
    proof (cases "p - a \<in> outerClassPoles K p a")
      case True
      have "outerClassPoles K p a = {p - a}" using sub naC True by blast
      thus ?thesis using single[OF b1 bp] by simp
    next
      case False
      have "outerClassPoles K p a = {}" using sub naC False by blast
      thus ?thesis using vpGge_C[OF muModPoly_vge[OF p p7 R]] by (simp add: muXmod_empty)
    qed
  qed
qed

lemma outerGram_int_large:
  assumes p: "prime p" and K: "40 dvd K" and K0: "0 < K" and Kp: "K < p" and x: "x <
    length (outer_idx K p)" and y: "y < length (outer_idx K p)"
  shows "vpGge p (outerGram K p $$ (x, y)) 0"
proof -
  obtain p7: "7 \<le> p" and m: "2 * mHalf p + 1 = p" and c0: "outerCount K p 0 = 0"
    and cl: "\<forall>a j. a \<le> mHalf p \<longrightarrow>
      j \<in> outerClassPoles K p a \<longrightarrow> (j = a \<or> j = p - a) \<and>
      Nof K + 1 \<le> j \<and> j \<le> K"
    using large_facts[OF p K K0 Kp] by fast
  define ix where "ix = outer_idx K p ! x"
  define iy where "iy = outer_idx K p ! y"
  define a where "a = fst ix"
  define c where "c = fst iy"
  have ixs: "ix \<in> set (outer_idx K p)" and iys: "iy \<in> set (outer_idx K p)"
    by (simp_all add: ix_def iy_def x y)
  have am: "a \<le> mHalf p" and xi: "snd ix < outerCount K p a" and cm: "c \<le>
    mHalf p" and yi: "snd iy < outerCount K p c"
    using mem_outer_idx ixs iys by (auto simp: a_def c_def)
  have a1: "1 \<le> a" using xi c0 by (cases "a = 0") auto
  have finC: "\<And>a. finite (outerClassPoles K p a)" and subC: "\<And>a. outerClassPoles K p a
    \<subseteq> tailPoles K"
    by (auto simp: outerClassPoles_def tailPoles_def)
  have entry: "outerGram K p $$ (x, y) =
    muXmod p {1..K} (Dm (Nof K) ^ 6 * (sqPoleProd (tailPoles K - outerClassPoles K p a) *
    oq K p ix) * (sqPoleProd (tailPoles K - outerClassPoles K p c) * oq K p iy))"
    using outerGram_apply[OF x y] outerBasis_eq[of K p ix] outerBasis_eq[of K p iy]
      by (simp add: ix_def iy_def a_def c_def)
  have int0: "vpGge p (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - outerClassPoles K p a)) 0"
    by (intro vpGge_mul0[OF p] vpGge_pow0[OF p] vpGge_Dm[OF p] vpGge_sqPoleProd[OF p])
  show ?thesis
  proof (cases "a = c")
    case False
    have ac: "a + c < p" using am cm m by linarith
    have "{a, p - a} \<inter> {c, p - c} = {}" using False ac by auto
    moreover have "outerClassPoles K p a \<subseteq> {a, p - a}" "outerClassPoles K p c \<subseteq>
      {c, p - c}" using cl am cm by blast+
    ultimately have disj: "outerClassPoles K p a \<inter> outerClassPoles K p c = {}" by blast
    have "outerGram K p $$ (x, y) = [:muModPoly p (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K -
      (outerClassPoles K p a \<union> outerClassPoles K p c)) * oq K p ix * oq K p iy):]"
      unfolding entry by (rule cross_class_cancel[OF finC finC disj subC subC])
    thus ?thesis
      using vpGge_C[OF muModPoly_vge[OF p p7
          vpGge_mul0[OF p vpGge_mul0[OF p vpGge_mul0[OF p vpGge_pow0[OF p vpGge_Dm[OF p]]
            vpGge_sqPoleProd[OF p]] oq_vge[OF p]] oq_vge[OF p]]]]
      by simp
  next
    case True
    have same: "outerGram K p $$ (x, y) =
      muXmod p (outerClassPoles K p a) (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K -
      outerClassPoles K p a) * oq K p ix * oq K p iy)"
      unfolding entry True[symmetric] by (rule same_class_cancel[OF finC subC])
    have R: "vpGge p (Dm (Nof K) ^ 5 * sqPoleProd (tailPoles K - outerClassPoles K p a) *
      oq K p ix * oq K p iy) 0"
      by (rule vpGge_mul0[OF p vpGge_mul0[OF p int0 oq_vge[OF p]] oq_vge[OF p]])
    show ?thesis unfolding same by (rule large_class_entry[OF p K K0 Kp a1 am R])
  qed
qed

text \<open>Proposition 4.3, second part: @{text "v_p^G(\<Delta>_K) \<ge> 0"}
  for @{text "p > K"}.\<close>
theorem DeltaK_vpGge_large_prime:
  assumes p: "prime p" and K: "40 dvd K" and Kp: "K < p"
  shows "vpGge p (DeltaK K) 0"
proof (cases "K = 0")
  case True
  have "DeltaK 0 = 1" by (simp add: DeltaK_def GK_def hof_def)
  thus ?thesis using True by (simp add: vpGge_one)
next
  case False
  hence K0: "0 < K" by simp
  define h where "h = hof K"
  define B where "B = Matrix.mat (hof K) (hof K) (\<lambda>(x,
    d). Polynomial.coeff (outerBasis K p (outer_idx K p ! x)) d)"
  have len: "length (outer_idx K p) = h"
  proof -
    obtain k where k: "K = 40 * k" using K by (elim dvdE)
    have p2: "2 < p" using K0 Kp k by simp
    have hk: "hof K = 37 * k" and Nk: "Nof K = 3 * k" unfolding k hof_def Nof_def by simp_all
    have "length (outer_idx K p) = (\<Sum> a \<in> set [0..<mHalf p + 1]. outerCount K p a)"
      unfolding outer_idx_def length_concat map_map
        by (simp add: o_def sum_list_distinct_conv_sum_set)
    also have "set [0..<mHalf p + 1] = {..mHalf p}" by auto
    also have "(\<Sum> a \<le> mHalf p. outerCount K p a) = card {Nof K + 1..K}"
      unfolding outerCount_def outerClassPoles_def by (rule sum_classes_card[OF p p2]) simp
    also have "\<dots> = h" using hk Nk k by (simp add: h_def)
    finally show ?thesis .
  qed
  have Bc: "B \<in> carrier_mat h h" and Gc: "GK K \<in>
    carrier_mat h h" and OGc: "outerGram K p \<in> carrier_mat h h"
    by (simp_all add: B_def GK_def outerGram_def h_def len Let_def)
  have uni: "Determinant.det B \<noteq> 0 \<and> vp p (Determinant.det B) = 0"
    unfolding B_def by (rule outerBasis_unimodular_large[OF p K K0 Kp])
  have conj: "outerGram K p = map_mat (\<lambda>q. [:q:]) B * GK K *
    transpose_mat (map_mat (\<lambda>q. [:q:]) B)"
  proof -
    have lenH: "length (outer_idx K p) = hof K" using len unfolding h_def by blast
    have "outerGram K p = map_mat (\<lambda>q. [:q:]) B * Aout K p *
      transpose_mat (map_mat (\<lambda>q. [:q:]) B)"
      unfolding B_def using outerGram_eq_conj_gen[OF lenH degree_outerBasis_lt_large[OF p K K0 Kp]]
        by blast
    thus ?thesis using G_eq_Aout_large[OF p K K0 Kp] by simp
  qed
  have gramv: "vpGge p (Determinant.det (outerGram K p)) 0"
    by (rule vpGge_det_of_terms[OF p OGc]) (use outerGram_int_large[OF p K K0 Kp] len in \<open>auto
      intro!: vpGge_prod[OF p, where b =
      "\<lambda>_. 0", simplified] simp: permutes_in_image\<close>)
  show ?thesis
    unfolding DeltaK_def
    by (rule det_gram_transfer[OF p Gc Bc conjunct1[OF uni] conjunct2[OF uni]]) (use gramv conj in
      simp)
qed

end


