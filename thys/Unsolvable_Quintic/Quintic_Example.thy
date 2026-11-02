section \<open>A Concrete Quintic with Galois Group \<open>S\<^sub>5\<close>\<close>

theory Quintic_Example
  imports
    "HOL-New_Algebra.Complex_Field_Extension"
    "HOL-New_Algebra.Abel_Ruffini"
    "HOL-New_Algebra.Galois_Transitivity"
    "HOL-Computational_Algebra.Polynomial_Factorial"
    "Sturm_Sequences.Sturm"
begin

text \<open>
  We study the quintic \<open>x\<^sup>5 - 4x + 2\<close> over the rationals.  It is irreducible (Eisenstein at
  \<open>2\<close>, proved here directly) and has exactly three real roots and one pair of
  complex-conjugate roots (the real-root count via the \<open>sturm\<close> method of
  @{theory "Sturm_Sequences.Sturm"}).  These are the hypotheses from which its Galois group is
  shown to be \<open>S\<^sub>5\<close>.
\<close>

subsection \<open>Eisenstein's irreducibility criterion\<close>

text \<open>A general form of Eisenstein's criterion over the integers: a polynomial satisfying the
  Eisenstein conditions for a prime @{term p} has no factorisation into two factors of
  positive degree.\<close>

lemma sum_atMost_split: "(\<Sum>l\<le>(i::nat). F l) = F i + (\<Sum>l<i. F l)"
  by (metis add.commute lessThan_Suc_atMost sum.lessThan_Suc)

lemma eisenstein_factor_helper:
  fixes f g h :: "int poly" and p :: int
  assumes prime: "prime p"
    and fgh: "f = g * h"
    and lead: "\<not> p dvd lead_coeff g"
    and mid: "\<And>i. i < degree f \<Longrightarrow> p dvd coeff f i"
    and ph0: "\<not> p dvd coeff h 0"
    and dg: "0 < degree g" and dh: "0 < degree h"
  shows False
proof -
  have g0: "g \<noteq> 0" and h0: "h \<noteq> 0" using dg dh by auto
  have df: "degree f = degree g + degree h" using fgh g0 h0 by (simp add: degree_mult_eq)
  have all_dvd: "p dvd coeff g i" if "i \<le> degree g" for i
    using that 
  proof (induct i rule: less_induct)
    case (less i)
    have ilt: "i < degree f" using less.prems df dh by simp
    have "coeff f i = (\<Sum>l\<le>i. coeff g l * coeff h (i - l))" using fgh by (simp add: coeff_mult)
    also have "\<dots> = coeff g i * coeff h 0 + (\<Sum>l<i. coeff g l * coeff h (i - l))"
      by (subst sum_atMost_split) simp
    finally have eq: "coeff f i = coeff g i * coeff h 0 + (\<Sum>l<i. coeff g l * coeff h (i - l))" .
    have psum: "p dvd (\<Sum>l<i. coeff g l * coeff h (i - l))"
      by (intro dvd_sum) (use less.hyps less.prems in auto)
    then have "p dvd coeff g i * coeff h 0" 
      by (metis (lifting) eq psum ilt mid add.commute dvd_add_right_iff)
    then show "p dvd coeff g i" using ph0 prime by (auto dest: prime_dvd_multD)
  qed
  have "p dvd lead_coeff g" using all_dvd[of "degree g"] by simp
  with lead show False ..
qed

lemma eisenstein_no_factor:
  fixes f g h :: "int poly" and p :: int
  assumes prime: "prime p"
    and fgh: "f = g * h"
    and lead: "\<not> p dvd lead_coeff f"
    and mid: "\<And>i. i < degree f \<Longrightarrow> p dvd coeff f i"
    and const: "\<not> p^2 dvd coeff f 0"
    and dg: "0 < degree g" and dh: "0 < degree h"
  shows False
proof -
  have "lead_coeff f = lead_coeff g * lead_coeff h" using fgh by (simp add: lead_coeff_mult)
  then have lg: "\<not> p dvd lead_coeff g" and lh: "\<not> p dvd lead_coeff h"
    using lead by (auto simp: prime_dvd_mult_iff[OF prime])
  have "coeff f 0 = coeff g 0 * coeff h 0" using fgh by (simp add: coeff_mult_0)
  then have "\<not> (p dvd coeff g 0 \<and> p dvd coeff h 0)"
    by (metis const mult_dvd_mono power2_eq_square)
  then show False
    by (metis dg dh eisenstein_factor_helper fgh lg lh mid mult.commute prime)
qed


subsection \<open>The polynomial and its real roots\<close>

text \<open>The quintic, as an integer polynomial; it is irreducible by Eisenstein at @{term 2}.\<close>
definition PhiZ :: "int poly" 
  where "PhiZ \<equiv> [:2, -4, 0, 0, 0, 1:]"

lemma degree_PhiZ: "degree PhiZ = 5" 
  by (simp add: PhiZ_def)

lemma content_PhiZ: "Polynomial.content PhiZ = 1" 
  by (simp add: PhiZ_def content_def)

lemma PhiZ_coeffs:
  "coeff PhiZ 0 = 2" "coeff PhiZ 1 = -4" "coeff PhiZ 2 = 0"
  "coeff PhiZ 3 = 0" "coeff PhiZ 4 = 0" "coeff PhiZ 5 = 1"
  by (simp_all add: PhiZ_def coeff_pCons numeral_eq_Suc)

text \<open>A degree-0 factor of @{term PhiZ} is a unit.\<close>
lemma PhiZ_deg0_factor_unit:
  assumes eq: "PhiZ = smult c q" 
  shows "[:c:] dvd 1"
proof -
  have "normalize c dvd 1" using content_PhiZ
    by (metis eq content_smult dvd_def)
  then show "[:c:] dvd 1" by (simp add: is_unit_const_poly_iff)
qed

theorem irreducible_PhiZ: "irreducible PhiZ"
proof (rule irreducibleI)
  show "PhiZ \<noteq> 0" by (simp add: PhiZ_def)
  show "\<not> PhiZ dvd 1" using degree_PhiZ by (auto dest!: dvd_imp_degree_le)
next
  fix a b 
  assume eq: "PhiZ = a * b"
  show "a dvd 1 \<or> b dvd 1"
  proof (rule ccontr)
    assume "\<not> (a dvd 1 \<or> b dvd 1)"
    then have \<section>: False if "degree a = 0 \<or> degree b = 0"
      by (metis degree_eq_zeroE that PhiZ_deg0_factor_unit eq  mult_smult_right smult_one mult.commute)
    show False
    proof (rule eisenstein_no_factor[OF _ eq _ _ _])
      show "\<And>i. i < degree PhiZ \<Longrightarrow> (2::int) dvd coeff PhiZ i"
        using degree_PhiZ PhiZ_coeffs by (auto simp: less_Suc_eq numeral_eq_Suc)
    qed (use PhiZ_coeffs degree_PhiZ \<section> in force)+
  qed
qed


subsection \<open>The real polynomial and its real roots\<close>

definition Phi :: "real poly" 
  where "Phi \<equiv> [:2, -4, 0, 0, 0, 1:]"

lemma Phi_eval: "poly Phi x = x^5 - 4*x + 2"
  by (simp add: Phi_def eval_nat_numeral algebra_simps)

lemma degree_Phi: "degree Phi = 5"
  by (simp add: Phi_def)

text \<open>At least three real roots, in disjoint intervals.\<close>
lemma Phi_root_neg: "\<exists>x. -2 < x \<and> x < 0 \<and> poly Phi x = 0"
  using poly_IVT_pos[of "-2" 0 Phi]  by (simp add: Phi_eval)

lemma Phi_root_01: "\<exists>x. 0 < x \<and> x < 1 \<and> poly Phi x = 0"
  using poly_IVT_neg[of 0 1 Phi] by (simp add: Phi_eval)

lemma Phi_root_12: "\<exists>x. 1 < x \<and> x < 2 \<and> poly Phi x = 0"
  using poly_IVT_pos[of 1 2 Phi] by (simp add: Phi_eval)

text \<open>The Sturm method counts the real roots: there are exactly three.\<close>
theorem Phi_three_real_roots: "card {x::real. poly Phi x = 0} = 3"
  unfolding Phi_def by sturm


subsection \<open>The complex roots: three real and one conjugate pair\<close>

text \<open>The same polynomial over the complex numbers.\<close>
definition PhiC :: "complex poly" where "PhiC \<equiv> [:2, -4, 0, 0, 0, 1:]"

lemma degree_PhiC: "degree PhiC = 5" 
  by (simp add: PhiC_def)

lemma PhiC_nonzero: "PhiC \<noteq> 0"
  by (simp add: PhiC_def)

lemma PhiC_eval: "poly PhiC x = x^5 - 4*x + 2"
  by (simp add: PhiC_def eval_nat_numeral algebra_simps)

lemma pderiv_PhiC: "pderiv PhiC = [:-4, 0, 0, 0, 5:]"
  by (simp add: PhiC_def pderiv_pCons)

lemma pderiv_PhiC_eval: "poly (pderiv PhiC) x = 5*x^4 - 4"
  by (simp add: pderiv_PhiC eval_nat_numeral algebra_simps)

text \<open>The quintic is squarefree: it shares no root with its derivative.  (A common root would
  force \<open>x = 5/8\<close>, which does not satisfy \<open>5x\<^sup>4 = 4\<close>.)\<close>
lemma PhiC_rsquarefree: "rsquarefree PhiC"
  unfolding rsquarefree_roots PhiC_eval pderiv_PhiC_eval
  by algebra

lemma PhiC_roots_finite: "finite {z. poly PhiC z = 0}"
  using PhiC_nonzero poly_roots_finite by blast

text \<open>Being squarefree of degree 5, it has exactly five distinct complex roots.\<close>
theorem card_PhiC_roots: "card {z. poly PhiC z = 0} = 5"
proof -
  have decomp: "smult (lead_coeff PhiC) (\<Prod>z | poly PhiC z = 0. [:- z, 1:]) = PhiC"
    using PhiC_rsquarefree by (rule complex_poly_decompose_rsquarefree)
  have lead: "lead_coeff PhiC = 1" by (simp add: PhiC_def)
  have "degree PhiC = degree (\<Prod>z | poly PhiC z = 0. [:- z, 1:])"
    by (metis decomp lead smult_1_left)
  also have "\<dots> = (\<Sum>z | poly PhiC z = 0. degree [:- z, 1:])"
    by (simp add: degree_prod_eq_sum_degree)
  also have "\<dots> = card {z. poly PhiC z = 0}" by simp
  finally show ?thesis using degree_PhiC by simp
qed

text \<open>The real complex-roots are the images of the real roots, hence number three.\<close>
lemma poly_PhiC_of_real: "poly PhiC (complex_of_real x) = complex_of_real (poly Phi x)"
  by (simp add: PhiC_eval Phi_eval)

lemma real_roots_PhiC: "{z. poly PhiC z = 0 \<and> z \<in> \<real>} = complex_of_real ` {x. poly Phi x = 0}"
  by (auto simp: poly_PhiC_of_real elim!: Reals_cases)

theorem card_real_roots_PhiC: "card {z. poly PhiC z = 0 \<and> z \<in> \<real>} = 3"
  by (simp add: Phi_three_real_roots card_image inj_on_def real_roots_PhiC)

text \<open>Conjugation maps roots to roots (the coefficients are real).\<close>
lemma cnj_poly_PhiC: "poly PhiC (cnj z) = cnj (poly PhiC z)"
  by (simp add: PhiC_eval)

lemma cnj_root_PhiC: "poly PhiC z = 0 \<Longrightarrow> poly PhiC (cnj z) = 0"
  by (simp add: cnj_poly_PhiC)

text \<open>Hence exactly two non-real roots.\<close>
theorem card_nonreal_roots_PhiC: "card {z. poly PhiC z = 0 \<and> z \<notin> \<real>} = 2"
proof -
  have part: "{z. poly PhiC z = 0} = {z. poly PhiC z = 0 \<and> z \<in> \<real>} \<union> {z. poly PhiC z = 0 \<and> z \<notin> \<real>}" 
    by auto
  have "{z. poly PhiC z = 0 \<and> z \<in> \<real>} \<inter> {z. poly PhiC z = 0 \<and> z \<notin> \<real>} = {}" by auto
  then have "card {z. poly PhiC z = 0} = card {z. poly PhiC z = 0 \<and> z \<in> \<real>} + card {z. poly PhiC z = 0 \<and> z \<notin> \<real>}"
    using part PhiC_roots_finite by (metis (no_types, lifting) card_Un_disjoint finite_Un)
  then show ?thesis using card_PhiC_roots card_real_roots_PhiC by simp
qed

lemma cnj_notreal: "z \<notin> \<real> \<Longrightarrow> cnj z \<notin> \<real>"
  by (simp add: Reals_cnj_iff)

lemma cnj_ne_self_of_notreal: "z \<notin> \<real> \<Longrightarrow> z \<noteq> cnj z"
  by (metis Reals_cnj_iff)

text \<open>The two non-real roots form a single conjugate pair, so complex conjugation transposes
  them while fixing the three real roots.\<close>
lemma nonreal_roots_conj_pair:
  obtains a where "{z. poly PhiC z = 0 \<and> z \<notin> \<real>} = {a, cnj a}" and "a \<noteq> cnj a"
    and "poly PhiC a = 0" and "a \<notin> \<real>"
proof -
  obtain a where a: "poly PhiC a = 0" and anr: "a \<notin> \<real>"
    using card_nonreal_roots_PhiC that unfolding card_2_iff' by blast
  then have sub: "{a, cnj a} \<subseteq> {z. poly PhiC z = 0 \<and> z \<notin> \<real>}" 
    using cnj_notreal cnj_root_PhiC by blast
  have ne: "a \<noteq> cnj a"
    by (simp add: anr cnj_ne_self_of_notreal)
  have card2: "card {a, cnj a} = 2" using ne by simp
  have fin: "finite {z. poly PhiC z = 0 \<and> z \<notin> \<real>}" using PhiC_roots_finite by simp
  have "{z. poly PhiC z = 0 \<and> z \<notin> \<real>} = {a, cnj a}"
    using sub card2 card_nonreal_roots_PhiC fin by (metis card_subset_eq)
  with ne a anr show ?thesis using that by blast
qed

text \<open>Summary of the root structure feeding the Galois-group argument.\<close>
theorem PhiC_root_structure:
  "card {z. poly PhiC z = 0} = 5 \<and>
   card {z. poly PhiC z = 0 \<and> z \<in> \<real>} = 3 \<and>
   card {z. poly PhiC z = 0 \<and> z \<notin> \<real>} = 2 \<and>
   (\<forall>z. poly PhiC z = 0 \<longrightarrow> poly PhiC (cnj z) = 0)"
  using card_PhiC_roots card_real_roots_PhiC card_nonreal_roots_PhiC cnj_root_PhiC by blast


subsection \<open>Irreducibility of the quintic over the rationals\<close>

text \<open>The complex quintic is the @{term of_int}-image of the integer quintic, equivalently the
  @{term of_rat}-image of its rational version.\<close>
lemma PhiC_eq_map_of_int: "PhiC = map_poly of_int PhiZ"
  by (simp add: PhiC_def PhiZ_def map_poly_pCons)

lemma map_of_rat_of_int_PhiZ:
  "map_poly of_rat (map_poly of_int PhiZ :: rat poly) = (PhiC :: complex poly)"
  by (simp add: PhiC_eq_map_of_int PhiZ_def map_poly_pCons)

theorem irreducible_over_Rats_PhiC: "irreducible_over (\<rat> :: complex set) PhiC"
proof -
  have degree_PhiZ_ne0: "degree PhiZ \<noteq> 0"
    by (simp add: degree_PhiZ)
  have "irreducible (map_poly of_int PhiZ :: rat poly)"
    using irreducible_PhiZ degree_PhiZ_ne0 content_PhiZ
    by (metis Polynomial_Factorial.irreducible_int_imp_rat)
  moreover have "degree (map_poly of_int PhiZ :: rat poly) > 0"
    by (simp add: degree_PhiZ degree_map_poly)
  ultimately show ?thesis
    using irreducible_imp_irreducible_over_Rats map_of_rat_of_int_PhiZ by fastforce
qed


subsection \<open>The Galois group of the quintic is not solvable\<close>

text \<open>The quintic has rational (indeed integer) coefficients.\<close>
lemma PhiC_poly_over_Rats: "PhiC \<in> poly_over (\<rat> :: complex set)"
  by (simp add: PhiC_eq_map_of_int coeff_map_poly poly_over_iff_aux)

text \<open>Relabelling an involution that swaps exactly two points yields a transposition.  Here
  @{term \<tau>} is an involution of the finite set @{term X} enumerated by @{term e}, fixing every
  point except the pair @{term "{a, \<tau> a}"}.\<close>
lemma pull_involution_two_points_transpose:
  fixes e :: "nat \<Rightarrow> complex" and X :: "complex set" and \<tau> :: "complex \<Rightarrow> complex" and n :: nat
  assumes ebij: "bij_betw e {0..<n} X"
    and tauX: "\<tau> ` X = X"
    and invol: "\<And>x. x \<in> X \<Longrightarrow> \<tau> (\<tau> x) = x"
    and a: "a \<in> X" and ta: "\<tau> a \<in> X" and ane: "a \<noteq> \<tau> a"
    and fixed: "\<And>x. x \<in> X \<Longrightarrow> x \<noteq> a \<Longrightarrow> x \<noteq> \<tau> a \<Longrightarrow> \<tau> x = x"
  defines "i \<equiv> inv_into {0..<n} e a" and "j \<equiv> inv_into {0..<n} e (\<tau> a)"
  shows "pull n e (restrict \<tau> X) = Transposition.transpose i j"
proof
  fix k
  obtain e: "e i = a"  "e j = \<tau> a" and ln: "i < n" "j < n"
    unfolding i_def j_def using ebij a ta by (meson e_inv_e inv_e_lt) 
  show "pull n e (restrict \<tau> X) k = Transposition.transpose i j k"
  proof (cases "k < n")
    case False
    then show ?thesis using ln by (simp add: pull_def transpose_def)
  next
    case True
    have ekX: "e k \<in> X" using ebij True by (auto simp: bij_betw_def)
    have "pull n e (restrict \<tau> X) k = inv_into {0..<n} e (\<tau> (e k))"
      using True ekX by (simp add: pull_def)
    also have "\<dots> = Transposition.transpose i j k"
      using True a ebij e ekX fixed invol 
      unfolding i_def j_def by (metis inv_e_e transpose_eq_iff)
    finally show ?thesis .
  qed
qed


subsection \<open>The main theorem\<close>

text \<open>The Galois group of the quintic \<open>x^5 - 4x + 2\<close> --- the group of automorphisms of its
  splitting subfield of @{typ complex} fixing @{term \<rat>} --- is not solvable. 
  This will imply that the quintic is not solvable by radicals.\<close>
theorem quintic_galois_group_not_solvable:
  defines "X \<equiv> {z. poly PhiC z = 0}"
  defines "K \<equiv> generate_field (\<rat> \<union> X)"
  shows "\<not> Group.solvable (field_auto K \<rat>) (compose K) (identity K)"
proof -
  \<comment> \<open>The base field and ambient setup.\<close>
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  obtain finX: "finite X" and cardX: "card X = 5" 
    using card_PhiC_roots by (fastforce simp: X_def)
  have FK: "(\<rat> :: complex set) \<subseteq> K" unfolding K_def using subset_generate_field by blast
  have XK: "X \<subseteq> K" unfolding K_def using subset_generate_field by blast
  have sfK: "Subfield K" unfolding K_def by (rule subfield_generate_field)
  have closed: "\<exists>b. poly q b = 0" if "0 < degree q" for q :: "complex poly"
    using that by (intro fundamental_theorem_of_algebra) (simp add: constant_degree)
  \<comment> \<open>The Galois group acts on the roots.\<close>
  interpret GA: Group_Action "field_auto K \<rat>" "compose K" "identity K" "\<lambda>\<sigma>. restrict \<sigma> X" X
    using FK PhiC_poly_over_Rats XK X_def finX galois_group_action sfK sfQ by blast
  \<comment> \<open>An enumeration of the five roots.\<close>
  obtain e where ebij: "bij_betw e {0..<(5::nat)} X"
    using ex_bij_betw_nat_finite[OF finX] cardX by force
  \<comment> \<open>Faithfulness: an automorphism fixing every root (and \<open>\<rat>\<close>) is the identity on \<open>K\<close>.\<close>
  have Kgen: "K = gen_subfield (\<rat> \<union> X)"
    by (simp add: K_def gen_subfield_eq_generate_field)
  have faith: "GA.faithful"
    unfolding GA.faithful_def
  proof (intro ballI impI)
    fix \<sigma> assume s: "\<sigma> \<in> field_auto K \<rat>" and triv: "\<forall>x\<in>X. restrict \<sigma> X x = x"
    have sgen: "\<sigma> \<in> field_auto (gen_subfield (\<rat> \<union> X)) \<rat>" using s Kgen by simp
    have "complex_subfield K" using sfK by (simp add: complex_subfield_iff_subfield)
    then have allK: "\<forall>x\<in>K. \<sigma> x = x"
      by (metis Kgen field_auto_faithful restrict_apply s triv)
    have sext: "\<sigma> \<in> K \<rightarrow>\<^sub>E K" using s by (simp only: field_auto_mem_iff)
    with allK show "\<sigma> = identity K"
      by (metis PiE_restrict restrict_ext) 
  qed
  \<comment> \<open>Finiteness of the Galois group: it embeds into the finite symmetric group on @{term X}.\<close>
  have finGal: "finite (field_auto K \<rat>)"
  proof -
    have "inj_on (\<lambda>\<sigma>. restrict \<sigma> X) (field_auto K \<rat>)"
      using GA.faithful_inj [OF faith] inj_on_restrict_eq by blast
    moreover have "(\<lambda>\<sigma>. restrict \<sigma> X) ` field_auto K \<rat> \<subseteq> transformations.Sym X"
      using GA.hom_closed by auto
    moreover have "finite (transformations.Sym X)"
      by (metis GA.mem_UnitsD finX finite_PiE finite_subset subsetI)
    ultimately show ?thesis by (metis inj_on_finite finite_subset)
  qed
  \<comment> \<open>Transitivity: the orbit of any root is all of X.\<close>
  have trans: "\<exists>s\<in>X. GA.orbit s = X"
  proof -
    obtain a where aX: "a \<in> X" using cardX by (metis card.empty equals0I zero_neq_numeral)
    have surj: "\<forall>b\<in>X. \<exists>\<sigma>\<in>field_auto K \<rat>. restrict \<sigma> X a = b"
      using galois_action_transitive[OF sfQ finX PhiC_poly_over_Rats irreducible_over_Rats_PhiC _ closed aX] 
      unfolding K_def X_def by blast
    have "X \<subseteq> GA.orbit a"
      using GA.orbit_mem_iff aX surj by force
    then show ?thesis using aX GA.orbit_subset by blast
  qed
  \<comment> \<open>Complex conjugation contributes a transposition to the image.\<close>
  have transp: "\<exists>i j. i < 5 \<and> j < 5 \<and> i \<noteq> j
                  \<and> Transposition.transpose i j \<in> (\<lambda>\<sigma>. pull 5 e (restrict \<sigma> X)) ` field_auto K \<rat>"
  proof -
    have cnjXX: "cnj ` X = X"
      unfolding X_def using cnj_image_eq cnj_poly_PhiC by force
    obtain a where Xnr: "{z. poly PhiC z = 0 \<and> z \<notin> \<real>} = {a, cnj a}" and ane: "a \<noteq> cnj a"
      and aroot: "poly PhiC a = 0" and anr: "a \<notin> \<real>" by (rule nonreal_roots_conj_pair)
    have aX: "a \<in> X" using aroot unfolding X_def by simp
    have caX: "cnj a \<in> X" using aroot cnj_root_PhiC unfolding X_def by simp
    \<comment> \<open>cnj is the field automorphism that fixes \<open>\<rat>\<close>, and on \<open>X\<close> moves exactly @{term a}, @{term "cnj a"}.\<close>
    have cnjK: "cnj ` K = K"
      using Kgen cnjXX splitting_subfield_cnj_closed by presburger
    have QR: "(\<rat> :: complex set) \<subseteq> \<real>"
      using Reals_cnj_iff cnj_fixes_Rats by blast
    have cnjaut: "restrict cnj K \<in> field_auto K \<rat>"
      using FK QR cnjK cnj_field_auto complex_subfield_iff_subfield sfK by presburger
    \<comment> \<open>On X, cnj fixes everything except the conjugate pair.\<close>
    have fixed: "cnj x = x" if "x \<in> X" "x \<noteq> a" "x \<noteq> cnj a" for x
      using Reals_cnj_iff X_def Xnr that by blast
    have invol: "cnj (cnj x) = x" for x by simp
    \<comment> \<open>So the relabelling of cnj is a transposition.\<close>
    define i where "i \<equiv> inv_into {0..<5} e a"
    define j where "j \<equiv> inv_into {0..<5} e (cnj a)"
    have pull_t: "pull 5 e (restrict cnj X) = Transposition.transpose i j"
      unfolding i_def j_def
      by (rule pull_involution_two_points_transpose[OF ebij cnjXX invol aX caX ane fixed])
    obtain 5: "i < 5" "j < 5" unfolding i_def j_def
      by (meson ebij aX caX  inv_e_lt)
    have inej: "i \<noteq> j"
      unfolding i_def j_def by (metis aX ane caX e_inv_e ebij)
    \<comment> \<open>This transposition is the image of the conjugation automorphism.\<close>
    have "Transposition.transpose i j = pull 5 e (restrict (restrict cnj K) X)"
      using pull_t by (simp add: Int_absorb1 XK)
    then have "Transposition.transpose i j \<in> (\<lambda>\<sigma>. pull 5 e (restrict \<sigma> X)) ` field_auto K \<rat>"
      using cnjaut by blast
    then show ?thesis using 5 inej by blast
  qed
  \<comment> \<open>Assemble via the abstract Abel--Ruffini theorem (@{term "p = 5"}).\<close>
  show ?thesis
    by (rule GA.not_solvable_of_transitive_with_transposition
              [OF ebij _ _ finGal faith trans transp]) auto
qed

end
