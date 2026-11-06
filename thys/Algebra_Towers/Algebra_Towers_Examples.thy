theory Algebra_Towers_Examples
  imports
    Algebra_Norm
    "HOL-Computational_Algebra.Primes"
begin

section \<open>Examples\<close>

subsection \<open>Finite-field towers\<close>

datatype gf4 = GF4 bool bool

instantiation gf4 :: field
begin

definition zero_gf4 :: gf4
  where "zero_gf4 = GF4 False False"

definition one_gf4 :: gf4
  where "one_gf4 = GF4 True False"

fun plus_gf4 :: "gf4 \<Rightarrow> gf4 \<Rightarrow> gf4"
  where "plus_gf4 (GF4 a b) (GF4 c d) =
    GF4 (a \<noteq> c) (b \<noteq> d)"

fun uminus_gf4 :: "gf4 \<Rightarrow> gf4"
  where "uminus_gf4 (GF4 a b) = GF4 a b"

definition minus_gf4 :: "gf4 \<Rightarrow> gf4 \<Rightarrow> gf4"
  where "minus_gf4 x y = x + y"

fun times_gf4 :: "gf4 \<Rightarrow> gf4 \<Rightarrow> gf4"
  where "times_gf4 (GF4 a b) (GF4 c d) =
    GF4 ((a \<and> c) \<noteq> (b \<and> d))
      (((a \<and> d) \<noteq> (b \<and> c)) \<noteq> (b \<and> d))"

fun inverse_gf4 :: "gf4 \<Rightarrow> gf4"
  where
    "inverse_gf4 (GF4 False False) = GF4 False False"
  | "inverse_gf4 (GF4 True False) = GF4 True False"
  | "inverse_gf4 (GF4 False True) = GF4 True True"
  | "inverse_gf4 (GF4 True True) = GF4 False True"

definition divide_gf4 :: "gf4 \<Rightarrow> gf4 \<Rightarrow> gf4"
  where "divide_gf4 x y = x * inverse y"

lemma inverse_times_gf4:
  assumes "x \<noteq> (0 :: gf4)"
  shows "inverse x * x = 1"
proof (cases x)
  case (GF4 a b)
  then show ?thesis
    using assms
    by (cases a; cases b;
        simp add: zero_gf4_def one_gf4_def)
qed

instance
  apply standard
  subgoal for a b c
    by (cases a; cases b; cases c; auto)
  subgoal for a b
    by (cases a; cases b; auto)
  subgoal for a
    by (cases a; auto simp: one_gf4_def)
  subgoal for a b c
    by (cases a; cases b; cases c; auto)
  subgoal for a b
    by (cases a; cases b; auto)
  subgoal for a
    by (cases a; auto simp: zero_gf4_def)
  subgoal for a
    by (cases a; auto simp: zero_gf4_def)
  subgoal for a b
    by (cases a; cases b; auto simp: minus_gf4_def)
  subgoal for a b c
    by (cases a; cases b; cases c; auto)
  apply (simp_all add: inverse_times_gf4 divide_gf4_def
      zero_gf4_def one_gf4_def)
  done

end

instance gf4 :: finite_field
proof
  show "finite (UNIV :: gf4 set)"
  proof (rule finite_subset)
    show "finite
      {GF4 False False, GF4 True False, GF4 False True, GF4 True True}"
      by simp
    show "UNIV \<subseteq>
      {GF4 False False, GF4 True False, GF4 False True, GF4 True True}"
    proof
      fix x :: gf4
      assume "x \<in> UNIV"
      obtain a b where "x = GF4 a b"
        by (cases x) simp
      show "x \<in>
        {GF4 False False, GF4 True False, GF4 False True, GF4 True True}"
        using \<open>x = GF4 a b\<close>
        by (cases a; cases b; simp)
    qed
  qed
qed

locale finite_field_tower_example =
  indexed_field_algebra_tower rS sA rA lower_basis upper_basis
  for rS :: "'r::finite_field \<Rightarrow> 's::finite_field \<Rightarrow> 's"
    and sA :: "'s \<Rightarrow> 'a::finite_field \<Rightarrow> 'a"
    and rA :: "'r \<Rightarrow> 'a \<Rightarrow> 'a"
    and lower_basis :: "'i::finite \<Rightarrow> 's"
    and upper_basis :: "'j::finite \<Rightarrow> 'a"
begin

sublocale dimensions: indexed_field_tower
  rS sA rA lower_basis upper_basis
  by unfold_locales

theorem finite_field_tower_dimension:
  "dimensions.direct_space.dim UNIV =
    dimensions.lower_space.dim UNIV *
      dimensions.upper_space.dim UNIV"
  by (rule dimensions.finrank_tower)

theorem finite_field_tower_trace:
  "tower_algebra.algebra_trace a =
    lower_algebra.algebra_trace (upper_algebra.algebra_trace a)"
  by (rule algebra_trace_trans)

theorem finite_field_tower_norm:
  "tower_algebra.algebra_norm a =
    lower_algebra.algebra_norm (upper_algebra.algebra_norm a)"
  by (rule algebra_norm_trans)

end

text \<open>
The preceding locale covers arbitrary nested finite fields without imposing a
separability assumption.  The next example supplies a concrete nontrivial
extension: the four-element field is represented as
\<^term>\<open>GF4 a b\<close>, corresponding to \(a+b\alpha\) over
\(\mathbb F_2\), with \(\alpha^2=\alpha+1\).
\<close>

subsection \<open>The four-element field over \(\mathbb F_2\)\<close>

lemma gf2_cases [case_names zero one]:
  fixes r :: gf2
  obtains "r = 0" | "r = 1"
  by transfer auto

lemma gf2_one_add_one [simp]:
  "(1 :: gf2) + 1 = 0"
  by transfer simp

lemma gf2_two [simp]:
  "(2 :: gf2) = 0"
  using gf2_one_add_one
  by (simp only: one_add_one)

definition gf2_gf4_embed :: "gf2 \<Rightarrow> gf4"
  where "gf2_gf4_embed r = (if r = 0 then 0 else 1)"

definition gf2_gf4_scale :: "gf2 \<Rightarrow> gf4 \<Rightarrow> gf4"
  where "gf2_gf4_scale r x = gf2_gf4_embed r * x"

definition gf4_self_scale :: "gf4 \<Rightarrow> gf4 \<Rightarrow> gf4"
  where "gf4_self_scale r x = r * x"

lemma gf2_gf4_embed_zero [simp]:
  "gf2_gf4_embed 0 = 0"
  by (simp add: gf2_gf4_embed_def)

lemma gf2_gf4_embed_one [simp]:
  "gf2_gf4_embed 1 = 1"
  by (simp add: gf2_gf4_embed_def)

lemma gf2_gf4_embed_add [simp]:
  "gf2_gf4_embed (r + s) =
    gf2_gf4_embed r + gf2_gf4_embed s"
  by (cases r rule: gf2_cases; cases s rule: gf2_cases;
      simp add: gf2_gf4_embed_def zero_gf4_def one_gf4_def)

lemma gf2_gf4_embed_mult [simp]:
  "gf2_gf4_embed (r * s) =
    gf2_gf4_embed r * gf2_gf4_embed s"
  by (cases r rule: gf2_cases; cases s rule: gf2_cases;
      simp add: gf2_gf4_embed_def)

interpretation gf2_gf4: commutative_algebra gf2_gf4_scale
  by unfold_locales
    (simp_all add: gf2_gf4_scale_def algebra_simps)

interpretation gf4_self: commutative_algebra gf4_self_scale
  by unfold_locales
    (simp_all add: gf4_self_scale_def algebra_simps)

abbreviation gf4_alpha :: gf4
  where "gf4_alpha \<equiv> GF4 False True"

lemma gf4_one_ne_alpha [simp]:
  "(1 :: gf4) \<noteq> gf4_alpha"
  by (simp add: one_gf4_def)

definition gf4_basis :: "2 \<Rightarrow> gf4"
  where "gf4_basis i = (if i = 1 then 1 else gf4_alpha)"

definition gf4_unit_basis :: "1 \<Rightarrow> gf4"
  where "gf4_unit_basis i = 1"

definition gf4_tower_basis :: "(2 \<times> 1) \<Rightarrow> gf4"
  where "gf4_tower_basis ij =
    gf4_self_scale (gf4_basis (fst ij))
      (gf4_unit_basis (snd ij))"

lemma gf4_basis_range:
  "range gf4_basis = {1, gf4_alpha}"
proof -
  have index_cases: "i = 1 \<or> i = 2" for i :: 2
    using UNIV_2 by auto
  have subset: "range gf4_basis \<subseteq> {1, gf4_alpha}"
  proof
    fix x
    assume "x \<in> range gf4_basis"
    then obtain i where "x = gf4_basis i"
      by auto
    with index_cases[of i] show "x \<in> {1, gf4_alpha}"
      by (auto simp: gf4_basis_def)
  qed
  have "1 = gf4_basis (1 :: 2)"
    by (simp add: gf4_basis_def)
  moreover have "gf4_alpha = gf4_basis (2 :: 2)"
    by (simp add: gf4_basis_def one_gf4_def)
  ultimately have "{1, gf4_alpha} \<subseteq> range gf4_basis"
    by blast
  with subset show ?thesis
    by blast
qed

lemma gf4_basis_inj:
  "inj gf4_basis"
proof (rule injI)
  fix i j :: 2
  have i_cases: "i = 1 \<or> i = 2"
    using UNIV_2 by auto
  have j_cases: "j = 1 \<or> j = 2"
    using UNIV_2 by auto
  show "gf4_basis i = gf4_basis j \<Longrightarrow> i = j"
    using i_cases j_cases
    by (auto simp: gf4_basis_def one_gf4_def)
qed

lemma gf2_gf4_scale_one_zero_iff [simp]:
  "gf2_gf4_scale r 1 = 0 \<longleftrightarrow> r = 0"
  by (cases r rule: gf2_cases;
      simp add: gf2_gf4_scale_def gf2_gf4_embed_def)

lemma gf2_gf4_scale_alpha_zero_iff [simp]:
  "gf2_gf4_scale r gf4_alpha = 0 \<longleftrightarrow> r = 0"
  by (cases r rule: gf2_cases;
      simp add: gf2_gf4_scale_def gf2_gf4_embed_def
        zero_gf4_def one_gf4_def)

lemma gf4_linear_combination_zero_iff [simp]:
  "gf2_gf4_scale r 1 +
      gf2_gf4_scale s gf4_alpha = 0 \<longleftrightarrow>
    r = 0 \<and> s = 0"
  by (cases r rule: gf2_cases; cases s rule: gf2_cases;
      simp add: gf2_gf4_scale_def gf2_gf4_embed_def
        zero_gf4_def one_gf4_def)

lemma gf4_basis_independent:
  "gf2_gf4.independent (range gf4_basis)"
  unfolding gf2_gf4.independent_explicit_module
proof (intro allI impI)
  fix T c x
  assume subset: "T \<subseteq> range gf4_basis"
    and sum_zero:
      "(\<Sum>v\<in>T. gf2_gf4_scale (c v) v) = 0"
    and x: "x \<in> T"
  have T_cases:
    "T = {} \<or> T = {1} \<or> T = {gf4_alpha} \<or>
      T = {1, gf4_alpha}"
    using subset
    by (auto simp: gf4_basis_range)
  then consider
      (empty) "T = {}"
    | (one) "T = {1}"
    | (alpha) "T = {gf4_alpha}"
    | (both) "T = {1, gf4_alpha}"
    by blast
  then show "c x = 0"
  proof cases
    case empty
    with x show ?thesis
      by simp
  next
    case one
    have "c 1 = 0"
      using sum_zero
      by (simp add: one)
    with one x show ?thesis
      by simp
  next
    case alpha
    have "c gf4_alpha = 0"
      using sum_zero
      by (simp add: alpha)
    with alpha x show ?thesis
      by simp
  next
    case both
    have coefficients:
      "c 1 = 0 \<and> c gf4_alpha = 0"
      using sum_zero
      by (simp add: both)
    with both x show ?thesis
      by auto
  qed
qed

lemma gf4_basis_span:
  "gf2_gf4.span (range gf4_basis) = UNIV"
proof -
  have one_mem:
      "(1 :: gf4) \<in> gf2_gf4.span (range gf4_basis)"
    by (rule gf2_gf4.span_base)
      (auto simp: gf4_basis_range)
  have alpha_mem:
      "gf4_alpha \<in> gf2_gf4.span (range gf4_basis)"
    by (rule gf2_gf4.span_base)
      (auto simp: gf4_basis_range)
  have sum_mem:
      "1 + gf4_alpha \<in> gf2_gf4.span (range gf4_basis)"
    by (rule gf2_gf4.span_add[OF one_mem alpha_mem])
  have "x \<in> gf2_gf4.span (range gf4_basis)" for x
  proof (cases x)
    case (GF4 a b)
    then show ?thesis
      using gf2_gf4.span_zero one_mem alpha_mem sum_mem
      by (cases a; cases b;
          simp add: zero_gf4_def one_gf4_def)
  qed
  then show ?thesis
    by auto
qed

lemma gf4_unit_basis_inj:
  "inj gf4_unit_basis"
  by (auto simp: inj_def)

lemma gf4_unit_basis_range:
  "range gf4_unit_basis = {1}"
  by (auto simp: gf4_unit_basis_def)

lemma gf4_unit_basis_independent:
  "gf4_self.independent (range gf4_unit_basis)"
  unfolding gf4_self.independent_explicit_module
proof (intro allI impI)
  fix T c x
  assume subset: "T \<subseteq> range gf4_unit_basis"
    and sum_zero:
      "(\<Sum>v\<in>T. gf4_self_scale (c v) v) = 0"
    and x: "x \<in> T"
  have T: "T = {1}"
    using subset x
    by (auto simp: gf4_unit_basis_range gf4_unit_basis_def)
  have "c 1 = 0"
    using sum_zero
    by (simp add: T gf4_self_scale_def)
  with T x show "c x = 0"
    by simp
qed

lemma gf4_unit_basis_span:
  "gf4_self.span (range gf4_unit_basis) = UNIV"
proof -
  have one_mem:
      "(1 :: gf4) \<in> gf4_self.span (range gf4_unit_basis)"
    by (rule gf4_self.span_base)
      (auto simp: gf4_unit_basis_def)
  have "x \<in> gf4_self.span (range gf4_unit_basis)" for x
  proof -
    have "gf4_self_scale x 1 \<in>
        gf4_self.span (range gf4_unit_basis)"
      by (rule gf4_self.span_scale[OF one_mem])
    then show ?thesis
      by (simp add: gf4_self_scale_def)
  qed
  then show ?thesis
    by auto
qed

lemma gf4_unit_basis_independent_single:
  "gf4_self.independent {gf4_unit_basis (1 :: 1)}"
  using gf4_unit_basis_independent
  by (simp add: gf4_unit_basis_range gf4_unit_basis_def)

lemma gf4_unit_basis_span_single:
  "gf4_self.span {gf4_unit_basis (1 :: 1)} = UNIV"
  using gf4_unit_basis_span
  by (simp add: gf4_unit_basis_range gf4_unit_basis_def)

interpretation gf4_over_gf2:
    indexed_algebra gf2_gf4_scale gf4_basis
  by unfold_locales
    (fact gf4_basis_inj gf4_basis_independent
      gf4_basis_span)+

interpretation gf4_over_itself:
    indexed_algebra gf4_self_scale gf4_unit_basis
  by unfold_locales
    (fact gf4_unit_basis_inj gf4_unit_basis_independent
      gf4_unit_basis_span)+

interpretation gf4_over_gf2_space: vector_space gf2_gf4_scale
  using gf2_gf4.module_axioms
  by (simp add: module_iff_vector_space)

definition gf2_of_bool :: "bool \<Rightarrow> gf2"
  where "gf2_of_bool b = (if b then 1 else 0)"

text \<open>The Boolean coordinates of an element determine its coefficients in
this basis of the four-element field over the two-element field.\<close>

lemma gf4_expansion_coefficients:
  "gf2_gf4_scale r 1 +
      gf2_gf4_scale s gf4_alpha = GF4 a b \<longleftrightarrow>
    r = gf2_of_bool a \<and> s = gf2_of_bool b"
  by (cases r rule: gf2_cases; cases s rule: gf2_cases)
    (cases a; cases b; simp add: gf2_of_bool_def gf2_gf4_scale_def
      gf2_gf4_embed_def zero_gf4_def one_gf4_def)+

lemma gf4_coordinate_one [simp]:
  "gf4_over_gf2.coordinates.coordinate (GF4 a b) (1 :: 2) =
    gf2_of_bool a"
proof -
  have expansion:
    "gf2_gf4_scale
        (gf4_over_gf2.coordinates.coordinate (GF4 a b) (1 :: 2)) 1 +
      gf2_gf4_scale
        (gf4_over_gf2.coordinates.coordinate (GF4 a b) (2 :: 2))
          gf4_alpha =
      GF4 a b"
    using gf4_over_gf2.coordinates.basis_expansion[of "GF4 a b"]
    by (simp add: UNIV_2 gf4_basis_def one_gf4_def)
  show ?thesis
    using gf4_expansion_coefficients[THEN iffD1, OF expansion]
    by simp
qed

lemma gf4_coordinate_two [simp]:
  "gf4_over_gf2.coordinates.coordinate (GF4 a b) (2 :: 2) =
    gf2_of_bool b"
proof -
  have expansion:
    "gf2_gf4_scale
        (gf4_over_gf2.coordinates.coordinate (GF4 a b) (1 :: 2)) 1 +
      gf2_gf4_scale
        (gf4_over_gf2.coordinates.coordinate (GF4 a b) (2 :: 2))
          gf4_alpha =
      GF4 a b"
    using gf4_over_gf2.coordinates.basis_expansion[of "GF4 a b"]
    by (simp add: UNIV_2 gf4_basis_def one_gf4_def)
  show ?thesis
    using gf4_expansion_coefficients[THEN iffD1, OF expansion]
    by simp
qed

lemma gf4_regular_matrix_11 [simp]:
  "gf4_over_gf2.regular_matrix (GF4 a b) $
      (1 :: 2) $ (1 :: 2) = gf2_of_bool a"
  by (cases a; cases b;
      simp add: gf4_over_gf2.regular_matrix_def
        gf2_gf4.left_multiplication_def gf4_basis_def
        gf2_of_bool_def one_gf4_def)

lemma gf4_regular_matrix_12 [simp]:
  "gf4_over_gf2.regular_matrix (GF4 a b) $
      (1 :: 2) $ (2 :: 2) = gf2_of_bool b"
  by (cases a; cases b;
      simp add: gf4_over_gf2.regular_matrix_def
        gf2_gf4.left_multiplication_def gf4_basis_def
        gf2_of_bool_def one_gf4_def)

lemma gf4_regular_matrix_21 [simp]:
  "gf4_over_gf2.regular_matrix (GF4 a b) $
      (2 :: 2) $ (1 :: 2) = gf2_of_bool b"
  by (cases a; cases b;
      simp add: gf4_over_gf2.regular_matrix_def
        gf2_gf4.left_multiplication_def gf4_basis_def
        gf2_of_bool_def one_gf4_def)

lemma gf4_regular_matrix_22 [simp]:
  "gf4_over_gf2.regular_matrix (GF4 a b) $
      (2 :: 2) $ (2 :: 2) = gf2_of_bool (a \<noteq> b)"
  by (cases a; cases b;
      simp add: gf4_over_gf2.regular_matrix_def
        gf2_gf4.left_multiplication_def gf4_basis_def
        gf2_of_bool_def one_gf4_def)

lemma gf4_algebra_trace:
  "gf4_over_gf2.algebra_trace (GF4 a b) = gf2_of_bool b"
  by (cases a; cases b;
      simp add: gf4_over_gf2.algebra_trace_def trace_def
        UNIV_2 gf2_of_bool_def)

lemma gf4_algebra_norm:
  "gf4_over_gf2.algebra_norm (GF4 a b) =
    gf2_of_bool (a \<or> b)"
  unfolding gf4_over_gf2.algebra_norm_def det_2
  by (cases a; cases b;
      simp add: gf2_of_bool_def)

theorem gf4_over_gf2_trace_norm:
  "gf4_over_gf2.algebra_trace gf4_alpha = 1 \<and>
    gf4_over_gf2.algebra_norm gf4_alpha = 1"
  by (simp add: gf4_algebra_trace gf4_algebra_norm
    gf2_of_bool_def)

theorem gf4_over_gf2_dimension:
  "gf4_over_gf2_space.dim UNIV = 2"
proof -
  have dimension:
    "card (range gf4_basis) = gf4_over_gf2_space.dim UNIV"
    by (rule gf4_over_gf2_space.basis_card_eq_dim)
      (simp_all add: gf4_basis_span gf4_basis_independent)
  show ?thesis
    using dimension
    by (simp add: gf4_basis_range)
qed

theorem concrete_finite_field_tower_laws:
  "indexed_algebra.algebra_trace
      gf2_gf4_scale gf4_tower_basis x =
    gf4_over_gf2.algebra_trace
      (gf4_over_itself.algebra_trace x) \<and>
   indexed_algebra.algebra_norm
      gf2_gf4_scale gf4_tower_basis x =
    gf4_over_gf2.algebra_norm
      (gf4_over_itself.algebra_norm x)"
proof -
  interpret tower: indexed_field_algebra_tower
    gf2_gf4_scale gf4_self_scale gf2_gf4_scale
    gf4_basis gf4_unit_basis
    by unfold_locales
      (simp_all add: gf2_gf4_scale_def gf4_self_scale_def
        algebra_simps gf4_basis_inj gf4_basis_independent
        gf4_basis_span gf4_unit_basis_inj gf4_unit_basis_range
        gf4_unit_basis_independent gf4_unit_basis_span
        gf4_unit_basis_independent_single gf4_unit_basis_span_single)
  note trace_law = tower.algebra_trace_trans[of x]
  note norm_law = tower.algebra_norm_trans[of x]
  have basis_eq: "tower.tower_basis = gf4_tower_basis"
    by (rule ext)
      (simp add: tower.tower_basis_def gf4_tower_basis_def)
  show ?thesis
    using trace_law norm_law
    by (simp only: basis_eq)
qed

subsection \<open>The quadratic extension of the reals by the imaginary unit\<close>

definition real_complex_scale :: "real \<Rightarrow> complex \<Rightarrow> complex"
  where "real_complex_scale r z = of_real r * z"

definition real_complex_direct_scale :: "real \<Rightarrow> complex \<Rightarrow> complex"
  where "real_complex_direct_scale r z = of_real r * z"

definition complex_complex_scale :: "complex \<Rightarrow> complex \<Rightarrow> complex"
  where "complex_complex_scale z w = z * w"

definition complex_basis :: "2 \<Rightarrow> complex"
  where "complex_basis i = (if i = 1 then 1 else \<i>)"

definition complex_unit_basis :: "1 \<Rightarrow> complex"
  where "complex_unit_basis i = 1"

definition complex_tower_basis :: "(2 \<times> 1) \<Rightarrow> complex"
  where "complex_tower_basis ij =
    complex_complex_scale (complex_basis (fst ij))
      (complex_unit_basis (snd ij))"

interpretation real_complex: commutative_algebra real_complex_scale
  by unfold_locales
    (simp_all add: real_complex_scale_def algebra_simps)

interpretation complex_complex: commutative_algebra complex_complex_scale
  by unfold_locales
    (simp_all add: complex_complex_scale_def algebra_simps)

lemma complex_basis_range:
  "range complex_basis = {1, \<i>}"
proof -
  have index_cases: "i = 1 \<or> i = 2" for i :: 2
    using UNIV_2 by auto
  have subset: "range complex_basis \<subseteq> {1, \<i>}"
  proof
    fix z
    assume "z \<in> range complex_basis"
    then obtain i where "z = complex_basis i"
      by auto
    with index_cases[of i] show "z \<in> {1, \<i>}"
      by (auto simp: complex_basis_def)
  qed
  have "1 = complex_basis (1 :: 2)"
    by (simp add: complex_basis_def)
  moreover have "\<i> = complex_basis (2 :: 2)"
    by (simp add: complex_basis_def)
  ultimately have "{1, \<i>} \<subseteq> range complex_basis"
    by blast
  with subset show ?thesis
    by blast
qed

lemma complex_basis_inj:
  "inj complex_basis"
proof (rule injI)
  fix i j :: 2
  have i_cases: "i = 1 \<or> i = 2"
    using UNIV_2 by auto
  have j_cases: "j = 1 \<or> j = 2"
    using UNIV_2 by auto
  show "complex_basis i = complex_basis j \<Longrightarrow> i = j"
    using i_cases j_cases
    by (auto simp: complex_basis_def complex_eq_iff)
qed

lemma complex_basis_independent:
  "real_complex.independent (range complex_basis)"
  unfolding real_complex.independent_explicit_module
proof (intro allI impI)
  fix T c w
  assume finite_T: "finite T"
    and subset: "T \<subseteq> range complex_basis"
    and sum_zero:
      "(\<Sum>z\<in>T. real_complex_scale (c z) z) = 0"
    and w: "w \<in> T"
  have T_cases:
    "T = {} \<or> T = {1} \<or> T = {\<i>} \<or> T = {1, \<i>}"
    using subset
    by (auto simp: complex_basis_range)
  then consider
      (empty) "T = {}"
    | (one) "T = {1}"
    | (imaginary) "T = {\<i>}"
    | (both) "T = {1, \<i>}"
    by blast
  then show "c w = 0"
  proof cases
    case empty
    with w show ?thesis
      by simp
  next
    case one
    have coefficient: "c 1 = 0"
      using sum_zero
      by (simp add: one real_complex_scale_def)
    with one w show ?thesis
      by simp
  next
    case imaginary
    have coefficient: "c \<i> = 0"
      using sum_zero
      by (simp add: imaginary real_complex_scale_def)
    with imaginary w show ?thesis
      by simp
  next
    case both
    have coefficient_one: "c 1 = 0"
      using sum_zero
      by (simp add: both real_complex_scale_def complex_eq_iff)
    have coefficient_imaginary: "c \<i> = 0"
      using sum_zero
      by (simp add: both real_complex_scale_def complex_eq_iff)
    with coefficient_one both w show ?thesis
      by auto
  qed
qed

lemma complex_basis_span:
  "real_complex.span (range complex_basis) = UNIV"
proof -
  have one_mem: "(1 :: complex) \<in>
      real_complex.span (range complex_basis)"
    by (rule real_complex.span_base) (auto simp: complex_basis_range)
  have imaginary_mem: "\<i> \<in>
      real_complex.span (range complex_basis)"
    by (rule real_complex.span_base) (auto simp: complex_basis_range)
  have expansion:
    "real_complex_scale (Re z) 1 +
      real_complex_scale (Im z) \<i> = z" for z
  proof -
    have "z = of_real (Re z) + \<i> * of_real (Im z)"
      by (rule complex_eq)
    then show ?thesis
      by (simp add: real_complex_scale_def mult.commute)
  qed
  have "z \<in> real_complex.span (range complex_basis)" for z
  proof -
    have "real_complex_scale (Re z) 1 +
        real_complex_scale (Im z) \<i> \<in>
      real_complex.span (range complex_basis)"
      by (rule real_complex.span_add)
        (rule real_complex.span_scale[OF one_mem],
         rule real_complex.span_scale[OF imaginary_mem])
    then show ?thesis
      by (simp only: expansion)
  qed
  then show ?thesis
    by auto
qed

lemma complex_unit_basis_inj:
  "inj complex_unit_basis"
  by (auto simp: inj_def)

lemma complex_unit_basis_range:
  "range complex_unit_basis = {1}"
  by (auto simp: complex_unit_basis_def)

lemma complex_unit_basis_independent:
  "complex_complex.independent (range complex_unit_basis)"
  unfolding complex_complex.independent_explicit_module
proof (intro allI impI)
  fix T c w
  assume subset: "T \<subseteq> range complex_unit_basis"
    and sum_zero:
      "(\<Sum>z\<in>T. complex_complex_scale (c z) z) = 0"
    and w: "w \<in> T"
  have T: "T = {1}"
    using subset w
    by (auto simp: complex_unit_basis_range complex_unit_basis_def)
  have "c 1 = 0"
    using sum_zero
    by (simp add: T complex_complex_scale_def)
  with T w show "c w = 0"
    by simp
qed

lemma complex_unit_basis_span:
  "complex_complex.span (range complex_unit_basis) = UNIV"
proof -
  have one_mem: "(1 :: complex) \<in>
      complex_complex.span (range complex_unit_basis)"
    by (rule complex_complex.span_base)
      (auto simp: complex_unit_basis_def)
  have "z \<in> complex_complex.span (range complex_unit_basis)" for z
  proof -
    have "complex_complex_scale z 1 \<in>
      complex_complex.span (range complex_unit_basis)"
      by (rule complex_complex.span_scale[OF one_mem])
    then show ?thesis
      by (simp add: complex_complex_scale_def)
  qed
  then show ?thesis
    by auto
qed

lemma complex_unit_basis_independent_single:
  "complex_complex.independent {complex_unit_basis (1 :: 1)}"
  using complex_unit_basis_independent
  by (simp add: complex_unit_basis_range complex_unit_basis_def)

lemma complex_unit_basis_span_single:
  "complex_complex.span {complex_unit_basis (1 :: 1)} = UNIV"
  using complex_unit_basis_span
  by (simp add: complex_unit_basis_range complex_unit_basis_def)

interpretation complex_real_algebra:
    indexed_algebra real_complex_scale complex_basis
  by unfold_locales
    (fact complex_basis_inj complex_basis_independent
      complex_basis_span)+

interpretation complex_scalar_algebra:
    indexed_algebra complex_complex_scale complex_unit_basis
  by unfold_locales
    (fact complex_unit_basis_inj complex_unit_basis_independent
      complex_unit_basis_span)+

lemma complex_coordinate_one [simp]:
  "complex_real_algebra.coordinates.coordinate z (1 :: 2) = Re z"
  using complex_real_algebra.coordinates.basis_expansion[of z]
  by (simp add: UNIV_2 complex_basis_def real_complex_scale_def
    complex_eq_iff)

lemma complex_coordinate_two [simp]:
  "complex_real_algebra.coordinates.coordinate z (2 :: 2) = Im z"
  using complex_real_algebra.coordinates.basis_expansion[of z]
  by (simp add: UNIV_2 complex_basis_def real_complex_scale_def
    complex_eq_iff)

lemma complex_regular_matrix_11 [simp]:
  "complex_real_algebra.regular_matrix z $ (1 :: 2) $ (1 :: 2) =
    Re z"
  by (simp add: complex_real_algebra.regular_matrix_def
    real_complex.left_multiplication_def complex_basis_def)

lemma complex_regular_matrix_12 [simp]:
  "complex_real_algebra.regular_matrix z $ (1 :: 2) $ (2 :: 2) =
    - Im z"
  by (simp add: complex_real_algebra.regular_matrix_def
    real_complex.left_multiplication_def complex_basis_def)

lemma complex_regular_matrix_21 [simp]:
  "complex_real_algebra.regular_matrix z $ (2 :: 2) $ (1 :: 2) =
    Im z"
  by (simp add: complex_real_algebra.regular_matrix_def
    real_complex.left_multiplication_def complex_basis_def)

lemma complex_regular_matrix_22 [simp]:
  "complex_real_algebra.regular_matrix z $ (2 :: 2) $ (2 :: 2) =
    Re z"
  by (simp add: complex_real_algebra.regular_matrix_def
    real_complex.left_multiplication_def complex_basis_def)

lemma complex_algebra_trace:
  "complex_real_algebra.algebra_trace z = 2 * Re z"
  by (simp add: complex_real_algebra.algebra_trace_def trace_def UNIV_2)

lemma complex_algebra_norm:
  "complex_real_algebra.algebra_norm z =
    (Re z)\<^sup>2 + (Im z)\<^sup>2"
  unfolding complex_real_algebra.algebra_norm_def det_2
  by (simp add: power2_eq_square)

theorem quadratic_extension_trace_norm:
  "complex_real_algebra.algebra_trace z = 2 * Re z \<and>
    complex_real_algebra.algebra_norm z =
      (Re z)\<^sup>2 + (Im z)\<^sup>2"
  by (simp add: complex_algebra_trace complex_algebra_norm)

theorem complex_quadratic_tower_laws:
  "indexed_algebra.algebra_trace
      real_complex_direct_scale complex_tower_basis z =
    complex_real_algebra.algebra_trace
      (complex_scalar_algebra.algebra_trace z) \<and>
   indexed_algebra.algebra_norm
      real_complex_direct_scale complex_tower_basis z =
    complex_real_algebra.algebra_norm
      (complex_scalar_algebra.algebra_norm z)"
proof -
  interpret tower: indexed_field_algebra_tower
    real_complex_scale complex_complex_scale
    real_complex_direct_scale complex_basis complex_unit_basis
    by unfold_locales
      (simp_all add: real_complex_scale_def
        real_complex_direct_scale_def complex_complex_scale_def
        algebra_simps complex_basis_inj complex_basis_independent
        complex_basis_span complex_unit_basis_inj
        complex_unit_basis_range complex_unit_basis_independent
        complex_unit_basis_span complex_unit_basis_independent_single
        complex_unit_basis_span_single)
  have "tower.tower_basis = complex_tower_basis"
    by (force simp: tower.tower_basis_def complex_tower_basis_def)
  then show ?thesis
    using tower.algebra_norm_trans tower.algebra_trace_trans by force
qed

end
