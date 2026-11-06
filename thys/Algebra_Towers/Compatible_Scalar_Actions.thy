theory Compatible_Scalar_Actions
  imports
    "HOL-Analysis.Determinants"
begin

section \<open>Existing scalar infrastructure\<close>

text \<open>
Isabelle's type-based algebra library represents a module by the locale
\<^locale>\<open>module\<close>, parameterized by an explicit scalar action.  Consequently,
several scalar actions may coexist without introducing new type classes.
Linear maps are already represented by \<^locale>\<open>module_hom\<close>, and over
fields by the definitionally equivalent locale \<^locale>\<open>vector_space\<close>.
We use its existing operations for subspaces, spans, independence, and
coordinate representations.  The Cartesian matrix library supplies trace and
determinant.

\<close>

locale compatible_scalar_actions =
  RS: Modules.module rS +
  SA: Modules.module sA +
  RA: Modules.module rA
  for rS :: "'r::comm_ring_1 \<Rightarrow> 's::comm_ring_1 \<Rightarrow> 's"
    and sA :: "'s \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and rA :: "'r \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes scalar_compat [simp]:
    "rA r (sA s a) = sA (rS r s) a"
begin

abbreviation scalar_embed :: "'r \<Rightarrow> 's"
  where "scalar_embed r \<equiv> rS r 1"

lemma direct_eq_upper_embed [simp]:
  "rA r a = sA (scalar_embed r) a"
  using scalar_compat[of r 1 a] by simp

lemma module_hom_restrict_scalars:
  assumes "module_hom sA sA f"
  shows "module_hom rA rA f"
proof -
  interpret f: module_hom sA sA f
    by fact
  show ?thesis
    by unfold_locales (simp_all add: f.add f.scale)
qed

end

locale compatible_vector_spaces =
  compatible_scalar_actions rS sA rA
  for rS :: "'r::field \<Rightarrow> 's::field \<Rightarrow> 's"
    and sA :: "'s \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and rA :: "'r \<Rightarrow> 'a \<Rightarrow> 'a"
begin

lemma linear_restrict_scalars:
  assumes "Vector_Spaces.linear sA sA f"
  shows "Vector_Spaces.linear rA rA f"
  using assms module_hom_restrict_scalars
  by (simp add: module_hom_iff_linear)

end

locale commutative_algebra =
  Modules.module scale
  for scale :: "'r::comm_ring_1 \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a" +
  assumes scale_mult_right [algebra_simps]:
    "scale r x * y = scale r (x * y)"
begin

abbreviation scalar_embed :: "'r \<Rightarrow> 'a"
  where "scalar_embed r \<equiv> scale r 1"

lemma scale_eq_embed_mult:
  "scale r x = scalar_embed r * x"
  using scale_mult_right[of r 1 x] by simp

lemma scale_mult_left [algebra_simps]:
  "x * scale r y = scale r (x * y)"
proof -
  have "x * scale r y = scale r y * x"
    by (rule mult.commute)
  also have "\<dots> = scale r (y * x)"
    by (rule scale_mult_right)
  also have "\<dots> = scale r (x * y)"
    by (simp only: mult.commute)
  finally show ?thesis .
qed

lemma scalar_embed_zero [simp]:
  "scalar_embed 0 = 0"
  by simp

lemma scalar_embed_one [simp]:
  "scalar_embed 1 = 1"
  by simp

lemma scalar_embed_add [simp]:
  "scalar_embed (r + s) = scalar_embed r + scalar_embed s"
  by (simp add: scale_left_distrib)

lemma scalar_embed_minus [simp]:
  "scalar_embed (- r) = - scalar_embed r"
  by simp

lemma scalar_embed_diff [simp]:
  "scalar_embed (r - s) = scalar_embed r - scalar_embed s"
  by (simp add: scale_left_diff_distrib)

lemma scalar_embed_mult [simp]:
  "scalar_embed (r * s) = scalar_embed r * scalar_embed s"
proof -
  have "scalar_embed (r * s) = scale r (scale s 1)"
    by (simp only: scale_scale)
  also have "\<dots> = scalar_embed r * scalar_embed s"
    by (rule scale_eq_embed_mult)
  finally show ?thesis .
qed

lemma scalar_embed_of_nat [simp]:
  "scalar_embed (of_nat n) = of_nat n"
  by (induction n) simp_all

lemma scalar_embed_of_int [simp]:
  "scalar_embed (of_int z) = of_int z"
  by (cases z) simp_all

lemma scalar_embed_power [simp]:
  "scalar_embed (r ^ n) = scalar_embed r ^ n"
  by (induction n) simp_all

end

locale algebra_tower =
  RS: commutative_algebra rS +
  SA: commutative_algebra sA +
  RA: commutative_algebra rA
  for rS :: "'r::comm_ring_1 \<Rightarrow> 's::comm_ring_1 \<Rightarrow> 's"
    and sA :: "'s \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and rA :: "'r \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes scalar_compat [simp]:
    "rA r (sA s a) = sA (rS r s) a"
begin

sublocale compatible_scalar_actions rS sA rA
  by unfold_locales (fact scalar_compat)

lemma composed_scalar_embed [simp]:
  "rA r 1 = sA (rS r 1) 1"
  using scalar_compat[of r 1 1] by simp

lemma scalar_compat_mult [simp]:
  "rA r (sA s a * b) = sA (rS r s) (a * b)"
proof -
  have "rA r (sA s a * b) = rA r (sA s a) * b"
    by (rule RA.scale_mult_right[symmetric])
  also have "\<dots> = sA (rS r s) a * b"
    by (simp only: scalar_compat)
  also have "\<dots> = sA (rS r s) (a * b)"
    by (rule SA.scale_mult_right)
  finally show ?thesis .
qed

lemma scalar_compat_linear:
  assumes "module_hom sA sA f"
  shows "f (rA r a) = rA r (f a)"
proof -
  interpret f: module_hom sA sA f
    by fact
  have "f (rA r a) = f (sA (rS r 1) a)"
    by simp
  also have "\<dots> = sA (rS r 1) (f a)"
    by (rule f.scale)
  also have "\<dots> = rA r (f a)"
    by simp
  finally show ?thesis .
qed

end

end
