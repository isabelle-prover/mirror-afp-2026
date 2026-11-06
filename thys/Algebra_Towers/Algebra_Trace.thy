theory Algebra_Trace
  imports Regular_Representation
begin

section \<open>Algebra trace\<close>

context indexed_algebra
begin

definition algebra_trace :: "'a \<Rightarrow> 'r"
  where "algebra_trace a = trace (regular_matrix a)"

lemma algebra_trace_zero [simp]:
  "algebra_trace 0 = 0"
  by (simp add: algebra_trace_def trace_def)

lemma algebra_trace_add:
  "algebra_trace (a + b) = algebra_trace a + algebra_trace b"
  by (simp add: algebra_trace_def regular_matrix_add trace_add)

lemma algebra_trace_sum:
  "algebra_trace (\<Sum>x\<in>X. f x) =
    (\<Sum>x\<in>X. algebra_trace (f x))"
  by (induction X rule: infinite_finite_induct)
    (simp_all add: algebra_trace_add)

lemma algebra_trace_scale:
  "algebra_trace (scale r a) = r * algebra_trace a"
  by (simp add: algebra_trace_def regular_matrix_scale trace_def
    sum_distrib_left)

theorem algebra_trace_linear:
  "module_hom scale ((*) :: 'r \<Rightarrow> 'r \<Rightarrow> 'r) algebra_trace"
  by unfold_locales
    (simp_all add: algebra_trace_add algebra_trace_scale algebra_simps)

lemma algebra_trace_scalar:
  "algebra_trace (scale r 1) = of_nat CARD('i) * r"
  by (simp add: algebra_trace_def regular_matrix_scalar_embed
    trace_def mat_def)

end

context indexed_basis_pair
begin

theorem trace_matrix_change_basis:
  assumes "module_hom scale scale f"
  shows "trace (second.matrix_of f) = trace (first.matrix_of f)"
proof -
  have "trace (second.matrix_of f) =
    trace ((to_second ** first.matrix_of f) ** to_first)"
    by (simp only: matrix_change_basis[OF assms])
  also have "\<dots> = trace (to_first ** (to_second ** first.matrix_of f))"
    by (rule trace_mul_sym)
  also have "\<dots> =
    trace ((to_first ** to_second) ** first.matrix_of f)"
    by (simp only: matrix_mul_assoc)
  also have "\<dots> = trace (first.matrix_of f)"
    by (simp only: to_first_to_second matrix_mul_lid)
  finally show ?thesis .
qed

end

context indexed_algebra_reindex
begin

theorem algebra_trace_reindexed:
  "reindexed.algebra_trace a = original.algebra_trace a"
  unfolding reindexed.algebra_trace_def original.algebra_trace_def
    trace_def
  apply (simp only: regular_matrix_reindexed_component)
  apply (rule sum.reindex_bij_betw)
  using index_iso_bij
  by (simp add: bij_betw_def bij_def)

end

context indexed_algebra
begin

theorem algebra_trace_basis_independent:
  fixes other_basis :: "'i \<Rightarrow> 'a"
  assumes other_inj: "inj other_basis"
    and other_independent: "independent (range other_basis)"
    and other_span: "span (range other_basis) = UNIV"
  shows "algebra_trace a =
    indexed_algebra.algebra_trace scale other_basis a"
proof -
  interpret other: indexed_algebra scale other_basis
    by unfold_locales
      (fact other_inj other_independent other_span)+
  interpret change: indexed_basis_pair scale basis other_basis
    by unfold_locales
      (fact basis_inj basis_independent basis_span
        other_inj other_independent other_span)+
  have "trace (other.regular_matrix a) = trace (regular_matrix a)"
    unfolding other.regular_matrix_def regular_matrix_def
    by (rule change.trace_matrix_change_basis)
      (rule left_multiplication_module_hom)
  then show ?thesis
    by (simp add: algebra_trace_def other.algebra_trace_def)
qed

theorem algebra_trace_basis_independent_bij:
  fixes other_basis :: "'j::finite \<Rightarrow> 'a"
    and index_iso :: "'i \<Rightarrow> 'j"
  assumes other_inj: "inj other_basis"
    and other_independent: "independent (range other_basis)"
    and other_span: "span (range other_basis) = UNIV"
    and index_iso_bij: "bij index_iso"
  shows "algebra_trace a =
    indexed_algebra.algebra_trace scale other_basis a"
proof -
  interpret other: indexed_algebra scale other_basis
    by unfold_locales
      (fact other_inj other_independent other_span)+
  interpret reindex:
    indexed_algebra_reindex scale other_basis index_iso
    by unfold_locales
      (fact other_inj other_independent other_span index_iso_bij)+
  have "algebra_trace a = reindex.reindexed.algebra_trace a"
    by (rule algebra_trace_basis_independent)
      (fact reindex.reindexed.basis_inj
        reindex.reindexed.basis_independent
        reindex.reindexed.basis_span)+
  also have "\<dots> = other.algebra_trace a"
    by (rule reindex.algebra_trace_reindexed)
  finally show ?thesis .
qed

end

context indexed_algebra_isomorphism
begin

theorem algebra_trace_iso:
  "target.algebra_trace (iso a) = source.algebra_trace a"
  by (simp add: target.algebra_trace_def source.algebra_trace_def
    regular_matrix_iso)

end

context indexed_algebra_isomorphism_general
begin

theorem algebra_trace_iso:
  "target.algebra_trace (iso a) = source.algebra_trace a"
proof -
  have basis_change:
    "transported.algebra_trace (iso a) =
      target.algebra_trace (iso a)"
    by (rule transported.algebra_trace_basis_independent_bij)
      (fact target.basis_inj target.basis_independent
        target.basis_span index_iso_bij)+
  have transported:
    "transported.algebra_trace (iso a) =
      source.algebra_trace a"
    by (rule basis_iso.algebra_trace_iso)
  show ?thesis
    using basis_change transported by simp
qed

end

context indexed_algebra_tower
begin

sublocale lower_algebra: indexed_algebra rS lower_basis
  by unfold_locales
    (fact lower_basis_inj lower_basis_independent lower_basis_span)+

sublocale upper_algebra: indexed_algebra sA upper_basis
  by unfold_locales
    (fact upper_basis_inj upper_basis_independent upper_basis_span)+

sublocale tower_algebra: indexed_algebra rA tower_basis
  by unfold_locales
    (fact tower_basis_inj tower_basis_independent tower_basis_span)+

lemma restricted_matrix_diagonal:
  assumes f: "module_hom sA sA f"
  shows "composed.matrix_of f $ (i, j) $ (i, j) = lower_algebra.regular_matrix (upper.matrix_of f $ j $ j) $ i $ i"
proof -
  interpret f: module_hom sA sA f
    by fact
  have "composed.matrix_of f $ (i, j) $ (i, j) =
    composed.coordinate
      (f (tower_basis (i, j))) (i, j)"
    by simp
  also have "\<dots> = tower_coordinate
      (f (tower_basis (i, j))) (i, j)"
    by (rule composed_coordinate)
  also have "\<dots> =
    tower_coordinate
      (f (sA (lower_basis i) (upper_basis j))) (i, j)"
    by (simp only: tower_basis_def fst_conv snd_conv)
  also have "\<dots> =
    tower_coordinate
      (sA (lower_basis i) (f (upper_basis j))) (i, j)"
    by (simp only: f.scale)
  also have "\<dots> =
    lower.coordinate
      (lower_basis i *
        upper.coordinate (f (upper_basis j)) j) i"
    by (simp add: tower_coordinate_def)
  also have "\<dots> =
    lower.coordinate
      (upper.coordinate (f (upper_basis j)) j *
        lower_basis i) i"
    by (simp only: mult.commute)
  also have "\<dots> =
    lower_algebra.regular_matrix
      (upper.matrix_of f $ j $ j) $ i $ i"
    by (simp add: lower_algebra.regular_matrix_def
      RS.left_multiplication_def)
  finally show ?thesis .
qed

theorem trace_restrict_scalars:
  assumes f: "module_hom sA sA f"
  shows "trace (composed.matrix_of f) =
    lower_algebra.algebra_trace
      (trace (upper.matrix_of f))"
proof -
  have pair_sum: "(\<Sum>ij\<in>(UNIV :: ('i \<times> 'j) set). composed.matrix_of f $ ij $ ij) =
    (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. composed.matrix_of f $ (i, j) $ (i, j))"
    using sum.swap by (force simp add: sum.cartesian_product' simp flip: UNIV_Times_UNIV)
  have "trace (composed.matrix_of f) = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. composed.matrix_of f $ (i, j) $ (i, j))"
    by (simp only: trace_def pair_sum)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. lower_algebra.regular_matrix (upper.matrix_of f $ j $ j) $ i $ i)"
    using f restricted_matrix_diagonal by presburger
  also have "\<dots> = (\<Sum>j\<in>UNIV. lower_algebra.algebra_trace (upper.matrix_of f $ j $ j))"
    by (simp add: lower_algebra.algebra_trace_def trace_def)
  also have "\<dots> = lower_algebra.algebra_trace (\<Sum>j\<in>UNIV. upper.matrix_of f $ j $ j)"
    by (rule lower_algebra.algebra_trace_sum[symmetric])
  also have "\<dots> = lower_algebra.algebra_trace (trace (upper.matrix_of f))"
    by (simp only: trace_def)
  finally show ?thesis .
qed

theorem algebra_trace_trans:
  "tower_algebra.algebra_trace a =
    lower_algebra.algebra_trace (upper_algebra.algebra_trace a)"
  unfolding tower_algebra.algebra_trace_def
    upper_algebra.algebra_trace_def
    tower_algebra.regular_matrix_def
    upper_algebra.regular_matrix_def
    RA.left_multiplication_def
    SA.left_multiplication_def
  by (rule trace_restrict_scalars)
    (rule SA.left_multiplication_module_hom[
      unfolded SA.left_multiplication_def])

end

end
