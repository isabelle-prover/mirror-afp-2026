theory Regular_Representation
  imports Finite_Dimensional_Towers
begin

section \<open>Regular representation\<close>

context commutative_algebra
begin

definition left_multiplication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "left_multiplication a x = a * x"

lemma left_multiplication_module_hom:
  "module_hom scale scale (left_multiplication a)"
  by unfold_locales
    (simp_all add: left_multiplication_def algebra_simps)

lemma left_multiplication_zero [simp]:
  "left_multiplication 0 x = 0"
  by (simp add: left_multiplication_def)

lemma left_multiplication_one [simp]:
  "left_multiplication 1 = id"
  by (rule ext) (simp add: left_multiplication_def)

lemma left_multiplication_add:
  "left_multiplication (a + b) x =
    left_multiplication a x + left_multiplication b x"
  by (simp add: left_multiplication_def algebra_simps)

lemma left_multiplication_mult:
  "left_multiplication (a * b) =
    left_multiplication a \<circ> left_multiplication b"
  by (rule ext) (simp add: left_multiplication_def mult.assoc)

definition regular_representation :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "regular_representation a = left_multiplication a"

lemma regular_representation_module_hom:
  "module_hom scale scale (regular_representation a)"
  unfolding regular_representation_def
  by (rule left_multiplication_module_hom)

lemma regular_representation_add:
  "regular_representation (a + b) x =
    regular_representation a x + regular_representation b x"
  by (simp add: regular_representation_def left_multiplication_add)

lemma regular_representation_mult:
  "regular_representation (a * b) =
    regular_representation a \<circ> regular_representation b"
  by (simp add: regular_representation_def left_multiplication_mult)

lemma regular_representation_one [simp]:
  "regular_representation 1 = id"
  by (simp add: regular_representation_def)

end

context indexed_basis
begin

definition matrix_of :: "('a \<Rightarrow> 'a) \<Rightarrow> 'r^'i^'i"
  where "matrix_of f = (\<chi> i j. coordinate (f (basis j)) i)"

lemma matrix_of_component [simp]:
  "matrix_of f $ i $ j = coordinate (f (basis j)) i"
  by (simp add: matrix_of_def)

lemma matrix_of_id [simp]:
  "matrix_of id = mat 1"
  by (vector matrix_of_def mat_def coordinate_basis)

lemma matrix_of_zero [simp]:
  "matrix_of (\<lambda>_. 0) = 0"
  by (vector matrix_of_def coordinate_zero)

lemma matrix_of_add:
  "matrix_of (\<lambda>x. f x + g x) = matrix_of f + matrix_of g"
  by (vector matrix_of_def coordinate_add)

lemma matrix_of_comp:
  assumes f: "module_hom scale scale f"
    and g: "module_hom scale scale g"
  shows "matrix_of (g \<circ> f) = matrix_of g ** matrix_of f"
proof -
  interpret f: module_hom scale scale f
    by fact
  interpret g: module_hom scale scale g
    by fact
  have expand: "g (f (basis j)) = (\<Sum>k\<in>UNIV. scale (coordinate (f (basis j)) k) (g (basis k)))"
    for j
  proof -
    have "g (f (basis j)) =
      g (\<Sum>k\<in>UNIV. scale (coordinate (f (basis j)) k) (basis k))"
      by (simp only: basis_expansion)
    also have "\<dots> =
      (\<Sum>k\<in>UNIV. g (scale (coordinate (f (basis j)) k) (basis k)))"
      by (rule g.sum)
    also have "\<dots> =
      (\<Sum>k\<in>UNIV. scale (coordinate (f (basis j)) k) (g (basis k)))"
      using g.scale by presburger
    finally show ?thesis .
  qed

  have entry: "matrix_of (g \<circ> f) $ i $ j = (matrix_of g ** matrix_of f) $ i $ j" for i j
  proof -
    have "matrix_of (g \<circ> f) $ i $ j = coordinate (\<Sum>k\<in>UNIV. scale (coordinate (f (basis j)) k) (g (basis k))) i"
      by (simp add: matrix_of_def expand)
    also have "\<dots> = (\<Sum>k\<in>UNIV. coordinate (scale (coordinate (f (basis j)) k) (g (basis k))) i)"
      by (rule coordinate_sum)
    also have "\<dots> = (\<Sum>k\<in>UNIV. coordinate (g (basis k)) i * coordinate (f (basis j)) k)"
      by (simp add: mult.commute)
    also have "\<dots> = (matrix_of g ** matrix_of f) $ i $ j"
      by (simp add: matrix_matrix_mult_def matrix_of_def)
    finally show ?thesis .
  qed

  show ?thesis
    using entry by (meson vec_eq_iff)
qed

end

locale indexed_basis_pair =
  first: indexed_basis scale first_basis +
  second: indexed_basis scale second_basis
  for scale :: "'r::comm_ring_1 \<Rightarrow> 'a::ab_group_add \<Rightarrow> 'a"
    and first_basis :: "'i::finite \<Rightarrow> 'a"
    and second_basis :: "'i \<Rightarrow> 'a"
begin

definition to_second :: "'r^'i^'i"
  where "to_second =
    (\<chi> i j. second.coordinate (first_basis j) i)"

definition to_first :: "'r^'i^'i"
  where "to_first =
    (\<chi> i j. first.coordinate (second_basis j) i)"

definition first_to_second_matrix :: "('a \<Rightarrow> 'a) \<Rightarrow> 'r^'i^'i"
  where "first_to_second_matrix f =
    (\<chi> i j. second.coordinate (f (first_basis j)) i)"

lemma to_second_component [simp]:
  "to_second $ i $ j = second.coordinate (first_basis j) i"
  by (simp add: to_second_def)

lemma to_first_component [simp]:
  "to_first $ i $ j = first.coordinate (second_basis j) i"
  by (simp add: to_first_def)

lemma first_to_second_component [simp]:
  "first_to_second_matrix f $ i $ j =
    second.coordinate (f (first_basis j)) i"
  by (simp add: first_to_second_matrix_def)

lemma to_second_to_first:
  "to_second ** to_first = mat 1"
proof -
  have entry: "(to_second ** to_first) $ i $ j = (mat 1 :: 'r^'i^'i) $ i $ j" for i j
  proof -
    have "(to_second ** to_first) $ i $ j = (\<Sum>k\<in>UNIV. second.coordinate (first_basis k) i * first.coordinate (second_basis j) k)"
      by (simp add: matrix_matrix_mult_def)
    also have "\<dots> = (\<Sum>k\<in>UNIV. first.coordinate (second_basis j) k * second.coordinate (first_basis k) i)"
      by (simp add: mult.commute)
    also have "\<dots> = second.coordinate (\<Sum>k\<in>UNIV. scale (first.coordinate (second_basis j) k) (first_basis k)) i"
      by (simp add: second.coordinate_sum)
    also have "\<dots> = (mat 1 :: 'r^'i^'i) $ i $ j"
      by (simp add: first.basis_expansion mat_def)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: entry vec_eq_iff)
qed

lemma to_first_to_second:
  "to_first ** to_second = mat 1"
proof -
  have entry:
    "(to_first ** to_second) $ i $ j = (mat 1 :: 'r^'i^'i) $ i $ j"
    for i j
  proof -
    have "(to_first ** to_second) $ i $ j =
      (\<Sum>k\<in>UNIV.
        first.coordinate (second_basis k) i *
        second.coordinate (first_basis j) k)"
      by (simp add: matrix_matrix_mult_def)
    also have "\<dots> = (\<Sum>k\<in>UNIV. second.coordinate (first_basis j) k * first.coordinate (second_basis k) i)"
      by (simp add: mult.commute)
    also have "\<dots> = first.coordinate (\<Sum>k\<in>UNIV. scale (second.coordinate (first_basis j) k) (second_basis k)) i"
      by (simp add: first.coordinate_sum)
    also have "\<dots> = (mat 1 :: 'r^'i^'i) $ i $ j"
      by (simp add: second.basis_expansion mat_def)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: entry vec_eq_iff)
qed

lemma first_to_second_matrix_left:
  assumes f: "module_hom scale scale f"
  shows "first_to_second_matrix f =
    to_second ** first.matrix_of f"
proof -
  interpret f: module_hom scale scale f
    by fact
  have entry: "first_to_second_matrix f $ i $ j = (to_second ** first.matrix_of f) $ i $ j" for i j
  proof -
    have "first_to_second_matrix f $ i $ j =
      second.coordinate (\<Sum>k\<in>UNIV. scale (first.coordinate (f (first_basis j)) k) (first_basis k)) i"
      by (simp add: first.basis_expansion)
    also have "\<dots> = (\<Sum>k\<in>UNIV. second.coordinate (first_basis k) i * first.coordinate (f (first_basis j)) k)"
      by (simp add: second.coordinate_sum mult.commute)
    also have "\<dots> = (to_second ** first.matrix_of f) $ i $ j"
      by (simp add: matrix_matrix_mult_def)
    finally show ?thesis .
  qed
  show ?thesis
    using entry by (meson vec_eq_iff)
qed

lemma second_matrix_from_mixed:
  assumes f: "module_hom scale scale f"
  shows "second.matrix_of f =
    first_to_second_matrix f ** to_first"
proof -
  interpret f: module_hom scale scale f
    by fact
  have entry: "second.matrix_of f $ i $ j = (first_to_second_matrix f ** to_first) $ i $ j" for i j
  proof -
    have "second.matrix_of f $ i $ j =
      second.coordinate (f (\<Sum>k\<in>UNIV. scale (first.coordinate (second_basis j) k) (first_basis k))) i"
      by (simp add: first.basis_expansion)
    also have "\<dots> =
      second.coordinate (\<Sum>k\<in>UNIV. scale (first.coordinate (second_basis j) k) (f (first_basis k))) i"
      by (simp add: f.sum f.scale)
    also have "\<dots> = (\<Sum>k\<in>UNIV. second.coordinate (f (first_basis k)) i * first.coordinate (second_basis j) k)"
      by (simp add: second.coordinate_sum mult.commute)
    also have "\<dots> = (first_to_second_matrix f ** to_first) $ i $ j"
      by (simp add: matrix_matrix_mult_def)
    finally show ?thesis .
  qed
  show ?thesis
    using entry by (meson vec_eq_iff)
qed

theorem matrix_change_basis:
  assumes "module_hom scale scale f"
  shows "second.matrix_of f =
    (to_second ** first.matrix_of f) ** to_first"
  using second_matrix_from_mixed[OF assms]
    first_to_second_matrix_left[OF assms]
  by simp

end

locale indexed_algebra =
  commutative_algebra scale
  for scale :: "'r::comm_ring_1 \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a" +
  fixes basis :: "'i::finite \<Rightarrow> 'a"
  assumes basis_inj: "inj basis"
    and basis_independent: "independent (range basis)"
    and basis_span: "span (range basis) = UNIV"
begin

sublocale coordinates: indexed_basis scale basis
  by unfold_locales (fact basis_inj basis_independent basis_span)+

definition regular_matrix :: "'a \<Rightarrow> 'r^'i^'i"
  where "regular_matrix a =
    coordinates.matrix_of (left_multiplication a)"

lemma regular_matrix_zero [simp]:
  "regular_matrix 0 = 0"
  by (vector regular_matrix_def left_multiplication_def
    coordinates.matrix_of_def coordinates.coordinate_zero)

lemma regular_matrix_add:
  "regular_matrix (a + b) = regular_matrix a + regular_matrix b"
  by (vector regular_matrix_def left_multiplication_def
    coordinates.matrix_of_def coordinates.coordinate_add algebra_simps)

lemma regular_matrix_scale:
  "regular_matrix (scale r a) =
    (\<chi> i j. r * regular_matrix a $ i $ j)"
  by (vector regular_matrix_def left_multiplication_def
    coordinates.matrix_of_def coordinates.coordinate_scale
    scale_mult_right)

lemma regular_matrix_one [simp]:
  "regular_matrix 1 = mat 1"
  unfolding regular_matrix_def left_multiplication_one
  by (rule coordinates.matrix_of_id)

lemma regular_matrix_scalar_embed:
  "regular_matrix (scale r 1) = mat r"
  by (vector regular_matrix_def left_multiplication_def
    coordinates.matrix_of_def coordinates.coordinate_scale
    coordinates.coordinate_basis mat_def scale_mult_right)

lemma regular_matrix_mult:
  "regular_matrix (a * b) = regular_matrix a ** regular_matrix b"
proof -
  have "regular_matrix (a * b) =
    coordinates.matrix_of
      (left_multiplication a \<circ> left_multiplication b)"
    by (simp add: regular_matrix_def left_multiplication_mult)
  also have "\<dots> =
    coordinates.matrix_of (left_multiplication a) **
      coordinates.matrix_of (left_multiplication b)"
    by (rule coordinates.matrix_of_comp)
      (rule left_multiplication_module_hom)+
  finally show ?thesis
    by (simp add: regular_matrix_def)
qed

end

text \<open>
Finite basis index types are bookkeeping rather than mathematical data.  The
following locale transports an indexed algebra structure along an explicit
bijection between finite index types, so later trace and determinant results
can compare bases with genuinely different index types.
\<close>

locale indexed_algebra_reindex =
  original: indexed_algebra scale original_basis
  for scale :: "'r::comm_ring_1 \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and original_basis :: "'j::finite \<Rightarrow> 'a" +
  fixes index_iso :: "'i::finite \<Rightarrow> 'j"
  assumes index_iso_bij: "bij index_iso"
begin

definition reindexed_basis :: "'i \<Rightarrow> 'a"
  where "reindexed_basis i = original_basis (index_iso i)"

lemma reindexed_basis_range:
  "range reindexed_basis = range original_basis"
proof
  show "range reindexed_basis \<subseteq> range original_basis"
    by (auto simp: reindexed_basis_def)
next
  show "range original_basis \<subseteq> range reindexed_basis"
  proof
    fix x
    assume "x \<in> range original_basis"
    then obtain j where x: "x = original_basis j"
      by blast
    have surj: "surj index_iso"
      using index_iso_bij by (rule bij_is_surj)
    have "\<exists>i. j = index_iso i"
      using surj by (simp add: surj_def)
    then obtain i where i: "j = index_iso i"
      by blast
    have "reindexed_basis i = original_basis j"
      by (simp add: reindexed_basis_def i)
    have "reindexed_basis i \<in> range reindexed_basis"
      by (rule rangeI)
    show "x \<in> range reindexed_basis"
      using x \<open>reindexed_basis i = original_basis j\<close>
        \<open>reindexed_basis i \<in> range reindexed_basis\<close>
      by simp
  qed
qed

lemma reindexed_basis_inj:
  "inj reindexed_basis"
  using original.basis_inj index_iso_bij
  by (auto simp: reindexed_basis_def bij_def inj_def)

lemma reindexed_basis_independent:
  "original.independent (range reindexed_basis)"
  by (simp add: reindexed_basis_range original.basis_independent)

lemma reindexed_basis_span:
  "original.span (range reindexed_basis) = UNIV"
  by (simp add: reindexed_basis_range original.basis_span)

sublocale reindexed: indexed_algebra scale reindexed_basis
  by unfold_locales
    (fact reindexed_basis_inj reindexed_basis_independent
      reindexed_basis_span)+

lemma coordinate_reindexed:
  "reindexed.coordinates.coordinate x i =
    original.coordinates.coordinate x (index_iso i)"
  unfolding reindexed.coordinates.coordinate_def
    original.coordinates.coordinate_def
  apply (subst reindexed_basis_range)
  apply (simp add: reindexed_basis_def)
  done

lemma regular_matrix_reindexed_component [simp]:
  "reindexed.regular_matrix a $ i $ k =
    original.regular_matrix a $ index_iso i $ index_iso k"
  by (simp add: reindexed.regular_matrix_def
    original.regular_matrix_def reindexed.coordinates.matrix_of_def
    original.coordinates.matrix_of_def coordinate_reindexed
    reindexed_basis_def)

end

locale indexed_algebra_isomorphism =
  source: indexed_algebra source_scale source_basis +
  target: indexed_algebra target_scale target_basis
  for source_scale :: "'r::comm_ring_1 \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and source_basis :: "'i::finite \<Rightarrow> 'a"
    and target_scale :: "'r \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b"
    and target_basis :: "'i \<Rightarrow> 'b" +
  fixes iso :: "'a \<Rightarrow> 'b"
  assumes iso_module_hom: "module_hom source_scale target_scale iso"
    and iso_mult: "iso (x * y) = iso x * iso y"
    and iso_one: "iso 1 = 1"
    and iso_bij: "bij iso"
    and iso_basis: "iso (source_basis i) = target_basis i"
begin

interpretation iso: module_hom source_scale target_scale iso
  by (rule iso_module_hom)

lemma iso_basis_expansion:
  "(\<Sum>i\<in>UNIV. target_scale (source.coordinates.coordinate x i) (target_basis i)) = iso x"
  by (simp add: source.coordinates.basis_expansion flip: iso_basis iso.sum iso.scale)

lemma coordinate_iso:
  "target.coordinates.coordinate (iso x) i =
    source.coordinates.coordinate x i"
proof -
  have mapped: "target.coordinates.coordinate
      (\<Sum>j\<in>UNIV.
        target_scale (source.coordinates.coordinate x j) (target_basis j)) i =
    target.coordinates.coordinate (iso x) i"
    by (rule arg_cong[OF iso_basis_expansion])
  have coefficients: "target.coordinates.coordinate
      (\<Sum>j\<in>UNIV. target_scale (source.coordinates.coordinate x j) (target_basis j)) i =
    source.coordinates.coordinate x i"
  proof -
    have "target.coordinates.coordinate
        (\<Sum>j\<in>UNIV. target_scale (source.coordinates.coordinate x j) (target_basis j)) i =
      (\<Sum>j\<in>UNIV. source.coordinates.coordinate x j * target.coordinates.coordinate (target_basis j) i)"
      by (simp add: target.coordinates.coordinate_sum)
    also have "\<dots> = (\<Sum>j\<in>UNIV. if j = i then source.coordinates.coordinate x i else 0)"
      using target.coordinates.coordinate_basis by (metis mult.comm_neutral mult_not_zero)
    also have "\<dots> = source.coordinates.coordinate x i"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    using mapped coefficients by simp
qed

lemma regular_matrix_iso:
  "target.regular_matrix (iso a) = source.regular_matrix a"
proof -
  have entry:
    "target.regular_matrix (iso a) $ i $ j =
      source.regular_matrix a $ i $ j" for i j
  proof -
    have "target.regular_matrix (iso a) $ i $ j =
      target.coordinates.coordinate (iso a * target_basis j) i"
      by (simp add: target.regular_matrix_def
        target.left_multiplication_def)
    also have "\<dots> =
      target.coordinates.coordinate
        (iso a * iso (source_basis j)) i"
      by (simp only: iso_basis)
    also have "\<dots> =
      target.coordinates.coordinate (iso (a * source_basis j)) i"
      by (simp only: iso_mult)
    also have "\<dots> =
      source.coordinates.coordinate (a * source_basis j) i"
      by (rule coordinate_iso)
    also have "\<dots> = source.regular_matrix a $ i $ j"
      by (simp add: source.regular_matrix_def
        source.left_multiplication_def)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: entry vec_eq_iff)
qed

end

locale indexed_algebra_isomorphism_general =
  source: indexed_algebra source_scale source_basis +
  target: indexed_algebra target_scale target_basis
  for source_scale :: "'r::comm_ring_1 \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and source_basis :: "'i::finite \<Rightarrow> 'a"
    and target_scale :: "'r \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b"
    and target_basis :: "'j::finite \<Rightarrow> 'b" +
  fixes iso :: "'a \<Rightarrow> 'b"
    and index_iso :: "'i \<Rightarrow> 'j"
  assumes iso_module_hom: "module_hom source_scale target_scale iso"
    and iso_mult: "iso (x * y) = iso x * iso y"
    and iso_one: "iso 1 = 1"
    and iso_bij: "bij iso"
    and index_iso_bij: "bij index_iso"
begin

interpretation iso: module_hom source_scale target_scale iso
  by (rule iso_module_hom)

definition transported_basis :: "'i \<Rightarrow> 'b"
  where "transported_basis i = iso (source_basis i)"

lemma transported_basis_range:
  "range transported_basis = iso ` range source_basis"
  by (auto simp: transported_basis_def)

lemma transported_basis_inj:
  "inj transported_basis"
  using source.basis_inj iso_bij
  by (auto simp: transported_basis_def bij_def inj_def)

lemma transported_basis_independent:
  "target.independent (range transported_basis)"
  unfolding transported_basis_range
  apply (rule iso.independent_inj_image)
   apply (fact source.basis_independent)
  using iso_bij
  by (simp add: bij_def)

lemma transported_basis_span:
  "target.span (range transported_basis) = UNIV"
proof -
  have "target.span (range transported_basis) =
    iso ` source.span (range source_basis)"
    by (simp only: transported_basis_range iso.span_image)
  also have "\<dots> = iso ` UNIV"
    by (simp only: source.basis_span)
  also have "\<dots> = UNIV"
    using iso_bij by (simp add: bij_def)
  finally show ?thesis .
qed

sublocale transported: indexed_algebra target_scale transported_basis
  by unfold_locales
    (fact transported_basis_inj transported_basis_independent
      transported_basis_span)+

sublocale basis_iso: indexed_algebra_isomorphism
    source_scale source_basis target_scale transported_basis iso
  apply unfold_locales
     apply (fact iso_mult)
    apply (fact iso_one)
   apply (fact iso_bij)
  apply (simp add: transported_basis_def)
  done

sublocale reindexed_target:
  indexed_algebra_reindex target_scale target_basis index_iso
  by unfold_locales (fact index_iso_bij)

end

end
