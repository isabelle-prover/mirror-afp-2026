theory Tower_Bases
  imports Restriction_of_Scalars
begin

section \<open>Composition of bases\<close>

text \<open>
An indexed basis below is only a convenient locale wrapper around Isabelle's
existing set-valued notions of independence and span.  It adds no competing
basis predicate.
\<close>

locale indexed_basis =
  Modules.module scale
  for scale :: "'r::comm_ring_1 \<Rightarrow> 'a::ab_group_add \<Rightarrow> 'a" +
  fixes basis :: "'i::finite \<Rightarrow> 'a"
  assumes basis_inj: "inj basis"
    and independent_basis: "independent (range basis)"
    and span_basis: "span (range basis) = UNIV"
begin

definition coordinate :: "'a \<Rightarrow> 'i \<Rightarrow> 'r"
  where "coordinate x i = representation (range basis) x (basis i)"

lemma basis_mem_span [simp]:
  "basis i \<in> span (range basis)"
  by (rule span_base) blast

lemma all_mem_span [simp]:
  "x \<in> span (range basis)"
  using span_basis by simp

lemma coordinate_zero [simp]:
  "coordinate 0 i = 0"
  by (simp add: coordinate_def representation_zero)

lemma coordinate_add [simp]:
  "coordinate (x + y) i = coordinate x i + coordinate y i"
  by (simp add: coordinate_def representation_add independent_basis)

lemma coordinate_diff [simp]:
  "coordinate (x - y) i = coordinate x i - coordinate y i"
  by (simp add: coordinate_def representation_diff independent_basis)

lemma coordinate_scale [simp]:
  "coordinate (scale r x) i = r * coordinate x i"
  by (simp add: coordinate_def representation_scale independent_basis)

lemma coordinate_sum:
  "coordinate (\<Sum>x\<in>X. f x) i =
    (\<Sum>x\<in>X. coordinate (f x) i)"
  by (induction X rule: infinite_finite_induct) simp_all

lemma coordinate_basis [simp]:
  "coordinate (basis i) j = (if j = i then 1 else 0)"
proof -
  have "representation (range basis) (basis i) =
    (\<lambda>b. if b = basis i then 1 else 0)"
    by (rule representation_basis[OF independent_basis]) blast
  then show ?thesis
    by (simp add: coordinate_def basis_inj inj_eq)
qed

lemma basis_expansion:
  "(\<Sum>i\<in>UNIV. scale (coordinate x i) (basis i)) = x"
proof -
  have "(\<Sum>b\<in>range basis.
      scale (representation (range basis) x b) b) = x"
    by (rule sum_representation_eq[OF independent_basis])
      (simp_all add: span_basis)
  also have "(\<Sum>b\<in>range basis.
      scale (representation (range basis) x b) b) =
      (\<Sum>i\<in>UNIV. scale (coordinate x i) (basis i))"
    by (simp add: coordinate_def sum.reindex[OF basis_inj])
  finally show ?thesis .
qed

lemma coordinate_eq_iff:
  "x = y \<longleftrightarrow> (\<forall>i. coordinate x i = coordinate y i)"
proof
  show "x = y \<Longrightarrow> \<forall>i. coordinate x i = coordinate y i"
    by simp
next
  assume coordinates: "\<forall>i. coordinate x i = coordinate y i"
  have "(\<Sum>i\<in>UNIV. scale (coordinate x i) (basis i)) =
    (\<Sum>i\<in>UNIV. scale (coordinate y i) (basis i))"
    using coordinates by simp
  then show "x = y"
    by (simp only: basis_expansion)
qed

end

locale indexed_algebra_tower =
  algebra_tower rS sA rA
  for rS :: "'r::comm_ring_1 \<Rightarrow> 's::comm_ring_1 \<Rightarrow> 's"
    and sA :: "'s \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and rA :: "'r \<Rightarrow> 'a \<Rightarrow> 'a" +
  fixes lower_basis :: "'i::finite \<Rightarrow> 's"
    and upper_basis :: "'j::finite \<Rightarrow> 'a"
  assumes lower_basis_inj: "inj lower_basis"
    and lower_basis_independent: "RS.independent (range lower_basis)"
    and lower_basis_span: "RS.span (range lower_basis) = UNIV"
    and upper_basis_inj: "inj upper_basis"
    and upper_basis_independent: "SA.independent (range upper_basis)"
    and upper_basis_span: "SA.span (range upper_basis) = UNIV"
begin

sublocale lower: indexed_basis rS lower_basis
  by unfold_locales
    (fact lower_basis_inj lower_basis_independent lower_basis_span)+

sublocale upper: indexed_basis sA upper_basis
  by unfold_locales
    (fact upper_basis_inj upper_basis_independent upper_basis_span)+

definition tower_basis :: "('i \<times> 'j) \<Rightarrow> 'a"
  where "tower_basis ij =
    sA (lower_basis (fst ij)) (upper_basis (snd ij))"

definition tower_coordinate :: "'a \<Rightarrow> ('i \<times> 'j) \<Rightarrow> 'r"
  where "tower_coordinate x ij =
    lower.coordinate (upper.coordinate x (snd ij)) (fst ij)"

lemma tower_coordinate_zero [simp]:
  "tower_coordinate 0 ij = 0"
  by (simp add: tower_coordinate_def)

lemma tower_coordinate_add [simp]:
  "tower_coordinate (x + y) ij =
    tower_coordinate x ij + tower_coordinate y ij"
  by (simp add: tower_coordinate_def)

lemma tower_coordinate_diff [simp]:
  "tower_coordinate (x - y) ij =
    tower_coordinate x ij - tower_coordinate y ij"
  by (simp add: tower_coordinate_def)

lemma upper_coordinate_lower_scale:
  "upper.coordinate (rA r x) j =
    rS r (upper.coordinate x j)"
proof -
  have "upper.coordinate (rA r x) j =
      upper.coordinate (sA (rS r 1) x) j"
    by simp
  also have "\<dots> = (rS r 1) * upper.coordinate x j"
    by simp
  also have "\<dots> = rS r (upper.coordinate x j)"
    by (rule RS.scale_eq_embed_mult[symmetric])
  finally show ?thesis .
qed

lemma tower_coordinate_scale [simp]:
  "tower_coordinate (rA r x) ij = r * tower_coordinate x ij"
  by (cases ij)
    (simp only: tower_coordinate_def fst_conv snd_conv
      upper_coordinate_lower_scale lower.coordinate_scale)

lemma tower_coordinate_sum:
  "tower_coordinate (\<Sum>x\<in>X. f x) ij =
    (\<Sum>x\<in>X. tower_coordinate (f x) ij)"
  by (induction X rule: infinite_finite_induct) simp_all

lemma tower_coordinate_basis [simp]:
  "tower_coordinate (tower_basis ij) kl =
    (if kl = ij then 1 else 0)"
  by (cases ij; cases kl)
    (simp add: tower_coordinate_def tower_basis_def)

lemma tower_basis_inj:
  "inj tower_basis"
proof (rule injI)
  fix ij kl
  assume equal: "tower_basis ij = tower_basis kl"
  have "tower_coordinate (tower_basis ij) ij =
    tower_coordinate (tower_basis kl) ij"
    using equal by simp
  then show "ij = kl"
    by (cases "ij = kl") simp_all
qed

lemma tower_basis_span:
  "RA.span (range tower_basis) = UNIV"
proof -
  have upper_term:
    "sA (upper.coordinate x j) (upper_basis j) =
      (\<Sum>i\<in>UNIV. rA
        (lower.coordinate (upper.coordinate x j) i)
        (tower_basis (i, j)))"
    for x j
  proof -
    have "sA (upper.coordinate x j) (upper_basis j) =
      sA (\<Sum>i\<in>UNIV.
        rS (lower.coordinate (upper.coordinate x j) i) (lower_basis i))
        (upper_basis j)"
      by (simp only: lower.basis_expansion)
    also have "\<dots> = (\<Sum>i\<in>UNIV.
      sA (rS (lower.coordinate (upper.coordinate x j) i) (lower_basis i))
        (upper_basis j))"
      by (rule SA.scale_sum_left)
    also have "\<dots> = (\<Sum>i\<in>UNIV. rA
      (lower.coordinate (upper.coordinate x j) i)
      (tower_basis (i, j)))"
    proof (rule sum.cong)
      show "(UNIV :: 'i set) = UNIV"
        by simp
      fix i
      assume "i \<in> (UNIV :: 'i set)"
      show "sA (rS (lower.coordinate (upper.coordinate x j) i)
          (lower_basis i)) (upper_basis j) =
        rA (lower.coordinate (upper.coordinate x j) i)
          (tower_basis (i, j))"
        unfolding tower_basis_def
        by (simp only: fst_conv snd_conv scalar_compat)
    qed
    finally show ?thesis .
  qed

  have expansion:
    "(\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. rA
      (lower.coordinate (upper.coordinate x j) i)
      (tower_basis (i, j))) = x"
    for x
  proof -
    have "(\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. rA
      (lower.coordinate (upper.coordinate x j) i)
      (tower_basis (i, j))) =
      (\<Sum>j\<in>UNIV. sA (upper.coordinate x j) (upper_basis j))"
    proof (rule sum.cong)
      show "(UNIV :: 'j set) = UNIV"
        by simp
      fix j
      assume "j \<in> (UNIV :: 'j set)"
      show "(\<Sum>i\<in>UNIV. rA
        (lower.coordinate (upper.coordinate x j) i)
        (tower_basis (i, j))) =
        sA (upper.coordinate x j) (upper_basis j)"
        by (rule upper_term[symmetric])
    qed
    also have "\<dots> = x"
      by (rule upper.basis_expansion)
    finally show ?thesis .
  qed

  have inner_span:
    "(\<Sum>i\<in>UNIV. rA
      (lower.coordinate (upper.coordinate x j) i)
      (tower_basis (i, j))) \<in> RA.span (range tower_basis)"
    for x j
  proof (rule RA.span_sum)
    fix i
    assume "i \<in> (UNIV :: 'i set)"
    show "rA (lower.coordinate (upper.coordinate x j) i)
      (tower_basis (i, j)) \<in> RA.span (range tower_basis)"
      by (rule RA.span_scale, rule RA.span_base) blast
  qed

  have "x \<in> RA.span (range tower_basis)" for x
  proof -
    have "(\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. rA
      (lower.coordinate (upper.coordinate x j) i)
      (tower_basis (i, j))) \<in> RA.span (range tower_basis)"
    proof (rule RA.span_sum)
      fix j
      assume "j \<in> (UNIV :: 'j set)"
      show "(\<Sum>i\<in>UNIV. rA
        (lower.coordinate (upper.coordinate x j) i)
        (tower_basis (i, j))) \<in> RA.span (range tower_basis)"
        by (rule inner_span)
    qed
    then show ?thesis
      by (simp only: expansion)
  qed
  then show ?thesis
    by auto
qed

lemma tower_basis_independent:
  "RA.independent (range tower_basis)"
  unfolding RA.independent_explicit_module
proof (intro allI impI)
  fix T c w
  assume finite_T: "finite T"
    and subset: "T \<subseteq> range tower_basis"
    and sum_zero: "(\<Sum>x\<in>T. rA (c x) x) = 0"
    and w: "w \<in> T"
  obtain ij where w_eq: "w = tower_basis ij"
    using subset w by blast
  have "0 = tower_coordinate (\<Sum>x\<in>T. rA (c x) x) ij"
    using sum_zero by simp
  also have "\<dots> =
    (\<Sum>x\<in>T. tower_coordinate (rA (c x) x) ij)"
    by (rule tower_coordinate_sum)
  also have "\<dots> = (\<Sum>x\<in>T. c x * tower_coordinate x ij)"
  proof (rule sum.cong)
    show "T = T"
      by simp
    fix x
    assume "x \<in> T"
    show "tower_coordinate (rA (c x) x) ij =
      c x * tower_coordinate x ij"
      by (rule tower_coordinate_scale)
  qed
  also have "\<dots> = c w"
  proof -
    have summand:
      "c x * tower_coordinate x ij = (if x = w then c w else 0)"
      if "x \<in> T" for x
    proof (cases "x = w")
      case True
      then show ?thesis
        by (simp add: w_eq)
    next
      case False
      have "x \<in> range tower_basis"
        using subset that by blast
      obtain kl where x_eq: "x = tower_basis kl"
        using \<open>x \<in> range tower_basis\<close> by blast
      have "kl \<noteq> ij"
        using False x_eq w_eq tower_basis_inj
        by (auto simp: inj_def)
      then show ?thesis
        using False by (simp add: x_eq)
    qed
    have "(\<Sum>x\<in>T. c x * tower_coordinate x ij) =
      (\<Sum>x\<in>T. if x = w then c w else 0)"
      by (rule sum.cong) (simp_all add: summand)
    also have "\<dots> = c w"
      using finite_T w by simp
    finally show ?thesis .
  qed
  finally show "c w = 0"
    by simp
qed

theorem basis_tower:
  "RA.independent (range tower_basis) \<and>
    RA.span (range tower_basis) = UNIV"
  using tower_basis_independent tower_basis_span by blast

sublocale composed: indexed_basis rA tower_basis
  by unfold_locales
    (fact tower_basis_inj tower_basis_independent tower_basis_span)+

lemma composed_coordinate:
  "composed.coordinate x ij = tower_coordinate x ij"
proof -
  have mapped: "tower_coordinate
      (\<Sum>kl\<in>UNIV.
        rA (composed.coordinate x kl) (tower_basis kl)) ij =
    tower_coordinate x ij"
    by (rule arg_cong[OF composed.basis_expansion])
  have coefficients: "tower_coordinate
      (\<Sum>kl\<in>UNIV.
        rA (composed.coordinate x kl) (tower_basis kl)) ij =
    composed.coordinate x ij"
  proof -
    have "tower_coordinate
        (\<Sum>kl\<in>UNIV.
          rA (composed.coordinate x kl) (tower_basis kl)) ij =
      (\<Sum>kl\<in>UNIV.
        tower_coordinate
          (rA (composed.coordinate x kl) (tower_basis kl)) ij)"
      by (rule tower_coordinate_sum)
    also have "\<dots> =
      (\<Sum>kl\<in>UNIV.
        composed.coordinate x kl *
          tower_coordinate (tower_basis kl) ij)"
    proof (rule sum.cong)
      show "(UNIV :: ('i \<times> 'j) set) = UNIV"
        by simp
      fix kl
      assume "kl \<in> (UNIV :: ('i \<times> 'j) set)"
      show "tower_coordinate
          (rA (composed.coordinate x kl) (tower_basis kl)) ij =
        composed.coordinate x kl *
          tower_coordinate (tower_basis kl) ij"
        by (rule tower_coordinate_scale)
    qed
    also have "\<dots> =
      (\<Sum>kl\<in>UNIV.
        if kl = ij then composed.coordinate x ij else 0)"
    proof (rule sum.cong)
      show "(UNIV :: ('i \<times> 'j) set) = UNIV"
        by simp
      fix kl
      assume "kl \<in> (UNIV :: ('i \<times> 'j) set)"
      show "composed.coordinate x kl *
          tower_coordinate (tower_basis kl) ij =
        (if kl = ij then composed.coordinate x ij else 0)"
        by (cases "kl = ij") simp_all
    qed
    also have "\<dots> = composed.coordinate x ij"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    using mapped coefficients by simp
qed

end

end
