theory Restriction_of_Scalars
  imports Algebra_Towers
begin

section \<open>Restriction of scalars\<close>

text \<open>
Linear maps in \<^theory>\<open>HOL.Modules\<close> are plain functions equipped with a
locale proposition.  Restricting scalars therefore changes only the proposition
used to view a function, never the function itself.
\<close>

definition restrict_scalars :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "restrict_scalars f x = f x"

lemma restrict_scalars_apply [simp]:
  "restrict_scalars f x = f x"
  by (simp add: restrict_scalars_def)

definition subspace_rel :: "'a::ab_group_add set \<Rightarrow> ('a \<times> 'a) set"
  where "subspace_rel U = {(x, y). x - y \<in> U}"

definition subspace_coset :: "'a::ab_group_add set \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "subspace_coset U x = ((+) x) ` U"

lemma subspace_coset_class:
  "subspace_coset U x = {y. (y, x) \<in> subspace_rel U}"
proof (rule equalityI)
  show "subspace_coset U x \<subseteq> {y. (y, x) \<in> subspace_rel U}"
  proof
    fix y
    assume "y \<in> subspace_coset U x"
    then obtain u where "u \<in> U" "y = x + u"
      by (auto simp: subspace_coset_def)
    then show "y \<in> {y. (y, x) \<in> subspace_rel U}"
      by (simp add: subspace_rel_def)
  qed
  show "{y. (y, x) \<in> subspace_rel U} \<subseteq> subspace_coset U x"
  proof
    fix y
    assume "y \<in> {y. (y, x) \<in> subspace_rel U}"
    then have "y - x \<in> U"
      by (simp add: subspace_rel_def)
    then have "x + (y - x) \<in> ((+) x) ` U"
      by (rule imageI)
    then show "y \<in> subspace_coset U x"
      by (simp add: subspace_coset_def)
  qed
qed

context Modules.module
begin

lemma subspace_rel_refl:
  assumes "subspace U"
  shows "(x, x) \<in> subspace_rel U"
  using assms by (simp add: subspace_rel_def subspace_0)

lemma subspace_rel_sym:
  assumes U: "subspace U"
    and xy: "(x, y) \<in> subspace_rel U"
  shows "(y, x) \<in> subspace_rel U"
proof -
  have "x - y \<in> U"
    using xy by (simp add: subspace_rel_def)
  then have "- (x - y) \<in> U"
    by (rule subspace_neg[OF U])
  then show ?thesis
    by (simp add: subspace_rel_def)
qed

lemma subspace_rel_trans:
  assumes U: "subspace U"
    and xy: "(x, y) \<in> subspace_rel U"
    and yz: "(y, z) \<in> subspace_rel U"
  shows "(x, z) \<in> subspace_rel U"
proof -
  have "x - y \<in> U" and "y - z \<in> U"
    using xy yz by (simp_all add: subspace_rel_def)
  then have "(x - y) + (y - z) \<in> U"
    by (rule subspace_add[OF U])
  then show ?thesis
    by (simp add: subspace_rel_def)
qed

lemma subspace_rel_equiv:
  assumes U: "subspace U"
  shows "equiv UNIV (subspace_rel U)"
proof (rule equivI)
  show "subspace_rel U \<subseteq> UNIV \<times> UNIV"
    by simp
  show "refl_on UNIV (subspace_rel U)"
    unfolding refl_on_def
    using subspace_rel_refl[OF U] by simp
  show "sym (subspace_rel U)"
  proof (unfold sym_def, intro allI impI)
    fix x y
    assume "(x, y) \<in> subspace_rel U"
    then show "(y, x) \<in> subspace_rel U"
      by (rule subspace_rel_sym[OF U])
  qed
  show "trans (subspace_rel U)"
  proof (unfold trans_def, intro allI impI)
    fix x y z
    assume "(x, y) \<in> subspace_rel U" "(y, z) \<in> subspace_rel U"
    then show "(x, z) \<in> subspace_rel U"
      by (rule subspace_rel_trans[OF U])
  qed
qed

end

locale scalar_tower_pair =
  source: compatible_scalar_actions rS sA rA +
  target: compatible_scalar_actions rS sB rB
  for rS :: "'r::comm_ring_1 \<Rightarrow> 's::comm_ring_1 \<Rightarrow> 's"
    and sA :: "'s \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and rA :: "'r \<Rightarrow> 'a \<Rightarrow> 'a"
    and sB :: "'s \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b"
    and rB :: "'r \<Rightarrow> 'b \<Rightarrow> 'b"
begin

lemma restrict_scalars_module_hom:
  assumes "module_hom sA sB f"
  shows "module_hom rA rB (restrict_scalars f)"
proof -
  interpret f: module_hom sA sB f
    by fact
  show ?thesis
    by unfold_locales (simp_all add: f.add f.scale)
qed

lemma restrict_scalars_id [simp]:
  "restrict_scalars id = id"
  by (rule ext) simp

lemma restrict_scalars_comp [simp]:
  "restrict_scalars (g \<circ> f) =
    restrict_scalars g \<circ> restrict_scalars f"
  by (rule ext) simp

lemma restrict_scalars_inj [simp]:
  "inj (restrict_scalars f) \<longleftrightarrow> inj f"
  by (simp add: inj_def)

lemma restrict_scalars_surj [simp]:
  "surj (restrict_scalars f) \<longleftrightarrow> surj f"
  by (simp add: surj_def)

lemma restrict_scalars_bij [simp]:
  "bij (restrict_scalars f) \<longleftrightarrow> bij f"
  by (simp add: bij_def)

lemma restrict_scalars_kernel [simp]:
  "{x. restrict_scalars f x = 0} = {x. f x = 0}"
  by simp

lemma restrict_scalars_image [simp]:
  "restrict_scalars f ` X = f ` X"
  by auto

lemma restrict_scalars_range [simp]:
  "range (restrict_scalars f) = range f"
  by auto

lemma source_subspace_restrict_scalars:
  assumes U: "source.SA.subspace U"
  shows "source.RA.subspace U"
proof (rule source.RA.subspaceI)
  show "0 \<in> U"
    by (rule source.SA.subspace_0[OF U])
  show "x + y \<in> U" if "x \<in> U" "y \<in> U" for x y
    using that by (rule source.SA.subspace_add[OF U])
  show "rA r x \<in> U" if "x \<in> U" for r x
  proof -
    have "sA (rS r 1) x \<in> U"
      using that by (rule source.SA.subspace_scale[OF U])
    then show ?thesis
      by simp
  qed
qed

lemma target_subspace_restrict_scalars:
  assumes U: "target.SA.subspace U"
  shows "target.RA.subspace U"
proof (rule target.RA.subspaceI)
  show "0 \<in> U"
    by (rule target.SA.subspace_0[OF U])
  show "x + y \<in> U" if "x \<in> U" "y \<in> U" for x y
    using that by (rule target.SA.subspace_add[OF U])
  show "rB r x \<in> U" if "x \<in> U" for r x
  proof -
    have "sB (rS r 1) x \<in> U"
      using that by (rule target.SA.subspace_scale[OF U])
    then show ?thesis
      by simp
  qed
qed

lemma restrict_scalars_kernel_subspace:
  assumes f: "module_hom sA sB f"
  shows "source.RA.subspace {x. restrict_scalars f x = 0}"
proof -
  interpret rf: module_hom rA rB "restrict_scalars f"
    by (rule restrict_scalars_module_hom[OF f])
  show ?thesis
    by (rule rf.subspace_kernel)
qed

lemma restrict_scalars_image_subspace:
  assumes f: "module_hom sA sB f"
    and U: "source.SA.subspace U"
  shows "target.RA.subspace (restrict_scalars f ` U)"
proof -
  interpret rf: module_hom rA rB "restrict_scalars f"
    by (rule restrict_scalars_module_hom[OF f])
  show ?thesis
    by (rule rf.subspace_image[OF source_subspace_restrict_scalars[OF U]])
qed

lemma restrict_scalars_quotient:
  assumes f: "module_hom sA sB f"
    and maps: "f ` U \<subseteq> V"
    and xy: "(x, y) \<in> subspace_rel U"
  shows "(restrict_scalars f x, restrict_scalars f y) \<in> subspace_rel V"
proof -
  interpret f: module_hom sA sB f
    by fact
  have "f (x - y) \<in> f ` U"
    using xy by (auto simp: subspace_rel_def)
  then have "f (x - y) \<in> V"
    using maps by blast
  then show ?thesis
    by (simp add: subspace_rel_def f.diff)
qed

lemma restrict_scalars_coset_image:
  assumes "module_hom sA sB f"
  shows "restrict_scalars f ` subspace_coset U x =
    subspace_coset (f ` U) (f x)"
proof -
  interpret f: module_hom sA sB f
    by fact
  show ?thesis
  proof (rule equalityI)
    show "restrict_scalars f ` subspace_coset U x \<subseteq>
      subspace_coset (f ` U) (f x)"
    proof
      fix y
      assume "y \<in> restrict_scalars f ` subspace_coset U x"
      then obtain z u where "u \<in> U" "z = x + u"
        and "y = f z"
        by (auto simp: subspace_coset_def)
      then have "y = f x + f u"
        by (simp add: f.add)
      moreover have "f u \<in> f ` U"
        using \<open>u \<in> U\<close> by blast
      ultimately show "y \<in> subspace_coset (f ` U) (f x)"
        by (auto simp: subspace_coset_def)
    qed
    show "subspace_coset (f ` U) (f x) \<subseteq>
      restrict_scalars f ` subspace_coset U x"
    proof
      fix y
      assume "y \<in> subspace_coset (f ` U) (f x)"
      then obtain u where "u \<in> U" "y = f x + f u"
        by (auto simp: subspace_coset_def)
      then have "y = restrict_scalars f (x + u)"
        by (simp add: f.add)
      moreover have "x + u \<in> subspace_coset U x"
        using \<open>u \<in> U\<close> by (auto simp: subspace_coset_def)
      ultimately show "y \<in> restrict_scalars f ` subspace_coset U x"
        by blast
    qed
  qed
qed

end

locale scalar_tower_pair_fields =
  scalar_tower_pair rS sA rA sB rB
  for rS :: "'r::field \<Rightarrow> 's::field \<Rightarrow> 's"
    and sA :: "'s \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and rA :: "'r \<Rightarrow> 'a \<Rightarrow> 'a"
    and sB :: "'s \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b"
    and rB :: "'r \<Rightarrow> 'b \<Rightarrow> 'b"
begin

lemma restrict_scalars_linear:
  assumes "Vector_Spaces.linear sA sB f"
  shows "Vector_Spaces.linear rA rB (restrict_scalars f)"
  using assms restrict_scalars_module_hom
  by (simp add: module_hom_iff_linear)

end

end
