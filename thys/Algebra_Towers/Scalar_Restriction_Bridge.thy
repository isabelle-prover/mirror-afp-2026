theory Scalar_Restriction_Bridge
  imports "HOL-New_Algebra.Steinitz"
begin

section \<open>Restriction of scalars for carrier-based vector spaces\<close>

text \<open>
The upper carrier is an arbitrary vector space, not a field.  In particular,
it may be the zero space.  The lower vector space describes the intermediate
field over the smaller field, using the same scalar operations.  These
parameters can also describe subfields of a noncommutative ambient ring and a
vector subspace of that ring.
\<close>

locale scalar_restriction_tower =
  lower: Vector_Space K sadd smult szero sone sadd szero F smult +
  upper: Vector_Space F sadd smult szero sone vadd vzero E scale
  for K F :: "'s set"
    and sadd smult :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    and szero sone :: 's
    and vadd :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and vzero :: 'v
    and E :: "'v set"
    and scale :: "'s \<Rightarrow> 'v \<Rightarrow> 'v" +
  assumes base_subset: "K \<subseteq> F"
begin

sublocale direct: Vector_Space K sadd smult szero sone vadd vzero E scale
proof (intro Vector_Space.intro Vector_Space_axioms.intro)
  show "Field K sadd smult szero sone" by (rule lower.Field_axioms)
  show "Abelian_Group E vadd vzero" by (rule upper.vadd_group)
  show "\<And>a v. \<lbrakk>a \<in> K; v \<in> E\<rbrakk> \<Longrightarrow> scale a v \<in> E"
    using base_subset by (blast intro: upper.scale_closed)
  show "\<And>a u v. \<lbrakk>a \<in> K; u \<in> E; v \<in> E\<rbrakk> \<Longrightarrow>
      scale a (vadd u v) = vadd (scale a u) (scale a v)"
    using base_subset by (blast intro: upper.scale_distrib_vadd)
  show "\<And>a b v. \<lbrakk>a \<in> K; b \<in> K; v \<in> E\<rbrakk> \<Longrightarrow>
      scale (sadd a b) v = vadd (scale a v) (scale b v)"
    using base_subset by (blast intro: upper.scale_distrib_add)
  show "\<And>a b v. \<lbrakk>a \<in> K; b \<in> K; v \<in> E\<rbrakk> \<Longrightarrow>
      scale (smult a b) v = scale a (scale b v)"
    using base_subset by (blast intro: upper.scale_scale)
  show "\<And>v. v \<in> E \<Longrightarrow> scale sone v = v"
    by (rule upper.scale_one)
qed

text \<open>Restricting the field changes the allowed coefficients, but not
the expression for a linear combination.\<close>

lemma restricted_lincomb:
  "direct.lincomb c A = upper.lincomb c A"
  by (simp only: direct.lincomb_def)

definition product_basis :: "'s set \<Rightarrow> 'v set \<Rightarrow> 'v set"
  where "product_basis B C = (\<lambda>(b,c). scale b c) ` (B \<times> C)"

lemma product_basis_finite:
  assumes "finite B" "finite C"
  shows "finite (product_basis B C)"
  using assms by (simp add: product_basis_def)

lemma product_basis_subset:
  assumes "B \<subseteq> F" "C \<subseteq> E"
  shows "product_basis B C \<subseteq> E"
  using assms unfolding product_basis_def by (auto intro: upper.scale_closed)

lemma product_basis_empty [simp]:
  "product_basis B {} = {}"
  by (simp add: product_basis_def)

lemma lower_basis_nonzero:
  assumes B: "lower.basis B" and b: "b \<in> B"
  shows "b \<noteq> szero"
proof
  assume "b = szero"
  have ind: "lower.lin_indep B" by (rule lower.basis_lin_indep[OF B])
  have "b \<notin> lower.span (B - {b})"
    by (rule lower.lin_indep_not_in_span[OF ind b])
  moreover have "b \<in> lower.span (B - {b})"
    using \<open>b = szero\<close> lower.span_zero by simp
  ultimately show False by contradiction
qed

lemma upper_basis_scaled_unique:
  assumes C: "upper.basis C" and c: "c \<in> C" and d: "d \<in> C"
    and b: "b \<in> F" and e: "e \<in> F"
    and eq: "scale b c = scale e d"
  shows "b = (if c = d then e else szero)"
proof -
  have finC: "finite C" and CE: "C \<subseteq> E"
    using C by (auto simp: upper.basis_def)
  have ind: "upper.mod.lin_indep C"
    by (rule iffD1[OF upper.lin_indep_iff_mod_lin_indep[OF finC CE]
        upper.basis_lin_indep[OF C]])
  have cE: "c \<in> E" and dE: "d \<in> E" using CE c d by blast+
  have coeff_b: "upper.mod.coeffs_on (\<lambda>_. b) {c}"
    by (rule upper.mod.coeffs_onI) (simp add: b)
  have coeff_e: "upper.mod.coeffs_on (\<lambda>_. e) {d}"
    by (rule upper.mod.coeffs_onI) (simp add: e)
  have comb:
    "upper.mod.lincomb (\<lambda>_. b) {c} = upper.mod.lincomb (\<lambda>_. e) {d}"
    using eq by (simp add: cE dE b e)
  have "(if c \<in> {c} then b else szero) =
    (if c \<in> {d} then e else szero)"
    by (rule upper.mod.lin_indep_lincomb_unique_gen[OF ind _ _ _ _ coeff_b coeff_e comb])
      (use c d in auto)
  then show ?thesis by simp
qed

lemma product_basis_injective:
  assumes B: "lower.basis B" and C: "upper.basis C"
  shows "inj_on (\<lambda>(b,c). scale b c) (B \<times> C)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> B \<times> C" and y: "y \<in> B \<times> C"
    and eq: "(\<lambda>(b,c). scale b c) x = (\<lambda>(b,c). scale b c) y"
  obtain b c where x': "x = (b,c)" and b: "b \<in> B" and c: "c \<in> C"
    using x by (cases x) auto
  obtain e d where y': "y = (e,d)" and e: "e \<in> B" and d: "d \<in> C"
    using y by (cases y) auto
  have BF: "B \<subseteq> F" using B by (auto simp: lower.basis_def)
  have bF: "b \<in> F" and eF: "e \<in> F" using BF b e by blast+
  have scaled: "scale b c = scale e d" using eq x' y' by simp
  have unique: "b = (if c = d then e else szero)"
    by (rule upper_basis_scaled_unique[OF C c d bF eF scaled])
  have "c = d" using unique lower_basis_nonzero[OF B b] by (cases "c = d") auto
  then have "b = e" using unique by simp
  then show "x = y" using x' y' \<open>c = d\<close> by simp
qed

lemma scalar_lower_combination_in_product_span:
  assumes BF: "B \<subseteq> F" and CE: "C \<subseteq> E" and c: "c \<in> C"
    and fin: "finite T" and TB: "T \<subseteq> B"
    and coeff: "\<And>b. b \<in> T \<Longrightarrow> f b \<in> K"
  shows "scale (lower.lincomb f T) c \<in> direct.span (product_basis B C)"
proof -
  have PE: "product_basis B C \<subseteq> E" by (rule product_basis_subset[OF BF CE])
  have cE: "c \<in> E" using c CE by blast
  have step: "scale (lower.lincomb f U) c \<in> direct.span (product_basis B C)"
    if "finite U" "U \<subseteq> B" "\<forall>b\<in>U. f b \<in> K" for U
    using that
  proof (induction U rule: finite_induct)
    case empty
    then show ?case
      by (simp add: upper.mod.scale_zero_scalar cE)
  next
    case (insert b U)
    have bF: "b \<in> F" and UF: "U \<subseteq> F"
      using insert.prems BF by auto
    have fK: "f b \<in> K" and fUK: "\<And>x. x \<in> U \<Longrightarrow> f x \<in> K"
      using insert.prems by auto
    have fF: "f b \<in> F" and fUF: "\<And>x. x \<in> U \<Longrightarrow> f x \<in> F"
      using fK fUK base_subset by blast+
    have tailF: "lower.lincomb f U \<in> F"
      by (rule lower.lincomb_closed[OF UF fUK])
    have termF: "smult (f b) b \<in> F"
      by (rule lower.scale_closed[OF fK bF])
    have termsU: "(\<lambda>x. smult (f x) x) \<in> U \<rightarrow> F"
      using UF fUK by (auto intro: lower.scale_closed)
    have split: "lower.lincomb f (insert b U) =
        sadd (smult (f b) b) (lower.lincomb f U)"
      using lower.vadd.fincomp_insert[OF insert.hyps(1,2) termsU termF]
      by (simp only: lower.lincomb_def)
    have base: "scale b c \<in> direct.span (product_basis B C)"
    proof (rule direct.span_incl[OF PE])
      show "scale b c \<in> product_basis B C"
        using insert.prems c by (auto simp: product_basis_def)
    qed
    have first: "scale (smult (f b) b) c \<in> direct.span (product_basis B C)"
      using direct.span_scale[OF PE fK base] upper.scale_scale[OF fF bF cE] by simp
    have rest: "scale (lower.lincomb f U) c \<in> direct.span (product_basis B C)"
      using insert.IH insert.prems by auto
    have "vadd (scale (smult (f b) b) c) (scale (lower.lincomb f U) c)
        \<in> direct.span (product_basis B C)"
      by (rule direct.span_vadd[OF PE first rest])
    then show ?case
      using upper.scale_distrib_add[OF termF tailF cE] by (simp only: split)
  qed
  show ?thesis by (rule step[OF fin TB]) (use coeff in blast)
qed

lemma fincomp_in_direct_span:
  assumes PE: "P \<subseteq> E" and fin: "finite A"
    and terms: "\<And>a. a \<in> A \<Longrightarrow> g a \<in> direct.span P"
  shows "upper.vadd.fincomp g A \<in> direct.span P"
  using fin terms
proof (induction A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  have ga: "g a \<in> direct.span P" using insert.prems by simp
  have rest: "upper.vadd.fincomp g A \<in> direct.span P"
    using insert.IH insert.prems by blast
  have gE: "g \<in> insert a A \<rightarrow> E"
    using insert.prems direct.span_subset_V[OF PE] by blast
  have "vadd (g a) (upper.vadd.fincomp g A) \<in> direct.span P"
    by (rule direct.span_vadd[OF PE ga rest])
  then show ?case using insert.hyps gE by simp
qed

lemma product_basis_spanning:
  assumes B: "lower.basis B" and C: "upper.basis C"
  shows "direct.spanning (product_basis B C)"
proof -
  have finB: "finite B" and BF: "B \<subseteq> F"
    using B by (auto simp: lower.basis_def)
  have finC: "finite C" and CE: "C \<subseteq> E"
    using C by (auto simp: upper.basis_def)
  have PE: "product_basis B C \<subseteq> E" by (rule product_basis_subset[OF BF CE])
  have finP: "finite (product_basis B C)" by (rule product_basis_finite[OF finB finC])
  have lower_span: "lower.spanning B" by (rule lower.basis_spanning[OF B])
  have upper_span: "upper.spanning C" by (rule upper.basis_spanning[OF C])
  have all_span: "x \<in> direct.span (product_basis B C)" if xE: "x \<in> E" for x
  proof -
    obtain d where d: "d \<in> C \<rightarrow>\<^sub>E F" and x: "x = upper.lincomb d C"
      using upper_span xE by (auto simp: upper.spanning_def)
    have summand: "scale (d c) c \<in> direct.span (product_basis B C)" if c: "c \<in> C" for c
    proof -
      have dcF: "d c \<in> F" using d c by auto
      obtain f where f: "f \<in> B \<rightarrow>\<^sub>E K" and dc: "d c = lower.lincomb f B"
        using lower_span dcF by (auto simp: lower.spanning_def)
      have "scale (lower.lincomb f B) c \<in> direct.span (product_basis B C)"
        by (rule scalar_lower_combination_in_product_span[OF BF CE c finB subset_refl])
          (use f in auto)
      then show ?thesis using dc by simp
    qed
    have "upper.vadd.fincomp (\<lambda>c. scale (d c) c) C
        \<in> direct.span (product_basis B C)"
      by (rule fincomp_in_direct_span[OF PE finC summand])
    then show ?thesis using x by (simp add: upper.lincomb_def)
  qed
  have "direct.mod.spanning (product_basis B C)"
    by (rule direct.mod.spanningI[OF PE all_span])
  then show ?thesis
    using direct.spanning_iff_mod_spanning[OF finP PE] by blast
qed

lemma scale_lower_lincomb:
  assumes BF: "B \<subseteq> F" and cE: "c \<in> E"
    and fK: "\<And>b. b \<in> B \<Longrightarrow> f b \<in> K"
  shows "scale (lower.lincomb f B) c =
    upper.vadd.fincomp (\<lambda>b. scale (smult (f b) b) c) B"
proof -
  have terms: "(\<lambda>b. smult (f b) b) \<in> B \<rightarrow> F"
    using BF fK by (auto intro: lower.scale_closed)
  have hom: "scale (lower.vadd.fincomp (\<lambda>b. smult (f b) b) B) c =
      upper.vadd.fincomp (\<lambda>b. scale (smult (f b) b) c) B"
  proof (rule fincomp_hom[OF lower.vadd.commutative_monoid_axioms
        upper.vadd.commutative_monoid_axioms])
    show "\<And>x. x \<in> F \<Longrightarrow> scale x c \<in> E"
      by (rule upper.scale_closed[OF _ cE])
    show "scale szero c = vzero" by (rule upper.mod.scale_zero_scalar[OF cE])
    show "\<And>x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow>
        scale (sadd x y) c = vadd (scale x c) (scale y c)"
      by (rule upper.scale_distrib_add[OF _ _ cE])
    show "(\<lambda>b. smult (f b) b) \<in> B \<rightarrow> F" by (rule terms)
  qed
  show ?thesis using hom by (simp only: lower.lincomb_def)
qed

lemma vector_fincomp_cartesian:
  assumes finB: "finite B" and finC: "finite C"
    and gE: "\<And>b c. \<lbrakk>b \<in> B; c \<in> C\<rbrakk> \<Longrightarrow> g (b,c) \<in> E"
  shows "upper.vadd.fincomp g (B \<times> C) =
    upper.vadd.fincomp (\<lambda>c. upper.vadd.fincomp (\<lambda>b. g (b,c)) B) C"
proof -
  have disjoint: "pairwise (\<lambda>c d. disjnt (B \<times> {c}) (B \<times> {d})) C"
    by (auto simp: pairwise_def disjnt_def)
  have union: "(\<Union>c\<in>C. B \<times> {c}) = B \<times> C" by blast
  have split:
    "upper.vadd.fincomp g (B \<times> C) =
      upper.vadd.fincomp (\<lambda>c. upper.vadd.fincomp g (B \<times> {c})) C"
    using upper.vadd.fincomp_UN_disjoint[OF finC _ disjoint, of g] finB gE union
    by auto
  have slice: "upper.vadd.fincomp g (B \<times> {c}) =
      upper.vadd.fincomp (\<lambda>b. g (b,c)) B" if c: "c \<in> C" for c
  proof -
    have image: "(\<lambda>b. (b,c)) ` B = B \<times> {c}" by auto
    have valid: "g \<in> ((\<lambda>b. (b,c)) ` B) \<rightarrow> E"
      using gE c by auto
    have injective: "inj_on (\<lambda>b. (b,c)) B" by (auto simp: inj_on_def)
    show ?thesis using upper.vadd.fincomp_reindex[OF valid injective] image by simp
  qed
  show ?thesis using split slice
    by (intro trans[OF split] upper.vadd.fincomp_cong')
      (auto intro: upper.vadd.fincomp_closed gE)
qed

lemma product_lincomb_nested:
  assumes B: "lower.basis B" and C: "upper.basis C"
    and fK: "\<And>v. v \<in> product_basis B C \<Longrightarrow> f v \<in> K"
  shows "direct.lincomb f (product_basis B C) =
    upper.lincomb (\<lambda>c. lower.lincomb (\<lambda>b. f (scale b c)) B) C"
proof -
  have finB: "finite B" and BF: "B \<subseteq> F"
    using B by (auto simp: lower.basis_def)
  have finC: "finite C" and CE: "C \<subseteq> E"
    using C by (auto simp: upper.basis_def)
  have PE: "product_basis B C \<subseteq> E" by (rule product_basis_subset[OF BF CE])
  have fk: "f (scale b c) \<in> K" if b: "b \<in> B" and c: "c \<in> C" for b c
  proof (rule fK)
    show "scale b c \<in> product_basis B C" using b c by (auto simp: product_basis_def)
  qed
  have terms: "(\<lambda>v. scale (f v) v) \<in> product_basis B C \<rightarrow> E"
    using PE fK base_subset by (auto intro: upper.scale_closed)
  have inj: "inj_on (\<lambda>(b,c). scale b c) (B \<times> C)"
    by (rule product_basis_injective[OF B C])
  have reindex: "upper.vadd.fincomp (\<lambda>v. scale (f v) v) (product_basis B C) =
      upper.vadd.fincomp (\<lambda>(b,c). scale (f (scale b c)) (scale b c)) (B \<times> C)"
    using upper.vadd.fincomp_reindex[OF terms[unfolded product_basis_def] inj]
    by (simp only: product_basis_def case_prod_unfold)
  have pairE: "scale (f (scale b c)) (scale b c) \<in> E"
    if "b \<in> B" "c \<in> C" for b c
    using BF CE base_subset fk[OF that] that by (auto intro: upper.scale_closed)
  have cart:
    "upper.vadd.fincomp (\<lambda>(b,c). scale (f (scale b c)) (scale b c)) (B \<times> C) =
      upper.vadd.fincomp (\<lambda>c. upper.vadd.fincomp
        (\<lambda>b. scale (f (scale b c)) (scale b c)) B) C"
  proof -
    have pairE': "(\<lambda>(b,c). scale (f (scale b c)) (scale b c)) (b,c) \<in> E"
      if "b \<in> B" "c \<in> C" for b c
      using pairE[OF that] by simp
    note result = vector_fincomp_cartesian[where g="\<lambda>(b,c). scale (f (scale b c)) (scale b c)",
        OF finB finC pairE']
    show ?thesis using result by simp
  qed
  have inner:
    "upper.vadd.fincomp (\<lambda>b. scale (f (scale b c)) (scale b c)) B =
      scale (lower.lincomb (\<lambda>b. f (scale b c)) B) c"
    if c: "c \<in> C" for c
  proof -
    have cE: "c \<in> E" using CE c by blast
    have rightE: "(\<lambda>b. scale (smult (f (scale b c)) b) c) \<in> B \<rightarrow> E"
    proof
      fix b assume b: "b \<in> B"
      have bF: "b \<in> F" using BF b by blast
      have "smult (f (scale b c)) b \<in> F"
        by (rule lower.scale_closed[OF fk[OF b c] bF])
      then show "scale (smult (f (scale b c)) b) c \<in> E"
        by (rule upper.scale_closed[OF _ cE])
    qed
    have equal:
      "upper.vadd.fincomp (\<lambda>b. scale (f (scale b c)) (scale b c)) B =
       upper.vadd.fincomp (\<lambda>b. scale (smult (f (scale b c)) b) c) B"
    proof (rule upper.vadd.fincomp_cong'[OF refl rightE])
      fix b assume b: "b \<in> B"
      have fbF: "f (scale b c) \<in> F" using fk[OF b c] base_subset by blast
      have bF: "b \<in> F" using BF b by blast
      show "scale (f (scale b c)) (scale b c) = scale (smult (f (scale b c)) b) c"
        by (rule upper.scale_scale[OF fbF bF cE, symmetric])
    qed
    show ?thesis using equal scale_lower_lincomb[OF BF cE, of "\<lambda>b. f (scale b c)"] fk c
      by simp
  qed
  have dF: "lower.lincomb (\<lambda>b. f (scale b c)) B \<in> F" if "c \<in> C" for c
    by (rule lower.lincomb_closed[OF BF]) (use fk that in auto)
  have outer:
    "upper.vadd.fincomp (\<lambda>c. upper.vadd.fincomp
        (\<lambda>b. scale (f (scale b c)) (scale b c)) B) C =
      upper.vadd.fincomp (\<lambda>c. scale (lower.lincomb (\<lambda>b. f (scale b c)) B) c) C"
    by (rule upper.vadd.fincomp_cong'[OF refl])
      (use dF CE inner in \<open>auto intro: upper.scale_closed\<close>)
  have whole:
    "upper.vadd.fincomp (\<lambda>v. scale (f v) v) (product_basis B C) =
     upper.vadd.fincomp (\<lambda>c. scale (lower.lincomb (\<lambda>b. f (scale b c)) B) c) C"
    by (rule trans[OF reindex], rule trans[OF cart outer])
  show ?thesis
    unfolding direct.lincomb_def upper.lincomb_def by (rule whole)
qed

lemma product_basis_independent:
  assumes B: "lower.basis B" and C: "upper.basis C"
  shows "direct.lin_indep (product_basis B C)"
proof -
  have finB: "finite B" and BF: "B \<subseteq> F"
    using B by (auto simp: lower.basis_def)
  have finC: "finite C" and CE: "C \<subseteq> E"
    using C by (auto simp: upper.basis_def)
  have PE: "product_basis B C \<subseteq> E" by (rule product_basis_subset[OF BF CE])
  have finP: "finite (product_basis B C)" by (rule product_basis_finite[OF finB finC])
  have lower_ind: "lower.lin_indep B" by (rule lower.basis_lin_indep[OF B])
  have upper_ind: "upper.lin_indep C" by (rule upper.basis_lin_indep[OF C])
  have zero_coeff:
    "\<forall>v\<in>product_basis B C. f v = szero"
    if f: "f \<in> product_basis B C \<rightarrow>\<^sub>E K"
      and zero: "direct.lincomb f (product_basis B C) = vzero" for f
  proof -
    define d where "d c = lower.lincomb (\<lambda>b. f (scale b c)) B" for c
    have fk: "f (scale b c) \<in> K" if b: "b \<in> B" and c: "c \<in> C" for b c
      using f b c by (auto simp: product_basis_def)
    have dF: "d c \<in> F" if c: "c \<in> C" for c
      unfolding d_def by (rule lower.lincomb_closed[OF BF]) (use fk c in auto)
    have dPi: "restrict d C \<in> C \<rightarrow>\<^sub>E F" using dF by auto
    have fkp: "\<And>v. v \<in> product_basis B C \<Longrightarrow> f v \<in> K"
      using f by auto
    have nested: "direct.lincomb f (product_basis B C) =
        upper.lincomb (\<lambda>c. lower.lincomb (\<lambda>b. f (scale b c)) B) C"
      by (rule product_lincomb_nested[OF B C fkp])
    have d_eq: "d = (\<lambda>c. lower.lincomb (\<lambda>b. f (scale b c)) B)"
      by (rule ext) (simp only: d_def)
    have combine: "upper.lincomb d C = vzero"
      using nested zero by (simp only: d_eq)
    have combine_restrict: "upper.lincomb (restrict d C) C = vzero"
    proof -
      have "upper.lincomb (restrict d C) C = upper.lincomb d C"
        by (rule upper.lincomb_cong[OF CE]) (use dF in auto)
      then show ?thesis using combine by simp
    qed
    have dzero: "d c = szero" if c: "c \<in> C" for c
    proof -
      have "restrict d C c = szero"
        using upper_ind dPi combine_restrict c unfolding upper.lin_indep_def by blast
      then show ?thesis using c by simp
    qed
    have fzero: "f (scale b c) = szero" if b: "b \<in> B" and c: "c \<in> C" for b c
    proof -
      define h where "h = (\<lambda>b. f (scale b c))"
      have hK: "\<And>b. b \<in> B \<Longrightarrow> h b \<in> K"
        using fk c by (simp add: h_def)
      have hPi: "restrict h B \<in> B \<rightarrow>\<^sub>E K" using hK by auto
      have comb0: "lower.lincomb (restrict h B) B = szero"
      proof -
        have "lower.lincomb (restrict h B) B = lower.lincomb h B"
          by (rule lower.lincomb_cong[OF BF]) (use hK in auto)
        then show ?thesis using dzero[OF c] by (simp add: d_def h_def)
      qed
      have "restrict h B b = szero"
        using lower_ind hPi comb0 b unfolding lower.lin_indep_def by blast
      then show ?thesis using b by (simp add: h_def)
    qed
    show ?thesis using fzero by (auto simp: product_basis_def)
  qed
  show ?thesis unfolding direct.lin_indep_def using finP PE zero_coeff by blast
qed

theorem product_basis:
  assumes B: "lower.basis B" and C: "upper.basis C"
  shows "direct.basis (product_basis B C)"
proof (rule direct.basisI)
  show "direct.spanning (product_basis B C)"
    by (rule product_basis_spanning[OF B C])
  show "direct.lin_indep (product_basis B C)"
    by (rule product_basis_independent[OF B C])
qed

lemma product_basis_in_direct_span:
  assumes B: "lower.basis B" and C: "upper.basis C"
    and b: "b \<in> B" and c: "c \<in> C"
  shows "scale b c \<in> direct.span (product_basis B C)"
proof -
  have BF: "B \<subseteq> F" and CE: "C \<subseteq> E"
    using B C by (auto simp: lower.basis_def upper.basis_def)
  have "scale b c \<in> product_basis B C"
    using b c by (auto simp: product_basis_def)
  then show ?thesis
    by (rule direct.span_incl[OF product_basis_subset[OF BF CE]])
qed

text \<open>Cardinality uniqueness turns a product basis into the dimension
formula.\<close>

lemma dimension_from_product_basis:
  assumes B: "lower.basis B" and C: "upper.basis C"
    and P: "direct.basis (product_basis B C)"
    and inj: "inj_on (\<lambda>(b,c). scale b c) (B \<times> C)"
  shows "direct.dimension = lower.dimension * upper.dimension"
proof -
  have cardP: "card (product_basis B C) = card B * card C"
    unfolding product_basis_def
    by (simp add: card_image[OF inj] card_cartesian_product)
  have "direct.dimension = card (product_basis B C)"
    by (rule direct.dimension_eq_any_field[OF P])
  also have "\<dots> = card B * card C" by (rule cardP)
  also have "\<dots> = lower.dimension * upper.dimension"
    using lower.dimension_eq_any_field[OF B] upper.dimension_eq_any_field[OF C]
    by simp
  finally show ?thesis .
qed

theorem finite_dimension_tower:
  assumes lower_finite: "\<exists>B. lower.basis B"
    and upper_finite: "\<exists>C. upper.basis C"
  shows "\<exists>P. direct.basis P"
    and "direct.dimension = lower.dimension * upper.dimension"
proof -
  obtain B where B: "lower.basis B" using lower_finite by blast
  obtain C where C: "upper.basis C" using upper_finite by blast
  have P: "direct.basis (product_basis B C)" by (rule product_basis[OF B C])
  show "\<exists>P. direct.basis P" using P by blast
  show "direct.dimension = lower.dimension * upper.dimension"
    by (rule dimension_from_product_basis[OF B C P product_basis_injective[OF B C]])
qed

text \<open>The zero space has an empty basis over either field.  This case
must not be excluded by an index type or by requiring the upper carrier to be
a field.\<close>

lemma zero_space_tower:
  assumes "E = {vzero}"
  shows "direct.basis {}" "upper.basis {}"
    and "direct.dimension = lower.dimension * upper.dimension"
proof -
  show D: "direct.basis {}" by (rule direct.basis_empty_trivial[OF assms])
  show U: "upper.basis {}" by (rule upper.basis_empty_trivial[OF assms])
  have "direct.dimension = 0"
    using direct.dimension_eq_any_field[OF D] by simp
  moreover have "upper.dimension = 0"
    using upper.dimension_eq_any_field[OF U] by simp
  ultimately show "direct.dimension = lower.dimension * upper.dimension" by simp
qed

end

end
