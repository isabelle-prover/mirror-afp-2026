theory HoTT_Equivalence_Inverse
  imports HoTT_Equivalence_Characterization
begin

section \<open>Bi-inverses from quasi-inverse data\<close>

text \<open>
  Bi-invertibility is a product of independent left and right inverse data.
  A quasi-inverse supplies both components at once: one map \<open>g\<close> is used
  twice, once with a retraction homotopy \<open>g \<circ> f \<sim> id\<close> and once with a
  section homotopy \<open>f \<circ> g \<sim> id\<close>.  This is the basic construction lemma
  for equivalence witnesses, dual to the extraction lemmas
  @{term left_inverse_function} and @{term right_inverse_function}.
\<close>

definition quasi_inverse_biinvertible ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "quasi_inverse_biinvertible A B f g eta rho \<equiv>
    pair (pair g eta) (pair g rho)"

lemma quasi_inverse_biinvertible_type:
  assumes g: "g \<Colon>\<^sub>h arrow B A"
    and eta: "eta \<Colon>\<^sub>h homotopy A (\<lambda>_. A)
      (compose A B A g f) (identity_function A)"
    and rho: "rho \<Colon>\<^sub>h homotopy B (\<lambda>_. B)
      (compose B A B f g) (identity_function B)"
  shows "quasi_inverse_biinvertible A B f g eta rho \<Colon>\<^sub>h
    biinvertible A B f"
  unfolding quasi_inverse_biinvertible_def biinvertible_def
proof (rule product_intro)
  show "pair g eta \<Colon>\<^sub>h left_inverse A B f"
    unfolding left_inverse_def
  proof (rule sigma_intro)
    show "g \<Colon>\<^sub>h arrow B A" by (rule g)
  next
    show "eta \<Colon>\<^sub>h homotopy A (\<lambda>_. A)
        (compose A B A g f) (identity_function A)"
      by (rule eta)
  qed
next
  show "pair g rho \<Colon>\<^sub>h right_inverse A B f"
    unfolding right_inverse_def
  proof (rule sigma_intro)
    show "g \<Colon>\<^sub>h arrow B A" by (rule g)
  next
    show "rho \<Colon>\<^sub>h homotopy B (\<lambda>_. B)
        (compose B A B f g) (identity_function B)"
      by (rule rho)
  qed
qed

definition quasi_inverse_equivalence ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "quasi_inverse_equivalence A B f g eta rho \<equiv>
    pair f (quasi_inverse_biinvertible A B f g eta rho)"

theorem quasi_inverse_equivalence_type:
  assumes f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow B A"
    and eta: "eta \<Colon>\<^sub>h homotopy A (\<lambda>_. A)
      (compose A B A g f) (identity_function A)"
    and rho: "rho \<Colon>\<^sub>h homotopy B (\<lambda>_. B)
      (compose B A B f g) (identity_function B)"
  shows "quasi_inverse_equivalence A B f g eta rho \<Colon>\<^sub>h
    equivalence A B"
  unfolding quasi_inverse_equivalence_def
  by (rule equivalence_intro[OF f
        quasi_inverse_biinvertible_type[OF g eta rho]])

section \<open>The selected inverse of a bi-invertible map\<close>

text \<open>
  Let \<open>f : A \<rightarrow> B\<close> be bi-invertible with witness \<open>w\<close>.  Its selected left
  inverse \<open>g\<close> already carries the retraction homotopy \<open>g \<circ> f \<sim> id\<^sub>A\<close>, and
  @{term quasi_rho} manufactures the section homotopy \<open>f \<circ> g \<sim> id\<^sub>B\<close> from the
  independent right inverse.  Reading that pair from the other side exhibits
  \<open>f\<close> as both a left and a right inverse of \<open>g\<close>, so \<open>g\<close> is bi-invertible.
\<close>

definition inverse_biinvertible ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "inverse_biinvertible A B f w \<equiv>
    quasi_inverse_biinvertible B A
      (left_inverse_function A B f w) f
      (quasi_rho A B f w)
      (left_inverse_homotopy A B f w)"

theorem inverse_biinvertible_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "inverse_biinvertible A B f w \<Colon>\<^sub>h
    biinvertible B A (left_inverse_function A B f w)"
  unfolding inverse_biinvertible_def
proof (rule quasi_inverse_biinvertible_type)
  show "f \<Colon>\<^sub>h arrow A B" by (rule f)
next
  show "quasi_rho A B f w \<Colon>\<^sub>h homotopy B (\<lambda>_. B)
      (compose B A B f (left_inverse_function A B f w))
      (identity_function B)"
    by (rule quasi_rho_type[OF A B f w])
next
  show "left_inverse_homotopy A B f w \<Colon>\<^sub>h homotopy A (\<lambda>_. A)
      (compose A B A (left_inverse_function A B f w) f)
      (identity_function A)"
    by (rule left_inverse_homotopy_type[OF w])
qed

definition inverse_contractible_map ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "inverse_contractible_map A B f w \<equiv>
    biinvertible_to_contractible_map B A
      (left_inverse_function A B f w)
      (inverse_biinvertible A B f w)"

corollary inverse_contractible_map_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "inverse_contractible_map A B f w \<Colon>\<^sub>h
    contractible_map B A (left_inverse_function A B f w)"
  unfolding inverse_contractible_map_def
  by (rule biinvertible_to_contractible_map_type[OF B A
        left_inverse_function_type[OF w]
        inverse_biinvertible_type[OF A B f w]])

section \<open>Inverting an equivalence\<close>

definition equivalence_inverse_function ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "equivalence_inverse_function A B e \<equiv>
    left_inverse_function A B
      (equivalence_function e) (equivalence_biinvertible e)"

lemma equivalence_inverse_function_type:
  assumes e: "e \<Colon>\<^sub>h equivalence A B"
  shows "equivalence_inverse_function A B e \<Colon>\<^sub>h arrow B A"
  unfolding equivalence_inverse_function_def
  by (rule left_inverse_function_type[OF equivalence_biinvertible_type[OF e]])

definition inverse_equivalence ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "inverse_equivalence A B e \<equiv>
    pair (equivalence_inverse_function A B e)
      (inverse_biinvertible A B
        (equivalence_function e) (equivalence_biinvertible e))"

theorem inverse_equivalence_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and e: "e \<Colon>\<^sub>h equivalence A B"
  shows "inverse_equivalence A B e \<Colon>\<^sub>h equivalence B A"
proof -
  have f: "equivalence_function e \<Colon>\<^sub>h arrow A B"
    by (rule equivalence_function_type[OF e])
  have w: "equivalence_biinvertible e \<Colon>\<^sub>h
      biinvertible A B (equivalence_function e)"
    by (rule equivalence_biinvertible_type[OF e])
  have g: "equivalence_inverse_function A B e \<Colon>\<^sub>h arrow B A"
    by (rule equivalence_inverse_function_type[OF e])
  have witness: "inverse_biinvertible A B
      (equivalence_function e) (equivalence_biinvertible e) \<Colon>\<^sub>h
      biinvertible B A (equivalence_inverse_function A B e)"
    unfolding equivalence_inverse_function_def
    by (rule inverse_biinvertible_type[OF A B f w])
  show "inverse_equivalence A B e \<Colon>\<^sub>h equivalence B A"
    unfolding inverse_equivalence_def
    by (rule equivalence_intro[OF g witness])
qed

section \<open>Contractibility transfers along an equivalence\<close>

text \<open>
  Combined with @{thm [source] equivalence_preserves_contractible_type}, the
  inverse equivalence transfers contractibility backwards, so contractibility
  is invariant in both directions.
\<close>

definition equivalence_reflects_contractible ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "equivalence_reflects_contractible A B e c \<equiv>
    equivalence_preserves_contractible B A (inverse_equivalence A B e) c"

theorem equivalence_reflects_contractible_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and e: "e \<Colon>\<^sub>h equivalence A B"
    and c: "c \<Colon>\<^sub>h contractible B"
  shows "equivalence_reflects_contractible A B e c \<Colon>\<^sub>h contractible A"
  unfolding equivalence_reflects_contractible_def
  by (rule equivalence_preserves_contractible_type[OF B A
        inverse_equivalence_type[OF A B e] c])

section \<open>Type equivalence is an equivalence relation\<close>

text \<open>
  The identity equivalence, the inverse equivalence, and the composite
  equivalence make @{term equivalence} reflexive, symmetric, and transitive
  on the types of a universe.  Every witness is an explicit object-language
  term, so the three closure properties are inhabitation results rather than
  meta-level assertions.
\<close>

corollary equivalence_relation_refl:
  assumes A: "A \<Colon>\<^sub>h universe i"
  shows "identity_equivalence A \<Colon>\<^sub>h equivalence A A"
  by (rule identity_equivalence_type[OF A])

corollary equivalence_relation_symm:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and e: "e \<Colon>\<^sub>h equivalence A B"
  shows "inverse_equivalence A B e \<Colon>\<^sub>h equivalence B A"
  by (rule inverse_equivalence_type[OF A B e])

corollary equivalence_relation_trans:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and C: "C \<Colon>\<^sub>h universe i"
    and e: "e \<Colon>\<^sub>h equivalence A B"
    and d: "d \<Colon>\<^sub>h equivalence B C"
  shows "compose_equivalence A B C e d \<Colon>\<^sub>h equivalence A C"
  by (rule compose_equivalence_type[OF A B C e d])

end
