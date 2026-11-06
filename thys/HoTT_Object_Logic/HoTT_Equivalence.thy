theory HoTT_Equivalence
  imports HoTT_Identity
begin

section \<open>Contractibility and fibers\<close>

definition contractible :: "expr \<Rightarrow> expr" where
  "contractible A \<equiv>
    sigma_type A
      (\<lambda>center. pi_type A
        (\<lambda>x. identity_type A center x))"

lemma contractible_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
  shows "contractible A \<Colon>\<^sub>h universe i"
  unfolding contractible_def
proof (rule sigma_form[OF A])
  fix center
  assume center: "center \<Colon>\<^sub>h A"
  show "pi_type A (\<lambda>x. identity_type A center x) \<Colon>\<^sub>h universe i"
  proof (rule pi_form[OF A])
    fix x
    assume x: "x \<Colon>\<^sub>h A"
    show "identity_type A center x \<Colon>\<^sub>h universe i"
      by (rule identity_form[OF A center x])
  qed
qed

definition fiber ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "fiber A B f b \<equiv>
    sigma_type A (\<lambda>a. identity_type B (app f a) b)"

lemma fiber_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and b: "b \<Colon>\<^sub>h B"
  shows "fiber A B f b \<Colon>\<^sub>h universe i"
  unfolding fiber_def
proof (rule sigma_form[OF A])
  fix a
  assume a: "a \<Colon>\<^sub>h A"
  have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
  show "identity_type B (app f a) b \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fa b])
qed

definition contractible_map ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "contractible_map A B f \<equiv>
    pi_type B (\<lambda>b. contractible (fiber A B f b))"

lemma contractible_map_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
  shows "contractible_map A B f \<Colon>\<^sub>h universe i"
  unfolding contractible_map_def
proof (rule pi_form[OF B])
  fix b
  assume b: "b \<Colon>\<^sub>h B"
  have fib: "fiber A B f b \<Colon>\<^sub>h universe i"
    by (rule fiber_form[OF A B f b])
  show "contractible (fiber A B f b) \<Colon>\<^sub>h universe i"
    by (rule contractible_form[OF fib])
qed

section \<open>Bi-invertible maps and equivalences\<close>

definition left_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "left_inverse A B f \<equiv>
    sigma_type (arrow B A)
      (\<lambda>g. homotopy A (\<lambda>_. A)
        (compose A B A g f) (identity_function A))"

definition right_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "right_inverse A B f \<equiv>
    sigma_type (arrow B A)
      (\<lambda>g. homotopy B (\<lambda>_. B)
        (compose B A B f g) (identity_function B))"

definition biinvertible ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "biinvertible A B f \<equiv>
    product (left_inverse A B f) (right_inverse A B f)"

definition equivalence :: "expr \<Rightarrow> expr \<Rightarrow> expr" where
  "equivalence A B \<equiv>
    sigma_type (arrow A B) (\<lambda>f. biinvertible A B f)"

lemma nondependent_homotopy_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow A B"
  shows "homotopy A (\<lambda>_. B) f g \<Colon>\<^sub>h universe i"
proof (rule homotopy_form[OF A])
  fix x
  assume "x \<Colon>\<^sub>h A"
  show "B \<Colon>\<^sub>h universe i" by (rule B)
next
  show "f \<Colon>\<^sub>h pi_type A (\<lambda>_. B)"
    using f unfolding arrow_def .
next
  show "g \<Colon>\<^sub>h pi_type A (\<lambda>_. B)"
    using g unfolding arrow_def .
qed

lemma nondependent_homotopy_refl_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
  shows "homotopy_refl A (\<lambda>_. B) f \<Colon>\<^sub>h
    homotopy A (\<lambda>_. B) f f"
proof (rule homotopy_refl_type[OF A])
  fix x
  assume "x \<Colon>\<^sub>h A"
  show "B \<Colon>\<^sub>h universe i" by (rule B)
next
  show "f \<Colon>\<^sub>h pi_type A (\<lambda>_. B)"
    using f unfolding arrow_def .
qed

lemma left_inverse_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
  shows "left_inverse A B f \<Colon>\<^sub>h universe i"
  unfolding left_inverse_def
proof (rule sigma_form)
  show "arrow B A \<Colon>\<^sub>h universe i"
    by (rule arrow_form[OF B A])
next
  fix g
  assume g: "g \<Colon>\<^sub>h arrow B A"
  have gf: "compose A B A g f \<Colon>\<^sub>h arrow A A"
    by (rule compose_type[OF A f g])
  have id: "identity_function A \<Colon>\<^sub>h arrow A A"
    by (rule identity_function_type[OF A])
  show "homotopy A (\<lambda>_. A) (compose A B A g f)
      (identity_function A) \<Colon>\<^sub>h universe i"
    by (rule nondependent_homotopy_form[OF A A gf id])
qed

lemma right_inverse_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
  shows "right_inverse A B f \<Colon>\<^sub>h universe i"
  unfolding right_inverse_def
proof (rule sigma_form)
  show "arrow B A \<Colon>\<^sub>h universe i"
    by (rule arrow_form[OF B A])
next
  fix g
  assume g: "g \<Colon>\<^sub>h arrow B A"
  have fg: "compose B A B f g \<Colon>\<^sub>h arrow B B"
    by (rule compose_type[OF B g f])
  have id: "identity_function B \<Colon>\<^sub>h arrow B B"
    by (rule identity_function_type[OF B])
  show "homotopy B (\<lambda>_. B) (compose B A B f g)
      (identity_function B) \<Colon>\<^sub>h universe i"
    by (rule nondependent_homotopy_form[OF B B fg id])
qed

lemma biinvertible_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
  shows "biinvertible A B f \<Colon>\<^sub>h universe i"
  unfolding biinvertible_def
  by (rule product_form[OF left_inverse_form[OF A B f]
        right_inverse_form[OF A B f]])

lemma equivalence_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
  shows "equivalence A B \<Colon>\<^sub>h universe i"
  unfolding equivalence_def
proof (rule sigma_form)
  show "arrow A B \<Colon>\<^sub>h universe i"
    by (rule arrow_form[OF A B])
next
  fix f
  assume f: "f \<Colon>\<^sub>h arrow A B"
  show "biinvertible A B f \<Colon>\<^sub>h universe i"
    by (rule biinvertible_form[OF A B f])
qed

lemma equivalence_intro:
  assumes f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "pair f w \<Colon>\<^sub>h equivalence A B"
  unfolding equivalence_def
proof (rule sigma_intro)
  show "f \<Colon>\<^sub>h arrow A B" by (rule f)
next
  show "w \<Colon>\<^sub>h biinvertible A B f" by (rule w)
qed

section \<open>The identity equivalence\<close>

lemma compose_identity_self [simp]:
  "compose A A A (identity_function A) (identity_function A) \<equiv>
    identity_function A"
  unfolding compose_def identity_function_def by simp

definition identity_biinvertible :: "expr \<Rightarrow> expr" where
  "identity_biinvertible A \<equiv>
    pair
      (pair (identity_function A)
        (homotopy_refl A (\<lambda>_. A) (identity_function A)))
      (pair (identity_function A)
        (homotopy_refl A (\<lambda>_. A) (identity_function A)))"

lemma identity_biinvertible_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
  shows "identity_biinvertible A \<Colon>\<^sub>h
    biinvertible A A (identity_function A)"
proof -
  have id: "identity_function A \<Colon>\<^sub>h arrow A A"
    by (rule identity_function_type[OF A])
  have H: "homotopy_refl A (\<lambda>_. A) (identity_function A)
      \<Colon>\<^sub>h homotopy A (\<lambda>_. A)
        (identity_function A) (identity_function A)"
    by (rule nondependent_homotopy_refl_type[OF A A id])
  have Hcomp: "homotopy_refl A (\<lambda>_. A) (identity_function A)
      \<Colon>\<^sub>h homotopy A (\<lambda>_. A)
        (compose A A A (identity_function A) (identity_function A))
        (identity_function A)"
    using H by simp
  have left: "pair (identity_function A)
      (homotopy_refl A (\<lambda>_. A) (identity_function A))
      \<Colon>\<^sub>h left_inverse A A (identity_function A)"
    unfolding left_inverse_def
  proof (rule sigma_intro)
    show "identity_function A \<Colon>\<^sub>h arrow A A" by (rule id)
  next
    show "homotopy_refl A (\<lambda>_. A) (identity_function A) \<Colon>\<^sub>h
        homotopy A (\<lambda>_. A)
          (compose A A A (identity_function A) (identity_function A))
          (identity_function A)"
      by (rule Hcomp)
  qed
  have right: "pair (identity_function A)
      (homotopy_refl A (\<lambda>_. A) (identity_function A))
      \<Colon>\<^sub>h right_inverse A A (identity_function A)"
    unfolding right_inverse_def
  proof (rule sigma_intro)
    show "identity_function A \<Colon>\<^sub>h arrow A A" by (rule id)
  next
    show "homotopy_refl A (\<lambda>_. A) (identity_function A) \<Colon>\<^sub>h
        homotopy A (\<lambda>_. A)
          (compose A A A (identity_function A) (identity_function A))
          (identity_function A)"
      by (rule Hcomp)
  qed
  show "identity_biinvertible A \<Colon>\<^sub>h
      biinvertible A A (identity_function A)"
    unfolding identity_biinvertible_def biinvertible_def
    by (rule product_intro[OF left right])
qed

definition identity_equivalence :: "expr \<Rightarrow> expr" where
  "identity_equivalence A \<equiv>
    pair (identity_function A) (identity_biinvertible A)"

theorem identity_equivalence_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
  shows "identity_equivalence A \<Colon>\<^sub>h equivalence A A"
  unfolding identity_equivalence_def equivalence_def
proof (rule sigma_intro)
  show "identity_function A \<Colon>\<^sub>h arrow A A"
    by (rule identity_function_type[OF A])
next
  show "identity_biinvertible A \<Colon>\<^sub>h
      biinvertible A A (identity_function A)"
    by (rule identity_biinvertible_type[OF A])
qed

section \<open>Composition of equivalences\<close>

definition left_inverse_function ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "left_inverse_function A B f w \<equiv> first (first w)"

definition left_inverse_homotopy ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "left_inverse_homotopy A B f w \<equiv> second (first w)"

definition right_inverse_function ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "right_inverse_function A B f w \<equiv> first (second w)"

definition right_inverse_homotopy ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "right_inverse_homotopy A B f w \<equiv> second (second w)"

lemma left_inverse_component_type:
  assumes w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "first w \<Colon>\<^sub>h left_inverse A B f"
  using w unfolding biinvertible_def by (rule product_first)

lemma right_inverse_component_type:
  assumes w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "second w \<Colon>\<^sub>h right_inverse A B f"
  using w unfolding biinvertible_def by (rule product_second)

lemma left_inverse_function_type:
  assumes w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
proof -
  have L: "first w \<Colon>\<^sub>h left_inverse A B f"
    by (rule left_inverse_component_type[OF w])
  show "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    unfolding left_inverse_function_def
    using L unfolding left_inverse_def by (rule sigma_first)
qed

lemma left_inverse_homotopy_type:
  assumes w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "left_inverse_homotopy A B f w \<Colon>\<^sub>h
    homotopy A (\<lambda>_. A)
      (compose A B A (left_inverse_function A B f w) f)
      (identity_function A)"
proof -
  have L: "first w \<Colon>\<^sub>h left_inverse A B f"
    by (rule left_inverse_component_type[OF w])
  show "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f w) f)
        (identity_function A)"
    unfolding left_inverse_homotopy_def left_inverse_function_def
    using L unfolding left_inverse_def by (rule sigma_second)
qed

lemma right_inverse_function_type:
  assumes w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "right_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
proof -
  have R: "second w \<Colon>\<^sub>h right_inverse A B f"
    by (rule right_inverse_component_type[OF w])
  show "right_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    unfolding right_inverse_function_def
    using R unfolding right_inverse_def by (rule sigma_first)
qed

lemma right_inverse_homotopy_type:
  assumes w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "right_inverse_homotopy A B f w \<Colon>\<^sub>h
    homotopy B (\<lambda>_. B)
      (compose B A B f (right_inverse_function A B f w))
      (identity_function B)"
proof -
  have R: "second w \<Colon>\<^sub>h right_inverse A B f"
    by (rule right_inverse_component_type[OF w])
  show "right_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy B (\<lambda>_. B)
        (compose B A B f (right_inverse_function A B f w))
        (identity_function B)"
    unfolding right_inverse_homotopy_def right_inverse_function_def
    using R unfolding right_inverse_def by (rule sigma_second)
qed

definition composite_left_inverse_function ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "composite_left_inverse_function A B C f g wf wg \<equiv>
    compose C B A
      (left_inverse_function A B f wf)
      (left_inverse_function B C g wg)"

lemma composite_left_inverse_function_type:
  assumes C: "C \<Colon>\<^sub>h universe i"
    and wf: "wf \<Colon>\<^sub>h biinvertible A B f"
    and wg: "wg \<Colon>\<^sub>h biinvertible B C g"
  shows "composite_left_inverse_function A B C f g wf wg
    \<Colon>\<^sub>h arrow C A"
  unfolding composite_left_inverse_function_def
  by (rule compose_type[OF C
        left_inverse_function_type[OF wg]
        left_inverse_function_type[OF wf]])

definition composite_left_homotopy ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "composite_left_homotopy A B C f g wf wg \<equiv>
    lambda A (\<lambda>x.
      path_concat A
        (app (left_inverse_function A B f wf)
          (app (left_inverse_function B C g wg) (app g (app f x))))
        (app (left_inverse_function A B f wf) (app f x))
        x
        (ap B A (left_inverse_function A B f wf)
          (app (left_inverse_function B C g wg) (app g (app f x)))
          (app f x)
          (app (left_inverse_homotopy B C g wg) (app f x)))
        (app (left_inverse_homotopy A B f wf) x))"

lemma composite_left_homotopy_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and C: "C \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow B C"
    and wf: "wf \<Colon>\<^sub>h biinvertible A B f"
    and wg: "wg \<Colon>\<^sub>h biinvertible B C g"
  shows "composite_left_homotopy A B C f g wf wg \<Colon>\<^sub>h
    homotopy A (\<lambda>_. A)
      (compose A C A
        (composite_left_inverse_function A B C f g wf wg)
        (compose A B C g f))
      (identity_function A)"
  unfolding composite_left_homotopy_def homotopy_def
    composite_left_inverse_function_def
proof (rule pi_intro[OF A])
  fix x
  assume x: "x \<Colon>\<^sub>h A"
  have fx: "app f x \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f x])
  have gfx: "app g (app f x) \<Colon>\<^sub>h C"
    by (rule arrow_elim[OF g fx])
  have lf: "left_inverse_function A B f wf \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF wf])
  have lg: "left_inverse_function B C g wg \<Colon>\<^sub>h arrow C B"
    by (rule left_inverse_function_type[OF wg])
  have lg_gfx: "app (left_inverse_function B C g wg) (app g (app f x))
      \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF lg gfx])
  have lf_lg_gfx: "app (left_inverse_function A B f wf)
      (app (left_inverse_function B C g wg) (app g (app f x)))
      \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF lf lg_gfx])
  have lf_fx: "app (left_inverse_function A B f wf) (app f x)
      \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF lf fx])
  have Lg: "left_inverse_homotopy B C g wg \<Colon>\<^sub>h
      homotopy B (\<lambda>_. B)
        (compose B C B (left_inverse_function B C g wg) g)
        (identity_function B)"
    by (rule left_inverse_homotopy_type[OF wg])
  have Lg_pi: "left_inverse_homotopy B C g wg \<Colon>\<^sub>h
      pi_type B
        (\<lambda>u. identity_type B
          (app (compose B C B (left_inverse_function B C g wg) g) u)
          (app (identity_function B) u))"
    using Lg unfolding homotopy_def .
  have Lg_x_raw: "app (left_inverse_homotopy B C g wg) (app f x)
      \<Colon>\<^sub>h identity_type B
        (app (compose B C B (left_inverse_function B C g wg) g) (app f x))
        (app (identity_function B) (app f x))"
    by (rule pi_elim[OF Lg_pi fx])
  have Lg_x: "app (left_inverse_homotopy B C g wg) (app f x)
      \<Colon>\<^sub>h identity_type B
        (app (left_inverse_function B C g wg) (app g (app f x)))
        (app f x)"
    using Lg_x_raw by simp
  have step_one: "ap B A (left_inverse_function A B f wf)
      (app (left_inverse_function B C g wg) (app g (app f x)))
      (app f x)
      (app (left_inverse_homotopy B C g wg) (app f x))
      \<Colon>\<^sub>h identity_type A
        (app (left_inverse_function A B f wf)
          (app (left_inverse_function B C g wg) (app g (app f x))))
        (app (left_inverse_function A B f wf) (app f x))"
    by (rule ap_type[OF B A lf lg_gfx fx Lg_x])
  have Lf: "left_inverse_homotopy A B f wf \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f wf) f)
        (identity_function A)"
    by (rule left_inverse_homotopy_type[OF wf])
  have Lf_pi: "left_inverse_homotopy A B f wf \<Colon>\<^sub>h
      pi_type A
        (\<lambda>u. identity_type A
          (app (compose A B A (left_inverse_function A B f wf) f) u)
          (app (identity_function A) u))"
    using Lf unfolding homotopy_def .
  have Lf_x_raw: "app (left_inverse_homotopy A B f wf) x
      \<Colon>\<^sub>h identity_type A
        (app (compose A B A (left_inverse_function A B f wf) f) x)
        (app (identity_function A) x)"
    by (rule pi_elim[OF Lf_pi x])
  have Lf_x: "app (left_inverse_homotopy A B f wf) x
      \<Colon>\<^sub>h identity_type A
        (app (left_inverse_function A B f wf) (app f x)) x"
    using Lf_x_raw by simp
  have composed: "path_concat A
      (app (left_inverse_function A B f wf)
        (app (left_inverse_function B C g wg) (app g (app f x))))
      (app (left_inverse_function A B f wf) (app f x))
      x
      (ap B A (left_inverse_function A B f wf)
        (app (left_inverse_function B C g wg) (app g (app f x)))
        (app f x)
        (app (left_inverse_homotopy B C g wg) (app f x)))
      (app (left_inverse_homotopy A B f wf) x)
      \<Colon>\<^sub>h identity_type A
        (app (left_inverse_function A B f wf)
          (app (left_inverse_function B C g wg) (app g (app f x)))) x"
    by (rule path_concat_type[OF A lf_lg_gfx lf_fx x step_one Lf_x])
  show "path_concat A
      (app (left_inverse_function A B f wf)
        (app (left_inverse_function B C g wg) (app g (app f x))))
      (app (left_inverse_function A B f wf) (app f x)) x
      (ap B A (left_inverse_function A B f wf)
        (app (left_inverse_function B C g wg) (app g (app f x)))
        (app f x)
        (app (left_inverse_homotopy B C g wg) (app f x)))
      (app (left_inverse_homotopy A B f wf) x)
      \<Colon>\<^sub>h identity_type A
        (app
          (compose A C A
            (compose C B A
              (left_inverse_function A B f wf)
              (left_inverse_function B C g wg))
            (compose A B C g f)) x)
        (app (identity_function A) x)"
    using composed by simp
qed

definition composite_left_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "composite_left_inverse A B C f g wf wg \<equiv>
    pair
      (composite_left_inverse_function A B C f g wf wg)
      (composite_left_homotopy A B C f g wf wg)"

lemma composite_left_inverse_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and C: "C \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow B C"
    and wf: "wf \<Colon>\<^sub>h biinvertible A B f"
    and wg: "wg \<Colon>\<^sub>h biinvertible B C g"
  shows "composite_left_inverse A B C f g wf wg \<Colon>\<^sub>h
    left_inverse A C (compose A B C g f)"
  unfolding composite_left_inverse_def left_inverse_def
proof (rule sigma_intro)
  show "composite_left_inverse_function A B C f g wf wg \<Colon>\<^sub>h
      arrow C A"
    by (rule composite_left_inverse_function_type[OF C wf wg])
next
  show "composite_left_homotopy A B C f g wf wg \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A C A
          (composite_left_inverse_function A B C f g wf wg)
          (compose A B C g f))
        (identity_function A)"
    by (rule composite_left_homotopy_type[OF A B C f g wf wg])
qed

definition composite_right_inverse_function ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "composite_right_inverse_function A B C f g wf wg \<equiv>
    compose C B A
      (right_inverse_function A B f wf)
      (right_inverse_function B C g wg)"

lemma composite_right_inverse_function_type:
  assumes C: "C \<Colon>\<^sub>h universe i"
    and wf: "wf \<Colon>\<^sub>h biinvertible A B f"
    and wg: "wg \<Colon>\<^sub>h biinvertible B C g"
  shows "composite_right_inverse_function A B C f g wf wg
    \<Colon>\<^sub>h arrow C A"
  unfolding composite_right_inverse_function_def
  by (rule compose_type[OF C
        right_inverse_function_type[OF wg]
        right_inverse_function_type[OF wf]])

definition composite_right_homotopy ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "composite_right_homotopy A B C f g wf wg \<equiv>
    lambda C (\<lambda>z.
      path_concat C
        (app g (app f
          (app (right_inverse_function A B f wf)
            (app (right_inverse_function B C g wg) z))))
        (app g (app (right_inverse_function B C g wg) z))
        z
        (ap B C g
          (app f
            (app (right_inverse_function A B f wf)
              (app (right_inverse_function B C g wg) z)))
          (app (right_inverse_function B C g wg) z)
          (app (right_inverse_homotopy A B f wf)
            (app (right_inverse_function B C g wg) z)))
        (app (right_inverse_homotopy B C g wg) z))"

lemma composite_right_homotopy_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and C: "C \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow B C"
    and wf: "wf \<Colon>\<^sub>h biinvertible A B f"
    and wg: "wg \<Colon>\<^sub>h biinvertible B C g"
  shows "composite_right_homotopy A B C f g wf wg \<Colon>\<^sub>h
    homotopy C (\<lambda>_. C)
      (compose C A C (compose A B C g f)
        (composite_right_inverse_function A B C f g wf wg))
      (identity_function C)"
  unfolding composite_right_homotopy_def homotopy_def
    composite_right_inverse_function_def
proof (rule pi_intro[OF C])
  fix z
  assume z: "z \<Colon>\<^sub>h C"
  have rf: "right_inverse_function A B f wf \<Colon>\<^sub>h arrow B A"
    by (rule right_inverse_function_type[OF wf])
  have rg: "right_inverse_function B C g wg \<Colon>\<^sub>h arrow C B"
    by (rule right_inverse_function_type[OF wg])
  have rgz: "app (right_inverse_function B C g wg) z \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF rg z])
  have rf_rgz: "app (right_inverse_function A B f wf)
      (app (right_inverse_function B C g wg) z) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF rf rgz])
  have f_rf_rgz: "app f
      (app (right_inverse_function A B f wf)
        (app (right_inverse_function B C g wg) z)) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f rf_rgz])
  have g_f_rf_rgz: "app g (app f
      (app (right_inverse_function A B f wf)
        (app (right_inverse_function B C g wg) z))) \<Colon>\<^sub>h C"
    by (rule arrow_elim[OF g f_rf_rgz])
  have g_rgz: "app g (app (right_inverse_function B C g wg) z)
      \<Colon>\<^sub>h C"
    by (rule arrow_elim[OF g rgz])
  have Rf: "right_inverse_homotopy A B f wf \<Colon>\<^sub>h
      homotopy B (\<lambda>_. B)
        (compose B A B f (right_inverse_function A B f wf))
        (identity_function B)"
    by (rule right_inverse_homotopy_type[OF wf])
  have Rf_pi: "right_inverse_homotopy A B f wf \<Colon>\<^sub>h
      pi_type B
        (\<lambda>u. identity_type B
          (app (compose B A B f (right_inverse_function A B f wf)) u)
          (app (identity_function B) u))"
    using Rf unfolding homotopy_def .
  have Rf_z_raw: "app (right_inverse_homotopy A B f wf)
      (app (right_inverse_function B C g wg) z)
      \<Colon>\<^sub>h identity_type B
        (app (compose B A B f (right_inverse_function A B f wf))
          (app (right_inverse_function B C g wg) z))
        (app (identity_function B)
          (app (right_inverse_function B C g wg) z))"
    by (rule pi_elim[OF Rf_pi rgz])
  have Rf_z: "app (right_inverse_homotopy A B f wf)
      (app (right_inverse_function B C g wg) z)
      \<Colon>\<^sub>h identity_type B
        (app f (app (right_inverse_function A B f wf)
          (app (right_inverse_function B C g wg) z)))
        (app (right_inverse_function B C g wg) z)"
    using Rf_z_raw by simp
  have step_one: "ap B C g
      (app f (app (right_inverse_function A B f wf)
        (app (right_inverse_function B C g wg) z)))
      (app (right_inverse_function B C g wg) z)
      (app (right_inverse_homotopy A B f wf)
        (app (right_inverse_function B C g wg) z))
      \<Colon>\<^sub>h identity_type C
        (app g (app f (app (right_inverse_function A B f wf)
          (app (right_inverse_function B C g wg) z))))
        (app g (app (right_inverse_function B C g wg) z))"
    by (rule ap_type[OF B C g f_rf_rgz rgz Rf_z])
  have Rg: "right_inverse_homotopy B C g wg \<Colon>\<^sub>h
      homotopy C (\<lambda>_. C)
        (compose C B C g (right_inverse_function B C g wg))
        (identity_function C)"
    by (rule right_inverse_homotopy_type[OF wg])
  have Rg_pi: "right_inverse_homotopy B C g wg \<Colon>\<^sub>h
      pi_type C
        (\<lambda>u. identity_type C
          (app (compose C B C g (right_inverse_function B C g wg)) u)
          (app (identity_function C) u))"
    using Rg unfolding homotopy_def .
  have Rg_z_raw: "app (right_inverse_homotopy B C g wg) z
      \<Colon>\<^sub>h identity_type C
        (app (compose C B C g (right_inverse_function B C g wg)) z)
        (app (identity_function C) z)"
    by (rule pi_elim[OF Rg_pi z])
  have Rg_z: "app (right_inverse_homotopy B C g wg) z
      \<Colon>\<^sub>h identity_type C
        (app g (app (right_inverse_function B C g wg) z)) z"
    using Rg_z_raw by simp
  have composed: "path_concat C
      (app g (app f (app (right_inverse_function A B f wf)
        (app (right_inverse_function B C g wg) z))))
      (app g (app (right_inverse_function B C g wg) z)) z
      (ap B C g
        (app f (app (right_inverse_function A B f wf)
          (app (right_inverse_function B C g wg) z)))
        (app (right_inverse_function B C g wg) z)
        (app (right_inverse_homotopy A B f wf)
          (app (right_inverse_function B C g wg) z)))
      (app (right_inverse_homotopy B C g wg) z)
      \<Colon>\<^sub>h identity_type C
        (app g (app f (app (right_inverse_function A B f wf)
          (app (right_inverse_function B C g wg) z)))) z"
    by (rule path_concat_type[OF C g_f_rf_rgz g_rgz z step_one Rg_z])
  show "path_concat C
      (app g (app f (app (right_inverse_function A B f wf)
        (app (right_inverse_function B C g wg) z))))
      (app g (app (right_inverse_function B C g wg) z)) z
      (ap B C g
        (app f (app (right_inverse_function A B f wf)
          (app (right_inverse_function B C g wg) z)))
        (app (right_inverse_function B C g wg) z)
        (app (right_inverse_homotopy A B f wf)
          (app (right_inverse_function B C g wg) z)))
      (app (right_inverse_homotopy B C g wg) z)
      \<Colon>\<^sub>h identity_type C
        (app
          (compose C A C (compose A B C g f)
            (compose C B A
              (right_inverse_function A B f wf)
              (right_inverse_function B C g wg))) z)
        (app (identity_function C) z)"
    using composed by simp
qed

definition composite_right_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "composite_right_inverse A B C f g wf wg \<equiv>
    pair
      (composite_right_inverse_function A B C f g wf wg)
      (composite_right_homotopy A B C f g wf wg)"

lemma composite_right_inverse_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and C: "C \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow B C"
    and wf: "wf \<Colon>\<^sub>h biinvertible A B f"
    and wg: "wg \<Colon>\<^sub>h biinvertible B C g"
  shows "composite_right_inverse A B C f g wf wg \<Colon>\<^sub>h
    right_inverse A C (compose A B C g f)"
  unfolding composite_right_inverse_def right_inverse_def
proof (rule sigma_intro)
  show "composite_right_inverse_function A B C f g wf wg \<Colon>\<^sub>h
      arrow C A"
    by (rule composite_right_inverse_function_type[OF C wf wg])
next
  show "composite_right_homotopy A B C f g wf wg \<Colon>\<^sub>h
      homotopy C (\<lambda>_. C)
        (compose C A C (compose A B C g f)
          (composite_right_inverse_function A B C f g wf wg))
        (identity_function C)"
    by (rule composite_right_homotopy_type[OF A B C f g wf wg])
qed

definition compose_biinvertible ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "compose_biinvertible A B C f g wf wg \<equiv>
    pair
      (composite_left_inverse A B C f g wf wg)
      (composite_right_inverse A B C f g wf wg)"

lemma compose_biinvertible_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and C: "C \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow B C"
    and wf: "wf \<Colon>\<^sub>h biinvertible A B f"
    and wg: "wg \<Colon>\<^sub>h biinvertible B C g"
  shows "compose_biinvertible A B C f g wf wg \<Colon>\<^sub>h
    biinvertible A C (compose A B C g f)"
  unfolding compose_biinvertible_def biinvertible_def
  by (rule product_intro[OF
        composite_left_inverse_type[OF A B C f g wf wg]
        composite_right_inverse_type[OF A B C f g wf wg]])

definition compose_equivalence ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "compose_equivalence A B C e d \<equiv>
    pair
      (compose A B C (first d) (first e))
      (compose_biinvertible A B C
        (first e) (first d) (second e) (second d))"

theorem compose_equivalence_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and C: "C \<Colon>\<^sub>h universe i"
    and e: "e \<Colon>\<^sub>h equivalence A B"
    and d: "d \<Colon>\<^sub>h equivalence B C"
  shows "compose_equivalence A B C e d \<Colon>\<^sub>h equivalence A C"
proof -
  have ef: "first e \<Colon>\<^sub>h arrow A B"
    using e unfolding equivalence_def by (rule sigma_first)
  have ew: "second e \<Colon>\<^sub>h biinvertible A B (first e)"
    using e unfolding equivalence_def by (rule sigma_second)
  have df: "first d \<Colon>\<^sub>h arrow B C"
    using d unfolding equivalence_def by (rule sigma_first)
  have dw: "second d \<Colon>\<^sub>h biinvertible B C (first d)"
    using d unfolding equivalence_def by (rule sigma_second)
  have composite: "compose A B C (first d) (first e)
      \<Colon>\<^sub>h arrow A C"
    by (rule compose_type[OF A ef df])
  have witness: "compose_biinvertible A B C
      (first e) (first d) (second e) (second d)
      \<Colon>\<^sub>h biinvertible A C
        (compose A B C (first d) (first e))"
    by (rule compose_biinvertible_type[OF A B C ef df ew dw])
  show "compose_equivalence A B C e d \<Colon>\<^sub>h equivalence A C"
    unfolding compose_equivalence_def equivalence_def
    by (intro sigma_intro composite witness)
qed

end
