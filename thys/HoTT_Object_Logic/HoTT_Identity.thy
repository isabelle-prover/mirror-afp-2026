theory HoTT_Identity
  imports HoTT_Type_Formers
begin

section \<open>Identity types and path induction\<close>

consts
  identity_type :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
  reflexivity :: "expr \<Rightarrow> expr \<Rightarrow> expr"
  identity_ind ::
    "expr \<Rightarrow> expr \<Rightarrow> (expr \<Rightarrow> expr \<Rightarrow> expr) \<Rightarrow>
      expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"

axiomatization where
  identity_form:
    "A \<Colon>\<^sub>h universe i \<Longrightarrow> x \<Colon>\<^sub>h A \<Longrightarrow> y \<Colon>\<^sub>h A \<Longrightarrow>
      identity_type A x y \<Colon>\<^sub>h universe i" and
  identity_intro:
    "A \<Colon>\<^sub>h universe i \<Longrightarrow> x \<Colon>\<^sub>h A \<Longrightarrow>
      reflexivity A x \<Colon>\<^sub>h identity_type A x x" and
  identity_elim:
    "A \<Colon>\<^sub>h universe i \<Longrightarrow> x \<Colon>\<^sub>h A \<Longrightarrow>
      (\<And>y p. y \<Colon>\<^sub>h A \<Longrightarrow> p \<Colon>\<^sub>h identity_type A x y \<Longrightarrow>
        C y p \<Colon>\<^sub>h universe j) \<Longrightarrow>
      d \<Colon>\<^sub>h C x (reflexivity A x) \<Longrightarrow>
      y \<Colon>\<^sub>h A \<Longrightarrow> p \<Colon>\<^sub>h identity_type A x y \<Longrightarrow>
      identity_ind A x C d y p \<Colon>\<^sub>h C y p" and
  identity_beta [simp]:
    "identity_ind A x C d x (reflexivity A x) \<equiv> d"

section \<open>Transport and elementary path operations\<close>

definition transport ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "transport A P x y p u \<equiv>
    identity_ind A x (\<lambda>y _. P y) u y p"

lemma transport_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and P: "\<And>w. w \<Colon>\<^sub>h A \<Longrightarrow> P w \<Colon>\<^sub>h universe j"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
    and u: "u \<Colon>\<^sub>h P x"
  shows "transport A P x y p u \<Colon>\<^sub>h P y"
  unfolding transport_def
proof (rule identity_elim[OF A x])
  fix w q
  assume "w \<Colon>\<^sub>h A"
  then show "P w \<Colon>\<^sub>h universe j" by (rule P)
next
  show "u \<Colon>\<^sub>h P x" by (rule u)
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

lemma transport_refl [simp]:
  "transport A P x x (reflexivity A x) u \<equiv> u"
  unfolding transport_def by simp

definition path_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_inverse A x y p \<equiv>
    identity_ind A x
      (\<lambda>y _. identity_type A y x)
      (reflexivity A x) y p"

lemma path_inverse_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "path_inverse A x y p \<Colon>\<^sub>h identity_type A y x"
  unfolding path_inverse_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume "q \<Colon>\<^sub>h identity_type A x w"
  show "identity_type A w x \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A w x])
next
  show "reflexivity A x \<Colon>\<^sub>h identity_type A x x"
    by (rule identity_intro[OF A x])
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

lemma path_inverse_refl [simp]:
  "path_inverse A x x (reflexivity A x) \<equiv> reflexivity A x"
  unfolding path_inverse_def by simp

definition path_concat ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_concat A x y z p q \<equiv>
    transport A (\<lambda>w. identity_type A x w) y z q p"

lemma path_concat_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and z: "z \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
    and q: "q \<Colon>\<^sub>h identity_type A y z"
  shows "path_concat A x y z p q \<Colon>\<^sub>h identity_type A x z"
  unfolding path_concat_def
proof (rule transport_type[OF A])
  fix w
  assume w: "w \<Colon>\<^sub>h A"
  show "identity_type A x w \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x w])
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "z \<Colon>\<^sub>h A" by (rule z)
next
  show "q \<Colon>\<^sub>h identity_type A y z" by (rule q)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

lemma path_concat_refl_right [simp]:
  "path_concat A x y y p (reflexivity A y) \<equiv> p"
  unfolding path_concat_def by simp

section \<open>Groupoid laws\<close>

definition path_right_unit ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_right_unit A x y p \<equiv>
    reflexivity (identity_type A x y) p"

lemma path_right_unit_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "path_right_unit A x y p \<Colon>\<^sub>h
    identity_type (identity_type A x y)
      (path_concat A x y y p (reflexivity A y)) p"
proof -
  have path_space: "identity_type A x y \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x y])
  have "reflexivity (identity_type A x y) p \<Colon>\<^sub>h
      identity_type (identity_type A x y) p p"
    by (rule identity_intro[OF path_space p])
  then show "path_right_unit A x y p \<Colon>\<^sub>h
      identity_type (identity_type A x y)
        (path_concat A x y y p (reflexivity A y)) p"
    unfolding path_right_unit_def
    by simp
qed

definition path_left_unit ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_left_unit A x y p \<equiv>
    identity_ind A x
      (\<lambda>y p. identity_type (identity_type A x y)
        (path_concat A x x y (reflexivity A x) p) p)
      (reflexivity (identity_type A x x) (reflexivity A x)) y p"

lemma path_left_unit_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "path_left_unit A x y p \<Colon>\<^sub>h
    identity_type (identity_type A x y)
      (path_concat A x x y (reflexivity A x) p) p"
  unfolding path_left_unit_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume q: "q \<Colon>\<^sub>h identity_type A x w"
  have path_space: "identity_type A x w \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x w])
  have composed: "path_concat A x x w (reflexivity A x) q
      \<Colon>\<^sub>h identity_type A x w"
    by (rule path_concat_type[OF A x x w identity_intro[OF A x] q])
  show "identity_type (identity_type A x w)
      (path_concat A x x w (reflexivity A x) q) q \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space composed q])
next
  have path_space: "identity_type A x x \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x x])
  have base: "reflexivity (identity_type A x x) (reflexivity A x)
      \<Colon>\<^sub>h identity_type (identity_type A x x)
        (reflexivity A x) (reflexivity A x)"
    by (rule identity_intro[OF path_space identity_intro[OF A x]])
  show "reflexivity (identity_type A x x) (reflexivity A x)
      \<Colon>\<^sub>h identity_type (identity_type A x x)
        (path_concat A x x x (reflexivity A x) (reflexivity A x))
        (reflexivity A x)"
    using base by simp
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

definition path_assoc ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_assoc A w x y z p q r \<equiv>
    identity_ind A y
      (\<lambda>z r. identity_type (identity_type A w z)
        (path_concat A w y z (path_concat A w x y p q) r)
        (path_concat A w x z p (path_concat A x y z q r)))
      (reflexivity (identity_type A w y) (path_concat A w x y p q))
      z r"

lemma path_assoc_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and w: "w \<Colon>\<^sub>h A"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and z: "z \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A w x"
    and q: "q \<Colon>\<^sub>h identity_type A x y"
    and r: "r \<Colon>\<^sub>h identity_type A y z"
  shows "path_assoc A w x y z p q r \<Colon>\<^sub>h
    identity_type (identity_type A w z)
      (path_concat A w y z (path_concat A w x y p q) r)
      (path_concat A w x z p (path_concat A x y z q r))"
  unfolding path_assoc_def
proof (rule identity_elim[OF A y])
  fix v s
  assume v: "v \<Colon>\<^sub>h A"
  assume s: "s \<Colon>\<^sub>h identity_type A y v"
  have pq: "path_concat A w x y p q \<Colon>\<^sub>h identity_type A w y"
    by (rule path_concat_type[OF A w x y p q])
  have lhs: "path_concat A w y v (path_concat A w x y p q) s
      \<Colon>\<^sub>h identity_type A w v"
    by (rule path_concat_type[OF A w y v pq s])
  have qr: "path_concat A x y v q s \<Colon>\<^sub>h identity_type A x v"
    by (rule path_concat_type[OF A x y v q s])
  have rhs: "path_concat A w x v p (path_concat A x y v q s)
      \<Colon>\<^sub>h identity_type A w v"
    by (rule path_concat_type[OF A w x v p qr])
  have path_space: "identity_type A w v \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A w v])
  show "identity_type (identity_type A w v)
      (path_concat A w y v (path_concat A w x y p q) s)
      (path_concat A w x v p (path_concat A x y v q s))
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space lhs rhs])
next
  have pq: "path_concat A w x y p q \<Colon>\<^sub>h identity_type A w y"
    by (rule path_concat_type[OF A w x y p q])
  have path_space: "identity_type A w y \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A w y])
  have base: "reflexivity (identity_type A w y) (path_concat A w x y p q)
      \<Colon>\<^sub>h identity_type (identity_type A w y)
        (path_concat A w x y p q) (path_concat A w x y p q)"
    by (rule identity_intro[OF path_space pq])
  show "reflexivity (identity_type A w y) (path_concat A w x y p q)
      \<Colon>\<^sub>h identity_type (identity_type A w y)
        (path_concat A w y y (path_concat A w x y p q) (reflexivity A y))
        (path_concat A w x y p
          (path_concat A x y y q (reflexivity A y)))"
    using base by simp
next
  show "z \<Colon>\<^sub>h A" by (rule z)
next
  show "r \<Colon>\<^sub>h identity_type A y z" by (rule r)
qed

definition path_inverse_right ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_inverse_right A x y p \<equiv>
    identity_ind A x
      (\<lambda>y p. identity_type (identity_type A x x)
        (path_concat A x y x p (path_inverse A x y p))
        (reflexivity A x))
      (reflexivity (identity_type A x x) (reflexivity A x)) y p"

lemma path_inverse_right_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "path_inverse_right A x y p \<Colon>\<^sub>h
    identity_type (identity_type A x x)
      (path_concat A x y x p (path_inverse A x y p))
      (reflexivity A x)"
  unfolding path_inverse_right_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume q: "q \<Colon>\<^sub>h identity_type A x w"
  have inv: "path_inverse A x w q \<Colon>\<^sub>h identity_type A w x"
    by (rule path_inverse_type[OF A x w q])
  have composed: "path_concat A x w x q (path_inverse A x w q)
      \<Colon>\<^sub>h identity_type A x x"
    by (rule path_concat_type[OF A x w x q inv])
  have path_space: "identity_type A x x \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x x])
  show "identity_type (identity_type A x x)
      (path_concat A x w x q (path_inverse A x w q))
      (reflexivity A x) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space composed identity_intro[OF A x]])
next
  have path_space: "identity_type A x x \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x x])
  have base: "reflexivity (identity_type A x x) (reflexivity A x)
      \<Colon>\<^sub>h identity_type (identity_type A x x)
        (reflexivity A x) (reflexivity A x)"
    by (rule identity_intro[OF path_space identity_intro[OF A x]])
  show "reflexivity (identity_type A x x) (reflexivity A x)
      \<Colon>\<^sub>h identity_type (identity_type A x x)
        (path_concat A x x x (reflexivity A x)
          (path_inverse A x x (reflexivity A x)))
        (reflexivity A x)"
    using base by simp
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

definition path_inverse_left ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_inverse_left A x y p \<equiv>
    identity_ind A x
      (\<lambda>y p. identity_type (identity_type A y y)
        (path_concat A y x y (path_inverse A x y p) p)
        (reflexivity A y))
      (reflexivity (identity_type A x x) (reflexivity A x)) y p"

lemma path_inverse_left_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "path_inverse_left A x y p \<Colon>\<^sub>h
    identity_type (identity_type A y y)
      (path_concat A y x y (path_inverse A x y p) p)
      (reflexivity A y)"
  unfolding path_inverse_left_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume q: "q \<Colon>\<^sub>h identity_type A x w"
  have inv: "path_inverse A x w q \<Colon>\<^sub>h identity_type A w x"
    by (rule path_inverse_type[OF A x w q])
  have composed: "path_concat A w x w (path_inverse A x w q) q
      \<Colon>\<^sub>h identity_type A w w"
    by (rule path_concat_type[OF A w x w inv q])
  have path_space: "identity_type A w w \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A w w])
  show "identity_type (identity_type A w w)
      (path_concat A w x w (path_inverse A x w q) q)
      (reflexivity A w) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space composed identity_intro[OF A w]])
next
  have path_space: "identity_type A x x \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x x])
  have base: "reflexivity (identity_type A x x) (reflexivity A x)
      \<Colon>\<^sub>h identity_type (identity_type A x x)
        (reflexivity A x) (reflexivity A x)"
    by (rule identity_intro[OF path_space identity_intro[OF A x]])
  show "reflexivity (identity_type A x x) (reflexivity A x)
      \<Colon>\<^sub>h identity_type (identity_type A x x)
        (path_concat A x x x
          (path_inverse A x x (reflexivity A x)) (reflexivity A x))
        (reflexivity A x)"
    using base by simp
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

section \<open>Functorial action and homotopies\<close>

definition ap ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr"
where
  "ap A B f x y p \<equiv>
    identity_ind A x
      (\<lambda>y _. identity_type B (app f x) (app f y))
      (reflexivity B (app f x)) y p"

lemma ap_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "ap A B f x y p \<Colon>\<^sub>h
    identity_type B (app f x) (app f y)"
  unfolding ap_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume "q \<Colon>\<^sub>h identity_type A x w"
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have fw: "app f w \<Colon>\<^sub>h B" by (rule arrow_elim[OF f w])
  show "identity_type B (app f x) (app f w) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fx fw])
next
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  show "reflexivity B (app f x) \<Colon>\<^sub>h
      identity_type B (app f x) (app f x)"
    by (rule identity_intro[OF B fx])
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

lemma ap_refl [simp]:
  "ap A B f x x (reflexivity A x) \<equiv> reflexivity B (app f x)"
  unfolding ap_def by simp

definition ap_concat ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "ap_concat A B f x y z p q \<equiv>
    identity_ind A y
      (\<lambda>z q. identity_type
        (identity_type B (app f x) (app f z))
        (ap A B f x z (path_concat A x y z p q))
        (path_concat B (app f x) (app f y) (app f z)
          (ap A B f x y p) (ap A B f y z q)))
      (reflexivity
        (identity_type B (app f x) (app f y))
        (ap A B f x y p))
      z q"

lemma ap_concat_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and z: "z \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
    and q: "q \<Colon>\<^sub>h identity_type A y z"
  shows "ap_concat A B f x y z p q \<Colon>\<^sub>h
    identity_type (identity_type B (app f x) (app f z))
      (ap A B f x z (path_concat A x y z p q))
      (path_concat B (app f x) (app f y) (app f z)
        (ap A B f x y p) (ap A B f y z q))"
  unfolding ap_concat_def
proof (rule identity_elim[OF A y])
  fix w r
  assume w: "w \<Colon>\<^sub>h A"
  assume r: "r \<Colon>\<^sub>h identity_type A y w"
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have fy: "app f y \<Colon>\<^sub>h B" by (rule arrow_elim[OF f y])
  have fw: "app f w \<Colon>\<^sub>h B" by (rule arrow_elim[OF f w])
  have pq: "path_concat A x y w p r \<Colon>\<^sub>h identity_type A x w"
    by (rule path_concat_type[OF A x y w p r])
  have ap_pq: "ap A B f x w (path_concat A x y w p r) \<Colon>\<^sub>h
      identity_type B (app f x) (app f w)"
    by (rule ap_type[OF A B f x w pq])
  have ap_p: "ap A B f x y p \<Colon>\<^sub>h
      identity_type B (app f x) (app f y)"
    by (rule ap_type[OF A B f x y p])
  have ap_r: "ap A B f y w r \<Colon>\<^sub>h
      identity_type B (app f y) (app f w)"
    by (rule ap_type[OF A B f y w r])
  have composite: "path_concat B (app f x) (app f y) (app f w)
      (ap A B f x y p) (ap A B f y w r) \<Colon>\<^sub>h
      identity_type B (app f x) (app f w)"
    by (rule path_concat_type[OF B fx fy fw ap_p ap_r])
  have path_space: "identity_type B (app f x) (app f w)
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fx fw])
  show "identity_type (identity_type B (app f x) (app f w))
      (ap A B f x w (path_concat A x y w p r))
      (path_concat B (app f x) (app f y) (app f w)
        (ap A B f x y p) (ap A B f y w r)) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space ap_pq composite])
next
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have fy: "app f y \<Colon>\<^sub>h B" by (rule arrow_elim[OF f y])
  have ap_p: "ap A B f x y p \<Colon>\<^sub>h
      identity_type B (app f x) (app f y)"
    by (rule ap_type[OF A B f x y p])
  have path_space: "identity_type B (app f x) (app f y)
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fx fy])
  show "reflexivity (identity_type B (app f x) (app f y))
      (ap A B f x y p) \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) (app f y))
        (ap A B f x y (path_concat A x y y p (reflexivity A y)))
        (path_concat B (app f x) (app f y) (app f y)
          (ap A B f x y p)
          (ap A B f y y (reflexivity A y)))"
    using identity_intro[OF path_space ap_p] by simp
next
  show "z \<Colon>\<^sub>h A" by (rule z)
next
  show "q \<Colon>\<^sub>h identity_type A y z" by (rule q)
qed

definition ap_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr"
where
  "ap_inverse A B f x y p \<equiv>
    identity_ind A x
      (\<lambda>y p. identity_type
        (identity_type B (app f y) (app f x))
        (ap A B f y x (path_inverse A x y p))
        (path_inverse B (app f x) (app f y) (ap A B f x y p)))
      (reflexivity
        (identity_type B (app f x) (app f x))
        (reflexivity B (app f x)))
      y p"

lemma ap_inverse_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "ap_inverse A B f x y p \<Colon>\<^sub>h
    identity_type (identity_type B (app f y) (app f x))
      (ap A B f y x (path_inverse A x y p))
      (path_inverse B (app f x) (app f y) (ap A B f x y p))"
  unfolding ap_inverse_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume q: "q \<Colon>\<^sub>h identity_type A x w"
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have fw: "app f w \<Colon>\<^sub>h B" by (rule arrow_elim[OF f w])
  have inv_q: "path_inverse A x w q \<Colon>\<^sub>h identity_type A w x"
    by (rule path_inverse_type[OF A x w q])
  have lhs: "ap A B f w x (path_inverse A x w q) \<Colon>\<^sub>h
      identity_type B (app f w) (app f x)"
    by (rule ap_type[OF A B f w x inv_q])
  have ap_q: "ap A B f x w q \<Colon>\<^sub>h
      identity_type B (app f x) (app f w)"
    by (rule ap_type[OF A B f x w q])
  have rhs: "path_inverse B (app f x) (app f w) (ap A B f x w q)
      \<Colon>\<^sub>h identity_type B (app f w) (app f x)"
    by (rule path_inverse_type[OF B fx fw ap_q])
  have path_space: "identity_type B (app f w) (app f x)
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fw fx])
  show "identity_type (identity_type B (app f w) (app f x))
      (ap A B f w x (path_inverse A x w q))
      (path_inverse B (app f x) (app f w) (ap A B f x w q))
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space lhs rhs])
next
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have loop_space: "identity_type B (app f x) (app f x)
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fx fx])
  have refl_path: "reflexivity B (app f x) \<Colon>\<^sub>h
      identity_type B (app f x) (app f x)"
    by (rule identity_intro[OF B fx])
  show "reflexivity (identity_type B (app f x) (app f x))
      (reflexivity B (app f x)) \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) (app f x))
        (ap A B f x x (path_inverse A x x (reflexivity A x)))
        (path_inverse B (app f x) (app f x)
          (ap A B f x x (reflexivity A x)))"
    using identity_intro[OF loop_space refl_path] by simp
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

definition pair_second_map ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr"
where
  "pair_second_map A B x \<equiv> lambda (B x) (\<lambda>u. pair x u)"

lemma pair_second_map_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
  shows "pair_second_map A B x \<Colon>\<^sub>h arrow (B x) (sigma_type A B)"
  unfolding pair_second_map_def
proof (rule arrow_intro[OF B[OF x]])
  fix u
  assume u: "u \<Colon>\<^sub>h B x"
  show "pair x u \<Colon>\<^sub>h sigma_type A B"
    by (rule sigma_intro[where B=B, OF x u])
qed

definition sigma_path ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "sigma_path A B x y u v p q \<equiv>
    app
      (app
        (identity_ind A x
          (\<lambda>y p. pi_type (B y) (\<lambda>v.
            arrow
              (identity_type (B y) (transport A B x y p u) v)
              (identity_type (sigma_type A B) (pair x u) (pair y v))))
          (lambda (B x) (\<lambda>v.
            lambda (identity_type (B x) u v) (\<lambda>r.
              ap (B x) (sigma_type A B) (pair_second_map A B x)
                u v r)))
          y p)
        v)
      q"

lemma sigma_path_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and u: "u \<Colon>\<^sub>h B x"
    and v: "v \<Colon>\<^sub>h B y"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
    and q: "q \<Colon>\<^sub>h
      identity_type (B y) (transport A B x y p u) v"
  shows "sigma_path A B x y u v p q \<Colon>\<^sub>h
    identity_type (sigma_type A B) (pair x u) (pair y v)"
proof -
  have Sigma: "sigma_type A B \<Colon>\<^sub>h universe i"
    by (rule sigma_form[OF A B])
  have xu: "pair x u \<Colon>\<^sub>h sigma_type A B"
    by (rule sigma_intro[where B=B, OF x u])
  have motive:
    "\<And>w r. w \<Colon>\<^sub>h A \<Longrightarrow>
      r \<Colon>\<^sub>h identity_type A x w \<Longrightarrow>
      pi_type (B w) (\<lambda>t.
        arrow
          (identity_type (B w) (transport A B x w r u) t)
          (identity_type (sigma_type A B) (pair x u) (pair w t)))
        \<Colon>\<^sub>h universe i"
  proof -
    fix w r
    assume w: "w \<Colon>\<^sub>h A"
    assume r: "r \<Colon>\<^sub>h identity_type A x w"
    have transported: "transport A B x w r u \<Colon>\<^sub>h B w"
      by (rule transport_type[where P=B, OF A B x w r u])
    show "pi_type (B w) (\<lambda>t.
        arrow
          (identity_type (B w) (transport A B x w r u) t)
          (identity_type (sigma_type A B) (pair x u) (pair w t)))
        \<Colon>\<^sub>h universe i"
    proof (rule pi_form[OF B[OF w]])
      fix t
      assume t: "t \<Colon>\<^sub>h B w"
      have wt: "pair w t \<Colon>\<^sub>h sigma_type A B"
        by (rule sigma_intro[where B=B, OF w t])
      have path_domain:
        "identity_type (B w) (transport A B x w r u) t
          \<Colon>\<^sub>h universe i"
        by (rule identity_form[OF B[OF w] transported t])
      have path_codomain:
        "identity_type (sigma_type A B) (pair x u) (pair w t)
          \<Colon>\<^sub>h universe i"
        by (rule identity_form[OF Sigma xu wt])
      show "arrow
          (identity_type (B w) (transport A B x w r u) t)
          (identity_type (sigma_type A B) (pair x u) (pair w t))
          \<Colon>\<^sub>h universe i"
        by (rule arrow_form[OF path_domain path_codomain])
    qed
  qed
  have pair_map: "pair_second_map A B x \<Colon>\<^sub>h
      arrow (B x) (sigma_type A B)"
    by (rule pair_second_map_type[OF A B x])
  have base_raw: "lambda (B x) (\<lambda>t.
      lambda (identity_type (B x) u t) (\<lambda>r.
        ap (B x) (sigma_type A B) (pair_second_map A B x) u t r))
      \<Colon>\<^sub>h
      pi_type (B x) (\<lambda>t.
        arrow (identity_type (B x) u t)
          (identity_type (sigma_type A B) (pair x u) (pair x t)))"
  proof (rule pi_intro[OF B[OF x]])
    fix t
    assume t: "t \<Colon>\<^sub>h B x"
    have path_domain: "identity_type (B x) u t \<Colon>\<^sub>h universe i"
      by (rule identity_form[OF B[OF x] u t])
    show "lambda (identity_type (B x) u t) (\<lambda>r.
        ap (B x) (sigma_type A B) (pair_second_map A B x) u t r)
        \<Colon>\<^sub>h arrow (identity_type (B x) u t)
          (identity_type (sigma_type A B) (pair x u) (pair x t))"
    proof (rule arrow_intro[OF path_domain])
      fix r
      assume r: "r \<Colon>\<^sub>h identity_type (B x) u t"
      show "ap (B x) (sigma_type A B) (pair_second_map A B x) u t r
          \<Colon>\<^sub>h identity_type (sigma_type A B) (pair x u) (pair x t)"
        using ap_type[OF B[OF x] Sigma pair_map u t r]
        unfolding pair_second_map_def by simp
    qed
  qed
  have base: "lambda (B x) (\<lambda>t.
      lambda (identity_type (B x) u t) (\<lambda>r.
        ap (B x) (sigma_type A B) (pair_second_map A B x) u t r))
      \<Colon>\<^sub>h
      pi_type (B x) (\<lambda>t.
        arrow
          (identity_type (B x)
            (transport A B x x (reflexivity A x) u) t)
          (identity_type (sigma_type A B) (pair x u) (pair x t)))"
    using base_raw by simp
  have inducted: "identity_ind A x
      (\<lambda>w r. pi_type (B w) (\<lambda>t.
        arrow
          (identity_type (B w) (transport A B x w r u) t)
          (identity_type (sigma_type A B) (pair x u) (pair w t))))
      (lambda (B x) (\<lambda>t.
        lambda (identity_type (B x) u t) (\<lambda>r.
          ap (B x) (sigma_type A B) (pair_second_map A B x) u t r)))
      y p \<Colon>\<^sub>h
      pi_type (B y) (\<lambda>t.
        arrow
          (identity_type (B y) (transport A B x y p u) t)
          (identity_type (sigma_type A B) (pair x u) (pair y t)))"
  proof (rule identity_elim[OF A x])
    fix w r
    assume w: "w \<Colon>\<^sub>h A"
    assume r: "r \<Colon>\<^sub>h identity_type A x w"
    show "pi_type (B w) (\<lambda>t.
        arrow
          (identity_type (B w) (transport A B x w r u) t)
          (identity_type (sigma_type A B) (pair x u) (pair w t)))
        \<Colon>\<^sub>h universe i"
      by (rule motive[OF w r])
  next
    show "lambda (B x) (\<lambda>t.
        lambda (identity_type (B x) u t) (\<lambda>r.
          ap (B x) (sigma_type A B) (pair_second_map A B x) u t r))
        \<Colon>\<^sub>h
        pi_type (B x) (\<lambda>t.
          arrow
            (identity_type (B x)
              (transport A B x x (reflexivity A x) u) t)
            (identity_type (sigma_type A B) (pair x u) (pair x t)))"
      by (rule base)
  next
    show "y \<Colon>\<^sub>h A" by (rule y)
  next
    show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
  qed
  have at_v: "app
      (identity_ind A x
        (\<lambda>w r. pi_type (B w) (\<lambda>t.
          arrow
            (identity_type (B w) (transport A B x w r u) t)
            (identity_type (sigma_type A B) (pair x u) (pair w t))))
        (lambda (B x) (\<lambda>t.
          lambda (identity_type (B x) u t) (\<lambda>r.
            ap (B x) (sigma_type A B) (pair_second_map A B x) u t r)))
        y p)
      v \<Colon>\<^sub>h
      arrow
        (identity_type (B y) (transport A B x y p u) v)
        (identity_type (sigma_type A B) (pair x u) (pair y v))"
    by (rule pi_elim[OF inducted v])
  show "sigma_path A B x y u v p q \<Colon>\<^sub>h
      identity_type (sigma_type A B) (pair x u) (pair y v)"
    unfolding sigma_path_def
    by (rule arrow_elim[OF at_v q])
qed

definition homotopy ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "homotopy A B f g \<equiv>
    pi_type A (\<lambda>x. identity_type (B x) (app f x) (app g x))"

lemma homotopy_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h pi_type A B"
    and g: "g \<Colon>\<^sub>h pi_type A B"
  shows "homotopy A B f g \<Colon>\<^sub>h universe i"
  unfolding homotopy_def
proof (rule pi_form[OF A])
  fix x
  assume x: "x \<Colon>\<^sub>h A"
  have fx: "app f x \<Colon>\<^sub>h B x" by (rule pi_elim[OF f x])
  have gx: "app g x \<Colon>\<^sub>h B x" by (rule pi_elim[OF g x])
  show "identity_type (B x) (app f x) (app g x) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B[OF x] fx gx])
qed

definition homotopy_refl ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr"
where
  "homotopy_refl A B f \<equiv>
    lambda A (\<lambda>x. reflexivity (B x) (app f x))"

lemma homotopy_refl_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h pi_type A B"
  shows "homotopy_refl A B f \<Colon>\<^sub>h homotopy A B f f"
  unfolding homotopy_refl_def homotopy_def
proof (rule pi_intro[OF A])
  fix x
  assume x: "x \<Colon>\<^sub>h A"
  have fx: "app f x \<Colon>\<^sub>h B x" by (rule pi_elim[OF f x])
  show "reflexivity (B x) (app f x) \<Colon>\<^sub>h
      identity_type (B x) (app f x) (app f x)"
    by (rule identity_intro[OF B[OF x] fx])
qed

definition homotopy_concat ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "homotopy_concat A B f g h H K \<equiv>
    lambda A (\<lambda>x.
      path_concat (B x) (app f x) (app g x) (app h x)
        (app H x) (app K x))"

lemma homotopy_concat_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h pi_type A B"
    and g: "g \<Colon>\<^sub>h pi_type A B"
    and h: "h \<Colon>\<^sub>h pi_type A B"
    and H: "H \<Colon>\<^sub>h homotopy A B f g"
    and K: "K \<Colon>\<^sub>h homotopy A B g h"
  shows "homotopy_concat A B f g h H K \<Colon>\<^sub>h homotopy A B f h"
  unfolding homotopy_concat_def homotopy_def
proof (rule pi_intro[OF A])
  fix x
  assume x: "x \<Colon>\<^sub>h A"
  have fx: "app f x \<Colon>\<^sub>h B x" by (rule pi_elim[OF f x])
  have gx: "app g x \<Colon>\<^sub>h B x" by (rule pi_elim[OF g x])
  have hx: "app h x \<Colon>\<^sub>h B x" by (rule pi_elim[OF h x])
  have Hx: "app H x \<Colon>\<^sub>h identity_type (B x) (app f x) (app g x)"
    using H unfolding homotopy_def by (rule pi_elim[OF _ x])
  have Kx: "app K x \<Colon>\<^sub>h identity_type (B x) (app g x) (app h x)"
    using K unfolding homotopy_def by (rule pi_elim[OF _ x])
  show "path_concat (B x) (app f x) (app g x) (app h x)
      (app H x) (app K x) \<Colon>\<^sub>h
      identity_type (B x) (app f x) (app h x)"
    by (rule path_concat_type[OF B[OF x] fx gx hx Hx Kx])
qed

definition homotopy_inverse ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr"
where
  "homotopy_inverse A B f g H \<equiv>
    lambda A (\<lambda>x.
      path_inverse (B x) (app f x) (app g x) (app H x))"

lemma homotopy_inverse_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h pi_type A B"
    and g: "g \<Colon>\<^sub>h pi_type A B"
    and H: "H \<Colon>\<^sub>h homotopy A B f g"
  shows "homotopy_inverse A B f g H \<Colon>\<^sub>h homotopy A B g f"
  unfolding homotopy_inverse_def homotopy_def
proof (rule pi_intro[OF A])
  fix x
  assume x: "x \<Colon>\<^sub>h A"
  have fx: "app f x \<Colon>\<^sub>h B x" by (rule pi_elim[OF f x])
  have gx: "app g x \<Colon>\<^sub>h B x" by (rule pi_elim[OF g x])
  have Hx: "app H x \<Colon>\<^sub>h
      identity_type (B x) (app f x) (app g x)"
    using H unfolding homotopy_def by (rule pi_elim[OF _ x])
  show "path_inverse (B x) (app f x) (app g x) (app H x)
      \<Colon>\<^sub>h identity_type (B x) (app g x) (app f x)"
    by (rule path_inverse_type[OF B[OF x] fx gx Hx])
qed

definition homotopy_naturality ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "homotopy_naturality A B f g H x y p \<equiv>
    identity_ind A x
      (\<lambda>y p. identity_type
        (identity_type B (app f x) (app g y))
        (path_concat B (app f x) (app f y) (app g y)
          (ap A B f x y p) (app H y))
        (path_concat B (app f x) (app g x) (app g y)
          (app H x) (ap A B g x y p)))
      (path_left_unit B (app f x) (app g x) (app H x))
      y p"

lemma homotopy_naturality_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow A B"
    and H: "H \<Colon>\<^sub>h homotopy A (\<lambda>_. B) f g"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "homotopy_naturality A B f g H x y p \<Colon>\<^sub>h
    identity_type (identity_type B (app f x) (app g y))
      (path_concat B (app f x) (app f y) (app g y)
        (ap A B f x y p) (app H y))
      (path_concat B (app f x) (app g x) (app g y)
        (app H x) (ap A B g x y p))"
  unfolding homotopy_naturality_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume q: "q \<Colon>\<^sub>h identity_type A x w"
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have fw: "app f w \<Colon>\<^sub>h B" by (rule arrow_elim[OF f w])
  have gx: "app g x \<Colon>\<^sub>h B" by (rule arrow_elim[OF g x])
  have gw: "app g w \<Colon>\<^sub>h B" by (rule arrow_elim[OF g w])
  have Hx: "app H x \<Colon>\<^sub>h identity_type B (app f x) (app g x)"
    using H unfolding homotopy_def by (rule pi_elim[OF _ x])
  have Hw: "app H w \<Colon>\<^sub>h identity_type B (app f w) (app g w)"
    using H unfolding homotopy_def by (rule pi_elim[OF _ w])
  have ap_f: "ap A B f x w q \<Colon>\<^sub>h
      identity_type B (app f x) (app f w)"
    by (rule ap_type[OF A B f x w q])
  have ap_g: "ap A B g x w q \<Colon>\<^sub>h
      identity_type B (app g x) (app g w)"
    by (rule ap_type[OF A B g x w q])
  have lhs: "path_concat B (app f x) (app f w) (app g w)
      (ap A B f x w q) (app H w) \<Colon>\<^sub>h
      identity_type B (app f x) (app g w)"
    by (rule path_concat_type[OF B fx fw gw ap_f Hw])
  have rhs: "path_concat B (app f x) (app g x) (app g w)
      (app H x) (ap A B g x w q) \<Colon>\<^sub>h
      identity_type B (app f x) (app g w)"
    by (rule path_concat_type[OF B fx gx gw Hx ap_g])
  have path_space: "identity_type B (app f x) (app g w)
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fx gw])
  show "identity_type (identity_type B (app f x) (app g w))
      (path_concat B (app f x) (app f w) (app g w)
        (ap A B f x w q) (app H w))
      (path_concat B (app f x) (app g x) (app g w)
        (app H x) (ap A B g x w q)) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space lhs rhs])
next
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have gx: "app g x \<Colon>\<^sub>h B" by (rule arrow_elim[OF g x])
  have Hx: "app H x \<Colon>\<^sub>h identity_type B (app f x) (app g x)"
    using H unfolding homotopy_def by (rule pi_elim[OF _ x])
  show "path_left_unit B (app f x) (app g x) (app H x)
      \<Colon>\<^sub>h identity_type
        (identity_type B (app f x) (app g x))
        (path_concat B (app f x) (app f x) (app g x)
          (ap A B f x x (reflexivity A x)) (app H x))
        (path_concat B (app f x) (app g x) (app g x)
          (app H x) (ap A B g x x (reflexivity A x)))"
    using path_left_unit_type[OF B fx gx Hx] by simp
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

section \<open>Functorial reduction lemmas\<close>

definition ap_identity ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "ap_identity A x y p \<equiv>
    identity_ind A x
      (\<lambda>y p. identity_type (identity_type A x y)
        (ap A A (identity_function A) x y p) p)
      (reflexivity (identity_type A x x) (reflexivity A x))
      y p"

lemma ap_identity_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "ap_identity A x y p \<Colon>\<^sub>h
    identity_type (identity_type A x y)
      (ap A A (identity_function A) x y p) p"
  unfolding ap_identity_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume q: "q \<Colon>\<^sub>h identity_type A x w"
  have id: "identity_function A \<Colon>\<^sub>h arrow A A"
    by (rule identity_function_type[OF A])
  have apq: "ap A A (identity_function A) x w q \<Colon>\<^sub>h
      identity_type A x w"
    using ap_type[OF A A id x w q] by simp
  have path_space: "identity_type A x w \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x w])
  show "identity_type (identity_type A x w)
      (ap A A (identity_function A) x w q) q \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space apq q])
next
  have path_space: "identity_type A x x \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x x])
  have base: "reflexivity (identity_type A x x) (reflexivity A x) \<Colon>\<^sub>h
      identity_type (identity_type A x x)
        (reflexivity A x) (reflexivity A x)"
    by (rule identity_intro[OF path_space identity_intro[OF A x]])
  show "reflexivity (identity_type A x x) (reflexivity A x) \<Colon>\<^sub>h
      identity_type (identity_type A x x)
        (ap A A (identity_function A) x x (reflexivity A x))
        (reflexivity A x)"
    using base by simp
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

definition ap_compose ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "ap_compose A B C g f x y p \<equiv>
    identity_ind A x
      (\<lambda>y p. identity_type
        (identity_type C (app g (app f x)) (app g (app f y)))
        (ap A C (compose A B C g f) x y p)
        (ap B C g (app f x) (app f y) (ap A B f x y p)))
      (reflexivity
        (identity_type C (app g (app f x)) (app g (app f x)))
        (reflexivity C (app g (app f x))))
      y p"

lemma ap_compose_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and C: "C \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow B C"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "ap_compose A B C g f x y p \<Colon>\<^sub>h
    identity_type
      (identity_type C (app g (app f x)) (app g (app f y)))
      (ap A C (compose A B C g f) x y p)
      (ap B C g (app f x) (app f y) (ap A B f x y p))"
  unfolding ap_compose_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume q: "q \<Colon>\<^sub>h identity_type A x w"
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have fw: "app f w \<Colon>\<^sub>h B" by (rule arrow_elim[OF f w])
  have gfx: "app g (app f x) \<Colon>\<^sub>h C" by (rule arrow_elim[OF g fx])
  have gfw: "app g (app f w) \<Colon>\<^sub>h C" by (rule arrow_elim[OF g fw])
  have gf: "compose A B C g f \<Colon>\<^sub>h arrow A C"
    by (rule compose_type[OF A f g])
  have ap_gf: "ap A C (compose A B C g f) x w q \<Colon>\<^sub>h
      identity_type C (app g (app f x)) (app g (app f w))"
    using ap_type[OF A C gf x w q] by simp
  have apf: "ap A B f x w q \<Colon>\<^sub>h
      identity_type B (app f x) (app f w)"
    by (rule ap_type[OF A B f x w q])
  have ap_g: "ap B C g (app f x) (app f w) (ap A B f x w q) \<Colon>\<^sub>h
      identity_type C (app g (app f x)) (app g (app f w))"
    by (rule ap_type[OF B C g fx fw apf])
  have path_space:
      "identity_type C (app g (app f x)) (app g (app f w))
        \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF C gfx gfw])
  show "identity_type
      (identity_type C (app g (app f x)) (app g (app f w)))
      (ap A C (compose A B C g f) x w q)
      (ap B C g (app f x) (app f w) (ap A B f x w q))
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space ap_gf ap_g])
next
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have gfx: "app g (app f x) \<Colon>\<^sub>h C" by (rule arrow_elim[OF g fx])
  have path_space:
      "identity_type C (app g (app f x)) (app g (app f x))
        \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF C gfx gfx])
  have base: "reflexivity
      (identity_type C (app g (app f x)) (app g (app f x)))
      (reflexivity C (app g (app f x))) \<Colon>\<^sub>h
      identity_type
        (identity_type C (app g (app f x)) (app g (app f x)))
        (reflexivity C (app g (app f x)))
        (reflexivity C (app g (app f x)))"
    by (rule identity_intro[OF path_space identity_intro[OF C gfx]])
  show "reflexivity
      (identity_type C (app g (app f x)) (app g (app f x)))
      (reflexivity C (app g (app f x))) \<Colon>\<^sub>h
      identity_type
        (identity_type C (app g (app f x)) (app g (app f x)))
        (ap A C (compose A B C g f) x x (reflexivity A x))
        (ap B C g (app f x) (app f x)
          (ap A B f x x (reflexivity A x)))"
    using base by simp
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

definition transport_identity_left ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "transport_identity_left A B f c x y p w \<equiv>
    identity_ind A x
      (\<lambda>y p. identity_type (identity_type B (app f y) c)
        (transport A (\<lambda>a. identity_type B (app f a) c) x y p w)
        (path_concat B (app f y) (app f x) c
          (path_inverse B (app f x) (app f y) (ap A B f x y p)) w))
      (path_inverse (identity_type B (app f x) c)
        (path_concat B (app f x) (app f x) c
          (reflexivity B (app f x)) w)
        w
        (path_left_unit B (app f x) c w))
      y p"

lemma transport_identity_left_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and c: "c \<Colon>\<^sub>h B"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
    and w: "w \<Colon>\<^sub>h identity_type B (app f x) c"
  shows "transport_identity_left A B f c x y p w \<Colon>\<^sub>h
    identity_type (identity_type B (app f y) c)
      (transport A (\<lambda>a. identity_type B (app f a) c) x y p w)
      (path_concat B (app f y) (app f x) c
        (path_inverse B (app f x) (app f y) (ap A B f x y p)) w)"
  unfolding transport_identity_left_def
proof (rule identity_elim[OF A x])
  fix v r
  assume v: "v \<Colon>\<^sub>h A"
  assume r: "r \<Colon>\<^sub>h identity_type A x v"
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have fv: "app f v \<Colon>\<^sub>h B" by (rule arrow_elim[OF f v])
  have transported:
      "transport A (\<lambda>a. identity_type B (app f a) c) x v r w \<Colon>\<^sub>h
        identity_type B (app f v) c"
  proof (rule transport_type[OF A])
    fix a
    assume a: "a \<Colon>\<^sub>h A"
    have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
    show "identity_type B (app f a) c \<Colon>\<^sub>h universe i"
      by (rule identity_form[OF B fa c])
  next
    show "x \<Colon>\<^sub>h A" by (rule x)
  next
    show "v \<Colon>\<^sub>h A" by (rule v)
  next
    show "r \<Colon>\<^sub>h identity_type A x v" by (rule r)
  next
    show "w \<Colon>\<^sub>h identity_type B (app f x) c" by (rule w)
  qed
  have apr: "ap A B f x v r \<Colon>\<^sub>h identity_type B (app f x) (app f v)"
    by (rule ap_type[OF A B f x v r])
  have inv: "path_inverse B (app f x) (app f v) (ap A B f x v r) \<Colon>\<^sub>h
      identity_type B (app f v) (app f x)"
    by (rule path_inverse_type[OF B fx fv apr])
  have composed: "path_concat B (app f v) (app f x) c
      (path_inverse B (app f x) (app f v) (ap A B f x v r)) w \<Colon>\<^sub>h
      identity_type B (app f v) c"
    by (rule path_concat_type[OF B fv fx c inv w])
  have path_space: "identity_type B (app f v) c \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fv c])
  show "identity_type (identity_type B (app f v) c)
      (transport A (\<lambda>a. identity_type B (app f a) c) x v r w)
      (path_concat B (app f v) (app f x) c
        (path_inverse B (app f x) (app f v) (ap A B f x v r)) w)
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space transported composed])
next
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have path_space: "identity_type B (app f x) c \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fx c])
  have composed: "path_concat B (app f x) (app f x) c
      (reflexivity B (app f x)) w \<Colon>\<^sub>h
      identity_type B (app f x) c"
    by (rule path_concat_type[OF B fx fx c identity_intro[OF B fx] w])
  have base: "path_inverse (identity_type B (app f x) c)
      (path_concat B (app f x) (app f x) c
        (reflexivity B (app f x)) w)
      w
      (path_left_unit B (app f x) c w) \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) c)
        w
        (path_concat B (app f x) (app f x) c
          (reflexivity B (app f x)) w)"
    by (rule path_inverse_type[OF path_space composed w
          path_left_unit_type[OF B fx c w]])
  show "path_inverse (identity_type B (app f x) c)
      (path_concat B (app f x) (app f x) c
        (reflexivity B (app f x)) w)
      w
      (path_left_unit B (app f x) c w) \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) c)
        (transport A (\<lambda>a. identity_type B (app f a) c) x x
          (reflexivity A x) w)
        (path_concat B (app f x) (app f x) c
          (path_inverse B (app f x) (app f x)
            (ap A B f x x (reflexivity A x))) w)"
    using base by simp
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

section \<open>Whiskering and cancellation of paths\<close>

definition path_inverse_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_inverse_inverse A x y p \<equiv>
    identity_ind A x
      (\<lambda>y p. identity_type (identity_type A x y)
        (path_inverse A y x (path_inverse A x y p)) p)
      (reflexivity (identity_type A x x) (reflexivity A x))
      y p"

lemma path_inverse_inverse_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
  shows "path_inverse_inverse A x y p \<Colon>\<^sub>h
    identity_type (identity_type A x y)
      (path_inverse A y x (path_inverse A x y p)) p"
  unfolding path_inverse_inverse_def
proof (rule identity_elim[OF A x])
  fix w q
  assume w: "w \<Colon>\<^sub>h A"
  assume q: "q \<Colon>\<^sub>h identity_type A x w"
  have inv: "path_inverse A x w q \<Colon>\<^sub>h identity_type A w x"
    by (rule path_inverse_type[OF A x w q])
  have double: "path_inverse A w x (path_inverse A x w q) \<Colon>\<^sub>h
      identity_type A x w"
    by (rule path_inverse_type[OF A w x inv])
  have path_space: "identity_type A x w \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x w])
  show "identity_type (identity_type A x w)
      (path_inverse A w x (path_inverse A x w q)) q \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space double q])
next
  have path_space: "identity_type A x x \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x x])
  have base: "reflexivity (identity_type A x x) (reflexivity A x) \<Colon>\<^sub>h
      identity_type (identity_type A x x)
        (reflexivity A x) (reflexivity A x)"
    by (rule identity_intro[OF path_space identity_intro[OF A x]])
  show "reflexivity (identity_type A x x) (reflexivity A x) \<Colon>\<^sub>h
      identity_type (identity_type A x x)
        (path_inverse A x x (path_inverse A x x (reflexivity A x)))
        (reflexivity A x)"
    using base by simp
next
  show "y \<Colon>\<^sub>h A" by (rule y)
next
  show "p \<Colon>\<^sub>h identity_type A x y" by (rule p)
qed

definition path_whisker_left ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_whisker_left A x y z r q q' m \<equiv>
    identity_ind (identity_type A y z) q
      (\<lambda>q' m. identity_type (identity_type A x z)
        (path_concat A x y z r q) (path_concat A x y z r q'))
      (reflexivity (identity_type A x z) (path_concat A x y z r q))
      q' m"

lemma path_whisker_left_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and z: "z \<Colon>\<^sub>h A"
    and r: "r \<Colon>\<^sub>h identity_type A x y"
    and q: "q \<Colon>\<^sub>h identity_type A y z"
    and q': "q' \<Colon>\<^sub>h identity_type A y z"
    and m: "m \<Colon>\<^sub>h identity_type (identity_type A y z) q q'"
  shows "path_whisker_left A x y z r q q' m \<Colon>\<^sub>h
    identity_type (identity_type A x z)
      (path_concat A x y z r q) (path_concat A x y z r q')"
  unfolding path_whisker_left_def
proof (rule identity_elim[OF identity_form[OF A y z] q])
  fix w mm
  assume w: "w \<Colon>\<^sub>h identity_type A y z"
  assume mm: "mm \<Colon>\<^sub>h identity_type (identity_type A y z) q w"
  have rq: "path_concat A x y z r q \<Colon>\<^sub>h identity_type A x z"
    by (rule path_concat_type[OF A x y z r q])
  have rw: "path_concat A x y z r w \<Colon>\<^sub>h identity_type A x z"
    by (rule path_concat_type[OF A x y z r w])
  have path_space: "identity_type A x z \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x z])
  show "identity_type (identity_type A x z)
      (path_concat A x y z r q) (path_concat A x y z r w) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space rq rw])
next
  have rq: "path_concat A x y z r q \<Colon>\<^sub>h identity_type A x z"
    by (rule path_concat_type[OF A x y z r q])
  have path_space: "identity_type A x z \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x z])
  show "reflexivity (identity_type A x z) (path_concat A x y z r q) \<Colon>\<^sub>h
      identity_type (identity_type A x z)
        (path_concat A x y z r q) (path_concat A x y z r q)"
    by (rule identity_intro[OF path_space rq])
next
  show "q' \<Colon>\<^sub>h identity_type A y z" by (rule q')
next
  show "m \<Colon>\<^sub>h identity_type (identity_type A y z) q q'" by (rule m)
qed

definition path_right_cancel ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_right_cancel A x y z alpha beta r s \<equiv>
    app
      (identity_ind A y
        (\<lambda>z r. arrow
          (identity_type (identity_type A x z)
            (path_concat A x y z alpha r)
            (path_concat A x y z beta r))
          (identity_type (identity_type A x y) alpha beta))
        (identity_function
          (identity_type (identity_type A x y) alpha beta))
        z r)
      s"

lemma path_right_cancel_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and z: "z \<Colon>\<^sub>h A"
    and alpha: "alpha \<Colon>\<^sub>h identity_type A x y"
    and beta: "beta \<Colon>\<^sub>h identity_type A x y"
    and r: "r \<Colon>\<^sub>h identity_type A y z"
    and s: "s \<Colon>\<^sub>h identity_type (identity_type A x z)
             (path_concat A x y z alpha r) (path_concat A x y z beta r)"
  shows "path_right_cancel A x y z alpha beta r s \<Colon>\<^sub>h
    identity_type (identity_type A x y) alpha beta"
proof -
  have path_space: "identity_type A x y \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x y])
  have goal_space:
      "identity_type (identity_type A x y) alpha beta \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space alpha beta])
  have base: "identity_function
      (identity_type (identity_type A x y) alpha beta) \<Colon>\<^sub>h
      arrow (identity_type (identity_type A x y) alpha beta)
            (identity_type (identity_type A x y) alpha beta)"
    by (rule identity_function_type[OF goal_space])
  have inducted: "identity_ind A y
      (\<lambda>z r. arrow
        (identity_type (identity_type A x z)
          (path_concat A x y z alpha r)
          (path_concat A x y z beta r))
        (identity_type (identity_type A x y) alpha beta))
      (identity_function
        (identity_type (identity_type A x y) alpha beta))
      z r \<Colon>\<^sub>h
      arrow
        (identity_type (identity_type A x z)
          (path_concat A x y z alpha r)
          (path_concat A x y z beta r))
        (identity_type (identity_type A x y) alpha beta)"
  proof (rule identity_elim[OF A y])
    fix w rr
    assume w: "w \<Colon>\<^sub>h A"
    assume rr: "rr \<Colon>\<^sub>h identity_type A y w"
    have ar: "path_concat A x y w alpha rr \<Colon>\<^sub>h identity_type A x w"
      by (rule path_concat_type[OF A x y w alpha rr])
    have br: "path_concat A x y w beta rr \<Colon>\<^sub>h identity_type A x w"
      by (rule path_concat_type[OF A x y w beta rr])
    have pspace: "identity_type A x w \<Colon>\<^sub>h universe i"
      by (rule identity_form[OF A x w])
    have dom: "identity_type (identity_type A x w)
        (path_concat A x y w alpha rr)
        (path_concat A x y w beta rr) \<Colon>\<^sub>h universe i"
      by (rule identity_form[OF pspace ar br])
    show "arrow
        (identity_type (identity_type A x w)
          (path_concat A x y w alpha rr)
          (path_concat A x y w beta rr))
        (identity_type (identity_type A x y) alpha beta) \<Colon>\<^sub>h universe i"
      by (rule arrow_form[OF dom goal_space])
  next
    show "identity_function
        (identity_type (identity_type A x y) alpha beta) \<Colon>\<^sub>h
        arrow
          (identity_type (identity_type A x y)
            (path_concat A x y y alpha (reflexivity A y))
            (path_concat A x y y beta (reflexivity A y)))
          (identity_type (identity_type A x y) alpha beta)"
      using base by simp
  next
    show "z \<Colon>\<^sub>h A" by (rule z)
  next
    show "r \<Colon>\<^sub>h identity_type A y z" by (rule r)
  qed
  show "path_right_cancel A x y z alpha beta r s \<Colon>\<^sub>h
      identity_type (identity_type A x y) alpha beta"
    unfolding path_right_cancel_def
    by (rule arrow_elim[OF inducted s])
qed

section \<open>The self-action of a homotopy to the identity\<close>

definition homotopy_self ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "homotopy_self A u H a \<equiv>
    path_right_cancel A (app u (app u a)) (app u a) a
      (ap A A u (app u a) a (app H a))
      (app H (app u a))
      (app H a)
      (path_concat (identity_type A (app u (app u a)) a)
        (path_concat A (app u (app u a)) (app u a) a
          (ap A A u (app u a) a (app H a)) (app H a))
        (path_concat A (app u (app u a)) (app u a) a
          (app H (app u a))
          (ap A A (identity_function A) (app u a) a (app H a)))
        (path_concat A (app u (app u a)) (app u a) a
          (app H (app u a)) (app H a))
        (homotopy_naturality A A u (identity_function A) H
          (app u a) a (app H a))
        (path_whisker_left A (app u (app u a)) (app u a) a
          (app H (app u a))
          (ap A A (identity_function A) (app u a) a (app H a))
          (app H a)
          (ap_identity A (app u a) a (app H a))))"

lemma homotopy_self_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and u: "u \<Colon>\<^sub>h arrow A A"
    and H: "H \<Colon>\<^sub>h homotopy A (\<lambda>_. A) u (identity_function A)"
    and a: "a \<Colon>\<^sub>h A"
  shows "homotopy_self A u H a \<Colon>\<^sub>h
    identity_type (identity_type A (app u (app u a)) (app u a))
      (ap A A u (app u a) a (app H a))
      (app H (app u a))"
proof -
  have id: "identity_function A \<Colon>\<^sub>h arrow A A"
    by (rule identity_function_type[OF A])
  have ua: "app u a \<Colon>\<^sub>h A" by (rule arrow_elim[OF u a])
  have uua: "app u (app u a) \<Colon>\<^sub>h A" by (rule arrow_elim[OF u ua])
  have Hpi: "H \<Colon>\<^sub>h
      pi_type A (\<lambda>x. identity_type A (app u x)
        (app (identity_function A) x))"
    using H unfolding homotopy_def .
  have Ha: "app H a \<Colon>\<^sub>h identity_type A (app u a) a"
    using pi_elim[OF Hpi a] by simp
  have Hua: "app H (app u a) \<Colon>\<^sub>h
      identity_type A (app u (app u a)) (app u a)"
    using pi_elim[OF Hpi ua] by simp
  have apuHa: "ap A A u (app u a) a (app H a) \<Colon>\<^sub>h
      identity_type A (app u (app u a)) (app u a)"
    by (rule ap_type[OF A A u ua a Ha])
  have apidHa: "ap A A (identity_function A) (app u a) a (app H a) \<Colon>\<^sub>h
      identity_type A (app u a) a"
    using ap_type[OF A A id ua a Ha] by simp
  have NAT: "homotopy_naturality A A u (identity_function A) H
        (app u a) a (app H a) \<Colon>\<^sub>h
      identity_type (identity_type A (app u (app u a)) a)
        (path_concat A (app u (app u a)) (app u a) a
          (ap A A u (app u a) a (app H a)) (app H a))
        (path_concat A (app u (app u a)) (app u a) a
          (app H (app u a))
          (ap A A (identity_function A) (app u a) a (app H a)))"
    using homotopy_naturality_type[OF A A u id H ua a Ha] by simp
  have AI: "ap_identity A (app u a) a (app H a) \<Colon>\<^sub>h
      identity_type (identity_type A (app u a) a)
        (ap A A (identity_function A) (app u a) a (app H a))
        (app H a)"
    by (rule ap_identity_type[OF A ua a Ha])
  have WH: "path_whisker_left A (app u (app u a)) (app u a) a
        (app H (app u a))
        (ap A A (identity_function A) (app u a) a (app H a))
        (app H a)
        (ap_identity A (app u a) a (app H a)) \<Colon>\<^sub>h
      identity_type (identity_type A (app u (app u a)) a)
        (path_concat A (app u (app u a)) (app u a) a
          (app H (app u a))
          (ap A A (identity_function A) (app u a) a (app H a)))
        (path_concat A (app u (app u a)) (app u a) a
          (app H (app u a)) (app H a))"
    by (rule path_whisker_left_type[OF A uua ua a Hua apidHa Ha AI])
  have ps: "identity_type A (app u (app u a)) a \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A uua a])
  have P1: "path_concat A (app u (app u a)) (app u a) a
        (ap A A u (app u a) a (app H a)) (app H a) \<Colon>\<^sub>h
      identity_type A (app u (app u a)) a"
    by (rule path_concat_type[OF A uua ua a apuHa Ha])
  have P2: "path_concat A (app u (app u a)) (app u a) a
        (app H (app u a))
        (ap A A (identity_function A) (app u a) a (app H a)) \<Colon>\<^sub>h
      identity_type A (app u (app u a)) a"
    by (rule path_concat_type[OF A uua ua a Hua apidHa])
  have P3: "path_concat A (app u (app u a)) (app u a) a
        (app H (app u a)) (app H a) \<Colon>\<^sub>h
      identity_type A (app u (app u a)) a"
    by (rule path_concat_type[OF A uua ua a Hua Ha])
  have NAT2: "path_concat (identity_type A (app u (app u a)) a)
        (path_concat A (app u (app u a)) (app u a) a
          (ap A A u (app u a) a (app H a)) (app H a))
        (path_concat A (app u (app u a)) (app u a) a
          (app H (app u a))
          (ap A A (identity_function A) (app u a) a (app H a)))
        (path_concat A (app u (app u a)) (app u a) a
          (app H (app u a)) (app H a))
        (homotopy_naturality A A u (identity_function A) H
          (app u a) a (app H a))
        (path_whisker_left A (app u (app u a)) (app u a) a
          (app H (app u a))
          (ap A A (identity_function A) (app u a) a (app H a))
          (app H a)
          (ap_identity A (app u a) a (app H a))) \<Colon>\<^sub>h
      identity_type (identity_type A (app u (app u a)) a)
        (path_concat A (app u (app u a)) (app u a) a
          (ap A A u (app u a) a (app H a)) (app H a))
        (path_concat A (app u (app u a)) (app u a) a
          (app H (app u a)) (app H a))"
    by (rule path_concat_type[OF ps P1 P2 P3 NAT WH])
  show "homotopy_self A u H a \<Colon>\<^sub>h
      identity_type (identity_type A (app u (app u a)) (app u a))
        (ap A A u (app u a) a (app H a))
        (app H (app u a))"
    unfolding homotopy_self_def
    by (rule path_right_cancel_type[OF A uua ua a apuHa Hua Ha NAT2])
qed

definition ap_congruence ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "ap_congruence A B f x y q q' m \<equiv>
    ap (identity_type A x y) (identity_type B (app f x) (app f y))
      (lambda (identity_type A x y) (\<lambda>t. ap A B f x y t))
      q q' m"

lemma ap_congruence_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and q: "q \<Colon>\<^sub>h identity_type A x y"
    and q': "q' \<Colon>\<^sub>h identity_type A x y"
    and m: "m \<Colon>\<^sub>h identity_type (identity_type A x y) q q'"
  shows "ap_congruence A B f x y q q' m \<Colon>\<^sub>h
    identity_type (identity_type B (app f x) (app f y))
      (ap A B f x y q) (ap A B f x y q')"
proof -
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have fy: "app f y \<Colon>\<^sub>h B" by (rule arrow_elim[OF f y])
  have pxA: "identity_type A x y \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x y])
  have pxB: "identity_type B (app f x) (app f y) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fx fy])
  have lam: "lambda (identity_type A x y) (\<lambda>t. ap A B f x y t) \<Colon>\<^sub>h
      arrow (identity_type A x y)
        (identity_type B (app f x) (app f y))"
  proof (rule arrow_intro[OF pxA])
    fix t
    assume t: "t \<Colon>\<^sub>h identity_type A x y"
    show "ap A B f x y t \<Colon>\<^sub>h identity_type B (app f x) (app f y)"
      by (rule ap_type[OF A B f x y t])
  qed
  have "ap (identity_type A x y) (identity_type B (app f x) (app f y))
      (lambda (identity_type A x y) (\<lambda>t. ap A B f x y t))
      q q' m \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) (app f y))
        (app (lambda (identity_type A x y) (\<lambda>t. ap A B f x y t)) q)
        (app (lambda (identity_type A x y) (\<lambda>t. ap A B f x y t)) q')"
    by (rule ap_type[OF pxA pxB lam q q' m])
  then show "ap_congruence A B f x y q q' m \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) (app f y))
        (ap A B f x y q) (ap A B f x y q')"
    unfolding ap_congruence_def by simp
qed

definition path_whisker_right ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_whisker_right A x y z p p' r m \<equiv>
    identity_ind (identity_type A x y) p
      (\<lambda>p' m. identity_type (identity_type A x z)
        (path_concat A x y z p r) (path_concat A x y z p' r))
      (reflexivity (identity_type A x z) (path_concat A x y z p r))
      p' m"

lemma path_whisker_right_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and z: "z \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type A x y"
    and p': "p' \<Colon>\<^sub>h identity_type A x y"
    and r: "r \<Colon>\<^sub>h identity_type A y z"
    and m: "m \<Colon>\<^sub>h identity_type (identity_type A x y) p p'"
  shows "path_whisker_right A x y z p p' r m \<Colon>\<^sub>h
    identity_type (identity_type A x z)
      (path_concat A x y z p r) (path_concat A x y z p' r)"
  unfolding path_whisker_right_def
proof (rule identity_elim[OF identity_form[OF A x y] p])
  fix w mm
  assume w: "w \<Colon>\<^sub>h identity_type A x y"
  assume mm: "mm \<Colon>\<^sub>h identity_type (identity_type A x y) p w"
  have pr: "path_concat A x y z p r \<Colon>\<^sub>h identity_type A x z"
    by (rule path_concat_type[OF A x y z p r])
  have wr: "path_concat A x y z w r \<Colon>\<^sub>h identity_type A x z"
    by (rule path_concat_type[OF A x y z w r])
  have path_space: "identity_type A x z \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x z])
  show "identity_type (identity_type A x z)
      (path_concat A x y z p r) (path_concat A x y z w r) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF path_space pr wr])
next
  have pr: "path_concat A x y z p r \<Colon>\<^sub>h identity_type A x z"
    by (rule path_concat_type[OF A x y z p r])
  have path_space: "identity_type A x z \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x z])
  show "reflexivity (identity_type A x z) (path_concat A x y z p r) \<Colon>\<^sub>h
      identity_type (identity_type A x z)
        (path_concat A x y z p r) (path_concat A x y z p r)"
    by (rule identity_intro[OF path_space pr])
next
  show "p' \<Colon>\<^sub>h identity_type A x y" by (rule p')
next
  show "m \<Colon>\<^sub>h identity_type (identity_type A x y) p p'" by (rule m)
qed

definition path_inverse_concat_left ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_inverse_concat_left A x y z q s \<equiv>
    path_concat (identity_type A y z)
      (path_concat A y x z (path_inverse A x y q)
        (path_concat A x y z q s))
      (path_concat A y y z
        (path_concat A y x y (path_inverse A x y q) q) s)
      s
      (path_inverse (identity_type A y z)
        (path_concat A y y z
          (path_concat A y x y (path_inverse A x y q) q) s)
        (path_concat A y x z (path_inverse A x y q)
          (path_concat A x y z q s))
        (path_assoc A y x y z (path_inverse A x y q) q s))
      (path_concat (identity_type A y z)
        (path_concat A y y z
          (path_concat A y x y (path_inverse A x y q) q) s)
        (path_concat A y y z (reflexivity A y) s)
        s
        (path_whisker_right A y y z
          (path_concat A y x y (path_inverse A x y q) q)
          (reflexivity A y) s
          (path_inverse_left A x y q))
        (path_left_unit A y z s))"

lemma path_inverse_concat_left_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and z: "z \<Colon>\<^sub>h A"
    and q: "q \<Colon>\<^sub>h identity_type A x y"
    and s: "s \<Colon>\<^sub>h identity_type A y z"
  shows "path_inverse_concat_left A x y z q s \<Colon>\<^sub>h
    identity_type (identity_type A y z)
      (path_concat A y x z (path_inverse A x y q)
        (path_concat A x y z q s)) s"
proof -
  have qinv: "path_inverse A x y q \<Colon>\<^sub>h identity_type A y x"
    by (rule path_inverse_type[OF A x y q])
  have qs: "path_concat A x y z q s \<Colon>\<^sub>h identity_type A x z"
    by (rule path_concat_type[OF A x y z q s])
  have qinv_qs: "path_concat A y x z (path_inverse A x y q)
      (path_concat A x y z q s) \<Colon>\<^sub>h identity_type A y z"
    by (rule path_concat_type[OF A y x z qinv qs])
  have qinv_q: "path_concat A y x y (path_inverse A x y q) q \<Colon>\<^sub>h
      identity_type A y y"
    by (rule path_concat_type[OF A y x y qinv q])
  have qinv_q_s: "path_concat A y y z
      (path_concat A y x y (path_inverse A x y q) q) s \<Colon>\<^sub>h
      identity_type A y z"
    by (rule path_concat_type[OF A y y z qinv_q s])
  have refl_s: "path_concat A y y z (reflexivity A y) s \<Colon>\<^sub>h
      identity_type A y z"
    by (rule path_concat_type[OF A y y z identity_intro[OF A y] s])
  have path_space: "identity_type A y z \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A y z])
  have assoc: "path_assoc A y x y z (path_inverse A x y q) q s \<Colon>\<^sub>h
      identity_type (identity_type A y z)
        (path_concat A y y z
          (path_concat A y x y (path_inverse A x y q) q) s)
        (path_concat A y x z (path_inverse A x y q)
          (path_concat A x y z q s))"
    by (rule path_assoc_type[OF A y x y z qinv q s])
  have assoc_inv: "path_inverse (identity_type A y z)
      (path_concat A y y z
        (path_concat A y x y (path_inverse A x y q) q) s)
      (path_concat A y x z (path_inverse A x y q)
        (path_concat A x y z q s))
      (path_assoc A y x y z (path_inverse A x y q) q s) \<Colon>\<^sub>h
      identity_type (identity_type A y z)
        (path_concat A y x z (path_inverse A x y q)
          (path_concat A x y z q s))
        (path_concat A y y z
          (path_concat A y x y (path_inverse A x y q) q) s)"
    by (rule path_inverse_type[OF path_space qinv_q_s qinv_qs assoc])
  have inv_left: "path_inverse_left A x y q \<Colon>\<^sub>h
      identity_type (identity_type A y y)
        (path_concat A y x y (path_inverse A x y q) q)
        (reflexivity A y)"
    by (rule path_inverse_left_type[OF A x y q])
  have whisk: "path_whisker_right A y y z
      (path_concat A y x y (path_inverse A x y q) q)
      (reflexivity A y) s
      (path_inverse_left A x y q) \<Colon>\<^sub>h
      identity_type (identity_type A y z)
        (path_concat A y y z
          (path_concat A y x y (path_inverse A x y q) q) s)
        (path_concat A y y z (reflexivity A y) s)"
    by (rule path_whisker_right_type[OF A y y z qinv_q
          identity_intro[OF A y] s inv_left])
  have left_unit: "path_left_unit A y z s \<Colon>\<^sub>h
      identity_type (identity_type A y z)
        (path_concat A y y z (reflexivity A y) s) s"
    by (rule path_left_unit_type[OF A y z s])
  have tail: "path_concat (identity_type A y z)
      (path_concat A y y z
        (path_concat A y x y (path_inverse A x y q) q) s)
      (path_concat A y y z (reflexivity A y) s)
      s
      (path_whisker_right A y y z
        (path_concat A y x y (path_inverse A x y q) q)
        (reflexivity A y) s
        (path_inverse_left A x y q))
      (path_left_unit A y z s) \<Colon>\<^sub>h
      identity_type (identity_type A y z)
        (path_concat A y y z
          (path_concat A y x y (path_inverse A x y q) q) s) s"
    by (rule path_concat_type[OF path_space qinv_q_s refl_s s whisk left_unit])
  show "path_inverse_concat_left A x y z q s \<Colon>\<^sub>h
      identity_type (identity_type A y z)
        (path_concat A y x z (path_inverse A x y q)
          (path_concat A x y z q s)) s"
    unfolding path_inverse_concat_left_def
    by (rule path_concat_type[OF path_space qinv_qs qinv_q_s s
          assoc_inv tail])
qed

definition path_concat_inverse_right ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "path_concat_inverse_right A x y z s q \<equiv>
    path_concat (identity_type A x z)
      (path_concat A x y z
        (path_concat A x z y s (path_inverse A y z q)) q)
      (path_concat A x z z s
        (path_concat A z y z (path_inverse A y z q) q))
      s
      (path_assoc A x z y z s (path_inverse A y z q) q)
      (path_whisker_left A x z z s
        (path_concat A z y z (path_inverse A y z q) q)
        (reflexivity A z)
        (path_inverse_left A y z q))"

lemma path_concat_inverse_right_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and x: "x \<Colon>\<^sub>h A"
    and y: "y \<Colon>\<^sub>h A"
    and z: "z \<Colon>\<^sub>h A"
    and s: "s \<Colon>\<^sub>h identity_type A x z"
    and q: "q \<Colon>\<^sub>h identity_type A y z"
  shows "path_concat_inverse_right A x y z s q \<Colon>\<^sub>h
    identity_type (identity_type A x z)
      (path_concat A x y z
        (path_concat A x z y s (path_inverse A y z q)) q) s"
proof -
  have qinv: "path_inverse A y z q \<Colon>\<^sub>h identity_type A z y"
    by (rule path_inverse_type[OF A y z q])
  have sqinv: "path_concat A x z y s (path_inverse A y z q) \<Colon>\<^sub>h
      identity_type A x y"
    by (rule path_concat_type[OF A x z y s qinv])
  have sqinv_q: "path_concat A x y z
      (path_concat A x z y s (path_inverse A y z q)) q \<Colon>\<^sub>h
      identity_type A x z"
    by (rule path_concat_type[OF A x y z sqinv q])
  have qinv_q: "path_concat A z y z (path_inverse A y z q) q \<Colon>\<^sub>h
      identity_type A z z"
    by (rule path_concat_type[OF A z y z qinv q])
  have s_qinvq: "path_concat A x z z s
      (path_concat A z y z (path_inverse A y z q) q) \<Colon>\<^sub>h
      identity_type A x z"
    by (rule path_concat_type[OF A x z z s qinv_q])
  have path_space: "identity_type A x z \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A x z])
  have assoc: "path_assoc A x z y z s (path_inverse A y z q) q \<Colon>\<^sub>h
      identity_type (identity_type A x z)
        (path_concat A x y z
          (path_concat A x z y s (path_inverse A y z q)) q)
        (path_concat A x z z s
          (path_concat A z y z (path_inverse A y z q) q))"
    by (rule path_assoc_type[OF A x z y z s qinv q])
  have inv_left: "path_inverse_left A y z q \<Colon>\<^sub>h
      identity_type (identity_type A z z)
        (path_concat A z y z (path_inverse A y z q) q)
        (reflexivity A z)"
    by (rule path_inverse_left_type[OF A y z q])
  have whisk: "path_whisker_left A x z z s
      (path_concat A z y z (path_inverse A y z q) q)
      (reflexivity A z)
      (path_inverse_left A y z q) \<Colon>\<^sub>h
      identity_type (identity_type A x z)
        (path_concat A x z z s
          (path_concat A z y z (path_inverse A y z q) q)) s"
    using path_whisker_left_type[OF A x z z s qinv_q
      identity_intro[OF A z] inv_left] by simp
  show "path_concat_inverse_right A x y z s q \<Colon>\<^sub>h
      identity_type (identity_type A x z)
        (path_concat A x y z
          (path_concat A x z y s (path_inverse A y z q)) q) s"
    unfolding path_concat_inverse_right_def
    by (rule path_concat_type[OF path_space sqinv_q s_qinvq s assoc whisk])
qed

end
