theory HoTT_Equivalence_Characterization
  imports HoTT_Equivalence
begin

section \<open>Extracting contraction data\<close>

definition contraction_center :: "expr \<Rightarrow> expr" where
  "contraction_center c \<equiv> first c"

definition contraction_paths :: "expr \<Rightarrow> expr" where
  "contraction_paths c \<equiv> second c"

lemma contraction_center_type:
  assumes c: "c \<Colon>\<^sub>h contractible A"
  shows "contraction_center c \<Colon>\<^sub>h A"
  unfolding contraction_center_def
  using c unfolding contractible_def by (rule sigma_first)

lemma contraction_paths_type:
  assumes c: "c \<Colon>\<^sub>h contractible A"
  shows "contraction_paths c \<Colon>\<^sub>h
    pi_type A (\<lambda>x. identity_type A (contraction_center c) x)"
  unfolding contraction_paths_def contraction_center_def
  using c unfolding contractible_def by (rule sigma_second)

definition fiber_center ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "fiber_center A B f c b \<equiv> contraction_center (app c b)"

definition fiber_contraction ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "fiber_contraction A B f c b \<equiv> contraction_paths (app c b)"

lemma contractible_map_component_type:
  assumes c: "c \<Colon>\<^sub>h contractible_map A B f"
    and b: "b \<Colon>\<^sub>h B"
  shows "app c b \<Colon>\<^sub>h contractible (fiber A B f b)"
  using c unfolding contractible_map_def
  by (rule pi_elim[OF _ b])

lemma fiber_center_type:
  assumes c: "c \<Colon>\<^sub>h contractible_map A B f"
    and b: "b \<Colon>\<^sub>h B"
  shows "fiber_center A B f c b \<Colon>\<^sub>h fiber A B f b"
  unfolding fiber_center_def
  by (rule contraction_center_type[OF contractible_map_component_type[OF c b]])

lemma fiber_contraction_type:
  assumes c: "c \<Colon>\<^sub>h contractible_map A B f"
    and b: "b \<Colon>\<^sub>h B"
  shows "fiber_contraction A B f c b \<Colon>\<^sub>h
    pi_type (fiber A B f b)
      (\<lambda>z. identity_type (fiber A B f b)
        (fiber_center A B f c b) z)"
  unfolding fiber_contraction_def fiber_center_def
  by (rule contraction_paths_type[OF contractible_map_component_type[OF c b]])

definition fiber_first_map ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "fiber_first_map A B f b \<equiv>
    lambda (fiber A B f b) (\<lambda>z. first z)"

lemma fiber_first_map_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and b: "b \<Colon>\<^sub>h B"
  shows "fiber_first_map A B f b \<Colon>\<^sub>h arrow (fiber A B f b) A"
proof -
  have fib: "fiber A B f b \<Colon>\<^sub>h universe i"
    by (rule fiber_form[OF A B f b])
  show "fiber_first_map A B f b \<Colon>\<^sub>h
      arrow (fiber A B f b) A"
    unfolding fiber_first_map_def
  proof (rule arrow_intro[OF fib])
    fix z
    assume z: "z \<Colon>\<^sub>h fiber A B f b"
    show "first z \<Colon>\<^sub>h A"
      using z unfolding fiber_def by (rule sigma_first)
  qed
qed

section \<open>Contractible fibers yield a bi-inverse\<close>

definition contractible_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "contractible_inverse A B f c \<equiv>
    lambda B (\<lambda>b. first (fiber_center A B f c b))"

lemma contractible_inverse_type:
  assumes B: "B \<Colon>\<^sub>h universe i"
    and c: "c \<Colon>\<^sub>h contractible_map A B f"
  shows "contractible_inverse A B f c \<Colon>\<^sub>h arrow B A"
  unfolding contractible_inverse_def
proof (rule arrow_intro[OF B])
  fix b
  assume b: "b \<Colon>\<^sub>h B"
  have center: "fiber_center A B f c b \<Colon>\<^sub>h fiber A B f b"
    by (rule fiber_center_type[OF c b])
  show "first (fiber_center A B f c b) \<Colon>\<^sub>h A"
    using center unfolding fiber_def by (rule sigma_first)
qed

definition contractible_right_homotopy ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "contractible_right_homotopy A B f c \<equiv>
    lambda B (\<lambda>b. second (fiber_center A B f c b))"

lemma contractible_right_homotopy_type:
  assumes B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and c: "c \<Colon>\<^sub>h contractible_map A B f"
  shows "contractible_right_homotopy A B f c \<Colon>\<^sub>h
    homotopy B (\<lambda>_. B)
      (compose B A B f (contractible_inverse A B f c))
      (identity_function B)"
  unfolding contractible_right_homotopy_def homotopy_def
proof (rule pi_intro[OF B])
  fix b
  assume b: "b \<Colon>\<^sub>h B"
  have center: "fiber_center A B f c b \<Colon>\<^sub>h fiber A B f b"
    by (rule fiber_center_type[OF c b])
  have path: "second (fiber_center A B f c b) \<Colon>\<^sub>h
      identity_type B
        (app f (first (fiber_center A B f c b))) b"
    using center unfolding fiber_def by (rule sigma_second)
  show "second (fiber_center A B f c b) \<Colon>\<^sub>h
      identity_type B
        (app
          (compose B A B f (contractible_inverse A B f c)) b)
        (app (identity_function B) b)"
    using path unfolding contractible_inverse_def by simp
qed

definition reflexive_fiber_point ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "reflexive_fiber_point A B f a \<equiv>
    pair a (reflexivity B (app f a))"

lemma reflexive_fiber_point_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and a: "a \<Colon>\<^sub>h A"
  shows "reflexive_fiber_point A B f a \<Colon>\<^sub>h
    fiber A B f (app f a)"
proof -
  have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
  have refl: "reflexivity B (app f a) \<Colon>\<^sub>h
      identity_type B (app f a) (app f a)"
    by (rule identity_intro[OF B fa])
  show "reflexive_fiber_point A B f a \<Colon>\<^sub>h
      fiber A B f (app f a)"
    unfolding reflexive_fiber_point_def fiber_def
    by (rule sigma_intro[where B="\<lambda>x. identity_type B (app f x) (app f a)",
          OF a refl])
qed

definition contractible_left_homotopy ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "contractible_left_homotopy A B f c \<equiv>
    lambda A (\<lambda>a.
      ap
        (fiber A B f (app f a))
        A
        (fiber_first_map A B f (app f a))
        (fiber_center A B f c (app f a))
        (reflexive_fiber_point A B f a)
        (app
          (fiber_contraction A B f c (app f a))
          (reflexive_fiber_point A B f a)))"

lemma contractible_left_homotopy_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and c: "c \<Colon>\<^sub>h contractible_map A B f"
  shows "contractible_left_homotopy A B f c \<Colon>\<^sub>h
    homotopy A (\<lambda>_. A)
      (compose A B A (contractible_inverse A B f c) f)
      (identity_function A)"
  unfolding contractible_left_homotopy_def homotopy_def
proof (rule pi_intro[OF A])
  fix a
  assume a: "a \<Colon>\<^sub>h A"
  have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
  have fib: "fiber A B f (app f a) \<Colon>\<^sub>h universe i"
    by (rule fiber_form[OF A B f fa])
  have center: "fiber_center A B f c (app f a) \<Colon>\<^sub>h
      fiber A B f (app f a)"
    by (rule fiber_center_type[OF c fa])
  have point: "reflexive_fiber_point A B f a \<Colon>\<^sub>h
      fiber A B f (app f a)"
    by (rule reflexive_fiber_point_type[OF A B f a])
  have contraction: "fiber_contraction A B f c (app f a) \<Colon>\<^sub>h
      pi_type (fiber A B f (app f a))
        (\<lambda>z. identity_type (fiber A B f (app f a))
          (fiber_center A B f c (app f a)) z)"
    by (rule fiber_contraction_type[OF c fa])
  have center_to_point:
      "app (fiber_contraction A B f c (app f a))
        (reflexive_fiber_point A B f a) \<Colon>\<^sub>h
      identity_type (fiber A B f (app f a))
        (fiber_center A B f c (app f a))
        (reflexive_fiber_point A B f a)"
    by (rule pi_elim[OF contraction point])
  have first_map: "fiber_first_map A B f (app f a) \<Colon>\<^sub>h
      arrow (fiber A B f (app f a)) A"
    by (rule fiber_first_map_type[OF A B f fa])
  have projected:
      "ap (fiber A B f (app f a)) A
        (fiber_first_map A B f (app f a))
        (fiber_center A B f c (app f a))
        (reflexive_fiber_point A B f a)
        (app (fiber_contraction A B f c (app f a))
          (reflexive_fiber_point A B f a)) \<Colon>\<^sub>h
      identity_type A
        (app (fiber_first_map A B f (app f a))
          (fiber_center A B f c (app f a)))
        (app (fiber_first_map A B f (app f a))
          (reflexive_fiber_point A B f a))"
    by (rule ap_type[OF fib A first_map center point center_to_point])
  show "ap (fiber A B f (app f a)) A
        (fiber_first_map A B f (app f a))
        (fiber_center A B f c (app f a))
        (reflexive_fiber_point A B f a)
        (app (fiber_contraction A B f c (app f a))
          (reflexive_fiber_point A B f a)) \<Colon>\<^sub>h
      identity_type A
        (app
          (compose A B A (contractible_inverse A B f c) f) a)
        (app (identity_function A) a)"
    using projected
    unfolding fiber_first_map_def reflexive_fiber_point_def
      contractible_inverse_def by simp
qed

definition contractible_left_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "contractible_left_inverse A B f c \<equiv>
    pair
      (contractible_inverse A B f c)
      (contractible_left_homotopy A B f c)"

lemma contractible_left_inverse_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and c: "c \<Colon>\<^sub>h contractible_map A B f"
  shows "contractible_left_inverse A B f c \<Colon>\<^sub>h
    left_inverse A B f"
  unfolding contractible_left_inverse_def left_inverse_def
proof (rule sigma_intro)
  show "contractible_inverse A B f c \<Colon>\<^sub>h arrow B A"
    by (rule contractible_inverse_type[OF B c])
next
  show "contractible_left_homotopy A B f c \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (contractible_inverse A B f c) f)
        (identity_function A)"
    by (rule contractible_left_homotopy_type[OF A B f c])
qed

definition contractible_right_inverse ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "contractible_right_inverse A B f c \<equiv>
    pair
      (contractible_inverse A B f c)
      (contractible_right_homotopy A B f c)"

lemma contractible_right_inverse_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and c: "c \<Colon>\<^sub>h contractible_map A B f"
  shows "contractible_right_inverse A B f c \<Colon>\<^sub>h
    right_inverse A B f"
  unfolding contractible_right_inverse_def right_inverse_def
proof (rule sigma_intro)
  show "contractible_inverse A B f c \<Colon>\<^sub>h arrow B A"
    by (rule contractible_inverse_type[OF B c])
next
  show "contractible_right_homotopy A B f c \<Colon>\<^sub>h
      homotopy B (\<lambda>_. B)
        (compose B A B f (contractible_inverse A B f c))
        (identity_function B)"
    by (rule contractible_right_homotopy_type[OF B f c])
qed

definition contractible_map_to_biinvertible ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "contractible_map_to_biinvertible A B f c \<equiv>
    pair
      (contractible_left_inverse A B f c)
      (contractible_right_inverse A B f c)"

theorem contractible_map_to_biinvertible_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and c: "c \<Colon>\<^sub>h contractible_map A B f"
  shows "contractible_map_to_biinvertible A B f c \<Colon>\<^sub>h
    biinvertible A B f"
  unfolding contractible_map_to_biinvertible_def biinvertible_def
  by (rule product_intro[OF
        contractible_left_inverse_type[OF A B f c]
        contractible_right_inverse_type[OF A B f c]])

definition contractible_map_to_biinvertible_map ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "contractible_map_to_biinvertible_map A B f \<equiv>
    lambda (contractible_map A B f)
      (\<lambda>c. contractible_map_to_biinvertible A B f c)"

corollary contractible_map_to_biinvertible_map_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
  shows "contractible_map_to_biinvertible_map A B f \<Colon>\<^sub>h
    arrow (contractible_map A B f) (biinvertible A B f)"
  unfolding contractible_map_to_biinvertible_map_def
proof (rule arrow_intro[OF contractible_map_form[OF A B f]])
  fix c
  assume c: "c \<Colon>\<^sub>h contractible_map A B f"
  show "contractible_map_to_biinvertible A B f c \<Colon>\<^sub>h
      biinvertible A B f"
    by (rule contractible_map_to_biinvertible_type[OF A B f c])
qed

section \<open>Equivalences preserve contractibility\<close>

definition equivalence_function :: "expr \<Rightarrow> expr" where
  "equivalence_function e \<equiv> first e"

definition equivalence_biinvertible :: "expr \<Rightarrow> expr" where
  "equivalence_biinvertible e \<equiv> second e"

lemma equivalence_function_type:
  assumes e: "e \<Colon>\<^sub>h equivalence A B"
  shows "equivalence_function e \<Colon>\<^sub>h arrow A B"
  unfolding equivalence_function_def
  using e unfolding equivalence_def by (rule sigma_first)

lemma equivalence_biinvertible_type:
  assumes e: "e \<Colon>\<^sub>h equivalence A B"
  shows "equivalence_biinvertible e \<Colon>\<^sub>h
    biinvertible A B (equivalence_function e)"
  unfolding equivalence_biinvertible_def equivalence_function_def
  using e unfolding equivalence_def by (rule sigma_second)

definition equivalence_contractible_center ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "equivalence_contractible_center A B e c \<equiv>
    app (equivalence_function e) (contraction_center c)"

definition equivalence_contractible_paths ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "equivalence_contractible_paths A B e c \<equiv>
    lambda B (\<lambda>b.
      path_concat B
        (equivalence_contractible_center A B e c)
        (app (equivalence_function e)
          (app
            (right_inverse_function A B
              (equivalence_function e) (equivalence_biinvertible e))
            b))
        b
        (ap A B
          (equivalence_function e)
          (contraction_center c)
          (app
            (right_inverse_function A B
              (equivalence_function e) (equivalence_biinvertible e))
            b)
          (app
            (contraction_paths c)
            (app
              (right_inverse_function A B
                (equivalence_function e) (equivalence_biinvertible e))
              b)))
        (app
          (right_inverse_homotopy A B
            (equivalence_function e) (equivalence_biinvertible e))
          b))"

lemma equivalence_contractible_paths_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and e: "e \<Colon>\<^sub>h equivalence A B"
    and c: "c \<Colon>\<^sub>h contractible A"
  shows "equivalence_contractible_paths A B e c \<Colon>\<^sub>h
    pi_type B (\<lambda>b.
      identity_type B (equivalence_contractible_center A B e c) b)"
  unfolding equivalence_contractible_paths_def
proof (rule pi_intro[OF B])
  fix b
  assume b: "b \<Colon>\<^sub>h B"
  have f: "equivalence_function e \<Colon>\<^sub>h arrow A B"
    by (rule equivalence_function_type[OF e])
  have w: "equivalence_biinvertible e \<Colon>\<^sub>h
      biinvertible A B (equivalence_function e)"
    by (rule equivalence_biinvertible_type[OF e])
  have center_A: "contraction_center c \<Colon>\<^sub>h A"
    by (rule contraction_center_type[OF c])
  have center_B: "app (equivalence_function e) (contraction_center c)
      \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f center_A])
  have inverse: "right_inverse_function A B
      (equivalence_function e) (equivalence_biinvertible e)
      \<Colon>\<^sub>h arrow B A"
    by (rule right_inverse_function_type[OF w])
  have inverse_b: "app
      (right_inverse_function A B
        (equivalence_function e) (equivalence_biinvertible e))
      b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF inverse b])
  have contraction: "contraction_paths c \<Colon>\<^sub>h
      pi_type A (\<lambda>x. identity_type A (contraction_center c) x)"
    by (rule contraction_paths_type[OF c])
  have center_to_inverse: "app (contraction_paths c)
      (app
        (right_inverse_function A B
          (equivalence_function e) (equivalence_biinvertible e))
        b) \<Colon>\<^sub>h
      identity_type A
        (contraction_center c)
        (app
          (right_inverse_function A B
            (equivalence_function e) (equivalence_biinvertible e))
          b)"
    by (rule pi_elim[OF contraction inverse_b])
  have mapped: "ap A B
      (equivalence_function e)
      (contraction_center c)
      (app
        (right_inverse_function A B
          (equivalence_function e) (equivalence_biinvertible e))
        b)
      (app (contraction_paths c)
        (app
          (right_inverse_function A B
            (equivalence_function e) (equivalence_biinvertible e))
          b)) \<Colon>\<^sub>h
      identity_type B
        (app (equivalence_function e) (contraction_center c))
        (app (equivalence_function e)
          (app
            (right_inverse_function A B
              (equivalence_function e) (equivalence_biinvertible e))
            b))"
    by (rule ap_type[OF A B f center_A inverse_b center_to_inverse])
  have inverse_image: "app (equivalence_function e)
      (app
        (right_inverse_function A B
          (equivalence_function e) (equivalence_biinvertible e))
        b) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f inverse_b])
  have right_homotopy: "right_inverse_homotopy A B
      (equivalence_function e) (equivalence_biinvertible e) \<Colon>\<^sub>h
      homotopy B (\<lambda>_. B)
        (compose B A B
          (equivalence_function e)
          (right_inverse_function A B
            (equivalence_function e) (equivalence_biinvertible e)))
        (identity_function B)"
    by (rule right_inverse_homotopy_type[OF w])
  have right_homotopy_pi: "right_inverse_homotopy A B
      (equivalence_function e) (equivalence_biinvertible e) \<Colon>\<^sub>h
      pi_type B (\<lambda>x.
        identity_type B
          (app
            (compose B A B
              (equivalence_function e)
              (right_inverse_function A B
                (equivalence_function e) (equivalence_biinvertible e)))
            x)
          (app (identity_function B) x))"
    using right_homotopy unfolding homotopy_def .
  have right_path_raw: "app
      (right_inverse_homotopy A B
        (equivalence_function e) (equivalence_biinvertible e))
      b \<Colon>\<^sub>h
      identity_type B
        (app
          (compose B A B
            (equivalence_function e)
            (right_inverse_function A B
              (equivalence_function e) (equivalence_biinvertible e)))
          b)
        (app (identity_function B) b)"
    by (rule pi_elim[OF right_homotopy_pi b])
  have right_path: "app
      (right_inverse_homotopy A B
        (equivalence_function e) (equivalence_biinvertible e))
      b \<Colon>\<^sub>h
      identity_type B
        (app (equivalence_function e)
          (app
            (right_inverse_function A B
              (equivalence_function e) (equivalence_biinvertible e))
            b))
        b"
    using right_path_raw by simp
  show "path_concat B
      (equivalence_contractible_center A B e c)
      (app (equivalence_function e)
        (app
          (right_inverse_function A B
            (equivalence_function e) (equivalence_biinvertible e))
          b))
      b
      (ap A B
        (equivalence_function e)
        (contraction_center c)
        (app
          (right_inverse_function A B
            (equivalence_function e) (equivalence_biinvertible e))
          b)
        (app (contraction_paths c)
          (app
            (right_inverse_function A B
              (equivalence_function e) (equivalence_biinvertible e))
            b)))
      (app
        (right_inverse_homotopy A B
          (equivalence_function e) (equivalence_biinvertible e))
        b) \<Colon>\<^sub>h
      identity_type B (equivalence_contractible_center A B e c) b"
    unfolding equivalence_contractible_center_def
    by (rule path_concat_type[OF B center_B inverse_image b mapped right_path])
qed

definition equivalence_preserves_contractible ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "equivalence_preserves_contractible A B e c \<equiv>
    pair
      (equivalence_contractible_center A B e c)
      (equivalence_contractible_paths A B e c)"

theorem equivalence_preserves_contractible_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and e: "e \<Colon>\<^sub>h equivalence A B"
    and c: "c \<Colon>\<^sub>h contractible A"
  shows "equivalence_preserves_contractible A B e c \<Colon>\<^sub>h
    contractible B"
proof -
  have f: "equivalence_function e \<Colon>\<^sub>h arrow A B"
    by (rule equivalence_function_type[OF e])
  have center_A: "contraction_center c \<Colon>\<^sub>h A"
    by (rule contraction_center_type[OF c])
  have center_B: "equivalence_contractible_center A B e c \<Colon>\<^sub>h B"
    unfolding equivalence_contractible_center_def
    by (rule arrow_elim[OF f center_A])
  have paths: "equivalence_contractible_paths A B e c \<Colon>\<^sub>h
      pi_type B (\<lambda>b.
        identity_type B (equivalence_contractible_center A B e c) b)"
    by (rule equivalence_contractible_paths_type[OF A B e c])
  show "equivalence_preserves_contractible A B e c \<Colon>\<^sub>h
      contractible B"
    unfolding equivalence_preserves_contractible_def contractible_def
    by (rule sigma_intro[where B=
          "\<lambda>b. pi_type B
            (\<lambda>x. identity_type B b x)", OF center_B paths])
qed

section \<open>From a bi-inverse to a single quasi-inverse\<close>

text \<open>
  A bi-invertible map carries independent left and right inverses.  We
  first bundle them into a single quasi-inverse: the left inverse
  \<open>g\<close> together with its retraction homotopy \<open>\<eta>\<close> is kept, and a
  compatible section homotopy \<open>f \<circ> g \<sim> id\<close> is manufactured from the
  right inverse via \<open>g \<sim> h\<close>.
\<close>

definition quasi_theta ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "quasi_theta A B f w b \<equiv>
    path_concat A
      (app (left_inverse_function A B f w) b)
      (app (left_inverse_function A B f w)
        (app f (app (right_inverse_function A B f w) b)))
      (app (right_inverse_function A B f w) b)
      (ap B A (left_inverse_function A B f w) b
        (app f (app (right_inverse_function A B f w) b))
        (path_inverse B (app f (app (right_inverse_function A B f w) b)) b
          (app (right_inverse_homotopy A B f w) b)))
      (app (left_inverse_homotopy A B f w)
        (app (right_inverse_function A B f w) b))"

lemma quasi_theta_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and b: "b \<Colon>\<^sub>h B"
  shows "quasi_theta A B f w b \<Colon>\<^sub>h
    identity_type A
      (app (left_inverse_function A B f w) b)
      (app (right_inverse_function A B f w) b)"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have h: "right_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule right_inverse_function_type[OF w])
  have eta: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f w) f)
        (identity_function A)"
    by (rule left_inverse_homotopy_type[OF w])
  have e0: "right_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy B (\<lambda>_. B)
        (compose B A B f (right_inverse_function A B f w))
        (identity_function B)"
    by (rule right_inverse_homotopy_type[OF w])
  have hb: "app (right_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF h b])
  have gb: "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g b])
  have fhb: "app f (app (right_inverse_function A B f w) b) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f hb])
  have glifhb: "app (left_inverse_function A B f w)
      (app f (app (right_inverse_function A B f w) b)) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fhb])
  have e0pi: "right_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type B (\<lambda>x. identity_type B
        (app (compose B A B f (right_inverse_function A B f w)) x)
        (app (identity_function B) x))"
    using e0 unfolding homotopy_def .
  have e0b: "app (right_inverse_homotopy A B f w) b \<Colon>\<^sub>h
      identity_type B (app f (app (right_inverse_function A B f w) b)) b"
    using pi_elim[OF e0pi b] by simp
  have e0b_inv: "path_inverse B
      (app f (app (right_inverse_function A B f w) b)) b
      (app (right_inverse_homotopy A B f w) b) \<Colon>\<^sub>h
      identity_type B b (app f (app (right_inverse_function A B f w) b))"
    by (rule path_inverse_type[OF B fhb b e0b])
  have ap_g: "ap B A (left_inverse_function A B f w) b
      (app f (app (right_inverse_function A B f w) b))
      (path_inverse B (app f (app (right_inverse_function A B f w) b)) b
        (app (right_inverse_homotopy A B f w) b)) \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w) b)
        (app (left_inverse_function A B f w)
          (app f (app (right_inverse_function A B f w) b)))"
    by (rule ap_type[OF B A g b fhb e0b_inv])
  have etapi: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type A (\<lambda>x. identity_type A
        (app (compose A B A (left_inverse_function A B f w) f) x)
        (app (identity_function A) x))"
    using eta unfolding homotopy_def .
  have eta_hb: "app (left_inverse_homotopy A B f w)
      (app (right_inverse_function A B f w) b) \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w)
          (app f (app (right_inverse_function A B f w) b)))
        (app (right_inverse_function A B f w) b)"
    using pi_elim[OF etapi hb] by simp
  show "quasi_theta A B f w b \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w) b)
        (app (right_inverse_function A B f w) b)"
    unfolding quasi_theta_def
    by (rule path_concat_type[OF A gb glifhb hb ap_g eta_hb])
qed

definition quasi_rho_point ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "quasi_rho_point A B f w b \<equiv>
    path_concat B
      (app f (app (left_inverse_function A B f w) b))
      (app f (app (right_inverse_function A B f w) b))
      b
      (ap A B f
        (app (left_inverse_function A B f w) b)
        (app (right_inverse_function A B f w) b)
        (quasi_theta A B f w b))
      (app (right_inverse_homotopy A B f w) b)"

lemma quasi_rho_point_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and b: "b \<Colon>\<^sub>h B"
  shows "quasi_rho_point A B f w b \<Colon>\<^sub>h
    identity_type B (app f (app (left_inverse_function A B f w) b)) b"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have h: "right_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule right_inverse_function_type[OF w])
  have e0: "right_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy B (\<lambda>_. B)
        (compose B A B f (right_inverse_function A B f w))
        (identity_function B)"
    by (rule right_inverse_homotopy_type[OF w])
  have hb: "app (right_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF h b])
  have gb: "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g b])
  have fgb: "app f (app (left_inverse_function A B f w) b) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gb])
  have fhb: "app f (app (right_inverse_function A B f w) b) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f hb])
  have theta: "quasi_theta A B f w b \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w) b)
        (app (right_inverse_function A B f w) b)"
    by (rule quasi_theta_type[OF A B f w b])
  have ap_f_theta: "ap A B f
      (app (left_inverse_function A B f w) b)
      (app (right_inverse_function A B f w) b)
      (quasi_theta A B f w b) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w) b))
        (app f (app (right_inverse_function A B f w) b))"
    by (rule ap_type[OF A B f gb hb theta])
  have e0pi: "right_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type B (\<lambda>x. identity_type B
        (app (compose B A B f (right_inverse_function A B f w)) x)
        (app (identity_function B) x))"
    using e0 unfolding homotopy_def .
  have e0b: "app (right_inverse_homotopy A B f w) b \<Colon>\<^sub>h
      identity_type B (app f (app (right_inverse_function A B f w) b)) b"
    using pi_elim[OF e0pi b] by simp
  show "quasi_rho_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    unfolding quasi_rho_point_def
    by (rule path_concat_type[OF B fgb fhb b ap_f_theta e0b])
qed

definition quasi_rho ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "quasi_rho A B f w \<equiv>
    lambda B (\<lambda>b. quasi_rho_point A B f w b)"

lemma quasi_rho_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "quasi_rho A B f w \<Colon>\<^sub>h
    homotopy B (\<lambda>_. B)
      (compose B A B f (left_inverse_function A B f w))
      (identity_function B)"
  unfolding quasi_rho_def homotopy_def
proof (rule pi_intro[OF B])
  fix b
  assume b: "b \<Colon>\<^sub>h B"
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have point: "quasi_rho_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule quasi_rho_point_type[OF A B f w b])
  show "quasi_rho_point A B f w b \<Colon>\<^sub>h
      identity_type B
        (app (compose B A B f (left_inverse_function A B f w)) b)
        (app (identity_function B) b)"
    using point by simp
qed

lemma quasi_rho_beta [simp]:
  "app (quasi_rho A B f w) b \<equiv> quasi_rho_point A B f w b"
  unfolding quasi_rho_def by simp

section \<open>Coherent (half-adjoint) inverse data\<close>

text \<open>
  The quasi-inverse \<open>(g, \<eta>, \<rho>)\<close> is upgraded to half-adjoint data by the
  standard eta trick: a coherent section homotopy \<open>\<epsilon>\<close> is defined so that
  the triangle identity \<open>ap f (\<eta> a) = \<epsilon> (f a)\<close> holds.
\<close>

definition coherent_eps_point ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "coherent_eps_point A B f w b \<equiv>
    path_concat B
      (app f (app (left_inverse_function A B f w) b))
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) b))))
      b
      (path_inverse B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) b))))
        (app f (app (left_inverse_function A B f w) b))
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) b))))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) b))))
        (app f (app (left_inverse_function A B f w) b))
        b
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) b)))
          (app (left_inverse_function A B f w) b)
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) b)))
        (quasi_rho_point A B f w b))"

lemma coherent_eps_point_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and b: "b \<Colon>\<^sub>h B"
  shows "coherent_eps_point A B f w b \<Colon>\<^sub>h
    identity_type B (app f (app (left_inverse_function A B f w) b)) b"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have eta: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f w) f)
        (identity_function A)"
    by (rule left_inverse_homotopy_type[OF w])
  have gb: "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g b])
  have fgb: "app f (app (left_inverse_function A B f w) b) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gb])
  have gfgb: "app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) b)) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fgb])
  have fgfgb: "app f (app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) b))) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfgb])
  have rho_b: "quasi_rho_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule quasi_rho_point_type[OF A B f w b])
  have rho_fgb: "quasi_rho_point A B f w
      (app f (app (left_inverse_function A B f w) b)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) b))))
        (app f (app (left_inverse_function A B f w) b))"
    by (rule quasi_rho_point_type[OF A B f w fgb])
  have rho_fgb_inv: "path_inverse B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) b))))
      (app f (app (left_inverse_function A B f w) b))
      (quasi_rho_point A B f w
        (app f (app (left_inverse_function A B f w) b))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w) b))
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) b))))"
    by (rule path_inverse_type[OF B fgfgb fgb rho_fgb])
  have etapi: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type A (\<lambda>x. identity_type A
        (app (compose A B A (left_inverse_function A B f w) f) x)
        (app (identity_function A) x))"
    using eta unfolding homotopy_def .
  have eta_gb: "app (left_inverse_homotopy A B f w)
      (app (left_inverse_function A B f w) b) \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) b)))
        (app (left_inverse_function A B f w) b)"
    using pi_elim[OF etapi gb] by simp
  have apf_eta: "ap A B f
      (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) b)))
      (app (left_inverse_function A B f w) b)
      (app (left_inverse_homotopy A B f w)
        (app (left_inverse_function A B f w) b)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) b))))
        (app f (app (left_inverse_function A B f w) b))"
    by (rule ap_type[OF A B f gfgb gb eta_gb])
  have inner: "path_concat B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) b))))
      (app f (app (left_inverse_function A B f w) b))
      b
      (ap A B f
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) b)))
        (app (left_inverse_function A B f w) b)
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) b)))
      (quasi_rho_point A B f w b) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) b))))
        b"
    by (rule path_concat_type[OF B fgfgb fgb b apf_eta rho_b])
  show "coherent_eps_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    unfolding coherent_eps_point_def
    by (rule path_concat_type[OF B fgb fgfgb b rho_fgb_inv inner])
qed

text \<open>
  Auxiliary two-cell \<open>coherent_D\<close>: the functorial image
  \<open>ap (f \<circ> g) (ap f (\<eta> a))\<close> agrees with \<open>ap f (\<eta> (g (f a)))\<close>.  This
  uses the self-action \<open>homotopy_self\<close> of \<open>\<eta>\<close> transported through \<open>ap f\<close>.
\<close>

definition coherent_D ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "coherent_D A B f w a \<equiv>
    path_concat
      (identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a))))
      (ap B B (compose B A B f (left_inverse_function A B f w))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (ap A B f
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))
        (ap B A (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a))))
      (ap A B f
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a))))
      (ap_compose B A B f (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (ap_congruence A B f
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))
        (ap B A (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a)))
        (path_concat
          (identity_type A
            (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a))))
            (app (left_inverse_function A B f w) (app f a)))
          (ap B A (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a)))
          (ap A A (compose A B A (left_inverse_function A B f w) f)
            (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a)))
          (path_inverse
            (identity_type A
              (app (left_inverse_function A B f w)
                (app f (app (left_inverse_function A B f w) (app f a))))
              (app (left_inverse_function A B f w) (app f a)))
            (ap A A (compose A B A (left_inverse_function A B f w) f)
              (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a))
            (ap B A (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))
              (app f a)
              (ap A B f (app (left_inverse_function A B f w) (app f a)) a
                (app (left_inverse_homotopy A B f w) a)))
            (ap_compose A B A (left_inverse_function A B f w) f
              (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a)))
          (homotopy_self A (compose A B A (left_inverse_function A B f w) f)
            (left_inverse_homotopy A B f w) a)))"

lemma coherent_D_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and a: "a \<Colon>\<^sub>h A"
  shows "coherent_D A B f w a \<Colon>\<^sub>h
    identity_type
      (identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a))))
      (ap B B (compose B A B f (left_inverse_function A B f w))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (ap A B f
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a))))"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have eta: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f w) f)
        (identity_function A)"
    by (rule left_inverse_homotopy_type[OF w])
  have gf: "compose A B A (left_inverse_function A B f w) f \<Colon>\<^sub>h arrow A A"
    by (rule compose_type[OF A f g])
  have fg: "compose B A B f (left_inverse_function A B f w) \<Colon>\<^sub>h arrow B B"
    by (rule compose_type[OF B g f])
  have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
  have gfa: "app (left_inverse_function A B f w) (app f a) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fa])
  have fgfa: "app f (app (left_inverse_function A B f w) (app f a)) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfa])
  have gfgfa: "app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fgfa])
  have fgfgfa: "app f (app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a)))) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfgfa])
  have etapi: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type A (\<lambda>x. identity_type A
        (app (compose A B A (left_inverse_function A B f w) f) x)
        (app (identity_function A) x))"
    using eta unfolding homotopy_def .
  have eta_a: "app (left_inverse_homotopy A B f w) a \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) (app f a)) a"
    using pi_elim[OF etapi a] by simp
  have s: "ap A B f (app (left_inverse_function A B f w) (app f a)) a
      (app (left_inverse_homotopy A B f w) a) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    by (rule ap_type[OF A B f gfa a eta_a])
  have Lp: "ap B B (compose B A B f (left_inverse_function A B f w))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    using ap_type[OF B B fg fgfa fa s] by simp
  have apg_s: "ap B A (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))"
    by (rule ap_type[OF B A g fgfa fa s])
  have eta_gfa: "app (left_inverse_homotopy A B f w)
      (app (left_inverse_function A B f w) (app f a)) \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))"
    using pi_elim[OF etapi gfa] by simp
  have mid: "ap A B f
      (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a))))
      (app (left_inverse_function A B f w) (app f a))
      (ap B A (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    by (rule ap_type[OF A B f gfgfa gfa apg_s])
  have apfeta: "ap A B f
      (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a))))
      (app (left_inverse_function A B f w) (app f a))
      (app (left_inverse_homotopy A B f w)
        (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    by (rule ap_type[OF A B f gfgfa gfa eta_gfa])
  have gspace: "identity_type A
      (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a))))
      (app (left_inverse_function A B f w) (app f a)) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF A gfgfa gfa])
  have apgf: "ap A A (compose A B A (left_inverse_function A B f w) f)
      (app (left_inverse_function A B f w) (app f a)) a
      (app (left_inverse_homotopy A B f w) a) \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))"
    using ap_type[OF A A gf gfa a eta_a] by simp
  have AC2: "ap_compose A B A (left_inverse_function A B f w) f
      (app (left_inverse_function A B f w) (app f a)) a
      (app (left_inverse_homotopy A B f w) a) \<Colon>\<^sub>h
      identity_type
        (identity_type A
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a)))
        (ap A A (compose A B A (left_inverse_function A B f w) f)
          (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))
        (ap B A (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))"
    by (rule ap_compose_type[OF A B A f g gfa a eta_a])
  have AC2inv: "path_inverse
      (identity_type A
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a)))
      (ap A A (compose A B A (left_inverse_function A B f w) f)
        (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a))
      (ap B A (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (ap_compose A B A (left_inverse_function A B f w) f
        (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type
        (identity_type A
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a)))
        (ap B A (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (ap A A (compose A B A (left_inverse_function A B f w) f)
          (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))"
    by (rule path_inverse_type[OF gspace apgf apg_s AC2])
  have SELF: "homotopy_self A (compose A B A (left_inverse_function A B f w) f)
      (left_inverse_homotopy A B f w) a \<Colon>\<^sub>h
      identity_type
        (identity_type A
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a)))
        (ap A A (compose A B A (left_inverse_function A B f w) f)
          (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a)))"
    using homotopy_self_type[OF A gf eta a] by simp
  have GS: "path_concat
      (identity_type A
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a)))
      (ap B A (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (ap A A (compose A B A (left_inverse_function A B f w) f)
        (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a))
      (app (left_inverse_homotopy A B f w)
        (app (left_inverse_function A B f w) (app f a)))
      (path_inverse
        (identity_type A
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a)))
        (ap A A (compose A B A (left_inverse_function A B f w) f)
          (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))
        (ap B A (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (ap_compose A B A (left_inverse_function A B f w) f
          (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (homotopy_self A (compose A B A (left_inverse_function A B f w) f)
        (left_inverse_homotopy A B f w) a) \<Colon>\<^sub>h
      identity_type
        (identity_type A
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a)))
        (ap B A (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a)))"
    by (rule path_concat_type[OF gspace apg_s apgf eta_gfa AC2inv SELF])
  have space: "identity_type B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fgfgfa fgfa])
  have AC1: "ap_compose B A B f (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap B B (compose B A B f (left_inverse_function A B f w))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (ap B A (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a))))"
    by (rule ap_compose_type[OF B A B g f fgfa fa s])
  have APGS: "ap_congruence A B f
      (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a))))
      (app (left_inverse_function A B f w) (app f a))
      (ap B A (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (app (left_inverse_homotopy A B f w)
        (app (left_inverse_function A B f w) (app f a)))
      (path_concat
        (identity_type A
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a)))
        (ap B A (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (ap A A (compose A B A (left_inverse_function A B f w) f)
          (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a)))
        (path_inverse
          (identity_type A
            (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a))))
            (app (left_inverse_function A B f w) (app f a)))
          (ap A A (compose A B A (left_inverse_function A B f w) f)
            (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a))
          (ap B A (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a)))
          (ap_compose A B A (left_inverse_function A B f w) f
            (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (homotopy_self A (compose A B A (left_inverse_function A B f w) f)
          (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (ap B A (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a))))
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a))))"
    by (rule ap_congruence_type[OF A B f gfgfa gfa apg_s eta_gfa GS])
  show "coherent_D A B f w a \<Colon>\<^sub>h
      identity_type
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap B B (compose B A B f (left_inverse_function A B f w))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a))))"
    unfolding coherent_D_def
    by (rule path_concat_type[OF space Lp mid apfeta AC1 APGS])
qed

text \<open>
  Auxiliary two-cell \<open>coherent_E\<close>: the naturality square of \<open>\<rho>\<close> at the
  path \<open>ap f (\<eta> a)\<close>.
\<close>

definition coherent_E ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "coherent_E A B f w a \<equiv>
    path_concat
      (identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap B B (compose B A B f (left_inverse_function A B f w))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (quasi_rho_point A B f w (app f a)))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap B B (identity_function B)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a))))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (homotopy_naturality B B
        (compose B A B f (left_inverse_function A B f w))
        (identity_function B)
        (quasi_rho A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (path_whisker_left B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap B B (identity_function B)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))
        (ap_identity B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a))))"

lemma coherent_E_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and a: "a \<Colon>\<^sub>h A"
  shows "coherent_E A B f w a \<Colon>\<^sub>h
    identity_type
      (identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap B B (compose B A B f (left_inverse_function A B f w))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (quasi_rho_point A B f w (app f a)))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have eta: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f w) f)
        (identity_function A)"
    by (rule left_inverse_homotopy_type[OF w])
  have fg: "compose B A B f (left_inverse_function A B f w) \<Colon>\<^sub>h arrow B B"
    by (rule compose_type[OF B g f])
  have idB: "identity_function B \<Colon>\<^sub>h arrow B B"
    by (rule identity_function_type[OF B])
  have rho_hom: "quasi_rho A B f w \<Colon>\<^sub>h
      homotopy B (\<lambda>_. B)
        (compose B A B f (left_inverse_function A B f w))
        (identity_function B)"
    by (rule quasi_rho_type[OF A B f w])
  have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
  have gfa: "app (left_inverse_function A B f w) (app f a) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fa])
  have fgfa: "app f (app (left_inverse_function A B f w) (app f a)) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfa])
  have gfgfa: "app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fgfa])
  have fgfgfa: "app f (app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a)))) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfgfa])
  have etapi: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type A (\<lambda>x. identity_type A
        (app (compose A B A (left_inverse_function A B f w) f) x)
        (app (identity_function A) x))"
    using eta unfolding homotopy_def .
  have eta_a: "app (left_inverse_homotopy A B f w) a \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) (app f a)) a"
    using pi_elim[OF etapi a] by simp
  have s: "ap A B f (app (left_inverse_function A B f w) (app f a)) a
      (app (left_inverse_homotopy A B f w) a) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    by (rule ap_type[OF A B f gfa a eta_a])
  have Lp: "ap B B (compose B A B f (left_inverse_function A B f w))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    using ap_type[OF B B fg fgfa fa s] by simp
  have rho_fa: "quasi_rho_point A B f w (app f a) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    by (rule quasi_rho_point_type[OF A B f w fa])
  have rho_fgfa: "quasi_rho_point A B f w
      (app f (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    by (rule quasi_rho_point_type[OF A B f w fgfa])
  have ap_idB_s: "ap B B (identity_function B)
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    using ap_type[OF B B idB fgfa fa s] by simp
  have NAT: "homotopy_naturality B B
      (compose B A B f (left_inverse_function A B f w))
      (identity_function B)
      (quasi_rho A B f w)
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap B B (compose B A B f (left_inverse_function A B f w))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a)))
          (quasi_rho_point A B f w (app f a)))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap B B (identity_function B)
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a))))"
    using homotopy_naturality_type[OF B B fg idB rho_hom fgfa fa s] by simp
  have AI_E: "ap_identity B
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a))
        (ap B B (identity_function B)
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))"
    by (rule ap_identity_type[OF B fgfa fa s])
  have WH_E: "path_whisker_left B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (quasi_rho_point A B f w
        (app f (app (left_inverse_function A B f w) (app f a))))
      (ap B B (identity_function B)
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a))
      (ap_identity B
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))) \<Colon>\<^sub>h
      identity_type
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap B B (identity_function B)
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a))))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))"
    by (rule path_whisker_left_type[OF B fgfgfa fgfa fa rho_fgfa ap_idB_s s AI_E])
  have Espace: "identity_type B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f a) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fgfgfa fa])
  have Lrhofa: "path_concat B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap B B (compose B A B f (left_inverse_function A B f w))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (quasi_rho_point A B f w (app f a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)"
    by (rule path_concat_type[OF B fgfgfa fgfa fa Lp rho_fa])
  have midE: "path_concat B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (quasi_rho_point A B f w
        (app f (app (left_inverse_function A B f w) (app f a))))
      (ap B B (identity_function B)
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)"
    by (rule path_concat_type[OF B fgfgfa fgfa fa rho_fgfa ap_idB_s])
  have rhofgfaS: "path_concat B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (quasi_rho_point A B f w
        (app f (app (left_inverse_function A B f w) (app f a))))
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)"
    by (rule path_concat_type[OF B fgfgfa fgfa fa rho_fgfa s])
  show "coherent_E A B f w a \<Colon>\<^sub>h
      identity_type
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap B B (compose B A B f (left_inverse_function A B f w))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a)))
          (quasi_rho_point A B f w (app f a)))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))"
    unfolding coherent_E_def
    by (rule path_concat_type[OF Espace Lrhofa midE rhofgfaS NAT WH_E])
qed

text \<open>
  Combining \<open>coherent_D\<close> and \<open>coherent_E\<close> gives the inner naturality cell
  \<open>ap f (\<eta> (g (f a))) \<cdot> \<rho> (f a) = \<rho> (f (g (f a))) \<cdot> ap f (\<eta> a)\<close>.
\<close>

definition coherent_inner ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "coherent_inner A B f w a \<equiv>
    path_concat
      (identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a))))
        (quasi_rho_point A B f w (app f a)))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap B B (compose B A B f (left_inverse_function A B f w))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (quasi_rho_point A B f w (app f a)))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (path_whisker_right B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a))))
        (ap B B (compose B A B f (left_inverse_function A B f w))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (quasi_rho_point A B f w (app f a))
        (path_inverse
          (identity_type B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap B B (compose B A B f (left_inverse_function A B f w))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a)))
          (ap A B f
            (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a))))
            (app (left_inverse_function A B f w) (app f a))
            (app (left_inverse_homotopy A B f w)
              (app (left_inverse_function A B f w) (app f a))))
          (coherent_D A B f w a)))
      (coherent_E A B f w a)"

lemma coherent_inner_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and a: "a \<Colon>\<^sub>h A"
  shows "coherent_inner A B f w a \<Colon>\<^sub>h
    identity_type
      (identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a))))
        (quasi_rho_point A B f w (app f a)))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have eta: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f w) f)
        (identity_function A)"
    by (rule left_inverse_homotopy_type[OF w])
  have fg: "compose B A B f (left_inverse_function A B f w) \<Colon>\<^sub>h arrow B B"
    by (rule compose_type[OF B g f])
  have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
  have gfa: "app (left_inverse_function A B f w) (app f a) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fa])
  have fgfa: "app f (app (left_inverse_function A B f w) (app f a)) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfa])
  have gfgfa: "app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fgfa])
  have fgfgfa: "app f (app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a)))) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfgfa])
  have etapi: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type A (\<lambda>x. identity_type A
        (app (compose A B A (left_inverse_function A B f w) f) x)
        (app (identity_function A) x))"
    using eta unfolding homotopy_def .
  have eta_a: "app (left_inverse_homotopy A B f w) a \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) (app f a)) a"
    using pi_elim[OF etapi a] by simp
  have eta_gfa: "app (left_inverse_homotopy A B f w)
      (app (left_inverse_function A B f w) (app f a)) \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))"
    using pi_elim[OF etapi gfa] by simp
  have s: "ap A B f (app (left_inverse_function A B f w) (app f a)) a
      (app (left_inverse_homotopy A B f w) a) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    by (rule ap_type[OF A B f gfa a eta_a])
  have Lp: "ap B B (compose B A B f (left_inverse_function A B f w))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    using ap_type[OF B B fg fgfa fa s] by simp
  have apfeta: "ap A B f
      (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a))))
      (app (left_inverse_function A B f w) (app f a))
      (app (left_inverse_homotopy A B f w)
        (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    by (rule ap_type[OF A B f gfgfa gfa eta_gfa])
  have rho_fa: "quasi_rho_point A B f w (app f a) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    by (rule quasi_rho_point_type[OF A B f w fa])
  have rho_fgfa: "quasi_rho_point A B f w
      (app f (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    by (rule quasi_rho_point_type[OF A B f w fgfa])
  have space_D: "identity_type B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fgfgfa fgfa])
  have Dinv: "path_inverse
      (identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a))))
      (ap B B (compose B A B f (left_inverse_function A B f w))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (ap A B f
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a))))
      (coherent_D A B f w a) \<Colon>\<^sub>h
      identity_type
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a))))
        (ap B B (compose B A B f (left_inverse_function A B f w))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))"
    by (rule path_inverse_type[OF space_D Lp apfeta coherent_D_type[OF A B f w a]])
  have WD: "path_whisker_right B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a))))
      (ap B B (compose B A B f (left_inverse_function A B f w))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (quasi_rho_point A B f w (app f a))
      (path_inverse
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap B B (compose B A B f (left_inverse_function A B f w))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a))))
        (coherent_D A B f w a)) \<Colon>\<^sub>h
      identity_type
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f
            (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a))))
            (app (left_inverse_function A B f w) (app f a))
            (app (left_inverse_homotopy A B f w)
              (app (left_inverse_function A B f w) (app f a))))
          (quasi_rho_point A B f w (app f a)))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap B B (compose B A B f (left_inverse_function A B f w))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a)))
          (quasi_rho_point A B f w (app f a)))"
    by (rule path_whisker_right_type[OF B fgfgfa fgfa fa apfeta Lp rho_fa Dinv])
  have innerspace: "identity_type B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f a) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fgfgfa fa])
  have apfeta_rhofa: "path_concat B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a))))
      (quasi_rho_point A B f w (app f a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)"
    by (rule path_concat_type[OF B fgfgfa fgfa fa apfeta rho_fa])
  have L_rhofa: "path_concat B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap B B (compose B A B f (left_inverse_function A B f w))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (quasi_rho_point A B f w (app f a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)"
    by (rule path_concat_type[OF B fgfgfa fgfa fa Lp rho_fa])
  have rhofgfa_s: "path_concat B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (quasi_rho_point A B f w
        (app f (app (left_inverse_function A B f w) (app f a))))
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)"
    by (rule path_concat_type[OF B fgfgfa fgfa fa rho_fgfa s])
  show "coherent_inner A B f w a \<Colon>\<^sub>h
      identity_type
        (identity_type B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f
            (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a))))
            (app (left_inverse_function A B f w) (app f a))
            (app (left_inverse_homotopy A B f w)
              (app (left_inverse_function A B f w) (app f a))))
          (quasi_rho_point A B f w (app f a)))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))"
    unfolding coherent_inner_def
    by (rule path_concat_type[OF innerspace apfeta_rhofa L_rhofa rhofgfa_s
          WD coherent_E_type[OF A B f w a]])
qed

text \<open>
  The half-adjoint triangle identity: \<open>ap f (\<eta> a) = \<epsilon> (f a)\<close>.
\<close>

definition coherent_tau ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "coherent_tau A B f w a \<equiv>
    path_inverse
      (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a))
      (path_concat B
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)
        (path_inverse B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a)))))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f
            (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a))))
            (app (left_inverse_function A B f w) (app f a))
            (app (left_inverse_homotopy A B f w)
              (app (left_inverse_function A B f w) (app f a))))
          (quasi_rho_point A B f w (app f a))))
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a))
      (path_concat
        (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f
              (app (left_inverse_function A B f w)
                (app f (app (left_inverse_function A B f w) (app f a))))
              (app (left_inverse_function A B f w) (app f a))
              (app (left_inverse_homotopy A B f w)
                (app (left_inverse_function A B f w) (app f a))))
            (quasi_rho_point A B f w (app f a))))
        (path_concat B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a))))
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))
        (path_whisker_left B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f
              (app (left_inverse_function A B f w)
                (app f (app (left_inverse_function A B f w) (app f a))))
              (app (left_inverse_function A B f w) (app f a))
              (app (left_inverse_homotopy A B f w)
                (app (left_inverse_function A B f w) (app f a))))
            (quasi_rho_point A B f w (app f a)))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a))))
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a)))
          (coherent_inner A B f w a))
        (path_inverse_concat_left B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a))))"

lemma coherent_tau_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and a: "a \<Colon>\<^sub>h A"
  shows "coherent_tau A B f w a \<Colon>\<^sub>h
    identity_type
      (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a))
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a))
      (coherent_eps_point A B f w (app f a))"
  unfolding coherent_tau_def coherent_eps_point_def
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have eta: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f w) f)
        (identity_function A)"
    by (rule left_inverse_homotopy_type[OF w])
  have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
  have gfa: "app (left_inverse_function A B f w) (app f a) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fa])
  have fgfa: "app f (app (left_inverse_function A B f w) (app f a)) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfa])
  have gfgfa: "app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fgfa])
  have fgfgfa: "app f (app (left_inverse_function A B f w)
      (app f (app (left_inverse_function A B f w) (app f a)))) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfgfa])
  have etapi: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type A (\<lambda>x. identity_type A
        (app (compose A B A (left_inverse_function A B f w) f) x)
        (app (identity_function A) x))"
    using eta unfolding homotopy_def .
  have eta_a: "app (left_inverse_homotopy A B f w) a \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) (app f a)) a"
    using pi_elim[OF etapi a] by simp
  have eta_gfa: "app (left_inverse_homotopy A B f w)
      (app (left_inverse_function A B f w) (app f a)) \<Colon>\<^sub>h
      identity_type A
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))"
    using pi_elim[OF etapi gfa] by simp
  have s: "ap A B f (app (left_inverse_function A B f w) (app f a)) a
      (app (left_inverse_homotopy A B f w) a) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    by (rule ap_type[OF A B f gfa a eta_a])
  have apfeta: "ap A B f
      (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a))))
      (app (left_inverse_function A B f w) (app f a))
      (app (left_inverse_homotopy A B f w)
        (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    by (rule ap_type[OF A B f gfgfa gfa eta_gfa])
  have rho_fa: "quasi_rho_point A B f w (app f a) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    by (rule quasi_rho_point_type[OF A B f w fa])
  have rho_fgfa: "quasi_rho_point A B f w
      (app f (app (left_inverse_function A B f w) (app f a))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))"
    by (rule quasi_rho_point_type[OF A B f w fgfa])
  have rho_fgfa_inv: "path_inverse B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (quasi_rho_point A B f w
        (app f (app (left_inverse_function A B f w) (app f a)))) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))"
    by (rule path_inverse_type[OF B fgfgfa fgfa rho_fgfa])
  have SPACE: "identity_type B
      (app f (app (left_inverse_function A B f w) (app f a))) (app f a)
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fgfa fa])
  have innerE: "path_concat B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (ap A B f
        (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a))))
        (app (left_inverse_function A B f w) (app f a))
        (app (left_inverse_homotopy A B f w)
          (app (left_inverse_function A B f w) (app f a))))
      (quasi_rho_point A B f w (app f a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)"
    by (rule path_concat_type[OF B fgfgfa fgfa fa apfeta rho_fa])
  have rhofgfa_s: "path_concat B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (quasi_rho_point A B f w
        (app f (app (left_inverse_function A B f w) (app f a))))
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)"
    by (rule path_concat_type[OF B fgfgfa fgfa fa rho_fgfa s])
  have eps: "path_concat B
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f a)
      (path_inverse B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a)))))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a))))
        (quasi_rho_point A B f w (app f a))) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    by (rule path_concat_type[OF B fgfa fgfgfa fa rho_fgfa_inv innerE])
  have MID: "path_concat B
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f a)
      (path_inverse B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a)))))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)"
    by (rule path_concat_type[OF B fgfa fgfgfa fa rho_fgfa_inv rhofgfa_s])
  have WL: "path_whisker_left B
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f a)
      (path_inverse B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a)))))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (ap A B f
          (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a))))
          (app (left_inverse_function A B f w) (app f a))
          (app (left_inverse_homotopy A B f w)
            (app (left_inverse_function A B f w) (app f a))))
        (quasi_rho_point A B f w (app f a)))
      (path_concat B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a)))
      (coherent_inner A B f w a) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f
              (app (left_inverse_function A B f w)
                (app f (app (left_inverse_function A B f w) (app f a))))
              (app (left_inverse_function A B f w) (app f a))
              (app (left_inverse_homotopy A B f w)
                (app (left_inverse_function A B f w) (app f a))))
            (quasi_rho_point A B f w (app f a))))
        (path_concat B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a))))
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a))))"
    by (rule path_whisker_left_type[OF B fgfa fgfgfa fa rho_fgfa_inv
          innerE rhofgfa_s coherent_inner_type[OF A B f w a]])
  have CANCEL: "path_inverse_concat_left B
      (app f (app (left_inverse_function A B f w)
        (app f (app (left_inverse_function A B f w) (app f a)))))
      (app f (app (left_inverse_function A B f w) (app f a)))
      (app f a)
      (quasi_rho_point A B f w
        (app f (app (left_inverse_function A B f w) (app f a))))
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a)) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a))))
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))"
    by (rule path_inverse_concat_left_type[OF B fgfgfa fgfa fa rho_fgfa s])
  have EQ: "path_concat
      (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a))
      (path_concat B
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)
        (path_inverse B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a)))))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f
            (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a))))
            (app (left_inverse_function A B f w) (app f a))
            (app (left_inverse_homotopy A B f w)
              (app (left_inverse_function A B f w) (app f a))))
          (quasi_rho_point A B f w (app f a))))
      (path_concat B
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)
        (path_inverse B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a)))))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a))))
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a))
      (path_whisker_left B
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)
        (path_inverse B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a)))))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f
            (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a))))
            (app (left_inverse_function A B f w) (app f a))
            (app (left_inverse_homotopy A B f w)
              (app (left_inverse_function A B f w) (app f a))))
          (quasi_rho_point A B f w (app f a)))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))
        (coherent_inner A B f w a))
      (path_inverse_concat_left B
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a)
        (quasi_rho_point A B f w
          (app f (app (left_inverse_function A B f w) (app f a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f
              (app (left_inverse_function A B f w)
                (app f (app (left_inverse_function A B f w) (app f a))))
              (app (left_inverse_function A B f w) (app f a))
              (app (left_inverse_homotopy A B f w)
                (app (left_inverse_function A B f w) (app f a))))
            (quasi_rho_point A B f w (app f a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))"
    by (rule path_concat_type[OF SPACE eps MID s WL CANCEL])
  show "path_inverse
      (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
        (app f a))
      (path_concat B
        (app f (app (left_inverse_function A B f w) (app f a)))
        (app f (app (left_inverse_function A B f w)
          (app f (app (left_inverse_function A B f w) (app f a)))))
        (app f a)
        (path_inverse B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a)))))
        (path_concat B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (ap A B f
            (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a))))
            (app (left_inverse_function A B f w) (app f a))
            (app (left_inverse_homotopy A B f w)
              (app (left_inverse_function A B f w) (app f a))))
          (quasi_rho_point A B f w (app f a))))
      (ap A B f (app (left_inverse_function A B f w) (app f a)) a
        (app (left_inverse_homotopy A B f w) a))
      (path_concat
        (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a))
        (path_concat B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f
              (app (left_inverse_function A B f w)
                (app f (app (left_inverse_function A B f w) (app f a))))
              (app (left_inverse_function A B f w) (app f a))
              (app (left_inverse_homotopy A B f w)
                (app (left_inverse_function A B f w) (app f a))))
            (quasi_rho_point A B f w (app f a))))
        (path_concat B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a))))
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a))))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))
        (path_whisker_left B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f
              (app (left_inverse_function A B f w)
                (app f (app (left_inverse_function A B f w) (app f a))))
              (app (left_inverse_function A B f w) (app f a))
              (app (left_inverse_homotopy A B f w)
                (app (left_inverse_function A B f w) (app f a))))
            (quasi_rho_point A B f w (app f a)))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a))))
            (ap A B f (app (left_inverse_function A B f w) (app f a)) a
              (app (left_inverse_homotopy A B f w) a)))
          (coherent_inner A B f w a))
        (path_inverse_concat_left B
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a)
          (quasi_rho_point A B f w
            (app f (app (left_inverse_function A B f w) (app f a))))
          (ap A B f (app (left_inverse_function A B f w) (app f a)) a
            (app (left_inverse_homotopy A B f w) a)))) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) (app f a)))
          (app f a))
        (ap A B f (app (left_inverse_function A B f w) (app f a)) a
          (app (left_inverse_homotopy A B f w) a))
        (path_concat B
          (app f (app (left_inverse_function A B f w) (app f a)))
          (app f (app (left_inverse_function A B f w)
            (app f (app (left_inverse_function A B f w) (app f a)))))
          (app f a)
          (path_inverse B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (quasi_rho_point A B f w
              (app f (app (left_inverse_function A B f w) (app f a)))))
          (path_concat B
            (app f (app (left_inverse_function A B f w)
              (app f (app (left_inverse_function A B f w) (app f a)))))
            (app f (app (left_inverse_function A B f w) (app f a)))
            (app f a)
            (ap A B f
              (app (left_inverse_function A B f w)
                (app f (app (left_inverse_function A B f w) (app f a))))
              (app (left_inverse_function A B f w) (app f a))
              (app (left_inverse_homotopy A B f w)
                (app (left_inverse_function A B f w) (app f a))))
            (quasi_rho_point A B f w (app f a))))"
    by (rule path_inverse_type[OF SPACE eps s EQ])
qed

text \<open>
  The coherent section homotopy bundled as a term, so that its naturality
  square is available.
\<close>

definition coherent_eps ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "coherent_eps A B f w \<equiv> lambda B (\<lambda>b. coherent_eps_point A B f w b)"

lemma coherent_eps_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "coherent_eps A B f w \<Colon>\<^sub>h
    homotopy B (\<lambda>_. B)
      (compose B A B f (left_inverse_function A B f w))
      (identity_function B)"
  unfolding coherent_eps_def homotopy_def
proof (rule pi_intro[OF B])
  fix b
  assume b: "b \<Colon>\<^sub>h B"
  have point: "coherent_eps_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule coherent_eps_point_type[OF A B f w b])
  show "coherent_eps_point A B f w b \<Colon>\<^sub>h
      identity_type B
        (app (compose B A B f (left_inverse_function A B f w)) b)
        (app (identity_function B) b)"
    using point by simp
qed

lemma coherent_eps_beta [simp]:
  "app (coherent_eps A B f w) b \<equiv> coherent_eps_point A B f w b"
  unfolding coherent_eps_def by simp

section \<open>Contractibility of the fibers of a bi-invertible map\<close>

text \<open>
  Given a fibre point \<open>(x, p)\<close> with \<open>p : f x = b\<close>, the first component of the
  path to the centre \<open>(g b, \<epsilon> b)\<close> is \<open>ap g p\<^sup>-\<^sup>1 \<cdot> \<eta> x : g b = x\<close>.
\<close>

definition fiber_gamma ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "fiber_gamma A B f w b x p \<equiv>
    path_concat A
      (app (left_inverse_function A B f w) b)
      (app (left_inverse_function A B f w) (app f x))
      x
      (ap B A (left_inverse_function A B f w) b (app f x)
        (path_inverse B (app f x) b p))
      (app (left_inverse_homotopy A B f w) x)"

lemma fiber_gamma_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and b: "b \<Colon>\<^sub>h B"
    and x: "x \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type B (app f x) b"
  shows "fiber_gamma A B f w b x p \<Colon>\<^sub>h
    identity_type A (app (left_inverse_function A B f w) b) x"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have eta: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f w) f)
        (identity_function A)"
    by (rule left_inverse_homotopy_type[OF w])
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have gb: "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g b])
  have gfx: "app (left_inverse_function A B f w) (app f x) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fx])
  have pinv: "path_inverse B (app f x) b p \<Colon>\<^sub>h
      identity_type B b (app f x)"
    by (rule path_inverse_type[OF B fx b p])
  have apg: "ap B A (left_inverse_function A B f w) b (app f x)
      (path_inverse B (app f x) b p) \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) b)
        (app (left_inverse_function A B f w) (app f x))"
    by (rule ap_type[OF B A g b fx pinv])
  have etapi: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type A (\<lambda>y. identity_type A
        (app (compose A B A (left_inverse_function A B f w) f) y)
        (app (identity_function A) y))"
    using eta unfolding homotopy_def .
  have etax: "app (left_inverse_homotopy A B f w) x \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) (app f x)) x"
    using pi_elim[OF etapi x] by simp
  show "fiber_gamma A B f w b x p \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) b) x"
    unfolding fiber_gamma_def
    by (rule path_concat_type[OF A gb gfx x apg etax])
qed

text \<open>
  The key computation \<open>ap f \<gamma> = \<epsilon> b \<cdot> p\<^sup>-\<^sup>1\<close>, obtained from functoriality
  of \<open>ap\<close>, the triangle identity \<open>coherent_tau\<close>, and naturality of \<open>\<epsilon>\<close>.
\<close>

definition fiber_apf_gamma ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "fiber_apf_gamma A B f w b x p \<equiv>
    path_concat
      (identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x))
      (ap A B f (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p))
      (path_concat B (app f (app (left_inverse_function A B f w) b))
        (app f (app (left_inverse_function A B f w) (app f x)))
        (app f x)
        (ap B B (compose B A B f (left_inverse_function A B f w)) b
          (app f x) (path_inverse B (app f x) b p))
        (coherent_eps_point A B f w (app f x)))
      (path_concat B (app f (app (left_inverse_function A B f w) b)) b
        (app f x)
        (coherent_eps_point A B f w b)
        (path_inverse B (app f x) b p))
      (path_concat
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (ap A B f (app (left_inverse_function A B f w) (app f x)) x
            (app (left_inverse_homotopy A B f w) x)))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (coherent_eps_point A B f w (app f x)))
        (path_concat
          (identity_type B (app f (app (left_inverse_function A B f w) b))
            (app f x))
          (ap A B f (app (left_inverse_function A B f w) b) x
            (fiber_gamma A B f w b x p))
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            (app f (app (left_inverse_function A B f w) (app f x)))
            (app f x)
            (ap A B f (app (left_inverse_function A B f w) b)
              (app (left_inverse_function A B f w) (app f x))
              (ap B A (left_inverse_function A B f w) b (app f x)
                (path_inverse B (app f x) b p)))
            (ap A B f (app (left_inverse_function A B f w) (app f x)) x
              (app (left_inverse_homotopy A B f w) x)))
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            (app f (app (left_inverse_function A B f w) (app f x)))
            (app f x)
            (ap B B (compose B A B f (left_inverse_function A B f w)) b
              (app f x) (path_inverse B (app f x) b p))
            (ap A B f (app (left_inverse_function A B f w) (app f x)) x
              (app (left_inverse_homotopy A B f w) x)))
          (ap_concat A B f (app (left_inverse_function A B f w) b)
            (app (left_inverse_function A B f w) (app f x)) x
            (ap B A (left_inverse_function A B f w) b (app f x)
              (path_inverse B (app f x) b p))
            (app (left_inverse_homotopy A B f w) x))
          (path_whisker_right B
            (app f (app (left_inverse_function A B f w) b))
            (app f (app (left_inverse_function A B f w) (app f x)))
            (app f x)
            (ap A B f (app (left_inverse_function A B f w) b)
              (app (left_inverse_function A B f w) (app f x))
              (ap B A (left_inverse_function A B f w) b (app f x)
                (path_inverse B (app f x) b p)))
            (ap B B (compose B A B f (left_inverse_function A B f w)) b
              (app f x) (path_inverse B (app f x) b p))
            (ap A B f (app (left_inverse_function A B f w) (app f x)) x
              (app (left_inverse_homotopy A B f w) x))
            (path_inverse
              (identity_type B (app f (app (left_inverse_function A B f w) b))
                (app f (app (left_inverse_function A B f w) (app f x))))
              (ap B B (compose B A B f (left_inverse_function A B f w)) b
                (app f x) (path_inverse B (app f x) b p))
              (ap A B f (app (left_inverse_function A B f w) b)
                (app (left_inverse_function A B f w) (app f x))
                (ap B A (left_inverse_function A B f w) b (app f x)
                  (path_inverse B (app f x) b p)))
              (ap_compose B A B f (left_inverse_function A B f w) b
                (app f x) (path_inverse B (app f x) b p)))))
        (path_whisker_left B
          (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (ap A B f (app (left_inverse_function A B f w) (app f x)) x
            (app (left_inverse_homotopy A B f w) x))
          (coherent_eps_point A B f w (app f x))
          (coherent_tau A B f w x)))
      (path_concat
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (coherent_eps_point A B f w (app f x)))
        (path_concat B (app f (app (left_inverse_function A B f w) b)) b
          (app f x)
          (coherent_eps_point A B f w b)
          (ap B B (identity_function B) b (app f x)
            (path_inverse B (app f x) b p)))
        (path_concat B (app f (app (left_inverse_function A B f w) b)) b
          (app f x)
          (coherent_eps_point A B f w b)
          (path_inverse B (app f x) b p))
        (homotopy_naturality B B
          (compose B A B f (left_inverse_function A B f w))
          (identity_function B)
          (coherent_eps A B f w)
          b (app f x) (path_inverse B (app f x) b p))
        (path_whisker_left B
          (app f (app (left_inverse_function A B f w) b)) b (app f x)
          (coherent_eps_point A B f w b)
          (ap B B (identity_function B) b (app f x)
            (path_inverse B (app f x) b p))
          (path_inverse B (app f x) b p)
          (ap_identity B b (app f x) (path_inverse B (app f x) b p))))"

lemma fiber_apf_gamma_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and b: "b \<Colon>\<^sub>h B"
    and x: "x \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type B (app f x) b"
  shows "fiber_apf_gamma A B f w b x p \<Colon>\<^sub>h
    identity_type
      (identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x))
      (ap A B f (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p))
      (path_concat B (app f (app (left_inverse_function A B f w) b)) b
        (app f x)
        (coherent_eps_point A B f w b)
        (path_inverse B (app f x) b p))"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have eta: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      homotopy A (\<lambda>_. A)
        (compose A B A (left_inverse_function A B f w) f)
        (identity_function A)"
    by (rule left_inverse_homotopy_type[OF w])
  have fg: "compose B A B f (left_inverse_function A B f w) \<Colon>\<^sub>h arrow B B"
    by (rule compose_type[OF B g f])
  have idB: "identity_function B \<Colon>\<^sub>h arrow B B"
    by (rule identity_function_type[OF B])
  have eps_hom: "coherent_eps A B f w \<Colon>\<^sub>h
      homotopy B (\<lambda>_. B)
        (compose B A B f (left_inverse_function A B f w))
        (identity_function B)"
    by (rule coherent_eps_type[OF A B f w])
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have gb: "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g b])
  have gfx: "app (left_inverse_function A B f w) (app f x) \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g fx])
  have fgb: "app f (app (left_inverse_function A B f w) b) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gb])
  have fgfx: "app f (app (left_inverse_function A B f w) (app f x)) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gfx])
  have pinv: "path_inverse B (app f x) b p \<Colon>\<^sub>h
      identity_type B b (app f x)"
    by (rule path_inverse_type[OF B fx b p])
  have apg: "ap B A (left_inverse_function A B f w) b (app f x)
      (path_inverse B (app f x) b p) \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) b)
        (app (left_inverse_function A B f w) (app f x))"
    by (rule ap_type[OF B A g b fx pinv])
  have etapi: "left_inverse_homotopy A B f w \<Colon>\<^sub>h
      pi_type A (\<lambda>y. identity_type A
        (app (compose A B A (left_inverse_function A B f w) f) y)
        (app (identity_function A) y))"
    using eta unfolding homotopy_def .
  have etax: "app (left_inverse_homotopy A B f w) x \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) (app f x)) x"
    using pi_elim[OF etapi x] by simp
  have gamma: "fiber_gamma A B f w b x p \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) b) x"
    by (rule fiber_gamma_type[OF A B f w b x p])
  have space: "identity_type B (app f (app (left_inverse_function A B f w) b))
      (app f x) \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fgb fx])
  have space2: "identity_type B (app f (app (left_inverse_function A B f w) b))
      (app f (app (left_inverse_function A B f w) (app f x)))
      \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fgb fgfx])
  have APFGAM: "ap A B f (app (left_inverse_function A B f w) b) x
      (fiber_gamma A B f w b x p) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x)"
    by (rule ap_type[OF A B f gb x gamma])
  have APF_APG: "ap A B f (app (left_inverse_function A B f w) b)
      (app (left_inverse_function A B f w) (app f x))
      (ap B A (left_inverse_function A B f w) b (app f x)
        (path_inverse B (app f x) b p)) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f (app (left_inverse_function A B f w) (app f x)))"
    by (rule ap_type[OF A B f gb gfx apg])
  have APF_ETAX: "ap A B f (app (left_inverse_function A B f w) (app f x)) x
      (app (left_inverse_homotopy A B f w) x) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f x)))
        (app f x)"
    by (rule ap_type[OF A B f gfx x etax])
  have EPSFX: "coherent_eps_point A B f w (app f x) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) (app f x)))
        (app f x)"
    by (rule coherent_eps_point_type[OF A B f w fx])
  have EPSB: "coherent_eps_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule coherent_eps_point_type[OF A B f w b])
  have APFG_COMPOSE: "ap B B (compose B A B f (left_inverse_function A B f w)) b
      (app f x) (path_inverse B (app f x) b p) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f (app (left_inverse_function A B f w) (app f x)))"
    using ap_type[OF B B fg b fx pinv] by simp
  have ap_idQ: "ap B B (identity_function B) b (app f x)
      (path_inverse B (app f x) b p) \<Colon>\<^sub>h
      identity_type B b (app f x)"
    using ap_type[OF B B idB b fx pinv] by simp
  have ACON: "ap_concat A B f (app (left_inverse_function A B f w) b)
      (app (left_inverse_function A B f w) (app f x)) x
      (ap B A (left_inverse_function A B f w) b (app f x)
        (path_inverse B (app f x) b p))
      (app (left_inverse_homotopy A B f w) x) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap A B f (app (left_inverse_function A B f w) b)
            (app (left_inverse_function A B f w) (app f x))
            (ap B A (left_inverse_function A B f w) b (app f x)
              (path_inverse B (app f x) b p)))
          (ap A B f (app (left_inverse_function A B f w) (app f x)) x
            (app (left_inverse_homotopy A B f w) x)))"
    using ap_concat_type[OF A B f gb gfx x apg etax]
    unfolding fiber_gamma_def by simp
  have AC_fg: "ap_compose B A B f (left_inverse_function A B f w) b
      (app f x) (path_inverse B (app f x) b p) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x))))
        (ap B B (compose B A B f (left_inverse_function A B f w)) b
          (app f x) (path_inverse B (app f x) b p))
        (ap A B f (app (left_inverse_function A B f w) b)
          (app (left_inverse_function A B f w) (app f x))
          (ap B A (left_inverse_function A B f w) b (app f x)
            (path_inverse B (app f x) b p)))"
    by (rule ap_compose_type[OF B A B g f b fx pinv])
  have ACFGinv: "path_inverse
      (identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f (app (left_inverse_function A B f w) (app f x))))
      (ap B B (compose B A B f (left_inverse_function A B f w)) b
        (app f x) (path_inverse B (app f x) b p))
      (ap A B f (app (left_inverse_function A B f w) b)
        (app (left_inverse_function A B f w) (app f x))
        (ap B A (left_inverse_function A B f w) b (app f x)
          (path_inverse B (app f x) b p)))
      (ap_compose B A B f (left_inverse_function A B f w) b
        (app f x) (path_inverse B (app f x) b p)) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x))))
        (ap A B f (app (left_inverse_function A B f w) b)
          (app (left_inverse_function A B f w) (app f x))
          (ap B A (left_inverse_function A B f w) b (app f x)
            (path_inverse B (app f x) b p)))
        (ap B B (compose B A B f (left_inverse_function A B f w)) b
          (app f x) (path_inverse B (app f x) b p))"
    by (rule path_inverse_type[OF space2 APFG_COMPOSE APF_APG AC_fg])
  have WR: "path_whisker_right B
      (app f (app (left_inverse_function A B f w) b))
      (app f (app (left_inverse_function A B f w) (app f x)))
      (app f x)
      (ap A B f (app (left_inverse_function A B f w) b)
        (app (left_inverse_function A B f w) (app f x))
        (ap B A (left_inverse_function A B f w) b (app f x)
          (path_inverse B (app f x) b p)))
      (ap B B (compose B A B f (left_inverse_function A B f w)) b
        (app f x) (path_inverse B (app f x) b p))
      (ap A B f (app (left_inverse_function A B f w) (app f x)) x
        (app (left_inverse_homotopy A B f w) x))
      (path_inverse
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x))))
        (ap B B (compose B A B f (left_inverse_function A B f w)) b
          (app f x) (path_inverse B (app f x) b p))
        (ap A B f (app (left_inverse_function A B f w) b)
          (app (left_inverse_function A B f w) (app f x))
          (ap B A (left_inverse_function A B f w) b (app f x)
            (path_inverse B (app f x) b p)))
        (ap_compose B A B f (left_inverse_function A B f w) b
          (app f x) (path_inverse B (app f x) b p))) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap A B f (app (left_inverse_function A B f w) b)
            (app (left_inverse_function A B f w) (app f x))
            (ap B A (left_inverse_function A B f w) b (app f x)
              (path_inverse B (app f x) b p)))
          (ap A B f (app (left_inverse_function A B f w) (app f x)) x
            (app (left_inverse_homotopy A B f w) x)))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (ap A B f (app (left_inverse_function A B f w) (app f x)) x
            (app (left_inverse_homotopy A B f w) x)))"
    by (rule path_whisker_right_type[OF B fgb fgfx fx APF_APG APFG_COMPOSE
          APF_ETAX ACFGinv])
  have WL: "path_whisker_left B
      (app f (app (left_inverse_function A B f w) b))
      (app f (app (left_inverse_function A B f w) (app f x)))
      (app f x)
      (ap B B (compose B A B f (left_inverse_function A B f w)) b
        (app f x) (path_inverse B (app f x) b p))
      (ap A B f (app (left_inverse_function A B f w) (app f x)) x
        (app (left_inverse_homotopy A B f w) x))
      (coherent_eps_point A B f w (app f x))
      (coherent_tau A B f w x) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (ap A B f (app (left_inverse_function A B f w) (app f x)) x
            (app (left_inverse_homotopy A B f w) x)))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (coherent_eps_point A B f w (app f x)))"
    by (rule path_whisker_left_type[OF B fgb fgfx fx APFG_COMPOSE APF_ETAX
          EPSFX coherent_tau_type[OF A B f w x]])
  have APFAPG_APFETAX: "path_concat B
      (app f (app (left_inverse_function A B f w) b))
      (app f (app (left_inverse_function A B f w) (app f x)))
      (app f x)
      (ap A B f (app (left_inverse_function A B f w) b)
        (app (left_inverse_function A B f w) (app f x))
        (ap B A (left_inverse_function A B f w) b (app f x)
          (path_inverse B (app f x) b p)))
      (ap A B f (app (left_inverse_function A B f w) (app f x)) x
        (app (left_inverse_homotopy A B f w) x)) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x)"
    by (rule path_concat_type[OF B fgb fgfx fx APF_APG APF_ETAX])
  have APFGCOMP_APFETAX: "path_concat B
      (app f (app (left_inverse_function A B f w) b))
      (app f (app (left_inverse_function A B f w) (app f x)))
      (app f x)
      (ap B B (compose B A B f (left_inverse_function A B f w)) b
        (app f x) (path_inverse B (app f x) b p))
      (ap A B f (app (left_inverse_function A B f w) (app f x)) x
        (app (left_inverse_homotopy A B f w) x)) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x)"
    by (rule path_concat_type[OF B fgb fgfx fx APFG_COMPOSE APF_ETAX])
  have APFGCOMP_EPSFX: "path_concat B
      (app f (app (left_inverse_function A B f w) b))
      (app f (app (left_inverse_function A B f w) (app f x)))
      (app f x)
      (ap B B (compose B A B f (left_inverse_function A B f w)) b
        (app f x) (path_inverse B (app f x) b p))
      (coherent_eps_point A B f w (app f x)) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x)"
    by (rule path_concat_type[OF B fgb fgfx fx APFG_COMPOSE EPSFX])
  have inner1: "path_concat
      (identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x))
      (ap A B f (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p))
      (path_concat B (app f (app (left_inverse_function A B f w) b))
        (app f (app (left_inverse_function A B f w) (app f x)))
        (app f x)
        (ap A B f (app (left_inverse_function A B f w) b)
          (app (left_inverse_function A B f w) (app f x))
          (ap B A (left_inverse_function A B f w) b (app f x)
            (path_inverse B (app f x) b p)))
        (ap A B f (app (left_inverse_function A B f w) (app f x)) x
          (app (left_inverse_homotopy A B f w) x)))
      (path_concat B (app f (app (left_inverse_function A B f w) b))
        (app f (app (left_inverse_function A B f w) (app f x)))
        (app f x)
        (ap B B (compose B A B f (left_inverse_function A B f w)) b
          (app f x) (path_inverse B (app f x) b p))
        (ap A B f (app (left_inverse_function A B f w) (app f x)) x
          (app (left_inverse_homotopy A B f w) x)))
      (ap_concat A B f (app (left_inverse_function A B f w) b)
        (app (left_inverse_function A B f w) (app f x)) x
        (ap B A (left_inverse_function A B f w) b (app f x)
          (path_inverse B (app f x) b p))
        (app (left_inverse_homotopy A B f w) x))
      (path_whisker_right B
        (app f (app (left_inverse_function A B f w) b))
        (app f (app (left_inverse_function A B f w) (app f x)))
        (app f x)
        (ap A B f (app (left_inverse_function A B f w) b)
          (app (left_inverse_function A B f w) (app f x))
          (ap B A (left_inverse_function A B f w) b (app f x)
            (path_inverse B (app f x) b p)))
        (ap B B (compose B A B f (left_inverse_function A B f w)) b
          (app f x) (path_inverse B (app f x) b p))
        (ap A B f (app (left_inverse_function A B f w) (app f x)) x
          (app (left_inverse_homotopy A B f w) x))
        (path_inverse
          (identity_type B (app f (app (left_inverse_function A B f w) b))
            (app f (app (left_inverse_function A B f w) (app f x))))
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (ap A B f (app (left_inverse_function A B f w) b)
            (app (left_inverse_function A B f w) (app f x))
            (ap B A (left_inverse_function A B f w) b (app f x)
              (path_inverse B (app f x) b p)))
          (ap_compose B A B f (left_inverse_function A B f w) b
            (app f x) (path_inverse B (app f x) b p)))) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (ap A B f (app (left_inverse_function A B f w) (app f x)) x
            (app (left_inverse_homotopy A B f w) x)))"
    by (rule path_concat_type[OF space APFGAM
          APFAPG_APFETAX APFGCOMP_APFETAX ACON WR])
  note CHAIN123 = path_concat_type[OF space APFGAM
        APFGCOMP_APFETAX APFGCOMP_EPSFX inner1 WL]
  have NATeps: "homotopy_naturality B B
      (compose B A B f (left_inverse_function A B f w))
      (identity_function B)
      (coherent_eps A B f w)
      b (app f x) (path_inverse B (app f x) b p) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f (app (left_inverse_function A B f w) (app f x)))
          (app f x)
          (ap B B (compose B A B f (left_inverse_function A B f w)) b
            (app f x) (path_inverse B (app f x) b p))
          (coherent_eps_point A B f w (app f x)))
        (path_concat B (app f (app (left_inverse_function A B f w) b)) b
          (app f x)
          (coherent_eps_point A B f w b)
          (ap B B (identity_function B) b (app f x)
            (path_inverse B (app f x) b p)))"
    using homotopy_naturality_type[OF B B fg idB eps_hom b fx pinv] by simp
  have WHnat: "path_whisker_left B
      (app f (app (left_inverse_function A B f w) b)) b (app f x)
      (coherent_eps_point A B f w b)
      (ap B B (identity_function B) b (app f x)
        (path_inverse B (app f x) b p))
      (path_inverse B (app f x) b p)
      (ap_identity B b (app f x) (path_inverse B (app f x) b p)) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (path_concat B (app f (app (left_inverse_function A B f w) b)) b
          (app f x)
          (coherent_eps_point A B f w b)
          (ap B B (identity_function B) b (app f x)
            (path_inverse B (app f x) b p)))
        (path_concat B (app f (app (left_inverse_function A B f w) b)) b
          (app f x)
          (coherent_eps_point A B f w b)
          (path_inverse B (app f x) b p))"
    by (rule path_whisker_left_type[OF B fgb b fx EPSB ap_idQ pinv
          ap_identity_type[OF B b fx pinv]])
  have EPSB_APIDQ: "path_concat B
      (app f (app (left_inverse_function A B f w) b)) b (app f x)
      (coherent_eps_point A B f w b)
      (ap B B (identity_function B) b (app f x)
        (path_inverse B (app f x) b p)) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x)"
    by (rule path_concat_type[OF B fgb b fx EPSB ap_idQ])
  have EPSB_Q: "path_concat B
      (app f (app (left_inverse_function A B f w) b)) b (app f x)
      (coherent_eps_point A B f w b)
      (path_inverse B (app f x) b p) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x)"
    by (rule path_concat_type[OF B fgb b fx EPSB pinv])
  note NATeps' = path_concat_type[OF space APFGCOMP_EPSFX EPSB_APIDQ EPSB_Q
        NATeps WHnat]
  show "fiber_apf_gamma A B f w b x p \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p))
        (path_concat B (app f (app (left_inverse_function A B f w) b)) b
          (app f x)
          (coherent_eps_point A B f w b)
          (path_inverse B (app f x) b p))"
    unfolding fiber_apf_gamma_def
    by (rule path_concat_type[OF space APFGAM APFGCOMP_EPSFX EPSB_Q
          CHAIN123 NATeps'])
qed

text \<open>
  The second component of the fibre path: transport of the centre proof
  along \<open>\<gamma>\<close> equals \<open>p\<close>.
\<close>

definition fiber_q ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "fiber_q A B f w b x p \<equiv>
    path_concat (identity_type B (app f x) b)
      (transport A (\<lambda>a. identity_type B (app f a) b)
        (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p)
        (coherent_eps_point A B f w b))
      (path_concat B (app f x) (app f (app (left_inverse_function A B f w) b))
        b
        (path_inverse B (app f (app (left_inverse_function A B f w) b))
          (app f x)
          (ap A B f (app (left_inverse_function A B f w) b) x
            (fiber_gamma A B f w b x p)))
        (coherent_eps_point A B f w b))
      p
      (transport_identity_left A B f b
        (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p)
        (coherent_eps_point A B f w b))
      (path_concat (identity_type B (app f x) b)
        (path_concat B (app f x)
          (app f (app (left_inverse_function A B f w) b)) b
          (path_inverse B (app f (app (left_inverse_function A B f w) b))
            (app f x)
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p)))
          (coherent_eps_point A B f w b))
        (path_concat B (app f x)
          (app f (app (left_inverse_function A B f w) b)) b
          (path_inverse B (app f (app (left_inverse_function A B f w) b))
            (app f x)
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p)))
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            (app f x) b
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p))
            p))
        p
        (path_whisker_left B (app f x)
          (app f (app (left_inverse_function A B f w) b)) b
          (path_inverse B (app f (app (left_inverse_function A B f w) b))
            (app f x)
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p)))
          (coherent_eps_point A B f w b)
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            (app f x) b
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p))
            p)
          (path_concat (identity_type B
              (app f (app (left_inverse_function A B f w) b)) b)
            (coherent_eps_point A B f w b)
            (path_concat B (app f (app (left_inverse_function A B f w) b))
              (app f x) b
              (path_concat B (app f (app (left_inverse_function A B f w) b))
                b (app f x)
                (coherent_eps_point A B f w b)
                (path_inverse B (app f x) b p))
              p)
            (path_concat B (app f (app (left_inverse_function A B f w) b))
              (app f x) b
              (ap A B f (app (left_inverse_function A B f w) b) x
                (fiber_gamma A B f w b x p))
              p)
            (path_inverse (identity_type B
                (app f (app (left_inverse_function A B f w) b)) b)
              (path_concat B (app f (app (left_inverse_function A B f w) b))
                (app f x) b
                (path_concat B (app f (app (left_inverse_function A B f w) b))
                  b (app f x)
                  (coherent_eps_point A B f w b)
                  (path_inverse B (app f x) b p))
                p)
              (coherent_eps_point A B f w b)
              (path_concat_inverse_right B
                (app f (app (left_inverse_function A B f w) b))
                (app f x) b
                (coherent_eps_point A B f w b) p))
            (path_inverse (identity_type B
                (app f (app (left_inverse_function A B f w) b)) b)
              (path_concat B (app f (app (left_inverse_function A B f w) b))
                (app f x) b
                (ap A B f (app (left_inverse_function A B f w) b) x
                  (fiber_gamma A B f w b x p))
                p)
              (path_concat B (app f (app (left_inverse_function A B f w) b))
                (app f x) b
                (path_concat B (app f (app (left_inverse_function A B f w) b))
                  b (app f x)
                  (coherent_eps_point A B f w b)
                  (path_inverse B (app f x) b p))
                p)
              (path_whisker_right B
                (app f (app (left_inverse_function A B f w) b))
                (app f x) b
                (ap A B f (app (left_inverse_function A B f w) b) x
                  (fiber_gamma A B f w b x p))
                (path_concat B (app f (app (left_inverse_function A B f w) b))
                  b (app f x)
                  (coherent_eps_point A B f w b)
                  (path_inverse B (app f x) b p))
                p
                (fiber_apf_gamma A B f w b x p)))))
        (path_inverse_concat_left B
          (app f (app (left_inverse_function A B f w) b)) (app f x) b
          (ap A B f (app (left_inverse_function A B f w) b) x
            (fiber_gamma A B f w b x p))
          p))"

lemma fiber_q_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and b: "b \<Colon>\<^sub>h B"
    and x: "x \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type B (app f x) b"
  shows "fiber_q A B f w b x p \<Colon>\<^sub>h
    identity_type (identity_type B (app f x) b)
      (transport A (\<lambda>a. identity_type B (app f a) b)
        (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p)
        (coherent_eps_point A B f w b))
      p"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have fx: "app f x \<Colon>\<^sub>h B" by (rule arrow_elim[OF f x])
  have gb: "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g b])
  have fgb: "app f (app (left_inverse_function A B f w) b) \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f gb])
  have gamma: "fiber_gamma A B f w b x p \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) b) x"
    by (rule fiber_gamma_type[OF A B f w b x p])
  have apfg: "ap A B f (app (left_inverse_function A B f w) b) x
      (fiber_gamma A B f w b x p) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x)"
    by (rule ap_type[OF A B f gb x gamma])
  have apfg_inv: "path_inverse B
      (app f (app (left_inverse_function A B f w) b)) (app f x)
      (ap A B f (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p)) \<Colon>\<^sub>h
      identity_type B (app f x)
        (app f (app (left_inverse_function A B f w) b))"
    by (rule path_inverse_type[OF B fgb fx apfg])
  have epsb: "coherent_eps_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule coherent_eps_point_type[OF A B f w b])
  have pinv: "path_inverse B (app f x) b p \<Colon>\<^sub>h
      identity_type B b (app f x)"
    by (rule path_inverse_type[OF B fx b p])
  have SPACEq: "identity_type B (app f x) b \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fx b])
  have SPACE2: "identity_type B (app f (app (left_inverse_function A B f w) b))
      b \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fgb b])
  have transp: "transport A (\<lambda>a. identity_type B (app f a) b)
      (app (left_inverse_function A B f w) b) x
      (fiber_gamma A B f w b x p)
      (coherent_eps_point A B f w b) \<Colon>\<^sub>h
      identity_type B (app f x) b"
  proof (rule transport_type[OF A])
    fix a
    assume a: "a \<Colon>\<^sub>h A"
    have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
    show "identity_type B (app f a) b \<Colon>\<^sub>h universe i"
      by (rule identity_form[OF B fa b])
  next
    show "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A" by (rule gb)
  next
    show "x \<Colon>\<^sub>h A" by (rule x)
  next
    show "fiber_gamma A B f w b x p \<Colon>\<^sub>h
        identity_type A (app (left_inverse_function A B f w) b) x"
      by (rule gamma)
  next
    show "coherent_eps_point A B f w b \<Colon>\<^sub>h
        identity_type B (app f (app (left_inverse_function A B f w) b)) b"
      by (rule epsb)
  qed
  have TILrhs: "path_concat B (app f x)
      (app f (app (left_inverse_function A B f w) b)) b
      (path_inverse B (app f (app (left_inverse_function A B f w) b))
        (app f x)
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p)))
      (coherent_eps_point A B f w b) \<Colon>\<^sub>h
      identity_type B (app f x) b"
    by (rule path_concat_type[OF B fx fgb b apfg_inv epsb])
  have apfg_p: "path_concat B (app f (app (left_inverse_function A B f w) b))
      (app f x) b
      (ap A B f (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p))
      p \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule path_concat_type[OF B fgb fx b apfg p])
  have epsb_pinv: "path_concat B
      (app f (app (left_inverse_function A B f w) b)) b (app f x)
      (coherent_eps_point A B f w b)
      (path_inverse B (app f x) b p) \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b))
        (app f x)"
    by (rule path_concat_type[OF B fgb b fx epsb pinv])
  have epsb_pinv_p: "path_concat B
      (app f (app (left_inverse_function A B f w) b)) (app f x) b
      (path_concat B (app f (app (left_inverse_function A B f w) b)) b
        (app f x)
        (coherent_eps_point A B f w b)
        (path_inverse B (app f x) b p))
      p \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule path_concat_type[OF B fgb fx b epsb_pinv p])
  have TIL: "transport_identity_left A B f b
      (app (left_inverse_function A B f w) b) x
      (fiber_gamma A B f w b x p)
      (coherent_eps_point A B f w b) \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) b)
        (transport A (\<lambda>a. identity_type B (app f a) b)
          (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p)
          (coherent_eps_point A B f w b))
        (path_concat B (app f x)
          (app f (app (left_inverse_function A B f w) b)) b
          (path_inverse B (app f (app (left_inverse_function A B f w) b))
            (app f x)
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p)))
          (coherent_eps_point A B f w b))"
    by (rule transport_identity_left_type[OF A B f b gb x gamma epsb])
  have APFG: "fiber_apf_gamma A B f w b x p \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b))
          (app f x))
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p))
        (path_concat B (app f (app (left_inverse_function A B f w) b)) b
          (app f x)
          (coherent_eps_point A B f w b)
          (path_inverse B (app f x) b p))"
    by (rule fiber_apf_gamma_type[OF A B f w b x p])
  have PCIR: "path_concat_inverse_right B
      (app f (app (left_inverse_function A B f w) b)) (app f x) b
      (coherent_eps_point A B f w b) p \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b)) b)
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f x) b
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            b (app f x)
            (coherent_eps_point A B f w b)
            (path_inverse B (app f x) b p))
          p)
        (coherent_eps_point A B f w b)"
    by (rule path_concat_inverse_right_type[OF B fgb fx b epsb p])
  have WRAPFG: "path_whisker_right B
      (app f (app (left_inverse_function A B f w) b)) (app f x) b
      (ap A B f (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p))
      (path_concat B (app f (app (left_inverse_function A B f w) b)) b
        (app f x)
        (coherent_eps_point A B f w b)
        (path_inverse B (app f x) b p))
      p
      (fiber_apf_gamma A B f w b x p) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b)) b)
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f x) b
          (ap A B f (app (left_inverse_function A B f w) b) x
            (fiber_gamma A B f w b x p))
          p)
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f x) b
          (path_concat B (app f (app (left_inverse_function A B f w) b)) b
            (app f x)
            (coherent_eps_point A B f w b)
            (path_inverse B (app f x) b p))
          p)"
    by (rule path_whisker_right_type[OF B fgb fx b apfg epsb_pinv p APFG])
  have EB: "path_concat (identity_type B
        (app f (app (left_inverse_function A B f w) b)) b)
      (coherent_eps_point A B f w b)
      (path_concat B (app f (app (left_inverse_function A B f w) b))
        (app f x) b
        (path_concat B (app f (app (left_inverse_function A B f w) b)) b
          (app f x)
          (coherent_eps_point A B f w b)
          (path_inverse B (app f x) b p))
        p)
      (path_concat B (app f (app (left_inverse_function A B f w) b))
        (app f x) b
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p))
        p)
      (path_inverse (identity_type B
          (app f (app (left_inverse_function A B f w) b)) b)
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f x) b
          (path_concat B (app f (app (left_inverse_function A B f w) b)) b
            (app f x)
            (coherent_eps_point A B f w b)
            (path_inverse B (app f x) b p))
          p)
        (coherent_eps_point A B f w b)
        (path_concat_inverse_right B
          (app f (app (left_inverse_function A B f w) b)) (app f x) b
          (coherent_eps_point A B f w b) p))
      (path_inverse (identity_type B
          (app f (app (left_inverse_function A B f w) b)) b)
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f x) b
          (ap A B f (app (left_inverse_function A B f w) b) x
            (fiber_gamma A B f w b x p))
          p)
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f x) b
          (path_concat B (app f (app (left_inverse_function A B f w) b)) b
            (app f x)
            (coherent_eps_point A B f w b)
            (path_inverse B (app f x) b p))
          p)
        (path_whisker_right B
          (app f (app (left_inverse_function A B f w) b)) (app f x) b
          (ap A B f (app (left_inverse_function A B f w) b) x
            (fiber_gamma A B f w b x p))
          (path_concat B (app f (app (left_inverse_function A B f w) b)) b
            (app f x)
            (coherent_eps_point A B f w b)
            (path_inverse B (app f x) b p))
          p
          (fiber_apf_gamma A B f w b x p))) \<Colon>\<^sub>h
      identity_type
        (identity_type B (app f (app (left_inverse_function A B f w) b)) b)
        (coherent_eps_point A B f w b)
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f x) b
          (ap A B f (app (left_inverse_function A B f w) b) x
            (fiber_gamma A B f w b x p))
          p)"
    by (rule path_concat_type[OF SPACE2 epsb epsb_pinv_p apfg_p
          path_inverse_type[OF SPACE2 epsb_pinv_p epsb PCIR]
          path_inverse_type[OF SPACE2 apfg_p epsb_pinv_p WRAPFG]])
  have WHISK_EB: "path_whisker_left B (app f x)
      (app f (app (left_inverse_function A B f w) b)) b
      (path_inverse B (app f (app (left_inverse_function A B f w) b))
        (app f x)
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p)))
      (coherent_eps_point A B f w b)
      (path_concat B (app f (app (left_inverse_function A B f w) b))
        (app f x) b
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p))
        p)
      (path_concat (identity_type B
          (app f (app (left_inverse_function A B f w) b)) b)
        (coherent_eps_point A B f w b)
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f x) b
          (path_concat B (app f (app (left_inverse_function A B f w) b)) b
            (app f x)
            (coherent_eps_point A B f w b)
            (path_inverse B (app f x) b p))
          p)
        (path_concat B (app f (app (left_inverse_function A B f w) b))
          (app f x) b
          (ap A B f (app (left_inverse_function A B f w) b) x
            (fiber_gamma A B f w b x p))
          p)
        (path_inverse (identity_type B
            (app f (app (left_inverse_function A B f w) b)) b)
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            (app f x) b
            (path_concat B (app f (app (left_inverse_function A B f w) b)) b
              (app f x)
              (coherent_eps_point A B f w b)
              (path_inverse B (app f x) b p))
            p)
          (coherent_eps_point A B f w b)
          (path_concat_inverse_right B
            (app f (app (left_inverse_function A B f w) b)) (app f x) b
            (coherent_eps_point A B f w b) p))
        (path_inverse (identity_type B
            (app f (app (left_inverse_function A B f w) b)) b)
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            (app f x) b
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p))
            p)
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            (app f x) b
            (path_concat B (app f (app (left_inverse_function A B f w) b)) b
              (app f x)
              (coherent_eps_point A B f w b)
              (path_inverse B (app f x) b p))
            p)
          (path_whisker_right B
            (app f (app (left_inverse_function A B f w) b)) (app f x) b
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p))
            (path_concat B (app f (app (left_inverse_function A B f w) b)) b
              (app f x)
              (coherent_eps_point A B f w b)
              (path_inverse B (app f x) b p))
            p
            (fiber_apf_gamma A B f w b x p)))) \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) b)
        (path_concat B (app f x)
          (app f (app (left_inverse_function A B f w) b)) b
          (path_inverse B (app f (app (left_inverse_function A B f w) b))
            (app f x)
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p)))
          (coherent_eps_point A B f w b))
        (path_concat B (app f x)
          (app f (app (left_inverse_function A B f w) b)) b
          (path_inverse B (app f (app (left_inverse_function A B f w) b))
            (app f x)
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p)))
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            (app f x) b
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p))
            p))"
    by (rule path_whisker_left_type[OF B fx fgb b apfg_inv epsb apfg_p EB])
  have PICL: "path_inverse_concat_left B
      (app f (app (left_inverse_function A B f w) b)) (app f x) b
      (ap A B f (app (left_inverse_function A B f w) b) x
        (fiber_gamma A B f w b x p))
      p \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) b)
        (path_concat B (app f x)
          (app f (app (left_inverse_function A B f w) b)) b
          (path_inverse B (app f (app (left_inverse_function A B f w) b))
            (app f x)
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p)))
          (path_concat B (app f (app (left_inverse_function A B f w) b))
            (app f x) b
            (ap A B f (app (left_inverse_function A B f w) b) x
              (fiber_gamma A B f w b x p))
            p))
        p"
    by (rule path_inverse_concat_left_type[OF B fgb fx b apfg p])
  have apfg_inv_apfg_p: "path_concat B (app f x)
      (app f (app (left_inverse_function A B f w) b)) b
      (path_inverse B (app f (app (left_inverse_function A B f w) b))
        (app f x)
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p)))
      (path_concat B (app f (app (left_inverse_function A B f w) b))
        (app f x) b
        (ap A B f (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p))
        p) \<Colon>\<^sub>h
      identity_type B (app f x) b"
    by (rule path_concat_type[OF B fx fgb b apfg_inv apfg_p])
  note BIGCHAIN = path_concat_type[OF SPACEq TILrhs apfg_inv_apfg_p p
        WHISK_EB PICL]
  show "fiber_q A B f w b x p \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) b)
        (transport A (\<lambda>a. identity_type B (app f a) b)
          (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p)
          (coherent_eps_point A B f w b))
        p"
    unfolding fiber_q_def
    by (rule path_concat_type[OF SPACEq transp TILrhs p TIL BIGCHAIN])
qed

text \<open>
  Assembling \<open>\<gamma>\<close> and \<open>q\<close> with @{term sigma_path} yields the path from the
  centre \<open>(g b, \<epsilon> b)\<close> to an arbitrary fibre point \<open>(x, p)\<close>.
\<close>

definition fiber_path ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "fiber_path A B f w b x p \<equiv>
    sigma_path A (\<lambda>a. identity_type B (app f a) b)
      (app (left_inverse_function A B f w) b) x
      (coherent_eps_point A B f w b) p
      (fiber_gamma A B f w b x p)
      (fiber_q A B f w b x p)"

lemma fiber_path_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and b: "b \<Colon>\<^sub>h B"
    and x: "x \<Colon>\<^sub>h A"
    and p: "p \<Colon>\<^sub>h identity_type B (app f x) b"
  shows "fiber_path A B f w b x p \<Colon>\<^sub>h
    identity_type (sigma_type A (\<lambda>a. identity_type B (app f a) b))
      (pair (app (left_inverse_function A B f w) b)
        (coherent_eps_point A B f w b))
      (pair x p)"
  unfolding fiber_path_def
proof (rule sigma_path_type[OF A])
  fix a
  assume a: "a \<Colon>\<^sub>h A"
  have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
  show "identity_type B (app f a) b \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF B fa b])
next
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  show "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g b])
next
  show "x \<Colon>\<^sub>h A" by (rule x)
next
  show "coherent_eps_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule coherent_eps_point_type[OF A B f w b])
next
  show "p \<Colon>\<^sub>h identity_type B (app f x) b" by (rule p)
next
  show "fiber_gamma A B f w b x p \<Colon>\<^sub>h
      identity_type A (app (left_inverse_function A B f w) b) x"
    by (rule fiber_gamma_type[OF A B f w b x p])
next
  show "fiber_q A B f w b x p \<Colon>\<^sub>h
      identity_type (identity_type B (app f x) b)
        (transport A (\<lambda>a. identity_type B (app f a) b)
          (app (left_inverse_function A B f w) b) x
          (fiber_gamma A B f w b x p)
          (coherent_eps_point A B f w b))
        p"
    by (rule fiber_q_type[OF A B f w b x p])
qed

definition biinv_fiber_contraction ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "biinv_fiber_contraction A B f w b \<equiv>
    lambda (fiber A B f b)
      (\<lambda>z. sigma_ind A (\<lambda>a. identity_type B (app f a) b)
        (\<lambda>z. identity_type (fiber A B f b)
          (pair (app (left_inverse_function A B f w) b)
            (coherent_eps_point A B f w b))
          z)
        (\<lambda>x p. fiber_path A B f w b x p)
        z)"

lemma biinv_fiber_contraction_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and b: "b \<Colon>\<^sub>h B"
  shows "biinv_fiber_contraction A B f w b \<Colon>\<^sub>h
    pi_type (fiber A B f b)
      (\<lambda>z. identity_type (fiber A B f b)
        (pair (app (left_inverse_function A B f w) b)
          (coherent_eps_point A B f w b))
        z)"
  unfolding biinv_fiber_contraction_def
proof (rule pi_intro[OF fiber_form[OF A B f b]])
  fix z
  assume z: "z \<Colon>\<^sub>h fiber A B f b"
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have gb: "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g b])
  have epsb: "coherent_eps_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule coherent_eps_point_type[OF A B f w b])
  have fibU: "fiber A B f b \<Colon>\<^sub>h universe i"
    by (rule fiber_form[OF A B f b])
  have center: "pair (app (left_inverse_function A B f w) b)
      (coherent_eps_point A B f w b) \<Colon>\<^sub>h fiber A B f b"
    unfolding fiber_def
    by (rule sigma_intro[where B="\<lambda>a. identity_type B (app f a) b",
          OF gb epsb])
  show "sigma_ind A (\<lambda>a. identity_type B (app f a) b)
      (\<lambda>z. identity_type (fiber A B f b)
        (pair (app (left_inverse_function A B f w) b)
          (coherent_eps_point A B f w b))
        z)
      (\<lambda>x p. fiber_path A B f w b x p) z \<Colon>\<^sub>h
      identity_type (fiber A B f b)
        (pair (app (left_inverse_function A B f w) b)
          (coherent_eps_point A B f w b))
        z"
  proof (rule sigma_elim[OF A])
    fix a
    assume a: "a \<Colon>\<^sub>h A"
    have fa: "app f a \<Colon>\<^sub>h B" by (rule arrow_elim[OF f a])
    show "identity_type B (app f a) b \<Colon>\<^sub>h universe i"
      by (rule identity_form[OF B fa b])
  next
    fix q
    assume q: "q \<Colon>\<^sub>h sigma_type A (\<lambda>a. identity_type B (app f a) b)"
    have qfib: "q \<Colon>\<^sub>h fiber A B f b" using q unfolding fiber_def .
    show "identity_type (fiber A B f b)
        (pair (app (left_inverse_function A B f w) b)
          (coherent_eps_point A B f w b))
        q \<Colon>\<^sub>h universe i"
      by (rule identity_form[OF fibU center qfib])
  next
    fix x p
    assume x: "x \<Colon>\<^sub>h A"
    assume pp: "p \<Colon>\<^sub>h identity_type B (app f x) b"
    have fp: "fiber_path A B f w b x p \<Colon>\<^sub>h
        identity_type (sigma_type A (\<lambda>a. identity_type B (app f a) b))
          (pair (app (left_inverse_function A B f w) b)
            (coherent_eps_point A B f w b))
          (pair x p)"
      by (rule fiber_path_type[OF A B f w b x pp])
    show "fiber_path A B f w b x p \<Colon>\<^sub>h
        identity_type (fiber A B f b)
          (pair (app (left_inverse_function A B f w) b)
            (coherent_eps_point A B f w b))
          (pair x p)"
      using fp unfolding fiber_def .
  next
    show "z \<Colon>\<^sub>h sigma_type A (\<lambda>a. identity_type B (app f a) b)"
      using z unfolding fiber_def .
  qed
qed

section \<open>Bi-invertible maps are contractible maps\<close>

definition biinv_fiber_contractible ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "biinv_fiber_contractible A B f w b \<equiv>
    pair
      (pair (app (left_inverse_function A B f w) b)
        (coherent_eps_point A B f w b))
      (biinv_fiber_contraction A B f w b)"

lemma biinv_fiber_contractible_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
    and b: "b \<Colon>\<^sub>h B"
  shows "biinv_fiber_contractible A B f w b \<Colon>\<^sub>h contractible (fiber A B f b)"
proof -
  have g: "left_inverse_function A B f w \<Colon>\<^sub>h arrow B A"
    by (rule left_inverse_function_type[OF w])
  have gb: "app (left_inverse_function A B f w) b \<Colon>\<^sub>h A"
    by (rule arrow_elim[OF g b])
  have epsb: "coherent_eps_point A B f w b \<Colon>\<^sub>h
      identity_type B (app f (app (left_inverse_function A B f w) b)) b"
    by (rule coherent_eps_point_type[OF A B f w b])
  have center: "pair (app (left_inverse_function A B f w) b)
      (coherent_eps_point A B f w b) \<Colon>\<^sub>h fiber A B f b"
    unfolding fiber_def
    by (rule sigma_intro[where B="\<lambda>a. identity_type B (app f a) b",
          OF gb epsb])
  have contr: "biinv_fiber_contraction A B f w b \<Colon>\<^sub>h
      pi_type (fiber A B f b)
        (\<lambda>z. identity_type (fiber A B f b)
          (pair (app (left_inverse_function A B f w) b)
            (coherent_eps_point A B f w b))
          z)"
    by (rule biinv_fiber_contraction_type[OF A B f w b])
  show "biinv_fiber_contractible A B f w b \<Colon>\<^sub>h contractible (fiber A B f b)"
    unfolding biinv_fiber_contractible_def contractible_def
    by (rule sigma_intro[where B="\<lambda>center.
          pi_type (fiber A B f b)
            (\<lambda>x. identity_type (fiber A B f b) center x)",
          OF center contr])
qed

definition biinvertible_to_contractible_map ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "biinvertible_to_contractible_map A B f w \<equiv>
    lambda B (\<lambda>b. biinv_fiber_contractible A B f w b)"

theorem biinvertible_to_contractible_map_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and w: "w \<Colon>\<^sub>h biinvertible A B f"
  shows "biinvertible_to_contractible_map A B f w \<Colon>\<^sub>h
    contractible_map A B f"
  unfolding biinvertible_to_contractible_map_def contractible_map_def
proof (rule pi_intro[OF B])
  fix b
  assume b: "b \<Colon>\<^sub>h B"
  show "biinv_fiber_contractible A B f w b \<Colon>\<^sub>h contractible (fiber A B f b)"
    by (rule biinv_fiber_contractible_type[OF A B f w b])
qed

definition biinvertible_to_contractible_map_map ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "biinvertible_to_contractible_map_map A B f \<equiv>
    lambda (biinvertible A B f)
      (\<lambda>w. biinvertible_to_contractible_map A B f w)"

corollary biinvertible_to_contractible_map_map_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
  shows "biinvertible_to_contractible_map_map A B f \<Colon>\<^sub>h
    arrow (biinvertible A B f) (contractible_map A B f)"
  unfolding biinvertible_to_contractible_map_map_def
proof (rule arrow_intro[OF biinvertible_form[OF A B f]])
  fix w
  assume w: "w \<Colon>\<^sub>h biinvertible A B f"
  show "biinvertible_to_contractible_map A B f w \<Colon>\<^sub>h contractible_map A B f"
    by (rule biinvertible_to_contractible_map_type[OF A B f w])
qed

section \<open>The bidirectional characterization\<close>

text \<open>
  A map \<open>f : A \<rightarrow> B\<close> is a contractible map if and only if it is
  bi-invertible.  Both directions are witnessed by object-language functions:

  \<^item> @{term contractible_map_to_biinvertible_map} turns a proof that every
  fiber is contractible into a bi-invertibility witness;

  \<^item> @{term biinvertible_to_contractible_map_map} turns a bi-invertibility
  witness into a proof that every fiber is contractible.

  The packaged witness is a pair of object-language implications, not an
  inhabitant of @{term equivalence}; it is named a correspondence to keep that
  distinction visible.
\<close>

definition contractible_map_biinvertible_correspondence ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "contractible_map_biinvertible_correspondence A B f \<equiv>
    pair
      (contractible_map_to_biinvertible_map A B f)
      (biinvertible_to_contractible_map_map A B f)"

theorem contractible_map_biinvertible_criterion:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
  shows "contractible_map_biinvertible_correspondence A B f \<Colon>\<^sub>h
    product
      (arrow (contractible_map A B f) (biinvertible A B f))
      (arrow (biinvertible A B f) (contractible_map A B f))"
  unfolding contractible_map_biinvertible_correspondence_def
  by (rule product_intro[OF
        contractible_map_to_biinvertible_map_type[OF A B f]
        biinvertible_to_contractible_map_map_type[OF A B f]])

end
