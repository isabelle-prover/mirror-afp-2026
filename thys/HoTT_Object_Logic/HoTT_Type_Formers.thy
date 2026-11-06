theory HoTT_Type_Formers
  imports HoTT_Base
begin

section \<open>Dependent products\<close>

consts
  pi_type :: "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr"
  lambda :: "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr"
  app :: "expr \<Rightarrow> expr \<Rightarrow> expr"

axiomatization where
  pi_form:
    "A \<Colon>\<^sub>h universe i \<Longrightarrow>
      (\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i) \<Longrightarrow>
      pi_type A B \<Colon>\<^sub>h universe i" and
  pi_intro:
    "A \<Colon>\<^sub>h universe i \<Longrightarrow>
      (\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> b x \<Colon>\<^sub>h B x) \<Longrightarrow>
      lambda A b \<Colon>\<^sub>h pi_type A B" and
  pi_elim:
    "f \<Colon>\<^sub>h pi_type A B \<Longrightarrow> a \<Colon>\<^sub>h A \<Longrightarrow>
      app f a \<Colon>\<^sub>h B a" and
  pi_beta [simp]:
    "app (lambda A b) a \<equiv> b a"

section \<open>Dependent sums\<close>

consts
  sigma_type :: "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr"
  pair :: "expr \<Rightarrow> expr \<Rightarrow> expr"
  first :: "expr \<Rightarrow> expr"
  second :: "expr \<Rightarrow> expr"
  sigma_ind ::
    "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow>
      (expr \<Rightarrow> expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr"

axiomatization where
  sigma_form:
    "A \<Colon>\<^sub>h universe i \<Longrightarrow>
      (\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i) \<Longrightarrow>
      sigma_type A B \<Colon>\<^sub>h universe i" and
  sigma_intro:
    "a \<Colon>\<^sub>h A \<Longrightarrow> b \<Colon>\<^sub>h B a \<Longrightarrow>
      pair a b \<Colon>\<^sub>h sigma_type A B" and
  sigma_first:
    "p \<Colon>\<^sub>h sigma_type A B \<Longrightarrow> first p \<Colon>\<^sub>h A" and
  sigma_second:
    "p \<Colon>\<^sub>h sigma_type A B \<Longrightarrow> second p \<Colon>\<^sub>h B (first p)" and
  sigma_elim:
    "A \<Colon>\<^sub>h universe i \<Longrightarrow>
      (\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i) \<Longrightarrow>
      (\<And>p. p \<Colon>\<^sub>h sigma_type A B \<Longrightarrow> C p \<Colon>\<^sub>h universe j) \<Longrightarrow>
      (\<And>x y. x \<Colon>\<^sub>h A \<Longrightarrow> y \<Colon>\<^sub>h B x \<Longrightarrow>
        d x y \<Colon>\<^sub>h C (pair x y)) \<Longrightarrow>
      p \<Colon>\<^sub>h sigma_type A B \<Longrightarrow>
      sigma_ind A B C d p \<Colon>\<^sub>h C p" and
  sigma_first_beta [simp]:
    "first (pair a b) \<equiv> a" and
  sigma_second_beta [simp]:
    "second (pair a b) \<equiv> b" and
  sigma_ind_beta [simp]:
    "sigma_ind A B C d (pair a b) \<equiv> d a b"

section \<open>Empty and unit types\<close>

consts
  empty_type :: expr
  empty_ind :: "(expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr"
  unit_type :: expr
  unit_term :: expr
  unit_ind :: "(expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"

axiomatization where
  empty_form: "empty_type \<Colon>\<^sub>h universe i" and
  empty_elim:
    "(\<And>z. z \<Colon>\<^sub>h empty_type \<Longrightarrow> C z \<Colon>\<^sub>h universe i) \<Longrightarrow>
      z \<Colon>\<^sub>h empty_type \<Longrightarrow> empty_ind C z \<Colon>\<^sub>h C z" and
  unit_form: "unit_type \<Colon>\<^sub>h universe i" and
  unit_intro: "unit_term \<Colon>\<^sub>h unit_type" and
  unit_elim:
    "(\<And>u. u \<Colon>\<^sub>h unit_type \<Longrightarrow> C u \<Colon>\<^sub>h universe i) \<Longrightarrow>
      d \<Colon>\<^sub>h C unit_term \<Longrightarrow> u \<Colon>\<^sub>h unit_type \<Longrightarrow>
      unit_ind C d u \<Colon>\<^sub>h C u" and
  unit_ind_beta [simp]:
    "unit_ind C d unit_term \<equiv> d"

section \<open>Natural numbers\<close>

consts
  natural_type :: expr
  natural_zero :: expr
  natural_succ :: "expr \<Rightarrow> expr"
  natural_ind ::
    "(expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow>
      (expr \<Rightarrow> expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr"

axiomatization where
  natural_form: "natural_type \<Colon>\<^sub>h universe i" and
  natural_zero_intro: "natural_zero \<Colon>\<^sub>h natural_type" and
  natural_succ_intro:
    "n \<Colon>\<^sub>h natural_type \<Longrightarrow> natural_succ n \<Colon>\<^sub>h natural_type" and
  natural_elim:
    "(\<And>n. n \<Colon>\<^sub>h natural_type \<Longrightarrow> C n \<Colon>\<^sub>h universe i) \<Longrightarrow>
      z \<Colon>\<^sub>h C natural_zero \<Longrightarrow>
      (\<And>n r. n \<Colon>\<^sub>h natural_type \<Longrightarrow> r \<Colon>\<^sub>h C n \<Longrightarrow>
        s n r \<Colon>\<^sub>h C (natural_succ n)) \<Longrightarrow>
      n \<Colon>\<^sub>h natural_type \<Longrightarrow>
      natural_ind C z s n \<Colon>\<^sub>h C n" and
  natural_ind_zero [simp]:
    "natural_ind C z s natural_zero \<equiv> z" and
  natural_ind_succ [simp]:
    "natural_ind C z s (natural_succ n) \<equiv>
      s n (natural_ind C z s n)"

section \<open>Non-dependent notation and functions\<close>

definition arrow :: "expr \<Rightarrow> expr \<Rightarrow> expr" where
  "arrow A B \<equiv> pi_type A (\<lambda>_. B)"

definition product :: "expr \<Rightarrow> expr \<Rightarrow> expr" where
  "product A B \<equiv> sigma_type A (\<lambda>_. B)"

definition identity_function :: "expr \<Rightarrow> expr" where
  "identity_function A \<equiv> lambda A (\<lambda>x. x)"

definition compose ::
  "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "compose A B C g f \<equiv> lambda A (\<lambda>x. app g (app f x))"

lemma arrow_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
  shows "arrow A B \<Colon>\<^sub>h universe i"
  unfolding arrow_def
proof (rule pi_form)
  show "A \<Colon>\<^sub>h universe i" by (rule A)
  fix x
  assume "x \<Colon>\<^sub>h A"
  show "B \<Colon>\<^sub>h universe i" by (rule B)
qed

lemma arrow_intro:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and b: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> b x \<Colon>\<^sub>h B"
  shows "lambda A b \<Colon>\<^sub>h arrow A B"
  unfolding arrow_def
  by (rule pi_intro[OF A b])

lemma arrow_elim:
  assumes f: "f \<Colon>\<^sub>h arrow A B"
    and a: "a \<Colon>\<^sub>h A"
  shows "app f a \<Colon>\<^sub>h B"
  using f unfolding arrow_def
  by (rule pi_elim[OF _ a])

lemma product_form:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
  shows "product A B \<Colon>\<^sub>h universe i"
  unfolding product_def
proof (rule sigma_form)
  show "A \<Colon>\<^sub>h universe i" by (rule A)
  fix x
  assume "x \<Colon>\<^sub>h A"
  show "B \<Colon>\<^sub>h universe i" by (rule B)
qed

lemma product_intro:
  assumes a: "a \<Colon>\<^sub>h A"
    and b: "b \<Colon>\<^sub>h B"
  shows "pair a b \<Colon>\<^sub>h product A B"
  unfolding product_def
  by (rule sigma_intro[OF a b])

lemma product_first:
  assumes "p \<Colon>\<^sub>h product A B"
  shows "first p \<Colon>\<^sub>h A"
  using assms unfolding product_def by (rule sigma_first)

lemma product_second:
  assumes "p \<Colon>\<^sub>h product A B"
  shows "second p \<Colon>\<^sub>h B"
  using assms unfolding product_def by (rule sigma_second)

lemma identity_function_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
  shows "identity_function A \<Colon>\<^sub>h arrow A A"
  unfolding identity_function_def
  by (rule arrow_intro[OF A], assumption)

lemma compose_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h arrow A B"
    and g: "g \<Colon>\<^sub>h arrow B C"
  shows "compose A B C g f \<Colon>\<^sub>h arrow A C"
  unfolding compose_def
proof (rule arrow_intro[OF A])
  fix x
  assume x: "x \<Colon>\<^sub>h A"
  have fx: "app f x \<Colon>\<^sub>h B"
    by (rule arrow_elim[OF f x])
  show "app g (app f x) \<Colon>\<^sub>h C"
    by (rule arrow_elim[OF g fx])
qed

lemma apply_identity [simp]:
  "app (identity_function A) x \<equiv> x"
  unfolding identity_function_def by simp

lemma apply_compose [simp]:
  "app (compose A B C g f) x \<equiv> app g (app f x)"
  unfolding compose_def by simp

end
