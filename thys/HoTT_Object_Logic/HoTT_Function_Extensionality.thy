theory HoTT_Function_Extensionality
  imports HoTT_Equivalence
begin

section \<open>The canonical map from function paths to homotopies\<close>

definition happly ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr"
where
  "happly A B f g p \<equiv>
    identity_ind (pi_type A B) f
      (\<lambda>g _. homotopy A B f g)
      (homotopy_refl A B f) g p"

lemma happly_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h pi_type A B"
    and g: "g \<Colon>\<^sub>h pi_type A B"
    and p: "p \<Colon>\<^sub>h identity_type (pi_type A B) f g"
  shows "happly A B f g p \<Colon>\<^sub>h homotopy A B f g"
  unfolding happly_def
proof (rule identity_elim)
  show "pi_type A B \<Colon>\<^sub>h universe i"
    by (rule pi_form[OF A B])
next
  show "f \<Colon>\<^sub>h pi_type A B" by (rule f)
next
  fix h q
  assume h: "h \<Colon>\<^sub>h pi_type A B"
  assume "q \<Colon>\<^sub>h identity_type (pi_type A B) f h"
  show "homotopy A B f h \<Colon>\<^sub>h universe i"
    by (rule homotopy_form[OF A B f h])
next
  show "homotopy_refl A B f \<Colon>\<^sub>h homotopy A B f f"
    by (rule homotopy_refl_type[OF A B f])
next
  show "g \<Colon>\<^sub>h pi_type A B" by (rule g)
next
  show "p \<Colon>\<^sub>h identity_type (pi_type A B) f g" by (rule p)
qed

lemma happly_refl [simp]:
  "happly A B f f (reflexivity (pi_type A B) f) \<equiv>
    homotopy_refl A B f"
  unfolding happly_def by simp

definition happly_map ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "happly_map A B f g \<equiv>
    lambda (identity_type (pi_type A B) f g)
      (\<lambda>p. happly A B f g p)"

lemma happly_map_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h pi_type A B"
    and g: "g \<Colon>\<^sub>h pi_type A B"
  shows "happly_map A B f g \<Colon>\<^sub>h
    arrow (identity_type (pi_type A B) f g) (homotopy A B f g)"
proof -
  have functions: "pi_type A B \<Colon>\<^sub>h universe i"
    by (rule pi_form[OF A B])
  have paths: "identity_type (pi_type A B) f g \<Colon>\<^sub>h universe i"
    by (rule identity_form[OF functions f g])
  show "happly_map A B f g \<Colon>\<^sub>h
      arrow (identity_type (pi_type A B) f g) (homotopy A B f g)"
    unfolding happly_map_def
  proof (rule arrow_intro[OF paths])
    fix p
    assume p: "p \<Colon>\<^sub>h identity_type (pi_type A B) f g"
    show "happly A B f g p \<Colon>\<^sub>h homotopy A B f g"
      by (rule happly_type[OF A B f g p])
  qed
qed

section \<open>Function extensionality\<close>

consts
  function_extensionality_witness ::
    "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"

axiomatization where
  function_extensionality:
    "A \<Colon>\<^sub>h universe i \<Longrightarrow>
      (\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i) \<Longrightarrow>
      f \<Colon>\<^sub>h pi_type A B \<Longrightarrow> g \<Colon>\<^sub>h pi_type A B \<Longrightarrow>
      function_extensionality_witness A B f g \<Colon>\<^sub>h
        biinvertible
          (identity_type (pi_type A B) f g)
          (homotopy A B f g)
          (happly_map A B f g)"

definition funext ::
  "expr \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow>
    expr \<Rightarrow> expr"
where
  "funext A B f g H \<equiv>
    app
      (left_inverse_function
        (identity_type (pi_type A B) f g)
        (homotopy A B f g)
        (happly_map A B f g)
        (function_extensionality_witness A B f g))
      H"

theorem funext_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "\<And>x. x \<Colon>\<^sub>h A \<Longrightarrow> B x \<Colon>\<^sub>h universe i"
    and f: "f \<Colon>\<^sub>h pi_type A B"
    and g: "g \<Colon>\<^sub>h pi_type A B"
    and H: "H \<Colon>\<^sub>h homotopy A B f g"
  shows "funext A B f g H \<Colon>\<^sub>h
    identity_type (pi_type A B) f g"
proof -
  have ext: "function_extensionality_witness A B f g \<Colon>\<^sub>h
      biinvertible
        (identity_type (pi_type A B) f g)
        (homotopy A B f g)
        (happly_map A B f g)"
    by (rule function_extensionality[OF A B f g])
  have inverse: "left_inverse_function
      (identity_type (pi_type A B) f g)
      (homotopy A B f g)
      (happly_map A B f g)
      (function_extensionality_witness A B f g)
      \<Colon>\<^sub>h arrow (homotopy A B f g)
        (identity_type (pi_type A B) f g)"
    by (rule left_inverse_function_type[OF ext])
  show "funext A B f g H \<Colon>\<^sub>h
      identity_type (pi_type A B) f g"
    unfolding funext_def
    by (rule arrow_elim[OF inverse H])
qed

end
