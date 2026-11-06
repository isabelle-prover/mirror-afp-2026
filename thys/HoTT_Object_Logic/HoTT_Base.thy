theory HoTT_Base
  imports Pure
begin

section \<open>Expressions, judgments, and universes\<close>

typedecl expr
typedecl level

judgment has_type :: "expr \<Rightarrow> expr \<Rightarrow> prop"
  (infix "\<Colon>\<^sub>h" 50)

consts
  level_zero :: level
  level_succ :: "level \<Rightarrow> level"
  level_less :: "level \<Rightarrow> level \<Rightarrow> prop"
    (infix "\<prec>\<^sub>l" 50)
  universe :: "level \<Rightarrow> expr"

text \<open>
  The level relation is a strict order.  Pure has no falsity, so irreflexivity
  is stated in its ex-falso form: a hypothetical self-relation \<open>i \<prec>\<^sub>l i\<close>
  derives an arbitrary Pure proposition.  Every axiom below holds in the
  intended model, which reads levels as natural numbers, \<open>level_succ\<close> as the
  successor, and \<open>\<prec>\<^sub>l\<close> as the strict order; there the irreflexivity
  premise is impossible, so the axiom is sound and serves only to derive
  asymmetry.
\<close>

axiomatization where
  level_step: "i \<prec>\<^sub>l level_succ i" and
  level_trans: "i \<prec>\<^sub>l j \<Longrightarrow> j \<prec>\<^sub>l k \<Longrightarrow> i \<prec>\<^sub>l k" and
  level_irrefl: "i \<prec>\<^sub>l i \<Longrightarrow> PROP W" and
  universe_form: "universe i \<Colon>\<^sub>h universe (level_succ i)" and
  universe_cumul:
    "i \<prec>\<^sub>l j \<Longrightarrow> A \<Colon>\<^sub>h universe i \<Longrightarrow> A \<Colon>\<^sub>h universe j" and
  type_conversion:
    "a \<Colon>\<^sub>h A \<Longrightarrow> A \<equiv> B \<Longrightarrow> a \<Colon>\<^sub>h B" and
  term_conversion:
    "a \<equiv> b \<Longrightarrow> a \<Colon>\<^sub>h A \<Longrightarrow> b \<Colon>\<^sub>h A"

lemma level_two_steps:
  "i \<prec>\<^sub>l level_succ (level_succ i)"
  by (rule level_trans[OF level_step level_step])

lemma level_asym:
  assumes ij: "i \<prec>\<^sub>l j"
    and ji: "j \<prec>\<^sub>l i"
  shows "PROP W"
  by (rule level_irrefl[OF level_trans[OF ij ji]])

lemma level_succ_not_below:
  assumes "level_succ i \<prec>\<^sub>l i"
  shows "PROP W"
  by (rule level_asym[OF level_step assms])

lemma level_two_steps_not_below:
  assumes "level_succ (level_succ i) \<prec>\<^sub>l i"
  shows "PROP W"
  by (rule level_asym[OF level_two_steps assms])

lemma universe_cumul_two:
  assumes "A \<Colon>\<^sub>h universe i"
  shows "A \<Colon>\<^sub>h universe (level_succ (level_succ i))"
  by (rule universe_cumul[OF level_two_steps assms])

end
