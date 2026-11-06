theory HoTT_Univalence
  imports HoTT_Equivalence
begin

section \<open>The canonical map from identity to equivalence\<close>

definition idtoequiv ::
  "level \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "idtoequiv i A B p \<equiv>
    identity_ind (universe i) A
      (\<lambda>B _. equivalence A B)
      (identity_equivalence A) B p"

lemma idtoequiv_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
    and p: "p \<Colon>\<^sub>h identity_type (universe i) A B"
  shows "idtoequiv i A B p \<Colon>\<^sub>h equivalence A B"
  unfolding idtoequiv_def
proof (rule identity_elim)
  show "universe i \<Colon>\<^sub>h universe (level_succ i)"
    by (rule universe_form)
next
  show "A \<Colon>\<^sub>h universe i" by (rule A)
next
  fix X q
  assume X: "X \<Colon>\<^sub>h universe i"
  assume "q \<Colon>\<^sub>h identity_type (universe i) A X"
  show "equivalence A X \<Colon>\<^sub>h universe i"
    by (rule equivalence_form[OF A X])
next
  show "identity_equivalence A \<Colon>\<^sub>h equivalence A A"
    by (rule identity_equivalence_type[OF A])
next
  show "B \<Colon>\<^sub>h universe i" by (rule B)
next
  show "p \<Colon>\<^sub>h identity_type (universe i) A B" by (rule p)
qed

lemma idtoequiv_refl [simp]:
  "idtoequiv i A A (reflexivity (universe i) A) \<equiv>
    identity_equivalence A"
  unfolding idtoequiv_def by simp

definition idtoequiv_map ::
  "level \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "idtoequiv_map i A B \<equiv>
    lambda (identity_type (universe i) A B)
      (\<lambda>p. idtoequiv i A B p)"

lemma idtoequiv_map_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
  shows "idtoequiv_map i A B \<Colon>\<^sub>h
    arrow (identity_type (universe i) A B) (equivalence A B)"
proof -
  have paths: "identity_type (universe i) A B
      \<Colon>\<^sub>h universe (level_succ i)"
    by (rule identity_form[OF universe_form A B])
  show "idtoequiv_map i A B \<Colon>\<^sub>h
      arrow (identity_type (universe i) A B) (equivalence A B)"
    unfolding idtoequiv_map_def
  proof (rule arrow_intro[OF paths])
    fix p
    assume p: "p \<Colon>\<^sub>h identity_type (universe i) A B"
    show "idtoequiv i A B p \<Colon>\<^sub>h equivalence A B"
      by (rule idtoequiv_type[OF A B p])
  qed
qed

section \<open>Univalence\<close>

consts
  univalence_witness :: "level \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"

axiomatization where
  univalence:
    "A \<Colon>\<^sub>h universe i \<Longrightarrow> B \<Colon>\<^sub>h universe i \<Longrightarrow>
      univalence_witness i A B \<Colon>\<^sub>h
        biinvertible
          (identity_type (universe i) A B)
          (equivalence A B)
          (idtoequiv_map i A B)"

definition univalence_equivalence ::
  "level \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "univalence_equivalence i A B \<equiv>
    pair (idtoequiv_map i A B) (univalence_witness i A B)"

theorem univalence_equivalence_type:
  assumes A: "A \<Colon>\<^sub>h universe i"
    and B: "B \<Colon>\<^sub>h universe i"
  shows "univalence_equivalence i A B \<Colon>\<^sub>h
    equivalence (identity_type (universe i) A B) (equivalence A B)"
  unfolding univalence_equivalence_def
proof (rule equivalence_intro)
  show "idtoequiv_map i A B \<Colon>\<^sub>h
      arrow (identity_type (universe i) A B) (equivalence A B)"
    by (rule idtoequiv_map_type[OF A B])
next
  show "univalence_witness i A B \<Colon>\<^sub>h
      biinvertible
        (identity_type (universe i) A B)
        (equivalence A B)
        (idtoequiv_map i A B)"
    by (rule univalence[OF A B])
qed

end
