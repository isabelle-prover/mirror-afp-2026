theory HIT_Canonical_Normal_Forms
  imports HIT_Confluence
begin

section \<open>Canonical normal-form comparison\<close>

text \<open>
  Strong normalization gives existence of a normal form and confluence gives
  uniqueness.  We package that mathematical result as a canonical function.
  The definition uses Hilbert choice and is therefore not an executable
  normalizer.  Its purpose is to replace semantic joinability obligations by
  equality of unique normal forms at the theorem interface.
\<close>

definition canonical_nf :: "sigenv \<Rightarrow> tm \<Rightarrow> tm" where
  "canonical_nf S t =
    (SOME u. reds S t u \<and> nform S u)"

theorem canonical_nf_spec:
  assumes typed: "wt S D G t A"
  shows "reds S t (canonical_nf S t) \<and>
    nform S (canonical_nf S t)"
proof -
  from SN_reaches_normal_form[OF wt_strong_normalization[OF typed]]
  have "\<exists>u. reds S t u \<and> nform S u" .
  then show ?thesis
    unfolding canonical_nf_def by (rule someI_ex)
qed

corollary canonical_nf_reachable:
  "wt S D G t A \<Longrightarrow> reds S t (canonical_nf S t)"
  using canonical_nf_spec by blast

corollary canonical_nf_normal:
  "wt S D G t A \<Longrightarrow> nform S (canonical_nf S t)"
  using canonical_nf_spec by blast

theorem canonical_nf_unique:
  assumes typed: "wt S D G t A"
    and steps: "reds S t u"
    and normal: "nform S u"
  shows "canonical_nf S t = u"
  by (rule wt_unique_normal_form[
        OF typed canonical_nf_reachable[OF typed]
          canonical_nf_normal[OF typed] steps normal])

corollary canonical_nf_of_normal:
  assumes typed: "wt S D G t A" and normal: "nform S t"
  shows "canonical_nf S t = t"
  by (rule canonical_nf_unique[OF typed _ normal]) simp

lemma regular_reds:
  assumes "reds S t u" and "regular S t"
  shows "regular S u"
  using assms
  by (induct rule: rtranclp_induct) (auto intro: regular_red)

theorem typed_joinable_iff_canonical_nf_eq:
  assumes typed_t: "wt S D G t A"
    and typed_u: "wt S E H u B"
  shows "joinable S t u \<longleftrightarrow>
    canonical_nf S t = canonical_nf S u"
proof
  assume join: "joinable S t u"
  then obtain v where tv: "reds S t v" and uv: "reds S u v"
    unfolding joinable_def by blast
  have tnf: "reds S t (canonical_nf S t)"
    by (rule canonical_nf_reachable[OF typed_t])
  have unf: "reds S u (canonical_nf S u)"
    by (rule canonical_nf_reachable[OF typed_u])
  have nt: "nform S (canonical_nf S t)"
    by (rule canonical_nf_normal[OF typed_t])
  have nu: "nform S (canonical_nf S u)"
    by (rule canonical_nf_normal[OF typed_u])
  from wt_church_rosser[OF typed_t tv tnf]
  obtain x where vx: "reds S v x"
    and ntx: "reds S (canonical_nf S t) x" by blast
  have x_t: "x = canonical_nf S t"
    by (rule nform_reds_eq[OF nt ntx])
  have vnt: "reds S v (canonical_nf S t)"
    using vx x_t by simp
  from wt_church_rosser[OF typed_u uv unf]
  obtain y where vy: "reds S v y"
    and nuy: "reds S (canonical_nf S u) y" by blast
  have y_u: "y = canonical_nf S u"
    by (rule nform_reds_eq[OF nu nuy])
  have vnu: "reds S v (canonical_nf S u)"
    using vy y_u by simp
  have snv: "SN S v"
    by (rule SN_reds[OF tv wt_strong_normalization[OF typed_t]])
  have regv: "regular S v"
    by (rule regular_reds[OF tv regular_wt[OF typed_t]])
  show "canonical_nf S t = canonical_nf S u"
    by (rule SN_unique_normal_form[OF snv regv vnt nt vnu nu])
next
  assume eq: "canonical_nf S t = canonical_nf S u"
  have "reds S t (canonical_nf S t)"
    by (rule canonical_nf_reachable[OF typed_t])
  moreover have "reds S u (canonical_nf S t)"
    using canonical_nf_reachable[OF typed_u] eq by simp
  ultimately show "joinable S t u"
    unfolding joinable_def by blast
qed

end
