section \<open>The quintic \<open>x\<^sup>5 - 4x + 2\<close> is not solvable by radicals\<close>

theory Abel_Ruffini_Quintic
  imports
    Radical_Normal_Closure   \<comment>\<open>the forward direction: the normal-closure construction\<close>
    Quintic_Example          \<comment>\<open>concrete non-solvability of the quintic's Galois group\<close>
begin

text \<open>The two halves of the argument meet here.\<close>

subsection \<open>The main theorem\<close>

theorem quintic_not_solvable_by_radicals:
  "\<not> solvable_by_radicals (\<rat> :: complex set) {r. poly PhiC r = 0}"
proof
  assume solv: "solvable_by_radicals (\<rat> :: complex set) {r. poly PhiC r = 0}"
  \<comment> \<open>Names and standing facts.\<close>
  define X where "X \<equiv> {r. poly PhiC r = 0}"
  define Kq where "Kq \<equiv> generate_field (\<rat> \<union> X)"
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have finX: "finite X" unfolding X_def by (rule PhiC_roots_finite)
  \<comment> \<open>Unpack the radical tower witnessing solvability.\<close>
  obtain Fs where tower: "radical_tower (\<rat> :: complex set) Fs"
    and Xtop: "{r. poly PhiC r = 0} \<subseteq> tower_top (\<rat> :: complex set) Fs"
    using solv by (auto simp: solvable_by_radicals_def)
  have Xtop': "X \<subseteq> tower_top (\<rat> :: complex set) Fs" using Xtop by (simp add: X_def)
  have X_eq: "X = {r. poly PhiC r = 0}" by (simp add: X_def)

  have solvKq: "Group.solvable (field_auto Kq \<rat>) (compose Kq) (identity Kq)"
    unfolding Kq_def
    by (rule radical_tower_root_field_solvable
      [OF sfQ tower PhiC_poly_over_Rats irreducible_over_Rats_PhiC
        X_eq finX Xtop' alg_closed_imp_poly_has_root])
  \<comment> \<open>Contradiction with the concrete non-solvability of the quintic Galois group.\<close>
  have "\<not> Group.solvable (field_auto Kq \<rat>) (compose Kq) (identity Kq)"
    using quintic_galois_group_not_solvable
    unfolding Kq_def X_def by simp
  with solvKq show False by contradiction
qed

end
