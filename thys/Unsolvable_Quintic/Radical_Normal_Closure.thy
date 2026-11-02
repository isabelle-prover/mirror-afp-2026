section \<open>The normal radical closure of a radical tower\<close>

theory Radical_Normal_Closure
  imports Radical_Solvable 
    "HOL-New_Algebra.Algebraic_Transitivity" 
    "HOL-New_Algebra.Galois_Transitivity"
begin

text \<open>To descend solvability of a radical extension onto a
  \<^emph>\<open>quotient\<close> Galois group we must first replace the radical tower by one whose top is \<^emph>\<open>normal\<close> over the
  base --- the ``normal radical closure''.  The construction (as in the standard textbook argument, and
  in Mathlib's @{text FieldTheory.AbelRuffini}): the conjugates of a radical tower are again radical
  towers (@{thm [source] radical_tower_image}), and splicing the finitely many conjugates together
  (@{thm [source] radical_tower_spliced}) yields one radical tower whose top is stable under the ambient
  Galois group.  These blocks develop the conjugate/splice reasoning; the quintic-specific assembly and
  the contradiction live in the joint session theory.\<close>

subsection \<open>A Galois conjugate of a radical tower is a radical tower\<close>

lemma radical_tower_conjugate:
  fixes N F :: "complex set" and Fs :: "complex set list" and \<sigma> :: "complex \<Rightarrow> complex"
  assumes N: "Subfield N" and sfF: "Subfield F"
    and tower: "radical_tower F Fs" and topN: "tower_top F Fs \<subseteq> N"
    and s: "\<sigma> \<in> field_auto N F"
  shows "radical_tower F (List.map ((`) \<sigma>) Fs)"
proof -
  have "field_hom_on N \<sigma>"
    using N s by (rule field_auto_imp_field_hom_on)
  then have image_tower: "radical_tower (\<sigma> ` F) (List.map ((`) \<sigma>) Fs)"
    using N radical_tower_image sfF topN tower by blast
  then show ?thesis using image_tower
    by (metis field_auto_image_base s)
qed

subsection \<open>The family of all conjugates is a family of towers over the base\<close>

text \<open>Applying a list @{term \<sigma>s} of @{term F}-automorphisms to a radical tower yields a
  family of radical towers over @{term F} --- the input shape that @{thm [source] radical_tower_spliced}
  consumes.\<close>
lemma conjugate_towers_over:
  fixes N F :: "complex set" and Fs :: "complex set list"
    and \<sigma>s :: "(complex \<Rightarrow> complex) list"
  assumes N: "Subfield N" and sfF: "Subfield F"
    and tower: "radical_tower F Fs" and topN: "tower_top F Fs \<subseteq> N"
    and ss: "set \<sigma>s \<subseteq> field_auto N F"
  shows "all_towers_over F (List.map (\<lambda>\<sigma>. List.map ((`) \<sigma>) Fs) \<sigma>s)"
  using ss
proof (induction \<sigma>s)
  case (Cons \<sigma> \<sigma>s)
  then show ?case
    using N radical_tower_conjugate sfF topN tower by force
qed auto

subsection \<open>The spliced tower's top contains every tower of the family\<close>

text \<open>Base-changing a tower @{term Ts} (over @{term F}) onto a larger base @{term B} can only enlarge its
  top.\<close>
lemma tower_top_basechange_superset:
  assumes "F \<subseteq> B"
  shows "tower_top F Ts \<subseteq> tower_top B (List.map (\<lambda>H. generate_field (B \<union> H)) Ts)"
  using assms
  by (auto simp: subset_generate_field tower_top_def generate_field.generate_field_base last_map)

text \<open>In the spliced tower @{term "spliced B Tss"} over @{term B}, the top field contains the
  top of \<^emph>\<open>every\<close> tower of the family (measured over the common base @{term F}).  This is what makes the
  splice top a compositum of the conjugates.\<close>
lemma spliced_top_contains_towers:
  assumes "Subfield B" and "Subfield F" and "F \<subseteq> B" and "all_towers_over F Tss"
  shows "\<forall>Ts \<in> set Tss. tower_top F Ts \<subseteq> tower_top B (spliced B Tss)"
  using assms
proof (induction Tss arbitrary: B)
  case Nil
  show ?case by simp
next
  case (Cons Ts Tss)
  define Ts' where "Ts' \<equiv> List.map (\<lambda>H. generate_field (B \<union> H)) Ts"
  define B' where "B' \<equiv> tower_top B Ts'"
  \<comment> \<open>The head tower base-changes onto @{term B}, giving a radical tower over @{term B} with top @{term B'}.\<close>
  have "radical_tower B Ts'" and rest: "all_towers_over F Tss" 
    using Cons.prems Ts'_def radical_tower_basechange_subfield by auto
  then obtain sfB': "Subfield B'" and BB': "B \<subseteq> B'"
    by (simp add: B'_def Cons.prems(1) subfield_tower_top)
  have FB': "F \<subseteq> B'" using Cons.prems(3) BB' by blast
  \<comment> \<open>The full splice over @{term B} equals the head @{term Ts'} followed by the splice over @{term B'}.\<close>
  have "spliced B (Ts # Tss) = Ts' @ spliced B' Tss"
    by (simp add: Ts'_def B'_def Let_def)
  then have top_eq: "tower_top B (spliced B (Ts # Tss)) = tower_top B' (spliced B' Tss)"
    by (simp add: tower_top_append B'_def)
  \<comment> \<open>The remainder is a radical tower over @{term B'}; hence @{term B'} lies below the final top.\<close>
  have B'top: "B' \<subseteq> tower_top B' (spliced B' Tss)"
    using FB' \<open>Subfield F\<close> radical_tower_spliced Cons.prems(4) sfB' subfield_tower_top by force
  show ?case
  proof
    fix Ts2 assume "Ts2 \<in> set (Ts # Tss)"
    then consider "Ts2 = Ts" | "Ts2 \<in> set Tss" by auto
    then show "tower_top F Ts2 \<subseteq> tower_top B (spliced B (Ts # Tss))"
      using Cons.IH[OF sfB' Cons.prems(2) FB']
      by (metis B'_def B'top Cons.prems(3) Ts'_def order.trans rest top_eq
          tower_top_basechange_superset)
  qed
qed

subsection \<open>The normal radical closure exists\<close>

text \<open>The top of a conjugated tower is the conjugate of the top: since @{term \<sigma>} fixes @{term F} setwise,
  @{term "tower_top F (List.map ((`) \<sigma>) Fs) = \<sigma> ` tower_top F Fs"} (the last field of the mapped list is
  the image of the last field; for the empty tower both sides are @{term "\<sigma> ` F = F"}).\<close>
lemma tower_top_conjugate:
  assumes sF: "\<sigma> ` F = F"
  shows "tower_top F (List.map ((`) \<sigma>) Fs) = \<sigma> ` tower_top F Fs"
  by (simp add: last_map sF tower_top_def)

text \<open>\<^emph>\<open>The normal radical closure exists (complex form).\<close>  Given a radical tower @{term Fs} over
  @{term F} inside an ambient field @{term N}, and any list @{term \<sigma>s} of @{term F}-automorphisms of
  @{term N}, splicing the conjugate family yields a single radical tower over @{term F} whose top
  @{term B} contains the conjugate @{term "\<sigma> ` tower_top F Fs"} of the original top for every
  @{term "\<sigma> \<in> set \<sigma>s"}.\<close>
theorem radical_normal_closure_exists:
  fixes N F :: "complex set" and Fs :: "complex set list"
    and \<sigma>s :: "(complex \<Rightarrow> complex) list"
  assumes N: "Subfield N" and sfF: "Subfield F"
    and tower: "radical_tower F Fs" and topN: "tower_top F Fs \<subseteq> N"
    and ss: "set \<sigma>s \<subseteq> field_auto N F"
  defines "Tss \<equiv> List.map (\<lambda>\<sigma>. List.map ((`) \<sigma>) Fs) \<sigma>s"
  shows "radical_tower F (spliced F Tss)"
        "(\<forall>\<sigma> \<in> set \<sigma>s. \<sigma> ` tower_top F Fs \<subseteq> tower_top F (spliced F Tss))"
proof -
  have allt: "all_towers_over F Tss"
    unfolding Tss_def by (rule conjugate_towers_over[OF N sfF tower topN ss])
  show rt: "radical_tower F (spliced F Tss)"
    by (rule radical_tower_spliced[OF sfF sfF subset_refl allt])
  show "\<forall>\<sigma> \<in> set \<sigma>s. \<sigma> ` tower_top F Fs \<subseteq> tower_top F (spliced F Tss)"
  proof
    fix \<sigma> assume s: "\<sigma> \<in> set \<sigma>s"
    then have sN: "\<sigma> \<in> field_auto N F" using ss by blast
    have sF: "\<sigma> ` F = F" by (rule field_auto_image_base[OF sN])
    \<comment> \<open>The conjugate tower is one of the family; its top is the conjugate of the original top.\<close>
    have mem: "List.map ((`) \<sigma>) Fs \<in> set Tss" using s unfolding Tss_def set_map by (rule imageI)
    have "\<sigma> ` tower_top F Fs = tower_top F (List.map ((`) \<sigma>) Fs)"
      using sF by (simp add: tower_top_conjugate)
    also have "\<dots> \<subseteq> tower_top F (spliced F Tss)"
      using spliced_top_contains_towers[OF sfF sfF subset_refl allt] mem by blast
    finally show "\<sigma> ` tower_top F Fs \<subseteq> tower_top F (spliced F Tss)" .
  qed
qed

subsection \<open>Every element of a radical tower top is algebraic over the base\<close>

text \<open>\<^emph>\<open>Algebraicity of a witness (Kummer/radical) chain over its base.\<close>  Every element of the top
  @{term "ktop F ws"} of a nondegenerate witness list is algebraic over the base @{term F}.\<close>
theorem ktop_algebraic_over_base:
  fixes F :: "complex set"
  shows "Subfield F \<Longrightarrow> wit_valid F ws \<Longrightarrow> y \<in> ktop F ws \<Longrightarrow> algebraic_over F y"
proof (induction ws arbitrary: F y)
  case Nil
  then show ?case by (auto intro: Subfield.algebraic_over_self)
next
  case (Cons w ws)
  then obtain a n where an: "w = (a, n)" and "n > 0" "a ^ n \<in> F" and wv: "wit_valid (eval_img F a) ws"
    by (metis prod.collapse wit_valid.simps(2))
  then have alg_aF: "algebraic_over F a" using radical_algebraic Cons by blast 
  define G where "G \<equiv> eval_img F a"
  have sfG: "Subfield G" unfolding G_def
    by (simp add: Cons.prems(1) Subfield.subfield_eval_img alg_aF)
  \<comment> \<open>The tail runs over @{term G}; every element of its top is algebraic over @{term G} (IH).\<close>
  with Cons show ?case
    using G_def alg_aF algebraic_over_transitive an ktop_Cons wv by blast
qed

text \<open>Recast for a bare radical tower (via its witness list): every element of @{term "tower_top F Fs"}
  is algebraic over @{term F}.\<close>
theorem radical_tower_top_algebraic:
  fixes F :: "complex set"
  assumes sfF: "Subfield F" and tower: "radical_tower F Fs"
  shows "\<forall>y \<in> tower_top F Fs. algebraic_over F y"
  using radical_tower_witnesses[OF sfF tower] ktop_algebraic_over_base ktop_eq_tower_top sfF by force

subsection \<open>A splitting field is normal and has a finite Galois group\<close>

theorem splitting_field_finite_galois:
  fixes F :: "complex set" and Phi :: "complex poly"
  assumes sfF: "Subfield F" and Phi: "Phi \<in> poly_over F" and Phinz: "Phi \<noteq> 0"
  defines "N \<equiv> generate_field (F \<union> {r. poly Phi r = 0})"
  shows "Subfield N" "F \<subseteq> N" "finite (field_auto N F)"
proof -
  define X where "X \<equiv> {r. poly Phi r = 0}"
  have finX: "finite X" unfolding X_def using Phinz by (rule poly_roots_finite)
  show sfN: "Subfield N" unfolding N_def by (rule subfield_generate_field)
  show FN: "F \<subseteq> N" unfolding N_def using subset_generate_field by blast
  have XN: "X \<subseteq> N" unfolding N_def X_def using subset_generate_field by blast
  have "N = gen_subfield (F \<union> X)"
    unfolding N_def X_def by (rule gen_subfield_eq_generate_field[symmetric])
  then show "finite (field_auto N F)"
    by (metis FN Phi XN X_def finX finite_field_auto sfF sfN)
qed

subsection \<open>Prepending a cyclotomic step\<close>

text \<open>Adjoining a root of unity is a radical step.  So a radical tower @{term Fs} over the
  cyclotomic base @{term "eval_img F (unity_root N)"} extends, by prepending that base as a first step,
  to a radical tower over @{term F} itself: @{term "eval_img F (unity_root N) # Fs"}.\<close>
lemma radical_step_cyclotomic:
  fixes F :: "complex set"
  assumes sfF: "Subfield F" and N: "N > 0"
  shows "radical_step F (eval_img F (unity_root N))"
proof -
  define \<zeta> where "\<zeta> \<equiv> unity_root N"
  have znF: "\<zeta> ^ N \<in> F" 
    using N Subfield.one_closed \<zeta>_def sfF unity_root_mem by auto
  have alg: "algebraic_over F \<zeta>"
    using radical_algebraic[OF sfF N znF] .
  then show ?thesis unfolding radical_step_def \<zeta>_def
    using N \<zeta>_def sfF Subfield.eval_img_eq_generate_field znF by blast
qed

text \<open>Prepending the cyclotomic step to a tower over the cyclotomic base yields a radical tower over
  @{term F}.\<close>
lemma radical_tower_cyclotomic_prepend:
  fixes F :: "complex set"
  assumes sfF: "Subfield F" and N: "N > 0"
    and tower: "radical_tower (eval_img F (unity_root N)) Fs"
  shows "radical_tower F (eval_img F (unity_root N) # Fs)"
  by (simp add: N radical_step_cyclotomic sfF tower)


subsection \<open>A radical tower embeds in a solvable normal radical top\<close>

text \<open>\<^emph>\<open>Witness validity is monotone in the base.\<close>  If @{term ws} is a nondegenerate witness list over
  @{term F} and @{term "F \<subseteq> B"} with @{term B} a subfield, then @{term ws} is also a nondegenerate
  witness list over @{term B}: the closure conditions @{term "a ^ n \<in> F"} persist to @{term B}, and
  the running field @{term "eval_img B a"} still contains @{term B} (hence @{term F}).\<close>
lemma wit_valid_exps_pos:
  fixes F :: "complex set"
  shows "wit_valid F ws \<Longrightarrow> \<forall>x \<in> set ws. snd x > 0"
  by (induction ws arbitrary: F; force)

lemma eval_img_mono_base: "F \<subseteq> B \<Longrightarrow> eval_img F a \<subseteq> eval_img B a"
  unfolding eval_img_def using poly_over_mono by blast

lemma mono_base_lemma:
  fixes F :: "complex set"
  shows "Subfield B \<Longrightarrow> F \<subseteq> B \<Longrightarrow> wit_valid F ws \<Longrightarrow> ktop F ws \<subseteq> ktop B ws \<and> wit_valid B ws"
proof (induction ws arbitrary: F B)
  case Nil
  then show ?case by simp
next
  case (Cons w ws)
  then obtain a n where an: "w = (a, n)" and "n > 0"  
    and "a ^ n \<in> B" and rest: "wit_valid (eval_img F a) ws"
    by (metis (no_types, opaque_lifting) prod.exhaust subset_iff wit_valid.simps(2))
  then have "algebraic_over B a" using radical_algebraic
    using Cons.prems(1) by blast
  then have sf: "Subfield (eval_img B a)"
    by (simp add: Cons.prems(1) Subfield.subfield_eval_img)
  have "eval_img F a \<subseteq> eval_img B a" using eval_img_mono_base[OF Cons.prems(2)] .
  then show ?case
    using Cons.IH Cons.prems(3) \<open>a ^ n \<in> B\<close> an sf by auto 
qed

lemma ktop_mono_base:
  fixes F :: "complex set"
  shows "Subfield B \<Longrightarrow> F \<subseteq> B \<Longrightarrow> wit_valid F ws \<Longrightarrow> ktop F ws \<subseteq> ktop B ws"
  by (simp add: mono_base_lemma)

lemma wit_valid_mono_base:
  fixes F :: "complex set"
  shows "Subfield B \<Longrightarrow> F \<subseteq> B \<Longrightarrow> wit_valid F ws \<Longrightarrow> wit_valid B ws"
  by (simp add: mono_base_lemma)

text \<open>A radical tower over a subfield @{term F} embeds into a field @{term N} that
  is a \<^emph>\<open>solvable\<close> radical top over @{term F}: prepend a cyclotomic step \<open>F \<leadsto> F(\<zeta>\<^sub>N\<^sub>0)\<close> (with @{term N\<^sub>0}
  the product of the extracted witness exponents), realise the tower over the enlarged base by the same
  witnesses, and combine solvability over the cyclotomic base with solvability 
  of the cyclotomic step via the tower step.\<close>
theorem radical_tower_embeds_solvable_top:
  fixes F :: "complex set"
  assumes sfF: "Subfield F" and tower: "radical_tower F Fs"
  obtains N Gs where "Subfield N" and "F \<subseteq> N" and "tower_top F Fs \<subseteq> N"
    and "radical_tower F Gs" and "tower_top F Gs = N"
    and "Group.solvable (field_auto N F) (compose N) (identity N)"
proof -
  obtain ws where wv: "wit_valid F ws" and kf: "kummer_fields F ws = Fs"
    using radical_tower_witnesses[OF sfF tower] by blast
  define N0 where "N0 \<equiv> prod_list (List.map snd ws)"
  have N0pos: "N0 > 0"
    unfolding N0_def using wit_valid_exps_pos[OF wv] by (induction ws) auto
  have dvdN0: "\<forall>x \<in> set ws. snd x dvd N0"
    by (simp add: N0_def prod_list_dvd)
  define \<zeta> where "\<zeta> \<equiv> unity_root N0"
  define Fz where "Fz \<equiv> eval_img F \<zeta>"  \<comment> \<open>The cyclotomic base\<close>
  have znF: "\<zeta> ^ N0 \<in> F"
    using N0pos Subfield.one_closed \<zeta>_def sfF unity_root_mem by auto
  have algz: "algebraic_over F \<zeta>" using radical_algebraic[OF sfF N0pos znF] .
  have sfFz: "Subfield Fz" unfolding Fz_def by (rule Subfield.subfield_eval_img[OF sfF algz])
  have FFz: "F \<subseteq> Fz" unfolding Fz_def using Subfield.eval_img_base[OF sfF] by auto
  \<comment> \<open>The same witnesses work over @{term Fz}; its Kummer top @{term N} is our normal radical top.\<close>
  have wvFz: "wit_valid Fz ws" by (rule wit_valid_mono_base[OF sfFz FFz wv])
  define N where "N = ktop Fz ws"
  have preFz: "pre_kummer_valid N0 Fz ws" by (rule wit_valid_imp_pre_kummer_valid[OF wvFz dvdN0])
  \<comment> \<open>@{term N} is a subfield containing @{term Fz} (hence @{term F}).\<close>
  have towerFz: "radical_tower Fz (kummer_fields Fz ws)"
    by (rule pre_kummer_valid_imp_radical_tower[OF sfFz preFz])
  have Ntop_eq: "tower_top Fz (kummer_fields Fz ws) = N"
    unfolding N_def by (rule ktop_eq_tower_top[OF refl, symmetric])
  have sfN: "Subfield N" and FzN: "Fz \<subseteq> N"
    using subfield_tower_top[OF sfFz towerFz] by (auto simp: Ntop_eq)
  have FN: "F \<subseteq> N" using FFz FzN by blast
  have topFs_sub: "tower_top F Fs \<subseteq> N"
    by (metis FFz N_def kf ktop_eq_tower_top ktop_mono_base sfFz wv)
  have zN: "unity_root N0 \<in> N"
    using FzN Subfield.eval_img_self[OF sfF] by (auto simp: Fz_def \<zeta>_def)
  have solvFzF: "Group.solvable (field_auto Fz F) (compose Fz) (identity Fz)" 
  and stableFz: "\<And>\<sigma>. \<sigma> \<in> field_auto N F \<Longrightarrow> \<sigma> ` Fz = Fz" 
  and rouFz: "\<forall>w. w ^ N0 = 1 \<longrightarrow> w \<in> Fz"     unfolding Fz_def \<zeta>_def
    using cyclotomic_step_solvable_and_stable[OF sfN sfF FN N0pos zN] by auto
  have solvNFz: "Group.solvable (field_auto N Fz) (compose N) (identity N)"
    unfolding N_def
    by (rule pre_kummer_chain_galois_solvable[OF sfFz rouFz preFz])
  \<comment> \<open>Combine over the tower \<open>F \<subseteq> Fz \<subseteq> N\<close>.\<close>
  have solvNF: "Group.solvable (field_auto N F) (compose N) (identity N)"
    using FFz FzN galois_solvable_tower_step sfFz sfN solvFzF solvNFz stableFz by blast
  \<comment> \<open>A radical tower over @{term F} with top @{term N}: prepend the cyclotomic step.\<close>
  have towerF: "radical_tower F (Fz # kummer_fields Fz ws)"
    using Fz_def N0pos \<zeta>_def radical_step_cyclotomic sfF towerFz by force
  have topF: "tower_top F (Fz # kummer_fields Fz ws) = N" using Ntop_eq by simp
  show ?thesis
    by (rule that[OF sfN FN topFs_sub towerF topF solvNF])
qed


subsection \<open>Polynomial helpers: products over a subfield and their roots\<close>

lemma poly_over_prod_list:
  assumes "Subfield K"
  shows "(\<And>p. p \<in> set ps \<Longrightarrow> p \<in> poly_over K) \<Longrightarrow> prod_list ps \<in> poly_over K"
  by (induction ps) (auto intro: Subfield.poly_over_mult[OF assms] Subfield.poly_over_1[OF assms])

lemma poly_prod_list_root_iff:
  fixes ps :: "'a :: idom poly list"
  shows "poly (prod_list ps) y = 0 \<longleftrightarrow> (\<exists>p \<in> set ps. poly p y = 0)"
  by (induction ps) auto

lemma prod_list_poly_nonzero:
  fixes ps :: "'a :: idom poly list"
  shows "(\<And>p. p \<in> set ps \<Longrightarrow> p \<noteq> 0) \<Longrightarrow> prod_list ps \<noteq> 0"
  by (induction ps) (auto simp: prod_list_zero_iff)

text \<open>Each radical base @{term "fst w"} of a witness list lies in the Kummer top.\<close>
lemma ktop_facts:
  fixes F :: "complex set"
  shows "Subfield F \<Longrightarrow> wit_valid F ws \<Longrightarrow> F \<subseteq> ktop F ws \<and> set (List.map fst ws) \<subseteq> ktop F ws"
proof (induction ws arbitrary: F)
  case (Cons w ws)
  then obtain a n where an: "w = (a, n)" and n: "n > 0" and a0: "a \<noteq> 0" and anF: "a ^ n \<in> F" and rest: "wit_valid (eval_img F a) ws"
    by (metis prod.exhaust wit_valid.simps(2))
  have sfE: "Subfield (eval_img F a)"
    using Cons.prems(1) Subfield.subfield_eval_img anF n radical_algebraic by blast
  \<comment> \<open>@{term a} is in the running field, hence in the top; the rest by induction.\<close>
  have aE: "a \<in> eval_img F a" by (rule Subfield.eval_img_self[OF Cons.prems(1)])
  then show ?case using an
    using Cons aE rest sfE by (simp add: Subfield.eval_img_base subset_iff)
qed auto

text \<open>The base is contained in the Kummer top of a nondegenerate witness list (the chain is
  increasing; roots of unity are not needed for this).\<close>
lemma
  assumes "Subfield F" "wit_valid F ws"
  shows F_subset_ktop_wit: "F \<subseteq> ktop F ws" and ktop_witness_bases_subset: "set (List.map fst ws) \<subseteq> ktop F ws"
  using ktop_facts [OF assms] by auto

subsection \<open>Witness-level normal closure: bounded-exponent Kummer chain for the conjugate family\<close>

text \<open>The image of a simple extension under a field homomorphism on a superfield is the generated
  field of the image --- unconditionally (no algebraicity of the image needed).\<close>
lemma eval_img_image_hom:
  assumes hom: "field_hom_on N f" and sfF: "Subfield F" and FN: "F \<subseteq> N"
    and alg: "algebraic_over F a" and aN: "a \<in> N"
  shows "f ` eval_img F a = generate_field (f ` F \<union> {f a})"
proof -
  interpret H: field_hom_on N f by (rule hom)
  have Fa_N: "F \<union> {a} \<subseteq> N" using FN aN by simp
  have genFa: "eval_img F a = generate_field (F \<union> {a})"
    by (rule Subfield.eval_img_eq_generate_field[OF sfF alg])
  then show ?thesis
    using Fa_N H.image_generate_field_eq by auto
qed

lemma ktop_append: "ktop F (xs @ ys) = ktop (ktop F xs) ys"
  by (induction xs arbitrary: F; force)

lemma pre_kummer_valid_append:
  "pre_kummer_valid N0 F xs \<Longrightarrow> pre_kummer_valid N0 (ktop F xs) ys
     \<Longrightarrow> pre_kummer_valid N0 F (xs @ ys)"
  by (induction xs arbitrary: F; force elim: pre_kummer_valid.elims)

text \<open>\<^emph>\<open>Conjugating and base-changing a witness list, at the witness level.\<close>  Let @{term \<sigma>} be a field
  homomorphism on the ambient @{term N} fixing @{term G} setwise via @{term "\<sigma> ` G = G"}.  Given a
  witness list @{term ws} over @{term G} whose top lies in @{term N} and whose exponents divide
  @{term N\<^sub>0}, and a base @{term B} (a subfield of @{term N}) containing @{term "\<sigma> ` G"}, there is a
  witness list @{term cw} over @{term B} --- with the \<^emph>\<open>same exponents\<close> --- that is @{term N\<^sub>0}-bounded
  (@{const pre_kummer_valid}) and whose Kummer top contains the conjugate @{term "\<sigma> ` ktop G ws"}.\<close>
lemma base_conj_witnesses:
  fixes N :: "complex set" and \<sigma> :: "complex \<Rightarrow> complex"
  assumes N: "Subfield N" and hom: "field_hom_on N \<sigma>" and homN: "\<sigma> ` N \<subseteq> N"
  shows "\<And>G B. Subfield G \<Longrightarrow> Subfield B \<Longrightarrow> G \<subseteq> N \<Longrightarrow> B \<subseteq> N \<Longrightarrow> \<sigma> ` G \<subseteq> B
           \<Longrightarrow> wit_valid G ws \<Longrightarrow> ktop G ws \<subseteq> N \<Longrightarrow> (\<forall>x \<in> set ws. snd x dvd N0)
           \<Longrightarrow> \<exists>cw. pre_kummer_valid N0 B cw \<and> \<sigma> ` ktop G ws \<subseteq> ktop B cw
                    \<and> B \<subseteq> ktop B cw \<and> ktop B cw \<subseteq> N"
proof (induction ws)
  case (Nil G B)
  have "\<sigma> ` ktop G [] \<subseteq> ktop B []" using Nil by simp
  moreover have "B \<subseteq> ktop B []" by simp
  moreover have "ktop B [] \<subseteq> N" using Nil by simp
  ultimately show ?case by (intro exI[of _ "[]"]) simp
next
  case (Cons w ws G B)
  interpret H: field_hom_on N \<sigma> by (rule hom)
  obtain a n where an: "w = (a, n)" by (cases w)
  have n: "n > 0" and a0: "a \<noteq> 0" and anG: "a ^ n \<in> G" and rest: "wit_valid (eval_img G a) ws"
    using Cons.prems(6) an by auto
  have ndvd: "n dvd N0" using Cons.prems(8) an by auto
  have alg: "algebraic_over G a" using radical_algebraic[OF Cons.prems(1) n anG] .
  have sfGa: "Subfield (eval_img G a)"
    by (rule Subfield.subfield_eval_img[OF Cons.prems(1) alg])
  \<comment> \<open>@{term a} lies in @{term N}: it is in the running field, contained in the top, in @{term N}.\<close>
  have aGa: "a \<in> eval_img G a" by (rule Subfield.eval_img_self[OF Cons.prems(1)])
  have GaktopN: "ktop (eval_img G a) ws \<subseteq> N" using Cons.prems(7) an by simp
  have GaN: "eval_img G a \<subseteq> N"
    using F_subset_ktop_wit GaktopN rest sfGa by auto
  have aN: "a \<in> N" using aGa GaN by blast
  \<comment> \<open>The conjugate radical @{term "\<sigma> a"}: nonzero, and its @{term n}th power lies in @{term B}.\<close>
  have sa0: "\<sigma> a \<noteq> 0"
    using H.hom_mult H.inverse_closed a0 aN by fastforce
  have sanB: "(\<sigma> a) ^ n \<in> B"
    using Cons.prems(5) H.hom_power aN anG by auto
  \<comment> \<open>The new base @{term "eval_img B (\<sigma> a)"} contains @{term "\<sigma> ` (eval_img G a)"}.\<close>
  define B' where "B' \<equiv> eval_img B (\<sigma> a)"
  have algsa: "algebraic_over B (\<sigma> a)" using radical_algebraic[OF Cons.prems(2) n sanB] .
  have sfB': "Subfield B'" unfolding B'_def by (rule Subfield.subfield_eval_img[OF Cons.prems(2) algsa])
  have BB': "B \<subseteq> B'" unfolding B'_def using Subfield.eval_img_base[OF Cons.prems(2)] by auto
  have saB': "\<sigma> a \<in> B'" unfolding B'_def by (rule Subfield.eval_img_self[OF Cons.prems(2)])
  \<comment> \<open>The conjugate simple extension is generated by the images and lands in the new base @{term B'}.\<close>
  have img_eq: "\<sigma> ` eval_img G a = generate_field (\<sigma> ` G \<union> {\<sigma> a})"
    by (rule eval_img_image_hom[OF hom Cons.prems(1) Cons.prems(3) alg aN])
  have B'gen: "B' = generate_field (B \<union> {\<sigma> a})"
    unfolding B'_def by (rule Subfield.eval_img_eq_generate_field[OF Cons.prems(2) algsa])
  have sGaB': "\<sigma> ` eval_img G a \<subseteq> B'"
  proof -
    have "\<sigma> ` G \<union> {\<sigma> a} \<subseteq> B \<union> {\<sigma> a}" using Cons.prems(5) by blast
    then show ?thesis by (metis img_eq B'gen generate_field_mono)
  qed
  have B'N: "B' \<subseteq> N"
  proof -
    have "\<sigma> a \<in> N" using aN homN by blast
    then show ?thesis using Cons.prems(4) B'gen generate_field_least[OF N] by simp
  qed
  \<comment> \<open>Recurse: witnesses over @{term B'} for the tail, conjugating @{term "eval_img G a"}.\<close>
  have tail_bound: "\<forall>x \<in> set ws. snd x dvd N0" using Cons.prems(8) by auto
  obtain cw where cw: "pre_kummer_valid N0 B' cw"
      "\<sigma> ` ktop (eval_img G a) ws \<subseteq> ktop B' cw" "B' \<subseteq> ktop B' cw" "ktop B' cw \<subseteq> N"
    using Cons.IH[OF sfGa sfB' GaN B'N sGaB' rest GaktopN tail_bound] by blast
  \<comment> \<open>Assemble: prepend the step @{term "(\<sigma> a, n)"}.\<close>
  have pre: "pre_kummer_valid N0 B ((\<sigma> a, n) # cw)"
    using n ndvd sa0 sanB cw(1) by (simp add: B'_def)
  have top: "\<sigma> ` ktop G (w # ws) \<subseteq> ktop B ((\<sigma> a, n) # cw)"
    using an cw(2) by (simp add: B'_def)
  have base: "B \<subseteq> ktop B ((\<sigma> a, n) # cw)" using BB' cw(3) by (simp add: B'_def)
  have topN: "ktop B ((\<sigma> a, n) # cw) \<subseteq> N" using cw(4) by (simp add: B'_def)
  show ?case using pre top base topN by blast
qed

text \<open>\<^emph>\<open>Folding the conjugate witnesses over the whole Galois group.\<close>  Given a base tower @{term ws} over
  @{term G}, a cyclotomic base @{term Fz} (a subfield of @{term N} containing @{term "\<sigma> ` G"} for every
  @{term \<sigma>} in the list), we accumulate the conjugate witness lists of @{term "\<sigma> ` ktop G ws"} for all
  @{term \<sigma>} into one @{term N\<^sub>0}-bounded pre-Kummer chain over @{term Fz} whose top stays inside @{term N}
  and contains every conjugate @{term "\<sigma> ` ktop G ws"}.  Induction on the list, appending each
  @{thm [source] base_conj_witnesses} chain with @{thm [source] pre_kummer_valid_append} /
  @{thm [source] ktop_append}.\<close>
lemma conj_family_witnesses:
  fixes N Fz G :: "complex set" and ws :: "(complex \<times> nat) list"
  assumes N: "Subfield N" and sfG: "Subfield G" and GN: "G \<subseteq> N"
    and wv: "wit_valid G ws" and topGN: "ktop G ws \<subseteq> N" and dvd: "\<forall>x \<in> set ws. snd x dvd N0"
  shows "\<And>Fz. Subfield Fz \<Longrightarrow> Fz \<subseteq> N \<Longrightarrow> G \<subseteq> Fz \<Longrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. \<sigma> \<in> field_auto N G)
           \<Longrightarrow> \<exists>CW. pre_kummer_valid N0 Fz CW \<and> Fz \<subseteq> ktop Fz CW \<and> ktop Fz CW \<subseteq> N
                    \<and> (\<forall>\<sigma> \<in> set \<sigma>s. \<sigma> ` ktop G ws \<subseteq> ktop Fz CW)"
proof (induction \<sigma>s)
  case (Nil Fz)
  show ?case by (intro exI[of _ "[]"]) (use Nil in simp)
next
  case (Cons \<sigma> \<sigma>s Fz)
  obtain CW0 where CW0: "pre_kummer_valid N0 Fz CW0" "Fz \<subseteq> ktop Fz CW0" "ktop Fz CW0 \<subseteq> N"
      "\<forall>\<tau> \<in> set \<sigma>s. \<tau> ` ktop G ws \<subseteq> ktop Fz CW0"
    using Cons.IH[OF Cons.prems(1,2,3)] Cons.prems(4) by auto
  define B where "B \<equiv> ktop Fz CW0"
  have sfB: "Subfield B"
  proof -
    have "radical_tower Fz (kummer_fields Fz CW0)"
      by (rule pre_kummer_valid_imp_radical_tower[OF Cons.prems(1) CW0(1)])
    then show ?thesis 
      using subfield_tower_top[OF Cons.prems(1)] by (force simp: B_def ktop_def tower_top_def)
  qed
  \<comment> \<open>Conjugate @{term "ktop G ws"} into a over @{term B}.\<close>
  have hom: "field_hom_on N \<sigma>" using N Cons using field_auto_imp_field_hom_on by fastforce
  have sNN: "\<sigma> ` N \<subseteq> N"
    using field_auto_closed Cons by auto
  have sGB: "\<sigma> ` G \<subseteq> B"
    using B_def CW0(2) Cons.prems field_auto_image_base by fastforce
  have BN: "B \<subseteq> N" unfolding B_def by (rule CW0(3))
  obtain cw where cw: "pre_kummer_valid N0 B cw" "\<sigma> ` ktop G ws \<subseteq> ktop B cw"
      "B \<subseteq> ktop B cw" "ktop B cw \<subseteq> N"
    using base_conj_witnesses[OF N hom sNN sfG sfB GN BN sGB wv topGN dvd] by blast
  \<comment> \<open>Append the two chains.\<close>
  define CW where "CW = CW0 @ cw"
  have pre: "pre_kummer_valid N0 Fz CW" unfolding CW_def B_def
    using B_def CW0(1) cw(1) pre_kummer_valid_append by blast
  then have covers: "Fz \<subseteq> ktop Fz CW" "\<forall>\<tau> \<in> set (\<sigma> # \<sigma>s). \<tau> ` ktop G ws \<subseteq> ktop Fz CW" "ktop Fz CW \<subseteq> N"
    using B_def CW_def ktop_append CW0 cw by force+
  with pre show ?case by blast
qed

text \<open>The Kummer top of a pre-Kummer chain is a subfield (each step is a simple algebraic extension;
  roots of unity are not needed).\<close>
lemma subfield_ktop_pre:
  fixes F :: "complex set"
  assumes "Subfield F" and "pre_kummer_valid N0 F ws"
  shows "Subfield (ktop F ws)"
proof -
  have "Subfield (tower_top F (kummer_fields F ws))"
    using assms pre_kummer_valid_imp_radical_tower subfield_tower_top by blast
  then show ?thesis by (simp add: ktop_def tower_top_def)
qed

text \<open>If the base lies in a subfield @{term N} and every radical base of the witness list lies in
  @{term N}, then the whole Kummer top lies in @{term N}: each simple step
  @{term "eval_img G a = generate_field (G \<union> {a})"} stays inside @{term N}.\<close>
lemma ktop_subset_of_bases:
  fixes N :: "complex set"
  assumes N: "Subfield N"
  shows "\<And>F. Subfield F \<Longrightarrow> F \<subseteq> N \<Longrightarrow> wit_valid F ws \<Longrightarrow> set (List.map fst ws) \<subseteq> N
           \<Longrightarrow> ktop F ws \<subseteq> N"
proof (induction ws)
  case Nil
  then show ?case by simp
next
  case (Cons w ws F)
  then obtain a n where an: "w = (a, n)" and n: "n > 0" and anF: "a ^ n \<in> F" 
                    and rest: "wit_valid (eval_img F a) ws"
    by (metis surj_pair wit_valid.simps(2))
  have aN: "a \<in> N" using Cons.prems(4) an by simp
  have alg: "algebraic_over F a" using radical_algebraic[OF Cons.prems(1) n anF] .
  have sfEa: "Subfield (eval_img F a)" by (rule Subfield.subfield_eval_img[OF Cons.prems(1) alg])
  \<comment> \<open>The one-step extension @{term "eval_img F a"} lands in @{term N}.\<close>
  have "eval_img F a = generate_field (F \<union> {a})"
    by (rule Subfield.eval_img_eq_generate_field[OF Cons.prems(1) alg])
  moreover have "F \<union> {a} \<subseteq> N" using Cons.prems(2) aN by simp
  ultimately have EaN: "eval_img F a \<subseteq> N" using generate_field_least[OF N] by simp
  with Cons show ?case using an sfEa by auto
qed

subsection \<open>The normal radical closure of a radical tower is a solvable splitting field\<close>

text \<open>Suppose @{term Fs} is a radical tower over @{term F} whose top contains the
  finite root set @{term X} of an irreducible @{term F}-polynomial @{term P}.  Let
  @{term "Kq = generate_field (F \<union> X)"}.  Then there is a normal closure @{term N} and an
  @{term F}-polynomial @{term \<Psi>} exhibiting @{term N} as the splitting field
  \<open>generate_field (Kq \<union> {r. poly \<Psi> r = 0})\<close> over @{term Kq}, with @{term N} solvable over @{term F}.\<close>
theorem radical_tower_normal_closure_solvable:
  fixes F :: "complex set" and P :: "complex poly"
  assumes sfF: "Subfield F" and tower: "radical_tower F Fs"
    and P: "P \<in> poly_over F" and irrP: "irreducible_over F P"
    and Xdef: "X = {r. poly P r = 0}" and finX: "finite X" and XKq: "X \<subseteq> tower_top F Fs"
    and closed: "\<And>q :: complex poly. 0 < degree q \<Longrightarrow> \<exists>b. poly q b = 0"
  defines "Kq \<equiv> generate_field (F \<union> X)"
  obtains N \<Psi> where "Subfield N" and "Kq \<subseteq> N"
    and "\<Psi> \<in> poly_over F"
    and "N = generate_field (Kq \<union> {r. poly \<Psi> r = 0})"
    and "finite {r. poly \<Psi> r = 0}"
    and "\<And>r. poly \<Psi> r = 0 \<Longrightarrow> algebraic_over Kq r"
    and "Group.solvable (field_auto N F) (compose N) (identity N)"
proof -
  interpret F: Subfield F by (rule sfF)
  \<comment> \<open>The radical generators, extracted as the bases of a witness list; each is algebraic over @{term F}.\<close>
  obtain ws where wv: "wit_valid F ws" and kf: "kummer_fields F ws = Fs"
    using radical_tower_witnesses[OF sfF tower] by blast
  define as where "as \<equiv> List.map fst ws"
  have ktop_eq: "ktop F ws = tower_top F Fs" by (rule ktop_eq_tower_top[OF kf])
  \<comment> \<open>Each radical base lies in the tower top.\<close>
  have as_sub: "set as \<subseteq> tower_top F Fs"
    using as_def ktop_eq ktop_witness_bases_subset sfF wv by blast
  have alg_top: "\<forall>y \<in> tower_top F Fs. algebraic_over F y"
    by (rule radical_tower_top_algebraic[OF sfF tower])
  have algas: "\<And>a. a \<in> set as \<Longrightarrow> algebraic_over F a" using as_sub alg_top by blast
  \<comment> \<open>The witnessing polynomial: the given irreducible @{term P}, the cyclotomic factor for the
     exponent bound, and the minimal polynomials of the radical generators.\<close>
  define N0 where "N0 = prod_list (List.map snd ws)"
  have N0pos: "N0 > 0"
    unfolding N0_def using wit_valid_exps_pos[OF wv] by (induction ws) auto
  define cyc where "cyc \<equiv> (monom 1 N0 - 1 :: complex poly)"
  define \<Psi> where "\<Psi> \<equiv> P * cyc * prod_list (List.map (minpoly F) as)"
  \<comment> \<open>@{term \<Psi>} is a nonzero polynomial over @{term F}.\<close>
  have cycF: "cyc \<in> poly_over F"
    unfolding cyc_def using F.poly_over_monom[of 1 N0] F.one_closed F.poly_over_diff F.poly_over_1
    by simp
  have minF: "\<And>a. a \<in> set as \<Longrightarrow> minpoly F a \<in> poly_over F"
    by (rule Subfield.minpoly_over[OF sfF algas])
  have prodF: "prod_list (List.map (minpoly F) as) \<in> poly_over F"
    by (rule poly_over_prod_list[OF sfF]) (auto simp: minF)
  have PsiF: "\<Psi> \<in> poly_over F"
    unfolding \<Psi>_def using P cycF prodF by (auto intro: F.poly_over_mult)
  have cyc_eval: "poly cyc 0 = - 1"
    unfolding cyc_def using N0pos by (simp add: poly_monom)
  have cyc_nz: "cyc \<noteq> 0" using cyc_eval by (metis poly_0 neg_equal_0_iff_equal one_neq_zero)
  have P_nz: "P \<noteq> 0" using irrP by (simp add: irreducible_over_def)
  have minpoly_nz: "\<And>a. a \<in> set as \<Longrightarrow> minpoly F a \<noteq> 0"
    by (rule Subfield.minpoly_nonzero[OF sfF algas])
  have prod_nz: "prod_list (List.map (minpoly F) as) \<noteq> 0"
    by (metis imageE list.set_map minpoly_nz prod_list_poly_nonzero)
  have Psi_nz: "\<Psi> \<noteq> 0" unfolding \<Psi>_def using P_nz cyc_nz prod_nz by simp
  \<comment> \<open>Its root set.\<close>
  define R where "R = {r. poly \<Psi> r = 0}"
  have finR: "finite R" unfolding R_def using Psi_nz by (rule poly_roots_finite)
  \<comment> \<open>@{term X} (roots of @{term P}) is among the roots of @{term \<Psi>}.\<close>
  have XR: "X \<subseteq> R"
    using R_def Xdef \<Psi>_def by force
  \<comment> \<open>The splitting field.\<close>
  define N where "N \<equiv> generate_field (F \<union> R)"
  have sfN: "Subfield N" unfolding N_def by (rule subfield_generate_field)
  have "R \<subseteq> N" unfolding N_def using subset_generate_field by blast
  \<comment> \<open>@{term Kq} lies in @{term N} and @{term N} is the splitting field of @{term \<Psi>} over @{term Kq}.\<close>
  have KqN: "Kq \<subseteq> N"
    unfolding Kq_def N_def using XR generate_field_mono[of "F \<union> X" "F \<union> R"] by blast
  have N_split_Kq: "N \<equiv> generate_field (Kq \<union> R)"
    by (simp add: Kq_def N_def XR sup.assoc sup.absorb2)
  \<comment> \<open>Roots of @{term \<Psi>} are algebraic over @{term F}, hence over @{term Kq}.\<close>
  have FKq: "F \<subseteq> Kq" unfolding Kq_def using subset_generate_field by blast
  have algR_Kq: "\<And>r. poly \<Psi> r = 0 \<Longrightarrow> algebraic_over Kq r"
    by (meson FKq PsiF Psi_nz algebraic_over_def algebraic_over_mono)
  \<comment> \<open>Key objective: solvability of the Galois group of the splitting field @{term N} over @{term F}.\<close>
  have FN: "F \<subseteq> N" unfolding N_def using subset_generate_field by blast
  have dvdN0: "\<forall>x \<in> set ws. snd x dvd N0"
    by (simp add: N0_def prod_list_dvd)
  define \<zeta> where "\<zeta> \<equiv> unity_root N0"
  define Fz where "Fz \<equiv> eval_img F \<zeta>"
  \<comment> \<open>Step 0: the cyclotomic base @{term Fz} sits inside @{term N} (the roots of unity are roots of the
     cyclotomic factor @{term cyc} of @{term \<Psi>}).\<close>
  have zroot: "\<zeta> ^ N0 = 1" unfolding \<zeta>_def using unity_root_mem[OF N0pos] by simp
  have algz: "algebraic_over F \<zeta>" 
    using radical_algebraic[OF sfF N0pos] by (simp add: zroot) 
  have sfFz: "Subfield Fz" unfolding Fz_def by (rule Subfield.subfield_eval_img[OF sfF algz])
  have FFz: "F \<subseteq> Fz" unfolding Fz_def using Subfield.eval_img_base[OF sfF] by auto
  have zetaR: "\<zeta> \<in> R"
    using zroot by (simp add: cyc_def R_def \<Psi>_def poly_monom)
  have zetaN: "\<zeta> \<in> N" using zetaR \<open>R \<subseteq> N\<close> by blast
  have Fz_gen: "Fz = generate_field (F \<union> {\<zeta>})"
    unfolding Fz_def by (rule Subfield.eval_img_eq_generate_field[OF sfF algz])
  have FzN: "Fz \<subseteq> N"
    by (simp add: FN Fz_gen generate_field_least sfN zetaN)
  \<comment> \<open>Step 1: @{term N} is the splitting field of @{term \<Psi>} over @{term Fz}, so @{term "field_auto N Fz"}
     is finite; likewise over @{term F}.\<close>
  have PsiFz: "\<Psi> \<in> poly_over Fz" using PsiF poly_over_mono[OF FFz] by blast
  have N_split_Fz: "N = generate_field (Fz \<union> R)"
    by (simp add: Fz_gen N_def insert_absorb zetaR)
  have finGalF: "finite (field_auto N F)"
    using splitting_field_finite_galois[OF sfF PsiF Psi_nz] unfolding N_def R_def by simp
  \<comment> \<open>Step 2: enumerate the (finite) Galois group @{term "field_auto N F"}.\<close>
  obtain \<sigma>s where \<sigma>s: "set \<sigma>s = field_auto N F" using finite_list[OF finGalF] by blast
  \<comment> \<open>Step 3: each radical base is a root of its minimal polynomial (a factor of
     @{term \<Psi>}), hence in \<open>R \<subseteq> N\<close>; so the base tower @{term ws} lies in @{term N}.\<close>
  have asR: "set as \<subseteq> R"
    using F.minpoly_root algas poly_prod_list_root_iff 
    by (fastforce simp: \<Psi>_def R_def)
  have asN: "set as \<subseteq> N" using asR \<open>R \<subseteq> N\<close> by blast
  have wsN: "ktop F ws \<subseteq> N"
    using FN asN as_def ktop_subset_of_bases sfF sfN wv by auto
  \<comment> \<open>Step 4: fold the conjugate witnesses over the whole group, giving a pre-Kummer chain @{term CW}
     over @{term Fz} whose top @{term "ktop Fz CW"} lies in @{term N} and covers every conjugate.\<close>
  have \<sigma>sF: "\<forall>\<sigma> \<in> set \<sigma>s. \<sigma> \<in> field_auto N F" using \<sigma>s by simp
  obtain CW where CW: "pre_kummer_valid N0 Fz CW" "Fz \<subseteq> ktop Fz CW" "ktop Fz CW \<subseteq> N"
      "\<forall>\<sigma> \<in> set \<sigma>s. \<sigma> ` ktop F ws \<subseteq> ktop Fz CW"
    using conj_family_witnesses[OF sfN sfF FN wv wsN dvdN0 sfFz FzN FFz \<sigma>sF] by blast
  define T where "T \<equiv> ktop Fz CW"
  have sfT: "Subfield T" unfolding T_def by (rule subfield_ktop_pre[OF sfFz CW(1)])
  \<comment> \<open>The cyclotomic step over @{term F}: solvable, stable, and supplying the roots of unity.\<close>
  have zetaN': "unity_root N0 \<in> N" using zetaN by (simp add: \<zeta>_def)
  have Fz_eq: "Fz = eval_img F (unity_root N0)" by (simp add: Fz_def \<zeta>_def)
  have rouFz: "\<forall>w. w ^ N0 = 1 \<longrightarrow> w \<in> Fz" 
    using cyclotomic_step_solvable_and_stable[OF sfN sfF FN N0pos zetaN']
    unfolding Fz_eq by force
  \<comment> \<open>Step 5: @{term "N = T"}.\<close>
  have FzT: "Fz \<subseteq> T" unfolding T_def by (rule CW(2))
  \<comment> \<open>The identity automorphism belongs to the enumerated group; the base tower top lies in @{term T}.\<close>
  have wsT: "ktop F ws \<subseteq> T"
  proof -
    have cN: "complex_subfield N" using sfN by (simp add: complex_subfield_iff_subfield)
    have idg: "identity N \<in> set \<sigma>s" using identity_field_auto[OF cN FN] \<sigma>s by simp
    have img: "identity N ` ktop F ws \<subseteq> ktop Fz CW" using CW(4) idg by blast
    show ?thesis
      using T_def img wsN by auto
  qed
  \<comment> \<open>\<^emph>\<open>Conjugacy.\<close>  Each root @{term b} of @{term "minpoly F a"} (for a radical generator @{term a}) is a
     Galois conjugate @{term "\<sigma> a"} of @{term a} under some @{term "\<sigma> \<in> field_auto N F"}, hence lies in
     @{term "\<sigma> ` ktop F ws \<subseteq> T"} (as @{term "a \<in> ktop F ws"}).\<close>
  have minroot_T: "b \<in> T" if a: "a \<in> set as" and mb: "poly (minpoly F a) b = 0" for a b
  proof -
    define m where "m \<equiv> minpoly F a"
    have alga: "algebraic_over F a" by (rule algas[OF a])
    have irrm: "irreducible_over F m" unfolding m_def by (rule irreducible_over_minpoly[OF sfF alga])
    have mF: "m \<in> poly_over F" unfolding m_def by (rule Subfield.minpoly_over[OF sfF alga])
    have ma: "poly m a = 0" unfolding m_def by (rule Subfield.minpoly_root[OF sfF alga])
    define Rm where "Rm \<equiv> {r. poly m r = 0}"
    have mnz: "m \<noteq> 0" unfolding m_def by (rule Subfield.minpoly_nonzero[OF sfF alga])
    have finRm: "finite Rm" unfolding Rm_def using mnz by (rule poly_roots_finite)
    have algRm: "\<And>r. r \<in> Rm \<Longrightarrow> algebraic_over F r"
      unfolding Rm_def using mF mnz unfolding algebraic_over_def by blast
    have aRm: "a \<in> Rm" using ma by (simp add: Rm_def)
    have bRm: "b \<in> Rm" using mb by (simp add: Rm_def m_def)
    \<comment> \<open>The roots of @{term m} all lie in @{term N} (\<open>m\<close> divides \<open>\<Psi>\<close>).\<close>
    have RmR: "Rm \<subseteq> R"
    proof
      fix r assume "r \<in> Rm"
      then have "poly m r = 0" by (simp add: Rm_def)
      then have "poly (prod_list (List.map (minpoly F) as)) r = 0"
        using a by (force simp: m_def poly_prod_list_root_iff)
      then show "r \<in> R" by (simp add: \<Psi>_def R_def)
    qed
    have RmN: "Rm \<subseteq> N" using RmR \<open>R \<subseteq> N\<close> by blast
    \<comment> \<open>Transitivity: an @{term F}-homomorphism on the root-generated field sending @{term a} to @{term b}.\<close>
    have Rm_eq: "Rm = {r. poly m r = 0}" by (simp add: Rm_def)
    obtain \<sigma> where hom0: "field_hom_on (generate_field (F \<union> Rm)) \<sigma>"
        and s_ab: "\<sigma> a = b" and fixF: "\<forall>x\<in>F. \<sigma> x = x"
        and onto0: "\<sigma> ` generate_field (F \<union> Rm) = generate_field (F \<union> Rm)"
      using galois_transitive_irreducible[OF sfF finRm algRm mF irrm Rm_eq closed aRm bRm]
      by blast
    \<comment> \<open>Extend @{term \<sigma>} over the remaining roots of @{term \<Psi>} to all of @{term N}.\<close>
    define K0 where "K0 \<equiv> generate_field (F \<union> Rm)"
    have algRmore: "algebraic_over K0 r" if "r \<in> R" for r
    proof -
      have "algebraic_over F r" using that PsiF Psi_nz R_def unfolding algebraic_over_def by blast
      then show "algebraic_over K0 r"
        by (metis K0_def algebraic_over_mono le_sup_iff subset_generate_field)
    qed
    obtain g where homg: "field_hom_on (generate_field (K0 \<union> R)) g" and gK0: "\<forall>x\<in>K0. g x = \<sigma> x"
      using field_hom_on_extend_finite[OF closed finR hom0[folded K0_def] algRmore] by blast
    \<comment> \<open>@{term "generate_field (K0 \<union> R) = N"}.\<close>
    have K0R_N: "generate_field (K0 \<union> R) = N"
      by (simp add: K0_def N_def RmR Un_assoc sup.absorb2)
    have homgN: "field_hom_on N g" using homg by (simp add: K0R_N)
    have fixFg: "\<And>x. x \<in> F \<Longrightarrow> g x = x"
      by (simp add: K0_def fixF gK0 generate_field.generate_field_base)
    \<comment> \<open>@{term g} maps @{term R} into @{term R} (it fixes @{term F} and preserves roots of @{term \<Psi>}),
       and injectively, so onto @{term R}; hence @{term g} maps @{term N} onto @{term N}.\<close>
    have gR_sub: "g ` R \<subseteq> R"
      using hom_preserves_roots[OF homgN sfF FN fixFg PsiF] \<open>R \<subseteq> N\<close>
      by (auto simp: R_def)
    have injR: "inj_on g R"
      using \<open>R \<subseteq> N\<close> field_hom_on.inj_on homgN inj_on_subset by blast
    have gR: "g ` R = R" by (rule endo_inj_surj[OF finR gR_sub injR])
    have gUn: "g ` (F \<union> R) = F \<union> R" using gR by (simp add: fixFg image_Un)
    have FR_N: "F \<union> R \<subseteq> N" using FN \<open>R \<subseteq> N\<close> by simp
    have gN: "g ` N = N"
      by (metis FR_N N_def field_hom_on.image_generate_field_eq gUn homgN)
    \<comment> \<open>So @{term "restrict g N"} is an @{term F}-automorphism of @{term N} sending @{term a} to @{term b}.\<close>
    have aut: "restrict g N \<in> field_auto N F"
      by (rule field_hom_on_imp_field_auto[OF homgN gN fixFg FN])
    have "a \<in> N" using a asN by blast
    have aws: "a \<in> ktop F ws"
      using ktop_witness_bases_subset[OF sfF wv] a by (auto simp: as_def)
    have "restrict g N a = b"
      using K0_def \<open>a \<in> N\<close> aRm gK0 s_ab by auto 
    then show ?thesis
    \<comment> \<open>@{term b} is the image of @{term "a \<in> ktop F ws"} under an automorphism in the family.\<close>
      using CW(4) T_def \<sigma>s aut aws by blast
  qed
    \<comment> \<open>Step 5: @{term "N = T"}.\<close>
  have RT: "R \<subseteq> T"
  proof
    fix r assume "r \<in> R"
    then consider "poly P r = 0" | "poly cyc r = 0" | "poly (prod_list (List.map (minpoly F) as)) r = 0"
      by (force simp: \<Psi>_def R_def)
    then show "r \<in> T"
    proof cases
      case 1
      then show ?thesis 
        using XKq Xdef ktop_eq wsT by auto
    next
      case 2
      then have "r ^ N0 = 1" unfolding cyc_def by (simp add: poly_monom)
      then show ?thesis using rouFz FzT by blast
    next
      case 3
      then show ?thesis 
        using minroot_T by (auto simp: poly_prod_list_root_iff)
    qed
  qed
  have "F \<subseteq> T" using FFz FzT by blast
  then have "F \<union> R \<subseteq> T" using RT by blast
  then have NT: "N=T"
    using generate_field_least sfT CW(3) unfolding N_def T_def by (metis subset_antisym)
    \<comment> \<open>Step 6: solvability of @{term N} over @{term Fz} (roots of unity in @{term Fz}).\<close>
  have solvNFz: "Group.solvable (field_auto N Fz) (compose N) (identity N)"
    using pre_kummer_chain_galois_solvable[OF sfFz rouFz CW(1)] NT by (simp flip: T_def)
  \<comment> \<open>Step 7: combine with the solvable cyclotomic step over @{term F}.\<close>
  obtain solvFzF: "Group.solvable (field_auto Fz F) (compose Fz) (identity Fz)"
    and stableFz: "\<And>\<sigma>. \<sigma> \<in> field_auto N F \<Longrightarrow> \<sigma> ` Fz = Fz"
    using Fz_eq N0pos NT cyclotomic_step_solvable_and_stable sfF
    using \<open>F \<subseteq> T\<close> sfT zetaN' by presburger
  have solvN: "Group.solvable (field_auto N F) (compose N) (identity N)"
    using galois_solvable_tower_step[where K = N and E = Fz and F = F]
    using FFz FzN sfFz sfN solvFzF solvNFz stableFz by blast
  show ?thesis
    using N_split_Kq PsiF R_def algR_Kq finR solvN that by auto
qed

text \<open>The preceding construction is the reusable bridge from a radical tower to the Galois group
  of the field generated by the roots of an irreducible polynomial.  The normal radical top is an
  auxiliary object: after its solvability is established, the splitting-field restriction theorem
  descends solvability to the root field itself.\<close>
theorem radical_tower_root_field_solvable:
  fixes F :: "complex set" and P :: "complex poly"
  assumes sfF: "Subfield F" and tower: "radical_tower F Fs"
    and P: "P \<in> poly_over F" and irrP: "irreducible_over F P"
    and Xdef: "X = {r. poly P r = 0}" and finX: "finite X"
    and Xtop: "X \<subseteq> tower_top F Fs"
    and closed: "\<And>q :: complex poly. 0 < degree q \<Longrightarrow> \<exists>b. poly q b = 0"
  defines "Kq \<equiv> generate_field (F \<union> X)"
  shows "Group.solvable (field_auto Kq F) (compose Kq) (identity Kq)"
proof -
  obtain N Psi where sfN: "Subfield N" and KqN: "Kq \<subseteq> N"
      and Psi: "Psi \<in> poly_over F"
      and N: "N = generate_field (Kq \<union> {r. poly Psi r = 0})"
      and finR: "finite {r. poly Psi r = 0}"
      and solvN: "Group.solvable (field_auto N F) (compose N) (identity N)"
    unfolding Kq_def
    by (blast intro: radical_tower_normal_closure_solvable
              [OF sfF tower P irrP Xdef finX Xtop closed, unfolded Kq_def])
  have sfKq: "Subfield Kq"
    unfolding Kq_def by (rule subfield_generate_field)
  have FKq: "F \<subseteq> Kq"
    unfolding Kq_def using subset_generate_field by blast
  have Psi_nz: "Psi \<noteq> 0"
    using finR infinite_UNIV_char_0 by fastforce
  have "Psi \<in> poly_over Kq"
    using Psi poly_over_mono[OF FKq] by blast
  then have splitN: "splitting_field Kq Psi N"
    unfolding splitting_field_def
    using Psi_nz N by (simp add: gen_subfield_eq_generate_field poly_root_set_def)
  have "X \<subseteq> Kq"
    unfolding Kq_def using subset_generate_field by blast
  then have XN: "X \<subseteq> N" using KqN by blast
  have stableKq: "\<And>\<sigma>. \<sigma> \<in> field_auto N F \<Longrightarrow> \<sigma> ` Kq = Kq"
    using root_generated_stable[OF sfN sfF _ P Xdef XN finX] FKq KqN by (auto simp: Kq_def)
  show ?thesis
    by (rule galois_splitting_subfield_solvable[OF sfKq sfF FKq Psi splitN stableKq solvN])
qed

end
