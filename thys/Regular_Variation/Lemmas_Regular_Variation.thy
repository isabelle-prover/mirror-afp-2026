(*  Title:   Lemmas_Regular_Variation.thy
    Author:  Michikazu Hirata
*)

section \<open>Lemmas\<close>
theory Lemmas_Regular_Variation
imports
   "HOL-Probability.Probability"
   "Standard_Borel_Spaces.StandardBorel"
begin

subsection \<open> General Lemmas\<close>
lemma image_mono_on_continuous_on_Icc:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b :: linorder_topology"
  assumes  ab:"a \<le> b" and mono:"mono_on {a..b} f"
    and cont:"continuous_on {a..b} f"
  shows "f ` {a..b} = {f a..f b}"
  using IVT'[OF _ _ ab cont] mono_onD[OF mono] by fastforce

lemma image_mono_on_continuous_on_Ic:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b :: linorder_topology"
  assumes mono:"mono_on {a..} f"
    and cont:"continuous_on {a..} f"
    and lim:"filterlim f at_top at_top"
  shows "f ` {a..} = {f a..}"
proof -
  have  "f ` {a..} = f ` (\<Union>b\<in>{a..}. {a..b})"
    by fastforce
  also have "... = (\<Union>b\<in>{a..}. f ` {a..b})"
    by blast
  also have "... = (\<Union>b\<in>{a..}. {f a..f b})"
  proof -
    have "\<And>b. a \<le> b \<Longrightarrow> f ` {a..b} = {f a.. f b}"
      by(intro image_mono_on_continuous_on_Icc mono_on_subset[OF mono]
          continuous_on_subset[OF cont]) auto
    thus ?thesis
      by fast
  qed
  also have "... = {f a..}"
  proof safe
    fix y
    assume y:"f a \<le> y"
    obtain b where b: "a \<le> b" "y \<le> f b"
      by (metis eventually_at_top_linorder filterlim_at_top lim nle_le)
    thus "y \<in>  (\<Union>b\<in>{a..}. {f a..f b})"
      using y by fastforce
  qed auto
  finally show ?thesis .
qed

lemma image_mono_on_continuous_on_Ioo:
  fixes f :: "'a::{linear_continuum_topology} \<Rightarrow> 'b :: linorder_topology"
  assumes ab:"a \<le> b" and mono:"strict_mono_on {a..b} f"
    and cont:"continuous_on {a..b} f"
  shows "f ` {a<..<b} = {f a<..<f b}"
proof -
  have "f ` {a<..<b} = f ` {a..b} - {f a, f b}"
    apply safe
       apply fastforce
      apply (metis ab mono atLeastAtMost_iff greaterThanLessThan_iff le_less less_le
                   strict_mono_on_less)
    apply (metis (mono_tags, opaque_lifting) ab mono
        atLeastAtMost_iff greaterThanLessThan_iff less_le
        monotone_onD order.refl)
    apply (metis atLeastAtMost_iff greaterThanLessThan_iff imageI less_le)
    done
  also have "... = {f a..f b} - {f a, f b}"
    by(simp add: image_mono_on_continuous_on_Icc
        [OF ab strict_mono_on_imp_mono_on[OF mono] cont])
  also have "... = {f a<..<f b}"
    by fastforce
  finally show ?thesis .
qed

lemma image_mono_on_continuous_on_Ioc:
  fixes f :: "'a::{linear_continuum_topology} \<Rightarrow> 'b :: linorder_topology"
  assumes ab:"a \<le> b" and mono:"strict_mono_on {a..b} f"
    and cont:"continuous_on {a..b} f"
  shows "f ` {a<..b} = {f a<..f b}"
proof -
  have "f ` {a<..b} = f ` {a..b} - {f a}"
    apply safe
      apply fastforce
     apply (metis ab mono atLeastAtMost_iff greaterThanAtMost_iff less_le order.refl
                  strict_mono_on_eqD)
    apply (metis atLeastAtMost_iff greaterThanAtMost_iff image_eqI less_le)
    done
  also have "... = {f a..f b} - {f a}"
    by(simp add: image_mono_on_continuous_on_Icc
        [OF ab strict_mono_on_imp_mono_on[OF mono] cont])
  also have "... = {f a<..f b}"
    by fastforce
  finally show ?thesis .
qed

lemma image_mono_on_continuous_on_greaterThan:
  fixes f :: "'a::{linear_continuum_topology} \<Rightarrow> 'b :: linorder_topology"
  assumes mono:"strict_mono_on {a..} f"
    and cont:"continuous_on {a..} f"
    and lim:"filterlim f at_top at_top"
  shows "f ` {a<..} = {f a<..}"
proof -
  have "f ` {a<..} = f ` {a..} - {f a}"
    apply safe
      apply fastforce
     apply (metis mono atLeast_iff less_le nle_le strict_mono_on_eq)
    apply (metis greaterThan_iff imageI less_le)
    done
  also have "... = {f a..} - {f a}"
    by(simp add: image_mono_on_continuous_on_Ic
        [OF strict_mono_on_imp_mono_on[OF mono] cont lim])
  also have "... = {f a<..}"
    by fastforce
  finally show ?thesis .
qed

lemma image_antimono_on_continuous_on_Icc:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b :: linorder_topology"
  assumes ab:"a \<le> b" and mono:"antimono_on {a..b} f"
    and cont:"continuous_on {a..b} f"
  shows "f ` {a..b} = {f b..f a}"
  using IVT2'[OF _ _ ab cont] monotone_onD[OF mono] by fastforce

lemma image_antimono_on_continuous_on_Ioc:
  fixes f :: "'a::{linear_continuum_topology} \<Rightarrow> 'b :: linorder_topology"
  assumes ab:"a \<le> b" and mono:"strict_antimono_on {a..b} f"
    and cont:"continuous_on {a..b} f"
  shows "f ` {a<..b} = {f b..<f a}"
proof -
  have "f ` {a<..b} = f ` {a..b} - {f a}"
    apply safe
      apply fastforce
    apply (metis (mono_tags, lifting) assms(1,2) atLeastAtMost_iff
        greaterThanAtMost_iff less_le monotone_onD order.refl)
    apply (metis atLeastAtMost_iff greaterThanAtMost_iff imageI less_le)
    done
  also have "... = {f b..f a} - {f a}"
    using mono
    by(subst image_antimono_on_continuous_on_Icc[OF ab _ cont])
      (auto simp: monotone_on_def le_less)
  also have "... = {f b..<f a}"
    by fastforce
  finally show ?thesis .
qed

lemma image_mult_greaterThanLessThan[simp]:
  fixes c :: real
  assumes "0 < c"
  shows "(*) c ` {a<..<b} = {c * a<..<c * b}"
proof -
  have "(*) c ` {a<..<b} = (*) c ` ball ((b + a) / 2) ((b - a) / 2)"
    by(rule arg_cong[where f="image (\<lambda>x. c * x)"])
      (simp add: ball_eq_greaterThanLessThan add_divide_distrib[symmetric]
                 diff_divide_distrib[symmetric])
  also have "... = ball (c * (b + a) / 2) (c * (b - a) / 2)"
    using ball_scale[of c "(b + a) / 2" "(b - a) / 2"] assms by simp
  also have "... = {c * a<..<c * b}"
    by(simp add: ball_eq_greaterThanLessThan add_divide_distrib[symmetric]
        distrib_left[symmetric] diff_divide_distrib[symmetric] right_diff_distrib[symmetric])
  finally show ?thesis .
qed

lemma image_times_atLeastLessThan[simp]:
  fixes c :: real
  assumes "0 < c"
  shows "(*) c ` {a<..b} = {c * a<..c * b}"
proof -
  have "(*) c ` {a<..b} = (*) c ` ({a<..<b+1} \<inter> {a-1..b})"
    by(rule arg_cong[where f="image (\<lambda>x. c * x)"]) auto
  also have "... = (*) c ` {a<..<b+1} \<inter> (*) c ` {a-1..b}"
    by(subst image_Int) (use assms in auto)
  also have "... = {c * a<..<c * (b + 1)} \<inter> {c * (a - 1)..c * b}"
    using assms by simp
  also have "... = {c * a<..c * b}"
    unfolding set_eq_iff greaterThanLessThan_iff Int_iff atLeastAtMost_iff greaterThanAtMost_iff
    by(intro allI iffI) (use assms in argo)+
  finally show ?thesis .
qed

lemma image_power_Icc_pos:
  assumes "0 \<le> \<rho>"
    and "0 < a" and "a \<le> b"
  shows "(\<lambda>x::real. x powr \<rho>) ` {a..b} = {a powr \<rho>..b powr \<rho>}"
  using assms
  by(intro image_mono_on_continuous_on_Icc mono_onI powr_mono2 continuous_on_powr)
    auto

lemma image_inverse_power_Icc_pos:
  assumes "0 \<le> \<rho>"
    and "0 < a" and "a \<le> b"
  shows "(\<lambda>x::real. 1 / x powr \<rho>) ` {a..b} = {1 / b powr \<rho>..1 / a powr \<rho>}"
  using assms
  by(intro image_antimono_on_continuous_on_Icc monotone_onI divide_left_mono powr_mono2
      continuous_on_divide continuous_on_powr)
     auto

lemma image_power_Icc_neg:
  assumes "\<rho> \<le> 0"
    and "0 < a" and "a \<le> b"
  shows "(\<lambda>x::real. x powr \<rho>) ` {a..b} = {b powr \<rho>..a powr \<rho>}"
  using assms
  by(intro image_antimono_on_continuous_on_Icc monotone_onI powr_mono2' continuous_on_powr)
    auto

lemma image_inverse_power_Icc_neg:
  assumes "\<rho> \<le> 0"
    and "0 < a" and "a \<le> b"
  shows "(\<lambda>x::real. 1 / x powr \<rho>) ` {a..b} = {1 / a powr \<rho>..1 / b powr \<rho>}"
  using assms
  by(intro image_mono_on_continuous_on_Icc continuous_on_divide
      divide_left_mono mono_onI powr_mono2' continuous_on_powr)
     auto

lemma image_times_atLeastLessThan'[simp]:
  fixes c :: real
  assumes "0 < c"
  shows "(\<lambda>x. x * c) ` {a<..b} = {c * a<..c * b}"
  using assms by(simp add: mult.commute[of _ c])

lemma bounded_times_comp:
  fixes f g::"'a \<Rightarrow> 'b::real_normed_field"
  assumes "bounded (f ` S)"
    and "bounded (g ` S)"
  shows "bounded ((\<lambda>x. f x * g x) ` S)"
proof -
  obtain a b where "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> a" "\<And>x. x \<in> S \<Longrightarrow> norm (g x) \<le> b"
                   "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> a"
    using assms by (metis bounded_pos less_eq_real_def rev_image_eqI)
  thus ?thesis
    by(auto simp: bounded_iff norm_mult intro!: exI[where x="a * b"] mult_mono)
qed

lemma antimono_on_iff_uminus_mono_on:
  fixes f :: "_ \<Rightarrow> _ :: ordered_ab_group_add"
  shows "antimono_on A f \<longleftrightarrow> mono_on A (\<lambda>x. -f x)"
  by(auto simp: monotone_on_def)

lemma filterlim_Pair_component:
 "LIM x F. f x :> G \<Longrightarrow> LIM x H. g x :> I \<Longrightarrow> LIM (x, y) F \<times>\<^sub>F H. (f x, g y) :> G \<times>\<^sub>F I"
  by (metis filterlim_def filtermap_prod_filter map_prod_def prod_filter_mono)

lemma eventually_eventually_prod_filter_principal1:
  "eventually P (F \<times>\<^sub>F principal A) \<longleftrightarrow> eventually (\<lambda>x. \<forall>y\<in>A. P (x, y)) F"
proof
  assume h:"\<forall>\<^sub>F x in F. \<forall>y\<in>A. P (x, y)"
  show "eventually P (F \<times>\<^sub>F principal A)"
    unfolding eventually_prod_filter
    by(intro exI[where x="\<lambda>x. \<forall>y\<in>A. P (x, y)"] exI[where x="\<lambda>y. y \<in> A"])
      (use h in "auto simp: eventually_principal")
qed(auto dest: eventually_eventually_prod_filter1 simp: eventually_principal)

lemma eventually_eventually_prod_filter_principal2:
  "eventually P (principal A \<times>\<^sub>F G) \<longleftrightarrow> eventually (\<lambda>y. \<forall>x\<in>A. P (x, y)) G"
proof
  assume h:"\<forall>\<^sub>F y in G. \<forall>x\<in>A. P (x, y)"
  show "eventually P (principal A \<times>\<^sub>F G)"
    unfolding eventually_prod_filter
    by(intro exI[where x="\<lambda>y. \<forall>x\<in>A. P (x, y)"] exI[where x="\<lambda>x. x \<in> A"])
      (use h in "auto simp: eventually_principal")
qed(auto dest: eventually_eventually_prod_filter2 simp: eventually_principal)

(* TODO: extend the following lemma *)
lemma prod_filter_distrib_right:
  "F \<times>\<^sub>F (G \<squnion> H) = F \<times>\<^sub>F G \<squnion> F \<times>\<^sub>F H"
proof(rule filter_eqI)
  fix P
  show "eventually P (F \<times>\<^sub>F (G \<squnion> H)) =
         eventually P (F \<times>\<^sub>F G \<squnion> F \<times>\<^sub>F H)"
  proof
    assume "eventually P (F \<times>\<^sub>F (G \<squnion> H))"
    then obtain Pf Pg where "eventually Pf F" "eventually Pg G" "eventually Pg H"
                            "\<forall>x y. Pf x \<longrightarrow> Pg y \<longrightarrow> P (x, y)"
      by(auto simp: eventually_prod_filter eventually_sup)
    thus "eventually P (F \<times>\<^sub>F G \<squnion> F \<times>\<^sub>F H)"
      by(auto simp: eventually_sup eventually_prod_filter)
  next
    assume "eventually P (F \<times>\<^sub>F G \<squnion> F \<times>\<^sub>F H)"
    then obtain Pf Pg Pf' Ph where h:
      "eventually Pf F" "eventually Pg G" "\<forall>x y. Pf x \<longrightarrow> Pg y \<longrightarrow> P (x, y)"
      "eventually Pf' F" "eventually Ph H" "\<forall>x y. Pf' x \<longrightarrow> Ph y \<longrightarrow> P (x, y)"
      by(auto simp: eventually_sup eventually_prod_filter)
    thus "eventually P (F \<times>\<^sub>F (G \<squnion> H))"
      unfolding eventually_prod_filter
      by(intro exI[where x="\<lambda>x. Pf x \<and> Pf' x"] exI[where x="\<lambda>y. Pg y \<or> Ph y"])
        (auto simp: eventually_sup eventually_conj eventually_mono)
  qed
qed

lemma suminf_const_infinity:
  fixes a :: ennreal
  assumes a:"0 < a"
  shows "(\<Sum>n. a) = \<top>"
proof -
  have *:"(\<Union>n. {real_of_int (from_nat_into UNIV n)..<real_of_int (from_nat_into UNIV n + 1)})
           = UNIV"
  proof safe
    fix x :: real
    have "\<exists>n. real_of_int (from_nat_into UNIV n) \<le> x
              \<and> x < real_of_int (from_nat_into UNIV n + 1)"
     by (metis UNIV_I countableI_type floor_correct from_nat_into_to_nat_on)
    thm from_nat_into_to_nat_on
    thus "x \<in> (\<Union>n. {real_of_int (from_nat_into UNIV n)..<real_of_int (from_nat_into UNIV n + 1)})"
      by auto
  qed auto
  have **:"disjoint_family
            (\<lambda>n. {real_of_int (from_nat_into UNIV n)..<real_of_int (from_nat_into UNIV n + 1)})"
  proof -
    have "\<And>n m. n \<noteq> m \<Longrightarrow> from_nat_into UNIV n \<noteq> (from_nat_into UNIV m :: int)"
      by simp
    thus ?thesis
      unfolding disjoint_family_on_def
      by (metis Int_emptyI atLeastLessThan_iff floor_exists1)
  qed
  have "(\<Sum>n. a) = (\<Sum>n. 
         (\<integral>\<^sup>+ x\<in>{real_of_int (from_nat_into UNIV n)..<real_of_int (from_nat_into UNIV n + 1)}.
                a \<partial>lborel))"
    by(auto intro!: suminf_cong simp: nn_integral_cmult_indicator)
  also have "... = (\<integral>\<^sup>+ x\<in>\<Union>n.
            {real_of_int (from_nat_into UNIV n)..<real_of_int (from_nat_into UNIV n + 1)}.
             a \<partial>lborel)"
    by(rule nn_integral_disjoint_family[symmetric])
      (use ** in auto)
  also have "... = (\<integral>\<^sup>+ x\<in>UNIV. a \<partial>lborel)"
    unfolding * by fastforce
  also have "(\<integral>\<^sup>+ x\<in>UNIV. a \<partial>lborel) = a * emeasure lborel UNIV"
    by(simp add: nn_integral_cmult_indicator)
  also have "... = \<top>"
    using a by force
  finally show ?thesis
    by simp
qed

subsection \<open>Limit\<close>
lemma tendsto_sandwich_mult_const:
  fixes c :: real
  assumes ev: "\<And>e::real. 0 < e \<Longrightarrow> eventually (\<lambda>n. f e \<le> g n / c \<and> g n / c \<le> h e) net"
    and limf:"(f \<longlongrightarrow> 1) (at_right 0)" and limh:"(h \<longlongrightarrow> 1) (at_right 0)"
  shows "(g \<longlongrightarrow> c) net"
proof -
  have "((\<lambda>n. g n / c) \<longlongrightarrow> 1) net"
    unfolding tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e:"0 < e"
    obtain a where a_pos:"0 < a" and a:"\<And>a'. 0 < a' \<Longrightarrow> a' < a \<Longrightarrow> \<bar>f a' - 1\<bar> < e"
      using limf e unfolding tendsto_iff eventually_at_right[OF e]
      by(auto simp: dist_real_def)
    obtain b where b_pos:"0 < b" and b:"\<And>b'. 0 < b' \<Longrightarrow> b' < b \<Longrightarrow> \<bar>h b' - 1\<bar> < e"
      using limh e unfolding tendsto_iff eventually_at_right[OF e]
      by(auto simp: dist_real_def)
    show " \<forall>\<^sub>F x in net. \<bar>g x / c - 1\<bar> < e"
    proof(safe intro!: eventually_mono[OF ev[of "min a b / 2"]])
      fix x
      assume le1:"f (min a b / 2) \<le> g x / c"
        and le2:"g x / c \<le> h (min a b / 2)"
      have "1 - e < f (min a b / 2)"
        using a[of "min a b / 2"] a_pos b_pos by argo
      also have "... \<le> g x / c"
        by fact
      finally have *:"1 - e < g x / c" .
      have "g x / c \<le> h (min a b / 2)"
        by fact
      also have "... <  e + 1"
        using b[of "min a b / 2"] a_pos b_pos by argo
      finally show "\<bar>g x / c - 1\<bar> < e"
        using * by auto
    qed(use a_pos b_pos in argo)
  qed
  from asymp_equivI'[OF this]
  show ?thesis
    by(auto simp: asymp_equivD_const)
qed

lemma asymp_equiv_Limsup_cong_ereal:
  assumes equiv:"f \<sim>[F] g"
    and nonneg1:"\<forall>\<^sub>F x in F. 0 \<le> f x"
    and nonneg2:"\<forall>\<^sub>F x in F. 0 \<le> g x"
  shows "Limsup F (\<lambda>x. ereal (f x)) = Limsup F (\<lambda>x. ereal (g x))"
proof(cases "F = \<bottom>")
  assume F:"F \<noteq> \<bottom>"
  have *:"Limsup F (\<lambda>x. ereal (f x)) \<le> Limsup F (\<lambda>x. ereal (g x))"
    if equiv:"f \<sim>[F] g"
    and nonneg1:"\<forall>\<^sub>F x in F. 0 \<le> f x"
    and nonneg2:"\<forall>\<^sub>F x in F. 0 \<le> g x" for f g
  proof -
    have Limsup1:"0 \<le> Limsup F (\<lambda>x. ereal (f x))"
      by(auto intro!: le_Limsup nonneg1 F)
    have Limsup2:"0 \<le> Limsup F (\<lambda>x. ereal (g x))"
      by(auto intro!: le_Limsup nonneg2 F)
    have le:"Limsup F (\<lambda>x. ereal (f x))
        \<le> ereal c * Limsup F (\<lambda>x. ereal (g x))" if c:"1 < c" for c :: real
    proof -
      have "Limsup F (\<lambda>x. ereal (f x)) \<le> Limsup F (\<lambda>x. ereal c * ereal (g x))"
        by(intro Limsup_mono eventually_mono[OF
              eventually_conj[OF eventually_conj[OF nonneg1 nonneg2]
                asymp_equiv_imp_eventually_le[OF equiv c]]])
          auto
      also have "... = ereal c * Limsup F (\<lambda>x. ereal (g x))"
        by(subst Limsup_ereal_mult_left) (use F c in auto)
      finally show ?thesis .
    qed
    have *:"((\<lambda>c. ereal c * Limsup F (\<lambda>x. ereal (g x)))
                  \<longlongrightarrow> Limsup F (\<lambda>x. ereal (g x))) (at_right 1)"
    proof -
      have "((\<lambda>c. ereal c) \<longlongrightarrow> ereal 1) (at_right 1)"
        by simp
      from tendsto_mult_ereal[OF this tendsto_const[of "Limsup F (\<lambda>x. ereal (g x))"]]
      show ?thesis
        by simp
    qed
    show ?thesis
      using le
      by(intro tendsto_lowerbound[OF *] eventually_at_rightI[where b=2]) auto
  qed
  show ?thesis
    by(intro antisym * assms asymp_equiv_symI)
qed simp

lemma asymp_equiv_Liminf_cong_ereal:
  assumes equiv:"f \<sim>[F] g"
    and nonneg1:"\<forall>\<^sub>F x in F. 0 \<le> f x"
    and nonneg2:"\<forall>\<^sub>F x in F. 0 \<le> g x"
  shows "Liminf F (\<lambda>x. ereal (f x)) = Liminf F (\<lambda>x. ereal (g x))"
proof(cases "F = \<bottom>")
  assume F:"F \<noteq> \<bottom>"
  have *:"Liminf F (\<lambda>x. ereal (f x)) \<le> Liminf F (\<lambda>x. ereal (g x))"
    if equiv:"f \<sim>[F] g"
    and nonneg1:"\<forall>\<^sub>F x in F. 0 \<le> f x"
    and nonneg2:"\<forall>\<^sub>F x in F. 0 \<le> g x" for f g
  proof -
    have le:"Liminf F (\<lambda>x. ereal (f x))
        \<le> ereal c * Liminf F (\<lambda>x. ereal (g x))" if c:"1 < c" for c :: real
    proof -
      have "Liminf F (\<lambda>x. ereal (f x)) \<le> Liminf F (\<lambda>x. ereal c * ereal (g x))"
        by(intro Liminf_mono eventually_mono[OF
              eventually_conj[OF eventually_conj[OF nonneg1 nonneg2]
                asymp_equiv_imp_eventually_le[OF equiv c]]])
          auto
      also have "... = ereal c * Liminf F (\<lambda>x. ereal (g x))"
        by(subst Liminf_ereal_mult_left) (use F c in auto)
      finally show ?thesis .
    qed
    have *:"((\<lambda>c. ereal c * Liminf F (\<lambda>x. ereal (g x)))
              \<longlongrightarrow> Liminf F (\<lambda>x. ereal (g x))) (at_right 1)"
    proof -
      have "((\<lambda>c. ereal c) \<longlongrightarrow> ereal 1) (at_right 1)"
        by simp
      from tendsto_mult_ereal[OF this tendsto_const[of "Liminf F (\<lambda>x. ereal (g x))"]]
      show ?thesis
        by simp
    qed
    show ?thesis
      using le
      by(intro tendsto_lowerbound[OF *] eventually_at_rightI[where b=2]) auto
  qed
  show ?thesis
    by(intro antisym * assms asymp_equiv_symI)
qed simp

lemma tendsto_at_topI_sequentially_real':
  fixes f :: "real \<Rightarrow> real"
  assumes mono: "mono_on {K..} f"
    and limseq: "(\<lambda>n. f (real n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_top"
proof -
  have mono2:"mono (\<lambda>x. if x < K then f K else f x)"
    using mono_onD[OF mono] by(auto intro!: monoI)
  obtain N where "K < real N"
    using reals_Archimedean2 by blast
  hence "(\<lambda>n. (\<lambda>x. if x < K then f K else f x) (real n)) \<longlonglongrightarrow> y"
    by(auto intro!: tendsto_cong[THEN iffD1,OF _ limseq]
        eventually_at_top_linorderI[where c=N])
  hence lim:"((\<lambda>x. if x < K then f K else f x) \<longlongrightarrow> y) at_top"
    by(auto intro!: tendsto_at_topI_sequentially_real mono2)
  show ?thesis
    by(auto intro!: tendsto_cong[THEN iffD1,OF _ lim]
        eventually_at_top_linorderI[where c=K])
qed

lemma mono_convergent_real_le:
  fixes f :: "real \<Rightarrow> real"
  assumes mono:"mono_on {K..} f"
    and le:"\<And>r. K \<le> r \<Longrightarrow> f r \<le> A"
  shows "\<exists>l. (f \<longlongrightarrow> l) at_top \<and> (\<forall>r\<ge>K. f r \<le> l)"
proof -
  have inc:" incseq (\<lambda>n. f (K + real n))"
    by(auto intro!: monoI mono_onD[OF mono])
  obtain L where L:"(\<lambda>n. f (K + real n)) \<longlonglongrightarrow> L" "\<And>i. f (K + real i) \<le> L"
    using incseq_convergent[OF inc,of A] le by auto
  hence "((\<lambda>r. f (K + r)) \<longlongrightarrow> L) at_top"
    using mono_onD[OF mono]
    by(auto intro!: tendsto_at_topI_sequentially_real'[of 0 "\<lambda>r. f (K + r)"]
        mono_onI)
  moreover have "LIM r at_top. r - K :> at_top"
    using filterlim_tendsto_add_at_top_iff[where f="\<lambda>x. - K",THEN iffD2]
          filterlim_ident by auto
  ultimately have 1:"(f \<longlongrightarrow> L) at_top"
    using filterlim_compose[of "\<lambda>r. f (K + r)" "nhds L" at_top "\<lambda>r. -K + r" at_top]
    by simp
  moreover have "f r \<le> L" if r:"K \<le> r" for r
  proof(rule ccontr)
    assume "\<not> f r \<le> L"
    hence "\<forall>\<^sub>F x in at_top. f x < f r"
      using order_topology_class.order_tendstoD[OF 1] by simp
    moreover have "\<forall>\<^sub>F x in at_top. f r \<le> f x"
      using mono_onD[OF mono,of r] r
      by(auto intro!: eventually_at_top_linorderI[where c=r])
    ultimately show False
      unfolding eventually_at_top_linorder
      by (metis nle_le not_less)
  qed
  ultimately show ?thesis
    by blast
qed

lemma mono_convergent_real_less:
  fixes f :: "real \<Rightarrow> real"
  assumes mono:"mono_on {K<..} f"
    and less:"\<And>r. K < r \<Longrightarrow> f r \<le> A"
  shows "\<exists>l. (f \<longlongrightarrow> l) at_top \<and> (\<forall>r>K. f r \<le> l)"
proof -
  have "\<exists>l. (f \<longlongrightarrow> l) at_top \<and> (\<forall>r\<ge>K + 1. f r \<le> l)"
    by(auto intro!: mono_convergent_real_le less mono_onI mono_onD[OF mono])
  then obtain L where L:"(f \<longlongrightarrow> L) at_top"
    by blast
  have "0 < e \<Longrightarrow> \<exists>l. (f \<longlongrightarrow> l) at_top \<and> (\<forall>r\<ge>K+e. f r \<le> l)" for e :: real
    by(auto intro!:  mono_convergent_real_le less mono_onI mono_onD[OF mono])
  then obtain l where l':"\<And>e. 0 < e \<Longrightarrow> (f \<longlongrightarrow> l e) at_top \<and> (\<forall>r\<ge>K+e. f r \<le> l e)"
    by metis
  hence "\<And>e. 0 < e \<Longrightarrow> l e = L"
    by(auto intro!: tendsto_unique[OF _ _ L])
  hence l:"\<And>e r. 0 < e \<Longrightarrow> K + e \<le> r \<Longrightarrow> f r \<le> L"
    using l' by fast
  hence "\<And>r. K < r \<Longrightarrow> f r \<le> L"
    by (metis not_le field_le_epsilon nle_le)
  with L show ?thesis by blast
qed

lemma at_top_real_iff_all_sequentially:
  fixes f :: "real \<Rightarrow> 'b :: topological_space"
  shows "(f \<longlongrightarrow> l) at_top
       \<longleftrightarrow> (\<forall>a. filterlim a at_top sequentially \<longrightarrow> incseq a
                 \<longrightarrow> (\<lambda>n. (f (a n))) \<longlonglongrightarrow> l)"
proof
  assume h:"\<forall>a. filterlim a at_top sequentially \<longrightarrow> (incseq a) \<longrightarrow> (\<lambda>n. f (a n)) \<longlonglongrightarrow> l"
  show "(f \<longlongrightarrow> l) at_top"
  proof (rule ccontr)
    assume c:"\<not> (f \<longlongrightarrow> l) at_top"
    then obtain S where S:"open S" "l \<in> S""\<And>R. \<exists>r \<ge> R. f r \<notin> S"
      by(fastforce simp: tendsto_def eventually_at_top_linorder)
    define a where "a \<equiv> rec_nat (SOME r. r \<ge> 0 \<and> f r \<notin> S)
                         (\<lambda>n an. SOME r. r > max an (real (Suc n)) \<and> f r \<notin> S)"
    have a_inc:"incseq a"
    proof(rule incseq_SucI)
      fix n
      have aSn:"a (Suc n) = (SOME r.  r > max (a n) (real (Suc n)) \<and> f r \<notin> S)"
        by(simp add: a_def)
      obtain r where r:"r \<ge> max (a n + 1) (Suc (Suc n))" "f r \<notin> S"
        using S by blast
      show "a n \<le> a (Suc n)"
        unfolding aSn
        by(rule someI2[where a=r]) (use r in auto)
    qed
    have a_ge_n:"a n \<ge> real n \<and> f (a n) \<notin> S" for n
    proof(cases n)
      case 0
      obtain r where r:"r \<ge> 0" "f r \<notin> S"
        using S by blast
      show ?thesis
        unfolding a_def 0 nat.rec
        by(rule someI2[where a=r]) (use r in auto)
    next
      case n':(Suc n')
      then have aSn':"a (Suc n') = (SOME r.  r > max (a n') (real (Suc n')) \<and> f r \<notin> S)"
        by(simp add: a_def)
      obtain r where r:"r \<ge> max (a n' + 1) (Suc (Suc n'))" "f r \<notin> S"
        using S by blast
      show ?thesis
        unfolding n' aSn'
        by(rule someI2[where a=r]) (use r in auto)
    qed
    hence a_ge_n:"a n \<ge> real n" and fan_nin_S:"f (a n) \<notin> S" for n
      by auto
    hence "filterlim a at_top sequentially"
      unfolding filterlim_at_top
      by (metis order.trans eventually_sequentially of_nat_mono real_arch_simple)
    hence "(\<lambda>n. f (a n)) \<longlonglongrightarrow> l"
      using h a_inc by simp
    thus False
      using S fan_nin_S
      by (meson lim_explicit order.refl)
  qed
qed(use filterlim_compose in blast)
lemma at_top_real_iff_all_sequentially':
  fixes f :: "real \<Rightarrow> 'b :: topological_space"
  shows "(f \<longlongrightarrow> l) at_top
    \<longleftrightarrow> (\<forall>a. filterlim a at_top sequentially \<longrightarrow> (\<forall>n. a n \<ge> K)
        \<longrightarrow> incseq a \<longrightarrow> (\<lambda>n. (f (a n))) \<longlonglongrightarrow> l)"
  unfolding at_top_real_iff_all_sequentially
proof safe
  fix a :: "nat \<Rightarrow> real"
  assume h:"\<forall>a. filterlim a at_top sequentially \<longrightarrow> (\<forall>n. K \<le> a n)
            \<longrightarrow> incseq a\<longrightarrow> (\<lambda>n. f (a n)) \<longlonglongrightarrow> l"
    and  a:"filterlim a at_top sequentially" "incseq a"
  then obtain N where N:"\<And>n. n \<ge> N \<Longrightarrow> a n \<ge> K"
    by (metis eventually_at_top_linorder filterlim_at_top)
  have a':"filterlim (\<lambda>n. a (n + N)) at_top sequentially" "incseq (\<lambda>n. a (n + N))"
    using a  filterlim_compose[OF _ filterlim_add_const_nat_at_top]
    by(auto simp: incseq_Suc_iff)    
  show "(\<lambda>n. f (a n)) \<longlonglongrightarrow> l"
    by(rule LIMSEQ_offset[where k=N]) (use h N a' in fastforce)
qed simp

subsection \<open>Integrals on Sets\<close>
lemma set_borel_measurable_iff_restrict_space:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes [measurable]:"A \<in> sets M"
  shows "set_borel_measurable M A f \<longleftrightarrow> f \<in> borel_measurable (restrict_space M A)"
  by (simp add: borel_measurable_restrict_space_iff set_borel_measurable_def)

lemma set_borel_measurable_add:
  fixes f :: "_ \<Rightarrow> _ :: {second_countable_topology, topological_monoid_add, real_vector}"
  assumes "set_borel_measurable M A f"
    and "set_borel_measurable M A g"
  shows "set_borel_measurable M A (\<lambda>x. f x + g x)"
  using assms by(simp add: set_borel_measurable_def scaleR_add_right)

lemma set_borel_measurable_scaleR:
  fixes g :: "_ \<Rightarrow> _ :: {second_countable_topology, real_normed_vector}"
  assumes "set_borel_measurable M A f"
    and "set_borel_measurable M A g"
  shows "set_borel_measurable M A (\<lambda>x. f x *\<^sub>R g x)"
proof -
  have *:"(\<lambda>x. indicat_real A x *\<^sub>R f x *\<^sub>R g x)
       = (\<lambda>x. (indicat_real A x * f x) *\<^sub>R (indicat_real A x *\<^sub>R g x))"
    by(auto simp: indicator_def)
  show ?thesis
    unfolding set_borel_measurable_def *
    by(rule borel_measurable_scaleR) (use assms in "auto simp: set_borel_measurable_def")
qed

lemma set_borel_measurable_times:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_algebra}"
  assumes "set_borel_measurable M A f"
    and "set_borel_measurable M A g"
  shows "set_borel_measurable M A (\<lambda>x. f x * g x)"
proof -
  have *:"(\<lambda>x. indicat_real A x *\<^sub>R (f x * g x))
       = (\<lambda>x. (indicat_real A x *\<^sub>R f x) * (indicat_real A x *\<^sub>R g x))"
    by(auto simp: indicator_def)
  show ?thesis
    unfolding set_borel_measurable_def *
    by(rule borel_measurable_times) (use assms in "auto simp: set_borel_measurable_def")
qed

lemma set_borel_measurable_restrict_space_iff:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes [measurable]:"A \<in> sets M"
  shows "set_borel_measurable (restrict_space M A) A f \<longleftrightarrow> set_borel_measurable M A f"
proof
  assume "set_borel_measurable (restrict_space M A) A f"
  moreover have "(\<lambda>x. indicat_real A x *\<^sub>R f x)
                  = (\<lambda>x. if x \<in> A then indicat_real A x *\<^sub>R f x else 0)"
    by auto
  ultimately show "set_borel_measurable M A f"
    by(auto simp: set_borel_measurable_def measurable_restrict_space_iff[symmetric])
qed(auto simp: set_borel_measurable_def measurable_restrict_space1)

lemma set_borel_measurable_comp':
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes [measurable]: "A \<in> sets M"
    and "set_borel_measurable N (g ` A) f"
    and [measurable]: "g \<in> measurable M N"
  shows "set_borel_measurable M A (\<lambda>x. f (g x))"
proof -
  have "x \<in> space (restrict_space M A) \<Longrightarrow>
        f (g x) = ((\<lambda>x. indicat_real (g ` A) x *\<^sub>R (f x)) \<circ> g) x" for x
    by simp
  moreover have "... \<in> borel_measurable (restrict_space M A)"
    by(rule measurable_comp[where N=N])
      (use assms in "auto simp: measurable_restrict_space1 set_borel_measurable_def")
  ultimately show ?thesis
    by(simp del: comp_apply space_restrict_space2
        add: set_borel_measurable_iff_restrict_space
        cong: measurable_cong)
qed

lemma set_borel_measurable_comp:
  fixes f :: "_ \<Rightarrow> _  ::real_normed_vector" and g :: "_ \<Rightarrow> _::real_vector"
  assumes [measurable]: "A \<in> sets M"
    and "set_borel_measurable borel (g ` A) f"
    and "set_borel_measurable M A g"
  shows "set_borel_measurable M A (\<lambda>x. f (g x))"
proof -
  have "x \<in> space (restrict_space M A) \<Longrightarrow>
        f (g x) = ((\<lambda>x. indicat_real (g ` A) x *\<^sub>R (f x))
                    \<circ> (\<lambda>x. indicat_real A x *\<^sub>R (g x))) x" for x
    by simp
  moreover have "... \<in> borel_measurable (restrict_space M A)"
    by(rule measurable_comp[where N="restrict_space borel (g ` A)"])
      (use assms in "auto simp: set_borel_measurable_def
         measurable_restrict_space2_iff measurable_restrict_space1")
  ultimately show ?thesis
    by(simp del: comp_apply space_restrict_space2
        add: set_borel_measurable_iff_restrict_space
        cong: measurable_cong)
qed

lemma set_integrable_set_borel_measurable:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "set_integrable M S f"
  shows "set_borel_measurable M S f"
  using assms integrable_iff_bounded set_borel_measurable_def set_integrable_def
  by blast

lemma set_integrable_uminus:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "set_integrable M S (\<lambda>x. - f x) \<longleftrightarrow> set_integrable M S f"
  by(auto simp: set_integrable_def)

lemma set_integrable_const:
  fixes a :: "'b::{banach, second_countable_topology}"
  assumes "emeasure M S < \<top>" "S \<in> sets M"
  shows "set_integrable M S (\<lambda>x. a)"
  using assms by(auto simp: set_integrable_def)

lemma set_integrable_zero[simp]: "set_integrable M S (\<lambda>x. 0)"
  by(auto simp: set_integrable_def)

lemma set_integral_cong:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x = g x"
  shows "(\<integral>x\<in>A. f x \<partial>M) = (\<integral>x\<in>A. g x \<partial>M)"
  unfolding set_lebesgue_integral_def
  by(auto intro!: Bochner_Integration.integral_cong assms simp: indicator_def)

lemma set_integrable_bounded:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "set_borel_measurable M S f"
    and S:"emeasure M S < \<top>" "S \<in> sets M"
    and le:"\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> K"
  shows "set_integrable M S f"
  unfolding set_integrable_def integrable_iff_bounded
proof
  have "(\<integral>\<^sup>+ x. ennreal (norm (indicat_real S x *\<^sub>R f x)) \<partial>M)
      \<le> (\<integral>\<^sup>+ x. ennreal (norm (indicat_real S x *\<^sub>R K)) \<partial>M)"
    using assms by(fastforce intro!: nn_integral_mono simp: indicator_def)
  also have "... = (\<integral>\<^sup>+x\<in>S. ennreal K \<partial>M)"
    using order.trans[OF norm_ge_zero le]
    by(auto intro!: nn_integral_cong ennreal_inj[THEN iffD2] simp: indicator_def)
  also have "... < \<infinity>"
    using S ennreal_less_top ennreal_mult_less_top
    by(simp add: nn_integral_cmult_indicator)
  finally show "(\<integral>\<^sup>+ x. ennreal (norm (indicat_real S x *\<^sub>R f x)) \<partial>M) < \<infinity>" .
qed(use assms in "simp add: set_borel_measurable_def")

lemma set_integral_subset_AE:
  fixes f :: "_ \<Rightarrow> real"
  assumes integ:"set_integrable M B f"
    and AB:"A \<in> sets M" "A \<subseteq> B"
    and nonneg:"AE x\<in> B - A in M. 0 \<le> f x"
  shows "(\<integral>x\<in>A. f x \<partial>M) \<le> (\<integral>x\<in>B. f x \<partial>M)"
  using set_integrable_subset[OF integ AB] assms
  unfolding set_lebesgue_integral_def set_integrable_def
  by(intro Bochner_Integration.integral_mono_AE eventually_mono[OF nonneg])
    (auto simp: indicator_def)

lemma set_integral_subset:
  fixes f :: "_ \<Rightarrow> real"
  assumes integ:"set_integrable M B f"
    and AB:"A \<in> sets M" "A \<subseteq> B"
    and nonneg:"\<And>x. x\<in> B - A \<Longrightarrow> 0 \<le> f x"
  shows "(\<integral>x\<in>A. f x \<partial>M) \<le> (\<integral>x\<in>B. f x \<partial>M)"
  by(auto intro!: set_integral_subset_AE assms)
 
lemma set_integral_empty[simp]:"(\<integral>x\<in>{}. f x \<partial>M) = 0"
  by(simp add: set_lebesgue_integral_def)

lemma set_integral_null_sets:
  assumes "N \<in> null_sets M"
  shows "(\<integral>x\<in>N. f x \<partial>M) = 0"
  by(auto simp: set_lebesgue_integral_def indicator_def
      intro!: integral_eq_zero_AE AE_I'[OF assms])

corollary LBINT_singleton[simp]:"(\<integral>x\<in>{a}. f x \<partial>lborel) = 0"
  by(auto intro!: set_integral_null_sets)

lemma not_set_integrable_integral_eq:
  assumes "\<not> set_integrable M A f"
  shows "(\<integral>x\<in>A. f x \<partial>M) = 0"
  using assms
  by(simp add: set_integrable_def set_lebesgue_integral_def not_integrable_integral_eq)

text \<open> The following is more general than @{thm set_borel_integrable_singleton}.\<close>
lemma set_borel_integrable_singleton'[simp]: "set_integrable lborel {a} f"
  unfolding set_integrable_def
  by(rule integrable_cong_AE[where f="\<lambda>x. 0",THEN iffD1
        ,OF _ measurable_cong[where f="\<lambda>x. if x = a then f a else 0",THEN iffD1]])
  (auto intro!: AE_I'[where N="{a}"])

lemma set_integrable_Ioc_eq_Icc:
  fixes a :: "_ :: linorder_topology"
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  shows "set_integrable lborel {a<..b} f \<longleftrightarrow> set_integrable lborel {a..b} f"
proof
  assume "set_integrable lborel {a<..b} f"
  from set_integrable_Un[OF set_borel_integrable_singleton'[of a f] this]
  have *:"set_integrable lborel ({a} \<union> {a<..b}) f"
    by simp
  show "set_integrable lborel {a..b} f"
    by(auto intro!: set_integrable_subset[OF *])
next
  assume *:"set_integrable lborel {a..b} f"
  show "set_integrable lborel {a<..b} f"
    by(auto intro!: set_integrable_subset[OF *])
qed

lemma LBINT_Ioc_eq_Icc:
  fixes f :: "_ :: linorder_topology \<Rightarrow> _ :: {banach, second_countable_topology}"
  shows "(\<integral>x\<in>{a<..b}. f x \<partial>lborel) = (\<integral>x\<in>{a..b}. f x \<partial>lborel)"
proof(cases "set_integrable lborel {a<..b} f \<and> a \<le> b")
  assume [simp]:"set_integrable lborel {a<..b} f \<and> a \<le> b"
  have "(\<integral>x\<in>{a<..b}. f x \<partial>lborel) = (\<integral>x\<in>{a<..b}. f x \<partial>lborel) + (\<integral>x\<in>{a}. f x \<partial>lborel)"
    by simp
  also have "... = (\<integral>x\<in>{a<..b} \<union> {a}. f x \<partial>lborel)"
    by(subst set_integral_Un) auto
  also have "... = (\<integral>x\<in>{a..b}. f x \<partial>lborel)"
    by(auto intro!: arg_cong[where f="\<lambda>B. (\<integral>x\<in>B. f x \<partial>lborel)"])
  finally show ?thesis .
qed (auto simp: set_integrable_Ioc_eq_Icc not_set_integrable_integral_eq)

lemma set_integrable_atLeast_eq:
  fixes a :: "_ :: linorder_topology"
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  shows "set_integrable lborel {a<..} f \<longleftrightarrow> set_integrable lborel {a..} f"
proof
  assume "set_integrable lborel {a<..} f"
  from set_integrable_Un[OF set_borel_integrable_singleton'[of a f] this]
  have *:"set_integrable lborel ({a} \<union> {a<..}) f"
    by simp
  show "set_integrable lborel {a..} f"
    by(auto intro!: set_integrable_subset[OF *])
next
  assume *:"set_integrable lborel {a..} f"
  show "set_integrable lborel {a<..} f"
    by(auto intro!: set_integrable_subset[OF *])
qed

lemma set_integral_atLeast_eq:
  fixes f :: "real \<Rightarrow> _ :: {banach, second_countable_topology}"
  shows "(\<integral>x\<in>{a<..}. f x \<partial>lborel) = (\<integral>x\<in>{a..}. f x \<partial>lborel)"
proof(cases "set_integrable lborel {a<..} f")
  assume [simp]:"set_integrable lborel {a<..} f"
  have "(\<integral>x\<in>{a<..}. f x \<partial>lborel) = (\<integral>x\<in>{a<..}. f x \<partial>lborel) + (\<integral>x\<in>{a}. f x \<partial>lborel)"
    by simp
  also have "... = (\<integral>x\<in>{a<..} \<union> {a}. f x \<partial>lborel)"
    by(subst set_integral_Un) auto
  also have "... = (\<integral>x\<in>{a..}. f x \<partial>lborel)"
    by(auto intro!: arg_cong[where f="\<lambda>B. (\<integral>x\<in>B. f x \<partial>lborel)"])
  finally show ?thesis .
qed (auto simp: set_integrable_atLeast_eq not_set_integrable_integral_eq)

lemma set_nn_integral_atLeast_eq:
  fixes a :: "_ :: linorder_topology"
  shows "(\<integral>\<^sup>+x\<in>{a<..}. f x \<partial>lborel) = (\<integral>\<^sup>+x\<in>{a..}. f x \<partial>lborel)"
  apply(safe intro!: nn_integral_cong_AE AE_I'[where N="{a}"])
   apply (simp add: countable_imp_null_set_lborel)
  apply (metis atLeast_iff greaterThan_iff indicator_simps order_less_le)
  done

lemma set_integrable_atMost_eq:
  fixes b :: "_ :: linorder_topology"
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  shows "set_integrable lborel {..<b} f \<longleftrightarrow> set_integrable lborel {..b} f"
proof
  assume "set_integrable lborel {..<b} f"
  from set_integrable_Un[OF set_borel_integrable_singleton'[of b f] this]
  have *:"set_integrable lborel ({b} \<union> {..<b}) f"
    by simp
  show "set_integrable lborel {..b} f"
    by(auto intro!: set_integrable_subset[OF *])
next
  assume *:"set_integrable lborel {..b} f"
  then show "set_integrable lborel {..<b} f"
    by(rule set_integrable_subset) auto
qed

lemma set_integral_atMost_eq:
  fixes f :: "real \<Rightarrow> _ :: {banach, second_countable_topology}"
  shows "(\<integral>x\<in>{..<b}. f x \<partial>lborel) = (\<integral>x\<in>{..b}. f x \<partial>lborel)"
proof(cases "set_integrable lborel {..<b} f")
  assume [simp]:"set_integrable lborel {..<b} f"
  have "(\<integral>x\<in>{..<b}. f x \<partial>lborel) = (\<integral>x\<in>{..<b}. f x \<partial>lborel) + (\<integral>x\<in>{b}. f x \<partial>lborel)"
    by simp
  also have "... = (\<integral>x\<in>{..<b} \<union> {b}. f x \<partial>lborel)"
    by(subst set_integral_Un) auto
  also have "... = (\<integral>x\<in>{..b}. f x \<partial>lborel)"
    by(auto intro!: arg_cong[where f="\<lambda>B. (\<integral>x\<in>B. f x \<partial>lborel)"])
  finally show ?thesis .
qed (auto simp: set_integrable_atMost_eq not_set_integrable_integral_eq)

lemma set_nn_integral_atMost_eq:
  fixes b :: "_ :: linorder_topology"
  shows "(\<integral>\<^sup>+x\<in>{..<b}. f x \<partial>lborel) = (\<integral>\<^sup>+x\<in>{..b}. f x \<partial>lborel)"
  apply(safe intro!: nn_integral_cong_AE AE_I'[where N="{b}"])
   apply (simp add: countable_imp_null_set_lborel)
  apply (metis atMost_iff indicator_simps lessThan_iff less_le)
  done

lemma AE_False_iff_False:
  assumes "0 < emeasure M A"
  shows "(AE x\<in>A in M. False) \<longleftrightarrow> False"
proof
  assume "AE x\<in>A in M. False"
  thus False
    using AE_iff_null_sets assms emeasure_notin_sets less_irrefl null_setsD1
    by metis
qed simp

lemma nn_integral_less':
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes f: "(\<integral>\<^sup>+x. f x \<partial>M) \<noteq> \<infinity>"
    and ord1: "AE x \<in> A in M. f x < g x" and ord2:"AE x in M. f x \<le> g x"
    and pos:"0 < emeasure M A"
  shows "(\<integral>\<^sup>+x. f x \<partial>M) < (\<integral>\<^sup>+x. g x \<partial>M)"
proof(rule nn_integral_less)
  have A:"A \<in> sets M"
    using pos emeasure_notin_sets by fastforce
  show "\<not> (AE x in M. g x \<le> f x)"
  proof
    assume h:"AE x in M. g x \<le> f x"
    have "AE x\<in>A in M. False"
      by(rule eventually_mono[OF eventually_conj[OF h ord1]]) auto
    thus False
      using pos AE_False_iff_False by blast
  qed
qed(use assms in auto)

lemma set_nn_integral_less':
  fixes f :: "_ \<Rightarrow> ennreal"
  assumes "(\<lambda>x. f x * indicator A x) \<in> borel_measurable M"
    and "(\<lambda>x. g x * indicator A x) \<in> borel_measurable M"
    and "A \<in> sets M"
    and "B \<subseteq> A"
    and le:"AE x\<in>B in M. f x < g x" "AE x\<in>A in M. f x \<le> g x"
    and "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) \<noteq> \<infinity>"
    and "0 < emeasure M B"
  shows "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) < (\<integral>\<^sup>+x\<in>A. g x \<partial>M)"
  using assms
  by(intro nn_integral_less'[where A=B] eventually_mono[OF AE_conjI[OF le]])
    (auto simp: indicator_def)

lemma set_nn_integral_less:
  fixes f :: "_ \<Rightarrow> ennreal"
  assumes "(\<lambda>x. f x * indicator A x) \<in> borel_measurable M"
    and "(\<lambda>x. g x * indicator A x) \<in> borel_measurable M"
    and "AE x\<in>A in M. f x < g x"
    and "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) \<noteq> \<infinity>"
    and "0 < emeasure M A"
  shows "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) < (\<integral>\<^sup>+x\<in>A. g x \<partial>M)"
  using emeasure_neq_0_sets[of M A] assms
  by(auto intro!: set_nn_integral_less'[of f A M g A])

lemma set_nn_integral_zero_less:
  assumes [measurable]:"(\<lambda>x. g x * indicator A x) \<in> borel_measurable M"
    and pos:"AE x\<in>A in M. 0 < g x"
    and meas:"0 < emeasure M A"
  shows "0 < (\<integral>\<^sup>+x\<in>A. g x \<partial>M)"
  using set_nn_integral_less[where f="\<lambda>x. 0" and g=g and A=A] assms
  by fastforce

lemma set_integral_zero_less:
  fixes f :: "_ \<Rightarrow> real"
  assumes integ:"set_integrable M A f"
    and le:"AE x\<in>A in M. 0 < f x"
    and meas:"0 < emeasure M A"
  shows "0 < (\<integral>x\<in>A. f x \<partial>M)"
proof -
  have *:"enn2real (\<integral>\<^sup>+x\<in>A. ennreal (f x) \<partial>M) = (\<integral>x\<in>A. f x \<partial>M)"
  proof -
    have "enn2real (\<integral>\<^sup>+x\<in>A. ennreal (f x) \<partial>M)
          = enn2real (\<integral>\<^sup>+x. ennreal (indicator A x * f x) \<partial>M)"
      by(auto intro!: arg_cong[where f=enn2real] nn_integral_cong simp: indicator_def)
    also have "... = enn2real (ennreal (\<integral>x. indicator A x * f x \<partial>M))"
      using integ le
      by(subst nn_integral_eq_integral) (auto simp: set_integrable_def)
    also have "... = (\<integral>x\<in>A. f x \<partial>M)"
      using le
      by(subst enn2real_ennreal)
        (auto simp: set_lebesgue_integral_def intro!: integral_nonneg_AE)
    finally show ?thesis .
  qed
  have [measurable]:"(\<lambda>x. ennreal (f x) * indicator A x) \<in> borel_measurable M"
    by (smt (verit, ccfv_threshold) integ mult.commute indicator_mult_ennreal
        integrable_iff_bounded measurable_compose measurable_cong measurable_ennreal
        real_scaleR_def set_integrable_def)
  have "0 < (\<integral>\<^sup>+x\<in>A. ennreal (f x) \<partial>M)"
    using assms
    by(auto intro!: set_nn_integral_zero_less simp: set_integrable_def)
  hence "0 < enn2real (\<integral>\<^sup>+x\<in>A. ennreal (f x) \<partial>M)"
    unfolding enn2real_positive_iff
    by (smt (verit, best) integ ennreal_0 ennreal_less_zero_iff ennreal_mult_top
        ennreal_zero_less_mult_iff indicator_def indicator_def indicator_def indicator_def
        indicator_eq_0_iff indicator_eq_0_iff indicator_simps indicator_times_eq_if
        integrable_iff_bounded less_top measurable_ennreal mult.right_neutral
        mult_eq_0_iff mult_eq_0_iff mult_zero_right nless_le nn_integral_mono not_le
        real_norm_def real_scaleR_def set_integrable_def)
  also have "... = (\<integral>x\<in>A. f x \<partial>M)"
    unfolding * ..
  finally show ?thesis .
qed

lemma set_integral_zero_less':
  fixes f :: "_ \<Rightarrow> real"
  assumes integ:"set_integrable M A f"
    and le:"AE x\<in>B in M. 0 < f x"
    and le2:"AE x\<in>A in M. 0 \<le> f x"
    and [measurable]:"A \<in> sets M"
    and AB:"B \<subseteq> A"
    and meas:"0 < emeasure M B"
  shows "0 < (\<integral>x\<in>A. f x \<partial>M)"
proof -
  have [measurable]:"B \<in> sets M"
    using meas emeasure_notin_sets by fastforce
  have "0 < (\<integral>x\<in>B. f x \<partial>M)"
    by(auto intro!: set_integral_zero_less set_integrable_subset[OF integ] assms)
  also have "... \<le> (\<integral>x\<in>A. f x \<partial>M)"
    using AB
    by(auto intro!: set_integral_subset_AE integ eventually_mono[OF le2])
  finally show ?thesis .
qed

lemma set_integral_less':
  fixes f :: "_ \<Rightarrow> real"
  assumes f:"set_integrable M A f"
    and g:"set_integrable M A g"
    and [measurable]:"A \<in> sets M"
    and AB:"B \<subseteq> A"
    and le:"AE x\<in>B in M. f x < g x" and le2:"AE x\<in>A in M. f x \<le> g x"
    and meas:"0 < emeasure M B"
  shows "(\<integral>x\<in>A. f x \<partial>M) < (\<integral>x\<in>A. g x \<partial>M)"
proof -
  have "0 < (\<integral>x\<in>A. g x - f x \<partial>M)"
    using assms
    by(intro set_integral_zero_less'[where B=B] set_integral_diff) auto
  also have "... = (\<integral>x\<in>A. g x \<partial>M) - (\<integral>x\<in>A. f x \<partial>M)"
    using assms by auto
  finally show ?thesis
    by simp
qed

lemma set_integral_less:
  fixes f :: "_ \<Rightarrow> real"
  assumes f:"set_integrable M A f"
    and g:"set_integrable M A g"
    and le:"AE x\<in>A in M. f x < g x"
    and meas:"0 < emeasure M A"
  shows "(\<integral>x\<in>A. f x \<partial>M) < (\<integral>x\<in>A. g x \<partial>M)"
  using assms 
  by(intro set_integral_less'[where B=A])
    (auto simp: emeasure_neq_0_sets)

corollary set_itegral_strict_mono_Icc:
  fixes f :: "real \<Rightarrow> real"
  fixes a b :: real
  assumes integ:"set_integrable lborel {a..b} f"
    and le:"AE x\<in>{a<..b} in lborel. 0 < f x"
  shows "strict_mono_on {a..b} (\<lambda>x. (\<integral>t\<in>{a<..x}. f t \<partial>lborel))"
proof(safe intro!: strict_mono_onI)
  fix r s
  assume "r \<in> {a..b}" "s \<in> {a..b}" and rs[arith]:"r < s"
  then have rab[arith]:"a \<le> r" "r \<le> b" and sab[arith]:"a \<le> s" "s \<le> b"
    by simp_all
  with rs have "(\<integral>t\<in>{a<..r}. f t \<partial>lborel) < (\<integral>t\<in>{a<..r}. f t \<partial>lborel) + (\<integral>t\<in>{r<..s}. f t \<partial>lborel)"
    by(auto intro!: set_integral_zero_less set_integrable_subset[OF integ] eventually_mono[OF le])
  also have "... = (\<integral>t\<in>{a<..s}. f t \<partial>lborel)"
    by(subst set_integral_Un[symmetric])
      (auto intro!: set_integrable_subset[OF integ] arg_cong[where f="\<lambda>A. (\<integral>t\<in>A. f t \<partial>lborel)"])
  finally show "(\<integral>t\<in>{a<..r}. f t \<partial>lborel) <(\<integral>t\<in>{a<..s}. f t \<partial>lborel)" .
qed

corollary set_itegral_tail_strict_antimono:
  fixes f :: "real \<Rightarrow> real"
  assumes integ:"set_integrable lborel {a..} f"
    and le:"AE x\<in>{a<..} in lborel. 0 < f x"
  shows "strict_antimono_on {a..} (\<lambda>x. (\<integral>t\<in>{x<..}. f t \<partial>lborel))"
proof(safe intro!: monotone_onI)
  fix x y
  assume x[arith]:"a \<le> x" and y[arith]:"a \<le> y" and xy[arith]:"x < y"
  have "(\<integral>t\<in>{y<..}. f t \<partial>lborel) < (\<integral>t\<in>{x<..y}. f t \<partial>lborel) + (\<integral>t\<in>{y<..}. f t \<partial>lborel)"
    by(auto intro!: set_integral_zero_less set_integrable_subset[OF integ] eventually_mono[OF le])
  also have "... = (\<integral>t\<in>{x<..}. f t \<partial>lborel)"
    by(subst set_integral_Un[symmetric])
      (auto intro!: set_integrable_subset[OF integ] arg_cong[where f="\<lambda>A. (\<integral>t\<in>A. f t \<partial>lborel)"])
  finally show "(\<integral>t\<in>{y<..}. f t \<partial>lborel) < (\<integral>t\<in>{x<..}. f t \<partial>lborel)" .
qed


subsection \<open>Integral of Composite Functions $g(\int_{t\in A_x} f (t)\, \mathrm{d}t)$\<close>
lemma continuous_on_LBINT_Ioc:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "\<And>b. a \<le> b \<Longrightarrow> set_integrable lborel {a..b} f"
  shows "continuous_on UNIV (\<lambda>b. LBINT x:{a<..b}. f x)"
  by (simp add: LBINT_Ioc_eq_Icc continuous_on_LBINT f)

corollary continuous_on_LBINT_tail:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "set_integrable lborel {a..} f"
  shows "continuous_on {a..} (\<lambda>b. LBINT x:{b<..}. f x)"
proof(subst continuous_on_cong)
  fix b
  assume b:"b \<in> {a..}"
  then have "(LBINT x:{b<..}. f x) + (LBINT x:{a<..b}. f x) = (LBINT x:{a<..}. f x)"
    by(subst set_integral_Un[symmetric])
      (auto intro!: set_integrable_subset[OF f] arg_cong[where f="\<lambda>B. (LBINT x:B. f x)"])
  thus "(LBINT x:{b<..}. f x) = (LBINT x:{a<..}. f x) - (LBINT x:{a<..b}. f x)"
    by argo
next
  show "continuous_on {a..} (\<lambda>b. (LBINT x:{a<..}. f x) - (LBINT x:{a<..b}. f x))"
    by(auto intro!: continuous_on_diff continuous_on_subset[OF continuous_on_LBINT_Ioc]
        set_integrable_subset[OF f])
qed simp

corollary continuous_on_LBINT_com:
  fixes f :: "real \<Rightarrow> real"
  assumes "integrable lborel f"
  shows "isCont (\<lambda>b. LBINT x:{..b}. f x) x"
proof(rule continuous_on_interior)
  have f:"set_integrable lborel UNIV f"
    using assms by(simp add: set_integrable_def)
  show "continuous_on {x-1<..<x+1} (\<lambda>b. LBINT x:{..b}. f x)"
    thm continuous_on_eq_continuous_at[OF open_UNIV]
  proof(subst continuous_on_cong)
    fix b
    assume "b \<in> {x - 1<..<x + 1}"
    thus "(LBINT x:{..b}. f x) = (LBINT x:{..x-1}. f x) + (LBINT x:{x-1<..b}. f x)"
      by(subst set_integral_Un[symmetric])
        (auto intro!: set_integrable_subset[OF f] arg_cong[where f="\<lambda>B. (LBINT x:B. f x)"])
  next
    show "continuous_on {x-1<..<x+1} (\<lambda>b. (LBINT x:{..x-1}. f x) + (LBINT x:{x-1<..b}. f x))"
      by(auto intro!: continuous_on_subset[OF continuous_on_LBINT_Ioc]
          continuous_on_add set_integrable_subset[OF f])
  qed simp
qed simp

lemma sets_restrict_space_sigma_sets:
  assumes "sets M = sigma_sets \<Omega> E"
    and A:"A \<in> sets M" and Ao:"A \<subseteq> \<Omega>"
  shows "sets (restrict_space M A) = sigma_sets A ((\<inter>) A ` E)"
  by (metis assms sets_restrict_space sigma_sets_Int)

lemma Int_stable_image_inter:
  assumes "Int_stable A"
  shows "Int_stable ((\<inter>) a ` A)"
proof(intro Int_stableI_image)
  fix i j
  assume "i \<in> A" "j \<in> A"
  thus "\<exists>k\<in>A. a \<inter> i \<inter> (a \<inter> j) = a \<inter> k"
    using Int_stableD[OF assms]
    by(auto intro!: bexI[where x="i \<inter> j"])
qed

lemma
  fixes f and g:: "real \<Rightarrow> real" and A B
  defines "F \<equiv> \<lambda>x::real. (\<integral>t\<in>A x. f t \<partial>lborel)"
  defines "M \<equiv> density (restrict_space lborel B) f"
  assumes f_pos:"AE x \<in> B in lborel. 0 \<le> f x"
    and f_int:"\<And>x. x \<in> X \<Longrightarrow> set_integrable lborel (A x) f"
    and F_meas:"F \<in> (restrict_space lborel B) \<rightarrow>\<^sub>M restrict_space borel C"
    and B:"F `B = C" and [measurable]:"B \<in> sets borel" "C \<in> sets borel" "\<And>x. A x \<in> sets borel"
    and AB:"B \<subseteq> A a" and a:"a \<in> X"
    and meq:"restrict_space lborel C = distr M (restrict_space borel C) F"
  shows set_integral_compose_integral:
    "g \<in> borel_measurable (restrict_space borel C)
       \<Longrightarrow> (\<integral>t\<in>B. g (F t) * f t \<partial>lborel) = (\<integral>t\<in>C. g t \<partial>lborel)"
    and set_integrable_compose_integral:
    "set_integrable lborel C g
      \<Longrightarrow> set_integrable lborel B (\<lambda>t. g (F t) * f t)"
proof -
  have [simp]:"AE x in restrict_space lborel B. 0 \<le> f x"
    by (simp add: AE_restrict_space_iff f_pos)
  have space_M:"space M = B"
    by(simp add: M_def)
  have indicat_eq:"x \<in> B \<Longrightarrow> indicat_real B x = indicat_real C (F x)" for x
    using B by auto

  have F_meas1:"F \<in> M \<rightarrow>\<^sub>M restrict_space borel C"
    using F_meas by(simp add: M_def)

  have f_intbc[measurable]:"integrable (restrict_space lborel B) f"
    using set_integrable_subset[OF f_int[OF a] _ AB]
    by(simp add: set_integrable_eq)

  show "(\<integral>t\<in>B. g (F t) * f t \<partial>lborel) = (\<integral>t\<in>C. g t \<partial>lborel)"
    if g_meas:"g \<in> borel_measurable (restrict_space borel C)"
  proof -
    have [measurable]:"(\<lambda>x. indicat_real B x * g (F x))
                        \<in> borel_measurable (restrict_space lborel B)"
      using measurable_compose[OF F_meas1 g_meas]
        measurable_restrict_space1[of _ _ borel B,OF measurable_id]
      by(auto simp add: M_def)
    have [measurable]:"(\<lambda>t. indicat_real C t * g t)
                        \<in> borel_measurable (restrict_space borel C)"
      by (simp add: borel_measurable_times g_meas measurable_restrict_space1)
    have "(\<integral>t\<in>B. g (F t) * f t \<partial>lborel) = (\<integral>t\<in>B. g (F t) \<partial>M)"
      unfolding set_lebesgue_integral_def M_def
      by(subst integral_density)
        (auto simp: integral_restrict_space indicator_times_eq_if
          intro!: f_pos Bochner_Integration.integral_cong[OF refl])
    also have "... = (\<integral>t. indicat_real C t * g t \<partial>distr M (restrict_space borel C) F)"
      unfolding set_lebesgue_integral_def using F_meas1
      by(subst integral_distr)
        (auto intro!: Bochner_Integration.integral_cong simp: space_M indicat_eq[symmetric])
    thm meq
    also have "... = (\<integral>t\<in>C. g t \<partial>(restrict_space lborel C))"
      by(simp add: meq[symmetric] set_lebesgue_integral_def)
    also have "... = (\<integral>t\<in>C. g t \<partial>lborel)"
      unfolding set_lebesgue_integral_def
      by(subst integral_restrict_space)
        (auto intro!: Bochner_Integration.integral_cong simp: indicator_def)
    finally show "(\<integral>t\<in>B. g (F t) * f t \<partial>lborel) = (\<integral>t\<in>C. g t \<partial>lborel)" .
  qed
  assume g_integ:"set_integrable lborel C g"
  have g_meas:"g \<in> borel_measurable (restrict_space borel C)"
    using g_integ by(simp add: set_integrable_eq)

  have [measurable]:"(\<lambda>x. indicat_real B x * g (F x))
                        \<in> borel_measurable (restrict_space lborel B)"
    using measurable_compose[OF F_meas1 g_meas]
      measurable_restrict_space1[of _ _ borel B,OF measurable_id]
    by(auto simp add: M_def)
  have [measurable]:"(\<lambda>t. indicat_real C t * g t)
                        \<in> borel_measurable (restrict_space borel C)"
    by (simp add: borel_measurable_times g_meas measurable_restrict_space1)

  have "set_integrable (restrict_space lborel C) C g"
    unfolding set_integrable_def
    by(rule Bochner_Integration.integrable_cong[where f=g,OF refl,THEN iffD1])
      (use g_integ in "simp_all add: set_integrable_eq")
  hence 1:"integrable (distr M (restrict_space borel C) F) (\<lambda>t. indicat_real C t * g t)"
    by(simp add: meq[symmetric] set_integrable_def)
  have "set_integrable M B (\<lambda>t. g (F t))"
    using F_meas1
    by(auto intro!:
        Bochner_Integration.integrable_cong[THEN iffD2,OF refl _ integrable_distr[OF _ 1]]
     simp: set_integrable_def indicat_eq[symmetric] space_M)
  hence "integrable (restrict_space lborel B)
                    (\<lambda>t. f t *\<^sub>R (indicat_real B t * g (F t)))"
    by(intro integrable_density[THEN iffD1])
      (auto simp: set_integrable_def M_def intro!: f_pos)
  hence 2:"integrable lborel
                    (\<lambda>t. indicat_real B t *\<^sub>R f t *\<^sub>R (indicat_real B t * g (F t)))"
    by(subst integrable_restrict_space[symmetric]) auto
  show "set_integrable lborel B (\<lambda>t. g (F t) * f t)"
    unfolding set_integrable_def
    by(auto intro!: Bochner_Integration.integrable_cong[THEN iffD1,OF refl _ 2]
         simp : indicator_def)
qed

lemma
  fixes f and g:: "real \<Rightarrow> real" and a b c::real
  defines "F \<equiv> \<lambda>x. (\<integral>t\<in>{a<..x}. f t \<partial>lborel)"
  assumes f_pos:"\<And>x. a < x \<Longrightarrow> 0 < f x"
    and f_int:"\<And>d. a \<le> d \<Longrightarrow> set_integrable lborel {a..d} f"
    and ab[arith]:"a \<le> b" and bc[arith]:"b \<le> c"
  shows set_integral_compose_integral_Ioc:
    "g \<in> borel_measurable (restrict_space borel {F b<..F c})
       \<Longrightarrow> (\<integral>t\<in>{b<..c}. g (F t) * f t \<partial>lborel) = (\<integral>t\<in>{F b<..F c}. g t \<partial>lborel)"
    and set_integrable_compose_integral_Ioc:
    "set_integrable lborel {F b<..F c} g
      \<Longrightarrow> set_integrable lborel {b<..c} (\<lambda>t. g (F t) * f t)"
proof -
  define M where "M \<equiv> density (restrict_space lborel {b<..c}) f"
  have space_M:"space M = {b<..c}"
    by(simp add: M_def)
  have F_strict_mono:"\<And>d. a \<le> d \<Longrightarrow> strict_mono_on {a..d} F"
    using f_pos unfolding F_def
    by(intro set_itegral_strict_mono_Icc f_int) auto
  have F_0:"\<And>d. d \<le> a \<Longrightarrow> F d = 0"
    by(simp add: F_def)
  have F_pos:"a < d \<Longrightarrow> 0 < F d" for d
    unfolding F_def using f_pos
    by(intro set_integral_zero_less set_integrable_subset[OF f_int[of d]]) auto 
  have F_cont:"continuous_on UNIV F"
    unfolding F_def
    by(intro continuous_on_LBINT_Ioc f_int)
  have im_F:"b \<le> d \<Longrightarrow> F ` {b<..d} = {F b<..F d}" for d
    by(intro image_mono_on_continuous_on_Ioc monotone_on_subset[OF F_strict_mono[of d]]
        continuous_on_subset[OF F_cont])
     auto
  have im_F2:"b \<le> d \<Longrightarrow> F ` {b..d} = {F b..F d}" for d
    by(intro image_mono_on_continuous_on_Icc
        strict_mono_on_imp_mono_on monotone_on_subset[OF F_strict_mono[of d]]
        continuous_on_subset[OF F_cont])
     auto
  have F_meas1:"F \<in> M \<rightarrow>\<^sub>M restrict_space borel {F b<..F c}"
    using im_F[OF bc] borel_measurable_continuous_onI[OF F_cont]
    by(auto simp add: M_def intro!: measurable_restrict_space3)
  have F_meas2:"F \<in> restrict_space borel {b<..c} \<rightarrow>\<^sub>M restrict_space borel {F b<..F c}"
    using F_meas1 by(simp add: M_def)
  have f_intbc[measurable]:"integrable (restrict_space lborel {b<..c}) f"
    using set_integrable_subset[where B="{b<..c}",OF f_int[of c]]
    by(fastforce simp: set_integrable_eq)
  have bij:"bij_betw F {b<..c} {F b<..F c}"
  proof -
    have "inj_on F {b<..c}"
      by(subst injective_eq_monotone_map)
        (auto intro!: disjI1 monotone_on_subset[OF F_strict_mono[of c]]
          continuous_on_subset[OF F_cont])
    from inj_on_imp_bij_betw[OF this]
    show ?thesis
      unfolding im_F[OF bc] by simp
  qed

  have inv_mono:"x' \<le> y'"
    if mono:"F x' \<le> F y'"
      and x'[arith]:"b \<le> x'" "x' \<le> c"
      and y'[arith]: "b \<le> y'" "y' \<le> c" for x' y'
  proof(rule ccontr)
    assume "\<not> x' \<le> y'"
    then have "F y' < F x'"
      using strict_mono_onD[OF F_strict_mono[of c],of y' x']
      by simp
    thus False
      using mono by simp
  qed
  have inv_strict_mono:"x' < y'"
    if mono:"F x' < F y'"
      and x'[arith]:"b \<le> x'" "x' \<le> c"
      and y'[arith]: "b \<le> y'" "y' \<le> c" for x' y'
    by (metis inv_mono leD le_less that)
  have eq_indicat:"b < x \<Longrightarrow> x \<le> c \<Longrightarrow>
                      indicat_real {F b<..F c} (F x) = indicat_real {b<..c} x" for x
    by (auto simp: indicator_def
        intro!: strict_mono_onD[OF F_strict_mono[of c]]
        mono_onD[OF strict_mono_on_imp_mono_on[OF F_strict_mono[of c]]])

  have ex_inv:"F b \<le> x \<Longrightarrow> x \<le> F c \<Longrightarrow> \<exists>x'. b \<le> x' \<and> x' \<le> c \<and> F x' = x" for x
    by (metis (mono_tags, lifting) bc atLeastAtMost_iff im_F2 image_iff)
  have eq:"emeasure (distr M (restrict_space borel {F b<..F c}) F) {x<..y} = ennreal (y - x)"
    if xy[arith]:"x \<le> y" "F b \<le> x" "y \<le> F c" for x y
  proof -
    obtain x' y' where x'[arith]:"b \<le> x'" "x' \<le> c" and y'[arith]:"b \<le> y'" "y' \<le> c"
      and x'_eq:"F x' = x" and y'_eq:"F y' = y"
      using ex_inv[of x] ex_inv[of y] by auto
    have [arith]:"x' \<le> y'"
      by(auto intro!: inv_mono[of x' y'] simp: x'_eq y'_eq)
    have [measurable]:"{x<..y} \<in> sets (restrict_space borel {F b<..F c})"
      by(subst sets_restrict_space_iff) auto
    have [measurable]:"{x'<..y'} \<in> sets (restrict_space borel {b<..c})"
      by(subst sets_restrict_space_iff) auto
    have eq_set:"F -` {x<..y} \<inter> {b<..c} = {x'<..y'}"
      using x'_eq y'_eq inv_mono[of _ y'] inv_strict_mono[of x']
      by(auto intro!: strict_mono_onD[OF F_strict_mono[of c]]
          mono_onD[OF strict_mono_on_imp_mono_on[OF F_strict_mono[of c]]])
    have "emeasure (distr M (restrict_space borel {F b<..F c}) F) {x<..y}
          = emeasure M (F -` {x<..y} \<inter> space M)"
      by(intro emeasure_distr F_meas1) simp
    also have "... = emeasure M {x'<..y'}"
      by(simp add: M_def eq_set)
    also have "... = (\<integral>\<^sup>+x\<in>{x'<..y'}. ennreal (f x) \<partial>restrict_space lborel {b<..c})"
      unfolding M_def
      by(subst emeasure_density) auto
    also have "... = ennreal (\<integral>x\<in>{x'<..y'}. f x\<partial>restrict_space lborel {b<..c})"
      by(intro nn_set_integral_eq_set_integral f_intbc)
        (auto intro!: less_imp_le[OF f_pos])
    also have "... = ennreal (\<integral>x\<in>{x'<..y'}. f x\<partial>lborel)"
      by(subst set_integral_restrict_space)
        (auto intro!: arg_cong[where f=ennreal] Bochner_Integration.integral_cong
          simp: set_lebesgue_integral_def indicator_def)
    also have "... = ennreal (\<integral>x. indicator {a<..y'} x * f x - indicator {a<..x'} x * f x\<partial>lborel)"
      by(auto intro!: arg_cong[where f=ennreal] Bochner_Integration.integral_cong
          simp: set_lebesgue_integral_def indicator_def)
    also have "... = ennreal (F y' - F x')"
      using set_integrable_subset[where B="{a<..y'}",OF f_int[of c]]
        set_integrable_subset[where B="{a<..x'}",OF f_int[of c]]
      unfolding F_def set_lebesgue_integral_def real_scaleR_def set_integrable_def
      by(fastforce intro!: arg_cong[where f=ennreal] Bochner_Integration.integral_diff)
    finally show ?thesis
      by(simp add: x'_eq y'_eq)
  qed

  have meq:"restrict_space lborel {F b<..F c} = distr M (restrict_space borel {F b<..F c}) F"
  proof(rule measure_eqI_generator_eq_countable
      [where \<Omega>="{F b<..F c}" and E="(\<inter>) {F b<..F c} ` (range (\<lambda>(a, b). {a <.. b::real}))"
           and A="(\<inter>) {F b<..F c} ` ((\<lambda>(a, b). {a <.. b::real}) ` (\<rat> \<times> \<rat>))"])
    show "Int_stable ((\<inter>) {F b<..F c} ` range (\<lambda>(a, b). {a<..b}))"
      by(intro Int_stable_image_inter) (fastforce intro!: Int_stableI)
  next
    have *:"sets (distr M (restrict_space borel {F b<..F c}) F) =
          sets (restrict_space lborel {F b<..F c})"
      by(simp add: M_def cong: sets_restrict_space_cong)

    show "sets (restrict_space lborel {F b<..F c}) =
    sigma_sets {F b<..F c} ((\<inter>) {F b<..F c} ` range (\<lambda>(a, b). {a<..b}))"
      by(intro sets_restrict_space_sigma_sets[where \<Omega>=UNIV])
         (auto simp: borel_sigma_sets_Ioc)
    thus "sets (distr M (restrict_space borel {F b<..F c}) F) =
          sigma_sets {F b<..F c} ((\<inter>) {F b<..F c} ` range (\<lambda>(a, b). {a<..b}))"
      unfolding * by meson
  next
    fix X
    assume X:"X \<in> (\<inter>) {F b<..F c} ` range (\<lambda>(a, b). {a<..b})"
    then obtain x y where "X = {x<..y}" "F b \<le> x" "y \<le> F c"
      by fastforce
    thus "emeasure (restrict_space lborel {F b<..F c}) X =
         emeasure (distr M (restrict_space borel {F b<..F c}) F) X"
      by(cases "x \<le> y", subst emeasure_restrict_space)
         (auto simp add: eq emeasure_restrict_space)
  next
    have "real_of_int \<lfloor>F b\<rfloor> \<in> \<rat>" "real_of_int \<lceil>F c\<rceil> \<in> \<rat>"
         "{F b<..F c} \<inter> {\<lfloor>F b\<rfloor><..\<lceil>F c\<rceil>} = {F b<..F c}"
      by auto
    thus "\<Union> ((\<inter>) {F b<..F c} ` (\<lambda>(a, b). {a<..b}) ` (\<rat> \<times> \<rat>)) = {F b<..F c}"
      by blast
  next
    fix a
    assume a:"a \<in> (\<inter>) {F b<..F c} ` (\<lambda>(a, b). {a<..b}) ` (\<rat> \<times> \<rat>)"
    then have "bounded a"
      using bounded_Ioc by blast
    from emeasure_bounded_finite[OF this] a
    show "emeasure (restrict_space lborel {F b<..F c}) a \<noteq> \<infinity>"
      by(subst emeasure_restrict_space) auto
  qed(auto intro!: countable_rat)

  have f_int':"\<And>x. x \<in> {a..} \<Longrightarrow> set_integrable lborel {a..x} f"
    by (simp add: f_int)
  have c_in:"c \<in> {a..}"
    by simp
  have f_nonneg:"AE x \<in> {b<..c} in lborel. 0 \<le> f x"
    by(auto intro!: less_imp_le f_pos)
  show "(\<integral>t\<in>{b<..c}. g (F t) * f t \<partial>lborel) = (\<integral>t\<in>{F b<..F c}. g t \<partial>lborel)"
    if g_meas:"g \<in> borel_measurable (restrict_space borel {F b<..F c})"
    using
      set_integral_compose_integral[where A="\<lambda>x. {a..x}" and B="{b<..c}"
        and C="{F b<..F c}" and a=c and X="{a..}" and f=f and g=g
        , OF f_nonneg f_int' _ _ _ _ _ _ c_in _ g_meas] meq F_meas2 im_F[of c]
    by (simp add: LBINT_Ioc_eq_Icc greaterThanAtMost_subseteq_atLeastAtMost_iff F_def M_def)

  show "set_integrable lborel {b<..c} (\<lambda>t. g (F t) * f t)"
    if g_integ:"set_integrable lborel {F b<..F c} g"
    using
      set_integrable_compose_integral[where A="\<lambda>x. {a..x}" and B="{b<..c}"
        and C="{F b<..F c}" and a=c and X="{a..}" and f=f and g=g
        , OF f_nonneg f_int' _ _ _ _ _ _ c_in _ g_integ] meq F_meas2 im_F[of c]
    by (simp add: LBINT_Ioc_eq_Icc greaterThanAtMost_subseteq_atLeastAtMost_iff F_def M_def)
qed


lemma
  fixes f and g:: "real \<Rightarrow> real" and a b c::real
  defines "F \<equiv> \<lambda>x. (\<integral>t\<in>{x<..}. f t \<partial>lborel)"
  assumes f_pos:"\<And>x. a < x \<Longrightarrow> 0 < f x"
    and f_int:"set_integrable lborel {a..} f"
    and ab[arith]:"a \<le> b" and bc[arith]:"b \<le> c"
  shows set_integral_compose_integral_tail:
    "g \<in> borel_measurable (restrict_space borel {F c<..F b})
       \<Longrightarrow> (\<integral>t\<in>{b<..c}. g (F t) * f t \<partial>lborel) = (\<integral>t\<in>{F c<..F b}. g t \<partial>lborel)"
    and set_integrable_compose_integral_tail:
    "set_integrable lborel {F c<..F b} g
      \<Longrightarrow> set_integrable lborel {b<..c} (\<lambda>t. g (F t) * f t)"
proof -
  have g_meas':"g \<in> borel_measurable (restrict_space borel {F c..F b})"
    if h:"g \<in> borel_measurable (restrict_space borel {F c<..F b})"
  proof -
    have *:"- {F c} \<inter> {F c..F b} = {F c<..F b}"
      by auto
    have "g = (\<lambda>x. if x \<in> -{F c} then g x else g (F c))"
      by auto
    also have "... \<in> borel_measurable (restrict_space borel {F c..F b})"
      by(subst measurable_restrict_space_iff[symmetric])
        (auto simp: Int_commute sets_restrict_space restrict_restrict_space * h)
    finally show ?thesis .
  qed
  define M where "M \<equiv> density (restrict_space lborel {b..c}) f"
  have space_M:"space M = {b..c}"
    by(simp add: M_def)
  have F_strict_mono:"strict_antimono_on {a..} F"
    using f_pos unfolding F_def
    by(intro set_itegral_tail_strict_antimono f_int) auto
  hence F_mono:"antimono_on {a..} F"
    using strict_antimono_iff_antimono by blast
  have F_pos:"a < d \<Longrightarrow> 0 < F d" for d
    unfolding F_def using f_pos
    by(intro set_integral_zero_less set_integrable_subset[OF f_int]
        order.strict_trans2[of _ "emeasure lborel {d<..d + 1}"
                                 "emeasure lborel {d<..}",OF _ emeasure_mono])
       auto
  have F_cont:"continuous_on {a..} F"
    unfolding F_def
    by(intro continuous_on_LBINT_tail f_int)
  have im_F:"b \<le> d \<Longrightarrow> F ` {b..d} = {F d..F b}" for d
    using monotone_on_subset[OF F_strict_mono]
    by(intro image_antimono_on_continuous_on_Icc 
        continuous_on_subset[OF F_cont])
      (auto simp: strict_antimono_iff_antimono)

  have F_meas1:"F \<in> M \<rightarrow>\<^sub>M restrict_space borel {F c..F b}"
    using im_F[OF bc]
      borel_measurable_continuous_on_restrict[OF continuous_on_subset[where t="{b..c}",OF F_cont]]
    by(fastforce simp add: M_def intro!: measurable_restrict_space2)
  hence F_meas2:"F \<in> restrict_space borel {b..c} \<rightarrow>\<^sub>M restrict_space borel {F c..F b}"
    by(simp add: M_def)
  have f_intbc[measurable]:"integrable (restrict_space lborel {b..c}) f"
    using set_integrable_subset[where B="{b..c}",OF f_int]
    by(fastforce simp: set_integrable_eq)

  have inv_mono:"y' \<le> x'"
    if mono:"F x' \<le> F y'"
      and x'[arith]:"b \<le> x'" "x' \<le> c"
      and y'[arith]: "b \<le> y'" "y' \<le> c" for x' y'
  proof(rule ccontr)
    assume "\<not> y' \<le> x'"
    thus False
      using monotone_onD[OF F_strict_mono,of x' y'] mono
      by simp
  qed
  have inv_strict_mono:"y' < x'"
    if mono:"F x' < F y'"
      and x'[arith]:"b \<le> x'" "x' \<le> c"
      and y'[arith]: "b \<le> y'" "y' \<le> c" for x' y'
    by (metis inv_mono leD le_less that)

  have ex_inv:"F c \<le> x \<Longrightarrow> x \<le> F b \<Longrightarrow> \<exists>x'. b \<le> x' \<and> x' \<le> c \<and> F x' = x" for x
    by (metis (mono_tags, lifting) im_F[OF bc] atLeastAtMost_iff image_iff)

  have eq:"emeasure (distr M (restrict_space borel {F c..F b}) F) {x..y} = ennreal (y - x)"
    if xy[arith]:"x \<le> y" "F c \<le> x" "y \<le> F b" for x y
  proof -
    obtain x' y' where x'[arith]:"b \<le> x'" "x' \<le> c" and y'[arith]:"b \<le> y'" "y' \<le> c"
      and x'_eq:"F x' = x" and y'_eq:"F y' = y"
      using ex_inv[of x] ex_inv[of y] by auto
    have [arith]:"y' \<le> x'"
      by(auto intro!: inv_mono[of x' y'] simp: x'_eq y'_eq)
    have [measurable]:"{x..y} \<in> sets (restrict_space borel {F c..F b})"
      by(subst sets_restrict_space_iff) simp_all
    have [measurable]:"{y'..x'} \<in> sets (restrict_space borel {b..c})"
      by(subst sets_restrict_space_iff) auto
    have eq_set:"F -` {x..y} \<inter> {b..c} = {y'..x'}"
      using x'_eq y'_eq inv_mono[of _ y'] inv_mono[of x']
      by(fastforce intro!: monotone_onD[OF F_mono])
    have "emeasure (distr M (restrict_space borel {F c..F b}) F) {x..y}
          = emeasure M (F -` {x..y} \<inter> space M)"
      by(intro emeasure_distr F_meas1) simp
    also have "... = emeasure M {y'..x'}"
      by(simp add: M_def eq_set)
    also have "... = (\<integral>\<^sup>+x\<in>{y'..x'}. ennreal (f x) \<partial>restrict_space lborel {b..c})"
      unfolding M_def
      by(subst emeasure_density) auto
    also have "... = ennreal (\<integral>x\<in>{y'..x'}. f x\<partial>restrict_space lborel {b..c})"
      by(intro nn_set_integral_eq_set_integral f_intbc)
        (auto intro!: AE_I'[where N="{b}"] less_imp_le[OF f_pos]
          simp: countable_imp_null_set_lborel null_sets_restrict_space)
    also have "... = ennreal (\<integral>x\<in>{y'..x'}. f x\<partial>lborel)"
      by(subst set_integral_restrict_space)
        (auto intro!: arg_cong[where f=ennreal] Bochner_Integration.integral_cong
          simp: set_lebesgue_integral_def indicator_def)
    also have "... = ennreal (\<integral>x. indicator {y'..} x * f x - indicator {x'<..} x * f x\<partial>lborel)"
      by(auto intro!: arg_cong[where f=ennreal] Bochner_Integration.integral_cong
          simp: set_lebesgue_integral_def indicator_def)
    also have "... = ennreal ((\<integral>x. indicator {y'..} x * f x \<partial>lborel)
                               - (\<integral>x. indicator {x'<..} x * f x\<partial>lborel))"
      using set_integrable_subset[where B="{y'..}",OF f_int]
        set_integrable_subset[where B="{x'<..}",OF f_int]
      by(fastforce intro!: arg_cong[where f=ennreal] Bochner_Integration.integral_diff
          simp: set_integrable_def)
    also have "... = ennreal (F y' - F x')"
      unfolding F_def set_integral_atLeast_eq[of y']
      by(simp add: set_lebesgue_integral_def)
    finally show ?thesis
      by(simp add: x'_eq y'_eq)
  qed

  have meq:"restrict_space lborel {F c..F b} = distr M (restrict_space borel {F c..F b}) F"
  proof(rule measure_eqI_generator_eq_countable
      [where \<Omega>="{F c..F b}" and E="(\<inter>) {F c..F b} ` (range (\<lambda>(a, b). {a .. b::real}))"
           and A="(\<inter>) {F c..F b} ` ((\<lambda>(a, b). {a .. b::real}) ` (\<rat> \<times> \<rat>))"])
    show "Int_stable ((\<inter>) {F c..F b} ` range (\<lambda>(a, b). {a..b}))"
      by(intro Int_stable_image_inter) (fastforce intro!: Int_stableI)
  next
    have *:"sets (distr M (restrict_space borel {F c..F b}) F) =
          sets (restrict_space lborel {F c..F b})"
      by(simp add: M_def cong: sets_restrict_space_cong)
    show "sets (restrict_space lborel {F c..F b}) =
    sigma_sets {F c..F b} ((\<inter>) {F c..F b} ` range (\<lambda>(a, b). {a..b}))"
      by(intro sets_restrict_space_sigma_sets[where \<Omega>=UNIV])
         (auto simp: borel_eq_atLeastAtMost)
    thus "sets (distr M (restrict_space borel {F c..F b}) F) =
          sigma_sets {F c..F b} ((\<inter>) {F c..F b} ` range (\<lambda>(a, b). {a..b}))"
      unfolding * by meson
  next
    fix X
    assume X:"X \<in> (\<inter>) {F c..F b} ` range (\<lambda>(a, b). {a..b})"
    then obtain x y where "X = {x..y}" "F c \<le> x" "y \<le> F b"
      by fastforce
    thus "emeasure (restrict_space lborel {F c..F b}) X =
         emeasure (distr M (restrict_space borel {F c..F b}) F) X"
      by(cases "x \<le> y", subst emeasure_restrict_space)
         (auto simp add: eq emeasure_restrict_space)
  next
    have "real_of_int \<lfloor>F c\<rfloor> \<in> \<rat>" "real_of_int \<lceil>F b\<rceil> \<in> \<rat>"
         "{F c..F b} \<inter> {\<lfloor>F c\<rfloor>..\<lceil>F b\<rceil>} = {F c..F b}"
      by auto
    thus "\<Union> ((\<inter>) {F c..F b} ` (\<lambda>(a, b). {a..b}) ` (\<rat> \<times> \<rat>)) = {F c..F b}"
      by blast
  next
    fix a
    assume a:"a \<in> (\<inter>) {F c..F b} ` (\<lambda>(a, b). {a..b}) ` (\<rat> \<times> \<rat>)"
    then have "bounded a"
      by auto     
    from emeasure_bounded_finite[OF this] a
    show "emeasure (restrict_space lborel {F c..F b}) a \<noteq> \<infinity>"
      by(subst emeasure_restrict_space) auto
  qed(auto intro!: countable_rat)

  have f_int':"\<And>x. x \<in> {a..} \<Longrightarrow> set_integrable lborel {x..} f"
    by (auto intro!: set_integrable_subset[OF f_int])
  have a_in:"a \<in> {a..}"
    by simp
  have f_nonneg:"AE x\<in>{b..c} in lborel. 0 \<le> f x"
    using less_imp_le[OF f_pos]
    by(auto intro!:  AE_I'[where N="{b}"])

  show "(\<integral>t\<in>{b<..c}. g (F t) * f t \<partial>lborel) = (\<integral>t\<in>{F c<..F b}. g t \<partial>lborel)"
    if g_meas:"g \<in> borel_measurable (restrict_space borel {F c<..F b})"
    using set_integral_compose_integral[where A="\<lambda>x. {x..}" and B="{b..c}"
        and C="{F c..F b}" and a=a and X="{a..}"  and f=f and g=g
        ,OF f_nonneg f_int' _ _ _ _ _ _ a_in _ g_meas'[OF g_meas]] meq F_meas2 im_F[of c]
    by(simp add: F_def M_def LBINT_Ioc_eq_Icc[symmetric] set_integral_atLeast_eq)

  show "set_integrable lborel {b<..c} (\<lambda>t. g (F t) * f t)"
    if integ:"set_integrable lborel {F c<..F b} g"
    using set_integrable_compose_integral[where A="\<lambda>x. {x..}" and B="{b..c}"
        and C="{F c..F b}" and a=a and X="{a..}"  and f=f and g=g
        ,OF f_nonneg f_int' _ _ _ _ _ _ a_in _ ] meq F_meas2 im_F[of c] integ
    by(simp add: F_def M_def LBINT_Ioc_eq_Icc[symmetric]
        set_integral_atLeast_eq set_integrable_Ioc_eq_Icc)
qed


subsection \<open> Convergence Theorems with Real Index\<close>
lemma borel_measurable_LIMSEQ_metric_at_top:
  fixes f :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: metric_space"
  assumes [measurable]: "\<And>r. K \<le> r \<Longrightarrow> f r \<in> borel_measurable M"
  assumes lim: "\<And>x. x \<in> space M \<Longrightarrow> ((\<lambda>r. f r x) \<longlongrightarrow> g x) at_top"
  shows "g \<in> borel_measurable M"
  by(rule borel_measurable_LIMSEQ_metric[where f="\<lambda>n. f (real n + K)"])
  (use assms in "auto simp: at_top_real_iff_all_sequentially add.commute[of _ K]
      intro!: filterlim_compose[OF _ filterlim_tendsto_add_at_top[OF tendsto_const[of K]
               filterlim_real_sequentially]]")

lemma nn_integral_at_top_real:
  assumes "mono_on {K..} f" "\<And>r. r \<ge> K \<Longrightarrow> f r \<in> borel_measurable M"
    and u: "\<And>x. ((\<lambda>r::real. f r x) \<longlongrightarrow> u x) at_top"
  shows "((\<lambda>r. integral\<^sup>N M (f r)) \<longlongrightarrow> integral\<^sup>N M u) at_top"
  using assms
  by(auto intro!: nn_integral_LIMSEQ
      simp: at_top_real_iff_all_sequentially'[where K=K] monotone_on_def)

theorem nn_integral_dominated_convergence_at_top:
  assumes
       "\<And>r::real. r \<ge> K \<Longrightarrow> u r \<in> borel_measurable M"
       "u' \<in> borel_measurable M" "w \<in> borel_measurable M"
    and "\<And>r. r \<ge> K \<Longrightarrow> AE x in M. u r x \<le> w x"
    and "(\<integral>\<^sup>+x. w x \<partial>M) < \<infinity>"
    and "AE x in M. ((\<lambda>r. u r x) \<longlongrightarrow> u' x) at_top"
  shows "((\<lambda>r. (\<integral>\<^sup>+x. u r x \<partial>M)) \<longlongrightarrow> (\<integral>\<^sup>+x. u' x \<partial>M)) at_top"
  using assms 
  by(force intro!: nn_integral_dominated_convergence
      simp: at_top_real_iff_all_sequentially'[where K=K])

lemma
  fixes f :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>r. K \<le> r \<Longrightarrow> integrable M (f r)" and mono: "AE x in M. mono_on {K..} (\<lambda>r. f r x)"
  and "AE x in M. ((\<lambda>r. f r x) \<longlongrightarrow> u x) at_top"
  and "((\<lambda>r. integral\<^sup>L M (f r)) \<longlongrightarrow> x) at_top"
  and u:"u \<in> borel_measurable M"
  shows integrable_monotone_convergence_real: "integrable M u" (is ?g1)
    and integral_monotone_convergence_real: "integral\<^sup>L M u = x" (is ?g2)
    and has_bochner_integral_monotone_convergence_real: "has_bochner_integral M u x" (is ?g3)
proof -
  have fl:"filterlim (\<lambda>n. K + real n) at_top sequentially"
    by(rule filterlim_tendsto_add_at_top) (use filterlim_real_sequentially in auto)
  have inc: "incseq (\<lambda>n. K + real n)"
    by(auto intro!: monoI)
  have "\<And>n. integrable M (f (K + real n))" "AE x in M. incseq (\<lambda>n. f (K + real n) x)"
    "AE x in M. (\<lambda>n. f (K + real n) x) \<longlonglongrightarrow> u x"
    "(\<lambda>n. integral\<^sup>L M (f (K + real n))) \<longlonglongrightarrow> x"
    using assms fl inc by(auto simp: at_top_real_iff_all_sequentially mono_on_def)
  thus ?g1 ?g2 ?g3
    using u integrable_monotone_convergence[where f="\<lambda>n. f (K + real n)"]
      integral_monotone_convergence[where f="\<lambda>n. f (K + real n)"]
      has_bochner_integral_monotone_convergence [where f="\<lambda>n. f (K + real n)"]
    by blast+
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}" and w :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "\<And>r::real. K \<le> r \<Longrightarrow> s r \<in> borel_measurable M"
    "integrable M w"
  assumes lim: "AE x in M. ((\<lambda>r. s r x) \<longlongrightarrow> f x) at_top"
  assumes bound: "\<And>r. K \<le> r \<Longrightarrow> AE x in M. norm (s r x) \<le> w x"
  shows integrable_dominated_convergence_real: "integrable M f"
    and integrable_dominated_convergence_real2: "\<And>r. K \<le> r \<Longrightarrow> integrable M (s r)"
    and integral_dominated_convergence_real: "((\<lambda>r. integral\<^sup>L M (s r)) \<longlongrightarrow> integral\<^sup>L M f) at_top"
proof -
  have fl:"filterlim (\<lambda>n. r + real n) at_top sequentially" for r
    by(rule filterlim_tendsto_add_at_top) (use filterlim_real_sequentially in auto)
  have inc: "incseq (\<lambda>n. r + real n)" for r
    by(auto intro!: monoI)
  show "integrable M f"
    by(rule integrable_dominated_convergence[where s="\<lambda>n. s (K + real n)" and w=w])
      (use assms fl[of K] inc[of K] bound[of "K + real _"]
       in "auto simp: at_top_real_iff_all_sequentially")
  have dct:"f \<in> borel_measurable M \<Longrightarrow> (\<And>i. s (r + real i) \<in> borel_measurable M)
            \<Longrightarrow> integrable M w \<Longrightarrow> AE x in M. (\<lambda>i. s (r + real i) x)  \<longlonglongrightarrow> f x
            \<Longrightarrow> (\<And>i. AE x in M. norm (s (r + real i) x) \<le> w x) \<Longrightarrow> integrable M (s r)" for r
    using integrable_dominated_convergence2[where s="\<lambda>n. s (r + real n)" and i=0]
    by simp
  show "K \<le> r \<Longrightarrow> integrable M (s r)" for r
    by(rule dct) (use assms fl[of r] inc[of r]
                  in "auto simp: at_top_real_iff_all_sequentially")
  show "((\<lambda>r. integral\<^sup>L M (s r)) \<longlongrightarrow> integral\<^sup>L M f) at_top"
    unfolding at_top_real_iff_all_sequentially'[where K=K]
    by(intro allI impI integral_dominated_convergence[where w=w])
      (use assms in "auto simp: at_top_real_iff_all_sequentially")
qed

corollary
  fixes f :: "real \<Rightarrow> real"
  assumes f_nonneg: "\<And>x. K < x \<Longrightarrow> 0 \<le> f x"
    and integrable: "\<And>r. K < r \<Longrightarrow> set_integrable M {K<..r} f"
    and le:"\<And>r. K < r \<Longrightarrow> (\<integral>x\<in>{K<..r}. f x \<partial>M) \<le> G"
  shows interval_integral_inf:
         "((\<lambda>r. (\<integral>x\<in>{K<..r}. f x \<partial>M)) \<longlongrightarrow> (\<integral>x\<in>{K<..}. f x \<partial>M)) at_top"
    and interval_integral_inf_integrable:
         "set_integrable M {K<..} f"
    and measurable_integral_inf:
         "set_borel_measurable M {K<..} f"
proof -
  have 1:"\<And>r. K + 1 \<le> r \<Longrightarrow> integrable M (\<lambda>x. indicat_real {K<..r} x * f x)"
    using integrable by(auto simp: set_integrable_def)
  have 2: "AE x in M. mono_on {K + 1..} (\<lambda>r. indicat_real {K<..r} x * f x)"
    by(auto intro!: mono_onI f_nonneg simp: indicator_def)
  have 3: "AE x in M.
           ((\<lambda>r. indicat_real {K<..r} x * f x) \<longlongrightarrow> indicator {K<..} x * f x) at_top"
  proof(rule AE_I2)
    fix x
    show "((\<lambda>r. indicat_real {K<..r} x * f x) \<longlongrightarrow> indicat_real {K<..} x * f x) at_top"
      by(auto intro!: tendstoI eventually_at_top_linorderI[where c=x]
          simp: dist_real_def indicator_def)
  qed
  have "mono_on {K<..} (\<lambda>r. (\<integral>x\<in>{K<..r}. f x \<partial>M))"
    using integrable f_nonneg
    by(auto intro!: mono_onI Bochner_Integration.integral_mono
        simp: set_lebesgue_integral_def set_integrable_def indicator_def)
  from mono_convergent_real_less[OF this le]
  obtain l where l:"((\<lambda>r. (\<integral>x\<in>{K<..r}. f x \<partial>M)) \<longlongrightarrow> l) at_top"
    by blast
  show "set_borel_measurable M {K<..} f"
    unfolding set_borel_measurable_def
  proof(rule borel_measurable_LIMSEQ_metric)
    fix x
    obtain n where "x \<le> K + real n"
      by (meson abs_diff_le_iff real_arch_simple)
    thus " (\<lambda>i. indicat_real {K<..K + real i + 1} x * f x)
         \<longlonglongrightarrow> indicat_real {K<..} x *\<^sub>R f x"
      by(auto intro!:LIMSEQ_I exI[where x=n] simp: indicator_def)
  qed(use integrable in "auto simp: set_integrable_def")
  thus  "((\<lambda>r. (\<integral>x\<in>{K<..r}. f x \<partial>M)) \<longlongrightarrow> (\<integral>x\<in>{K<..}. f x \<partial>M)) at_top"
    and "set_integrable M {K<..} f"
    using integrable_monotone_convergence_real[OF 1 2 3,of l] l
          integral_monotone_convergence_real[OF 1 2 3,of l ]
    unfolding set_lebesgue_integral_def set_borel_measurable_def set_integrable_def
    by auto
qed

corollary interval_integral_inf2:
  fixes f :: "real \<Rightarrow> real"
  assumes f_nonneg: "\<And>x. K < x \<Longrightarrow> 0 \<le> f x"
    and integrable: "\<And>r. K < r \<Longrightarrow> set_integrable M {K<..r} f"
    and integrable2:"set_integrable M {K<..} f"
  shows "((\<lambda>r. (\<integral>x\<in>{K<..r}. f x \<partial>M)) \<longlongrightarrow> (\<integral>x\<in>{K<..}. f x \<partial>M)) at_top"
proof(rule interval_integral_inf)
  fix r
  assume r:"K < r"
  show "(\<integral>x\<in>{K<..r}. f x \<partial>M) \<le> (\<integral>x\<in>{K<..}. f x \<partial>M)"
    using integrable[OF r] integrable2 f_nonneg
    by(auto intro!: Bochner_Integration.integral_mono
        simp: set_integrable_def set_lebesgue_integral_def indicator_def)
qed(use assms in auto)

subsection \<open> Change of Variables w.r.t. Lebesgue Integration on a Set\<close>
lemma lebesgue_integral_change_of_variables_real1:
  fixes f :: "real \<Rightarrow> real" and g :: "real\<Rightarrow> real"
  assumes S[measurable]: "S \<in> sets borel"
    and g[measurable]:"g \<in> borel_measurable (restrict_space borel S)"
    and g'[measurable]:"g' \<in> borel_measurable (restrict_space borel S)"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and integrable: "set_integrable lborel (g ` S) f"
  shows "(\<integral>x\<in> g ` S. f x \<partial>lborel) = (\<integral>x\<in>S. \<bar>g' x\<bar> * f (g x) \<partial>lborel)"
proof -
  have *:"set_borel_measurable borel S (\<lambda>x. f (g x))"
    using set_borel_measurable_comp[of S borel g f]
      set_integrable_set_borel_measurable[OF integrable] g
    by (simp add: borel_measurable_restrict_space_iff set_borel_measurable_def)
  hence [measurable]:"(\<lambda>x. indicat_real S x * (\<bar>g' x\<bar> * f (g x))) \<in> borel_measurable borel"
  proof -
    have "set_borel_measurable borel S (\<lambda>x. \<bar>g' x\<bar>)"
      by(auto simp: set_borel_measurable_iff_restrict_space)
    from set_borel_measurable_times[OF this *]
    show ?thesis
      by(simp add: set_borel_measurable_def)
  qed
  have S':"S \<in> sets lebesgue"
    using S sets_lborel by blast 
  have h:"f absolutely_integrable_on g ` S"
    using integrable by(auto simp: set_integrable_def integrable_completion)
  hence h':"(\<lambda>x. \<bar>g' x\<bar> * f (g x)) absolutely_integrable_on S"
    using absolutely_integrable_change_of_variables_real[OF S' der_g inj]
    by force
  have "(\<integral>x\<in> g ` S. f x \<partial>lborel) = integral (g ` S) f"
    by(intro set_borel_integral_eq_integral integrable)
  also have "... = integral S (\<lambda>x. \<bar>g' x\<bar> * f (g x))"
    using has_absolute_integral_change_of_variables_1'[OF S' der_g inj] h' by blast
  also have "... = (\<integral>x\<in>S. \<bar>g' x\<bar> * f (g x) \<partial>lborel)"
    by(subst set_borel_integral_eq_integral)
      (use h' in"auto simp: set_integrable_def integrable_completion")
  finally show ?thesis .
qed

lemma lebesgue_integral_change_of_variables_real2:
  fixes f :: "real \<Rightarrow> real" and g :: "real\<Rightarrow> real"
  assumes S[measurable]: "S \<in> sets borel"
    and f:"set_borel_measurable borel (g ` S) f"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and integrable:"set_integrable lborel S (\<lambda>x. \<bar>g' x\<bar> * f (g x))"
  shows  "(\<integral>x\<in> g ` S. f x \<partial>lborel) = (\<integral>x\<in>S. \<bar>g' x\<bar> * f (g x) \<partial>lborel)"
proof -
  have S':"S \<in> sets lebesgue"
    using S sets_lborel by blast
  have [measurable]:"(\<lambda>x. indicat_real (g ` S) x * f x) \<in> borel_measurable borel"
    using f by(simp add: set_borel_measurable_def)
  have h':"(\<lambda>x. \<bar>g' x\<bar> * f (g x)) absolutely_integrable_on S"
    using integrable by(auto simp: set_integrable_def integrable_completion)
  hence h:"f absolutely_integrable_on g ` S"
    using absolutely_integrable_change_of_variables_real[OF S' der_g inj]
    by force
  have "set_integrable lborel (g ` S) f"
    using h by(auto simp: set_integrable_def integrable_completion)
  hence "(\<integral>x\<in> g ` S. f x \<partial>lborel) = integral (g ` S) f"
    by(intro set_borel_integral_eq_integral)
  also have "... = integral S (\<lambda>x. \<bar>g' x\<bar> * f (g x))"
    using has_absolute_integral_change_of_variables_1'[OF S' der_g inj] h' by blast
  also have "... = (\<integral>x\<in>S. \<bar>g' x\<bar> * f (g x) \<partial>lborel)"
    by(simp add: integrable set_borel_integral_eq_integral)
  finally show ?thesis .
qed

lemma lebesgue_integrable_change_of_variables_real:
  fixes f :: "real \<Rightarrow> real" and g :: "real\<Rightarrow> real"
  assumes S[measurable]: "S \<in> sets borel"
    and f:"set_borel_measurable borel (g ` S) f"
    and g[measurable]:"g \<in> borel_measurable (restrict_space borel S)"
    and g'[measurable]:"g' \<in> borel_measurable (restrict_space borel S)"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "set_integrable lborel (g ` S) f
         \<longleftrightarrow> set_integrable lborel S (\<lambda>x. \<bar>g' x\<bar> * f (g x))"
proof -
  have *:"set_borel_measurable borel S (\<lambda>x. f (g x))"
    using set_borel_measurable_comp[of S borel g f] f g
    by (simp add: borel_measurable_restrict_space_iff set_borel_measurable_def)
  have [measurable]:"(\<lambda>x. indicat_real S x * (\<bar>g' x\<bar> * f (g x))) \<in> borel_measurable borel"
  proof -
    have "set_borel_measurable borel S (\<lambda>x. \<bar>g' x\<bar>)"
      by(auto simp: set_borel_measurable_iff_restrict_space)
    from set_borel_measurable_times[OF this *]
    show ?thesis
      by(simp add: set_borel_measurable_def)
  qed
  have [measurable]:"(\<lambda>x. indicat_real (g ` S) x * f x) \<in> borel_measurable borel"
    using f by(simp add: set_borel_measurable_def)
  show ?thesis
    using absolutely_integrable_change_of_variables_real[OF _ der_g inj,of f] S
    by(auto simp: set_integrable_def integrable_completion)
qed

lemma nn_integral_change_of_variables_real1:
  fixes f :: "real \<Rightarrow> real" and g :: "real\<Rightarrow> real"
  assumes S[measurable]: "S \<in> sets borel"
    and g[measurable]:"g \<in> borel_measurable (restrict_space borel S)"
    and g'[measurable]:"g' \<in> borel_measurable (restrict_space borel S)"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and integrable: "set_integrable lborel (g ` S) f"
    and nonneg:"AE x\<in>S in lborel. 0 \<le> f (g x)" "AE x\<in>g ` S in lborel. 0 \<le> f x"
  shows "(\<integral>\<^sup>+x\<in> g ` S. ennreal (f x) \<partial>lborel) = (\<integral>\<^sup>+x\<in>S. ennreal (\<bar>g' x\<bar> * f (g x)) \<partial>lborel)"
proof -
  have f:"set_borel_measurable borel (g ` S) f"
    using integrable by(auto simp: set_integrable_def set_borel_measurable_def)
  have integrable2:"set_integrable lborel S (\<lambda>x. \<bar>g' x\<bar> * f (g x))"
    using lebesgue_integrable_change_of_variables_real assms f by blast
  have "(\<integral>\<^sup>+x\<in> g ` S. ennreal (f x) \<partial>lborel)
         = (\<integral>\<^sup>+ x. ennreal (indicat_real (g ` S) x * f x) \<partial>lborel)"
    using mult.commute
    by(auto simp: indicator_mult_ennreal[symmetric] intro!: nn_integral_cong)
  also have "... = ennreal (\<integral>x. indicat_real (g ` S) x * f x \<partial>lborel)"
    by(rule nn_integral_eq_integral)
      (use integrable nonneg in "auto simp: set_integrable_def")
  also have "... = ennreal (\<integral>x\<in> g ` S. f x \<partial>lborel)"
    by(simp add: set_lebesgue_integral_def)
  also have "... = ennreal (\<integral>x\<in>S. \<bar>g' x\<bar> * f (g x) \<partial>lborel)"
    by(intro arg_cong[where f=ennreal] lebesgue_integral_change_of_variables_real1 assms)
  also have "... = ennreal (\<integral>x. indicat_real S x * (\<bar>g' x\<bar> * f (g x)) \<partial>lborel)"
    by(simp add: set_lebesgue_integral_def)
  also have "... = (\<integral>\<^sup>+ x. ennreal (indicat_real S x * (\<bar>g' x\<bar> * f (g x))) \<partial>lborel)"
    by(rule nn_integral_eq_integral[symmetric])
      (use integrable2 nonneg in "auto simp: set_integrable_def")
  also have "... = (\<integral>\<^sup>+x\<in>S. ennreal (\<bar>g' x\<bar> * f (g x)) \<partial>lborel)"
    using mult.commute
    by(auto simp: indicator_mult_ennreal[symmetric] intro!: nn_integral_cong)
  finally show ?thesis .
qed

lemma nn_integral_change_of_variables_real1':
  fixes f :: "real \<Rightarrow> real" and g :: "real\<Rightarrow> real"
  assumes "S \<in> sets borel"
    and "g \<in> borel_measurable (restrict_space borel S)"
    and "g' \<in> borel_measurable (restrict_space borel S)"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and "inj_on g S"
    and "set_integrable lborel (g ` S) f"
    and nonneg:"\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f (g x)"
  shows "(\<integral>\<^sup>+x\<in> g ` S. ennreal (f x) \<partial>lborel) = (\<integral>\<^sup>+x\<in>S. ennreal (\<bar>g' x\<bar> * f (g x)) \<partial>lborel)"
  by(auto intro!: nn_integral_change_of_variables_real1 assms)

lemma nn_integral_change_of_variables_real2:
  fixes f :: "real \<Rightarrow> real" and g :: "real\<Rightarrow> real"
  assumes S[measurable]: "S \<in> sets borel"
    and f:"set_borel_measurable borel (g ` S) f"
    and g[measurable]:"g \<in> borel_measurable (restrict_space borel S)"
    and g'[measurable]:"g' \<in> borel_measurable (restrict_space borel S)"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and integrable:"set_integrable lborel S (\<lambda>x. \<bar>g' x\<bar> * f (g x))"
    and nonneg:"AE x\<in>S in lborel. 0 \<le> f (g x)" "AE x\<in>g ` S in lborel. 0 \<le> f x"
  shows "(\<integral>\<^sup>+x\<in> g ` S. ennreal (f x) \<partial>lborel) = (\<integral>\<^sup>+x\<in>S. ennreal (\<bar>g' x\<bar> * f (g x)) \<partial>lborel)"
  by(auto intro!: nn_integral_change_of_variables_real1 assms
      lebesgue_integrable_change_of_variables_real[THEN iffD2])

lemma nn_integral_change_of_variables_real2':
  fixes f :: "real \<Rightarrow> real" and g :: "real\<Rightarrow> real"
  assumes S[measurable]: "S \<in> sets borel"
    and f:"set_borel_measurable borel (g ` S) f"
    and g[measurable]:"g \<in> borel_measurable (restrict_space borel S)"
    and g'[measurable]:"g' \<in> borel_measurable (restrict_space borel S)"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and integrable:"set_integrable lborel S (\<lambda>x. \<bar>g' x\<bar> * f (g x))"
    and nonneg:"\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f (g x)"
  shows "(\<integral>\<^sup>+x\<in> g ` S. ennreal (f x) \<partial>lborel) = (\<integral>\<^sup>+x\<in>S. ennreal (\<bar>g' x\<bar> * f (g x)) \<partial>lborel)"
  by(auto intro!: nn_integral_change_of_variables_real2 assms)

subsection \<open>Integral of Power Functions\<close>
lemma set_integrable_inverse:
  fixes a b c :: real
  assumes a_pos:"0 < a"
  shows "set_integrable lborel {a..b} (\<lambda>x. c / x)"
  using a_pos
  by(cases "a \<le> b")
    (auto intro!: set_integrable_bounded[where K="(abs c) / a"] divide_mono
      simp: lborel_eq_real set_borel_measurable_def emeasure_interval_measure_Icc)

lemma set_integrable_inverse':
  fixes a b c :: real
  assumes "0 < a"
  shows "set_integrable lborel {a<..b} (\<lambda>x. c / x)"
  by(auto intro!: set_integrable_subset[OF set_integrable_inverse] assms)

corollary set_integral_inverse:
  fixes a b c :: real
  assumes a_pos:"0 < a"
    and a_le_b:"a \<le> b"
  shows "(\<integral>x\<in>{a<..b}. c / x \<partial>lborel) = c * (ln b - ln a)"
proof -
  have ln_im:"ln ` {a<..b} = {ln a<..ln b}"
    using assms
    by(intro image_mono_on_continuous_on_Ioc strict_mono_on_imp_inj_on
        monotone_onI ln_strict_mono continuous_on_ln)
      auto   
  have "(\<integral>x\<in>{a<..b}. c / x \<partial>lborel) = (\<integral>x\<in>{a<..b}. \<bar>1 / x\<bar> * c \<partial>lborel)"
    using assms by(auto intro!: Bochner_Integration.integral_cong
        simp: set_lebesgue_integral_def indicator_def)
  also have "... = (\<integral>x\<in>ln ` {a<..b}. c \<partial>lborel)"
    using a_pos a_le_b
    by(intro lebesgue_integral_change_of_variables_real2[symmetric]
        has_field_derivative_at_within[OF DERIV_ln_divide]
        strict_mono_on_imp_inj_on monotone_onI ln_strict_mono)
      (fastforce intro!: integrableI_bounded_set[where A="{a<..b}" and B="\<bar>c\<bar> / a"]
        divide_mono simp: set_borel_measurable_def set_integrable_def ln_im)+
  also have "... = c * (ln b - ln a)"
    by(simp add: interval_integral_Ioc[symmetric] ln_mono[OF a_le_b a_pos] ln_im)
  finally show ?thesis .
qed

lemma set_integrable_powr_Icc:
  fixes c :: real
  assumes c:"0 < c"
  shows "set_integrable lborel {c..d} (\<lambda>x. x powr a)"
proof(cases "c \<le> d")
  assume cd:"c \<le> d"
  thus "set_integrable lborel {c..d} (\<lambda>x. x powr a)"
    using c
    by(cases "a = - 1")
      (auto intro!: borel_integrable_atLeastAtMost isCont_divide continuous_powr
        simp del: times_divide_eq_left simp add: set_integrable_def mult.commute)
qed simp

lemma set_integral_powr_Icc:
  fixes c :: real
  assumes a:"- 1 \<noteq> a"
    and c:"0 < c"
    and cd:"c \<le> d"
  shows "(\<integral>x\<in>{c..d}. x powr a \<partial>lborel) = d powr (a + 1) / (a + 1) - c powr (a + 1) / (a + 1)"
proof -
  have "(\<integral>x\<in>{c..d}. x powr a \<partial>lborel) = (\<integral>x. x powr a * indicat_real {c..d} x \<partial>lborel)"
    by(simp add: set_lebesgue_integral_def mult.commute)
  also have "... = d powr (a + 1) / (a + 1) - c powr (a + 1) / (a + 1)"
  proof(rule integral_FTC_Icc_nonneg)
    fix x
    assume "x \<in> {c..d}"
    then show "((\<lambda>y. (y powr (a + 1)) / (a + 1)) has_real_derivative x powr a) (at x)"
      using has_real_derivative_powr[of x "a + 1"] c a
        DERIV_cmult[OF has_real_derivative_powr[of x "a + 1"],where c="1 / (a + 1)"]
      by auto
  qed(use cd in auto)
  finally show "(\<integral>x\<in>{c..d}. x powr a \<partial>lborel)
                 = d powr (a + 1) / (a + 1) - c powr (a + 1) / (a + 1)" .
qed

corollary set_integrable_powr_Ioc:
  fixes c :: real
  assumes c:"0 < c"
  shows "set_integrable lborel {c<..d} (\<lambda>x. x powr a)"
  by(auto intro!: set_integrable_subset[OF set_integrable_powr_Icc[OF c]])

corollary set_integral_powr_Ioc:
  fixes c :: real
  shows "a \<noteq> - 1 \<Longrightarrow> 0 < c \<Longrightarrow> c \<le> d \<Longrightarrow>
   (\<integral>x\<in>{c<..d}. x powr a \<partial>lborel) = d powr (a + 1) / (a + 1) - c powr (a + 1) / (a + 1)"
  by(auto intro!: set_integrable_subset[OF set_integrable_powr_Icc[of a c]]
      simp: interval_integral_Ioc[symmetric] interval_integral_Icc set_integral_powr_Icc)

lemma
  fixes c :: real
  assumes a:"- 1 < a"
  shows set_integrable_powr_from_0:"set_integrable lborel {0<..c} (\<lambda>x. x powr a)"
    and set_integral_powr_from_0:"0 \<le> c \<Longrightarrow>
   (\<integral>x\<in>{0<..c}. x powr a \<partial>lborel) = c powr (a + 1) / (a + 1)"
proof -
  have *:"set_integrable lborel {0<..c} (\<lambda>x. x powr a)"
         "(\<integral>x\<in>{0<..c}. x powr a \<partial>lborel) = c powr (a + 1) / (a + 1)" if c:"0 < c"
  proof -
    obtain N where N:"0 < N" "1 / real N < c"
      using c by (metis less_Suc_eq_0_disj nat_approx_posE)
    hence cn0: "\<And>n. 1 / real (n + N) < c"
      by (metis basic_trans_rules(21) inverse_of_nat_le le_add2 not_gr0)
    have cnle0:"\<And>n. 1 / real (n + N) > 0"
      using N by simp
    have dec:"decseq (\<lambda>n. 1 / real (n + N))"
      using N by (metis (mono_tags, lifting) add_le_mono1
                        antimonoI inverse_of_nat_le not_add_less2)
    have 1:"integrable lborel (\<lambda>x. indicator {1 / real (n + N)..c} x * x powr a)" for n
      using set_integrable_powr_Icc[of "1 / real (n + N)" c] N
      by(auto simp: set_integrable_def)
    have 2:"AE x in lborel. incseq (\<lambda>n. indicator {1 / real (n + N)..c} x * x powr a)"
      using decseq_SucD[OF dec]
      by(intro AE_I2 incseq_SucI mult_mono order.refl indicator_pos_le powr_ge_zero indicator_leI)
        (meson atLeastAtMost_iff order.trans)
    have 3:"AE x in lborel. (\<lambda>n. indicator {1 / real (n + N)..c} x * x powr a)
                              \<longlonglongrightarrow> indicator {0<..c} x *  x powr a"
    proof(intro AE_I2 tendsto_mult_right)
      fix x
      consider "0 < x" "x \<le> c" | "x \<le> 0" | "c < x"
        by linarith
      then show "(\<lambda>n. indicator {1 / real (n + N)..c} x) \<longlonglongrightarrow> indicator {0<..c} x"
      proof cases
        assume x:"0 < x" "x \<le> c"
        then obtain N' where "1 / real (N' + N) \<le> x"
          by (smt (verit) inverse_of_nat_le le_add1 less_Suc_eq nat_approx_posE not_gr0)
        hence "\<And>n. N' \<le> n \<Longrightarrow> 1 / real (n + N) \<le> x"
          using N
          by (metis add_mono_thms_linordered_semiring(3) inverse_of_nat_le not_add_less2
              order.trans)
        with x have "\<forall>\<^sub>F n in sequentially. indicator {1 / real (n + N)..c} x = 1"
         by(auto intro!: eventually_sequentiallyI[where c=N'] simp: indicator_def)
        thus ?thesis
          using x atLeastAtMost_iff greaterThanAtMost_iff tendsto_eventually by fastforce
      next
        assume x:"x \<le> 0"
        then have *:"indicator {1 / real (n + N)..c} x = 0" for n
          using cnle0[of n] c
          by (meson atLeastAtMost_iff indicator_eq_0_iff not_less order.strict_trans1)
        thus ?thesis
          using x unfolding * by force
      qed simp
    qed
    have 4:"(\<lambda>n. (\<integral>x. indicator {1 / real (n + N)..c} x * x powr a \<partial>lborel))
                  \<longlonglongrightarrow> c powr (a + 1) / (a + 1)"
    proof -
      have "(\<integral>x. indicator {1 / real (n + N)..c} x * x powr a \<partial>lborel)
             = c powr (a + 1) / (a + 1) - (1 / real (n + N)) powr (a + 1) / (a + 1)" for n
        using cn0 a cnle0
        by(subst set_integral_powr_Icc[symmetric])
          (auto simp: set_lebesgue_integral_def less_imp_le)
      moreover have "(\<lambda>n. c powr (a + 1) / (a + 1) - (1 / real (n + N)) powr (a + 1) / (a + 1))
                      \<longlonglongrightarrow> c powr (a + 1) / (a + 1)"
        by(rule LIM_zero_cancel)
          (use a in "auto simp: tendsto_minus_cancel_left[symmetric]
                      simp del: of_nat_add intro!: lim_const_over_n  tendsto_divide_zero
                             tendsto_zero_powrI LIMSEQ_ignore_initial_segment[where a=0]")
      ultimately show ?thesis
        by presburger
    qed
    show "set_integrable lborel {0<..c} (\<lambda>x. x powr a)"
      and "(\<integral>x\<in>{0<..c}. x powr a \<partial>lborel) = c powr (a + 1) / (a + 1)"
      using integral_monotone_convergence[OF 1 2 3 4]
        integrable_monotone_convergence[OF 1 2 3 4]
      unfolding set_integrable_def set_lebesgue_integral_def
      by fastforce+
  qed
  show "set_integrable lborel {0<..c} (\<lambda>x. x powr a)"
    by(cases "0 < c") (use * in auto)
  show "0 \<le> c \<Longrightarrow>
   (\<integral>x\<in>{0<..c}. x powr a \<partial>lborel) = c powr (a + 1) / (a + 1)"
    by(cases "0 < c") (use * in auto)
qed

lemma
  fixes c :: real
  assumes a:"a < - 1"
    and c:"0 < c"
  shows set_integrable_powr_inf:"set_integrable lborel {c<..} (\<lambda>x. x powr a)"
    and set_integral_powr_inf:"(\<integral>x\<in>{c<..}. x powr a \<partial>lborel) = - (c powr (a + 1) / (a + 1))"
proof -
  show "set_integrable lborel {c<..} (\<lambda>x. x powr a)"
    using a c
    by(intro interval_integral_inf_integrable[where G="- (c powr (a + 1) / (a + 1))"]
        set_integrable_powr_Ioc)
      (auto simp: set_integral_powr_Ioc[of a c] intro!: divide_nonneg_neg)
  have "((\<lambda>r. (\<integral>x\<in>{c<..r}. x powr a \<partial>lborel)) \<longlongrightarrow> (\<integral>x\<in>{c<..}. x powr a \<partial>lborel)) at_top"
    using a c
    by(intro interval_integral_inf[where G="- (c powr (a + 1) / (a + 1))"]
        set_integrable_powr_Ioc)
      (auto simp: set_integral_powr_Ioc[of a c] intro!: divide_nonneg_neg)
  moreover have "((\<lambda>r. (\<integral>x\<in>{c<..r}. x powr a \<partial>lborel))
                   \<longlongrightarrow> - (c powr (a + 1) / (a + 1))) at_top"
  proof -
    have "\<forall>\<^sub>F r in at_top. (\<integral>x\<in>{c<..r}. x powr a \<partial>lborel)
                          = r powr (a + 1) / (a + 1) - c powr (a + 1) / (a + 1)"
      unfolding eventually_at_top_linorder
      using a c by(auto simp add: set_integral_powr_Ioc intro!: exI[where x=c])
    moreover have "((\<lambda>r::real. r powr (a + 1) / (a + 1) - c powr (a + 1) / (a + 1))
                     \<longlongrightarrow> - (c powr (a + 1) / (a + 1))) at_top"
      using a
      by(intro LIM_zero_cancel[where l="- (c powr (a + 1) / (a + 1))"])
        (auto intro!: tendsto_divide_zero tendsto_neg_powr filterlim_ident)
    ultimately show ?thesis
      by(simp cong: tendsto_cong)
  qed
  ultimately show "(\<integral>x\<in>{c<..}. x powr a \<partial>lborel) = - (c powr (a + 1) / (a + 1))"
    using tendsto_unique trivial_limit_at_top_linorder by blast
qed

subsection \<open>Uniform Convergence\<close>
corollary uniform_limit_uminus_iff:
  fixes f :: "_ \<Rightarrow> _ :: real_normed_vector"
  shows "uniform_limit A (\<lambda>i x. - fi i x) (\<lambda>x. - f x) F
          \<longleftrightarrow> uniform_limit A fi f F"
  using uniform_limit_uminus by fastforce

lemma uniform_lim_mult_bdd1:
  fixes f :: "_ \<Rightarrow> _ :: real_normed_field"
  assumes ul:"uniform_limit A fi f F"
    and bdd:"bounded (g ` A)"
  shows "uniform_limit A (\<lambda>i x. g x * fi i x) (\<lambda>x. g x * f x) F"
  unfolding uniform_limit_iff
proof safe
  fix e :: real
  assume e:"0 < e"
  obtain K where K:"\<And>x. x \<in> A \<Longrightarrow> norm (g x) \<le> K" "0 < K"
    by (metis bdd bounded_pos image_eqI)
  hence eK:"0 < e / K"
    using e by simp
  show "\<forall>\<^sub>F i in F. \<forall>x\<in>A. dist (g x * fi i x) (g x * f x) < e"
    by(intro eventually_mono[OF uniform_limitD[OF ul eK]] ballI)
      (smt (verit, best) K(1) dist_mult_left e frac_le
        nonzero_mult_div_cancel_left norm_ge_zero zero_less_mult_iff)
qed

lemma uconvergence_on_bdd_times2:
  fixes f :: "_ \<Rightarrow> _ :: real_normed_field"
  assumes "uniform_limit A fi f F"
    and "bounded (g ` A)"
  shows "uniform_limit A (\<lambda>i x. fi i x * g x) (\<lambda>x. f x * g x) F"
  using uniform_lim_mult_bdd1[OF assms] by(simp add: mult.commute)

lemma uniform_limit_eventually_in:
  assumes lim: "uniform_limit A g g' F"
    and e:"0 < e"
    and d: "\<And>x y. x \<in> A \<Longrightarrow> dist (g' x) y < e \<Longrightarrow> y \<in> B"
  shows "\<forall>\<^sub>F t in F. \<forall>y\<in>A. g t y \<in> B"
  by(rule eventually_mono[OF uniform_limitD[OF lim e]])
    (use d in "simp add: Met_TC.commute")

lemma mono_on_UCT:
  fixes Ui :: "_ \<Rightarrow> real \<Rightarrow> real"
  assumes ab:"a \<le> b"
    and mono:"\<forall>\<^sub>F i in F. mono_on {a..b} (Ui i)" and monoU:"mono_on {a..b} U"
    and U:"continuous_on {a..b} U"
    and lim: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> ((\<lambda>i. Ui i x) \<longlongrightarrow> U x) F"
  shows "uniform_limit {a..b} Ui U F"
proof(intro uniform_limitI)
  fix e :: real
  assume e:"0 < e"
  hence e':"0 < e / 2"
    by simp
  then obtain d' where d': "d' > 0"
    "\<And>x y. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> a \<le> y \<Longrightarrow> y \<le> b
       \<Longrightarrow> \<bar>x - y\<bar> < d' \<Longrightarrow> \<bar>U x - U y\<bar> < e / 2"
    using compact_uniformly_continuous[OF U compact_interval[of a b]]
    unfolding uniformly_continuous_on_def
    by (metis atLeastAtMost_iff dist_real_def)
  define d where "d \<equiv> min d' (1 / 2)"
  have d_less:"d < 1" and d_pos:"0 < d"
    and  d:"\<And>x y. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> a \<le> y \<Longrightarrow> y \<le> b
                 \<Longrightarrow> \<bar>x - y\<bar> < d \<Longrightarrow> \<bar>U x - U y\<bar> < e / 2"
    using d' by(auto simp: d_def)
  have *:"{a..b} \<subseteq> (\<Union> ((\<lambda>x. {x - d / 4<..< x + d / 4}) ` {a..b}))"
    using d_pos by fastforce
  then obtain K where finK:"finite K" and K_sub:"K \<subseteq> {a..b}"
    and K: "{a..b} \<subseteq> (\<Union>x\<in>K. {x - d / 4<..< x + d / 4})"
    using compactE_image[OF compact_interval _ *] by force
  hence K': "(\<Union>x\<in>K. {x - d / 4<..< x + d / 4} \<inter> {a..b}) = {a..b}"
    (is "(\<Union>x\<in>K. ?A x) = {a..b}")
    by blast
  have K_ne:"K \<noteq> {}"
    using K ab by fastforce
  have "\<And>x. x \<in> K \<Longrightarrow> a \<le> max (x - d / 4) a" "\<And>x. x \<in> K \<Longrightarrow> max (x - d / 4) a \<le> b"
    "\<And>x. x \<in> K \<Longrightarrow> a \<le> (min (x + d / 4) b)" "\<And>x. x \<in> K \<Longrightarrow> (min (x + d / 4) b) \<le> b"
    using ab K_sub d_pos by auto
  hence "\<forall>x\<in>K. \<forall>\<^sub>F i in F. \<bar>Ui i (max (x - d / 4) a) - U (max (x - d / 4) a)\<bar> < e / 2"
    and "\<forall>x\<in>K. \<forall>\<^sub>F i in F. \<bar>Ui i (min (x + d / 4) b) - U (min (x + d / 4) b)\<bar> < e / 2"
    using e' lim
    unfolding tendsto_iff dist_norm real_norm_def by fast+
  hence "\<forall>\<^sub>F i in F. \<forall>x\<in>K. \<bar>Ui i (max (x - d / 4) a) - U (max (x - d / 4) a)\<bar> < e / 2"
    and "\<forall>\<^sub>F i in F. \<forall>x\<in>K. \<bar>Ui i (min (x + d / 4) b) - U (min (x + d / 4) b)\<bar> < e / 2"
    using finK by(auto simp: eventually_ball_finite)
  hence *:"\<forall>\<^sub>F i in F. \<forall>x\<in>K. \<bar>Ui i (max (x - d / 4) a) - U (max (x - d / 4) a)\<bar> < e / 2
                          \<and> \<bar>Ui i (min (x + d / 4) b) - U (min (x + d / 4) b)\<bar> < e / 2"
    using eventually_elim2 by fastforce
  show "\<forall>\<^sub>F i in F. \<forall>x\<in>{a..b}. dist (Ui i x) (U x) < e"
  proof(safe intro!: eventually_mono[where Q="\<lambda>i. \<forall>x\<in>{a..b}. dist (Ui i x) (U x) < e",
                                     OF eventually_conj[OF * mono]])
    fix i and x :: real
    assume i:"\<forall>y\<in>K. \<bar>Ui i (max (y - d / 4) a) - U (max (y - d / 4) a)\<bar> < e / 2
                  \<and> \<bar>Ui i (min (y + d / 4) b) - U (min (y + d / 4) b)\<bar> < e / 2"
      and x:"x \<in> {a..b}" and monoUi:"mono_on {a..b} (Ui i)"
    then obtain y where y:"y \<in> K" "x \<in> {y - d / 4<..< y + d / 4} \<inter> {a..b}"
      using K' by blast
    have "Ui i x - U x \<le> Ui i (min (y + d / 4) b) - U (max (y - d / 4) a)"
      using mono_onD[OF monoUi] y mono_onD[OF monoU]
      by(auto intro!: diff_mono)
    also have "... \<le> \<bar>Ui i (min (y + d / 4) b) - U (min (y + d / 4) b)\<bar>
                   + \<bar>U (min (y + d / 4) b) - U (max (y - d / 4) a)\<bar>"
      by simp
    also have "... < e / 2 + e / 2"
      using d[of "min (y + d / 4) b" "max (y - d / 4) a"] y i K_sub d_less d_pos
      by(intro add_strict_mono) auto
    also have "... = e"
      by simp
    finally have 1:"Ui i x - U x < e" .
    have "- e = - e / 2 - e / 2"
      by simp
    also have "... < - \<bar>Ui i (max (y - d / 4) a) - U (max (y - d / 4) a)\<bar>
                     - \<bar>U (max (y - d / 4) a) - U (min (y + d / 4) b)\<bar>"
      using y i K_sub d_less d_pos
      by(intro diff_strict_mono d) auto
    also have "... \<le> Ui i (max (y - d / 4) a) - U (min (y + d / 4) b)"
      by linarith
    also have "... \<le> Ui i x - U x"
      using mono_onD[OF monoUi] y mono_onD[OF monoU]
      by(auto intro!: diff_mono)
    finally have 2:"- e < Ui i x - U x" .
    show "dist (Ui i x) (U x) < e"
      using 1 2 by (simp add: dist_real_def)
  qed
qed

lemma mono_on_UCT_atLeast:
  fixes f :: "'a \<Rightarrow> real \<Rightarrow> real" and g :: "real \<Rightarrow> real" and F :: "'a filter"
  assumes mono: "\<forall>\<^sub>F i in F. mono_on {a..} (f i)"
    and bdd: "\<forall>\<^sub>F i in F. \<forall>x\<ge>a. f i x \<le> B"
    and gmono: "mono_on {a..} g"
    and gcont: "continuous_on {a..} g"
    and glim: "(g \<longlongrightarrow> B) at_top"
    and lim: "\<And>x. a \<le> x \<Longrightarrow> ((\<lambda>i. f i x) \<longlongrightarrow> g x) F"
  shows "uniform_limit {a..} f g F"
proof(safe intro!: uniform_limitI)
  fix e :: real
  assume e[arith]:"0 < e"
  have gB:"g x \<le> B" if x:"a \<le> x" for x
    using mono_onD[OF gmono] x
    by(auto intro!: tendsto_lowerbound[OF glim] eventually_at_top_linorderI[where c=x])
  obtain b' where b':"\<And>x. b' \<le> x \<Longrightarrow> \<bar>g x - B\<bar> < e / 2"
    using tendstoD[OF glim half_gt_zero[OF e]]
    unfolding dist_real_def eventually_at_top_linorder
    by blast
  define b where "b \<equiv> max b' a"
  have b:"\<And>x. b \<le> x \<Longrightarrow> B - g x < e / 2" and ab:"a \<le> b"
    using gB b' by(fastforce simp: b_def simp del: less_divide_eq_numeral1)+
  have "e / 2 - (B - g b) > 0"
    using b[OF order.refl] by simp
  from tendstoD[OF lim[OF ab] this]
  have "\<forall>\<^sub>F i in F. \<bar>f i b - g b\<bar> < e / 2 - (B - g b)"
    by(auto simp: dist_real_def)
  hence *:"\<forall>\<^sub>F i in F. B - f i b < e / 2"
    by eventually_elim argo
  have 1:"\<forall>\<^sub>F i in F. \<forall>x\<in>{b..}. dist (f i x) (g x) < e"
  proof(safe intro!: eventually_mono[OF eventually_conj[OF * eventually_conj[OF bdd mono]]])
    fix i x
    assume h:"B - f i b < e / 2"
      and mono:"mono_on {a..} (f i)"
      and bx:"b \<le> x" and bdd:"\<forall>y\<ge>a. f i y \<le> B"
    have "dist (f i x) (g x) \<le> \<bar>B - g x\<bar> + \<bar>B - f i x\<bar>"
      by(simp add: dist_real_def)
    also have "... = B - g x + (B - f i x)"
      using bdd bx gB ab by simp
    also have "... \<le> B - g x + (B - f i b)"
      using mono_onD[OF mono] ab bx by simp
    finally show "dist (f i x) (g x) < e"
      using b[OF bx] h by linarith
  qed
  have "uniform_limit {a..b} f g F"
    by(intro mono_on_UCT[OF ab eventually_mp[OF _ mono]
          mono_on_subset[OF gmono] continuous_on_subset[OF gcont] lim] eventuallyI)
      (auto simp: mono_on_subset)
  hence 2:"\<forall>\<^sub>F i in F. \<forall>x\<in>{a..b}. dist (f i x) (g x) < e"
    using uniform_limitD e by blast
  show "\<forall>\<^sub>F i in F. \<forall>x\<in>{a..}. dist (f i x) (g x) < e"
    using 1 2 by eventually_elim auto
qed

lemma antimono_on_UCT:
  fixes Ui :: "_ \<Rightarrow> real \<Rightarrow> real"
  assumes ab:"a \<le> b"
    and mono:"\<forall>\<^sub>F i in F. antimono_on {a..b} (Ui i)" and monoU:"antimono_on {a..b} U"
    and U:"continuous_on {a..b} U"
    and lim: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> ((\<lambda>i. Ui i x) \<longlongrightarrow> U x) F"
  shows "uniform_limit {a..b} Ui U F"
  using assms mono_on_UCT[where Ui="\<lambda>i x. - Ui i x" and U="\<lambda>x. - U x"]
  by(auto simp: antimono_on_iff_uminus_mono_on uniform_limit_uminus_iff
      tendsto_minus_cancel continuous_on_minus)

end