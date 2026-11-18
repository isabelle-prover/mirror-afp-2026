section \<open>A very special case of Green's theorem for a convex area\<close>

theory Green_Variant
  imports Wirtinger

begin

subsection \<open>Area under an arc.\<close>

locale Area =
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex" and u v S
  assumes uv: "u \<le> v"
    and Re_g_le: "Re (g u) \<le> Re (g v)"
    and acont_g: "absolutely_continuous_on {u..v} g"
    and gim: "g ` {u..v} \<subseteq> {z. Im z \<ge> 0}"
    and inj_g: "inj_on g {u..v}"
    and inj_Re: "inj_on Re (g ` {u..v})"
    and negS: "negligible S"
    and gder: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"

begin

lemma below_arclet:
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"  (is ?th1)
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"  (is ?th2)
proof -
  obtain h where h: "\<And>x. x \<in> {u..v} \<Longrightarrow> h (Re (g x)) = x"
    by (metis inj_g inj_Re comp_def comp_inj_on inv_into_f_f)
  define ax where "ax \<equiv> (\<lambda>t. Re (g t)) ` {u..v}"
  have cont_h: "continuous_on ax h"
    unfolding ax_def
    by (simp add: absolutely_continuous_on_imp_continuous acont_g continuous_on_Re continuous_on_inv h)
  show ?th1
  proof -
    have cont_g: "continuous_on {u..v} g"
      by (simp add: absolutely_continuous_on_imp_continuous acont_g)
    have gp_ai: "g' absolutely_integrable_on {u..v}"
      by (meson absolutely_integrable_absolutely_continuous_derivative acont_g gder
          has_vector_derivative_at_within negS)
    have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {u..v}"
      using Re_absolutely_integrable_on gp_ai by blast
    have Im_g_cont: "continuous_on {u..v} (\<lambda>t. Im (g t))"
      by (intro continuous_intros cont_g)
    have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {u..v})"
      by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
    have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {u..v})"
      using continuous_imp_measurable_on_sets_lebesgue[OF Im_g_cont] atLeastAtMost_borel lborelD
      by (metis sets_completionI_sets)
    show ?thesis
      using absolutely_integrable_bounded_measurable_product_real [OF Im_g_meas _ Im_g_bdd Re_gp_ai]
      by (simp add: mult.commute)
  qed
  have cont_g: "continuous_on {u..v} g"
    using acont_g absolutely_continuous_on_imp_continuous is_interval_cc by blast
  have cont_Reg: "continuous_on {u..v} (\<lambda>t. Re (g t))"
    by (intro continuous_intros cont_g)
  have inj_Reg: "inj_on (\<lambda>t. Re (g t)) {u..v}"
    using comp_inj_on[OF inj_g inj_Re] by (simp add: o_def)
  have *: "strict_mono_on {u..v} (\<lambda>t. Re (g t)) \<or> strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
    using injective_eq_monotone_map[OF is_interval_cc cont_Reg] inj_Reg by auto
  have ax: "ax = {Re (g u)..Re (g v)}"
  proof (rule antisym)
    show "ax \<subseteq> {Re (g u)..Re (g v)}"
    proof (cases "u = v")
      case False
      with * uv have mono: "strict_mono_on {u..v} (\<lambda>t. Re (g t))"
        by (smt (verit, ccfv_threshold) Re_g_le atLeastAtMost_iff monotone_onD)
      show ?thesis
        using mono by (auto simp: monotone_on_def ax_def less_eq_real_def)
    qed (auto simp: ax_def)
  next
    show "{Re (g u)..Re (g v)} \<subseteq> ax"
      using ivt_increasing_component_on_1[OF uv cont_g, of 1] by (force simp: ax_def)
  qed
  show ?th2
  proof -
    define f where "f \<equiv> (\<lambda>x. Im (g (h x)))"
    have h_range: "h ` ax \<subseteq> {u..v}"
      using h by (force simp: ax_def)
    have cont_f: "continuous_on ax f"
      using cont_g cont_h continuous_on_Im continuous_on_compose2 f_def h_range by blast
    have f_nonneg: "\<And>x. x \<in> ax \<Longrightarrow> f x \<ge> 0"
      unfolding f_def using gim h_range by blast
    have mono_Reg: "mono_on {u..v} (\<lambda>t. Re (g t))"
      using * Re_g_le atLeastAtMost_iff leD order_le_less uv 
      unfolding monotone_on_def by metis
    have acont_Reg: "absolutely_continuous_on {u..v} (\<lambda>t. Re (g t))"
      using absolutely_continuous_on_compose_linear[OF acont_g bounded_linear_Re[THEN bounded_linear.linear]]
      by (simp add: o_def)
    have deriv_Reg: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> ((\<lambda>t. Re (g t)) has_vector_derivative Re (g' t)) (at t)"
      using bounded_linear_Re[THEN bounded_linear.has_vector_derivative] gder by blast
    \<comment> \<open>Apply substitution: $\int_{Re(g\,u)}^{Re(g\,v)} f = \int_u^v Re(g') \cdot f(Re(g)) = \int_u^v Re(g') \cdot Im(g)$\<close>
    have subst: "((\<lambda>t. Re (g' t) * f (Re (g t))) has_integral (integral {Re (g u)..Re (g v)} f)) {u..v}"
      using has_integral_substitution_ac[OF uv Re_g_le acont_Reg negS deriv_Reg _]
      using mono_Reg cont_f ax negS by (force simp: monotone_on_def)
    \<comment> \<open>Since $f(Re(g\,t)) = Im(g\,t)$, the left-hand side simplifies\<close>
    have "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) = integral {Re (g u)..Re (g v)} f"
      using h has_integral_spike[OF negligible_empty _ subst] integral_unique
      by (fastforce simp: f_def)
    \<comment> \<open>Apply area-under-curve: measure of the subgraph $= \int f$\<close>
    also have "\<dots> = measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    proof -
      \<comment> \<open>First show the subgraph set equals the area under the graph of @{term f}\<close>
      have set_eq: "{z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w} =
                    {z. Re (g u) \<le> Re z \<and> Re z \<le> Re (g v) \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}" (is "?L=?R")
      proof (intro antisym subsetI)
        fix z assume "z \<in> ?L"
        then obtain w t where wt: "t \<in> {u..v}" "w = g t" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
          by auto
        have "Re z \<in> ax" unfolding ax_def using wt by force
        then show "z \<in> ?R"
          using f_def h wt ax by fastforce
      next
        fix z assume z: "z \<in> ?R"
        then have Rez: "Re z \<in> ax" using ax by auto
        then show "z \<in> ?L"
          unfolding ax_def using h z by (fastforce simp: f_def)
      qed
      \<comment> \<open>Then apply area-under-curve (Fubini/Cavalieri)\<close>
      show ?thesis unfolding set_eq
        using has_integral_area_under_curve[OF Re_g_le _ _] cont_f f_nonneg ax
        by (metis (no_types, lifting))
    qed
    finally show ?thesis .
  qed
qed

end (*Area*)

subsection \<open>Area above an arc.\<close>

lemma area_above_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and Re_g_ge: "Re (g v) \<le> Re (g u)"
    and ac_g: "absolutely_continuous_on {u..v} g"
    and gim: "g ` {u..v} \<subseteq> {z. Im z \<le> 0}"
    and injg: "inj_on g {u..v}"
    and injRe: "inj_on Re (g ` {u..v})"
    and "negligible S"
    and vder_g: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"  (is ?th1)
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"  (is ?th2)
proof -
  \<comment> \<open>Symmetry: define $h(t) = \overline{g(u+v-t)}$ and apply \<open>area_below_arclet\<close>\<close>
  define \<phi> where "\<phi> \<equiv> \<lambda>t. u + v - t"
  define h where "h \<equiv> cnj \<circ> g \<circ> \<phi>"
  define h' where "h' \<equiv> \<lambda>t. - cnj (g' (\<phi> t))"
  interpret Area h h' u v "\<phi> ` S"
  proof
    show "u \<le> v"
      by fact
    show "Re (h u) \<le> Re (h v)"
      by (simp add: \<phi>_def Re_g_ge h_def)
    show "absolutely_continuous_on {u..v} h"
      by (simp add: \<phi>_def absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect assms(3)
          h_def linear_cnj)
    show "h ` {u..v} \<subseteq> {z. 0 \<le> Im z}"
      using gim by (auto simp: h_def \<phi>_def image_subset_iff)
    show "inj_on h {u..v}"
      using injg by (fastforce simp: inj_on_def h_def \<phi>_def)
    show "inj_on Re (h ` {u..v})"
      using injRe by (fastforce simp: inj_on_def h_def \<phi>_def)
    have "\<phi> ` S = (+) (u + v) ` (uminus ` S)"
      unfolding \<phi>_def image_image by (simp add: algebra_simps)
    then show "negligible (\<phi> ` S)"
      by (simp add: \<open>negligible S\<close> linear_uminus negligible_linear_image negligible_translation)
    show "\<And>t. t \<in> {u..v} - (\<phi>`S) \<Longrightarrow> (h has_vector_derivative h' t) (at t)"
      unfolding has_vector_derivative_def h_def h'_def \<phi>_def 
      by (rule vder_g [unfolded has_vector_derivative_def] derivative_eq_intros | force)+
  qed
  have integrand_eq: "\<And>t. Re (h' t) * Im (h t) = Re (g' (\<phi> t)) * Im (g (\<phi> t))"
    unfolding h_def h'_def by (simp add: o_def cnj.sel)
  have integral_eq: "integral {u..v} (\<lambda>t. Re (g' (\<phi> t)) * Im (g (\<phi> t))) =
                     integral {u..v} (\<lambda>t. Re (g' t) * Im (g t))"
  proof -
    define f where "f \<equiv> \<lambda>t. Re (g' t) * Im (g t)"
    have comp_eq: "(f \<circ> (+) (u + v)) \<circ> uminus = f \<circ> \<phi>"
      unfolding \<phi>_def comp_def by (simp add: algebra_simps)
    have "(f \<circ> \<phi>) absolutely_integrable_on {u..v}"
      using below_arclet(1) f_def integrand_eq set_integrable_cong by fastforce
    then have "integral {u..v} (f \<circ> \<phi>) = integral (uminus ` {u..v}) (f \<circ> (+) (u + v))"
      by (subst integral_change_of_variables_linear[OF linear_uminus]) (auto simp: comp_eq)
    also have "\<dots> = integral {u..v} f"
      using integral_shift_Icc_real[of "-v" "-u" f "u+v"] by (simp add: algebra_simps)
    finally show ?thesis 
      by (simp add: f_def comp_def)
  qed
  show ?th1
  proof -
    have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {u..v}"
      using Re_absolutely_integrable_on has_vector_derivative_at_within assms
      by (metis vder_g absolutely_integrable_absolutely_continuous_derivative)
    have Im_g_cont: "continuous_on {u..v} (\<lambda>t. Im (g t))"
      by (simp add: absolutely_continuous_on_imp_continuous assms(3) continuous_on_Im)
    have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {u..v})"
      by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
    have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {u..v})"
      using Im_g_cont integrable_continuous_real integrable_imp_measurable by blast
    show ?thesis
      using absolutely_integrable_bounded_measurable_product_real [OF Im_g_meas _ Im_g_bdd Re_gp_ai]
      by (simp add: mult.commute)
  qed
  have \<phi>_image: "\<phi> ` {u..v} = {u..v}"
    using assms(1) unfolding \<phi>_def by (auto simp: image_iff)
  have h_image: "h ` {u..v} = cnj ` (g ` {u..v})"
    by (metis \<phi>_image h_def image_comp)
  define A where "A \<equiv> {z. \<exists>w \<in> h ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
  define B where "B \<equiv> {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
  have AB: "A = cnj ` B"
    unfolding A_def h_image B_def by (force simp: in_image_cnj_iff)
  have cont_g_uv: "continuous_on {u..v} g"
    using assms(3) absolutely_continuous_on_imp_continuous is_interval_cc by blast
  have "compact B"
  proof -
    \<comment> \<open>@{term B} is the continuous image of the compact set @{term "{u..v} \<times> {0..1}"}\<close>
    define \<psi> where "\<psi> \<equiv> \<lambda>(t,s). Complex (Re (g t)) ((1 - s) * Im (g t))"
    have cont_\<psi>: "continuous_on ({u..v} \<times> {0..1}) \<psi>"
      unfolding \<psi>_def split_def
      by (intro continuous_intros continuous_on_compose2[OF continuous_on_Re[OF cont_g_uv]]
          continuous_on_compose2[OF continuous_on_Im[OF cont_g_uv]] continuous_on_fst) auto
    have img: "\<psi> ` ({u..v} \<times> {0..1}) = B"
    proof (rule set_eqI)
      fix z :: complex
      show "z \<in> \<psi> ` ({u..v} \<times> {0..1}) \<longleftrightarrow> z \<in> B"
      proof
        assume "z \<in> \<psi> ` ({u..v} \<times> {0..1})"
        then obtain t s where ts: "t \<in> {u..v}" "s \<in> {0..1}" "z = Complex (Re (g t)) ((1 - s) * Im (g t))"
          unfolding \<psi>_def by auto
        have Im_le: "Im (g t) \<le> 0"
          using assms(4) ts(1) by (auto simp: image_subset_iff)
        have "g t \<in> g ` {u..v}" using ts(1) by auto
        moreover have "Im (g t) \<le> Im z"
          using ts Im_le mult_right_mono_neg by (simp add: mult_le_cancel_right1)
        moreover have "Im z \<le> 0"
          using ts Im_le mult_nonneg_nonpos[of "1-s" "Im (g t)"] by auto
        ultimately show "z \<in> B" unfolding B_def using ts by auto
      next
        assume "z \<in> B"
        then obtain w t where wt: "t \<in> {u..v}" "w = g t" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
          unfolding B_def by auto
        show "z \<in> \<psi> ` ({u..v} \<times> {0..1})"
        proof (cases "Im (g t) = 0")
          case True
          then show ?thesis 
            using wt by (force simp: image_iff \<psi>_def complex_eq_iff)
        next
          case False
          then have neg: "Im (g t) < 0"
            using wt by force
          define s where "s \<equiv> 1 - Im z / Im (g t)"
          have "0 \<le> Im z / Im (g t)" 
            using wt(5) neg by (simp add: field_simps)
          then have "s \<in> {0..1}" 
            using neg s_def wt(2,4) by force
          moreover have "z = \<psi> (t, s)" unfolding \<psi>_def s_def
            using wt(2,3) False by (simp add: complex_eq_iff field_simps)
          ultimately show ?thesis using wt(1) by auto
        qed
      qed
    qed
    then show ?thesis
      using img compact_continuous_image[OF cont_\<psi>] by (simp add: compact_Times)
  qed
  then have B_meas: "B \<in> lmeasurable" using lmeasurable_compact by blast    
  have measure_eq: "measure lebesgue {z. \<exists>w \<in> h ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w} =
                    measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    using AB measure_linear_image[OF linear_cnj B_meas] det_complex
    by (simp add: A_def B_def)
  show ?th2
    using below_arclet(2) integrand_eq integral_eq measure_eq by (simp add: o_def)
qed

subsection \<open>Lemmas for Green's theorem\<close>

definition Green_concl :: "(real \<Rightarrow> complex) \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool" where
  "Green_concl g g' \<equiv> (\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}
    \<and> \<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> = measure lebesgue (inside (path_image g))"

text \<open>At most two points on the frontier of a $2$-dimensional convex body can share the same
  inner product with a non-zero vector. Consequence: if three distinct points
  on the frontier have the same @{term Re} (or @{term Im}), the body must lie on one side.\<close>
lemma frontier_vertical_at_most_two:
  fixes S :: "complex set" and c :: real
  assumes "convex S" "compact S" "interior S \<noteq> {}"
    and sides: "\<exists>p \<in> S. Re p < c" "\<exists>q \<in> S. c < Re q"
    and xyz: "x \<in> frontier S" "y \<in> frontier S" "z \<in> frontier S"
      "Re x = c" "Re y = c" "Re z = c"
  shows "\<not> (x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z)"
proof -
  define T where "T \<equiv> {w :: complex. 1 \<bullet> w = c}"
  have aff_T: "affine T" unfolding T_def by (rule affine_hyperplane)
  have T_eq: "T = {w. Re w = c}" unfolding T_def by (simp add: complex_inner_1)
  have xT: "x \<in> T" "y \<in> T" "z \<in> T"
    using xyz unfolding T_eq by auto
  \<comment> \<open>The interior of @{term S} intersects @{term T}\<close>
  have int_T: "interior S \<inter> T \<noteq> {}"
  proof -
    have cl_int: "closure (interior S) = S"
      by (simp add: assms compact_imp_closed convex_closure_interior)
    \<comment> \<open>Find interior points on each side of $Re = c$\<close>
    obtain p where p: "p \<in> interior S" "Re p < c"
    proof -
      obtain p0 where p0: "p0 \<in> S" "Re p0 < c" using sides(1) by auto
      then obtain ps where ps: "\<forall>n. ps n \<in> interior S" "ps \<longlonglongrightarrow> p0"
        using cl_int closure_sequential by blast
      obtain n where "Re (ps n) < c" using eventually_sequentially
        by (metis LIMSEQ_le_const not_less p0(2) ps(2) tendsto_complex_iff)
      then show thesis using that ps(1) by auto
    qed
    obtain q where q: "q \<in> interior S" "c < Re q"
    proof -
      obtain q0 where q0: "q0 \<in> S" "c < Re q0" using sides(2) by auto
      then obtain qs where qs: "\<forall>n. qs n \<in> interior S" "qs \<longlonglongrightarrow> q0"
        using cl_int closure_sequential by blast
      then obtain n where "c < Re (qs n)" using eventually_sequentially
        by (metis LIMSEQ_le_const2 not_le q0(2) tendsto_complex_iff)
      then show thesis using that qs(1) by auto
    qed
    \<comment> \<open>IVT on the segment $\{p..q\} \subseteq \mathit{interior}\ S$\<close>
    have seg_sub: "closed_segment p q \<subseteq> interior S"
      using convex_interior \<open>convex S\<close> closed_segment_subset p(1) q(1) by metis
    obtain r where "r \<in> closed_segment p q" "1 \<bullet> r = c"
      using connected_ivt_hyperplane[OF connected_segment]
      by (smt (verit, del_insts) complex_inner_1 ends_in_segment p(2) q(2))
    then show ?thesis using seg_sub T_eq by auto
  qed
  \<comment> \<open>Apply \<open>convex_affine_rel_frontier_Int\<close>\<close>
  have rf_eq: "rel_frontier (S \<inter> T) = frontier S \<inter> T"
    using convex_affine_rel_frontier_Int[OF assms(1) aff_T int_T] .
  \<comment> \<open>@{term "S \<inter> T"} is a compact convex collinear set, hence a closed segment\<close>
  have ST_ne: "S \<inter> T \<noteq> {}"
    using int_T interior_subset by blast
  have ST_compact: "compact (S \<inter> T)"
    using T_def assms(2) closed_hyperplane by blast
  have ST_convex: "convex (S \<inter> T)"
    using assms(1) convex_Int aff_T affine_imp_convex by auto
  have "aff_dim T = int (DIM(complex) - 1)"
    unfolding T_def by (rule aff_dim_hyperplane) simp
  then have "aff_dim T = 1" by simp
  then have ST_collinear: "collinear (S \<inter> T)"
    by (metis collinear_aff_dim collinear_subset dual_order.refl inf_le2)
  obtain p q where pq: "S \<inter> T = closed_segment p q"
    using compact_convex_collinear_segment[OF ST_ne ST_compact ST_convex ST_collinear] by auto
  \<comment> \<open>The @{term rel_frontier} of a closed segment has at most two elements\<close>
  have rf_sub: "rel_frontier (S \<inter> T) \<subseteq> {p, q}"
  proof (cases "p = q")
    case True
    then show ?thesis unfolding pq by simp
  next
    case False then show ?thesis
      by (simp add: Diff_Diff_Int pq rel_frontier_def rel_interior_segment(1) segment(1))
  qed
  \<comment> \<open>@{term x}, @{term y}, @{term z} all lie in @{term "rel_frontier (S \<inter> T)"} $=$ @{term "frontier S \<inter> T"} $\subseteq \{p, q\}$\<close>
  have "x \<in> {p, q}" "y \<in> {p, q}" "z \<in> {p, q}"
    using xyz xT rf_eq rf_sub by auto
  then show ?thesis by auto
qed


locale Green =
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
    and U :: "real set"
    and a b :: "complex"
  assumes g: "simple_path g" "pathstart g = a" "pathfinish g = a"
    and b: "b \<in> path_image g" "Re a < Re b" "Im a = Im b"
    and dab: "dist a b = diameter (path_image g)"
    and conv: "convex (inside (path_image g))"
    and cont: "absolutely_continuous_on {0..1} g"
    and U: "negligible U"
    and vder: "\<And>t. t \<in> {0..1} - U \<Longrightarrow> (g has_vector_derivative g' t) (at t)"

begin

definition "gop \<equiv> cnj \<circ> reversepath g"
definition "gop' \<equiv> uminus \<circ> cnj \<circ> reversepath g'"

lemma cnj_rev: "Green gop gop' ((\<lambda>t. 1-t) ` U) (cnj a) (cnj b)"
proof
  show "simple_path gop"
    using g by (simp add: simple_path_def gop_def loop_free_reversepath loop_free_cnj)
  show "pathstart gop = cnj a"
    using g by (simp add: gop_def pathstart_compose)
  show "pathfinish gop = cnj a"
    using g by (simp add: gop_def pathfinish_compose)
  show "cnj b \<in> path_image gop"
    using b by (simp add: gop_def path_image_compose)
  show "Re (cnj a) < Re (cnj b)" "Im (cnj a) = Im (cnj b)"
    using b by auto
  show "dist (cnj a) (cnj b) = diameter (path_image gop)"
    by (simp add: gop_def dab diameter_image_cnj path_image_compose flip: dab)
  show "convex (inside (path_image gop))"
    unfolding gop_def
    by (metis conv convex_linear_vimage image_cnj_conv_vimage_cnj 
        inside_cnj_image linear_cnj path_image_compose path_image_reversepath)
  show "absolutely_continuous_on {0..1} gop"
    using cont unfolding gop_def
    by (simp add: absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect linear_cnj
        reversepath_o)
  have "negligible (uminus ` U)"
    by (simp add: U linear_uminus negligible_linear_image_eq)
  then have "negligible (((+)1) ` uminus ` U)"
    using negligible_translation by blast
  then show "negligible ((-) 1 ` U)"
    by (smt (verit, best) image_cong image_image)
next
  fix t :: real
  note vder [unfolded has_vector_derivative_def, derivative_intros]
  assume "t \<in> {0..1} - (-) 1 ` U"
  then have "0 \<le> t" "t \<le> 1" "1-t \<notin> U"
    by (auto simp: image_iff)
  then show "(gop has_vector_derivative gop' t) (at t)"
    unfolding gop_def gop'_def has_vector_derivative_def reversepath_o
    by - (rule derivative_eq_intros | simp add: o_def | assumption)+
qed

lemma rev: "Green (reversepath g) (uminus \<circ> reversepath g') ((\<lambda>t. 1-t) ` U) a b"
proof
  show "simple_path (reversepath g)"
    using g by (simp add: simple_path_def loop_free_reversepath)
  show "pathstart (reversepath g) = a"
    using g by (simp add: pathstart_compose)
  show "pathfinish (reversepath g) = a"
    using g by (simp add: pathfinish_compose)
  show "b \<in> path_image (reversepath g)"
    using b by (simp add: path_image_compose)
  show "Re a < Re b" "Im a = Im b"
    using b by auto
  show "dist a b = diameter (path_image (reversepath g))"
    by (simp add: gop_def dab path_image_compose flip: dab)
  show "convex (inside (path_image (reversepath g)))"
    by (simp add: gop_def conv)
  show "absolutely_continuous_on {0..1} (reversepath g)"
    using cont unfolding gop_def
    by (simp add: absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect linear_cnj
        reversepath_o)
  have "negligible (uminus ` U)"
    by (simp add: U linear_uminus negligible_linear_image_eq)
  then have "negligible (((+)1) ` uminus ` U)"
    using negligible_translation by blast
  then show "negligible ((-) 1 ` U)"
    by (smt (verit, best) image_cong image_image)
next
  fix t :: real
  note vder [unfolded has_vector_derivative_def, derivative_intros]
  assume "t \<in> {0..1} - (-) 1 ` U"
  then have "0 \<le> t" "t \<le> 1" "1-t \<notin> U"
    by (auto simp: image_iff)
  then show "((reversepath g) has_vector_derivative (uminus \<circ> reversepath g') t) (at t)"
    unfolding gop_def gop'_def has_vector_derivative_def reversepath_o
    by - (rule derivative_eq_intros | simp add: o_def | assumption)+
qed


lemma f_abs_int: "(\<lambda>s. Re (g' s) * Im (g s)) absolutely_integrable_on {0..1}"
proof -
  have cont_g: "continuous_on {0..1} g"
    using simple_path_imp_path[OF g(1)] by (simp add: path_def)
  have Im_g_cont: "continuous_on {0..1} (\<lambda>t. Im (g t))"
    by (intro continuous_intros cont_g)
  have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {0..1})"
    by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
  have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {0..1})"
    using continuous_imp_measurable_on_sets_lebesgue[OF Im_g_cont]
      atLeastAtMost_borel lborelD
    by (metis sets_completionI_sets)
  have gp_ai: "g' absolutely_integrable_on {0..1}"
    using absolutely_integrable_absolutely_continuous_derivative[OF cont U]
      vder has_vector_derivative_at_within by blast
  then show ?thesis
    using absolutely_integrable_bounded_measurable_product_real[OF Im_g_meas _ Im_g_bdd Re_absolutely_integrable_on]
    by (simp add: mult.commute)
qed

lemma arc_inj_on:
  assumes huv: "0 \<le> u" "v \<le> 1" "u < v" and hne: "u > 0 \<or> v < 1" 
  shows "inj_on g {u..v}"
proof (rule inj_onI)
  fix s1 s2 assume s1: "s1 \<in> {u..v}" and s2: "s2 \<in> {u..v}" and eq: "g s1 = g s2"
  then have s1_01: "s1 \<in> {0..1}" and s2_01: "s2 \<in> {0..1}" using huv by auto
  show "s1 = s2"
  proof (rule ccontr)
    assume neq: "s1 \<noteq> s2"
    from g(1) have lf: "loop_free g" by (simp add: simple_path_def)
    have "s1 = s2 \<or> s1 = 0 \<and> s2 = 1 \<or> s1 = 1 \<and> s2 = 0"
      using eq lf loop_free_def s1_01 s2_01 by blast
    with neq show False using s1 s2 huv hne by auto
  qed
qed

lemma arc_Re_inj_on:
  assumes "inj_on g {u..v}"
    and "\<And>s1 s2. \<lbrakk>s1 \<in> {u..v}; s2 \<in> {u..v}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
               \<Longrightarrow> Re (g u) = Re (g v)"
    and "Re (g u) \<noteq> Re (g v)"
  shows "inj_on Re (g ` {u..v})"
  using assms by (blast intro: inj_onI)

lemma Re_inj_upper_gen: 
  assumes s1t: "s1 \<in> {0..t}" and s2t: "s2 \<in> {0..t}"
    and Re_eq: "Re (g s1) = Re (g s2)" and neq: "s1 \<noteq> s2"
    and geq0: "g 0 = 0" "g 1 = 0"
    and ht: "0 < t" "t < 1" "g t = b"
  shows "(s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)"
proof (rule ccontr)
  assume not_endpts: "\<not> ((s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0))"
    \<comment> \<open>Define @{term "S \<equiv> convex hull (path_image g)"}. This is the right set for
       \<open>frontier_vertical_at_most_two\<close>.\<close>
  define S where "S \<equiv> convex hull (path_image g)"
  have S_convex: "convex S" unfolding S_def by (rule convex_convex_hull)
  have S_compact: "compact S" unfolding S_def
    using compact_simple_path_image[OF g(1)] compact_convex_hull by auto
  have frontier_S: "frontier S = path_image g"
    unfolding S_def using frontier_convex_hull_eq_path_image[OF g(1) _ conv] g(2,3) by auto
  have S_int_ne: "interior S \<noteq> {}"
    using Jordan_inside_outside[OF g(1)] g
    by (metis Diff_empty S_convex convex_closure frontier_S frontier_def inside_convex)
      \<comment> \<open>Step 2: $g\,s_1 \neq g\,s_2$ (from injectivity of @{term g} on $\{0..t\}$, which is a proper sub-arc).\<close>
  have inj_sub: "inj_on g {0..t}"
    using arc_inj_on[of 0 t] ht by auto
  have g_neq: "g s1 \<noteq> g s2"
    by (meson neq inj_on_def inj_sub s1t s2t)
    \<comment> \<open>Step 3: Both $g\,s_1$ and $g\,s_2$ are on @{term "frontier S"} $=$ @{term "path_image g"}.\<close>
  have s1_01: "s1 \<in> {0..1}" using s1t ht(2) by auto
  have s2_01: "s2 \<in> {0..1}" using s2t ht(2) by auto
  have gs1_frontier: "g s1 \<in> frontier S"
    using frontier_S s1_01 by (auto simp: path_image_def)
  have gs2_frontier: "g s2 \<in> frontier S"
    using frontier_S s2_01 by (auto simp: path_image_def)
      \<comment> \<open>Find a third distinct point on @{term "frontier S"} with the same real part.
       Key insight: one of $g(0)=0$ or $g(t)=b$ has a \emph{different} parameter from $s_1$ and $s_2$,
       and since @{term g} is injective on $\{0..t\}$, it gives a distinct point.\<close>
  define c where "c \<equiv> Re (g s1)"
    \<comment> \<open>Show $c \in \{0, Re\,b\}$ forces $s_1$ or $s_2$ to an endpoint, contradicting \<open>not_endpts\<close>.\<close>
  have c_strict: "0 < c \<and> c < Re b"
  proof -
    have a0: "a = 0" using geq0(1) g(2) by (simp add: pathstart_def)
    have Imb: "Im b = 0" using b(3) a0 by simp
    have Reb: "Re b > 0" using b(2) a0 by simp
    have bdd: "bounded (path_image g)"
      using compact_simple_path_image[OF g(1)] compact_imp_bounded by blast
    have gs1_pi: "g s1 \<in> path_image g" and gs2_pi: "g s2 \<in> path_image g" 
      using s1_01 s2_01 by (auto simp: path_image_def)
    have g0_pi: "0 \<in> path_image g" using geq0(1) by (metis pathstart_def pathstart_in_path_image)
    have diam_eq: "dist 0 b = diameter (path_image g)" using dab a0 by simp
    have dist_0b: "dist 0 b = Re b"
      using Imb Reb cmod_eq_Re by auto
    \<comment> \<open>Every point on the curve is within distance $Re\,b$ of both $0$ and $b$\<close>
    have d1: "dist (g s1) b \<le> Re b"
      using diameter_bounded_bound[OF bdd gs1_pi b(1)] diam_eq dist_0b by simp
    have d2: "dist 0 (g s1) \<le> Re b"
      using diameter_bounded_bound[OF bdd g0_pi gs1_pi] diam_eq dist_0b by simp
    \<comment> \<open>Helper: from $\mathit{cmod}\ z \le Re\,b$, derive $(Re\,z)^2 + (Im\,z)^2 \le (Re\,b)^2$\<close>
    have cmod_sq: "(Re z)\<^sup>2 + (Im z)\<^sup>2 \<le> (Re b)\<^sup>2" if "cmod z \<le> Re b" for z
      by (metis cmod_power2 norm_ge_zero power_mono that)
    \<comment> \<open>Helper: from $\mathit{cmod}\,(z - b) \le Re\,b$, derive $(Re\,z - Re\,b)^2 + (Im\,z)^2 \le (Re\,b)^2$\<close>
    have cmod_sq_b: "(Re z - Re b)\<^sup>2 + (Im z)\<^sup>2 \<le> (Re b)\<^sup>2" if "cmod (z - b) \<le> Re b" for z
      using Imb cmod_sq that by force
    \<comment> \<open>Helper: injectivity gives $s = 0$ from $g\,s = 0$, and $s = t$ from $g\,s = b$\<close>
    have eq_0: "s = 0" if "g s = 0" "s \<in> {0..t}" for s
      using geq0(1) inj_onD inj_sub that by fastforce
    have eq_t: "s = t" if "g s = b" "s \<in> {0..t}" for s
      using ht(3) inj_on_contraD inj_sub that by fastforce
    \<comment> \<open>Case $c = 0$: $Re(g\,s_1) = 0$, and $\mathit{dist}\,(g\,s_1)\,b \le Re\,b$ forces $Im(g\,s_1) = 0$, so $g\,s_1 = 0$\<close>
    have "c \<noteq> 0"
    proof
      assume "c = 0"
      have "(Re (g s1) - Re b)\<^sup>2 + (Im (g s1))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq_b d1 by (simp add: dist_norm)
      then have "g s1 = 0" using \<open>c = 0\<close> by (auto simp: c_def complex_eq_iff)
      then have "s1 = 0" using eq_0 s1t by simp
      moreover have "Re (g s2) = 0" using Re_eq \<open>c = 0\<close> c_def by simp
      then have "(Re (g s2) - Re b)\<^sup>2 + (Im (g s2))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq_b[of "g s2"] diameter_bounded_bound[OF bdd gs2_pi b(1)]
          diam_eq dist_0b by (simp add: dist_norm)
      then have "g s2 = 0" using \<open>Re (g s2) = 0\<close> by (auto simp: complex_eq_iff)
      then have "s2 = 0" using eq_0 s2t by simp
      ultimately show False using neq by simp
    qed
    \<comment> \<open>Case $c = Re\,b$: $\mathit{dist}\,0\,(g\,s_1) \le Re\,b$ forces $Im(g\,s_1) = 0$, so $g\,s_1 = b$\<close>
    moreover have "c \<noteq> Re b"
    proof
      assume c: "c = Re b"
      have "(Re (g s1))\<^sup>2 + (Im (g s1))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq d2 by (simp add: dist_norm)
      then have "g s1 = b" using c Imb by (auto simp: c_def complex_eq_iff)
      then have "s1 = t" using eq_t s1t by simp
      moreover have "Re (g s2) = Re b" using Re_eq \<open>c = Re b\<close> c_def by simp
      then have "(Re (g s2))\<^sup>2 + (Im (g s2))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq[of "g s2"] diameter_bounded_bound[OF bdd g0_pi gs2_pi]
          diam_eq dist_0b by (simp add: dist_norm)
      then have "g s2 = b" using \<open>Re (g s2) = Re b\<close> Imb by (simp add: complex.expand)
      then have "s2 = t" using eq_t s2t by simp
      ultimately show False using neq by simp
    qed
    \<comment> \<open>$c$ is bounded: $0 \le c \le Re\,b$ from the diameter bound\<close>
    moreover have "0 \<le> c"
      using abs_Re_le_cmod[of "g s1 - b"] d1 c_def by (simp add: dist_norm)
    moreover have "c \<le> Re b"
      by (smt (verit) c_def complex_Re_le_cmod d2 dist_0_norm)
    ultimately show ?thesis by linarith
  qed
      \<comment> \<open>By the IVT on $\{t..1\}$, find $s_3$ with $Re(g\,s_3) = c$.\<close>
  have cont_Re_g: "continuous_on {t..1} (Re \<circ> g)"
    using absolutely_continuous_on_imp_continuous assms(2) cont continuous_on_Re
      continuous_on_eq continuous_on_subset by fastforce
  obtain s3 where s3: "s3 \<in> {t..1}" "Re (g s3) = c"
  proof -
    have "Re (g t) \<in> (Re \<circ> g) ` {t..1}" using ht by (auto simp: image_def)
    then have Regt_in: "Re b \<in> (Re \<circ> g) ` {t..1}" using ht(3) by simp
    have "Re (g 1) \<in> (Re \<circ> g) ` {t..1}" using ht(2) by (auto simp: image_def)
    then have Re0_in: "0 \<in> (Re \<circ> g) ` {t..1}" using geq0 by simp
    have "is_interval ((Re \<circ> g) ` {t..1})"
      using connected_Icc connected_continuous_image cont_Re_g is_interval_connected_1 by blast
    then have "c \<in> (Re \<circ> g) ` {t..1}"
      using  Regt_in Re0_in c_strict by (auto simp: is_interval_1)
    then show ?thesis using that by (auto simp: image_def)
  qed
    \<comment> \<open>$g\,s_3$ is on @{term "frontier S"} and distinct from $g\,s_1$ and $g\,s_2$.\<close>
  have s3_01: "s3 \<in> {0..1}" using s3(1) ht(1) by auto
  have loopfr_g: "loop_free g" using g by (simp add: simple_path_def)
  have gs3_frontier: "g s3 \<in> frontier S"
    using frontier_S s3_01 by (auto simp: path_image_def)
  have gs3_ne_gs1: "g s3 \<noteq> g s1"
  proof
    assume eq: "g s3 = g s1"
    with loopfr_g have "s3 = s1 \<or> s3 = 0 \<and> s1 = 1 \<or> s3 = 1 \<and> s1 = 0"
      using eq loop_free_def s1_01 s3_01 by blast
    then show False
      using assms(1) c_def c_strict eq geq0(2) ht(3) s3(1) by auto
  qed
  have gs3_ne_gs2: "g s3 \<noteq> g s2"
  proof
    assume eq: "g s3 = g s2"
    with loopfr_g have "s3 = s2 \<or> s3 = 0 \<and> s2 = 1 \<or> s3 = 1 \<and> s2 = 0"
      using eq loop_free_def s2_01 s3_01 by blast
    then show False
      using assms(2) c_strict geq0(2) ht(3) s3(1,2) by fastforce
  qed
    \<comment> \<open>The ``sides'' condition for \<open>frontier_vertical_at_most_two\<close>.\<close>
  have side_left: "\<exists>p \<in> S. Re p < c"
    by (metis S_def assms(5) c_strict hull_inc pathstart_def pathstart_in_path_image
        zero_complex.sel(1))
  have side_right: "\<exists>q \<in> S. c < Re q"
    by (metis S_def b(1) c_strict hull_inc)
    \<comment> \<open>Apply \<open>frontier_vertical_at_most_two\<close> for the contradiction.\<close>
  have three_distinct: "g s1 \<noteq> g s2 \<and> g s1 \<noteq> g s3 \<and> g s2 \<noteq> g s3"
    using g_neq gs3_ne_gs1 gs3_ne_gs2 by auto
  have Re_all_c: "Re (g s1) = c" "Re (g s2) = c" "Re (g s3) = c"
    unfolding c_def using Re_eq s3(2) c_def by auto
  have "\<not> (g s1 \<noteq> g s2 \<and> g s1 \<noteq> g s3 \<and> g s2 \<noteq> g s3)"
    using frontier_vertical_at_most_two[OF S_convex S_compact S_int_ne side_left side_right
        gs1_frontier gs2_frontier gs3_frontier Re_all_c] .
  then show False using three_distinct by auto
qed

lemma not_all_above:
  assumes Reb: "Re b > 0"
  assumes "a = 0"
  assumes real_on_curve: "\<And>z. z \<in> path_image g \<Longrightarrow> Im z = 0 \<Longrightarrow> z = 0 \<or> z = b"
  shows "\<not> (path_image g \<subseteq> {z. 0 \<le> Im z})"
proof
  assume "path_image g \<subseteq> {z. 0 \<le> Im z}"
  then have "convex hull (path_image g) \<subseteq> {z. 0 \<le> Im z}"
    by (intro hull_minimal convex_halfspace_Im_ge)
  then have "inside (path_image g) \<subseteq> {z. (0::real) \<le> \<i> \<bullet> z}"
    using closure_subset conv convex_hull_eq_closure_inside g by auto
  then have "inside (path_image g) \<subseteq> interior {z. (0::real) \<le> \<i> \<bullet> z}"
    using interior_maximal open_inside Jordan_inside_outside g by blast
  also have "\<dots> = {z. 0 < \<i> \<bullet> z}"
    by (rule interior_halfspace_ge) simp
  finally have *: "inside (path_image g) \<subseteq> {z. 0 < Im z}"
    by simp
  have seg_infinite: "\<not> finite (open_segment a b)"
    using Reb assms by force
  have seg_Im0: "open_segment a b \<subseteq> {z. Im z = 0}"
    using assms b by (auto simp: in_segment complex_eq_iff)
  then have seg_in_closure: "open_segment a b \<subseteq> closure (inside (path_image g))"
    by (metis b(1) conv convex_contains_open_segment convex_convex_hull convex_hull_eq_closure_inside
        g hull_inc pathfinish_in_path_image)
  have "open_segment a b \<subseteq> {z \<in> path_image g. Im z = 0}"
    using * Jordan_inside_outside[of g] frontier_def g interior_open seg_Im0 seg_in_closure
    by fastforce
  also have "\<dots> \<subseteq> {0, b}"
    using real_on_curve by blast
  finally show False using seg_infinite finite_subset by blast
qed

interpretation CR: Green gop gop' "(\<lambda>t. 1-t) ` U" "cnj a" "cnj b"
  by (rule cnj_rev)

lemma Green_area_zero_A:
  assumes "a = 0" 
    and t: "0 < t" "t < 1"
    and hgt: "g t = b"
    and above: "g ` {0..t} \<subseteq> {z. 0 \<le> Im z}"
    and below: "g ` {t..1} \<subseteq> {z. Im z \<le> 0}"
  shows "Green_concl g g'"
proof -
  \<comment> \<open>Common facts used by both \<open>split_case\<close> and \<open>split_case'\<close>\<close>
  have g0: "g 0 = 0" using assms g(2) by (simp add: pathstart_def)
  have g1: "g 1 = 0" using assms g(3) by (simp add: pathfinish_def)
  have Reb: "Re b > 0" and Imb: "Im b = 0" using b assms by auto
    \<comment> \<open>Re-injectivity: on each arc, @{term "Re \<circ> g"} is injective (except at endpoints).
       Otherwise \<open>frontier_vertical_at_most_two\<close> gives a contradiction via three points
       on $\mathit{frontier}\,(\mathit{closure}\,(\mathit{inside}))$ with the same real part.\<close>
  have Re_inj_upper: "\<lbrakk>s1 \<in> {0..t}; s2 \<in> {0..t}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)" for s1 s2
    using Re_inj_upper_gen g0 g1 using hgt t by presburger
  have Re_inj_lower: "\<lbrakk>s1 \<in> {t..1}; s2 \<in> {t..1}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = t \<and> s2 = 1) \<or> (s1 = 1 \<and> s2 = t)" for s1 s2
    using CR.Re_inj_upper_gen[of "1-s1" "1-t" "1-s2"] hgt t using g g0 g1 assms
    by (auto simp: gop_def reversepath_def)
      \<comment> \<open>Step 0: absolute integrability (needed for integral splitting)\<close>
  define f where "f \<equiv> \<lambda>s. Re (g' s) * Im (g s)"
  have f_int: "f integrable_on {0..1}"
    using set_lebesgue_integral_eq_integral(1)[OF f_abs_int] f_def by argo
  have split_int: "integral {0..1} f = integral {0..t} f + integral {t..1} f"
    using Henstock_Kurzweil_Integration.integral_combine[of 0 t 1 f] t f_int by auto
      \<comment> \<open>Upper arc integral $\ge 0$.
       By the change of variables $x = Re(g(s))$ and Re-injectivity, the integral
       $\int_0^t Re(g') \cdot Im(g)\,ds = \int_0^{Re\,b} f_{\mathit{upper}}(x)\,dx \ge 0$
       since $f_{\mathit{upper}} = Im \circ g \circ Re^{-1} \ge 0$ on the upper arc.\<close>
  interpret A0t: Area g g' 0 t U
  proof
    show "Re (g 0) \<le> Re (g t)" 
      using g0 hgt Reb by simp
    show "absolutely_continuous_on {0..t} g"
      using absolutely_continuous_on_subset[OF cont] t by auto
    show "inj_on g {0..t}"
      using arc_inj_on t less_eq_real_def by presburger
    then show "inj_on Re (g ` {0..t})"
      using Reb Re_inj_upper g0 t
      by (intro arc_Re_inj_on; fastforce simp: assms b(2))
  qed (use above U vder t in auto)
  have upper_int: "integral {0..t} f \<ge> 0"
    unfolding f_def using A0t.below_arclet(2) by auto
    \<comment> \<open>Lower arc integral $\ge 0$ as well.\<close>
  have Re_le': "Re (g 1) \<le> Re (g t)" using g1 hgt Reb by simp
  have ac_sub': "absolutely_continuous_on {t..1} g"
    using absolutely_continuous_on_subset[OF cont] t by auto
  have inj_g_lower: "inj_on g {t..1}"
    using arc_inj_on t(2) less_eq_real_def t by presburger
  then have inj_Re_lower: "inj_on Re (g ` {t..1})"
    using Reb Re_inj_lower g1 t
    by (intro arc_Re_inj_on; fastforce simp: assms b(2))
  have lower_int: "integral {t..1} f \<ge> 0"
    unfolding f_def
    using t vder area_above_arclet(2)[OF _ Re_le' ac_sub' below inj_g_lower inj_Re_lower U]
    by auto
    \<comment> \<open>Total integral $=$ area of the inside.
       The inside decomposes as the region between the two arcs:
       $\mathit{inside}\,(\mathit{path\_image}\ g) = \{z \mid Re\,z \in (0, Re\,b) \wedge f_{\mathit{lower}}(Re\,z) < Im\,z < f_{\mathit{upper}}(Re\,z)\}$.
       By Fubini, its area $= \int_0^{Re\,b} (f_{\mathit{upper}}(x) - f_{\mathit{lower}}(x))\,dx$,
       and by the change-of-variables computations above, this equals
       @{term "integral {0..t} f + integral {t..1} f"} $=$ @{term "integral {0..1} f"}.\<close>
  have area_decomp: "measure lebesgue (inside (path_image g)) = integral {0..t} f + integral {t..1} f"
  proof -
    \<comment> \<open>Re-derive the integral-equals-measure identities (proved locally in \<open>upper_int\<close>/\<open>lower_int\<close>)\<close>
    have Re_le: "Re (g 0) \<le> Re (g t)" and Re_le': "Re (g 1) \<le> Re (g t)" 
      using g0 g1 hgt Reb by auto
        \<comment> \<open>The integral-equals-measure identities\<close>
    define Au where "Au \<equiv> {z. \<exists>w \<in> g ` {0..t}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    define Al where "Al \<equiv> {z. \<exists>w \<in> g ` {t..1}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    have int_upper: "integral {0..t} f = measure lebesgue Au"
      using A0t.below_arclet(2) unfolding f_def Au_def by auto
    have int_lower: "integral {t..1} f = measure lebesgue Al"
      using t vder area_above_arclet(2)[OF _ Re_le' ac_sub' below inj_g_lower inj_Re_lower U]
      unfolding f_def Al_def by auto
        \<comment> \<open>Step A: @{term Au} and @{term Al} are measurable (compact, hence @{term lmeasurable})\<close>
    have cont_g_upper: "continuous_on {0..t} g"
      by (simp add: absolutely_continuous_on_imp_continuous A0t.acont_g)
    define \<phi> where "\<phi> \<equiv> \<lambda>(s,r). Complex (Re (g s)) (r * Im (g s))"
    have cont_\<phi>: "continuous_on ({0..t} \<times> {0..1}) \<phi>"
      unfolding \<phi>_def split_def
      by (intro continuous_intros continuous_on_compose2[OF cont_g_upper] continuous_on_fst) auto
    have img: "\<phi> ` ({0..t} \<times> {0..1}) = Au"
    proof (rule set_eqI)
      fix z 
      show "z \<in> \<phi> ` ({0..t} \<times> {0..1}) \<longleftrightarrow> z \<in> Au"
      proof
        assume "z \<in> \<phi> ` ({0..t} \<times> {0..1})"
        then obtain s r where sr: "s \<in> {0..t}" "r \<in> {0..1}" "z = Complex (Re (g s)) (r * Im (g s))"
          unfolding \<phi>_def by auto
        have Im_ge: "Im (g s) \<ge> 0"
          using subsetD[OF above imageI[OF sr(1)]] by simp
        have "g s \<in> g ` {0..t}" using sr(1) by auto
        moreover have "Im z \<le> Im (g s)" 
          using sr Im_ge by (auto simp: mult_left_le_one_le)
        ultimately show "z \<in> Au" using sr Im_ge unfolding Au_def by auto
      next
        assume "z \<in> Au"
        then obtain w where w: "w \<in> g ` {0..t}" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
          unfolding Au_def by auto
        then obtain s where s: "s \<in> {0..t}" "w = g s" by auto
        show "z \<in> \<phi> ` ({0..t} \<times> {0..1})"
        proof (cases "Im w = 0")
          case True 
          then have "z = \<phi> (s, 0)" unfolding \<phi>_def using w s(2) by (simp add: complex_eq_iff)
          then show ?thesis using s(1) by auto
        next
          case False
          define r where "r \<equiv> Im z / Im w"
          have "Im w > 0" using False w(3,4) by linarith
          moreover have "z = \<phi> (s, r)"
            unfolding \<phi>_def r_def using False w s(2) by (simp add: field_simps complex_eq_iff)
          ultimately show ?thesis using w s(1) by (auto simp: r_def)
        qed
      qed
    qed
    have Au_meas: "Au \<in> lmeasurable"
      using img compact_continuous_image[OF cont_\<phi>] lmeasurable_compact by (metis compact_Icc compact_Times)
    have cont_g_lower: "continuous_on {t..1} g"
      using absolutely_continuous_on_imp_continuous[OF ac_sub'] is_interval_cc by blast
    define \<psi> where "\<psi> \<equiv> \<lambda>(s::real, r::real). Complex (Re (g s)) (r * Im (g s))"
    have cont_\<psi>: "continuous_on ({t..1} \<times> {0..1}) \<psi>"
      unfolding \<psi>_def split_def
      by (intro continuous_intros continuous_on_compose2[OF cont_g_lower] continuous_on_fst) auto
    have img: "\<psi> ` ({t..1} \<times> {0..1}) = Al"
    proof (rule set_eqI)
      fix z :: complex
      show "z \<in> \<psi> ` ({t..1} \<times> {0..1}) \<longleftrightarrow> z \<in> Al"
      proof
        assume "z \<in> \<psi> ` ({t..1} \<times> {0..1})"
        then obtain s r where sr: "s \<in> {t..1}" "r \<in> {0..1}" "z = Complex (Re (g s)) (r * Im (g s))"
          unfolding \<psi>_def by auto
        have Im_le: "Im (g s) \<le> 0"
          using subsetD[OF below imageI[OF sr(1)]] by simp
        then have "Im (g s) \<le> Im z"
          using less_eq_real_def sr by fastforce
        moreover have "Im z \<le> 0"
          using sr Im_le mult_nonneg_nonpos[of r "Im (g s)"] by simp
        ultimately show "z \<in> Al" 
          unfolding Al_def using sr by auto
      next
        assume "z \<in> Al"
        then obtain w where w: "w \<in> g ` {t..1}" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
          unfolding Al_def by auto
        then obtain s where s: "s \<in> {t..1}" "w = g s" by auto
        show "z \<in> \<psi> ` ({t..1} \<times> {0..1})"
        proof (cases "Im w = 0")
          case True
          then have "z = \<psi> (s, 0)" unfolding \<psi>_def using w s(2) by (simp add: complex_eq_iff)
          then show ?thesis using s(1) by auto
        next
          case False
          define r where "r \<equiv> Im z / Im w"
          have "r \<in> {0..1}" unfolding r_def using w
            using False by (auto simp: field_simps)
          moreover have "z = \<psi> (s, r)"
            unfolding \<psi>_def r_def using False w(2) s(2) by (simp add: complex_eq_iff)
          ultimately show ?thesis using s(1) by auto
        qed
      qed
    qed
    have "compact ({t..1} \<times> {0..1::real})" by (intro compact_Times compact_Icc)
    then have Al_meas: "Al \<in> lmeasurable" \<comment> \<open>duality\<close>
      using img compact_continuous_image[OF cont_\<psi>] lmeasurable_compact by blast

    have ch_eq: "convex hull (path_image g) = closure (inside (path_image g))"
      using convex_hull_eq_closure_inside[OF g(1) _ conv] g(2,3) by auto
    have zero_in_ch: "0 \<in> convex hull (path_image g)"
      using hull_subset[of "path_image g" convex] g0
      by (auto simp: path_image_def intro!: imageI[of 0])
    have b_in_ch: "b \<in> convex hull (path_image g)"
      using hull_subset[of "path_image g" convex] b(1) by auto
    have bdd_pi: "bounded (path_image g)"
      using compact_simple_path_image[OF g(1)] compact_imp_bounded by blast
        \<comment> \<open>Key fact: every point on the path has $Re \in [0, Re\,b]$\<close>
    have zero_in_pi: "(0::complex) \<in> path_image g"
      using g0 by (auto simp: path_image_def intro!: imageI[of 0])
    have Re_bounds: "0 \<le> Re w \<and> Re w \<le> Re b" if "w \<in> path_image g" for w
    proof -
      have "diameter (path_image g) = dist 0 b" using dab g0 g1 assms by simp
      then have diam_eq: "diameter (path_image g) = Re b"
        using Imb Re_le cmod_eq_Re g0 hgt by auto
      have "cmod w \<le> Re b" 
        using diameter_bounded_bound[OF bdd_pi that zero_in_pi] diam_eq by (simp add: dist_norm)
      moreover have "cmod (w - b) \<le> Re b" 
        using diameter_bounded_bound[OF bdd_pi that b(1)] diam_eq by (simp add: dist_norm)
      ultimately show ?thesis using abs_Re_le_cmod[of w] abs_Re_le_cmod[of "w - b"] by auto
    qed
      \<comment> \<open>Sublemma: @{term "Complex (Re w) 0 \<in> closed_segment 0 b"} for any @{term w} on the path\<close>
    have real_point_in_seg: "Complex (Re w) 0 \<in> closed_segment 0 b"
      if "w \<in> path_image g" for w
    proof -
      have bds: "0 \<le> Re w" "Re w \<le> Re b" using Re_bounds[OF that] by auto
      define u where "u \<equiv> Re w / Re b"
      have "0 \<le> u" "u \<le> 1" unfolding u_def using bds Reb by auto
      have "Complex (Re w) 0 = (1 - u) *\<^sub>R 0 + u *\<^sub>R b"
        unfolding u_def using Reb Imb
        by (simp add: complex_eq_iff scaleR_complex.ctr)
      then show ?thesis using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
        unfolding closed_segment_def by auto
    qed
      \<comment> \<open>Sublemma: any @{term z} between $p = \mathit{Complex}\,(Re\,w)\,0$ and @{term w} is in the convex hull\<close>
    have in_ch_via_seg: "z \<in> convex hull (path_image g)"
      if w_pi: "w \<in> path_image g"
        and Re_eq: "Re w = Re z"
        and Im_between: "(0 \<le> Im z \<and> Im z \<le> Im w) \<or> (Im w \<le> Im z \<and> Im z \<le> 0)"
      for z w
    proof -
      define p where "p \<equiv> Complex (Re w) 0"
      have p_in_ch: "p \<in> convex hull (path_image g)"
        using b_in_ch closed_segment_subset p_def real_point_in_seg w_pi zero_in_ch by blast
      have w_in_ch: "w \<in> convex hull (path_image g)"
        using hull_subset[of "path_image g" convex] w_pi by auto
      show "z \<in> convex hull (path_image g)"
      proof (cases "Im w = 0")
        case True
        with that show ?thesis using p_in_ch
          unfolding p_def
          by (metis complex.exhaust_sel[of z] nle_le)
      next
        case False
        define u where "u \<equiv> Im z / Im w"
        have "0 \<le> u" "u \<le> 1" unfolding u_def using Im_between False
          by (auto simp: field_simps split: if_splits)
        have "z = (1 - u) *\<^sub>R p + u *\<^sub>R w"
          using False by (simp add: Re_eq p_def u_def complex_eq_iff scaleR_complex.ctr field_simps)
        then show ?thesis
          by (simp add: \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> convexD_alt p_in_ch w_in_ch)
      qed
    qed
    have Au_sub: "Au \<subseteq> convex hull (path_image g)"
    proof (rule subsetI)
      fix z assume "z \<in> Au"
      then obtain w where "w \<in> g ` {0..t}" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
        unfolding Au_def by auto
      then show "z \<in> convex hull (path_image g)"
        using t in_ch_via_seg[of w z] by (auto simp: path_image_def)
    qed
    have Al_sub: "Al \<subseteq> convex hull (path_image g)"
    proof (rule subsetI)
      fix z assume "z \<in> Al"
      then obtain w where "w \<in> g ` {t..1}" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
        unfolding Al_def by auto
      then show "z \<in> convex hull (path_image g)"
        using t in_ch_via_seg[of w z] by (auto simp: path_image_def)
    qed
    have Au_Al_sub_closure: "Au \<union> Al \<subseteq> closure (inside (path_image g))"
      using Au_sub Al_sub ch_eq by auto

    have inside_sub_Au_Al: "inside (path_image g) \<subseteq> Au \<union> Al"
    proof (rule subsetI)
      fix z assume z_in: "z \<in> inside (path_image g)"
        \<comment> \<open>Set up the convex hull S and its key properties\<close>
      define S where "S \<equiv> convex hull (path_image g)"
      have S_bounded: "bounded S"
        by (simp add: S_def bounded_convex_hull bounded_simple_path_image g)
      have frontier_S: "frontier S = path_image g"
        unfolding S_def using frontier_convex_hull_eq_path_image[OF g(1) _ conv] g(2,3) by auto
      have inside_eq_int: "inside (path_image g) = interior S"
        using S_bounded S_def frontier_S inside_frontier_eq_interior by force
      have S_int_ne: "interior S \<noteq> {}"
        using z_in inside_eq_int by auto
      have rel_fr_eq: "rel_frontier S = frontier S"
        using rel_frontier_nonempty_interior[OF S_int_ne] .
      have z_int: "z \<in> interior S" and z_rel_int: "z \<in> rel_interior S" 
        using z_in inside_eq_int rel_interior_nonempty_interior by auto
          \<comment> \<open>Case split on the sign of $Im\,z$\<close>
      show "z \<in> Au \<union> Al"
      proof (cases "Im z \<ge> 0")
        case True
          \<comment> \<open>Shoot a ray upward from @{term z} in direction @{term \<i>}.
             By \<open>ray_to_rel_frontier\<close>, we hit a point on @{term "frontier S"} $=$ @{term "path_image g"}.\<close>
        obtain d where d: "d > 0" "z + d *\<^sub>R \<i> \<in> rel_frontier S"
          by (metis S_bounded complex_i_not_zero ray_to_frontier rel_fr_eq z_int)
        define w where "w \<equiv> z + d *\<^sub>R \<i>"
        have w_on_path: "w \<in> path_image g"
          using d(2) rel_fr_eq frontier_S w_def by auto
        have Re_w: "Re w = Re z" and Im_w: "Im w = Im z + d" unfolding w_def by auto
        have Im_w_pos: "Im w > 0" using True d(1) Im_w by linarith
        \<comment> \<open>Since $Im\,w > 0$ and the lower arc has $Im \le 0$, @{term w} must be on the upper arc\<close>
        have "{0..1} = {0..t} \<union> {t..1}" using t by (auto simp: ivl_disj_un_two_touch)
        then have w_upper: "w \<in> g ` {0..t}"
          using w_on_path Im_w_pos below subsetD by (fastforce simp: path_image_def)
        show "z \<in> Au \<union> Al"
          using Au_def Im_w Re_w True d(1) w_upper by auto
      next
        case False
        then have Im_z_neg: "Im z \<le> 0" by simp
            \<comment> \<open>Shoot a ray downward from @{term z} in direction @{term "-\<i>"}\<close>
        obtain d where d: "d > 0" "z + d *\<^sub>R (-\<i>) \<in> frontier S"
          by (metis S_bounded complex_i_not_zero neg_equal_0_iff_equal ray_to_frontier z_int)
        have d2: "z - d *\<^sub>R \<i> \<in> rel_frontier S"
          using d(2) rel_fr_eq by (simp add: real_vector.scale_minus_right)
        define w where "w \<equiv> z - d *\<^sub>R \<i>"
        have w_on_path: "w \<in> path_image g"
          using d2 rel_fr_eq frontier_S w_def by auto
        have Re_w: "Re w = Re z" and Im_w: "Im w = Im z - d" unfolding w_def by auto
        have Im_w_neg: "Im w < 0" using Im_z_neg d(1) Im_w by linarith
            \<comment> \<open>Since $Im\,w < 0$, @{term w} must be on the lower arc\<close>
        have w_lower: "w \<in> g ` {t..1}"
        proof -
          have "{0..1} = {0..t} \<union> {t..1}" using t by (auto simp: ivl_disj_un_two_touch)
          then have "path_image g = g ` {0..t} \<union> g ` {t..1}"
            unfolding path_image_def by (simp add: image_Un)
          then have "w \<in> g ` {0..t} \<union> g ` {t..1}" using w_on_path by simp
          moreover have "w \<notin> g ` {0..t}"
            using above Im_w_neg by (auto simp: subset_iff)
          ultimately show ?thesis by blast
        qed
        show "z \<in> Au \<union> Al"
          using Al_def Im_w Im_z_neg Re_w d(1) w_lower by auto
      qed
    qed
    have inside_eq: "measure lebesgue (inside (path_image g)) = measure lebesgue (Au \<union> Al)"
    proof -
      have bdd_inside: "bounded (inside (path_image g))"
       and frontier_inside: "frontier (inside (path_image g)) = path_image g"
        using Jordan_inside_outside g by auto
      have neg_frontier: "negligible (frontier (inside (path_image g)))"
        using negligible_convex_frontier[OF conv] .
      have inside_meas: "inside (path_image g) \<in> lmeasurable"
        using measurable_Jordan[OF bdd_inside neg_frontier] .
          \<comment> \<open>The symmetric difference is contained in @{term "path_image g"}, which is negligible\<close>
      have "inside (path_image g) \<Delta> (Au \<union> Al) \<subseteq> path_image g"
        by (metis Au_Al_sub_closure Diff_mono Diff_subset_conv closure_Un_frontier frontier_inside 
            inside_sub_Au_Al le_iff_sup)
      then show ?thesis
        using measure_negligible_symdiff[OF inside_meas] negligible_subset neg_frontier frontier_inside
        by metis
    qed
      \<comment> \<open>Step D: @{term "Au \<inter> Al \<subseteq> {z. Im z = 0}"}, which is negligible in $\mathbb{R}^2$.
         Therefore $\mathit{measure}\,(Au \cup Al) = \mathit{measure}\,Au + \mathit{measure}\,Al$.\<close>
    have inter_null: "Au \<inter> Al \<subseteq> {z. Im z = 0}"
      unfolding Au_def Al_def by auto
    have "measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al"
    proof -
      have "negligible (Au \<inter> Al)"
        using negligible_hyperplane[of \<i> 0] negligible_subset inter_null by auto
      then have "measure lebesgue (Au \<inter> Al) = 0"
        by (rule negligible_imp_measure0)
      moreover have "measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al - measure lebesgue (Au \<inter> Al)"
        using measure_Un3[of Au lebesgue Al] Au_meas Al_meas by auto
      ultimately show ?thesis by simp
    qed
    show ?thesis
      using inside_eq \<open>measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al\<close>
        int_upper int_lower by simp
  qed
  have int_eq: "\<bar>integral {0..1} f\<bar> = measure lebesgue (inside (path_image g))"
    using split_int area_decomp upper_int lower_int by linarith
  show ?thesis unfolding Green_concl_def f_def
    using int_eq f_abs_int unfolding f_def by auto
qed

subsection \<open>Green's theorem special case at zero\<close>

interpretation R: Green "reversepath g" "uminus \<circ> reversepath g'" "(\<lambda>t. 1-t) ` U" a b
  by (rule rev)

lemma Green_area_zero:
  assumes "a = 0"
  shows "Green_concl g g'"
proof -
  have g0: "g 0 = 0" using assms g(2) by (simp add: pathstart_def)
  have g1: "g 1 = 0" using assms g(3) by (simp add: pathfinish_def)
  define f where "f \<equiv> \<lambda>s. Re (g' s) * Im (g s)"
  have split_case: "Green_concl g g'"
    if assms: "a = 0"
      and t: "0 < t" "t < 1"
      and hgt: "g t = b"
      and above: "g ` {0..t} \<subseteq> {z. 0 \<le> Im z}"
      and below: "g ` {t..1} \<subseteq> {z. Im z \<le> 0}"
    for t :: real
    using Green_area_zero_A[OF assms t hgt above below] .
  have split_case': "Green_concl g g'"
    if assms: "a = 0"
      and t: "0 < t" "t < 1"
      and hgt: "g t = b"
      and below: "g ` {0..t} \<subseteq> {z. Im z \<le> 0}"
      and above: "g ` {t..1} \<subseteq> {z. 0 \<le> Im z}"
    for t :: real
  proof -
    have "Green_concl (reversepath g) (uminus \<circ> reversepath g')"
    proof (intro R.Green_area_zero_A)
      show "a=0" "0 < 1-t" "1-t < 1"
        using assms t by auto
      show "reversepath g (1-t) = b"
        by (simp add: hgt reversepath_def)
      show "reversepath g ` {0..1-t} \<subseteq> {z. 0 \<le> Im z}"
        using above by (force simp: reversepath_def image_subset_iff)
      show "reversepath g ` {1-t..1} \<subseteq> {z. Im z \<le> 0}"
        using below by (force simp: reversepath_def image_subset_iff)
    qed
    moreover have "integral {0..1} (\<lambda>t. Re (reversepath g' t) * Im (reversepath g t)) 
                 = integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))"
      using has_integral_affinity [of f _ 0 1 "-1" 1] f_abs_int
      by (fastforce simp add: reversepath_def f_def absolutely_integrable_on_def)
    ultimately show ?thesis
      using f_abs_int by (auto simp: Green_concl_def)
  qed

  have Reb: "Re b > 0" using b(2) assms by simp
  have Im_a: "Im a = 0" using assms by simp
  have Im_b: "Im b = 0" using b(3) Im_a by simp
  have path_g: "path g" using g(1) simple_path_imp_path by blast
  have cont_g: "continuous_on {0..1} g"
    using path_g by (simp add: path_def)
  obtain t where t: "g t = b" "0 < t" "t < 1"
  proof -
    obtain t where t0: "g t = b" "t \<in> {0..1}"
      using b by (auto simp: path_image_def)
    have "0 < t"
      by (metis atLeastAtMost_iff b(2) g(2) not_le order_eq_iff pathstart_def t0)
    moreover have "t < 1"
      by (smt (verit, best) b(2) box_real(2) g(3) mem_box_real(2) pathfinish_def t0)
    ultimately show thesis using t0 that by blast
  qed
  have "g ` {0..t} \<subseteq> {z. 0 \<le> Im z} \<and> g ` {t..1} \<subseteq> {z. Im z \<le> 0} \<or>
        g ` {0..t} \<subseteq> {z. Im z \<le> 0} \<and> g ` {t..1} \<subseteq> {z. 0 \<le> Im z}"
  proof -
    have "open_segment 0 b \<subseteq> frontier (inside (path_image g)) \<or>
          open_segment 0 b \<subseteq> interior (inside (path_image g))"
    proof (rule convex_open_segment_cases_alt)
      show "convex (inside (path_image g))"
        by (simp add: conv)
      show "0 \<in> closure (inside (path_image g))"
        using hull_inc convex_hull_eq_closure_inside
        by (metis assms conv g pathfinish_in_path_image)
      show "b \<in> closure (inside (path_image g))"
        using hull_inc convex_hull_eq_closure_inside
        using R.g(2) b(1) conv g(1,2) by fastforce
    qed
    then consider "open_segment 0 b \<subseteq> path_image g" 
      | "open_segment 0 b \<subseteq> inside (path_image g)"
      by (metis Jordan_inside_outside g interior_subset subset_trans)
    then show ?thesis
    proof cases
      case 1
      have *: "connectedin euclidean (open_segment 0 b)"
        by (simp add: convex_connected)
      with 1 have conn: "connectedin (subtopology euclidean (path_image g))
                         (open_segment 0 b)"
        by (simp add: connectedin_subtopology)
      have pi1: "g ` {0<..<t} \<subseteq> path_image g" and pi2: "g ` {t<..<1} \<subseteq> path_image g"
        using t by (auto simp: path_image_def image_iff)
      have cl1: "g ` {0<..<t} \<inter> path_image g \<inter> closure (path_image g \<inter> g ` {t<..<1}) = {}"
      proof -
        have lf: "loop_free g" using g(1) by (simp add: simple_path_def)
        have inj: "inj_on g {0<..<1}" using lf loop_free_inj_on by blast
        have disj: "g ` {0<..<t} \<inter> g ` {t..1} = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain x y where xy: "x \<in> {0<..<t}" "y \<in> {t..1}" "g x = g y"
            by blast
          have x01: "x \<in> {0..1}" using xy(1) t(3) by auto
          have y01: "y \<in> {0..1}" using xy(2)
            using t(2) by auto
          have "x \<noteq> y" using xy(1,2) by auto
          then have "x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
            using lf xy(3) x01 y01 unfolding loop_free_def by blast
          then show False using xy(1,2) by auto
        qed
        have closed_img: "closed (g ` {t..1})"
          using compact_continuous_image[OF continuous_on_subset[OF cont_g]]
          by (simp add: compact_imp_closed less_eq_real_def t(2))
        have "closure (g ` {t<..<1}) \<subseteq> g ` {t..1}"
          using closed_img closure_minimal by (meson closure_minimal image_mono greaterThanLessThan_subseteq_atLeastAtMost_iff order.refl less_imp_le)
        then have "closure (path_image g \<inter> g ` {t<..<1}) \<subseteq> g ` {t..1}"
          by (meson Int_lower2 closure_mono dual_order.trans)
        then show ?thesis using disj by auto
      qed
      have cl2: "g ` {t<..<1} \<inter> path_image g \<inter> closure (path_image g \<inter> g ` {0<..<t}) = {}"
      proof -
        have lf: "loop_free g" using g(1) by (simp add: simple_path_def)
        have disj: "g ` {t<..<1} \<inter> g ` {0..t} = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain x y where xy: "x \<in> {t<..<1}" "y \<in> {0..t}" "g x = g y"
            by blast
          have x01: "x \<in> {0..1}" using xy(1) using t(2) by force
          have y01: "y \<in> {0..1}" using xy(2) t(3) by auto
          have "x \<noteq> y" using xy(1,2) by auto
          then have "x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
            using lf xy(3) x01 y01 unfolding loop_free_def by blast
          then show False using xy(1,2) by auto
        qed
        have closed_img: "closed (g ` {0..t})"
          using compact_continuous_image[OF continuous_on_subset[OF cont_g] _]
          by (meson atLeastatMost_subset_iff compact_imp_closed compact_interval
              eucl_less_le_not_le order.refl t(3))
        have "closure (g ` {0<..<t}) \<subseteq> g ` {0..t}"
          using closed_img closure_minimal by (meson closure_minimal image_mono greaterThanLessThan_subseteq_atLeastAtMost_iff order.refl less_imp_le)
        then have "closure (path_image g \<inter> g ` {0<..<t}) \<subseteq> g ` {0..t}"
          by (meson Int_lower2 closure_mono dual_order.trans)
        then show ?thesis using disj by auto
      qed
      have sub: "open_segment 0 b \<subseteq> g ` {0<..<t} \<union> g ` {t<..<1}"
      proof -
        have decomp: "path_image g \<subseteq> g ` {0<..<t} \<union> g ` {t<..<1} \<union> {0, b}"
        proof
          fix z assume "z \<in> path_image g"
          then obtain s where s: "s \<in> {0..1}" "g s = z" by (auto simp: path_image_def)
          then consider "s = 0" | "s \<in> {0<..<t}" | "s = t" | "s \<in> {t<..<1}" | "s = 1"
            using t by force
          then show "z \<in> g ` {0<..<t} \<union> g ` {t<..<1} \<union> {0, b}"
            using \<open>g s = z\<close> t g0 g1 by blast 
        qed
        have "open_segment 0 b \<inter> {0, b} = {}"
          unfolding open_segment_def by auto
        then show ?thesis using 1 decomp by auto
      qed
      have sep: "separatedin (subtopology euclidean (path_image g))
                              (g ` {0<..<t}) (g ` {t<..<1})"
      proof -
        have d1: "g ` {0<..<t} \<inter> closure (g ` {t<..<1}) = {}"
          by (metis cl1 inf.absorb_iff2 inf.commute pi1 pi2)
        have d2: "g ` {t<..<1} \<inter> closure (g ` {0<..<t}) = {}"
          by (metis Int_absorb1 Int_commute cl2 pi1 pi2)
        have "separatedin euclidean (g ` {0<..<t}) (g ` {t<..<1})"
          unfolding separatedin_def using d1 d2
          by (simp add: euclidean_closure_of topspace_euclidean)
        then show ?thesis
          using pi1 pi2 by (simp add: separatedin_subtopology)
      qed
      have "open_segment 0 b \<subseteq> g ` {0<..<t} \<or> open_segment 0 b \<subseteq> g ` {t<..<1}"
        using connectedin_subset_separated_union[OF conn sep sub] .
      then have "closed_segment 0 b \<subseteq> g ` {0..t} \<or> closed_segment 0 b \<subseteq> g ` {t..1}"
        unfolding closed_segment_eq_open
        by (elim disj_forward) (use g0 g1 t in auto)
      then have seg_eq: "g ` {0..t} = closed_segment 0 b \<or> g ` {t..1} = closed_segment 0 b"
      proof (elim disjE)
        assume sub: "closed_segment 0 b \<subseteq> g ` {0..t}"
        have inj: "inj_on g {0..t}" using arc_inj_on[of 0 t] t by auto
        have "continuous_on {0..t} g"
          using continuous_on_subset[OF cont_g] t by auto
        then have cont_inv: "continuous_on (g ` {0..t}) (the_inv_into {0..t} g)"
          using continuous_on_inv_into[OF _ compact_Icc inj] by metis
        have inv_mem: "the_inv_into {0..t} g z \<in> {0..t}" if "z \<in> closed_segment 0 b" for z
          using the_inv_into_into[OF inj _ order_refl] sub that by blast
        have eq0: "the_inv_into {0..t} g 0 = 0"
          using the_inv_into_f_f[OF inj, of 0] g0 t by auto
        have eqt: "the_inv_into {0..t} g b = t"
          using the_inv_into_f_f[OF inj, of t] t by auto
        have conn: "connected (the_inv_into {0..t} g ` closed_segment 0 b)"
          by (intro connected_continuous_image continuous_on_subset[OF cont_inv sub]
              connected_segment)
        have "0 \<in> the_inv_into {0..t} g ` closed_segment 0 b"
          using eq0 by (auto intro: rev_image_eqI ends_in_segment)
        moreover have "t \<in> the_inv_into {0..t} g ` closed_segment 0 b"
          using eqt by (auto intro: rev_image_eqI ends_in_segment)
        ultimately have "{0..t} \<subseteq> the_inv_into {0..t} g ` closed_segment 0 b"
          using connected_contains_Icc[OF conn] by auto
        then have "g ` {0..t} \<subseteq> g ` (the_inv_into {0..t} g ` closed_segment 0 b)"
          by (rule image_mono)
        also have "\<dots> \<subseteq> closed_segment 0 b"
          using f_the_inv_into_f[OF inj] sub by (auto simp: image_image)
        finally show ?thesis using sub by auto
      next
        assume sub: "closed_segment 0 b \<subseteq> g ` {t..1}"
        have inj: "inj_on g {t..1}" using arc_inj_on[of t 1] t by auto
        have cont_sub: "continuous_on {t..1} g"
          using continuous_on_subset[OF cont_g] t by auto
        have cont_inv: "continuous_on (g ` {t..1}) (the_inv_into {t..1} g)"
          using continuous_on_inv_into[OF cont_sub compact_Icc inj] .
        have eqt: "the_inv_into {t..1} g b = t"
          using the_inv_into_f_f[OF inj, of t] t by auto
        have eq1: "the_inv_into {t..1} g 0 = 1"
          using the_inv_into_f_f[OF inj, of 1] g1 t by auto
        have conn: "connected (the_inv_into {t..1} g ` closed_segment 0 b)"
          by (intro connected_continuous_image continuous_on_subset[OF cont_inv sub]
              connected_segment)
        have "t \<in> the_inv_into {t..1} g ` closed_segment 0 b"
          using eqt by (auto intro: rev_image_eqI ends_in_segment)
        moreover have "1 \<in> the_inv_into {t..1} g ` closed_segment 0 b"
          using eq1 by (auto intro: rev_image_eqI ends_in_segment)
        ultimately have "{t..1} \<subseteq> the_inv_into {t..1} g ` closed_segment 0 b"
          using connected_contains_Icc[OF conn] by auto
        then have "g ` {t..1} \<subseteq> g ` (the_inv_into {t..1} g ` closed_segment 0 b)"
          by (rule image_mono)
        also have "\<dots> \<subseteq> closed_segment 0 b"
          using f_the_inv_into_f[OF inj] sub by (auto simp: image_image)
        finally show ?thesis using sub by auto
      qed
        \<comment> \<open>Use \<open>convex_triple_rel_frontier\<close> to show the inside is on one side of $Im = 0$\<close>
      have inside_side: "inside (path_image g) \<subseteq> {z. Im z \<le> 0} \<or>
                         inside (path_image g) \<subseteq> {z. 0 \<le> Im z}"
      proof -
        have J: "inside (path_image g) \<noteq> {}" "open (inside (path_image g))"
          "frontier (inside (path_image g)) = path_image g"
          using Jordan_inside_outside g by blast+
        have intne: "interior (inside (path_image g)) \<noteq> {}"
          using J(1,2) interior_eq by auto
        have rf_eq: "rel_frontier (inside (path_image g)) = frontier (inside (path_image g))"
          using rel_frontier_nonempty_interior intne by blast
        have mid_on: "midpoint 0 b \<in> path_image g"
          using "1" Reb by force
        have rf0: "(0::complex) \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) g0 by (auto simp: path_image_def intro!: image_eqI[of _ _ 0])
        have rfb: "b \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) b(1) by auto
        have rfm: "midpoint 0 b \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) mid_on by auto
        have ne1: "(0::complex) \<noteq> b" using b(2) assms by (auto simp: complex_eq_iff)
        have ne2: "(0::complex) \<noteq> midpoint 0 b"
          using ne1 by (simp add: midpoint_def complex_eq_iff)
        have ne3: "b \<noteq> midpoint 0 b"
          using ne1 by (simp add: midpoint_def complex_eq_iff)
        have \<section>: "\<i> \<bullet> midpoint 0 b = 0"
          using Im_b by (simp add: midpoint_def complex_inner_i_left)
        show ?thesis
          using Im_b convex_triple_rel_frontier[OF conv rf0 rfb rfm ne1 ne2 ne3 _ _ \<section>] 
          by (auto simp: midpoint_def complex_inner_i_left)
      qed
      have pi_sub: "path_image g \<subseteq> closure (inside (path_image g))"
        using hull_subset[of "path_image g" convex] convex_hull_eq_closure_inside[OF g(1)] g(2,3) conv by force
          \<comment> \<open>The closed segment from $0$ to $b$ has $Im = 0$, so lies in both half-planes.\<close>
      have seg_both: "closed_segment 0 b \<subseteq> {z. Im z \<le> 0}" "closed_segment 0 b \<subseteq> {z. 0 \<le> Im z}"
        using Im_b by (auto simp: closed_segment_def)
          \<comment> \<open>If the inside is contained in a half-plane, then so is @{term "path_image g"} (by closure).\<close>
      have "inside (path_image g) \<subseteq> {z. Im z \<le> 0} \<Longrightarrow> path_image g \<subseteq> {z. Im z \<le> 0}"
        using pi_sub closure_minimal[OF _ closed_halfspace_le[of \<i> 0, simplified complex_inner_i_left]]
        by auto
      moreover
      have "inside (path_image g) \<subseteq> {z. 0 \<le> Im z} \<Longrightarrow> path_image g \<subseteq> {z. 0 \<le> Im z}"
        using pi_sub closure_minimal[OF _ closed_halfspace_ge[of 0 \<i>, simplified complex_inner_i_left]]
        by auto
      ultimately show ?thesis
        using seg_eq inside_side seg_both
        by (auto simp: path_image_def image_subset_iff)
    next
      case seg_inside:2
      have real_on_curve: "z = 0 \<or> z = b" 
        if z_on: "z \<in> path_image g" and z_real: "Im z = 0" for z
      proof (rule ccontr)
        assume non: "\<not> ?thesis"
          \<comment> \<open>diameter bounds force @{term z} into @{term "closed_segment 0 b"}.\<close>
        have bdd: "bounded (path_image g)"
          using g(1) bounded_simple_path_image by blast
        have z0_on: "0 \<in> path_image g"
          using pathstart_in_path_image[of g] g(2) \<open>a=0\<close> by simp
        have diam_eq: "diameter (path_image g) = Re b"
          using dab \<open>a=0\<close> Im_b Reb by (simp add: dist_complex_def cmod_eq_Re)
        have d1: "dist 0 z \<le> Re b"
          using diameter_bounded_bound[OF bdd z0_on z_on] diam_eq by simp
        have d2: "dist z b \<le> Re b"
          using diameter_bounded_bound[OF bdd z_on b(1)] diam_eq by simp
        have Re_le: "Re z \<le> Re b"
          using d1 z_real by (simp add: dist_complex_def cmod_eq_Re)
        have Re_ge: "Re z \<ge> 0"
          using d2 z_real Im_b by (simp add: dist_complex_def cmod_eq_Re minus_complex.sel)
        have z_eq: "z = of_real (Re z)"
          using z_real complex_is_Real_iff of_real_Re by metis
        have b_eq: "b = of_real (Re b)"
          using Im_b complex_is_Real_iff of_real_Re by metis
        have z_in_seg: "z \<in> closed_segment 0 b"
          by (metis Re_ge Re_le Reb atLeastAtMost_iff b_eq closed_segment_eq_real_ivl1
              less_eq_real_def of_real_0 of_real_closed_segment z_eq)
          \<comment> \<open>Step 4: @{term z} is on the curve, so @{term "z \<notin> inside (path_image g)"}. Hence @{term "z \<notin> open_segment 0 b"}.
       Combined with @{term "z \<in> closed_segment 0 b"}, we get $z = 0 \vee z = b$.\<close>
        have "z \<notin> inside (path_image g)"
          using inside_no_overlap z_on by blast
        then have "z \<notin> open_segment 0 b"
          using seg_inside by blast
        then show False
          using non z_in_seg by (auto simp: closed_segment_eq_open)
      qed

\<comment> \<open>@{term "Im \<circ> g"} doesn't change sign on either arc: if it did, the IVT gives a real point
     in the interior of the arc, contradicting \<open>real_on_curve\<close> and injectivity.\<close>
      have no_cross: "(\<forall>s \<in> {u..v}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {u..v}. Im (g s) \<le> 0)"
        if huv: "u < v" "{u..v} \<subseteq> {0..1}" and hinj: "inj_on g {u..v}"
          and hend: "Im (g u) = 0" "Im (g v) = 0" for u v
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain s\<^sub>1 s\<^sub>2 where s1: "s\<^sub>1 \<in> {u..v}" "Im (g s\<^sub>1) > 0"
          and s2: "s\<^sub>2 \<in> {u..v}" "Im (g s\<^sub>2) < 0"
          by (meson linorder_not_le)
        have cont_uv: "continuous_on {u..v} g"
          using cont_g continuous_on_subset huv(2) by blast
            \<comment> \<open>The IVT gives $s \in (u,v)$ with $Im(g\,s) = 0$\<close>
        obtain s where s: "s \<in> {u..v}" "Im (g s) = 0" "s \<noteq> u" "s \<noteq> v"
        proof (cases "s\<^sub>1 \<le> s\<^sub>2")
          case True
          obtain s where hs: "s \<in> {s\<^sub>1..s\<^sub>2}" "Im (g s) = 0"
            using ivt_decreasing_component_on_1[OF True, of g \<i> 0] continuous_on_subset[OF cont_uv] s1 s2
            by (force simp: complex_inner_i_right)
          then obtain "s \<noteq> u" "s \<noteq> v" "s \<in> {u..v}"
            using s1 s2 by force
          then show thesis using that hs by blast
        next
          case False
          then have le: "s\<^sub>2 \<le> s\<^sub>1" by linarith
          obtain s where hs: "s \<in> {s\<^sub>2..s\<^sub>1}" "Im (g s) = 0"
            using ivt_increasing_component_on_1[OF le, of g \<i> 0] continuous_on_subset[OF cont_uv] s1 s2
            by (force simp: complex_inner_i_right)
          then obtain  "s \<noteq> u" "s \<noteq> v" "s \<in> {u..v}"
            using s1 s2 by force
          then show thesis using that hs by blast
        qed

        \<comment> \<open>$g\,s$ is on the path, so @{term "g s \<in> {0, b}"} by \<open>real_on_curve\<close>\<close>
        have "g s = 0 \<or> g s = b" using real_on_curve s(2)
          by (metis subsetD imageI path_image_def s(1) that(2))
        \<comment> \<open>But @{term g} is injective on $\{u..v\}$ and $s \in (u,v)$, so $g\,s \neq g\,u$ and $g\,s \neq g\,v$\<close>
        moreover have "g s \<noteq> g u" "g s \<noteq> g v"
          using inj_onD[OF hinj] s by auto
            \<comment> \<open>Since @{term "{g u, g v} \<subseteq> {0, b}"}, this gives the contradiction\<close>
        moreover have "g u \<in> {0, b}" "g v \<in> {0, b}"
          using real_on_curve hend huv by (auto simp: path_image_def subset_iff)
        ultimately show False
          using \<open>u < v\<close> inj_onD [OF hinj] by (auto simp: order_class.less_le)
      qed
      have no_cross_1: "(\<forall>s \<in> {0..t}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {0..t}. Im (g s) \<le> 0)"
        using no_cross[of 0 t] arc_inj_on[of 0 t] t g0 Im_b by auto
      have no_cross_2: "(\<forall>s \<in> {t..1}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {t..1}. Im (g s) \<le> 0)"
        using no_cross[of t 1] arc_inj_on[of t 1] t g1 Im_b by auto
      \<comment> \<open>Eliminate the case where both arcs are on the same side of the real axis.\<close>
      have not_all_above: "\<not> (path_image g \<subseteq> {z. 0 \<le> Im z})"
        using Reb assms not_all_above real_on_curve t Im_b by blast
      have not_all_below: "\<not> (path_image g \<subseteq> {z. Im z \<le> 0})"
        using CR.not_all_above using g g0 g1 assms Reb real_on_curve
        by (force simp add: gop_def  path_image_compose)
          \<comment> \<open>With the elimination, the 4-way case split from \<open>no_cross_1\<close>/\<open>no_cross_2\<close> reduces to two\<close>
      have "path_image g = g ` {0..t} \<union> g ` {t..1}"
        unfolding path_image_def using t
        by (metis image_Un ivl_disj_un_two_touch(4) less_eq_real_def)
      with no_cross_1 no_cross_2 not_all_above not_all_below
      show ?thesis by (auto simp: image_subset_iff)
    qed
  qed
  then show ?thesis
    using assms split_case split_case' t by blast
qed


subsection \<open>Conclusion of Green's theorem and the signed area formula for a convex closed curve.\<close>

lemma Green_invariant:
  assumes "\<And>g g' U b. Green g g' U 0 b \<Longrightarrow> Green_concl g g'"
  shows "Green_concl g g'"
proof -
  have *: "Green_concl ((\<lambda>x. -a+x) \<circ> g) g'"
  proof (intro assms)
    show "Green ((+) (- a) \<circ> g) g' U 0 (-a+b)"
    proof
      show "simple_path ((+) (- a) \<circ> g)"
        by (simp add: g simple_path_translation_eq)
      show "pathstart ((+) (- a) \<circ> g) = 0"
        by (simp add: g pathstart_compose)
      show "pathfinish ((+) (- a) \<circ> g) = 0"
        by (simp add: g pathfinish_compose)
      show "- a + b \<in> path_image ((+) (- a) \<circ> g)"
        by (simp add: b path_image_translation)
       show "dist 0 (- a + b) = diameter (path_image ((+) (- a) \<circ> g))"
         by (metis add.commute dab diameter_translation dist_0_norm dist_commute dist_norm path_image_compose pth_2)
      show "convex (inside (path_image ((+) (- a) \<circ> g)))"
        by (metis path_image_translation inside_translation convex_translation_eq conv)
      show "absolutely_continuous_on {0..1} ((+) (- a) \<circ> g)"
        by (metis (no_types, lifting) ext absolutely_continuous_on_add absolutely_continuous_on_const cont o_apply)
    next
      fix t
      assume "t \<in> {0..1} - U"
      then show "((+) (- a) \<circ> g has_vector_derivative g' t) (at t)"
        using has_vector_derivative_shift vder by blast
    qed (use b U in auto)
  qed
  let ?G = "\<lambda>t. Re (g' t) * Im (g t)"
  show ?thesis
    unfolding Green_concl_def
  proof (intro conjI f_abs_int)
    have meas_eq: "measure lebesgue (inside (path_image ((+) (- a) \<circ> g)))
                 = measure lebesgue (inside (path_image g))"
      by (metis path_image_translation inside_translation measure_translation)
    have "(g' has_integral (g 1 - g 0)) {0..1}"
      using fundamental_theorem_of_calculus_absolutely_continuous[OF U _ cont, of g']
      by (metis zero_le_one vder has_vector_derivative_at_within)
    then have int_g': "(g' has_integral 0) {0..1}" 
      using g by (simp add: pathstart_def pathfinish_def)
    have Re_has_int: "((\<lambda>t. Re (g' t)) has_integral 0) {0..1}"
      using has_integral_Re[OF int_g'] by simp
    have Ima_has_int: "((\<lambda>t. Im a * Re (g' t)) has_integral 0) {0..1}"
      using has_integral_mult_right[OF Re_has_int] by simp
    have ai_translated: "(\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t)) integrable_on {0..1}"
      using * unfolding Green_concl_def absolutely_integrable_on_def by auto
    have "integral {0..1} ?G
          = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t) + Im a * Re (g' t))"
      by (simp add: o_def plus_complex.sel uminus_complex.sel algebra_simps)
    also have "\<dots> = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t))"
      using integral_add[OF ai_translated has_integral_integrable] 
        Ima_has_int integral_unique[OF Ima_has_int] by force
    finally show "\<bar>integral {0..1} ?G\<bar> = Sigma_Algebra.measure lebesgue (inside (path_image g))"
      using * meas_eq unfolding Green_concl_def by auto
  qed
qed

theorem area_theorem:
  obtains "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
      measure lebesgue (inside (path_image g))"
  using Green.Green_area_zero Green_concl_def Green_invariant by blast

end (*Green*)

end
