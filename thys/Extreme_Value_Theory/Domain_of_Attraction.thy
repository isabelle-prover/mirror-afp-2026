(*  Title:   Domain_of_Attraction.thy
    Author:  Michikazu Hirata
*)

section \<open>Domain of Attraction\<close>
theory Domain_of_Attraction
imports
   "HOL-Probability.Weak_Convergence"
   "Cauchy_Functional_Equation.Cauchy_Functional_Equation"
   "Pareto_Distribution"
begin

text \<open>This theory file is based on Chapter~1 of the book
      by de Haan and Ferreira~\<^cite>\<open>deHaanFerreira\<close>.\<close>

subsection \<open>Definitions\<close>
text \<open>We work with distribution functions as plain functions \<^typ>\<open>real \<Rightarrow> real\<close>,
      as does the book.
      The corresponding statements for i.i.d.\ random variables
      are given in Section~\ref{sec:examples}.\<close>

subsubsection \<open>Degenerate Distributions\<close>
definition degenerate_df :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
"degenerate_df F \<longleftrightarrow> (\<forall>x. F x = 0 \<or> F x = 1)"

lemma degenerate_df_iff_indicator:
  assumes "right_continuous_mono F 0 1"
  shows "degenerate_df F \<longleftrightarrow> (\<exists>c. F = (\<lambda>x. indicat_real {c..} x))"
proof -
  interpret right_continuous_mono F 0 1 by fact
  show ?thesis
  proof
    assume deg: "degenerate_df F"
    hence F01: "\<And>x. F x = 0 \<or> F x = 1"
      by (auto simp: degenerate_df_def)
    obtain z where z: "F z = 1"
      using order_tendstoD[OF top, of "1/2"] F01
      by (fastforce dest!: eventually_happens'[OF trivial_limit_at_top_linorder])
    obtain w where w: "F w = 0"
      using order_tendstoD[OF bot, of "1/2"] F01
      by (fastforce dest!: eventually_happens'[OF trivial_limit_at_bot_linorder])
    define c where "c = Inf {x. F x = 1}"
    have ne: "{x. F x = 1} \<noteq> {}"
      using z by auto
    have bdd: "bdd_below {x. F x = 1}"
    proof (intro bdd_belowI[of _ w])
      fix x
      assume "x \<in> {x. F x = 1}"
      thus "w \<le> x"
        using monoD[OF mono, of x w] w by force
    qed
    have F1: "F x = 1" if "c < x" for x
    proof -
      have "Inf {x. F x = 1} < x"
        using that by (simp add: c_def)
      from cInf_lessD[OF ne this] obtain x' where "F x' = 1" "x' < x"
        by auto
      thus ?thesis
        using monoD[OF mono, of x' x] F01[of x] by auto
    qed
    have F0: "F x = 0" if "x < c" for x
      using cInf_lower[OF _ bdd] that F01[of x] by (fastforce simp: c_def leD)
    have Fc: "F c = 1"
    proof (rule tendsto_unique[of "at_right c" F])
      show "(F \<longlongrightarrow> F c) (at_right c)"
        using cont[of c] by (simp add: continuous_within)
      show "(F \<longlongrightarrow> 1) (at_right c)"
        by (intro tendsto_eventually eventually_mono[OF eventually_at_right_less])
           (simp add: F1)
    qed auto
    have "F = (\<lambda>x. indicat_real {c..} x)"
    proof
      fix x
      consider "x < c" | "x = c" | "c < x"
        by argo
      thus "F x = indicat_real {c..} x"
        by cases (auto simp: F0 F1 Fc indicator_def)
    qed
    thus "\<exists>c. F = (\<lambda>x. indicat_real {c..} x)" ..
  qed(auto simp: degenerate_df_def indicator_def)
qed

lemma EVD_cdf_nondegenerate:
  assumes [arith]:"0 < \<sigma>"
  shows "\<not> degenerate_df (EVD_cdf \<xi> \<mu> \<sigma>)"
  by(auto simp: degenerate_df_def EVD_cdf_def Let_def intro!: exI[where x=\<mu>])

subsubsection \<open>Domain of Attraction\<close>
definition domain_of_attraction :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool"
  (infix \<open>(in'_domain'_attraction'_of)\<close> 50) where
"domain_of_attraction F G \<longleftrightarrow>
   right_continuous_mono F 0 1 \<and> right_continuous_mono G 0 1 \<and>
   (\<exists>a b. (\<forall>n::nat. 0 < a n) \<and> weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G)"

lemma domain_of_attractionD:
  assumes "domain_of_attraction F G"
  shows "right_continuous_mono F 0 1" "right_continuous_mono G 0 1"
    and "\<exists>a b. (\<forall>n::nat. 0 < a n) \<and> weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
  using assms by(auto simp: domain_of_attraction_def)

lemma domain_of_attractionI_eventually_pos:
  assumes F:"right_continuous_mono F 0 1"
    and G:"right_continuous_mono G 0 1"
    and a_pos:"\<forall>\<^sub>F n in at_top. a n > 0"
    and wc:"weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
  shows "domain_of_attraction F G"
proof -
  obtain k where a:"\<And>n. k \<le> n \<Longrightarrow> a n > 0"
    using a_pos eventually_sequentially by auto
  define a' where "a' \<equiv> \<lambda>n. if n < k then 1 else a n"
  have a'_pos:"a' n > 0" for n
    using a by(cases "n < k") (auto simp: a'_def)
  have ev:"\<forall>\<^sub>F n in sequentially.
         F (a n * x + b n) ^ n = F (a' n * x + b n) ^ n" for x
    by(auto intro!: eventually_sequentiallyI[where c=k] simp: a'_def)
  hence wc':"weak_conv (\<lambda>n x. F (a' n * x + b n) ^ n) G"
    using wc by(auto simp: weak_conv_cong[OF ev])
  thus ?thesis
    unfolding domain_of_attraction_def
    using F G a'_pos
    by(intro conjI exI[where x=a',OF exI[where x=b]]) auto
qed

lemma domain_of_attraction_EVD_cdf_rescale:
  fixes \<gamma> \<mu>1 \<mu>2 \<sigma>1 \<sigma>2 :: real
  assumes sigma1[arith]: "0 < \<sigma>1" and sigma2[arith]: "0 < \<sigma>2"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> \<mu>1 \<sigma>1)"
  shows "domain_of_attraction F (EVD_cdf \<gamma> \<mu>2 \<sigma>2)"
proof -
  obtain a b where a: "\<And>n. 0 < a n"
    and wc: "weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) (EVD_cdf \<gamma> \<mu>1 \<sigma>1)"
    and F: "right_continuous_mono F 0 1"
    using dom unfolding domain_of_attraction_def by blast
  define a' where "a' = (\<lambda>n. a n * \<sigma>1 / \<sigma>2)"
  define b' where "b' = (\<lambda>n. a n * \<mu>1 - a n * \<sigma>1 * \<mu>2 / \<sigma>2 + b n)"
  have a'_pos: "0 < a' n" for n
    using a by (simp add: a'_def)
  have arg_eq: "a' n * y + b' n = a n * (\<sigma>1 / \<sigma>2 * (y - \<mu>2) + \<mu>1) + b n" for n y
    by (simp add: a'_def b'_def field_simps)
  have fun_eq: "(\<lambda>n. F (a' n * y + b' n) ^ n)
                  = (\<lambda>n. F (a n * (\<sigma>1 / \<sigma>2 * (y - \<mu>2) + \<mu>1) + b n) ^ n)" for y
    by (simp add: arg_eq)
  have EVD_eq: "EVD_cdf \<gamma> \<mu>1 \<sigma>1 (\<sigma>1 / \<sigma>2 * (y - \<mu>2) + \<mu>1) = EVD_cdf \<gamma> \<mu>2 \<sigma>2 y" for y
  proof -
    have "EVD_cdf \<gamma> \<mu>1 \<sigma>1 (\<sigma>1 / \<sigma>2 * (y - \<mu>2) + \<mu>1)
            = EVD_cdf \<gamma> 0 1 ((\<sigma>1 / \<sigma>2 * (y - \<mu>2) + \<mu>1 - \<mu>1) / \<sigma>1)"
      by (subst EVD_cdf_location_scale) simp_all
    also have "... = EVD_cdf \<gamma> 0 1 ((y - \<mu>2) / \<sigma>2) "
      by simp
    also have "...  = EVD_cdf \<gamma> \<mu>2 \<sigma>2 y"
      by (simp add: EVD_cdf_location_scale)
    finally show ?thesis .
  qed
  have wc': "weak_conv (\<lambda>n y. F (a' n * y + b' n) ^ n) (EVD_cdf \<gamma> \<mu>2 \<sigma>2)"
    using wc isCont_EVD_cdf[OF sigma1]
    unfolding weak_conv_def EVD_eq[symmetric] fun_eq
    by simp
  show ?thesis
    unfolding domain_of_attraction_def
    using F a'_pos right_continuous_mono_EVD_cdf[OF sigma2] wc' by blast
qed

theorem domain_of_attraction_EVD_cdf_iff:
  fixes \<gamma> \<mu> \<sigma> :: real
  assumes sigma[arith]: "0 < \<sigma>"
  shows "domain_of_attraction F (EVD_cdf \<gamma> \<mu> \<sigma>) \<longleftrightarrow> domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  using domain_of_attraction_EVD_cdf_rescale[OF sigma,of 1]
        domain_of_attraction_EVD_cdf_rescale[OF zero_less_one sigma] by auto

lemma EVD_cdf_MDA:
  assumes sigma[arith]:"0 < \<sigma>"
  shows "domain_of_attraction (EVD_cdf \<xi> \<mu> \<sigma>) (EVD_cdf \<xi> \<mu> \<sigma>)"
proof -
  interpret real_distribution "density lborel (EVD_density \<xi> \<mu> \<sigma>)"
    by(rule real_distribution_EVD[OF sigma])
  define a where "a = (\<lambda>n::nat. if n = 0 \<or> \<xi> = 0 then 1 else real n powr \<xi>)"
  define b where "b = (\<lambda>n::nat. if n = 0 then 0 else if \<xi> = 0 then \<sigma> * ln (real n)
                                else (\<mu> - \<sigma> / \<xi>) * (1 - real n powr \<xi>))"
  have a_pos: "0 < a n" for n
    by (auto simp: a_def)
  have eq: "EVD_cdf \<xi> \<mu> \<sigma> (a n * x + b n) ^ n = EVD_cdf \<xi> \<mu> \<sigma> x" if n: "0 < n" for n x
  proof -
    have npos: "(0::real) < real n"
      using n by simp
    have "EVD_cdf \<xi> \<mu> \<sigma> (a n * x + b n) ^ n = EVD_cdf \<xi> 0 1 ((a n * x + b n - \<mu>) / \<sigma>) ^ n"
      by(simp add: EVD_cdf_location_scale)
    also have "\<dots> = EVD_cdf \<xi> 0 1 (if \<xi> = 0 then (a n * x + b n - \<mu>) / \<sigma> - ln (real n)
                     else real n powr (- \<xi>) * ((a n * x + b n - \<mu>) / \<sigma>)
                          + (real n powr (- \<xi>) - 1) / \<xi>)"
      by (rule EVD_cdf_max_stable[OF n])
    also have "(if \<xi> = 0 then (a n * x + b n - \<mu>) / \<sigma> - ln (real n)
                     else real n powr (- \<xi>) * ((a n * x + b n - \<mu>) / \<sigma>)
                          + (real n powr (- \<xi>) - 1) / \<xi>) = (x - \<mu>) / \<sigma>"
      by (cases "\<xi> = 0")
         (use npos in "auto simp: a_def b_def field_simps powr_minus_divide")
    also have "EVD_cdf \<xi> 0 1 ((x - \<mu>) / \<sigma>) = EVD_cdf \<xi> \<mu> \<sigma> x"
      by(simp add: EVD_cdf_location_scale)
    finally show ?thesis .
  qed
  have wc: "weak_conv (\<lambda>n x. EVD_cdf \<xi> \<mu> \<sigma> (a n * x + b n) ^ n) (EVD_cdf \<xi> \<mu> \<sigma>)"
    unfolding weak_conv_def
    by (intro allI impI tendsto_eventually eventually_mono[OF eventually_gt_at_top[of 0]])
       (simp add: eq)
  show ?thesis
    unfolding domain_of_attraction_def
    using right_continuous_mono_axioms a_pos wc by blast
qed

lemma GPD_cdf_MDA:
  fixes \<gamma> \<mu> \<sigma> :: real
  assumes "0 < \<sigma>"
  shows "domain_of_attraction (GPD_cdf \<gamma> \<mu> \<sigma>) (EVD_cdf \<gamma> 0 1)"
  using assms
  by(intro domain_of_attractionI_eventually_pos[OF _ _  eventually_sequentiallyI[of 1],
        where a="\<lambda>n. \<sigma> * (if \<gamma> = 0 then 1 else real n powr \<gamma>)"
          and b="\<lambda>n. \<mu> + \<sigma> * (if \<gamma> = 0 then ln (real n) else (real n powr \<gamma> - 1) / \<gamma>)"]
       right_continuous_mono_GPD_cdf right_continuous_mono_EVD_cdf
       LIMSEQ_imp_weak_conv GPD_normalization) auto

lemma domain_of_attraction_affine:
  fixes c d :: real
  assumes c[arith]:"0 < c" and dm:"domain_of_attraction F G"
  shows "domain_of_attraction (\<lambda>x. F ((x - d) / c)) G"
proof -
  have F:"right_continuous_mono F 0 1"
    and G:"right_continuous_mono G 0 1"
  and "\<exists>a b. (\<forall>n. 0 < a n) \<and> weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
    using domain_of_attractionD[OF dm] by auto
  then obtain a b where a:"\<And>n. 0 < a n" and wc:"weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
    by blast
  interpret F: right_continuous_mono F 0 1
    by fact
  have lim1:"LIM x at_top. (x - d) / c :> at_top"
    using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of "1 / c"] _
        filterlim_tendsto_add_at_top[OF tendsto_const[of "- d" at_top],of "\<lambda>x. x"]]
    by(simp add: filterlim_ident)
  have lim2:"LIM x at_bot. (x - d) / c :> at_bot"
    using filterlim_tendsto_pos_mult_at_bot[OF tendsto_const[of "1 / c"] _
        filterlim_tendsto_add_at_bot_iff
        [THEN iffD2,OF tendsto_const[of "- d" at_bot],of "\<lambda>x. x"]]
    by(simp add: filterlim_ident)
  have 1:"right_continuous_mono (\<lambda>x. F ((x - d) / c)) 0 1"
  proof
    fix x :: real
    have *:"(\<lambda>x. (x - d) / c) ` {x<..} = {(x - d) / c<..}"
      by(intro image_mono_on_continuous_on_greaterThan)
        (auto intro!: strict_mono_onI continuous_on_divide continuous_on_diff
          simp: divide_strict_right_mono lim1)
    show "continuous (at_right x) (\<lambda>x. F ((x - d) / c))"
      by(rule continuous_within_compose2[where g=F])
        (auto simp: continuous_cdivide_iff continuous_diff * F.cont)
    show " ((\<lambda>x. F ((x - d) / c)) \<longlongrightarrow> 0) at_bot"
      "((\<lambda>x. F ((x - d) / c)) \<longlongrightarrow> 1) at_top"
      by(auto intro!: filterlim_compose[where g=F,OF _ lim1] F.bot F.top
          filterlim_compose[where g=F,OF _ lim2])
    show "mono (\<lambda>x. F ((x - d) / c))"
      by(auto intro!: monoD[OF F.mono] monoI simp: divide_right_mono)
  qed
  show ?thesis
    by(auto intro!: exI[where x="\<lambda>n. c * a n",OF conjI[OF _ exI[where x="\<lambda>n. c * b n + d"]]]
        simp: domain_of_attraction_def 1 G a distrib_left[symmetric] mult.assoc wc)
qed

subsection \<open>Fisher--Tippett--Gnedenko Theorem\<close>
text \<open>The following two definitions correspond to
      the functions $U$ and $D$ in equation~(1.1.6) in the book.\<close>
abbreviation tail_quantile :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
"tail_quantile F t \<equiv> ginv F (1 - 1 / t)"

text \<open>@{term tail_quantile} is exactly the \emph{return level}
      associated with \emph{return period} $t$.\<close>

abbreviation limit_quantile :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
"limit_quantile G y \<equiv> ginv G (exp (- (1 / y)))"

lemma lt_tail_quantile_iff:
  fixes F :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and s: "1 < s"
  shows "w < tail_quantile F s \<longleftrightarrow> 1 / s < 1 - F w"
proof -
  have p: "0 < 1 - 1 / s" "1 - 1 / s < 1"
    using s by simp_all
  show ?thesis
    using right_continuous_mono.ginv_le_iff[OF F p, of w] by linarith
qed

lemma tail_quantile_le_of_lt_inv:
  assumes F: "right_continuous_mono F 0 1"
    and Ft[arith]: "F t < 1"
    and u1[arith]: "1 < u" and u2[arith]: "u < 1 / (1 - F t)"
  shows "tail_quantile F u \<le> t"
  by(subst right_continuous_mono.ginv_le_iff[OF F])
    (use pos_less_divide_eq[THEN iffD1,OF _ u2] in "simp_all add: field_simps")

lemma t_lt_tail_quantile_of_gt_inv:
  fixes F :: "real \<Rightarrow> real" and t u :: real
  assumes F: "right_continuous_mono F 0 1"
    and Ft: "F t < 1"
    and u: "1 / (1 - F t) < u"
  shows "t < tail_quantile F u"
  by (smt (verit, best) assms ln_divide_pos ln_less_cancel_iff right_continuous_mono.a_le_f
      right_continuous_mono.ginv_le_iff zero_less_divide_1_iff)

lemma tail_quantile_at_top:
  fixes F :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1"
    and unbdd: "\<And>x. F x < 1"
  shows "filterlim (tail_quantile F) at_top at_top"
  unfolding filterlim_at_top
proof
  interpret right_continuous_mono F 0 1
    by fact
  fix M :: real
  show "\<forall>\<^sub>F t in at_top. M \<le> tail_quantile F t"
    using eventually_gt_at_top[of "1 / (1 - F M)"] eventually_gt_at_top[of "1::real"]
    by eventually_elim
       (use assms less_eq_real_def F t_lt_tail_quantile_of_gt_inv in presburger)
qed

lemma limit_quantile_left_cont:
  assumes G: "right_continuous_mono G 0 1" and p: "0 < p"
  shows "(limit_quantile G \<longlongrightarrow> limit_quantile G p) (at_left p)"
proof -
  interpret right_continuous_mono G 0 1
    by fact
  define g where "g = (\<lambda>y::real. exp (- 1 / y))"
  have g_tendsto: "(g \<longlongrightarrow> g p) (at_left p)"
    unfolding g_def using p by (intro tendsto_intros) simp
  have g_ev: "\<forall>\<^sub>F y in at_left p. 0 < y \<and> y < p"
    using eventually_at_left_field[where x = p] p by auto
  have g_lt: "\<forall>\<^sub>F y in at_left p. g y < g p"
    using p by(auto intro!: eventually_mono[OF g_ev] simp: g_def field_simps)
  note g_at_left = tendsto_imp_filterlim_at_left[OF g_tendsto g_lt]
  have g01: "0 < g p" "g p < 1"
    unfolding g_def using p by auto
  have "filterlim (ginv G) (nhds (ginv G (g p))) (at_left (g p))"
    using ginv_left_cont[OF g01] by simp
  from filterlim_compose[OF this g_at_left]
  show ?thesis
    by(simp add: g_def)
qed

lemma limit_quantile_left_cont_scale:
  assumes G: "right_continuous_mono G 0 1" and y: "0 < y" and p: "0 < p"
  shows "((\<lambda>x. limit_quantile G (x * y)) \<longlongrightarrow> limit_quantile G (p * y)) (at_left p)"
proof -
  have mult_tendsto: "((\<lambda>x. x * y) \<longlongrightarrow> p * y) (at_left p)"
    by (intro tendsto_intros)
  have mult_ev: "\<forall>\<^sub>F x in at_left p. 0 < x \<and> x < p"
    using eventually_at_left_field[where x = p] p by auto
  have mult_lt: "\<forall>\<^sub>F x in at_left p. x * y < p * y"
    using mult_ev by eventually_elim (use y in \<open>auto intro!: mult_strict_right_mono\<close>)
  note mult_at_left = tendsto_imp_filterlim_at_left[OF mult_tendsto mult_lt]
  have py: "0 < p * y"
    using y p by simp
  have "filterlim (limit_quantile G) (nhds (limit_quantile G (p * y))) (at_left (p * y))"
    using limit_quantile_left_cont[OF G py] by simp
  from filterlim_compose[OF this mult_at_left]
  show ?thesis
    by simp
qed

lemma tail_quantile_mono:
  assumes F: "right_continuous_mono F 0 1" and s: "1 < s" and st: "s \<le> t"
  shows "tail_quantile F s \<le> tail_quantile F t"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  show ?thesis
    using s st ex_ge_b ex_less_a
    by(intro ginv_compose_mono[where A="{0<..<1}",THEN mono_onD] mono mono_onI)
      (auto simp: divide_mono)
qed

lemma limit_quantile_mono:
  assumes G: "right_continuous_mono G 0 1" and y1: "0 < y1" and y12: "y1 \<le> y2"
  shows "limit_quantile G y1 \<le> limit_quantile G y2"
proof -
  interpret right_continuous_mono G 0 1 by fact
  show ?thesis
    using y1 y12 ex_ge_b ex_less_a
    by(intro ginv_compose_mono[where A="{0<..<1}",THEN mono_onD] mono mono_onI)
      (auto simp: divide_mono)
qed

lemma limit_quantile_EVD_cdf:
  assumes sigma[arith]:"0 < \<sigma>"
    and ypos[arith]: "0 < y"
  shows "limit_quantile (EVD_cdf \<xi> \<mu> \<sigma>) y
          = (if \<xi> = 0 then \<sigma> * ln y + \<mu> else \<sigma> * (y powr \<xi> - 1) / \<xi> + \<mu>)"
    (is "ginv _ ?p = ?xs")
proof -
  have yppos: "0 < y powr \<xi>"
    using ypos by simp
  have iff: "?p \<le> EVD_cdf \<xi> \<mu> \<sigma> x \<longleftrightarrow> ?xs \<le> x" for x
  proof -
    consider "\<xi> = 0" | "0 < \<xi>" | "\<xi> < 0" by argo
    thus ?thesis
    proof cases
      case 1
      have "?p \<le> EVD_cdf \<xi> \<mu> \<sigma> x \<longleftrightarrow> exp (- ((x - \<mu>) / \<sigma>)) \<le> 1 / y"
        by (simp add: EVD_cdf_def Let_def 1)
      also have "\<dots> \<longleftrightarrow> exp (- ((x - \<mu>) / \<sigma>)) \<le> exp (- ln y)"
        by (simp add: exp_minus inverse_eq_divide)
      also have "\<dots> \<longleftrightarrow> ln y \<le> (x - \<mu>) / \<sigma>"
        by simp
      also have "\<dots> \<longleftrightarrow> \<sigma> * ln y + \<mu> \<le> x"
        by (auto simp: field_simps)
      finally show ?thesis
        by (simp add: 1)
    next
      case 2
      define u where "u = 1 + \<xi> * ((x - \<mu>) / \<sigma>)"
      show ?thesis
      proof (cases "0 < u")
        assume u[arith]:"0 < u"
        have "?p \<le> EVD_cdf \<xi> \<mu> \<sigma> x \<longleftrightarrow> u powr (- 1 / \<xi>) \<le> 1 / y"
          using 2 u by (auto simp add: EVD_cdf_def Let_def u_def)
        also have "\<dots> \<longleftrightarrow> ln (u powr (- 1 / \<xi>)) \<le> ln (1 / y)"
          by (rule ln_le_cancel_iff[symmetric]) auto
        also have "\<dots> \<longleftrightarrow> (- 1 / \<xi>) * ln u \<le> - ln y"
          by (simp add: ln_div)
        also have "\<dots> \<longleftrightarrow> \<xi> * ln y \<le> ln u"
          using 2 by (auto simp: field_simps)
        also have "\<dots> \<longleftrightarrow> ln (y powr \<xi>) \<le> ln u"
          by simp
        also have "\<dots> \<longleftrightarrow> y powr \<xi> \<le> u"
          by (rule ln_le_cancel_iff) auto
        also have "\<dots> \<longleftrightarrow> y powr \<xi> - 1 \<le> \<xi> * ((x - \<mu>) / \<sigma>)"
          by (simp add: u_def) linarith
        also have "\<dots> \<longleftrightarrow> ?xs \<le> x"
          using 2 by (simp add: field_simps)
        finally show ?thesis .
      next
        assume u:"\<not> 0 < u"
        have y:"0 < \<sigma> * y powr \<xi>"
          using yppos by simp
        show ?thesis
          using 2 u add_strict_increasing[OF y]
          by(auto simp: EVD_cdf_def Let_def u_def not_less not_le field_simps)
      qed
    next
      case 3
      define u where "u = 1 + \<xi> * ((x - \<mu>) / \<sigma>)"
      show ?thesis
      proof (cases "0 < u")
        case True
        have "?p \<le> EVD_cdf \<xi> \<mu> \<sigma> x \<longleftrightarrow> u powr (- 1 / \<xi>) \<le> 1 / y"
          using 3 True by (auto simp add: EVD_cdf_def Let_def u_def)
        also have "\<dots> \<longleftrightarrow> ln (u powr (- 1 / \<xi>)) \<le> ln (1 / y)"
          by (rule ln_le_cancel_iff[symmetric]) (use True in auto)
        also have "\<dots> \<longleftrightarrow> (- 1 / \<xi>) * ln u \<le> - ln y"
          by (simp add: ln_div)
        also have "\<dots> \<longleftrightarrow> ln u \<le> \<xi> * ln y"
          using 3 by (auto simp: field_simps)
        also have "\<dots> \<longleftrightarrow> ln u \<le> ln (y powr \<xi>)"
          by simp
        also have "\<dots> \<longleftrightarrow> u \<le> y powr \<xi>"
          by (rule ln_le_cancel_iff) (auto simp: True)
        also have "\<dots> \<longleftrightarrow> \<xi> * ((x - \<mu>) / \<sigma>) \<le> y powr \<xi> - 1"
          unfolding u_def by auto
        also have "\<dots> \<longleftrightarrow> ?xs \<le> x"
          using 3 by (simp add: field_simps)
        finally show ?thesis .
      next
        assume u:"\<not> 0 < u"
        have Gx: "EVD_cdf \<xi> \<mu> \<sigma> x = 1"
          using 3 u by (auto simp: EVD_cdf_def Let_def u_def not_less)
        have "\<xi> * ((x - \<mu>) / \<sigma>) < y powr \<xi> - 1"
          using u yppos unfolding u_def by linarith
        hence "\<sigma> * (y powr \<xi> - 1) / \<xi> + \<mu> \<le> x"
          using 3 by (simp add: field_simps)
        hence "?xs \<le> x"
          using 3 by simp
        moreover have "?p \<le> 1"
          by (auto intro!: less_imp_le)
        ultimately show ?thesis
          by (simp add: Gx)
      qed
    qed
  qed
  have set_eq: "{x. ?p \<le> EVD_cdf \<xi> \<mu> \<sigma> x} = {?xs..}"
    using iff by auto
  show ?thesis
    unfolding ginv_def set_eq by simp
qed

corollary isCont_limit_quantile_EVD_cdf:
  assumes sigma[arith]:"0 < \<sigma>"
    and ypos[arith]: "0 < y"
  shows "isCont (limit_quantile (EVD_cdf \<xi> \<mu> \<sigma>)) y"
proof(subst isCont_cong)
  show "\<forall>\<^sub>F x in nhds y.
       limit_quantile (EVD_cdf \<xi> \<mu> \<sigma>) x
       = (if \<xi> = 0 then \<sigma> * ln x + \<mu> else \<sigma> * (x powr \<xi> - 1) / \<xi> + \<mu>)"
    unfolding eventually_nhds
    by(auto intro!: exI[where x="{y/2<..<2*y}"] simp: limit_quantile_EVD_cdf)
next
  show "isCont (\<lambda>x. if \<xi> = 0 then \<sigma> * ln x + \<mu> else \<sigma> * (x powr \<xi> - 1) / \<xi> + \<mu>) y"
    by(cases "\<xi> = 0")
      (auto intro!: isCont_add isCont_mult isCont_ln isCont_divide isCont_diff
        simp: continuous_at_within_powr)
qed

lemma dist_function_unique_limit_quantile:
  assumes G:"right_continuous_mono G 0 1" and G':"right_continuous_mono G' 0 1"
    and eq:"\<And>y. 0 < y \<Longrightarrow> limit_quantile G y = limit_quantile G' y"
  shows "G = G'"
proof -
  have ginv_eq: "ginv G p = ginv G' p" if p: "0 < p" "p < 1" for p
    using eq[of "- 1 / ln p"] using p by simp
  have le: "H' x \<le> H x"
    if H: "right_continuous_mono H 0 1" and H': "right_continuous_mono H' 0 1"
      and geq: "\<And>p. 0 < p \<Longrightarrow> p < 1 \<Longrightarrow> ginv H p = ginv H' p"
    for H H' :: "real \<Rightarrow> real" and x
  proof (rule ccontr)
    interpret H: right_continuous_mono H 0 1
      by fact
    interpret H':right_continuous_mono H' 0 1
      by fact
    assume "\<not> H' x \<le> H x"
    hence lt: "H x < H' x"
      by simp
    define p where "p = (H x + H' x) / 2"
    have p1: "H x < p" "p < H' x"
      using lt by (simp_all add: p_def)
    have p0: "0 < p" "p < 1"
      using H.a_le_f[of x] p1 H'.f_le_b[of x]
      by auto
    have "ginv H' p \<le> x"
      using H'.ginv_le_iff p0 p1 by auto
    hence "ginv H p \<le> x"
      by (simp add: geq p0)
    with p1 show False
      by (simp add: H.ginv_le_iff p0(1,2))
  qed
  show ?thesis
    using le[OF G G' ginv_eq] le[OF G' G ginv_eq[symmetric]]
    by(auto dest: antisym)
qed

lemma isCont_ginv_iff_isCont_limit_quantile:
  assumes G: "right_continuous_mono G 0 1"
    and y: "0 < y"
  shows "isCont (ginv G) (exp (- (1 / y))) \<longleftrightarrow> isCont (limit_quantile G) y"
proof
  assume cont:"isCont (limit_quantile G) y"
  have 1: "isCont (\<lambda>x. - 1 / ln x) (exp (- 1 / y))"
    using y by (intro continuous_intros) simp_all
  have 2: "isCont (limit_quantile G) (- 1 / ln (exp (- 1 / y)))"
    using y by(simp add: cont)
  have 3: "\<forall>\<^sub>F p' in nhds (exp (- (1 / y))). limit_quantile G (- 1 / ln p') = ginv G p'"
    using eventually_nhds_in_open[of "{0<..<1}" "exp (- (1 / y))"] y
    by (auto elim!: eventually_mono)
  show "isCont (ginv G) (exp (- (1 / y)))"
    using continuous_at_compose[OF 1 2] isCont_cong[OF 3]
    by(auto simp: comp_def)
next
  assume cont:"isCont (ginv G) (exp (- (1 / y)))"
  show "isCont (limit_quantile G) y"
    using continuous_at_compose[where f="\<lambda>x. exp (- (1 / x))",OF _ cont] y
    by(simp add: comp_def)
qed

lemma seq_exp_quantile_tendsto:
  fixes F G :: "real \<Rightarrow> real" and a b :: "nat \<Rightarrow> real" and y :: real
  assumes F: "right_continuous_mono F 0 1" and G: "right_continuous_mono G 0 1"
    and a: "\<And>n. 0 < a n"
    and wc: "weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
    and y: "0 < y" and cont: "isCont (limit_quantile G) y"
  shows "(\<lambda>n. (limit_quantile F (real n * y) - b n) / a n) \<longlonglongrightarrow> limit_quantile G y"
proof -
  interpret G: right_continuous_mono G 0 1 by fact
  interpret F: right_continuous_mono F 0 1 by fact
  define p where "p = exp (- (1 / y))"
  have p01: "0 < p" "p < 1"
    using y by (auto simp: p_def)
  have cont': "isCont (ginv G) p"
    unfolding p_def using cont by(simp add: isCont_ginv_iff_isCont_limit_quantile[OF G y])
  obtain z where z: "p < G z"
    using order_tendstoD(1)[OF G.top p01(2)]
    by (auto dest!: eventually_happens'[OF trivial_limit_at_top_linorder])
  obtain w where w: "G w < p"
    using order_tendstoD(2)[OF G.bot p01(1)]
    by (auto dest!: eventually_happens'[OF trivial_limit_at_bot_linorder])
  have monoFn: "mono (\<lambda>x. F (a n * x + b n) ^ n)" for n
    using a by(auto intro!: monoI power_mono monoD[OF F.mono] F.a_le_f)
  have main: "(\<lambda>n. ginv (\<lambda>x. F (a n * x + b n) ^ n) p) \<longlonglongrightarrow> ginv G p"
    by (rule tendsto_ginv[OF monoFn G.mono _ cont' z w])
       (use wc in \<open>auto simp: weak_conv_def\<close>)
  have eq: "ginv (\<lambda>x. F (a n * x + b n) ^ n) p
              = (ginv F (exp (- 1 / (real n * y))) - b n) / a n" if n: "0 < n" for n
  proof -
    define qn where "qn = exp (- 1 / (real n * y))"
    have qn01: "0 < qn" "qn < 1"
      using n y by (auto simp: qn_def)
    have qn_pow: "qn ^ n = p"
      using n y by (simp add: qn_def p_def exp_of_nat_mult[symmetric])
    have iff1: "p \<le> F (a n * x + b n) ^ n \<longleftrightarrow> qn \<le> F (a n * x + b n)" for x
    proof
      assume "qn \<le> F (a n * x + b n)"
      hence "qn ^ n \<le> F (a n * x + b n) ^ n"
        using qn01(1) by (intro power_mono) auto
      thus "p \<le> F (a n * x + b n) ^ n"
        by (simp add: qn_pow)
    next
      assume *: "p \<le> F (a n * x + b n) ^ n"
      show "qn \<le> F (a n * x + b n)"
      proof (rule ccontr)
        assume "\<not> qn \<le> F (a n * x + b n)"
        hence "F (a n * x + b n) ^ n < qn ^ n"
          using F.a_le_f n by (intro power_strict_mono) auto
        with * show False
          by (simp add: qn_pow)
      qed
    qed
    have iff2: "qn \<le> F v \<longleftrightarrow> ginv F qn \<le> v" for v
      using F.ginv_le_iff[OF qn01] by simp
    have iff3: "ginv F qn \<le> a n * x + b n \<longleftrightarrow> (ginv F qn - b n) / a n \<le> x" for x
      using a[of n] by (auto simp: field_simps)
    have "{x. p \<le> F (a n * x + b n) ^ n} = {(ginv F qn - b n) / a n..}"
      by (auto simp: iff1 iff2 iff3)
    thus ?thesis
      by (simp add: ginv_def qn_def)
  qed
  have "(\<lambda>n. ginv (\<lambda>x. F (a n * x + b n) ^ n) p) \<longlonglongrightarrow> limit_quantile G y"
    using main by (simp add: p_def)
  moreover have "\<forall>\<^sub>F n in sequentially. ginv (\<lambda>x. F (a n * x + b n) ^ n) p
                                = (limit_quantile F (real n * y) - b n) / a n"
    using eventually_gt_at_top[of 0] by eventually_elim (simp add: eq)
  ultimately show ?thesis
    by (rule Lim_transform_eventually)
qed

lemma seq_tail_quantile_tendsto:
  fixes F G :: "real \<Rightarrow> real" and a b :: "nat \<Rightarrow> real" and y :: real
  assumes F:"right_continuous_mono F 0 1" and G:"right_continuous_mono G 0 1"
    and dg: "\<not> degenerate_df G"
    and a:"\<And>n. 0 < a n"
    and wc:"weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
    and y:"0 < y" and cont:"isCont (limit_quantile G) y"
  shows "(\<lambda>n. (tail_quantile F (real n * y) - b n) / a n) \<longlonglongrightarrow> limit_quantile G y"
proof (rule metric_LIMSEQ_I)
  interpret F: right_continuous_mono F 0 1 by fact
  interpret G: right_continuous_mono G 0 1 by fact
  fix \<epsilon> :: real
  assume eps: "0 < \<epsilon>"
  obtain \<delta> where \<delta>: "0 < \<delta>"
    "\<And>y''. y'' \<noteq> y \<and> \<bar>y'' - y\<bar> < \<delta> \<Longrightarrow> \<bar>limit_quantile G y'' - limit_quantile G y\<bar> < \<epsilon> / 2"
    using LIM_D[of _ _ _ "\<epsilon> / 2"] eps cont by (fastforce simp: isCont_def)
  have cd: "countable {s \<in> {0<..}. \<not> isCont (limit_quantile G) s}"
    by (intro mono_on_ctble_discont_open)
       (fastforce intro!: mono_onI limit_quantile_mono[OF G])+
  obtain y' where y': "y' \<in> {max (y - \<delta>) (y / 2)<..<y}"
    "y' \<notin> {s \<in> {0<..}. \<not> isCont (limit_quantile G) s}"
    using real_interval_avoid_countable_set[OF _ cd, of "max (y - \<delta>) (y / 2)" y] \<delta>(1) y
    by auto
  have y'1: "0 < y'" "y' < y" "\<bar>y' - y\<bar> < \<delta>"
    using y' y by auto
  have y'2: "isCont (limit_quantile G) y'"
    using y' y'1(1) by auto
  have y'3: "limit_quantile G y - \<epsilon> / 2 < limit_quantile G y'"
    using \<delta>(2)[of y'] y'1(2,3) by argo
  note L = seq_exp_quantile_tendsto[OF F G a wc y cont]
  note L' = seq_exp_quantile_tendsto[OF F G a wc y'1(1) y'2]
  have up: "\<forall>\<^sub>F n in sequentially. tail_quantile F (real n * y)
                           \<le> ginv F (exp (- 1 / (real n * y)))"
    using eventually_gt_at_top[of "nat \<lceil>1 / y\<rceil>"]
  proof eventually_elim
    case (elim n)
    have n1: "1 < real n * y"
    proof -
      have "real (nat \<lceil>1 / y\<rceil>) < real n"
        using elim by simp
      moreover have "1 / y \<le> real (nat \<lceil>1 / y\<rceil>)"
        by (rule real_nat_ceiling_ge)
      ultimately have "1 / y < real n"
        by simp
      thus ?thesis
        using y by (simp add: pos_divide_less_eq)
    qed
    have "1 - 1 / (real n * y) \<le> exp (- 1 / (real n * y))"
      using exp_ge_add_one_self[of "- 1 / (real n * y)"] by simp
    thus ?case
      using n1
      by (intro ginv_mono[OF F.mono] F.ex_less_a F.ex_ge_b) auto
  qed
  have low: "\<forall>\<^sub>F n in sequentially. ginv F (exp (- 1 / (real n * y')))
                           \<le> tail_quantile F (real n * y)"
  proof -
    have ev1: "\<forall>\<^sub>F n in sequentially. y' / y < exp (- 1 / (real n * y'))"
    proof (rule order_tendstoD(1))
      have "(\<lambda>n. - 1 / (real n * y')) \<longlonglongrightarrow> 0"
        using y'1(1) tendsto_mult[OF tendsto_const[of "- 1 / y'"] lim_1_over_n]
        by (auto simp: field_simps intro: Lim_transform_eventually)
      thus "(\<lambda>n. exp (- 1 / (real n * y'))) \<longlonglongrightarrow> 1"
        using tendsto_exp[of _ 0] by fastforce
      show "y' / y < 1"
        using y'1(1,2) y by simp
    qed
    show ?thesis
      using ev1 eventually_gt_at_top[of 0]
    proof eventually_elim
      case (elim n)
      define s where "s = 1 / (real n * y')"
      have s_pos: "0 < s"
        using elim y'1(1) by (auto simp: s_def)
      have ny_pos: "0 < real n * y"
        using elim y by auto
      have "exp s \<ge> 1 + s"
        by (rule exp_ge_add_one_self)
      hence "1 \<ge> (1 + s) * exp (- s)"
        using mult_right_mono[of "1 + s" "exp s" "exp (- s)"]
        by (simp add: exp_minus field_simps)
      hence *: "s * exp (- s) \<le> 1 - exp (- s)"
        by (simp add: algebra_simps)
      have "1 / (real n * y) = (y' / y) * s"
        using elim y'1(1) by (simp add: s_def field_simps)
      also have "\<dots> \<le> exp (- s) * s"
        using elim s_pos by (fastforce intro!: mult_right_mono simp: s_def)
      also have "\<dots> \<le> 1 - exp (- s)"
        using * by (simp add: mult.commute)
      finally have "exp (- 1 / (real n * y')) \<le> 1 - 1 / (real n * y)"
        by (simp add: s_def)
      moreover have "0 < exp (- 1 / (real n * y'))"
        by simp
      moreover have "1 - 1 / (real n * y) < 1"
        using ny_pos by simp
      ultimately show ?case
        by(intro ginv_mono[OF F.mono] F.ex_ge_b F.ex_less_a) auto
    qed
  qed

  have evlow: "\<forall>\<^sub>F n in sequentially. limit_quantile G y - \<epsilon>
                              < (tail_quantile F (real n * y) - b n) / a n"
  proof -
    have *:"\<forall>\<^sub>F n in sequentially. limit_quantile G y - \<epsilon>
                                      < ((limit_quantile F (real n * y')) - b n) / a n"
      using y'3 eps by (intro order_tendstoD(1)[OF L']) auto
    show ?thesis
      using a
      by(intro eventually_mono[OF eventually_conj[OF * low]])
        (smt (verit, ccfv_SIG) divide_minus_left divide_right_mono)
  qed
  have evup: "\<forall>\<^sub>F n in sequentially. (tail_quantile F (real n * y) - b n) / a n
                              < limit_quantile G y + \<epsilon>"
  proof -
    have *:"\<forall>\<^sub>F n in sequentially. ((limit_quantile F (real n * y)) - b n) / a n
                         < limit_quantile G y + \<epsilon>"
      using eps by (intro order_tendstoD(2)[OF L]) auto
    show ?thesis
      using a
      by(intro eventually_mono[OF eventually_conj[OF * up]])
        (smt (verit, ccfv_SIG) divide_right_mono_neg minus_divide_divide minus_divide_left)
  qed
  from evlow evup
  have "\<forall>\<^sub>F n in sequentially. dist ((tail_quantile F (real n * y) - b n) / a n)
                       (limit_quantile G y) < \<epsilon>"
    by eventually_elim (simp add: dist_real_def abs_diff_less_iff)
  thus "\<exists>no. \<forall>n\<ge>no. dist ((tail_quantile F (real n * y) - b n) / a n)
               (limit_quantile G y) < \<epsilon>"
    unfolding eventually_sequentially by blast
qed

lemma nondegenerate_growth_points:
  assumes G: "right_continuous_mono G 0 1" and deg: "\<not> degenerate_df G"
    and N: "countable N"
  obtains y1 y2 where "0 < y1" "y1 < y2" "y1 \<notin> N" "y2 \<notin> N"
    "isCont (limit_quantile G) y1" "isCont (limit_quantile G) y2"
    "limit_quantile G y1 < limit_quantile G y2"
proof -
  interpret G: right_continuous_mono G 0 1
    by fact
  obtain x0 where x0: "0 < G x0" "G x0 < 1"
  proof -
    from deg obtain x0 where "G x0 \<noteq> 0" "G x0 \<noteq> 1"
      by (auto simp: degenerate_df_def)
    thus thesis
      using G.a_le_f[of x0] G.f_le_b[of x0]
      by (intro that[of x0]) auto
  qed
  define p1 where "p1 = G x0"
  define p2 where "p2 = (G x0 + 1) / 2"
  have p12: "0 < p1" "p1 < p2" "p2 < 1"
    using x0 by (auto simp: p1_def p2_def)
  define v1 where "v1 = - 1 / ln p1"
  define v2 where "v2 = - 1 / ln p2"
  have ln1: "ln p1 < 0" and ln2: "ln p2 < 0"
    using p12 by auto
  have v1pos: "0 < v1"
    unfolding v1_def using ln1 by simp
  have v2pos: "0 < v2"
    unfolding v2_def using ln2 by simp
  have exp1: "exp (- 1 / v1) = p1"
    using ln1 p12(1) by (simp add: v1_def)
  have exp2: "exp (- 1 / v2) = p2"
    using ln2 p12 by (simp add: v2_def)
  have v12: "v1 < v2"
  proof -
    have *: "ln p1 < ln p2"
      using p12 by simp
    have "v1 = 1 / (- ln p1)" "v2 = 1 / (- ln p2)"
      by (simp_all add: v1_def v2_def)
    moreover have "1 / (- ln p1) < 1 / (- ln p2)"
      using * ln1 ln2 by (intro divide_strict_left_mono)
       (auto simp: zero_less_mult_iff)
    ultimately show ?thesis
      by simp
  qed
  have Dv1: "limit_quantile G v1 \<le> x0"
    using G.ginv_le_iff[of p1 x0] p12 exp1
    by (simp add: p1_def)
  have Dv2: "x0 < limit_quantile G v2"
  proof -
    have "\<not> ginv G p2 \<le> x0"
      using G.ginv_le_iff[of p2 x0] p12
      by (simp add: p1_def[symmetric])
    thus ?thesis
      using exp2 by simp
  qed
  have cd: "countable (N \<union> {s \<in> {0<..}. \<not> isCont (limit_quantile G) s})"
    using N
    by (intro countable_Un mono_on_ctble_discont_open)
       (fastforce intro!: mono_onI limit_quantile_mono[OF G])+
  obtain y1 where y1: "y1 \<in> {v1 / 2<..<v1}"
    "y1 \<notin> N \<union> {s \<in> {0<..}. \<not> isCont (limit_quantile G) s}"
    using real_interval_avoid_countable_set[OF _ cd, of "v1 / 2" v1] v1pos by auto
  obtain y2 where y2: "y2 \<in> {v2<..<v2 + 1}"
    "y2 \<notin> N \<union> {s \<in> {0<..}. \<not> isCont (limit_quantile G) s}"
    using real_interval_avoid_countable_set[OF _ cd, of v2 "v2 + 1"] by auto
  have y1f: "0 < y1" "y1 < v1"
    using y1(1) v1pos by auto
  have y2f: "0 < y2" "v2 < y2"
    using y2(1) v2pos by auto
  show ?thesis
  proof (rule that[of y1 y2])
    show "0 < y1"
      by fact
    show "y1 < y2"
      using y1f y2f v12 by simp
    show "y1 \<notin> N" "y2 \<notin> N"
      using y1(2) y2(2) by auto
    show "isCont (limit_quantile G) y1" "isCont (limit_quantile G) y2"
      using y1 y2 y1f(1) y2f(1) by auto
    have "limit_quantile G y1 \<le> limit_quantile G v1"
      using y1f by (intro limit_quantile_mono[OF G]) auto
    moreover have "limit_quantile G v2 \<le> limit_quantile G y2"
      using y2f v2pos by (intro limit_quantile_mono[OF G]) auto
    ultimately show "limit_quantile G y1 < limit_quantile G y2"
      using Dv1 Dv2 by simp
  qed
qed

lemma
  fixes F G :: "real \<Rightarrow> real" and a b :: "nat \<Rightarrow> real"
  assumes F:"right_continuous_mono F 0 1" and G:"right_continuous_mono G 0 1"
    and deg:"\<not> degenerate_df G"
    and a:"\<And>n. 0 < a n"
    and wc:"weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
  shows normalizing_ratio1:"(\<lambda>n. a (Suc n) / a n) \<longlonglongrightarrow> 1"
    and normalizing_ratio2:"(\<lambda>n. (b (Suc n) - b n) / a n) \<longlonglongrightarrow> 0"
proof -
  have er:"\<And>c. \<forall>\<^sub>F n in sequentially. c \<le> real n"
    using filterlim_real_sequentially unfolding filterlim_at_top by blast
  obtain y1 y2 where y12: "0 < y1" "y1 < y2"
    and cont12: "isCont (limit_quantile G) y1" "isCont (limit_quantile G) y2"
    and D12: "limit_quantile G y1 < limit_quantile G y2"
    by (rule nondegenerate_growth_points[OF G deg countable_empty]) auto
  have y2pos: "0 < y2"
    using y12 by simp
  have base: "(\<lambda>n. (tail_quantile F (real n * z) - b n) / a n) \<longlonglongrightarrow> limit_quantile G z"
    if z: "0 < z" "isCont (limit_quantile G) z" for z
    by (rule seq_tail_quantile_tendsto[OF F G deg a wc z])
  have shifted: "(\<lambda>n. (tail_quantile F (real n * z) - b (Suc n)) / a (Suc n))
                   \<longlonglongrightarrow> limit_quantile G z"
    if z: "0 < z" "isCont (limit_quantile G) z" for z
  proof (rule squeeze_tendsto_cont_points_pos[where
        gr = "\<lambda>y' n. (tail_quantile F (real (Suc n) * y') - b (Suc n)) / a (Suc n)"
        and f = "limit_quantile G", OF _ z])
    show "mono_on {0<..} (limit_quantile G)"
      by (auto intro!: mono_onI limit_quantile_mono[OF G])
  next
    fix y' :: real
    assume y': "0 < y'" "isCont (limit_quantile G) y'"
    show "(\<lambda>n. (tail_quantile F (real (Suc n) * y') - b (Suc n)) / a (Suc n))
            \<longlonglongrightarrow> limit_quantile G y'"
      by (intro LIMSEQ_Suc base y')
  next
    fix y' :: real
    assume y': "0 < y'" "y' < z"
    show "\<forall>\<^sub>F n in sequentially. (tail_quantile F (real (Suc n) * y') - b (Suc n)) / a (Suc n)
                         \<le> (tail_quantile F (real n * z) - b (Suc n)) / a (Suc n)"
      using er[of "max (y' / (z - y')) (1 / y')"]
    proof eventually_elim
      case h:(elim n)
      have 1: "1 < real (Suc n) * y'"
      proof -
        have "1 = (1 / y') * y'"
          using y'(1) by simp
        also have "\<dots> \<le> real n * y'"
          using h y'(1) by (intro mult_right_mono) auto
        also have "\<dots> < real (Suc n) * y'"
          using y'(1) by simp
        finally show ?thesis .
      qed
      have 2: "real (Suc n) * y' \<le> real n * z"
      proof -
        have "y' / (z - y') \<le> real n"
          using h by simp
        hence "y' \<le> real n * (z - y')"
          using y' by (simp add: field_simps)
        thus ?thesis
          by (simp add: algebra_simps)
      qed
      have "tail_quantile F (real (Suc n) * y') \<le> tail_quantile F (real n * z)"
        by (rule tail_quantile_mono[OF F 1 2])
      thus ?case
        using a[of "Suc n"] by (auto intro!: divide_right_mono)
    qed
  next
    fix y' :: real
    assume y': "z < y'"
    show "\<forall>\<^sub>F n in sequentially. (tail_quantile F (real n * z) - b (Suc n)) / a (Suc n)
                         \<le> (tail_quantile F (real (Suc n) * y') - b (Suc n)) / a (Suc n)"
      using er[of "1 / z + 1"]
    proof eventually_elim
      case (elim n)
      have zpos: "0 < z"
        using z by simp
      have 1: "1 < real n * z"
      proof -
        have "1 < (1 / z + 1) * z"
          using zpos by (simp add: field_simps)
        also have "\<dots> \<le> real n * z"
          using elim zpos by (intro mult_right_mono) auto
        finally show ?thesis .
      qed
      have 2: "real n * z \<le> real (Suc n) * y'"
        using y' zpos by (intro mult_mono) auto
      have "tail_quantile F (real n * z) \<le> tail_quantile F (real (Suc n) * y')"
        by (rule tail_quantile_mono[OF F 1 2])
      thus ?case
        using a[of "Suc n"] by (auto intro!: divide_right_mono)
    qed
  qed
  note B1 = base[OF y12(1) cont12(1)] and B2 = base[OF y2pos cont12(2)]
  note S1 = shifted[OF y12(1) cont12(1)] and S2 = shifted[OF y2pos cont12(2)]
  define D where "D = limit_quantile G y2 - limit_quantile G y1"
  have D_pos: "0 < D"
    using D12 by (simp add: D_def)
  have d1: "(\<lambda>n. (tail_quantile F (real n * y2) - tail_quantile F (real n * y1)) / a n)
              \<longlonglongrightarrow> D"
    using tendsto_diff[OF B2 B1]
    by (simp add: diff_divide_distrib D_def)
  have d2: "(\<lambda>n. (tail_quantile F (real n * y2) - tail_quantile F (real n * y1)) / a (Suc n))
              \<longlonglongrightarrow> D"
    using tendsto_diff[OF S2 S1]
    by (simp add: diff_divide_distrib D_def)
  have ev_pos: "\<forall>\<^sub>F n in sequentially. 0 < (tail_quantile F (real n * y2)
                               - tail_quantile F (real n * y1)) / a n"
    using order_tendstoD(1)[OF d1 D_pos] .
  show r1: "(\<lambda>n. a (Suc n) / a n) \<longlonglongrightarrow> 1"
  proof -
    have "(\<lambda>n. ((tail_quantile F (real n * y2) - tail_quantile F (real n * y1)) / a n)
             / ((tail_quantile F (real n * y2) - tail_quantile F (real n * y1)) / a (Suc n)))
            \<longlonglongrightarrow> D / D"
      using D_pos by (intro tendsto_divide d1 d2) auto
    hence *: "(\<lambda>n. ((tail_quantile F (real n * y2) - tail_quantile F (real n * y1)) / a n)
             / ((tail_quantile F (real n * y2) - tail_quantile F (real n * y1)) / a (Suc n)))
            \<longlonglongrightarrow> 1"
      using D_pos by simp
    have "\<forall>\<^sub>F n in sequentially. ((tail_quantile F (real n * y2)
                          - tail_quantile F (real n * y1)) / a n)
                          / ((tail_quantile F (real n * y2)
                               - tail_quantile F (real n * y1)) / a (Suc n))
                          = a (Suc n) / a n"
      using ev_pos
    proof eventually_elim
      case (elim n)
      have "0 < tail_quantile F (real n * y2) - tail_quantile F (real n * y1)"
        using elim a[of n] by (simp add: zero_less_divide_iff)
      thus ?case
        using a[of n] a[of "Suc n"] by (auto simp: field_simps)
    qed
    from Lim_transform_eventually[OF * this]
    show ?thesis .
  qed
  have eq: "(tail_quantile F (real n * y1) - b n) / a n
            - ((tail_quantile F (real n * y1) - b (Suc n)) / a (Suc n)) * (a (Suc n) / a n)
            = (b (Suc n) - b n) / a n" for n
    using  a[of n] a[of "Suc n"] by (simp add: field_simps)
  have "(\<lambda>n. (tail_quantile F (real n * y1) - b n) / a n
            - ((tail_quantile F (real n * y1) - b (Suc n)) / a (Suc n)) * (a (Suc n) / a n))
            \<longlonglongrightarrow> limit_quantile G y1 - limit_quantile G y1 * 1"
    by (intro tendsto_diff tendsto_mult B1 S1 r1)
  thus "(\<lambda>n. (b (Suc n) - b n) / a n) \<longlonglongrightarrow> 0"
    unfolding eq by simp
qed

lemma real_tail_quantile_tendsto:
  fixes F G :: "real \<Rightarrow> real" and a b :: "nat \<Rightarrow> real" and y :: real
  assumes F:"right_continuous_mono F 0 1" and G:"right_continuous_mono G 0 1"
    and deg:"\<not> degenerate_df G"
    and a:"\<And>n. 0 < a n"
    and wc:"weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
    and y:"0 < y" and cont:"isCont (limit_quantile G) y"
  shows "((\<lambda>t. (tail_quantile F (t * y) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
           \<longlongrightarrow> limit_quantile G y) at_top"
proof -
  note nf = filterlim_compose[OF filterlim_nat_sequentially filterlim_floor_sequentially]
  note nf_real = filterlim_compose[OF filterlim_real_sequentially nf]
  have ev_nf: "\<forall>\<^sub>F t::real in at_top. c \<le> real (nat \<lfloor>t\<rfloor>)" for c
    using nf_real unfolding filterlim_at_top by blast
  show ?thesis
  proof (rule squeeze_tendsto_cont_points_pos[where
        gr = "\<lambda>y' t. (tail_quantile F (real (nat \<lfloor>t\<rfloor>) * y') - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)"
        and f = "limit_quantile G", OF _ y cont])
    show "mono_on {0<..} (limit_quantile G)"
      by (auto intro!: mono_onI limit_quantile_mono[OF G])
  next
    fix y' :: real
    assume y': "0 < y'" "isCont (limit_quantile G) y'"
    show "((\<lambda>t. (tail_quantile F (real (nat \<lfloor>t\<rfloor>) * y') - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
            \<longlongrightarrow> limit_quantile G y') at_top"
      using filterlim_compose[OF seq_tail_quantile_tendsto[OF F G deg a wc y'] nf]
      by simp
  next
    fix y' :: real
    assume y'1: "0 < y'" and y'2: "y' < y"
    show "\<forall>\<^sub>F t in at_top. (tail_quantile F (real (nat \<lfloor>t\<rfloor>) * y') - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)
                   \<le> (tail_quantile F (t * y) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)"
      using ev_nf[of "1 / y' + 1"] eventually_ge_at_top[of 0]
    proof eventually_elim
      case (elim t)
      have 1: "1 < real (nat \<lfloor>t\<rfloor>) * y'"
      proof -
        have "1 < (1 / y' + 1) * y'"
          using y'1 by (simp add: field_simps)
        also have "\<dots> \<le> real (nat \<lfloor>t\<rfloor>) * y'"
          using elim y'1 by (intro mult_right_mono) auto
        finally show ?thesis .
      qed
      have "real (nat \<lfloor>t\<rfloor>) \<le> t"
        using elim by linarith
      hence 2: "real (nat \<lfloor>t\<rfloor>) * y' \<le> t * y"
        using y'1 y'2 y elim by (intro mult_mono) auto
      have "tail_quantile F (real (nat \<lfloor>t\<rfloor>) * y') \<le> tail_quantile F (t * y)"
        by (rule tail_quantile_mono[OF F 1 2])
      thus ?case
        using a[of "nat \<lfloor>t\<rfloor>"] by (auto intro!: divide_right_mono)
    qed
  next
    fix y' :: real
    assume y': "y < y'"
    show "\<forall>\<^sub>F t in at_top. (tail_quantile F (t * y) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)
                   \<le> (tail_quantile F (real (nat \<lfloor>t\<rfloor>) * y') - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)"
      using ev_nf[of "y / (y' - y)"] eventually_gt_at_top[of "1 / y"]
    proof eventually_elim
      case (elim t)
      have t_pos: "0 < t"
        using elim(2) y zero_less_divide_1_iff[of y] by linarith
      have 1: "1 < t * y"
        using elim(2) y by (simp add: field_simps)
      have 2: "t * y \<le> real (nat \<lfloor>t\<rfloor>) * y'"
      proof -
        have "t \<le> real (nat \<lfloor>t\<rfloor>) + 1"
          using t_pos by linarith
        hence "t * y \<le> (real (nat \<lfloor>t\<rfloor>) + 1) * y"
          using y by (intro mult_right_mono) auto
        also have "\<dots> \<le> real (nat \<lfloor>t\<rfloor>) * y'"
          using elim(1) y' y by (simp add: field_simps)
        finally show ?thesis .
      qed
      show ?case
        using a[of "nat \<lfloor>t\<rfloor>"] tail_quantile_mono[OF F 1 2]
        by (auto intro!: divide_right_mono)
    qed
  qed
qed

lemma scaling_limits_ex:
  fixes F G :: "real \<Rightarrow> real" and a b :: "nat \<Rightarrow> real"
  assumes F:"right_continuous_mono F 0 1" and G:"right_continuous_mono G 0 1"
    and deg: "\<not> degenerate_df G"
    and a:"\<And>n. 0 < a n"
    and wc:"weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
  obtains A B where
    "\<And>y. 0 < y \<Longrightarrow> 0 < A y"
    and "\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> A y) at_top"
    and "\<And>y. 0 < y \<Longrightarrow>
           ((\<lambda>t. (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> B y) at_top"
    and "A \<in> borel_measurable (restrict_space borel {0<..})"
    and "\<And>x y. 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> A (x * y) = A x * A y"
    and "\<And>x y. 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> isCont (limit_quantile G) x
          \<Longrightarrow> isCont (limit_quantile G) (x * y)
          \<Longrightarrow> limit_quantile G (x * y) = limit_quantile G x * A y + B y"
proof -
  have RT: "((\<lambda>t. (tail_quantile F (t * s) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
              \<longlongrightarrow> limit_quantile G s) at_top"
    if "0 < s" "isCont (limit_quantile G) s" for s
    by (rule real_tail_quantile_tendsto[OF F G deg a wc that])
  have mult_top: "filterlim (\<lambda>t::real. t * y) at_top at_top" if "0 < y" for y :: real
    using filterlim_tendsto_pos_mult_at_top[OF tendsto_const that filterlim_ident]
    by (simp add: mult.commute)
  have RTy: "((\<lambda>t. (tail_quantile F (t * y * s) - b (nat \<lfloor>t * y\<rfloor>)) / a (nat \<lfloor>t * y\<rfloor>))
               \<longlongrightarrow> limit_quantile G s) at_top"
    if y: "0 < y" and s: "0 < s" "isCont (limit_quantile G) s" for y s
    by (rule filterlim_compose[OF RT[OF s] mult_top[OF y]])
  have ex: "\<exists>L M. 0 \<le> L \<and>
             ((\<lambda>t. a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> L) at_top \<and>
             ((\<lambda>t. (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> M) at_top"
    if y: "0 < y" for y :: real
  proof -
    have cN: "countable {s \<in> {0<..}. \<not> isCont (limit_quantile G) (y * s)}"
    proof -
      have *: "countable {u \<in> {0<..}. \<not> isCont (limit_quantile G) u}"
        by (intro mono_on_ctble_discont_open)
           (fastforce intro!: mono_onI limit_quantile_mono[OF G])+
      have sub: "{s \<in> {0<..}. \<not> isCont (limit_quantile G) (y * s)}
              \<subseteq> (\<lambda>u. u / y) ` {u \<in> {0<..}. \<not> isCont (limit_quantile G) u}"
      proof
        fix s
        assume s: "s \<in> {s \<in> {0<..}. \<not> isCont (limit_quantile G) (y * s)}"
        hence "y * s \<in> {u \<in> {0<..}. \<not> isCont (limit_quantile G) u}"
          using y by auto
        moreover have "s = (y * s) / y"
          using y by simp
        ultimately show "s \<in> (\<lambda>u. u / y) ` {u \<in> {0<..}. \<not> isCont (limit_quantile G) u}"
          by blast
      qed
      show ?thesis
        by (rule countable_subset[OF sub countable_image[OF *]])
    qed
    obtain s1 s2 where s12: "0 < s1" "s1 < s2"
      and nn: "s1 \<notin> {s \<in> {0<..}. \<not> isCont (limit_quantile G) (y * s)}"
        "s2 \<notin> {s \<in> {0<..}. \<not> isCont (limit_quantile G) (y * s)}"
      and cs: "isCont (limit_quantile G) s1" "isCont (limit_quantile G) s2"
      and Ds: "limit_quantile G s1 < limit_quantile G s2"
      by (rule nondegenerate_growth_points[OF G deg cN])
    have s2pos: "0 < s2"
      using s12 by simp
    have cys: "isCont (limit_quantile G) (y * s1)" "isCont (limit_quantile G) (y * s2)"
      using nn s12 s2pos by auto
    have ys_pos: "0 < y * s1" "0 < y * s2"
      using y s12 s2pos by auto
    have P1: "((\<lambda>t. (tail_quantile F (t * y * s1) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                \<longlongrightarrow> limit_quantile G (y * s1)) at_top"
      using RT[OF ys_pos(1) cys(1)] by (simp add: mult.assoc)
    have P2: "((\<lambda>t. (tail_quantile F (t * y * s2) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                \<longlongrightarrow> limit_quantile G (y * s2)) at_top"
      using RT[OF ys_pos(2) cys(2)] by (simp add: mult.assoc)
    note Q1 = RTy[OF y s12(1) cs(1)] and Q2 = RTy[OF y s2pos cs(2)]
    define d where "d = limit_quantile G s2 - limit_quantile G s1"
    have d_pos: "0 < d"
      using Ds by (simp add: d_def)
    have Qdiff: "((\<lambda>t. (tail_quantile F (t * y * s2) - tail_quantile F (t * y * s1))
                    / a (nat \<lfloor>t * y\<rfloor>)) \<longlongrightarrow> d) at_top"
      using tendsto_diff[OF Q2 Q1] by (simp add: diff_divide_distrib d_def)
    have Pdiff: "((\<lambda>t. (tail_quantile F (t * y * s2) - tail_quantile F (t * y * s1))
                    / a (nat \<lfloor>t\<rfloor>))
                  \<longlongrightarrow> limit_quantile G (y * s2) - limit_quantile G (y * s1)) at_top"
      using tendsto_diff[OF P2 P1] by (simp add: diff_divide_distrib)
    have ev_pos: "\<forall>\<^sub>F t in at_top. 0 < (tail_quantile F (t * y * s2)
                           - tail_quantile F (t * y * s1)) / a (nat \<lfloor>t * y\<rfloor>)"
      using order_tendstoD(1)[OF Qdiff d_pos] .
    define L where "L = (limit_quantile G (y * s2) - limit_quantile G (y * s1)) / d"
    have Alim: "((\<lambda>t. a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> L) at_top"
    proof -
      have *: "((\<lambda>t. ((tail_quantile F (t * y * s2) - tail_quantile F (t * y * s1))
                  / a (nat \<lfloor>t\<rfloor>))
                / ((tail_quantile F (t * y * s2) - tail_quantile F (t * y * s1))
                  / a (nat \<lfloor>t * y\<rfloor>))) \<longlongrightarrow> L) at_top"
        unfolding L_def using d_pos by (intro tendsto_divide Pdiff Qdiff) auto
      have "\<forall>\<^sub>F t in at_top. ((tail_quantile F (t * y * s2) - tail_quantile F (t * y * s1))
                         / a (nat \<lfloor>t\<rfloor>))
                       / ((tail_quantile F (t * y * s2) - tail_quantile F (t * y * s1))
                         / a (nat \<lfloor>t * y\<rfloor>)) = a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)"
        using ev_pos
      proof eventually_elim
        case (elim t)
        have "0 < tail_quantile F (t * y * s2) - tail_quantile F (t * y * s1)"
          using elim a[of "nat \<lfloor>t * y\<rfloor>"] by (simp add: zero_less_divide_iff)
        thus ?case
          using a[of "nat \<lfloor>t\<rfloor>"] a[of "nat \<lfloor>t * y\<rfloor>"] by (auto simp: field_simps)
      qed
      from Lim_transform_eventually[OF * this]
      show ?thesis .
    qed
    have L_nonneg: "0 \<le> L"
      using a
      by(auto intro!: tendsto_lowerbound[OF Alim] always_eventually less_imp_le[of _ "_ / _"])
    have Blim: "((\<lambda>t. (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                  \<longlongrightarrow> limit_quantile G (y * s1) - limit_quantile G s1 * L) at_top"
    proof -
      have eq: "(tail_quantile F (t * y * s1) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)
            - ((tail_quantile F (t * y * s1) - b (nat \<lfloor>t * y\<rfloor>)) / a (nat \<lfloor>t * y\<rfloor>))
              * (a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>))
            = (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)" for t
        using a[of "nat \<lfloor>t\<rfloor>"] a[of "nat \<lfloor>t * y\<rfloor>"] by (simp add: field_simps)
      have "((\<lambda>t. (tail_quantile F (t * y * s1) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)
              - ((tail_quantile F (t * y * s1) - b (nat \<lfloor>t * y\<rfloor>)) / a (nat \<lfloor>t * y\<rfloor>))
                * (a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)))
              \<longlongrightarrow> limit_quantile G (y * s1) - limit_quantile G s1 * L) at_top"
        by (intro tendsto_diff tendsto_mult P1 Q1 Alim)
      thus ?thesis
        unfolding eq .
    qed
    show ?thesis
      using L_nonneg Alim Blim by blast
  qed
  define A where "A = (\<lambda>y::real. Lim at_top (\<lambda>t. a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)))"
  define B where "B = (\<lambda>y::real. Lim at_top (\<lambda>t. (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)))"
  have AB: "0 \<le> A y \<and>
      ((\<lambda>t. a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> A y) at_top \<and>
      ((\<lambda>t. (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> B y) at_top"
    if y: "0 < y" for y
  proof -
    obtain L M where LM: "0 \<le> L"
      "((\<lambda>t. a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> L) at_top"
      "((\<lambda>t. (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> M) at_top"
      using ex[OF y] by blast
    have "A y = L"
      unfolding A_def by (intro tendsto_Lim LM(2)) simp
    moreover have "B y = M"
      unfolding B_def by (intro tendsto_Lim LM(3)) simp
    ultimately show ?thesis
      using LM by simp
  qed
  have Anonneg: "0 \<le> A y" if "0 < y" for y
    using AB[OF that] by blast
  have Atend: "((\<lambda>t. a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> A y) at_top" if "0 < y" for y
    using AB[OF that] by blast
  have Btend: "((\<lambda>t. (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> B y) at_top"
    if "0 < y" for y
    using AB[OF that] by blast
  have Amul: "A (x * y) = A x * A y" if x: "0 < x" and y: "0 < y" for x y
  proof -
    have 1: "((\<lambda>t. a (nat \<lfloor>t * (x * y)\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> A (x * y)) at_top"
      using x y by (intro Atend) auto
    have "((\<lambda>t. (a (nat \<lfloor>t * x * y\<rfloor>) / a (nat \<lfloor>t * x\<rfloor>))
             * (a (nat \<lfloor>t * x\<rfloor>) / a (nat \<lfloor>t\<rfloor>))) \<longlongrightarrow> A y * A x) at_top"
      by (intro tendsto_mult Atend[OF x] filterlim_compose[OF Atend[OF y] mult_top[OF x]])
    moreover have "(a (nat \<lfloor>t * x * y\<rfloor>) / a (nat \<lfloor>t * x\<rfloor>))
             * (a (nat \<lfloor>t * x\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) = a (nat \<lfloor>t * x * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)"
      for t
      using a[of "nat \<lfloor>t * x\<rfloor>"] by (auto simp: field_simps)
    ultimately have "((\<lambda>t::real. a (nat \<lfloor>t * x * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> A y * A x) at_top"
      by (metis (no_types, lifting) ext)
    hence "((\<lambda>t. a (nat \<lfloor>t * (x * y)\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> A y * A x) at_top"
      by (simp add: mult.assoc)
    from tendsto_unique[OF _ 1 this]
    show ?thesis
      by (simp add: mult.commute)
  qed
  have A1: "A 1 = 1"
  proof -
    have "(\<lambda>t::real. a (nat \<lfloor>t * 1\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) = (\<lambda>t. 1)"
      using a
      by (metis divide_self_if less_irrefl mult.comm_neutral)
    hence "((\<lambda>t::real. a (nat \<lfloor>t * 1\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> 1) at_top"
      by simp
    from tendsto_unique[OF _ Atend[of 1] this]
    show ?thesis
      by simp
  qed
  have Apos: "0 < A y" if y: "0 < y" for y
  proof -
    have "A (y * (1 / y)) = A y * A (1 / y)"
      using y by (intro Amul) auto
    moreover have "y * (1 / y) = 1"
      using y by simp
    ultimately have "A y * A (1 / y) = 1"
      using A1 by simp
    hence "A y \<noteq> 0"
      by auto
    with Anonneg[OF y] show ?thesis
      by simp
  qed
  have Deq: "limit_quantile G (x * y) = limit_quantile G x * A y + B y"
    if x: "0 < x" and y: "0 < y"
      and cx: "isCont (limit_quantile G) x" and cxy: "isCont (limit_quantile G) (x * y)"
    for x y
  proof -
    have xy: "0 < x * y"
      using x y by simp
    have eq: "((tail_quantile F (t * y * x) - b (nat \<lfloor>t * y\<rfloor>)) / a (nat \<lfloor>t * y\<rfloor>))
            * (a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>))
            + (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)
            = (tail_quantile F (t * y * x) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)" for t
      using a[of "nat \<lfloor>t\<rfloor>"] a[of "nat \<lfloor>t * y\<rfloor>"] by (simp add: field_simps)
    have "((\<lambda>t. ((tail_quantile F (t * y * x) - b (nat \<lfloor>t * y\<rfloor>)) / a (nat \<lfloor>t * y\<rfloor>))
             * (a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>))
             + (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
             \<longlongrightarrow> limit_quantile G x * A y + B y) at_top"
      by (intro tendsto_add tendsto_mult RTy[OF y x cx] Atend[OF y] Btend[OF y])
    hence "((\<lambda>t. (tail_quantile F (t * (x * y)) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
             \<longlongrightarrow> limit_quantile G x * A y + B y) at_top"
      unfolding eq by (simp add: ac_simps)
    from tendsto_unique[OF _ RT[OF xy cxy] this]
    show ?thesis
      by simp
  qed
  have Ameas: "A \<in> borel_measurable (restrict_space borel {0<..})"
  proof (rule borel_measurable_LIMSEQ_real)
    fix i :: nat
    show "(\<lambda>y::real. a (nat \<lfloor>real i * y\<rfloor>) / a (nat \<lfloor>real i\<rfloor>))
            \<in> borel_measurable (restrict_space borel {0<..})"
      by(auto intro!: measurable_restrict_space1)
  next
    fix y::real
    assume "y \<in> space (restrict_space borel {0<..})"
    hence y: "0 < y"
      by (simp add: space_restrict_space)
    have "((\<lambda>i. a (nat \<lfloor>real i * y\<rfloor>) / a (nat \<lfloor>real i\<rfloor>)) \<longlongrightarrow> A y) sequentially"
      by (rule filterlim_compose[OF Atend[OF y] filterlim_real_sequentially])
    thus "(\<lambda>i. a (nat \<lfloor>real i * y\<rfloor>) / a (nat \<lfloor>real i\<rfloor>)) \<longlonglongrightarrow> A y" .
  qed
  show ?thesis
    by (rule that[of A B]) (fact Apos Atend Btend Ameas Amul Deq)+
qed

theorem limit_quantile_form:
  fixes F G :: "real \<Rightarrow> real" and a b :: "nat \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and G: "right_continuous_mono G 0 1"
    and deg: "\<not> degenerate_df G"
    and a: "\<And>n. 0 < a n"
    and wc: "weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
  obtains \<gamma> c d where "0 < c"
    and "\<And>y. 0 < y \<Longrightarrow> limit_quantile G y
            = (if \<gamma> = 0 then c * ln y + d else c * (y powr \<gamma> - 1) / \<gamma> + d)"
proof -
  obtain A B where Apos: "\<And>y. 0 < y \<Longrightarrow> 0 < A y"
    and Atend: "\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. a (nat \<lfloor>t * y\<rfloor>) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> A y) at_top"
    and Btend: "\<And>y. 0 < y \<Longrightarrow>
           ((\<lambda>t. (b (nat \<lfloor>t * y\<rfloor>) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)) \<longlongrightarrow> B y) at_top"
    and Ameas: "A \<in> borel_measurable (restrict_space borel {0<..})"
    and Amul: "\<And>x y. 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> A (x * y) = A x * A y"
    and Deq: "\<And>x y. 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> isCont (limit_quantile G) x
          \<Longrightarrow> isCont (limit_quantile G) (x * y)
          \<Longrightarrow> limit_quantile G (x * y) = limit_quantile G x * A y + B y"
    by (rule scaling_limits_ex[OF F G deg a wc]) auto
  obtain \<gamma> where Aform: "\<And>x. 0 < x \<Longrightarrow> A x = x powr \<gamma>"
    by (rule multiplicative_measurable_powr[where A=A,OF Ameas Apos Amul]) auto
  have Nx_ctble: "countable {s \<in> {0<..}. \<not> isCont (limit_quantile G) s}"
    by (intro mono_on_ctble_discont_open)
       (fastforce intro!: mono_onI limit_quantile_mono[OF G])+
  have DeqFull: "limit_quantile G (x * y) = limit_quantile G x * A y + B y"
    if x: "0 < x" and y: "0 < y" for x y
  proof -
    define Nx where "Nx = {s \<in> {0<..}. \<not> isCont (limit_quantile G) s}"
    have Nx_ctble': "countable Nx"
      unfolding Nx_def by (rule Nx_ctble)
    define N where "N = Nx \<union> (\<lambda>s. s / y) ` Nx"
    have N_ctble: "countable N"
      unfolding N_def using Nx_ctble' by (intro countable_Un countable_image) auto
    define f where "f = (\<lambda>x. limit_quantile G (x * y))"
    define h where "h = (\<lambda>x. limit_quantile G x * A y + B y)"
    have eq0: "f x' = h x'" if x'pos: "0 < x'" and x'N: "x' \<notin> N" for x'
    proof -
      have cx': "isCont (limit_quantile G) x'"
        using x'N x'pos by (auto simp: N_def Nx_def)
      have cxy': "isCont (limit_quantile G) (x' * y)"
      proof (rule ccontr)
        assume "\<not> isCont (limit_quantile G) (x' * y)"
        hence "(x' * y) / y \<in> (\<lambda>s. s / y) ` Nx"
          using x'pos y unfolding Nx_def by fastforce
        hence "x' \<in> N"
          using y by (auto simp add: N_def)
        with x'N show False
          by simp
      qed
      show ?thesis
        unfolding f_def h_def using Deq[OF x'pos y cx' cxy'] .
    qed
    have left_cont_f: "(f \<longlongrightarrow> f x) (at_left x)"
      unfolding f_def using limit_quantile_left_cont_scale[OF G y x] .
    have left_cont_h: "(h \<longlongrightarrow> h x) (at_left x)"
      unfolding h_def using limit_quantile_left_cont[OF G x] by (intro tendsto_intros)
    have "f x = h x"
      by (rule left_cont_agree_cocountable_eq[OF N_ctble x left_cont_f left_cont_h])
         (use eq0 in blast)
    thus ?thesis
      by (simp add: f_def h_def)
  qed

  define d where "d = limit_quantile G 1"
  have Bform: "B y = limit_quantile G y - d * A y" if y: "0 < y" for y
    using DeqFull[OF zero_less_one y] by (simp add: d_def)
  define H where "H = (\<lambda>u. limit_quantile G (exp u) - d)"
  have Acomp: "A (exp v) = exp (\<gamma> * v)" for v
    by(simp add: Aform powr_def)
  have H_eq: "H (u + v) = H u * exp (\<gamma> * v) + H v" for u v
  proof -
    have "limit_quantile G (exp (u + v)) = limit_quantile G (exp u * exp v)"
      by (simp add: exp_add)
    also have "\<dots> = limit_quantile G (exp u) * A (exp v) + B (exp v)"
      by (rule DeqFull[OF exp_gt_zero exp_gt_zero])
    also have "\<dots> = limit_quantile G (exp u) * exp (\<gamma> * v)
                     + (limit_quantile G (exp v) - d * exp (\<gamma> * v))"
      using Bform[OF exp_gt_zero] Acomp by simp
    also have "\<dots> = H u * exp (\<gamma> * v) + limit_quantile G (exp v)"
      by (simp add: H_def algebra_simps)
    finally have "limit_quantile G (exp (u + v)) = H u * exp (\<gamma> * v) + limit_quantile G (exp v)" .
    thus ?thesis
      by (simp add: H_def)
  qed
  have H_mono: "mono H"
    by(auto intro!: monoI limit_quantile_mono G simp: H_def)
  obtain c where c_nonneg: "0 \<le> c"
    and Hform: "\<And>u. H u = (if \<gamma> = 0 then c * u else c * (exp (\<gamma> * u) - 1) / \<gamma>)"
    by (rule cocycle_mono_solution[OF H_mono H_eq]) simp
  have Dform: "limit_quantile G y
      = (if \<gamma> = 0 then c * ln y + d else c * (y powr \<gamma> - 1) / \<gamma> + d)" if y: "0 < y" for y
  proof -
    have "limit_quantile G y = H (ln y) + d"
      using y by (simp add: H_def)
    also have "\<dots> = (if \<gamma> = 0 then c * ln y else c * (exp (\<gamma> * ln y) - 1) / \<gamma>) + d"
      using Hform[of "ln y"] by simp
    also have "(if \<gamma> = 0 then c * ln y else c * (exp (\<gamma> * ln y) - 1) / \<gamma>) + d
                 = (if \<gamma> = 0 then c * ln y + d else c * (y powr \<gamma> - 1) / \<gamma> + d)"
      using y by (simp add: powr_def)
    finally show ?thesis .
  qed
  have c_pos: "0 < c"
  proof (rule ccontr)
    assume "\<not> 0 < c"
    with c_nonneg have c0: "c = 0"
      by simp
    obtain y1 y2 where y12: "0 < y1" "y1 < y2"
      and D12: "limit_quantile G y1 < limit_quantile G y2"
      by (rule nondegenerate_growth_points[OF G deg countable_empty]) auto
    have y2pos: "0 < y2"
      using y12 by linarith
    have "limit_quantile G y1 = d" "limit_quantile G y2 = d"
      using Dform[OF y12(1)] Dform[OF y2pos] c0 by simp_all
    with D12 show False
      by simp
  qed
  show thesis
    by (rule that[of c \<gamma> d]) (use Dform c_pos in auto)
qed

text \<open>The Fisher--Tippett--Gnedenko theorem, which is Theorem~1.1.3 of the book by
      de Haan and Ferreira~\<^cite>\<open>deHaanFerreira\<close>
      (Fisher and Tippett (1928)~\<^cite>\<open>FisherTippett1928\<close>,
      Gnedenko (1943)~\<^cite>\<open>Gnedenko1943\<close>).\<close>
theorem Fisher_Tippett_Gnedenko:
  fixes F G :: "real \<Rightarrow> real" and a b :: "nat \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and G: "right_continuous_mono G 0 1"
    and deg: "\<not> degenerate_df G"
    and a: "\<And>n. 0 < a n"
    and wc: "weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
  obtains \<gamma> \<mu> \<sigma> where "0 < \<sigma>" and "G = EVD_cdf \<gamma> \<mu> \<sigma>"
proof -
  obtain \<gamma> c d where c_pos: "0 < c"
    and Dform: "\<And>y. 0 < y \<Longrightarrow> limit_quantile G y
            = (if \<gamma> = 0 then c * ln y + d else c * (y powr \<gamma> - 1) / \<gamma> + d)"
    by (rule limit_quantile_form[OF assms]) simp
  have Dform': "\<And>y. 0 < y \<Longrightarrow> limit_quantile (EVD_cdf \<gamma> d c) y
            = (if \<gamma> = 0 then c * ln y + d else c * (y powr \<gamma> - 1) / \<gamma> + d)"
    using limit_quantile_EVD_cdf[OF c_pos] by simp
  have eq: "\<And>y. 0 < y \<Longrightarrow> limit_quantile G y = limit_quantile (EVD_cdf \<gamma> d c) y"
    using Dform Dform' by simp
  have "G = EVD_cdf \<gamma> d c"
    by (intro dist_function_unique_limit_quantile[OF G _ eq]
        right_continuous_mono_cdf[OF real_distribution_EVD[OF c_pos]])
  with c_pos that
  show thesis
    by blast
qed

theorem Fisher_Tippett_Gnedenko':
  fixes F G :: "real \<Rightarrow> real" and a b :: "nat \<Rightarrow> real"
  assumes "right_continuous_mono F 0 1" "right_continuous_mono G 0 1" "\<not> degenerate_df G"
    and "\<And>n. 0 < a n"
    and "weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
  obtains \<gamma> \<alpha> \<beta> where "0 < \<alpha>" "\<And>x. G x = EVD_cdf \<gamma> 0 1 (\<alpha> * x + \<beta>)"
proof -
  obtain \<gamma> \<mu> \<sigma> where "0 < \<sigma>" and "G = EVD_cdf \<gamma> \<mu> \<sigma>"
    using Fisher_Tippett_Gnedenko[OF assms] by metis
  thus ?thesis
    using that[of "1 / \<sigma>" \<gamma> "- \<mu> / \<sigma>"]
    by(simp add: EVD_cdf_location_scale[of \<sigma> \<gamma>,symmetric] diff_divide_distrib)
qed

corollary Fisher_Tippett_Gnedenko_MDA':
  assumes deg: "\<not> degenerate_df G"
    and dom: "domain_of_attraction F G"
  obtains \<gamma> \<mu> \<sigma> where "0 < \<sigma>" and "G = EVD_cdf \<gamma> \<mu> \<sigma>"
proof -
  obtain a b where a: "\<And>n. 0 < a n"
    and wc: "weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) G"
    using dom unfolding domain_of_attraction_def by blast
  have G: "right_continuous_mono G 0 1" and F:"right_continuous_mono F 0 1"
    using dom unfolding domain_of_attraction_def by auto
  obtain \<gamma> \<mu> \<sigma> where "0 < \<sigma>" and "G = EVD_cdf \<gamma> \<mu> \<sigma>"
    by (rule Fisher_Tippett_Gnedenko[OF F G deg a wc])
  thus thesis
    by (rule that)
qed

corollary Fisher_Tippett_Gnedenko_MDA:
  assumes "\<not> degenerate_df G"
    and d:"domain_of_attraction F G"
  shows "\<exists>\<gamma>. domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
proof -
  obtain \<gamma> \<mu> \<sigma> where sigma:"0 < \<sigma>" and G:"G = EVD_cdf \<gamma> \<mu> \<sigma>"
    using Fisher_Tippett_Gnedenko_MDA'[OF assms] by metis
  thus ?thesis
    using d domain_of_attraction_EVD_cdf_iff[of \<sigma>]
    by(auto intro!: exI[where x=\<gamma>])
qed

subsection \<open>Alternative Characterizations of the Domain of Attraction\<close>
text \<open>We formalize Theorems~1.1.2 and~1.1.6 of the book~\<^cite>\<open>deHaanFerreira\<close>.\<close>
subsubsection \<open>Theorem 1.1.2 Part\<close>
lemma MDA_tail_probability_witness:
  fixes F a :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and a_pos: "\<And>t. 0 < a t" and sigma[arith]:"0 < \<sigma>"
    and tail: "\<And>x. 1 + \<gamma> * (x - \<mu>) / \<sigma> > 0 \<Longrightarrow>
                 ((\<lambda>t. t * (1 - F (a t * x + b t)))
                    \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) at_top"
  shows "(\<lambda>n. F (a (real n) * x + b (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
proof -
  have inside_conv: "(\<lambda>n. F (a (real n) * x' + b (real n)) ^ n)
                        \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x'"
    if supp': "1 + \<gamma> * (x' - \<mu>) / \<sigma> > 0" for x'
  proof -
    have seqtail: "(\<lambda>n::nat. real n * (1 - F (a (real n) * x' + b (real n))))
                     \<longlonglongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x')"
      by (rule filterlim_compose[OF tail[OF supp'] filterlim_real_sequentially])
    have Fbound: "\<And>n. 0 \<le> F (a (real n) * x' + b (real n))"
      "\<And>n. F (a (real n) * x' + b (real n)) \<le> 1"
      using right_continuous_mono.a_le_f[OF F] right_continuous_mono.f_le_b[OF F] by auto
    have EVDbound: "0 < EVD_cdf \<gamma> \<mu> \<sigma> x'" "EVD_cdf \<gamma> \<mu> \<sigma> x' \<le> 1"
      using EVD_cdf_supp_bounds[OF supp'] by auto
    show ?thesis
      using power_tendsto_iff_tendsto_tail
              [of "\<lambda>n. F (a (real n) * x' + b (real n))" "EVD_cdf \<gamma> \<mu> \<sigma> x'"]
        Fbound EVDbound seqtail
      by auto
  qed
  consider "1 + \<gamma> * (x - \<mu>) / \<sigma> > 0" | "1 + \<gamma> * (x - \<mu>) / \<sigma> \<le> 0" "\<gamma> > 0"
    | "1 + \<gamma> * (x - \<mu>) / \<sigma> \<le> 0" "\<gamma> < 0"
    by fastforce
  thus "(\<lambda>n. F (a (real n) * x + b (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
  proof cases
    assume "1 + \<gamma> * (x - \<mu>) / \<sigma> > 0"
    thus ?thesis
      using inside_conv by simp
  next
    assume supp_out:"1 + \<gamma> * (x - \<mu>) / \<sigma> \<le> 0" and gamma:"\<gamma> > 0"
    define y0 where "y0 = - \<sigma> / \<gamma> + \<mu>"
    have xy0: "x \<le> y0"
      using supp_out gamma
      by (simp add: y0_def field_simps)
    have val0: "EVD_cdf \<gamma> \<mu> \<sigma> x = 0"
      using supp_out gamma by(simp add: EVD_cdf_def Let_def)
    have valY0: "EVD_cdf \<gamma> \<mu> \<sigma> y0 = 0"
      using gamma by (simp add: EVD_cdf_def Let_def y0_def)
    have contY0: "isCont (EVD_cdf \<gamma> \<mu> \<sigma>) y0"
      by (rule isCont_EVD_cdf) simp
    have base_nonneg: "0 \<le> F (a (real n) * x + b (real n)) ^ n" for n
      using right_continuous_mono.a_le_f[OF F] by simp
    show ?thesis
      unfolding val0 tendsto_iff dist_real_def
    proof safe
      fix e :: real
      assume e: "0 < e"
      obtain \<delta> where \<delta>: "0 < \<delta>"
        "\<And>x''. x'' \<noteq> y0 \<and> \<bar>x'' - y0\<bar> < \<delta> \<Longrightarrow> \<bar>EVD_cdf \<gamma> \<mu> \<sigma> x'' - EVD_cdf \<gamma> \<mu> \<sigma> y0\<bar> < e"
        using LIM_D[OF contY0[unfolded isCont_def], of e] e by auto
      define x' where "x' = y0 + \<delta> / 2"
      have x'y0: "y0 < x'" "x' \<noteq> y0 \<and> \<bar>x' - y0\<bar> < \<delta>"
        using \<delta>(1) by (simp_all add: x'_def)
      have xx': "x \<le> x'"
        using xy0 x'y0(1) by linarith
      have anpos: "\<And>n. 0 \<le> a (real n)"
        using a_pos by (simp add: less_imp_le)
      have supp'': "1 + \<gamma> * (x' - \<mu>) / \<sigma> > 0"
        using x'y0(1) gamma by (simp add: y0_def field_simps)
      have target: "EVD_cdf \<gamma> \<mu> \<sigma> x' < e"
        using \<delta>(2)[OF x'y0(2)] valY0 EVD_cdf_supp_bounds[OF supp'']
        by simp
      have convx': "(\<lambda>n. F (a (real n) * x' + b (real n)) ^ n)
                     \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x'"
        using inside_conv[OF supp''] .
      obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> F (a (real n) * x' + b (real n)) ^ n < e"
        using order_tendstoD(2)[OF convx' target]
        unfolding eventually_sequentially by blast
      show "\<forall>\<^sub>F n in sequentially. \<bar>F (a (real n) * x + b (real n)) ^ n - 0\<bar> < e"
      proof (intro eventually_sequentiallyI[where c=N])
        fix n
        assume Nn: "N \<le> n"
        have "F (a (real n) * x + b (real n)) ^ n \<le> F (a (real n) * x' + b (real n)) ^ n"
          using right_continuous_mono.a_le_f[OF F] anpos xx'
          by (auto intro!: power_mono monoD[OF right_continuous_mono.mono[OF F]] mult_left_mono)
        thus "\<bar>F (a (real n) * x + b (real n)) ^ n - 0\<bar> < e"
          using base_nonneg N[OF Nn] by simp
      qed
    qed
  next
    assume supp_out:"1 + \<gamma> * (x - \<mu>) / \<sigma> \<le> 0" and neg:"\<gamma> < 0"
    define y0 where "y0 = - \<sigma> / \<gamma> + \<mu>"
    have xy0: "y0 \<le> x"
      using supp_out neg by (simp add: y0_def field_simps)
    have val0: "EVD_cdf \<gamma> \<mu> \<sigma> x = 1"
      using neg supp_out by (simp add: EVD_cdf_def Let_def)
    have valY0: "EVD_cdf \<gamma> \<mu> \<sigma> y0 = 1"
      using neg by (simp add: EVD_cdf_def y0_def Let_def)
    have contY0: "isCont (EVD_cdf \<gamma> \<mu> \<sigma>) y0"
      by (rule isCont_EVD_cdf) simp
    have base_le1: "F (a (real n) * x + b (real n)) ^ n \<le> 1" for n
      using right_continuous_mono.a_le_f[OF F] right_continuous_mono.f_le_b[OF F]
      by (simp add: power_le_one)
    show ?thesis
      unfolding val0 tendsto_iff dist_real_def
    proof safe
      fix e :: real
      assume e: "0 < e"
      obtain \<delta> where \<delta>: "0 < \<delta>"
        "\<And>x''. x'' \<noteq> y0 \<and> \<bar>x'' - y0\<bar> < \<delta> \<Longrightarrow> \<bar>EVD_cdf \<gamma> \<mu> \<sigma> x'' - EVD_cdf \<gamma> \<mu> \<sigma> y0\<bar> < e"
        using LIM_D[OF contY0[unfolded isCont_def], of e] e by auto
      define x' where "x' = y0 - \<delta> / 2"
      have x'y0: "x' < y0" "x' \<noteq> y0 \<and> \<bar>x' - y0\<bar> < \<delta>"
        using \<delta>(1) by (simp_all add: x'_def)
      have xx': "x' \<le> x"
        using xy0 x'y0(1) by linarith
      have anpos: "\<And>n. 0 \<le> a (real n)"
        using a_pos by (simp add: less_imp_le)
      have supp'': "1 + \<gamma> * (x' - \<mu>) / \<sigma> > 0"
        using x'y0(1) neg by (simp add: y0_def field_simps)
      have target: "1 - e < EVD_cdf \<gamma> \<mu> \<sigma> x'"
        using \<delta>(2)[OF x'y0(2)] valY0 EVD_cdf_supp_bounds[OF supp''] by simp
      have convx': "(\<lambda>n. F (a (real n) * x' + b (real n)) ^ n)
                        \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x'"
        using inside_conv[OF supp''] .
      obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> 1 - e < F (a (real n) * x' + b (real n)) ^ n"
        using order_tendstoD(1)[OF convx' target]
        unfolding eventually_sequentially by blast
      show "\<forall>\<^sub>F n in sequentially. \<bar>F (a (real n) * x + b (real n)) ^ n - 1\<bar> < e"
      proof (intro eventually_sequentiallyI[where c=N])
        fix n
        assume Nn: "N \<le> n"
        have "F (a (real n) * x' + b (real n)) ^ n \<le> F (a (real n) * x + b (real n)) ^ n"
          using right_continuous_mono.a_le_f[OF F] anpos xx'
          by (auto intro!: power_mono monoD[OF right_continuous_mono.mono[OF F]] mult_left_mono)
        thus "\<bar>F (a (real n) * x + b (real n)) ^ n - 1\<bar> < e"
          using base_le1 N[OF Nn] by simp
      qed
    qed
  qed
qed

lemma MDA_tail_quantile_to_tail_probability:
  fixes F a :: "real \<Rightarrow> real" and \<gamma> x :: real
  assumes F: "right_continuous_mono F 0 1"
    and a_pos: "\<And>t. 0 < a t"
    and sigma[arith]:"0 < \<sigma>"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
                 ((\<lambda>t. (tail_quantile F (t * x) - b t) / a t)
                    \<longlongrightarrow> (if \<gamma> = 0
                          then \<sigma> * ln x + \<mu>
                          else \<sigma> * (x powr \<gamma> - 1) / \<gamma> + \<mu>)) at_top"
    (is "\<And>x. 0 < x \<Longrightarrow> (_ \<longlongrightarrow> ?G x) at_top")
    and supp: "1 + \<gamma> * (x - \<mu>) / \<sigma> > 0"
  shows "((\<lambda>t. t * (1 - F (a t * x + b t)))
           \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) at_top"
proof -
  have st_mono1:"\<sigma> * ln y + \<mu> < \<sigma> * ln z + \<mu>"
    if "0 < y" "y < z" for y z
    using that by auto
  have st_mono2:"\<sigma> * (y powr \<gamma> - 1) / \<gamma> + \<mu> < \<sigma> * (z powr \<gamma> - 1) / \<gamma> + \<mu>"
    if "0 < y" "y < z" "\<gamma> \<noteq> 0" for y z
  proof(cases "\<gamma> > 0")
    show "0 < \<gamma> \<Longrightarrow>
           \<sigma> * (y powr \<gamma> - 1) / \<gamma> + \<mu> < \<sigma> * (z powr \<gamma> - 1) / \<gamma> + \<mu>"
      using that by(auto intro!: divide_strict_right_mono powr_less_mono2)
  next
    show "\<not> 0 < \<gamma> \<Longrightarrow>
          \<sigma> * (y powr \<gamma> - 1) / \<gamma> + \<mu> < \<sigma> * (z powr \<gamma> - 1) / \<gamma> + \<mu>"
      using that by(auto intro!: divide_strict_right_mono_neg powr_less_mono2_neg)
  qed
  define \<rho> where "\<rho> = (if \<gamma> = 0 then exp ((x - \<mu>) / \<sigma>) else (1 + \<gamma> * (x - \<mu>) / \<sigma>) powr (1 / \<gamma>))"
  have \<rho>_pos: "0 < \<rho>"
    using supp by (simp add: \<rho>_def)
  have D\<rho>: "?G \<rho> = x"
    using supp by(auto simp: \<rho>_def powr_powr)
  have EVD_val: "EVD_cdf \<gamma> \<mu> \<sigma> x
          = exp (- (if \<gamma> = 0 then exp (- ((x - \<mu>) / \<sigma>))
                    else (1 + \<gamma> * (x - \<mu>) / \<sigma>) powr (- 1 / \<gamma>)))"
    using supp by (simp add: EVD_cdf_def Let_def)
  have target_eq: "- ln (EVD_cdf \<gamma> \<mu> \<sigma> x) = 1 / \<rho>"
    by(auto simp add: EVD_val \<rho>_def exp_minus[of "(x - \<mu>) / \<sigma>"] inverse_eq_divide powr_minus)
  show "((\<lambda>t. t * (1 - F (a t * x + b t)))
               \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) at_top"
    unfolding target_eq tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    have inv_cont: "isCont (\<lambda>r. 1 / r) \<rho>"
      using \<rho>_pos by (intro continuous_intros) simp
    obtain \<delta> where \<delta>pos: "0 < \<delta>"
      and \<delta>bound: "\<And>r. r \<noteq> \<rho> \<Longrightarrow> \<bar>r - \<rho>\<bar> < \<delta> \<Longrightarrow> \<bar>1 / r - 1 / \<rho>\<bar> < e"
      using LIM_D[OF inv_cont[unfolded isCont_def], of e] e by auto
    define \<eta> where "\<eta> = min \<delta> \<rho> / 2"
    have \<eta>pos: "0 < \<eta>" and \<eta>lt\<rho>: "\<eta> < \<rho>" and \<eta>lt\<delta>: "\<eta> < \<delta>"
      using \<delta>pos \<rho>_pos by (simp_all add: \<eta>_def)
    define \<rho>1 where "\<rho>1 = \<rho> - \<eta>"
    define \<rho>2 where "\<rho>2 = \<rho> + \<eta>"
    have \<rho>1pos: "0 < \<rho>1" and \<rho>1lt\<rho>: "\<rho>1 < \<rho>" and \<rho>lt\<rho>2: "\<rho> < \<rho>2"
      using \<eta>pos \<eta>lt\<rho> by (simp_all add: \<rho>1_def \<rho>2_def)
    have e1: "\<bar>1 / \<rho>1 - 1 / \<rho>\<bar> < e"
      using \<delta>bound[of \<rho>1] \<eta>pos \<eta>lt\<delta> by (simp add: \<rho>1_def)
    have e2: "\<bar>1 / \<rho>2 - 1 / \<rho>\<bar> < e"
      using \<delta>bound[of \<rho>2] \<eta>pos \<eta>lt\<delta> by (simp add: \<rho>2_def)
    have \<rho>2pos: "0 < \<rho>2"
      using \<rho>lt\<rho>2 \<rho>_pos by linarith
    have x2gt: "x < ?G \<rho>2"
      using st_mono1[OF \<rho>_pos \<rho>lt\<rho>2] st_mono2[OF \<rho>_pos \<rho>lt\<rho>2] D\<rho> by auto
    have x1lt: "?G \<rho>1 < x"
      using st_mono1[OF \<rho>1pos \<rho>1lt\<rho>] st_mono2[OF \<rho>1pos \<rho>1lt\<rho>] D\<rho> by auto
    obtain T1 where T1: "\<And>t. T1 \<le> t \<Longrightarrow> x < (tail_quantile F (t * \<rho>2) - b t) / a t"
      using order_tendstoD(1)[OF quant[OF \<rho>2pos] x2gt]
      unfolding eventually_at_top_linorder by blast
    obtain T2 where T2: "\<And>t. T2 \<le> t \<Longrightarrow> (tail_quantile F (t * \<rho>1) - b t) / a t < x"
      using order_tendstoD(2)[OF quant[OF \<rho>1pos] x1lt]
      unfolding eventually_at_top_linorder by blast
    define T where "T = max (max T1 T2) (max (1 / \<rho>1 + 1) (1 / \<rho>2 + 1))"
    show "\<forall>\<^sub>F t in at_top. \<bar>t * (1 - F (a t * x + b t)) - 1 / \<rho>\<bar> < e"
    proof (intro eventually_at_top_linorderI[where c=T])
      fix t
      assume Tt: "T \<le> t"
      have T1t: "T1 \<le> t" and T2t: "T2 \<le> t"
        and t_ge1: "1 / \<rho>1 + 1 \<le> t" and t_ge2: "1 / \<rho>2 + 1 \<le> t"
        using Tt by (simp_all add: T_def)
      have \<rho>1inv_pos: "0 < 1 / \<rho>1"
        using \<rho>1pos by simp
      have tpos: "0 < t"
        using t_ge1 \<rho>1inv_pos by linarith
      have t\<rho>1: "1 < t * \<rho>1"
        using mult_strict_right_mono[OF _ \<rho>1pos, of "1 / \<rho>1" t] t_ge1 \<rho>1pos
        by simp
      have t\<rho>2: "1 < t * \<rho>2"
        using mult_strict_right_mono[OF _ \<rho>2pos, of "1 / \<rho>2" t] t_ge2 \<rho>2pos
        by simp
      have ineq1: "a t * x + b t < tail_quantile F (t * \<rho>2)"
        using T1[OF T1t] a_pos[of t] by (simp add: field_simps)
      have ineq2: "tail_quantile F (t * \<rho>1) < a t * x + b t"
        using T2[OF T2t] a_pos[of t] by (simp add: field_simps)
      have p_bounds2: "0 < 1 - 1 / (t * \<rho>2)" "1 - 1 / (t * \<rho>2) < 1"
        using t\<rho>2 by simp_all
      have lower: "1 / \<rho>2 < t * (1 - F (a t * x + b t))"
      proof -
        have "1 / (t * \<rho>2) < 1 - F (a t * x + b t)"
          using right_continuous_mono.ginv_le_iff[OF F p_bounds2, of "a t * x + b t"] ineq1
          by linarith
        hence "t * (1 / (t * \<rho>2)) < t * (1 - F (a t * x + b t))"
          using tpos by (intro mult_strict_left_mono) auto
        thus ?thesis
          using tpos \<rho>2pos by (simp add: field_simps)
      qed
      have p_bounds1: "0 < 1 - 1 / (t * \<rho>1)" "1 - 1 / (t * \<rho>1) < 1"
        using t\<rho>1 by simp_all
      have upper: "t * (1 - F (a t * x + b t)) \<le> 1 / \<rho>1"
      proof -
        have "F (tail_quantile F (t * \<rho>1)) \<le> F (a t * x + b t)"
          by (rule monoD[OF right_continuous_mono.mono[OF F], OF less_imp_le[OF ineq2]])
        moreover have "1 - 1 / (t * \<rho>1) \<le> F (tail_quantile F (t * \<rho>1))"
          using right_continuous_mono.ginv_attained[OF F p_bounds1] by simp
        ultimately have "1 - 1 / (t * \<rho>1) \<le> F (a t * x + b t)"
          by linarith
        hence "t * (1 - F (a t * x + b t)) \<le> t * (1 / (t * \<rho>1))"
          using tpos by (intro mult_left_mono) auto
        moreover have "t * (1 / (t * \<rho>1)) = 1 / \<rho>1"
          using tpos \<rho>1pos by (simp add: field_simps)
        ultimately show ?thesis
          by linarith
      qed
      show "\<bar>t * (1 - F (a t * x + b t)) - 1 / \<rho>\<bar> < e"
        using lower upper e1 e2 by linarith
    qed
  qed
qed

lemma MDA_tail_quantile_witness:
  fixes F a :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and a_pos: "\<And>t. 0 < a t" and sigma:"0 < \<sigma>"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
                 ((\<lambda>t. (tail_quantile F (t * x) - b t) / a t)
                    \<longlongrightarrow> (if \<gamma> = 0
                          then \<sigma> * ln x + \<mu>
                          else \<sigma> * (x powr \<gamma> - 1) / \<gamma> + \<mu>)) at_top"
  shows "(\<lambda>n. F (a (real n) * x + b (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
  by(intro MDA_tail_probability_witness[OF F a_pos]
      MDA_tail_quantile_to_tail_probability[OF F a_pos _ quant] sigma) auto

lemma MDA_imp_tail_probability:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and G: "right_continuous_mono G 0 1"
    and a:"\<And>n. 0 < a n"
    and deg:"\<not> degenerate_df G"
    and lim:"\<And>y. (\<lambda>n. F (a n * y + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 y"
    and sigma[arith]:"0 < \<sigma>"
    and supp:"1 + \<gamma> * x > 0"
  shows"((\<lambda>t. t * (1 - F (a (nat \<lfloor>t\<rfloor>) * x + tail_quantile F t)))
                  \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) at_top"
proof -
  have G': "right_continuous_mono (EVD_cdf \<gamma> 0 1) 0 1"
    by (rule right_continuous_mono_EVD_cdf) simp
  have deg': "\<not> degenerate_df (EVD_cdf \<gamma> 0 1)"
    by (rule EVD_cdf_nondegenerate) simp
  have wc: "weak_conv (\<lambda>n x'. F (a n * x' + b n) ^ n) (EVD_cdf \<gamma> 0 1)"
    by(subst weak_conv_EVD_cdf_iff) (auto simp: lim)
  have cont: "isCont (limit_quantile (EVD_cdf \<gamma> 0 1)) y" if y: "0 < y" for y
    by(intro isCont_limit_quantile_EVD_cdf y) simp

  have quant: "((\<lambda>t. (tail_quantile F (t * x') - tail_quantile F t) / a (nat \<lfloor>t\<rfloor>))
                  \<longlongrightarrow> (if \<gamma> = 0 then 1 * ln x' + 0 else 1 * (x' powr \<gamma> - 1) / \<gamma> + 0)) at_top"
    if x': "0 < x'" for x'
  proof -
    note at_x' = real_tail_quantile_tendsto[OF F G' deg' a wc x' cont[OF x']]
    have at_1: "((\<lambda>t. (tail_quantile F t - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                    \<longlongrightarrow> limit_quantile (EVD_cdf \<gamma> 0 1) 1) at_top"
      using real_tail_quantile_tendsto[OF F G' deg' a wc zero_less_one cont[OF zero_less_one]]
      by simp
    have diff: "((\<lambda>t. (tail_quantile F (t * x') - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)
                - (tail_quantile F t - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
              \<longlongrightarrow> limit_quantile (EVD_cdf \<gamma> 0 1) x' - limit_quantile (EVD_cdf \<gamma> 0 1) 1) at_top"
      by (intro tendsto_diff at_x' at_1)
    have val_1: "limit_quantile (EVD_cdf \<gamma> 0 1) 1 = 0"
      using limit_quantile_EVD_cdf[OF zero_less_one zero_less_one, of \<gamma> 0] by simp
    show ?thesis
      using diff val_1 limit_quantile_EVD_cdf[OF zero_less_one x', of \<gamma> 0]
      by (simp add: diff_divide_distrib)
  qed
  have a': "\<And>t. 0 < a (nat \<lfloor>t\<rfloor>)"
    using a by simp
  have supp01: "1 + \<gamma> * (x - 0) / 1 > 0"
    using supp by simp
  show ?thesis
    using MDA_tail_quantile_to_tail_probability
            [where a = "\<lambda>t. a (nat \<lfloor>t\<rfloor>)" and b = "tail_quantile F",
             OF F a' zero_less_one quant supp01]
    by simp
qed

lemma MDA_imp_tail_quantile:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and G: "right_continuous_mono G 0 1"
    and a:"\<And>n. 0 < a n"
    and deg:"\<not> degenerate_df G"
    and lim:"\<And>y. (\<lambda>n. F (a n * y + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 y"
    and sigma[arith]:"0 < \<sigma>"
    and x:"x > 0"
  shows"((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a (nat (floor t)))
                            \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
proof -
  have G': "right_continuous_mono (EVD_cdf \<gamma> 0 1) 0 1"
    by (rule right_continuous_mono_EVD_cdf) simp
  have deg': "\<not> degenerate_df (EVD_cdf \<gamma> 0 1)"
    by (rule EVD_cdf_nondegenerate) simp
  have wc: "weak_conv (\<lambda>n x'. F (a n * x' + b n) ^ n) (EVD_cdf \<gamma> 0 1)"
    by(auto intro!: weak_conv_EVD_cdf_iff[THEN iffD2] lim)
  have cont: "isCont (limit_quantile (EVD_cdf \<gamma> 0 1)) y" if y: "0 < y" for y
    by(intro isCont_limit_quantile_EVD_cdf y) simp
  have at_x: "((\<lambda>t. (tail_quantile F (t * x) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                  \<longlongrightarrow> limit_quantile (EVD_cdf \<gamma> 0 1) x) at_top"
    by (rule real_tail_quantile_tendsto[OF F G' deg' a wc x cont[OF x]])
  have at_1: "((\<lambda>t. (tail_quantile F t - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                  \<longlongrightarrow> limit_quantile (EVD_cdf \<gamma> 0 1) 1) at_top"
    using real_tail_quantile_tendsto[OF F G' deg' a wc zero_less_one cont[OF zero_less_one]]
    by simp
  have diff: "((\<lambda>t. (tail_quantile F (t * x) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>)
              - (tail_quantile F t - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                \<longlongrightarrow> limit_quantile (EVD_cdf \<gamma> 0 1) x - limit_quantile (EVD_cdf \<gamma> 0 1) 1) at_top"
    by (intro tendsto_diff at_x at_1)
  have val_1: "limit_quantile (EVD_cdf \<gamma> 0 1) 1 = 0"
    using limit_quantile_EVD_cdf[OF zero_less_one zero_less_one, of \<gamma> 0] by simp
  show ?thesis
    using diff val_1 limit_quantile_EVD_cdf[OF zero_less_one x, of \<gamma> 0]
    by (auto simp: diff_divide_distrib)
qed

lemma MDA_iff_tail_probability:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and a:"\<And>n. 0 < a n"
    and sigma[arith]:"0 < \<sigma>"
  shows "(\<forall>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x) \<longleftrightarrow>
         (\<forall>x. (1 + \<gamma> * (x - \<mu>) / \<sigma> > 0 \<longrightarrow>
                 ((\<lambda>t. t * (1 - F (a (nat \<lfloor>t\<rfloor>) * x + b (nat \<lfloor>t\<rfloor>))))
                    \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) at_top))"
proof
  assume wc:"\<forall>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
  have cont: "isCont (limit_quantile (EVD_cdf \<gamma> \<mu> \<sigma>)) y" if y: "0 < y" for y
    by(intro isCont_limit_quantile_EVD_cdf y) simp
  have "\<And>y. 0 < y \<Longrightarrow>
           ((\<lambda>t. (tail_quantile F (t * y) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
            \<longlongrightarrow> (if \<gamma> = 0 then \<sigma> * ln y + \<mu>
                           else \<sigma> * (y powr \<gamma> - 1) / \<gamma> + \<mu>)) at_top"
    using real_tail_quantile_tendsto[OF F right_continuous_mono_EVD_cdf
        EVD_cdf_nondegenerate a weak_conv_EVD_cdf_iff[THEN iffD2] _ cont]
        wc sigma
    by(auto simp add: limit_quantile_EVD_cdf[OF sigma,of _ \<gamma> \<mu>])
  from MDA_tail_quantile_to_tail_probability[OF F a sigma this]
  show "\<forall>x. 0 < 1 + \<gamma> * (x - \<mu>) / \<sigma> \<longrightarrow>
            ((\<lambda>t. t * (1 - F (a (nat \<lfloor>t\<rfloor>) * x + b (nat \<lfloor>t\<rfloor>))))
             \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) at_top"
    by blast
qed(use MDA_tail_probability_witness[where a="\<lambda>t. a (nat \<lfloor>t\<rfloor>)"
      and b ="\<lambda>t. b (nat \<lfloor>t\<rfloor>)",OF F a sigma]
     in simp)

lemma MDA_iff_tail_quantile:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and a:"\<And>n. 0 < a n"
    and sigma[arith]:"0 < \<sigma>"
  shows "(\<forall>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x) \<longleftrightarrow>
         (\<forall>x>0. ((\<lambda>t. (tail_quantile F (t * x) -  b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                 \<longlongrightarrow> (if \<gamma> = 0 then \<sigma> * ln x + \<mu> else \<sigma> * (x powr \<gamma> - 1) / \<gamma> + \<mu>)) at_top)"
proof
  assume wc:"\<forall>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
  have cont: "isCont (limit_quantile (EVD_cdf \<gamma> \<mu> \<sigma>)) y" if y: "0 < y" for y
    by(intro isCont_limit_quantile_EVD_cdf y) simp
  show "\<forall>x>0. ((\<lambda>t. (tail_quantile F (t * x) -  b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                 \<longlongrightarrow> (if \<gamma> = 0 then \<sigma> * ln x + \<mu>  else \<sigma> * (x powr \<gamma> - 1) / \<gamma> + \<mu>)) at_top"
    using real_tail_quantile_tendsto[OF F right_continuous_mono_EVD_cdf
        EVD_cdf_nondegenerate a weak_conv_EVD_cdf_iff[THEN iffD2] _ cont]
      wc
    by(auto simp: limit_quantile_EVD_cdf[OF sigma,of _ \<gamma> \<mu>])
qed(use MDA_tail_quantile_witness[where a="\<lambda>t. a (nat \<lfloor>t\<rfloor>)" and b ="\<lambda>t. b (nat \<lfloor>t\<rfloor>)",OF assms]
       in simp)

lemma MDA_iff_tail_quantile':
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
  shows "domain_of_attraction F (EVD_cdf \<gamma> 0 1)
          \<longleftrightarrow> (\<exists>a. (\<forall>t. 0 < a t) \<and>
                  (\<forall>x>0. ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
                            \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top))"
proof safe
  assume dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  obtain a b where a: "\<And>n. 0 < a n"
    and lim: "\<And>y. (\<lambda>n. F (a n * y + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 y"
    using dom unfolding domain_of_attraction_def
    by (auto simp: weak_conv_EVD_cdf_iff)
  show "\<exists>a. (\<forall>t. 0 < a t) \<and>
          (\<forall>x>0. ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
                    \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top)"
    using a
    by(intro exI[of _ "\<lambda>t. a (nat \<lfloor>t\<rfloor>)"] conjI allI
        MDA_imp_tail_quantile[OF F right_continuous_mono_EVD_cdf
          a EVD_cdf_nondegenerate lim] impI)
      auto
next
  fix a
  assume a: "\<forall>t. 0 < a t"
    and quant: "\<forall>x>0.
                  ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
                     \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
  thus "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
    by(auto intro!: exI[of _ "\<lambda>n. a (real n)",
          OF conjI[OF _ exI[of _ "\<lambda>n. tail_quantile F (real n)"]]]
        MDA_tail_quantile_witness[where b = "tail_quantile F", OF F]
        right_continuous_mono_EVD_cdf F
        simp: weak_conv_EVD_cdf_iff domain_of_attraction_def)
qed

lemma MDA_iff_tail_probability':
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
  shows "domain_of_attraction F (EVD_cdf \<gamma> 0 1)
          \<longleftrightarrow> (\<exists>a. (\<forall>t. 0 < a t) \<and>
                  (\<forall>x. 1 + \<gamma> * x > 0 \<longrightarrow>
                       ((\<lambda>t. t * (1 - F (a t * x + tail_quantile F t)))
                          \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) at_top))"
proof safe
  assume dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  obtain a b where a: "\<And>n. 0 < a n"
    and lim: "\<And>y. (\<lambda>n. F (a n * y + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 y"
    using dom unfolding domain_of_attraction_def
    by (auto simp: weak_conv_EVD_cdf_iff)
  show "\<exists>a. (\<forall>t. 0 < a t) \<and>
          (\<forall>x. 1 + \<gamma> * x > 0 \<longrightarrow>
               ((\<lambda>t. t * (1 - F (a t * x + tail_quantile F t)))
                  \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) at_top)"
    using a
    by(intro exI[of _ "\<lambda>t. a (nat \<lfloor>t\<rfloor>)"] conjI allI
        MDA_imp_tail_probability[OF F right_continuous_mono_EVD_cdf
          a EVD_cdf_nondegenerate lim] impI)
      auto
next
  fix a
  assume a: "\<forall>t. 0 < a t"
    and tail: "\<forall>x. 1 + \<gamma> * x > 0 \<longrightarrow>
                  ((\<lambda>t. t * (1 - F (a t * x + tail_quantile F t)))
                     \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) at_top"
  thus "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
    by(auto intro!: exI[of _ "\<lambda>n. a (real n)",
          OF conjI[OF _ exI[of _ "\<lambda>n. tail_quantile F (real n)"]]]
        MDA_tail_probability_witness[where b = "tail_quantile F", OF F]
        right_continuous_mono_EVD_cdf F
        simp: weak_conv_EVD_cdf_iff domain_of_attraction_def)
qed

subsubsection \<open>Theorem 1.1.6 Part\<close>
definition x_star :: "(real \<Rightarrow> real) \<Rightarrow> real" where
"x_star F = Sup {x. F x < 1}"

abbreviation bdd_support :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
"bdd_support F \<equiv> bdd_above {x. F x < 1}"

lemma not_bdd_supportI:
  assumes "\<And>x. \<exists>y>x. F y < 1"
  shows "\<not> bdd_support F"
  using assms by(auto simp: bdd_above_def) (meson linorder_not_le)

lemma not_bdd_supportI':
  assumes "\<And>x. F x < 1"
  shows "\<not> bdd_support F"
  by(intro not_bdd_supportI) (meson assms less_add_one)

definition endpoint_filter :: "(real \<Rightarrow> real) \<Rightarrow> real filter" where
"endpoint_filter F = (if bdd_support F then at_left (x_star F) else at_top)"

lemma endpoint_filter:
 "bdd_support F \<Longrightarrow> endpoint_filter F = at_left (x_star F)"
 "\<not> bdd_support F \<Longrightarrow> endpoint_filter F = at_top"
  by(auto simp: endpoint_filter_def)

lemma endpoint_filter_neq_bot: "endpoint_filter F \<noteq> \<bottom>"
  by (simp add: endpoint_filter_def)

lemma F_x_star_eq_1:
  assumes "right_continuous_mono F 0 1"
    and bdd:"bdd_above {x. F x < 1}"
  shows "F (x_star F) = 1"
proof(rule antisym)
  interpret right_continuous_mono F 0 1
    by fact
  show "1 \<le> F (x_star F)"
  proof(rule ccontr)
    assume h:"\<not> 1 \<le> F (x_star F)"
    hence "Sup {x. F x < 1} \<in> {x. F x < 1}"
      by(auto simp: x_star_def)
    have "\<forall>\<epsilon>>0. \<exists>\<delta>>0. F (\<Squnion> {x. F x < 1} + \<delta>) - F (\<Squnion> {x. F x < 1}) < \<epsilon>"
      using mono cont
      by(subst continuous_at_right_real_increasing[symmetric]) (auto simp: monoD)
    then obtain d where d:"d > 0"
      "F (\<Squnion> {x. F x < 1} + d) - F (\<Squnion> {x. F x < 1}) < 1 - F (Sup {x. F x < 1})"
      using h unfolding x_star_def
      by (metis diff_less_0_iff_less less_eq_real_def linorder_not_less right_minus_eq)
    hence "F (\<Squnion> {x. F x < 1} + d) < 1"
      by simp
    hence "(\<Squnion> {x. F x < 1} + d) \<le> (\<Squnion> {x. F x < 1})"
      by (metis bdd cSup_upper mem_Collect_eq)
    with d show False
      by simp
  qed
qed(auto intro!: assms right_continuous_mono.f_le_b[of F])

lemma F_tendsto_1_endpoint:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and a:"\<And>n. 0 < a n"
    and sigma[arith]:"0 < \<sigma>"
    and wc:"\<And>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
  shows "(F \<longlongrightarrow> 1) (endpoint_filter F)"
proof (cases "bdd_support F")
  assume "\<not> bdd_support F"
  with F show ?thesis
    by(simp add: endpoint_filter right_continuous_mono_def)
next
  assume bdd:"bdd_support F"
  have EVD_mu: "EVD_cdf \<gamma> \<mu> \<sigma> \<mu> = exp (- 1)"
    by (simp add: EVD_cdf_def)
  have supp_mu: "0 < 1 + \<gamma> * (\<mu> - \<mu>) / \<sigma>"
    by simp
  have tail_at_mu: "((\<lambda>t. t * (1 - F (a (nat \<lfloor>t\<rfloor>) * \<mu> + b (nat \<lfloor>t\<rfloor>))))
                      \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> \<mu>)) at_top"
    using F MDA_iff_tail_probability a sigma supp_mu wc
    by blast
  have tail_at_mu': "((\<lambda>t. t * (1 - F (a (nat \<lfloor>t\<rfloor>) * \<mu> + b (nat \<lfloor>t\<rfloor>)))) \<longlongrightarrow> 1) at_top"
    using tail_at_mu unfolding EVD_mu by simp
  have inv_tendsto: "((\<lambda>t::real. 1 / t) \<longlongrightarrow> 0) at_top"
    using tendsto_inverse_0_at_top[OF filterlim_ident] by (simp add: inverse_eq_divide)
  have step0: "((\<lambda>t::real. 1 - F (a (nat \<lfloor>t\<rfloor>) * \<mu> + b (nat \<lfloor>t\<rfloor>))) \<longlongrightarrow> 0) at_top"
  proof -
    have eq: "\<forall>\<^sub>F t::real in at_top. 1 - F (a (nat \<lfloor>t\<rfloor>) * \<mu> + b (nat \<lfloor>t\<rfloor>))
                = t * (1 - F (a (nat \<lfloor>t\<rfloor>) * \<mu> + b (nat \<lfloor>t\<rfloor>))) * (1 / t)"
      by (rule eventually_mono[OF eventually_gt_at_top[of 0]]) simp
    have prod_tendsto: "((\<lambda>t. t * (1 - F (a (nat \<lfloor>t\<rfloor>) * \<mu>
                            + b (nat \<lfloor>t\<rfloor>))) * (1 / t)) \<longlongrightarrow> 0) at_top"
      using tendsto_mult[OF tail_at_mu' inv_tendsto] by simp
    show ?thesis
      using tendsto_cong[OF eq] prod_tendsto by simp
  qed
  have Fxstar: "F (x_star F) = 1"
    by(intro F_x_star_eq_1 bdd assms)
  have filter_eq: "endpoint_filter F = at_left (x_star F)"
    using bdd by (simp add: endpoint_filter)
  have upper_ev: "\<forall>\<^sub>F t in at_left (x_star F). F t \<le> 1"
    using right_continuous_mono.f_le_b[OF F] by (intro always_eventually) simp
  show ?thesis
    unfolding filter_eq tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    have c2: "(1::real) / 2 < 1"
      by simp
    have ev_c: "\<forall>\<^sub>F t in at_top. 1 - F (a (nat \<lfloor>t\<rfloor>) * \<mu> + b (nat \<lfloor>t\<rfloor>)) < e
                  \<and> 1 / 2 < t * (1 - F (a (nat \<lfloor>t\<rfloor>) * \<mu> + b (nat \<lfloor>t\<rfloor>)))"
      using eventually_conj[OF order_tendstoD(2)
          [OF step0 e] order_tendstoD(1)[OF tail_at_mu' c2]] .
    then obtain t0 where t0: "1 - F (a (nat \<lfloor>t0\<rfloor>) * \<mu> + b (nat \<lfloor>t0\<rfloor>)) < e"
        "1 / 2 < t0 * (1 - F (a (nat \<lfloor>t0\<rfloor>) * \<mu> + b (nat \<lfloor>t0\<rfloor>)))"
      using eventually_happens'[OF trivial_limit_at_top_linorder] by blast
    define z where "z = a (nat \<lfloor>t0\<rfloor>) * \<mu> + b (nat \<lfloor>t0\<rfloor>)"
    have Fz: "1 - e < F z"
      using t0(1) by (simp add: z_def)
    have t0pos: "0 < t0"
    proof (rule ccontr)
      assume "\<not> 0 < t0"
      hence "t0 * (1 - F z) \<le> 0"
        using right_continuous_mono.f_le_b[OF F] unfolding z_def
        by (intro mult_nonpos_nonneg) auto
      with t0(2) show False
        unfolding z_def by simp
    qed
    have Fzlt1: "F z < 1"
    proof (rule ccontr)
      assume "\<not> F z < 1"
      hence "F z = 1"
        using right_continuous_mono.f_le_b[OF F, of z] by linarith
      thus False
        using t0(2) t0pos unfolding z_def by simp
    qed
    have zlt: "z < x_star F"
    proof -
      have "z \<le> x_star F"
        using Fzlt1 bdd unfolding x_star_def z_def by (intro cSup_upper) auto
      moreover have "z \<noteq> x_star F"
        using Fzlt1 Fxstar by auto
      ultimately show ?thesis
        by simp
    qed
    have lower_ev: "\<forall>\<^sub>F t in at_left (x_star F). 1 - e < F t"
      unfolding eventually_at_left_field
    proof (intro exI[of _ z] conjI zlt allI impI)
      fix y
      assume "z < y" "y < x_star F"
      hence "F z \<le> F y"
        by (intro monoD[OF right_continuous_mono.mono[OF F]]) simp
      thus "1 - e < F y"
        using Fz by simp
    qed
    show "\<forall>\<^sub>F t in at_left (x_star F). \<bar>F t - 1\<bar> < e"
      using lower_ev upper_ev by eventually_elim linarith
  qed
qed

lemma lt_x_star_iff_F_lt_1:
  fixes F :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and bdd: "bdd_support F"
  shows "y < x_star F \<longleftrightarrow> F y < 1"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  show ?thesis
  proof
    assume c: "y < x_star F"
    show "F y < 1"
    proof (rule ccontr)
      assume "\<not> F y < 1"
      hence "F y = 1"
        using f_le_b[of y] by linarith
      hence "y \<le> x \<Longrightarrow> F x = 1" for x
        using monoD[OF mono,of y x] f_le_b[of x] by simp
      hence "{x. F x < 1} \<subseteq> {..<y}"
        by (metis lessThan_iff linorder_not_le mem_Collect_eq order_less_irrefl subsetI)
      from cSup_subset_mono[OF _ _ this] ex_less_a[of 1] c
      show False
        by(auto simp: x_star_def)
    qed
  next
    assume y: "F y < 1"
    hence "y \<le> x_star F"
      unfolding x_star_def using bdd by (auto intro!: cSup_upper)
    thus "y < x_star F"
      using y F_x_star_eq_1[OF F bdd] by (metis order_less_le)
  qed
qed

lemma F_lt_1_unbdd_support:
  assumes F: "right_continuous_mono F 0 1" and bdd: "\<not> bdd_support F"
  shows "F x < 1"
proof (rule ccontr)
  interpret right_continuous_mono F 0 1
    by fact
  assume "\<not> F x < 1"
  hence Fx: "F x = 1"
    using f_le_b[of x] by linarith
  hence Fx1:"x \<le> y \<Longrightarrow> F y = 1" for y
    using monoD[OF mono,of x y] f_le_b[of y] by simp
  hence "{x. F x < 1} \<subseteq> {..<x}"
    by (metis lessThan_iff linorder_not_le mem_Collect_eq order_less_irrefl subsetI)
  with bdd show False
    by (meson bdd_above.mono bdd_above_Iio)
qed

lemma F_lt_1_endpoint:
  fixes F :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1"
  shows "\<forall>\<^sub>F t in endpoint_filter F. F t < 1"
  using F_lt_1_unbdd_support[OF F] lt_x_star_iff_F_lt_1[OF F, THEN iffD1]
  by (cases "bdd_support F")
     (auto simp: endpoint_filter intro!: eventually_at_leftI[of "x_star F - 1"])

lemma tail_quantile_tendsto_x_star:
  fixes F :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and bdd: "bdd_support F"
  shows "(tail_quantile F \<longlongrightarrow> x_star F) at_top"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  have U_le_xstar: "tail_quantile F t \<le> x_star F" if t1: "1 < t" for t
    using t1 F_x_star_eq_1[OF F bdd] by (simp add: field_simps ginv_le_iff)
  show ?thesis
    unfolding tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    define c where "c = x_star F - e"
    have Fc: "F c < 1"
      by (rule lt_x_star_iff_F_lt_1[OF F bdd, THEN iffD1]) (simp add: c_def e)
    have tendsto1: "((\<lambda>t::real. 1 - 1 / t) \<longlongrightarrow> 1) at_top"
      using tendsto_diff[OF tendsto_const[of 1] tendsto_inverse_0_at_top[OF filterlim_ident]]
      by (simp add: inverse_eq_divide)
    obtain T1 where T1: "\<And>t. T1 \<le> t \<Longrightarrow> F c < 1 - 1 / t"
      using order_tendstoD(1)[OF tendsto1 Fc]
      unfolding eventually_at_top_linorder by blast
    define T where "T = max 2 T1"
    show "\<forall>\<^sub>F t in at_top. \<bar>tail_quantile F t - x_star F\<bar> < e"
    proof (intro eventually_at_top_linorderI[where c=T])
      fix t
      assume Tt: "T \<le> t"
      have t1: "1 < t" and T1t: "T1 \<le> t"
        using Tt by (simp_all add: T_def)
      have p_bounds: "0 < 1 - 1 / t" "1 - 1 / t < 1"
        using t1 by simp_all
      have lower: "c < tail_quantile F t"
        using ginv_le_iff[OF p_bounds, of c] T1[OF T1t] by linarith
      show "\<bar>tail_quantile F t - x_star F\<bar> < e"
        using lower U_le_xstar[OF t1] by (simp add: c_def)
    qed
  qed
qed

lemma tail_quantile_lt_x_star:
  fixes F :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1" and bdd: "bdd_support F"
    and Flim: "(F \<longlongrightarrow> 1) (endpoint_filter F)" and t1: "1 < t"
  shows "tail_quantile F t < x_star F"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  have p0: "0 < 1 - 1 / t" and p1: "1 - 1 / t < 1"
    using t1 by simp_all
  obtain y where y: "1 - 1 / t < F y" "F y < 1"
    using eventually_happens'[OF endpoint_filter_neq_bot
        eventually_conj[OF order_tendstoD(1)[OF Flim p1] F_lt_1_endpoint[OF F]]] by blast
  have "F (tail_quantile F t) < 1"
    using ginv_le_iff[OF p0 p1, of y] y monoD[OF mono, of "ginv F (1 - 1 / t)" y] by force
  moreover have "tail_quantile F t \<le> x_star F"
    using calculation bdd by (auto simp: x_star_def intro!: cSup_upper)
  ultimately show ?thesis
    using F_x_star_eq_1[OF F bdd] by (metis order_less_le)
qed

lemma tail_quantile_tendsto_endpoint:
  fixes F :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1"
    and Flim: "(F \<longlongrightarrow> 1) (endpoint_filter F)"
  shows "filterlim (tail_quantile F) (endpoint_filter F) at_top"
proof (cases "bdd_support F")
  case True
  have "\<forall>\<^sub>F t in at_top. tail_quantile F t \<in> {..<x_star F} \<and> tail_quantile F t \<noteq> x_star F"
    using eventually_gt_at_top[of "1::real"]
    by eventually_elim (use tail_quantile_lt_x_star[OF F True Flim] in force)
  thus ?thesis
    unfolding endpoint_filter(1)[OF True] filterlim_at
    using tail_quantile_tendsto_x_star[OF F True] by simp
next
  case False
  thus ?thesis
    using tail_quantile_at_top[OF F F_lt_1_unbdd_support[OF F]] by (simp add: endpoint_filter)
qed

lemma F_tendsto_1_endpoint_of_lim:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and f1:"\<And>t. bdd_support F \<Longrightarrow> t < x_star F \<Longrightarrow> 0 < f t"
    and f2:"\<And>t. \<not> bdd_support F \<Longrightarrow> 0 < f t"
    and sigma[arith]: "0 < \<sigma>"
    and lim:"\<And>x. 0 < 1 + \<gamma> * (x - \<mu>) / \<sigma>
             \<Longrightarrow> ((\<lambda>t. (1 - F (t + (x - \<mu>) * f t)) / (1 - F t))
                          \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) (endpoint_filter F)"
  shows "(F \<longlongrightarrow> 1) (endpoint_filter F)"
proof (cases "bdd_support F")
  assume "\<not> bdd_support F"
  thus ?thesis
    using right_continuous_mono.top[OF F]
    by (simp add: endpoint_filter)
next
  assume bdd:"bdd_support F"
  have goal_eq: "endpoint_filter F = at_left (x_star F)"
    using bdd by (simp add: endpoint_filter)
  have op: "open {x'. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>}"
    by (intro open_Collect_less continuous_intros) simp
  hence "\<forall>\<^sub>F x' in nhds \<mu>. x' \<in> {x'. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>}"
    by (intro eventually_nhds_in_open) auto
  then obtain \<eta> where eta: "0 < \<eta>" and eta_supp: "\<And>x'. \<bar>x' - \<mu>\<bar> < \<eta> \<Longrightarrow> 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>"
    using eventually_nhds_metric[of "\<lambda>x'. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>" \<mu>]
    by (auto simp: dist_real_def)
  define x1 where "x1 = \<mu> + \<eta> / 2"
  have x1_supp: "0 < 1 + \<gamma> * (x1 - \<mu>) / \<sigma>"
    using eta_supp[of x1] eta by (simp add: x1_def)
  have x1_gt: "\<mu> < x1"
    using eta by (simp add: x1_def)
  define c1 where "c1 = - ln (EVD_cdf \<gamma> \<mu> \<sigma> x1)"
  have c1_pos: "0 < c1"
    using x1_supp
    by(cases "\<gamma> = 0")
      (auto simp: c1_def ln_EVD_cdf_0 ln_EVD_cdf_1[OF sigma])
  have c1_lt1: "c1 < 1"
  proof (cases "\<gamma> = 0")
    show "\<gamma> = 0 \<Longrightarrow> ?thesis"
      using x1_gt by(simp add: ln_EVD_cdf_0 c1_def)
  next
    assume h:"\<not> \<gamma> = 0"
    have eq: "c1 = (1 + \<gamma> * (x1 - \<mu>) / \<sigma>) powr (- 1 / \<gamma>)"
      using ln_EVD_cdf_1[OF sigma x1_supp h] by (simp add: c1_def)
    show ?thesis
      by (smt (verit) h eq eta mult_eq_0_iff mult_pos_pos mult_sign_intros(3)
          powr01_less_one powr_less_one sigma x1_def x1_supp
          zero_compare_simps(11,7))
  qed
  have limx1: "((\<lambda>t. (1 - F (t + (x1 - \<mu>) * f t)) / (1 - F t)) \<longlongrightarrow> c1) (endpoint_filter F)"
    using lim[OF x1_supp] by (simp add: c1_def)
  define \<phi> where "\<phi> = (\<lambda>t. 1 - F t)"
  have phi_mono: "\<And>s t. s \<le> t \<Longrightarrow> \<phi> t \<le> \<phi> s"
    using monoD[OF right_continuous_mono.mono[OF F]] by (auto simp: \<phi>_def)
  have phi_ge0: "\<And>t. 0 \<le> \<phi> t"
    using right_continuous_mono.f_le_b[OF F] by (simp add: \<phi>_def)
  define L where "L = Inf (\<phi> ` {..<x_star F})"
  have ne: "\<phi> ` {..<x_star F} \<noteq> {}"
    by force
  have bddb: "bdd_below (\<phi> ` {..<x_star F})"
    using phi_ge0 by (intro bdd_belowI[of _ 0]) auto
  have Lge0: "0 \<le> L"
    unfolding L_def using phi_ge0 ne bddb by (intro cInf_greatest) auto
  have Lbound: "\<And>t. t < x_star F \<Longrightarrow> L \<le> \<phi> t"
    unfolding L_def using bddb by (intro cInf_lower) auto
  have phi_tendsto_L: "(\<phi> \<longlongrightarrow> L) (at_left (x_star F))"
  proof (rule order_tendstoI)
    fix c
    assume c: "c < L"
    have "\<forall>\<^sub>F t in at_left (x_star F). t < x_star F"
      by (rule eventually_at_leftI[of "x_star F - 1"]) auto
    thus "\<forall>\<^sub>F t in at_left (x_star F). c < \<phi> t"
      by(eventually_elim) (use Lbound c in fastforce)
  next
    fix c
    assume c: "L < c"
    obtain t0 where t0: "t0 < x_star F" "\<phi> t0 < c"
      using cInf_lessD[OF ne, of c] c unfolding L_def by force
    have "\<forall>\<^sub>F t in at_left (x_star F). t0 < t"
      using t0 by(auto intro!: eventually_at_leftI[of t0])
    thus "\<forall>\<^sub>F t in at_left (x_star F). \<phi> t < c"
      by eventually_elim (auto intro!: order.strict_trans1[of _ "\<phi> t0" c,OF phi_mono t0(2)])
  qed
  have "\<forall>\<^sub>F t in at_left (x_star F). c1 / 2 < (1 - F (t + (x1 - \<mu>) * f t)) / (1 - F t)"
    using order_tendstoD(1)[OF limx1, of "c1 / 2"] c1_pos goal_eq by simp
  hence t'_lt: "\<forall>\<^sub>F t in at_left (x_star F). t + (x1 - \<mu>) * f t < x_star F"
  proof eventually_elim
    case (elim t)
    show ?case
    proof (rule ccontr)
      assume "\<not> t + (x1 - \<mu>) * f t < x_star F"
      hence "F (x_star F) \<le> F (t + (x1 - \<mu>) * f t)"
        by (intro monoD[OF right_continuous_mono.mono[OF F]]) simp
      hence "F (t + (x1 - \<mu>) * f t) = 1"
        using right_continuous_mono.f_le_b[OF F, of "t + (x1 - \<mu>) * f t"]
          F_x_star_eq_1[OF F bdd] by simp
      with elim c1_pos show False
        by simp
    qed
  qed
  have "\<forall>\<^sub>F t in at_left (x_star F). t < x_star F"
    by (rule eventually_at_leftI[of "x_star F - 1"]) auto
  hence t'_ge: "\<forall>\<^sub>F t in at_left (x_star F). t \<le> t + (x1 - \<mu>) * f t"
    by eventually_elim (use f1[OF bdd] x1_gt in fastforce)
  have t'_tendsto: "((\<lambda>t. t + (x1 - \<mu>) * f t) \<longlongrightarrow> x_star F) (at_left (x_star F))"
    unfolding tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    have ev1: "\<forall>\<^sub>F t in at_left (x_star F). x_star F - e < t"
      by (intro order_tendstoD(1)[OF tendsto_ident_at]) (use e in simp)
    have lower: "\<forall>\<^sub>F t in at_left (x_star F). x_star F - e < t + (x1 - \<mu>) * f t"
      using eventually_conj[OF ev1 t'_ge] by eventually_elim simp
    show "\<forall>\<^sub>F t in at_left (x_star F). \<bar>t + (x1 - \<mu>) * f t - x_star F\<bar> < e"
      using lower t'_lt by eventually_elim linarith
  qed
  have t'_filterlim: "filterlim (\<lambda>t. t + (x1 - \<mu>) * f t)
                                (at_left (x_star F)) (at_left (x_star F))"
    using tendsto_imp_filterlim_at_left[OF t'_tendsto] t'_lt by blast
  have phit'_to_L: "((\<lambda>t. \<phi> (t + (x1 - \<mu>) * f t)) \<longlongrightarrow> L) (at_left (x_star F))"
    using filterlim_compose[OF phi_tendsto_L t'_filterlim] by simp
  have eq_ratio: "\<forall>\<^sub>F t in at_left (x_star F). ((1 - F (t + (x1 - \<mu>) * f t)) / (1 - F t)) * \<phi> t
                                          = \<phi> (t + (x1 - \<mu>) * f t)"
    using F_lt_1_endpoint[OF F] unfolding goal_eq
    by eventually_elim (simp add: \<phi>_def)
  have prod_tendsto: "((\<lambda>t. ((1 - F (t + (x1 - \<mu>) * f t)) / (1 - F t)) * \<phi> t)
                        \<longlongrightarrow> c1 * L) (at_left (x_star F))"
    using tendsto_mult[OF limx1[unfolded goal_eq] phi_tendsto_L] by simp
  note phit'_to_c1L = Lim_transform_eventually[OF prod_tendsto eq_ratio]
  have LeqC1L: "L = c1 * L"
    by (rule tendsto_unique[OF trivial_limit_at_left_real[of "x_star F"]
                               phit'_to_L phit'_to_c1L])
  have Lzero: "L = 0"
    using c1_lt1 LeqC1L by simp
  have z: "((\<lambda>t. 1 - F t) \<longlongrightarrow> 0) (at_left (x_star F))"
    using phi_tendsto_L Lzero by (simp add: \<phi>_def)
  have "((\<lambda>t. 1 - (1 - F t)) \<longlongrightarrow> 1 - (0::real)) (at_left (x_star F))"
    by (rule tendsto_diff[OF tendsto_const z])
  thus ?thesis
    by(simp add: goal_eq)
qed

lemma s_tendsto_at_top_endpoint:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and a:"\<And>n. 0 < a n"
    and sigma[arith]:"0 < \<sigma>"
    and wc:"\<And>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
  shows "filterlim (\<lambda>t. 1 / (1 - F t)) at_top (endpoint_filter F)"
proof -
  have Ftend: "((\<lambda>t. 1 - F t) \<longlongrightarrow> 0) (endpoint_filter F)"
    using tendsto_diff[OF tendsto_const[where k="1::real"]
        F_tendsto_1_endpoint[OF F a sigma wc]]
    by simp
  have Fpos: "\<forall>\<^sub>F t in endpoint_filter F. 0 < 1 - F t"
    using F_lt_1_endpoint[OF F] by (rule eventually_mono) simp
  show ?thesis
    using filterlim_inverse_at_top[OF Ftend Fpos]
    by (simp add: inverse_eq_divide)
qed

lemma t_div_a_tendsto_mu_endpoint:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and a:"\<And>n. 0 < a n"
    and sigma[arith]:"0 < \<sigma>"
    and wc:"\<And>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
  shows "((\<lambda>t. (t - b (nat \<lfloor>1 / (1 - F t)\<rfloor>))
                / a (nat \<lfloor>1 / (1 - F t)\<rfloor>)) \<longlongrightarrow> \<mu>) (endpoint_filter F)"
proof -
  define s where "s = (\<lambda>t::real. 1 / (1 - F t))"
  define N where "N = (\<lambda>t::real. nat \<lfloor>s t\<rfloor>)"
  have goal_eq: "(\<lambda>t. (t - b (nat \<lfloor>1 / (1 - F t)\<rfloor>)) / a (nat \<lfloor>1 / (1 - F t)\<rfloor>))
                   = (\<lambda>t. (t - b (N t)) / a (N t))"
    by (simp add: s_def N_def)
  have stop: "filterlim s at_top (endpoint_filter F)"
    unfolding s_def by (rule s_tendsto_at_top_endpoint[OF F a sigma wc])
  note Flt1 = F_lt_1_endpoint[OF F]
  have spos: "\<forall>\<^sub>F t in endpoint_filter F. 0 < s t"
    using stop[unfolded filterlim_at_top_dense, rule_format, of 0] by simp
  have MDAtq: "\<forall>y>0. ((\<lambda>t. (tail_quantile F (t * y) - b (nat \<lfloor>t\<rfloor>)) / a (nat \<lfloor>t\<rfloor>))
                 \<longlongrightarrow> (if \<gamma> = 0 then \<sigma> * ln y + \<mu>  else \<sigma> * (y powr \<gamma> - 1) / \<gamma> + \<mu>)) at_top"
    using MDA_iff_tail_quantile[OF F a sigma] wc by fast
  define D where "D = (\<lambda>y::real. if \<gamma> = 0 then \<sigma> * ln y + \<mu> else \<sigma> * (y powr \<gamma> - 1) / \<gamma> + \<mu>)"
  have D1:"D 1 = \<mu>"
    by(simp add: D_def)
  have Dcont: "isCont D 1"
    unfolding D_def
    by(cases "\<gamma> = 0")
      (auto intro!: isCont_add isCont_mult isCont_ln isCont_divide isCont_diff continuous_powr)
  have conv: "\<And>y'. \<bar>y' - 1\<bar> < 1 \<Longrightarrow>
      ((\<lambda>t. (tail_quantile F (s t * y') - b (N t)) / a (N t)) \<longlongrightarrow> D y') (endpoint_filter F)"
    using MDAtq by(auto simp: D_def N_def intro!: filterlim_compose[OF _ stop])
  have low: "\<forall>\<^sub>F t in endpoint_filter F. (tail_quantile F (s t * y') - b (N t)) / a (N t)
                                       \<le> (t - b (N t)) / a (N t)"
    if y': "(1::real) - 1 < y'" "y' < 1" for y'
    using stop[unfolded filterlim_at_top_dense, rule_format, of "1 / y'"] spos Flt1
  proof eventually_elim
    case (elim t)
    hence s_gt: "1 / y' < s t" and s_pos: "0 < s t" and Ft: "F t < 1"
      by auto
    have u1: "1 < s t * y'"
      using mult_strict_right_mono[OF s_gt] y' by force
    have u2: "s t * y' < 1 / (1 - F t)"
      using mult_strict_left_mono[OF y'(2) s_pos]
      by(simp add: s_def)
    show ?case
      using a[of "N t"] Ft u1 u2
      by(auto intro!: divide_right_mono tail_quantile_le_of_lt_inv[OF F])
  qed
  have up: "\<forall>\<^sub>F t in endpoint_filter F. (t - b (N t)) / a (N t)
                                       \<le> (tail_quantile F (s t * y') - b (N t)) / a (N t)"
    if y': "(1::real) < y'" "y' < 1 + 1" for y'
    using spos Flt1
  proof eventually_elim
    case (elim t)
    hence s_pos: "0 < s t" and Ft: "F t < 1"
      by auto
    have u: "1 / (1 - F t) < s t * y'"
      using mult_strict_left_mono[OF _ s_pos] y'
      by(simp add: s_def)
    show ?case
      using a[of "N t"]
      by(auto intro!: divide_right_mono less_imp_le[OF t_lt_tail_quantile_of_gt_inv[OF F Ft u]])
  qed
  show ?thesis
    using squeeze_tendsto_local[OF zero_less_one Dcont conv low up]
    unfolding goal_eq
    by (simp add: D1)
qed

lemma MDA_imp_divide_tail:
  assumes F: "right_continuous_mono F 0 1"
    and a:"\<And>n. 0 < a n"
    and sigma[arith]:"0 < \<sigma>"
    and wc:"\<And>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
    and x:"0 < 1 + \<gamma> * (x - \<mu>) / \<sigma>"
  shows "((\<lambda>t. (1 - F (t + (x - \<mu>) * a (nat \<lfloor>1 / (1 - F (t))\<rfloor>))) / (1 - F t))
                          \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) (endpoint_filter F)"
proof -
  define s where "s = (\<lambda>t::real. 1 / (1 - F t))"
  define N where "N = (\<lambda>t::real. nat \<lfloor>s t\<rfloor>)"
  have goal_eq: "(\<lambda>t. (1 - F (t + (x - \<mu>) * a (nat \<lfloor>1 / (1 - F (t))\<rfloor>))) / (1 - F t))
                   = (\<lambda>t. (1 - F (t + (x - \<mu>) * a (N t))) / (1 - F t))"
    by (simp add: s_def N_def)
  have stop: "filterlim s at_top (endpoint_filter F)"
    unfolding s_def by(intro s_tendsto_at_top_endpoint[OF _ _ _ wc] assms)
  note Flt1 = F_lt_1_endpoint[OF F]
  have delta_tendsto: "((\<lambda>t. (t - b (N t)) / a (N t) - \<mu>) \<longlongrightarrow> 0) (endpoint_filter F)"
    using tendsto_diff[OF t_div_a_tendsto_mu_endpoint[OF F a sigma wc] tendsto_const[of \<mu>]]
    by(simp add: s_def N_def)
  have op: "open {x'. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>}"
    by (auto intro!: open_Collect_less continuous_on_add
        continuous_on_divide continuous_on_mult continuous_on_diff)
  have "\<forall>\<^sub>F x' in nhds x. x' \<in> {x'. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>}"
    using x op by (intro eventually_nhds_in_open) auto
  hence ev: "\<forall>\<^sub>F x' in nhds x. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>"
    by eventually_elim simp
  then obtain \<eta> where eta: "0 < \<eta>"
    and eta_supp: "\<And>x'. \<bar>x' - x\<bar> < \<eta> \<Longrightarrow> 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>"
    using eventually_nhds_metric[of "\<lambda>x'. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>" x]
    by(auto simp: dist_real_def)
  have Dcont: "isCont (\<lambda>x'. ln (EVD_cdf \<gamma> \<mu> \<sigma> x')) x"
    using EVD_cdf_supp_bounds[OF x sigma]
    by(auto intro!: isCont_ln' isCont_EVD_cdf)
  have conv: "((\<lambda>t. - ((1 - F (a (N t) * x' + b (N t))) / (1 - F t)))
         \<longlongrightarrow> ln (EVD_cdf \<gamma> \<mu> \<sigma> x')) (endpoint_filter F)"
    if x': "\<bar>x' - x\<bar> < \<eta>" for x'
  proof -
    have supp': "0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>"
      using that eta_supp by simp
    have base: "((\<lambda>t. t * (1 - F (a (nat \<lfloor>t\<rfloor>) * x' + b (nat \<lfloor>t\<rfloor>))))
                    \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x')) at_top"
      using MDA_iff_tail_probability[where a=a,OF F a sigma] wc eta_supp supp' by blast
    show ?thesis
      using tendsto_minus[OF filterlim_compose[OF base stop]] by(simp add: N_def s_def)
  qed
  have low: "\<forall>\<^sub>F t in endpoint_filter F. - ((1 - F (a (N t) * x' + b (N t))) / (1 - F t))
                                       \<le> - ((1 - F (t + (x - \<mu>) * a (N t))) / (1 - F t))"
    if  x': "x - \<eta> < x'" "x' < x" for x'
  proof -
    have dlt: "x' - x < 0"
      using x' by simp
    have ev1: "\<forall>\<^sub>F t in endpoint_filter F. x' - x < (t - b (N t)) / a (N t) - \<mu>"
      using order_tendstoD(1)[OF delta_tendsto dlt] .
    show "\<forall>\<^sub>F t in endpoint_filter F. - ((1 - F (a (N t) * x' + b (N t))) / (1 - F t))
                                       \<le> - ((1 - F (t + (x - \<mu>) * a (N t))) / (1 - F t))"
      using ev1 Flt1
    proof eventually_elim
      case (elim t)
      hence d: "x' - x < (t - b (N t)) / a (N t) - \<mu>" and Ft: "F t < 1"
        by auto
      have apos: "0 < a (N t)"
        using a by simp
      have "(x' - x) * a (N t) < ((t - b (N t)) / a (N t) - \<mu>) * a (N t)"
        using mult_strict_right_mono[OF d apos] .
      also have "\<dots> = t - b (N t) - \<mu> * a (N t)"
        using apos by (simp add: field_simps)
      finally have ineq: "(x' - x) * a (N t) < t - b (N t) - \<mu> * a (N t)" .
      have "a (N t) * x' + b (N t) < t + (x - \<mu>) * a (N t)"
        using ineq by (simp add: field_simps)
      hence fmono: "F (a (N t) * x' + b (N t)) \<le> F (t + (x - \<mu>) * a (N t))"
        by (intro monoD[OF right_continuous_mono.mono[OF F]]) simp
      have hFQ: "1 - F (t + (x - \<mu>) * a (N t)) \<le> 1 - F (a (N t) * x' + b (N t))"
        using fmono by simp
      have "(1 - F (t + (x - \<mu>) * a (N t))) / (1 - F t)
              \<le> (1 - F (a (N t) * x' + b (N t))) / (1 - F t)"
        by (rule divide_right_mono[OF hFQ]) (use Ft in simp)
      thus ?case
        by simp
    qed
  qed
  have up: "\<And>x'. x < x' \<Longrightarrow> x' < x + \<eta> \<Longrightarrow>
      \<forall>\<^sub>F t in endpoint_filter F. - ((1 - F (t + (x - \<mu>) * a (N t))) / (1 - F t))
                                       \<le> - ((1 - F (a (N t) * x' + b (N t))) / (1 - F t))"
  proof -
    fix x' :: real
    assume x': "x < x'" "x' < x + \<eta>"
    have dpos: "0 < x' - x"
      using x' by simp
    have ev1: "\<forall>\<^sub>F t in endpoint_filter F. (t - b (N t)) / a (N t) - \<mu> < x' - x"
      using order_tendstoD(2)[OF delta_tendsto dpos] .
    show "\<forall>\<^sub>F t in endpoint_filter F. - ((1 - F (t + (x - \<mu>) * a (N t))) / (1 - F t))
                                       \<le> - ((1 - F (a (N t) * x' + b (N t))) / (1 - F t))"
      using ev1 Flt1
    proof eventually_elim
      case (elim t)
      hence d: "(t - b (N t)) / a (N t) - \<mu> < x' - x" and Ft: "F t < 1"
        by auto
      have apos: "0 < a (N t)"
        using a by simp
      have "((t - b (N t)) / a (N t) - \<mu>) * a (N t) < (x' - x) * a (N t)"
        using mult_strict_right_mono[OF d apos] .
      also have "((t - b (N t)) / a (N t) - \<mu>) * a (N t) = t - b (N t) - \<mu> * a (N t)"
        using apos by (simp add: field_simps)
      finally have ineq: "t - b (N t) - \<mu> * a (N t) < (x' - x) * a (N t)"
        by simp
      have "t + (x - \<mu>) * a (N t) < a (N t) * x' + b (N t)"
        using ineq by (simp add: field_simps)
      hence fmono: "F (t + (x - \<mu>) * a (N t)) \<le> F (a (N t) * x' + b (N t))"
        by (intro monoD[OF right_continuous_mono.mono[OF F]]) simp
      have hFQ: "1 - F (a (N t) * x' + b (N t)) \<le> 1 - F (t + (x - \<mu>) * a (N t))"
        using fmono by simp
      have "(1 - F (a (N t) * x' + b (N t))) / (1 - F t)
              \<le> (1 - F (t + (x - \<mu>) * a (N t))) / (1 - F t)"
        by (rule divide_right_mono[OF hFQ]) (use Ft in simp)
      thus ?case
        by simp
    qed
  qed
  show ?thesis
    unfolding goal_eq
    using tendsto_minus[OF squeeze_tendsto_local[OF eta Dcont conv low up]]
    by simp
qed

lemma tail_quantile_asymp_inverse_of_lim:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and f1:"\<And>t. bdd_support F \<Longrightarrow> t < x_star F \<Longrightarrow> 0 < f t"
    and f2:"\<And>t. \<not> bdd_support F \<Longrightarrow> 0 < f t"
    and sigma[arith]: "0 < \<sigma>"
    and lim:"\<And>x. 0 < 1 + \<gamma> * (x - \<mu>) / \<sigma>
             \<Longrightarrow> ((\<lambda>t. (1 - F (t + (x - \<mu>) * f t)) / (1 - F t))
                          \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) (endpoint_filter F)"
  shows "((\<lambda>t. t * (1 - F (tail_quantile F t))) \<longlongrightarrow> 1) at_top"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  note Flim = F_tendsto_1_endpoint_of_lim[OF F f1 f2 sigma lim]
  note Uendpoint = tail_quantile_tendsto_endpoint[OF F Flim]
  have fU_pos: "0 < f (tail_quantile F t)" if t1: "1 < t" for t
  proof (cases "bdd_support F")
    case True
    show ?thesis
      by (rule f1[OF True tail_quantile_lt_x_star[OF F True Flim t1]])
  next
    case False
    show ?thesis
      by (rule f2[OF False])
  qed
  have fact_le1: "\<And>t. 1 < t \<Longrightarrow> t * (1 - F (tail_quantile F t)) \<le> 1"
    by (smt (verit, best) divide_less_eq zero_less_mult_iff t_lt_tail_quantile_of_gt_inv[OF F])
  have fact_gt1: "\<And>t z. 1 < t \<Longrightarrow> z < tail_quantile F t \<Longrightarrow> 1 < t * (1 - F z)"
    by (smt (verit, ccfv_SIG) divide_less_eq_1_pos divide_pos_pos
        nonzero_mult_div_cancel_left pos_less_divide_eq
        ginv_le_iff)
  have FUlt1: "\<forall>\<^sub>F t in at_top. F (tail_quantile F t) < 1"
    by (rule eventually_compose_filterlim[OF F_lt_1_endpoint[OF F] Uendpoint])
  define D where "D = (\<lambda>x'. - ln (EVD_cdf \<gamma> \<mu> \<sigma> x'))"
  have Dmu: "D \<mu> = 1"
    by (cases "\<gamma> = 0") (simp_all add: D_def ln_EVD_cdf_0 ln_EVD_cdf_1)
  have supp_mu: "0 < 1 + \<gamma> * (\<mu> - \<mu>) / \<sigma>"
    by simp
  have Dcont: "isCont D \<mu>"
    unfolding D_def
    using isCont_EVD_cdf[OF sigma] EVD_cdf_supp_bounds[OF supp_mu sigma]
    by (intro continuous_intros) auto
  have op: "open {x'. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>}"
    by (intro open_Collect_less continuous_intros) simp
  have "\<forall>\<^sub>F x' in nhds \<mu>. x' \<in> {x'. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>}"
    using op by (intro eventually_nhds_in_open) auto
  hence ev: "\<forall>\<^sub>F x' in nhds \<mu>. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>"
    by eventually_elim simp
  then obtain \<eta> where eta: "0 < \<eta>" and eta_supp: "\<And>x'. \<bar>x' - \<mu>\<bar> < \<eta> \<Longrightarrow> 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>"
    using eventually_nhds_metric[of "\<lambda>x'. 0 < 1 + \<gamma> * (x' - \<mu>) / \<sigma>" \<mu>]
    by(auto simp: dist_real_def)
  have upper: "t * (1 - F (tail_quantile F t)) \<le> 1" if t1: "1 < t" for t
    using fact_le1[OF t1] .
  show ?thesis
    unfolding tendsto_iff dist_real_def
  proof safe
    fix e :: real
    assume e: "0 < e"
    define e' where "e' = min (1 / 2) e"
    have e'_pos: "0 < e'" and e'_le: "e' \<le> e" and e'_lt1: "e' < 1"
      using e by (simp_all add: e'_def)
    define c where "c = 1 - e'"
    have cpos[arith]: "0 < c" and clt1[arith]: "c < 1"
      using e'_pos e'_lt1 by (simp_all add: c_def)
    define c' where "c' = 1 / c"
    have c'gt1: "1 < c'"
      by (simp add: c'_def)
    obtain \<delta> where \<delta>pos: "0 < \<delta>"
      and \<delta>bound: "\<And>x''. x'' \<noteq> \<mu> \<and> \<bar>x'' - \<mu>\<bar> < \<delta> \<Longrightarrow> \<bar>D x'' - D \<mu>\<bar> < c' - 1"
      using LIM_D[OF Dcont[unfolded isCont_def], of "c' - 1"] c'gt1 by auto
    have minpos: "0 < min \<delta> \<eta>" "min \<delta> \<eta> \<le> \<delta>" "min \<delta> \<eta> \<le> \<eta>"
      using \<delta>pos eta by auto
    define x1 where "x1 = \<mu> - min \<delta> \<eta> / 2"
    have x1_diff: "x1 - \<mu> = - (min \<delta> \<eta> / 2)"
      by (simp add: x1_def)
    have x1_abs: "\<bar>x1 - \<mu>\<bar> = min \<delta> \<eta> / 2"
      using minpos(1) by (simp add: x1_diff)
    have x1_ne: "x1 \<noteq> \<mu> \<and> \<bar>x1 - \<mu>\<bar> < \<delta>"
      using minpos x1_abs by linarith
    have x1_eta: "\<bar>x1 - \<mu>\<bar> < \<eta>"
      using minpos x1_abs by linarith
    have x1_lt: "x1 < \<mu>"
      using minpos x1_diff by linarith
    have x1_supp: "0 < 1 + \<gamma> * (x1 - \<mu>) / \<sigma>"
      using eta_supp[OF x1_eta] .
    have Dx1: "D x1 < c'"
      using \<delta>bound[OF x1_ne] Dmu by linarith
    have Dx1_pos: "0 < D x1"
      using x1_supp by (cases "\<gamma> = 0")
                       (auto simp: EVD_cdf_def D_def)
    have ratio: "((\<lambda>t. (1 - F (tail_quantile F t + (x1 - \<mu>) * f (tail_quantile F t)))
                        / (1 - F (tail_quantile F t))) \<longlongrightarrow> D x1) at_top"
      using filterlim_compose[OF lim[OF x1_supp] Uendpoint] by (simp add: D_def)
    obtain T1 where T1: "\<And>t. T1 \<le> t \<Longrightarrow>
        (1 - F (tail_quantile F t + (x1 - \<mu>) * f (tail_quantile F t)))
          / (1 - F (tail_quantile F t)) < c'"
      using order_tendstoD(2)[OF ratio Dx1] unfolding eventually_at_top_linorder by blast
    obtain T2 where T2: "\<And>t. T2 \<le> t \<Longrightarrow> 0 <
        (1 - F (tail_quantile F t + (x1 - \<mu>) * f (tail_quantile F t)))
          / (1 - F (tail_quantile F t))"
      using order_tendstoD(1)[OF ratio Dx1_pos] unfolding eventually_at_top_linorder
      by blast
    obtain T3 where T3: "\<And>t. T3 \<le> t \<Longrightarrow> F (tail_quantile F t) < 1"
      using FUlt1 unfolding eventually_at_top_linorder by blast
    define T where "T = max (max T1 T2) (max T3 2)"
    have lower_ev: "\<forall>\<^sub>F t in at_top. c < t * (1 - F (tail_quantile F t))"
    proof (intro eventually_at_top_linorderI[where c=T])
      fix t
      assume Tt: "T \<le> t"
      have T1t: "T1 \<le> t" and T2t: "T2 \<le> t" and T3t: "T3 \<le> t" and t1: "1 < t"
        using Tt by (simp_all add: T_def)
      have rlt: "(1 - F (tail_quantile F t + (x1 - \<mu>) * f (tail_quantile F t)))
                   / (1 - F (tail_quantile F t)) < c'"
        using T1[OF T1t] .
      have rpos: "0 < (1 - F (tail_quantile F t + (x1 - \<mu>) * f (tail_quantile F t)))
                   / (1 - F (tail_quantile F t))"
        using T2[OF T2t] .
      have FUlt: "F (tail_quantile F t) < 1"
        using T3[OF T3t] .
      have gt1: "1 < t * (1 - F (tail_quantile F t + (x1 - \<mu>) * f (tail_quantile F t)))"
        using x1_lt fU_pos[OF t1] by(auto intro!: fact_gt1 t1 mult_neg_pos)
      have "t * (1 - F (tail_quantile F t + (x1 - \<mu>) * f (tail_quantile F t)))
            < t * (c' * (1 - F (tail_quantile F t)))"
        using rlt FUlt t1
        by(intro comm_mult_strict_left_mono)
          (auto simp: field_simps)
      hence "c * 1 < c * (t * (1 - F (tail_quantile F t)) / c)"
        using gt1 order.strict_trans
        by(intro mult_strict_left_mono) (fastforce simp: c'_def)+
      thus "c < t * (1 - F (tail_quantile F t))"
        by simp
    qed
    have upper_ev: "\<forall>\<^sub>F t in at_top. t * (1 - F (tail_quantile F t)) \<le> 1"
      using eventually_gt_at_top[of "1::real"] by eventually_elim (use upper in blast)
    show "\<forall>\<^sub>F t in at_top. \<bar>t * (1 - F (tail_quantile F t)) - 1\<bar> < e"
      using lower_ev upper_ev
      by eventually_elim (use e'_le in "simp add: c_def")
  qed
qed

lemma divide_tail_imp_MDA:
  assumes F: "right_continuous_mono F 0 1"
    and a:"\<And>n. 0 < a n"
    and sigma[arith]:"0 < \<sigma>"
    and f1:"\<And>t. bdd_support F \<Longrightarrow> t < x_star F \<Longrightarrow> 0 < f t"
    and f2:"\<And>t. \<not> bdd_support F \<Longrightarrow> 0 < f t"
    and lim:"\<And>x. 0 < 1 + \<gamma> * (x - \<mu>) / \<sigma>
             \<Longrightarrow> ((\<lambda>t. (1 - F (t + (x - \<mu>) * f t)) / (1 - F t))
                          \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) (endpoint_filter F)"
  shows "\<exists>a b. (\<forall>n. 0 < a n) \<and> (\<forall>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x)"
proof -
  note Flim = F_tendsto_1_endpoint_of_lim[OF F f1 f2 sigma lim]
  note Uendpoint = tail_quantile_tendsto_endpoint[OF F Flim]
  have fU_pos: "0 < f (tail_quantile F t)" if t1:"1 < t" for t
  proof (cases "bdd_support F")
    case True
    show ?thesis
      by (rule f1[OF True tail_quantile_lt_x_star[OF F True Flim t1]])
  next
    case False
    show ?thesis
      by (rule f2[OF False])
  qed
  note asymp = tail_quantile_asymp_inverse_of_lim[OF F f1 f2 sigma lim]
  note Flt1 = F_lt_1_endpoint[OF F]
  have FUlt1: "\<forall>\<^sub>F t in at_top. F (tail_quantile F t) < 1"
    by (rule eventually_compose_filterlim[OF Flt1 Uendpoint])
  define A where "A = (\<lambda>t. if 1 < t then f (tail_quantile F t) else f (tail_quantile F 2))"
  define B where "B = (\<lambda>t. if 1 < t then tail_quantile F t - \<mu> * f (tail_quantile F t)
                                  else tail_quantile F 2 - \<mu> * f (tail_quantile F 2))"
  have A_pos: "\<And>t. 0 < A t"
    using fU_pos[of 2] fU_pos by(auto simp: A_def)
  have AB_eq: "\<And>t. 1 < t \<Longrightarrow> A t = f (tail_quantile F t)"
              "\<And>t. 1 < t \<Longrightarrow> B t = tail_quantile F t - \<mu> * f (tail_quantile F t)"
    unfolding A_def B_def by simp_all
  have tail: "\<And>x. 0 < 1 + \<gamma> * (x - \<mu>) / \<sigma> \<Longrightarrow>
       ((\<lambda>t. t * (1 - F (A t * x + B t))) \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) at_top"
  proof -
    fix x :: real
    assume supp: "0 < 1 + \<gamma> * (x - \<mu>) / \<sigma>"
    have argeq: "\<And>t. 1 < t \<Longrightarrow>
   A t * x + B t = tail_quantile F t + (x - \<mu>) * f (tail_quantile F t)"
      using AB_eq by (simp add: algebra_simps)
    have prod: "((\<lambda>t. (t * (1 - F (tail_quantile F t))) *
                    ((1 - F (tail_quantile F t + (x - \<mu>) * f (tail_quantile F t)))
                        / (1 - F (tail_quantile F t))))
                  \<longlongrightarrow> 1 * (- ln (EVD_cdf \<gamma> \<mu> \<sigma> x))) at_top"
      by (intro tendsto_mult asymp filterlim_compose[OF lim[OF supp] Uendpoint])
    have eqprod: "\<forall>\<^sub>F t in at_top. (t * (1 - F (tail_quantile F t))) *
                    ((1 - F (tail_quantile F t + (x - \<mu>) * f (tail_quantile F t)))
                        / (1 - F (tail_quantile F t)))
                  = t * (1 - F (tail_quantile F t + (x - \<mu>) * f (tail_quantile F t)))"
      using FUlt1 by eventually_elim (simp add: field_simps)
    have main: "((\<lambda>t. t * (1 - F (tail_quantile F t + (x - \<mu>) * f (tail_quantile F t))))
                    \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) at_top"
      using Lim_transform_eventually[OF prod eqprod] by simp
    have eqarg: "\<forall>\<^sub>F t in at_top.
  t * (1 - F (tail_quantile F t + (x - \<mu>) * f (tail_quantile F t)))
  = t * (1 - F (A t * x + B t))"
      using eventually_gt_at_top[of "1::real"] by eventually_elim (simp add: argeq)
    show "((\<lambda>t. t * (1 - F (A t * x + B t))) \<longlongrightarrow> - ln (EVD_cdf \<gamma> \<mu> \<sigma> x)) at_top"
      by (rule Lim_transform_eventually[OF main eqarg])
  qed
  define aa where "aa = (\<lambda>n::nat. A (real n))"
  define bb where "bb = (\<lambda>n::nat. B (real n))"
  have aa_pos: "\<forall>n. 0 < aa n"
    unfolding aa_def using A_pos by simp
  have main: "\<forall>x. (\<lambda>n. F (aa n * x + bb n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> \<mu> \<sigma> x"
    using MDA_tail_probability_witness[OF F A_pos sigma tail]
    by(auto simp: aa_def bb_def)
  show ?thesis
    using aa_pos main by blast
qed

lemma MDA_iff_divide_tail:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
  shows "domain_of_attraction F (EVD_cdf \<gamma> 0 1)
          \<longleftrightarrow> (\<exists>f. (\<forall>t. 0 < f t) \<and>
                  (\<forall>x. 1 + \<gamma> * x > 0 \<longrightarrow>
                       ((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
                          \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F)))"
proof
  assume dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  obtain a b where a: "\<And>n. 0 < a n"
    and "weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) (EVD_cdf \<gamma> 0 1)"
    using dom unfolding domain_of_attraction_def by blast
  hence wc: "\<And>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 x"
    by(simp add: weak_conv_EVD_cdf_iff)
  define f where "f = (\<lambda>t. a (nat \<lfloor>1 / (1 - F t)\<rfloor>))"
  have fpos: "\<And>t. 0 < f t"
    using a by (simp add: f_def)
  have lim: "\<And>x. 0 < 1 + \<gamma> * x \<Longrightarrow>
          ((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
             \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F)"
  proof -
    fix x :: real
    assume x: "0 < 1 + \<gamma> * x"
    have x': "0 < 1 + \<gamma> * (x - 0) / 1"
      using x by simp
    show "((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
             \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F)"
      using MDA_imp_divide_tail[OF F a zero_less_one wc x']
      by (simp add: f_def)
  qed
  show "\<exists>f. (\<forall>t. 0 < f t) \<and>
                  (\<forall>x. 1 + \<gamma> * x > 0 \<longrightarrow>
                       ((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
                          \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F))"
    using fpos lim by blast
next
  assume "\<exists>f. (\<forall>t. 0 < f t) \<and>
                  (\<forall>x. 1 + \<gamma> * x > 0 \<longrightarrow>
                       ((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
                          \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F))"
  then obtain f where fpos: "\<And>t. 0 < f t"
    and lim: "\<And>x. 1 + \<gamma> * x > 0 \<Longrightarrow>
                  ((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
                     \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F)"
    by blast
  have lim': "\<And>x. 0 < 1 + \<gamma> * (x - 0) / 1 \<Longrightarrow>
                  ((\<lambda>t. (1 - F (t + (x - 0) * f t)) / (1 - F t))
                     \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F)"
    using lim by simp
  have ex: "\<exists>a b. (\<forall>n. 0 < a n) \<and> (\<forall>x. (\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 x)"
    using divide_tail_imp_MDA[where \<mu> = 0 and \<sigma> = 1 and f = f and a = "\<lambda>n::nat. 1"
        ,OF F _ _ _ _ lim'] fpos
    by auto
  thus "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
    unfolding domain_of_attraction_def
    using F right_continuous_mono_EVD_cdf[OF zero_less_one]
    by(auto simp: weak_conv_EVD_cdf_iff)
qed

subsection \<open>von Mises' Conditions\<close>
lemma
  fixes F :: "real \<Rightarrow> real" and x0 t :: real
  assumes F: "right_continuous_mono F 0 1"
    and x0: "F x0 < 1"
    and Flim: "(F \<longlongrightarrow> 1) (endpoint_filter F)"
    and Fcont: "\<And>x. x0 < x \<Longrightarrow> F x < 1 \<Longrightarrow> isCont F x"
    and t: "1 / (1 - F x0) < t"
  shows tail_quantile_tail_eq: "1 - F (tail_quantile F t) = 1 / t"
    and F_tail_quantile_lt_1: "F (tail_quantile F t) < 1"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  have t1: "1 < t"
    using one_less_of_inverse_tail_less[OF F x0 t] .
  define p where "p = 1 - 1 / t"
  have p0: "0 < p" and p1: "p < 1"
    using t1 by (simp_all add: p_def)
  have px0: "F x0 < p"
    using t x0 t1 by (simp add: p_def field_simps)
  have c_gt: "x0 < ginv F p"
    using ginv_le_iff[OF p0 p1, of x0] px0 by force
  obtain y where y: "p < F y" "F y < 1"
    using eventually_happens'[OF endpoint_filter_neq_bot
        eventually_conj[OF order_tendstoD(1)[OF Flim p1] F_lt_1_endpoint[OF F]]] by blast
  have Fc1: "F (ginv F p) < 1"
    using ginv_le_iff[OF p0 p1, of y] y monoD[OF mono, of "ginv F p" y] by force
  have "F (ginv F p) \<le> p"
  proof (rule tendsto_upperbound[where F = "at_left (ginv F p)"])
    show "(F \<longlongrightarrow> F (ginv F p)) (at_left (ginv F p))"
      using Fcont[OF c_gt Fc1] by (simp add: isCont_def Lim_at_imp_Lim_at_within)
    show "\<forall>\<^sub>F z in at_left (ginv F p). F z \<le> p"
      by (intro eventually_at_leftI[OF _ c_gt])
         (force simp: linorder_not_le[symmetric] ginv_le_iff[OF p0 p1])
  qed (rule trivial_limit_at_left_real)
  thus eq: "1 - F (tail_quantile F t) = 1 / t"
    using ginv_attained[OF p0 p1] unfolding p_def by linarith
  show "F (tail_quantile F t) < 1"
    using eq zero_less_divide_1_iff[of t] t1 by linarith
qed

context
  fixes F f :: "real \<Rightarrow> real" and x0 :: real
  assumes F: "right_continuous_mono F 0 1"
    and x0: "F x0 < 1"
    and Flim: "(F \<longlongrightarrow> 1) (endpoint_filter F)"
    and Fderiv: "\<And>y. x0 < y \<Longrightarrow> F y < 1 \<Longrightarrow> (F has_real_derivative f y) (at y)"
    and fpos: "\<And>y. x0 < y \<Longrightarrow> F y < 1 \<Longrightarrow> 0 < f y"
begin

lemma tail_quantile_has_deriv:
  fixes t :: real
  assumes t: "1 / (1 - F x0) < t"
  shows "(tail_quantile F has_real_derivative
            1 / (t\<^sup>2 * f (tail_quantile F t))) (at t)"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  define T where "T = 1 / (1 - F x0)"
  define U where "U = tail_quantile F"
  define phi where "phi = (\<lambda>s. 1 / (1 - F s))"
  have smono: "F v < F w" if "x0 < v" "v < w" "F w < 1" for v w
    by (rule strict_mono_of_deriv[OF Fderiv fpos that])
  have s1: "1 < s" if "T < s" for s
    using one_less_of_inverse_tail_less[OF F x0] that by (simp add: T_def)
  have Ugt: "x0 < U s" if "T < s" for s
    using t_lt_tail_quantile_of_gt_inv[OF F x0] that by (simp add: U_def T_def)
  have UF: "1 - F (U s) = 1 / s" if "T < s" for s
    using tail_quantile_tail_eq[OF F x0 Flim DERIV_isCont[OF Fderiv]] that
    by (simp add: U_def T_def)
  have UFlt: "F (U s) < 1" if "T < s" for s
    using F_tail_quantile_lt_1[OF F x0 Flim DERIV_isCont[OF Fderiv]] that
    by (simp add: U_def T_def)
  have phi_U: "phi (U s) = s" if "T < s" for s
    using UF[OF that] s1[OF that] by (simp add: phi_def)
  have phi_deriv: "(phi has_real_derivative f z / (1 - F z)\<^sup>2) (at z)"
    if z: "x0 < z" "F z < 1" for z
    unfolding phi_def using Fderiv[OF z] z
    by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  have t_gt: "T < t"
    using t by (simp add: T_def)
  obtain w where wgt: "U t < w" and wlt1: "F w < 1"
    using ex_gt_less UFlt t_gt by blast
  define d where "d = min (U t - x0) (w - U t) / 2"
  have d0: "0 < d"
    using Ugt[OF t_gt] wgt by (simp add: d_def)
  have inreg: "x0 < z" "F z < 1" if zd: "\<bar>z - U t\<bar> \<le> d" for z
  proof -
    have dlo: "d < U t - x0" and dhi: "d < w - U t"
      using Ugt[OF t_gt] wgt by (auto simp: d_def)
    show "x0 < z"
      using zd dlo by (simp add: abs_le_iff)
    have "z < w"
      using zd dhi by (simp add: abs_le_iff)
    thus "F z < 1"
      using monoD[OF mono, of z w] wlt1 by simp
  qed
  have isC: "isCont U t"
  proof (subst phi_U[OF t_gt, symmetric],
         rule isCont_inverse_function[where f = phi and g = U and x = "U t" and d = d,
           OF d0])
    fix z
    assume z: "\<bar>z - U t\<bar> \<le> d"
    show "U (phi z) = z" "isCont phi z"
      using ginv_f_eq[OF smono inreg[OF z]] inreg[OF z]
        DERIV_isCont[OF phi_deriv[OF inreg[OF z]]]
      by (simp_all add: U_def phi_def)
  qed
  have D: "(phi has_real_derivative t\<^sup>2 * f (U t)) (at (U t))"
    using UF[OF t_gt] s1[OF t_gt] phi_deriv[OF Ugt[OF t_gt] UFlt[OF t_gt]]
    by (simp add: power_one_over mult.commute)
  have "(U has_real_derivative inverse (t\<^sup>2 * f (U t))) (at t)"
  proof (rule DERIV_inverse_function[OF D _ t_gt less_add_one _ isC])
    show "t\<^sup>2 * f (U t) \<noteq> 0"
      using fpos[OF Ugt[OF t_gt] UFlt[OF t_gt]] s1[OF t_gt] by simp
    fix y
    assume "T < y" "y < t + 1"
    thus "phi (U y) = y"
      by (simp add: phi_U)
  qed
  thus ?thesis
    by (simp add: U_def inverse_eq_divide)
qed

lemma f_tail_quantile_pos:
  fixes t :: real
  assumes t: "1 / (1 - F x0) < t"
  shows "0 < f (tail_quantile F t)"
  by (intro fpos t_lt_tail_quantile_of_gt_inv[OF F x0 t]
      F_tail_quantile_lt_1[OF F x0 Flim DERIV_isCont[OF Fderiv] t])

lemma tail_quantile_deriv_has_deriv:
  fixes f' :: "real \<Rightarrow> real" and t :: real
  assumes fderiv: "\<And>x. x0 < x \<Longrightarrow> F x < 1 \<Longrightarrow> (f has_real_derivative f' x) (at x)"
    and t: "1 / (1 - F x0) < t"
  shows "((\<lambda>s. 1 / (s\<^sup>2 * f (tail_quantile F s))) has_real_derivative
           - (2 * t * f (tail_quantile F t)
                + f' (tail_quantile F t) / f (tail_quantile F t))
             / (t\<^sup>2 * f (tail_quantile F t))\<^sup>2) (at t)"
proof -
  define T where "T = 1 / (1 - F x0)"
  define U where "U = tail_quantile F"
  have t_gt: "T < t"
    using t by (simp add: T_def)
  have t1: "1 < t"
    using one_less_of_inverse_tail_less[OF F x0 t] .
  have Ugt: "x0 < U t"
    using t_lt_tail_quantile_of_gt_inv[OF F x0 t] by (simp add: U_def)
  have UFlt: "F (U t) < 1"
    using F_tail_quantile_lt_1[OF F x0 Flim DERIV_isCont[OF Fderiv] t] by (simp add: U_def)
  have nz: "t \<noteq> 0" "f (U t) \<noteq> 0" and nz2: "t\<^sup>2 * f (U t) \<noteq> 0"
    using t1 fpos[OF Ugt UFlt] by auto
  have c1: "((\<lambda>s. f (U s)) has_real_derivative f' (U t) * (1 / (t\<^sup>2 * f (U t)))) (at t)"
    unfolding U_def
    by (rule DERIV_chain2[OF fderiv[OF Ugt UFlt, unfolded U_def]
          tail_quantile_has_deriv[OF t]])
  have c2: "((\<lambda>s. s\<^sup>2 * f (U s)) has_real_derivative
              2 * t * f (U t) + f' (U t) / f (U t)) (at t)"
  proof -
    have "2 * t * f (U t) + t\<^sup>2 * (f' (U t) * (1 / (t\<^sup>2 * f (U t))))
            = 2 * t * f (U t) + f' (U t) / f (U t)"
      using nz by (simp add: field_simps)
    thus ?thesis
      by (auto intro!: derivative_eq_intros c1)
  qed
  have "((\<lambda>s. 1 / (s\<^sup>2 * f (U s))) has_real_derivative
          - (2 * t * f (U t) + f' (U t) / f (U t)) / (t\<^sup>2 * f (U t))\<^sup>2) (at t)"
    using DERIV_divide[OF DERIV_const[of 1] c2 nz2] by (simp add: power2_eq_square)
  thus ?thesis
    by (simp add: U_def)
qed

lemma tail_quantile_second_deriv_eq:
  fixes f' u u' :: "real \<Rightarrow> real" and t :: real
  assumes fderiv: "\<And>x. x0 < x \<Longrightarrow> F x < 1 \<Longrightarrow> (f has_real_derivative f' x) (at x)"
    and uderiv: "\<And>s. 1 / (1 - F x0) < s
                   \<Longrightarrow> (tail_quantile F has_real_derivative u s) (at s)"
    and u'deriv: "\<And>s. 1 / (1 - F x0) < s \<Longrightarrow> (u has_real_derivative u' s) (at s)"
    and t: "1 / (1 - F x0) < t"
  shows "t * u' t / u t
           = - 2 - (1 - F (tail_quantile F t)) * f' (tail_quantile F t)
                     / (f (tail_quantile F t))\<^sup>2"
proof -
  define T where "T = 1 / (1 - F x0)"
  define U where "U = tail_quantile F"
  have t_gt: "T < t"
    using t by (simp add: T_def)
  have s1: "1 < s" if "T < s" for s
    using one_less_of_inverse_tail_less[OF F x0] that by (simp add: T_def)
  have Ugt: "x0 < U s" if "T < s" for s
    using t_lt_tail_quantile_of_gt_inv[OF F x0] that by (simp add: U_def T_def)
  have UF: "1 - F (U s) = 1 / s" if "T < s" for s
    using tail_quantile_tail_eq[OF F x0 Flim DERIV_isCont[OF Fderiv]] that
    by (simp add: U_def T_def)
  have UFlt: "F (U s) < 1" if "T < s" for s
    using F_tail_quantile_lt_1[OF F x0 Flim DERIV_isCont[OF Fderiv]] that
    by (simp add: U_def T_def)
  have fUpos: "0 < f (U s)" if "T < s" for s
    using f_tail_quantile_pos that by (simp add: T_def U_def)
  have u_eq: "u s = 1 / (s\<^sup>2 * f (U s))" if "T < s" for s
    using DERIV_unique[OF uderiv tail_quantile_has_deriv] that
    by (simp add: T_def U_def)
  have hd: "((\<lambda>s. 1 / (s\<^sup>2 * f (U s))) has_real_derivative
      - (2 * t * f (U t) + f' (U t) / f (U t)) / (t\<^sup>2 * f (U t))\<^sup>2) (at t)"
    using tail_quantile_deriv_has_deriv[OF fderiv t]
    by (simp add: U_def)
  have uderiv': "(u has_real_derivative
      - (2 * t * f (U t) + f' (U t) / f (U t)) / (t\<^sup>2 * f (U t))\<^sup>2) (at t)"
    by(intro has_field_derivative_transform_within_open[OF hd, where S = "{T<..}"])
      (auto simp: u_eq t_gt)
  have Uval: "tail_quantile F t = U t"
    by (simp add: U_def)
  have nz': "t \<noteq> 0" "f (U t) \<noteq> 0"
    using s1[OF t_gt] fUpos[OF t_gt] by auto
  show ?thesis
    unfolding Uval DERIV_unique[OF u'deriv[OF t] uderiv'] u_eq[OF t_gt] UF[OF t_gt]
    using nz' by (simp add: field_simps power2_eq_square)
qed

context
  fixes f' :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes fderiv: "\<And>y. x0 < y \<Longrightarrow> F y < 1 \<Longrightarrow> (f has_real_derivative f' y) (at y)"
    and f'cont: "continuous_on {y. x0 < y \<and> F y < 1} f'"
    and lim: "((\<lambda>y. (1 - F y) * f' y / (f y)\<^sup>2) \<longlongrightarrow> - \<gamma> - 1) (endpoint_filter F)"
begin

lemma von_Mises_quantile_diff:
  fixes x :: real
  assumes x: "0 < x"
  shows "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t)
                 * (t * f (tail_quantile F t)))
           \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
proof -
  define T where "T = 1 / (1 - F x0)"
  define U where "U = tail_quantile F"
  define u where "u = (\<lambda>s. 1 / (s\<^sup>2 * f (U s)))"
  define u' where "u' = (\<lambda>s. - (2 * s * f (U s) + f' (U s) / f (U s)) / (s\<^sup>2 * f (U s))\<^sup>2)"
  have Tpos: "0 < T"
    using x0 right_continuous_mono.a_le_f[OF F, of x0] by (simp add: T_def)
  have s1: "1 < s" if "T < s" for s
    using one_less_of_inverse_tail_less[OF F x0] that by (simp add: T_def)
  have Ugt: "x0 < U s" if "T < s" for s
    using t_lt_tail_quantile_of_gt_inv[OF F x0] that by (simp add: U_def T_def)
  have UF: "1 - F (U s) = 1 / s" if "T < s" for s
    using tail_quantile_tail_eq[OF F x0 Flim DERIV_isCont[OF Fderiv]] that
    by (simp add: U_def T_def)
  have UFlt: "F (U s) < 1" if "T < s" for s
    using F_tail_quantile_lt_1[OF F x0 Flim DERIV_isCont[OF Fderiv]] that
    by (simp add: U_def T_def)
  have fUpos: "0 < f (U s)" if "T < s" for s
    using f_tail_quantile_pos that by (simp add: T_def U_def)
  have UderivT: "(tail_quantile F has_real_derivative u s) (at s)"
    if "1 / (1 - F x0) < s" for s
    using tail_quantile_has_deriv[OF that] by (simp add: u_def U_def)
  have uderivT: "(u has_real_derivative u' s) (at s)" if "1 / (1 - F x0) < s" for s
    using tail_quantile_deriv_has_deriv[OF fderiv that]
    by (simp add: u_def u'_def U_def)
  have Uderiv: "(U has_real_derivative u s) (at s)" if "T < s" for s
    using UderivT that by (simp add: T_def U_def)
  have uderiv: "(u has_real_derivative u' s) (at s)" if "T < s" for s
    using uderivT that by (simp add: T_def)
  have upos: "0 < u s" if "T < s" for s
    using s1[OF that] fUpos[OF that] by (simp add: u_def)
  have regopen: "open {y. x0 < y \<and> F y < 1}"
  proof -
    have "{y. x0 < y \<and> F y < 1} = {x0<..} \<inter> {y. F y < 1}"
      by auto
    moreover have "open ({x0<..} \<inter> {y. F y < 1})"
      by (intro open_Int open_greaterThan right_continuous_mono.open_less[OF F])
    ultimately show ?thesis
      by simp
  qed
  have f'isCont: "isCont f' y" if "x0 < y" "F y < 1" for y
    by (rule continuous_on_interior[OF f'cont]) (simp add: interior_open[OF regopen] that)
  have u'cont: "continuous_on {T<..} u'"
  proof (safe intro!: continuous_at_imp_continuous_on)
    fix s
    assume sT: "T < s"
    show "isCont u' s"
      unfolding u'_def using fUpos[OF sT] s1[OF sT]
      by (intro continuous_intros
          isCont_o2[OF DERIV_isCont[OF Uderiv[OF sT]]
            DERIV_isCont[OF fderiv[OF Ugt[OF sT] UFlt[OF sT]]]]
          isCont_o2[OF DERIV_isCont[OF Uderiv[OF sT]]
            f'isCont[OF Ugt[OF sT] UFlt[OF sT]]])
         auto
  qed
  have lim2: "((\<lambda>s. s * u' s / u s) \<longlongrightarrow> \<gamma> - 1) at_top"
  proof -
    have "((\<lambda>s. (1 - F (U s)) * f' (U s) / (f (U s))\<^sup>2) \<longlongrightarrow> - \<gamma> - 1) at_top"
      unfolding U_def
      by (rule filterlim_compose[OF lim tail_quantile_tendsto_endpoint[OF F Flim]])
    from tendsto_diff[OF tendsto_const[of "- 2 :: real"] this]
    have "((\<lambda>s. - 2 - (1 - F (U s)) * f' (U s) / (f (U s))\<^sup>2) \<longlongrightarrow> \<gamma> - 1) at_top"
      by simp
    moreover have "\<forall>\<^sub>F s in at_top.
        - 2 - (1 - F (U s)) * f' (U s) / (f (U s))\<^sup>2 = s * u' s / u s"
      using eventually_gt_at_top[of T]
      by eventually_elim
        (use tail_quantile_second_deriv_eq[OF fderiv UderivT uderivT]
          in "simp add: T_def U_def")
    ultimately show ?thesis
      by (rule Lim_transform_eventually)
  qed
  have "\<forall>\<^sub>F s in at_top. (U (s * x) - U s) / (s * u s)
          = (U (s * x) - U s) * (s * f (U s))"
    using eventually_gt_at_top[of T]
    by eventually_elim (use s1 fUpos in "simp add: u_def field_simps power2_eq_square")
  from Lim_transform_eventually
    [OF deriv_diff_ratio_regularly_varying[OF Tpos Uderiv uderiv u'cont upos lim2 x] this]
  show ?thesis
    by (simp add: U_def)
qed

lemma von_Mises_normalizing_ex:
  shows "\<exists>a. (\<forall>t. 0 < a t)
           \<and> (\<forall>\<^sub>F t in at_top. a t = 1 / (t * f (tail_quantile F t)))
           \<and> (\<forall>x>0. ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
                       \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top)"
proof -
  define T where "T = 1 / (1 - F x0)"
  define a where "a = (\<lambda>t. if T < t then 1 / (t * f (tail_quantile F t)) else 1)"
  have t1: "1 < t" if "T < t" for t
    using one_less_of_inverse_tail_less[OF F x0] that by (simp add: T_def)
  have fU: "0 < f (tail_quantile F t)" if "T < t" for t
    using f_tail_quantile_pos that by (simp add: T_def)
  have apos: "0 < a t" for t
    by (cases "T < t") (use t1[of t] fU[of t] in "auto simp: a_def")
  have aev: "\<forall>\<^sub>F t in at_top. a t = 1 / (t * f (tail_quantile F t))"
    using eventually_gt_at_top[of T] by eventually_elim (simp add: a_def)
  have "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
          \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top" if x: "0 < x" for x
  proof -
    have "\<forall>\<^sub>F t in at_top. (tail_quantile F (t * x) - tail_quantile F t)
             * (t * f (tail_quantile F t))
           = (tail_quantile F (t * x) - tail_quantile F t) / a t"
      using eventually_gt_at_top[of T]
      by eventually_elim (use t1 fU in "simp add: a_def")
    from Lim_transform_eventually[OF von_Mises_quantile_diff[OF x] this]
    show ?thesis .
  qed
  thus ?thesis
    using apos aev by blast
qed

text \<open>von Mises' condition (Theorem~1.1.8 of the book by de Haan and
      Ferreira~\<^cite>\<open>deHaanFerreira\<close>).\<close>

theorem von_Mises_condition: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  unfolding MDA_iff_tail_quantile'[OF F]
  using von_Mises_normalizing_ex by blast

corollary von_Mises_normalization:
  fixes x :: real
  shows "(\<lambda>n. F (x / (real n * f (tail_quantile F (real n)))
                  + tail_quantile F (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 x"
proof -
  obtain a where apos: "\<And>t. 0 < a t"
    and aev: "\<forall>\<^sub>F t in at_top. a t = 1 / (t * f (tail_quantile F t))"
    and quant: "\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
                   \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
    using von_Mises_normalizing_ex by blast
  have "(\<lambda>n. F (a (real n) * x + tail_quantile F (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 x"
  proof (rule MDA_tail_quantile_witness[OF F apos zero_less_one])
    fix y :: real
    assume y: "0 < y"
    show "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
            \<longlongrightarrow> (if \<gamma> = 0 then 1 * ln y + 0 else 1 * (y powr \<gamma> - 1) / \<gamma> + 0)) at_top"
      by (cases "\<gamma> = 0") (use quant[OF y] in simp_all)
  qed
  moreover have "\<forall>\<^sub>F n in sequentially. F (a (real n) * x + tail_quantile F (real n)) ^ n
      = F (x / (real n * f (tail_quantile F (real n))) + tail_quantile F (real n)) ^ n"
    using eventually_compose_filterlim[OF aev filterlim_real_sequentially]
    by eventually_elim simp
  ultimately show ?thesis
    by (rule Lim_transform_eventually)
qed

end

end

text \<open>Relation~(1.1.35) of the book by de Haan and Ferreira~\<^cite>\<open>deHaanFerreira\<close>.\<close>
lemma tail_quantile_deriv_ratio_pos:
  fixes F f u :: "real \<Rightarrow> real" and \<gamma> x0 t0 :: real
  assumes F: "right_continuous_mono F 0 1"
    and unbdd: "\<not> bdd_support F"
    and gamma: "0 < \<gamma>"
    and Fderiv: "\<And>x. x0 < x \<Longrightarrow> (F has_real_derivative f x) (at x)"
    and fpos: "\<And>x. x0 < x \<Longrightarrow> 0 < f x"
    and uderiv: "\<And>t. t0 < t \<Longrightarrow> (tail_quantile F has_real_derivative u t) (at t)"
    and lim: "((\<lambda>t. t * f t / (1 - F t)) \<longlongrightarrow> 1 / \<gamma>) at_top"
  shows "((\<lambda>t. t * u t / tail_quantile F t) \<longlongrightarrow> \<gamma>) at_top"
proof -
  have x0lt: "F x0 < 1"
    by (rule F_lt_1_unbdd_support[OF F unbdd])
  have Flim: "(F \<longlongrightarrow> 1) (endpoint_filter F)"
    using right_continuous_mono.top[OF F] unbdd by (simp add: endpoint_filter)
  have Fderiv': "(F has_real_derivative f y) (at y)" if y: "x0 < y" and "F y < 1" for y
    by (rule Fderiv[OF y])
  have fpos': "0 < f y" if y: "x0 < y" and "F y < 1" for y
    by (rule fpos[OF y])
  define T where "T = max t0 (1 / (1 - F x0))"
  have t1: "1 < t" if "T < t" for t
    using one_less_of_inverse_tail_less[OF F x0lt] that by (simp add: T_def)
  have fU: "0 < f (tail_quantile F t)" if "T < t" for t
    using f_tail_quantile_pos[OF F x0lt Flim Fderiv' fpos'] that by (simp add: T_def)
  have UF: "1 - F (tail_quantile F t) = 1 / t" if "T < t" for t
    using tail_quantile_tail_eq[OF F x0lt Flim DERIV_isCont[OF Fderiv']] that
    by (simp add: T_def)
  have u_eq: "u t = 1 / (t\<^sup>2 * f (tail_quantile F t))" if "T < t" for t
    using DERIV_unique[OF uderiv tail_quantile_has_deriv[OF F x0lt Flim Fderiv' fpos']] that
    by (simp add: T_def)
  note Uat = tail_quantile_at_top[OF F F_lt_1_unbdd_support[OF F unbdd]]
  have "((\<lambda>s. (1 - F s) / (s * f s)) \<longlongrightarrow> \<gamma>) at_top"
    using tendsto_inverse[OF lim] gamma by simp
  from filterlim_compose[OF this Uat]
  have comp: "((\<lambda>t. (1 - F (tail_quantile F t))
                     / (tail_quantile F t * f (tail_quantile F t))) \<longlongrightarrow> \<gamma>) at_top" .
  have evU: "\<forall>\<^sub>F t in at_top. 1 \<le> tail_quantile F t"
    using Uat unfolding filterlim_at_top by blast
  have "\<forall>\<^sub>F t in at_top. (1 - F (tail_quantile F t))
          / (tail_quantile F t * f (tail_quantile F t)) = t * u t / tail_quantile F t"
    using eventually_gt_at_top[of T] evU
  proof eventually_elim
    fix t :: real
    assume tT: "T < t"
      and U1: "1 \<le> tail_quantile F t"
    show "(1 - F (tail_quantile F t)) / (tail_quantile F t * f (tail_quantile F t))
            = t * u t / tail_quantile F t"
      unfolding UF[OF tT] u_eq[OF tT]
      using t1[OF tT] fU[OF tT] U1 by (simp add: field_simps power2_eq_square)
  qed
  from Lim_transform_eventually[OF comp this]
  show ?thesis .
qed

text \<open>von Mises' condition for positive $\gamma$ (Theorem~1.1.11 of the book by
      de Haan and Ferreira~\<^cite>\<open>deHaanFerreira\<close>).\<close>

theorem von_Mises_condition_pos:
  fixes F f :: "real \<Rightarrow> real" and \<gamma> x0 :: real
  assumes F: "right_continuous_mono F 0 1"
    and unbdd: "\<not> bdd_support F"
    and gamma: "0 < \<gamma>"
    and Fderiv: "\<And>x. x0 < x \<Longrightarrow> (F has_real_derivative f x) (at x)"
    and fcont: "continuous_on {x0<..} f"
    and fpos: "\<And>x. x0 < x \<Longrightarrow> 0 < f x"
    and lim: "((\<lambda>t. t * f t / (1 - F t)) \<longlongrightarrow> 1 / \<gamma>) at_top"
  shows "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
proof -
  have x0lt: "F x0 < 1"
    by (rule F_lt_1_unbdd_support[OF F unbdd])
  have Flim: "(F \<longlongrightarrow> 1) (endpoint_filter F)"
    using right_continuous_mono.top[OF F] unbdd by (simp add: endpoint_filter)
  have Fderiv': "(F has_real_derivative f y) (at y)" if y: "x0 < y" and "F y < 1" for y
    by (rule Fderiv[OF y])
  have fpos': "0 < f y" if y: "x0 < y" and "F y < 1" for y
    by (rule fpos[OF y])
  have fcont': "isCont f y" if "x0 < y" for y
    by (rule continuous_on_interior[OF fcont]) (simp add: interior_open that)
  obtain T1 where T1: "\<And>t. T1 \<le> t \<Longrightarrow> 1 \<le> tail_quantile F t"
    using tail_quantile_at_top[OF F F_lt_1_unbdd_support[OF F unbdd]]
    unfolding filterlim_at_top eventually_at_top_linorder by blast
  define T where "T = max (1 / (1 - F x0)) (max T1 1)"
  define u where "u = (\<lambda>s. 1 / (s\<^sup>2 * f (tail_quantile F s)))"
  have Tpos: "0 < T"
    by (simp add: T_def)
  have t1: "1 < t" if "T < t" for t
    using one_less_of_inverse_tail_less[OF F x0lt] that by (simp add: T_def)
  have Upos: "0 < tail_quantile F t" if "T < t" for t
    using T1[of t] that by (simp add: T_def)
  have fU: "0 < f (tail_quantile F t)" if "T < t" for t
    using f_tail_quantile_pos[OF F x0lt Flim Fderiv' fpos'] that by (simp add: T_def)
  have Uderiv: "(tail_quantile F has_real_derivative u t) (at t)" if "T < t" for t
    using tail_quantile_has_deriv[OF F x0lt Flim Fderiv' fpos'] that by (simp add: u_def T_def)
  have ucont: "continuous_on {T<..} u"
  proof (safe intro!: continuous_at_imp_continuous_on)
    fix s
    assume sT: "T < s"
    show "isCont u s"
      unfolding u_def using fU[OF sT] t1[OF sT]
      by (intro continuous_intros
          isCont_o2[OF DERIV_isCont[OF Uderiv[OF sT]]
            fcont'[OF t_lt_tail_quantile_of_gt_inv[OF F x0lt, of s]]])
         (use sT in "auto simp: T_def")
  qed
  note lim2 = tail_quantile_deriv_ratio_pos[OF F unbdd gamma Fderiv fpos Uderiv lim]
  define a where "a = (\<lambda>t. if T < t then \<gamma> * tail_quantile F t else 1)"
  have apos: "0 < a t" for t
    by (cases "T < t") (use gamma Upos in "simp_all add: a_def")
  have "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
          \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top" if x: "0 < x" for x
  proof -
    have "((\<lambda>t. (tail_quantile F (t * x) / tail_quantile F t - 1) / \<gamma>)
            \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
      by (intro tendsto_divide tendsto_diff
          deriv_ratio_regularly_varying[OF Tpos Uderiv ucont Upos lim2 x] tendsto_const)
         (use gamma in simp_all)
    moreover have "\<forall>\<^sub>F t in at_top. (tail_quantile F (t * x) / tail_quantile F t - 1) / \<gamma>
            = (tail_quantile F (t * x) - tail_quantile F t) / a t"
      using eventually_gt_at_top[of T]
    proof eventually_elim
      case (elim t)
      show ?case
        using Upos[OF elim] gamma elim by (simp add: a_def field_simps)
    qed
    ultimately have "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
            \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
      by (rule Lim_transform_eventually)
    thus ?thesis
      using gamma by simp
  qed
  thus ?thesis
    unfolding MDA_iff_tail_quantile'[OF F] using apos by blast
qed

lemma F_tendsto_1_endpoint_of_deriv:
  fixes F f :: "real \<Rightarrow> real" and x0 c :: real
  assumes F: "right_continuous_mono F 0 1"
    and bdd: "bdd_support F"
    and x0: "x0 < x_star F"
    and Fderiv: "\<And>y. x0 < y \<Longrightarrow> y < x_star F \<Longrightarrow> (F has_real_derivative f y) (at y)"
    and cpos: "0 < c"
    and lim: "((\<lambda>y. (x_star F - y) * f y / (1 - F y)) \<longlongrightarrow> c) (at_left (x_star F))"
  shows "(F \<longlongrightarrow> 1) (endpoint_filter F)"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  define X where "X = x_star F"
  define G where "G = Sup (F ` {..<X})"
  have ne: "F ` {..<X} \<noteq> {}"
    by auto
  have leG: "F y \<le> G" if "y < X" for y
    unfolding G_def using that by (auto intro!: cSup_upper bdd_aboveI2[of _ _ 1] f_le_b)
  have G1: "G = 1"
  proof (rule ccontr)
    assume "G \<noteq> 1"
    moreover have "G \<le> 1"
      unfolding G_def by (auto intro!: cSup_least ne f_le_b)
    ultimately have Glt: "G < 1"
      by simp
    define e where "e = 1 - G"
    have epos: "0 < e"
      using Glt by (simp add: e_def)
    have tail_ge: "e \<le> 1 - F y" if "y < X" for y
      using leG[OF that] by (simp add: e_def)
    obtain b0 where b0X: "b0 < X"
      and b0: "\<And>y. b0 < y \<Longrightarrow> y < X \<Longrightarrow> c / 2 < (X - y) * f y / (1 - F y)"
      using order_tendstoD(1)[OF lim, of "c / 2"] cpos
      unfolding X_def eventually_at_left_field by auto
    define B where "B = max b0 x0"
    have BX: "B < X"
      using b0X x0 by (simp add: B_def X_def)
    have fbound: "c * e / 2 / (X - y) < f y" if yB: "B < y" and yX: "y < X" for y
    proof -
      have pos: "0 < 1 - F y"
        using tail_ge[OF yX] epos by simp
      have "c / 2 * e \<le> c / 2 * (1 - F y)"
        using tail_ge[OF yX] cpos by simp
      also have "\<dots> < (X - y) * f y"
        using b0[of y] yB yX pos by (simp add: B_def pos_less_divide_eq)
      finally show ?thesis
        using yX by (simp add: pos_divide_less_eq algebra_simps)
    qed
    obtain s where sX: "s < X" and Fs: "G - c * e / 4 < F s"
      using less_cSupD[OF ne, of "G - c * e / 4"] cpos epos by (auto simp: G_def)
    define p where "p = max s ((B + X) / 2)"
    have pX: "p < X" and Bp: "B < p" and sp: "s \<le> p"
      using sX BX by (auto simp: p_def less_max_iff_disj)
    have Fp: "G - c * e / 4 < F p"
      using Fs monoD[OF mono, of s p] sp by simp
    define q where "q = (p + X) / 2"
    have pq: "p < q" and qX: "q < X"
      using pX by (simp_all add: q_def)
    have deriv: "(F has_real_derivative f y) (at y)" if "p \<le> y" "y \<le> q" for y
      using that Bp qX x0 by (auto intro!: Fderiv simp: B_def X_def)
    obtain z where z: "p < z" "z < q" and Fz: "F q - F p = (q - p) * f z"
      using MVT2[OF pq deriv] by blast
    have "c * e / 4 < (q - p) * f z"
    proof -
      have "c * e / 2 / (X - p) \<le> c * e / 2 / (X - z)"
        using z pX qX cpos epos by (intro divide_left_mono) auto
      also have "\<dots> < f z"
        using fbound[of z] Bp z qX by simp
      finally show ?thesis
        using pX by (simp add: q_def field_simps)
    qed
    thus False
      using Fz Fp leG[OF qX] by simp
  qed
  show ?thesis
    unfolding endpoint_filter(1)[OF bdd] X_def[symmetric]
  proof (rule order_tendstoI)
    fix a :: real
    assume "a < 1"
    then obtain s where sX: "s < X" and Fs: "a < F s"
      using less_cSupD[OF ne, of a] by (auto simp: G_def G1[symmetric])
    show "\<forall>\<^sub>F y in at_left X. a < F y"
    proof (intro eventually_at_leftI[OF _ sX])
      fix y
      assume "y \<in> {s<..<X}"
      thus "a < F y"
        using Fs monoD[OF mono, of s y] by simp
    qed
  qed (auto intro!: always_eventually order.strict_trans1[OF f_le_b])
qed

text \<open>Relation~(1.1.38) of the book by de Haan and Ferreira~\<^cite>\<open>deHaanFerreira\<close>.\<close>

lemma tail_quantile_deriv_ratio_neg:
  fixes F f u :: "real \<Rightarrow> real" and \<gamma> x0 t0 :: real
  assumes F: "right_continuous_mono F 0 1"
    and bdd: "bdd_support F"
    and gamma: "\<gamma> < 0"
    and x0: "x0 < x_star F"
    and Fderiv: "\<And>x. x0 < x \<Longrightarrow> x < x_star F \<Longrightarrow> (F has_real_derivative f x) (at x)"
    and fpos: "\<And>x. x0 < x \<Longrightarrow> x < x_star F \<Longrightarrow> 0 < f x"
    and uderiv: "\<And>t. t0 < t \<Longrightarrow> (tail_quantile F has_real_derivative u t) (at t)"
    and lim: "((\<lambda>t. (x_star F - t) * f t / (1 - F t)) \<longlongrightarrow> - 1 / \<gamma>) (at_left (x_star F))"
  shows "((\<lambda>t. t * u t / (x_star F - tail_quantile F t)) \<longlongrightarrow> - \<gamma>) at_top"
proof -
  have Flim: "(F \<longlongrightarrow> 1) (endpoint_filter F)"
    by (intro F_tendsto_1_endpoint_of_deriv[OF F bdd x0 Fderiv _ lim])
       (use gamma in "auto simp: divide_neg_neg")
  have iff: "y < x_star F \<longleftrightarrow> F y < 1" for y
    by (rule lt_x_star_iff_F_lt_1[OF F bdd])
  have x0lt: "F x0 < 1"
    using x0 iff by simp
  have Fderiv': "(F has_real_derivative f y) (at y)" if "x0 < y" "F y < 1" for y
    using that iff by (auto intro!: Fderiv)
  have fpos': "0 < f y" if "x0 < y" "F y < 1" for y
    using that iff by (auto intro!: fpos)
  define T where "T = max t0 (1 / (1 - F x0))"
  have t1: "1 < t" if "T < t" for t
    using one_less_of_inverse_tail_less[OF F x0lt] that by (simp add: T_def)
  have fU: "0 < f (tail_quantile F t)" if "T < t" for t
    using f_tail_quantile_pos[OF F x0lt Flim Fderiv' fpos'] that by (simp add: T_def)
  have UF: "1 - F (tail_quantile F t) = 1 / t" if "T < t" for t
    using tail_quantile_tail_eq[OF F x0lt Flim DERIV_isCont[OF Fderiv']] that
    by (simp add: T_def)
  have u_eq: "u t = 1 / (t\<^sup>2 * f (tail_quantile F t))" if "T < t" for t
    using DERIV_unique[OF uderiv tail_quantile_has_deriv[OF F x0lt Flim Fderiv' fpos']] that
    by (simp add: T_def)
  have Uend: "filterlim (tail_quantile F) (at_left (x_star F)) at_top"
    using tail_quantile_tendsto_endpoint[OF F Flim] by (simp add: endpoint_filter bdd)
  have "((\<lambda>s. (1 - F s) / ((x_star F - s) * f s)) \<longlongrightarrow> - \<gamma>) (at_left (x_star F))"
    using tendsto_inverse[OF lim] gamma by simp
  from filterlim_compose[OF this Uend]
  have comp: "((\<lambda>t. (1 - F (tail_quantile F t))
                     / ((x_star F - tail_quantile F t) * f (tail_quantile F t)))
                \<longlongrightarrow> - \<gamma>) at_top" .
  have evU: "\<forall>\<^sub>F t in at_top. tail_quantile F t < x_star F"
    using eventually_gt_at_top[of "1 :: real"]
    by eventually_elim (rule tail_quantile_lt_x_star[OF F bdd Flim])
  have "\<forall>\<^sub>F t in at_top. (1 - F (tail_quantile F t))
          / ((x_star F - tail_quantile F t) * f (tail_quantile F t))
        = t * u t / (x_star F - tail_quantile F t)"
    using eventually_gt_at_top[of T] evU
  proof eventually_elim
    fix t :: real
    assume tT: "T < t"
      and Ult: "tail_quantile F t < x_star F"
    show "(1 - F (tail_quantile F t))
            / ((x_star F - tail_quantile F t) * f (tail_quantile F t))
          = t * u t / (x_star F - tail_quantile F t)"
      unfolding UF[OF tT] u_eq[OF tT]
      using t1[OF tT] fU[OF tT] Ult by (simp add: field_simps power2_eq_square)
  qed
  from Lim_transform_eventually[OF comp this]
  show ?thesis .
qed

text \<open>von Mises' condition for negative $\gamma$ (Theorem~1.1.13 of the book by
      de Haan and Ferreira~\<^cite>\<open>deHaanFerreira\<close>).\<close>

theorem von_Mises_condition_neg:
  fixes F f :: "real \<Rightarrow> real" and \<gamma> x0 :: real
  assumes F: "right_continuous_mono F 0 1"
    and bdd: "bdd_support F"
    and gamma: "\<gamma> < 0"
    and x0: "x0 < x_star F"
    and Fderiv: "\<And>x. x0 < x \<Longrightarrow> x < x_star F \<Longrightarrow> (F has_real_derivative f x) (at x)"
    and fcont: "continuous_on {x0<..<x_star F} f"
    and fpos: "\<And>x. x0 < x \<Longrightarrow> x < x_star F \<Longrightarrow> 0 < f x"
    and lim: "((\<lambda>t. (x_star F - t) * f t / (1 - F t)) \<longlongrightarrow> - 1 / \<gamma>) (at_left (x_star F))"
  shows "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
proof -
  have Flim: "(F \<longlongrightarrow> 1) (endpoint_filter F)"
    by (intro F_tendsto_1_endpoint_of_deriv[OF F bdd x0 Fderiv _ lim])
       (use gamma in "auto simp: divide_neg_neg")
  have iff: "y < x_star F \<longleftrightarrow> F y < 1" for y
    by (rule lt_x_star_iff_F_lt_1[OF F bdd])
  have x0lt: "F x0 < 1"
    using x0 iff by simp
  have Fderiv': "(F has_real_derivative f y) (at y)" if "x0 < y" "F y < 1" for y
    using that iff by (auto intro!: Fderiv)
  have fpos': "0 < f y" if "x0 < y" "F y < 1" for y
    using that iff by (auto intro!: fpos)
  have fcont': "isCont f y" if "x0 < y" "y < x_star F" for y
    by (rule continuous_on_interior[OF fcont]) (simp add: interior_open that)
  define T where "T = max (1 / (1 - F x0)) 1"
  define u where "u = (\<lambda>s. 1 / (s\<^sup>2 * f (tail_quantile F s)))"
  have Tpos: "0 < T"
    by (simp add: T_def)
  have t1: "1 < t" if "T < t" for t
    using one_less_of_inverse_tail_less[OF F x0lt] that by (simp add: T_def)
  have Ult: "tail_quantile F t < x_star F" if "T < t" for t
    by (rule tail_quantile_lt_x_star[OF F bdd Flim t1[OF that]])
  have Ugt: "x0 < tail_quantile F t" if "T < t" for t
    using t_lt_tail_quantile_of_gt_inv[OF F x0lt] that by (simp add: T_def)
  have fU: "0 < f (tail_quantile F t)" if "T < t" for t
    by (rule fpos[OF Ugt[OF that] Ult[OF that]])
  have Uderiv: "(tail_quantile F has_real_derivative u t) (at t)" if "T < t" for t
    using tail_quantile_has_deriv[OF F x0lt Flim Fderiv' fpos'] that by (simp add: u_def T_def)
  have ucont: "continuous_on {T<..} u"
  proof (safe intro!: continuous_at_imp_continuous_on)
    fix s
    assume sT: "T < s"
    show "isCont u s"
      unfolding u_def using fU[OF sT] t1[OF sT]
      by (intro continuous_intros
          isCont_o2[OF DERIV_isCont[OF Uderiv[OF sT]] fcont'[OF Ugt[OF sT] Ult[OF sT]]])
         auto
  qed
  note lim2 = tail_quantile_deriv_ratio_neg[OF F bdd gamma x0 Fderiv fpos Uderiv lim]
  define a where "a = (\<lambda>t. if T < t then - \<gamma> * (x_star F - tail_quantile F t) else 1)"
  have apos: "0 < a t" for t
    by (cases "T < t") (use gamma Ult in "simp_all add: a_def mult_neg_pos")
  have "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
          \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top" if x: "0 < x" for x
  proof -
    have "((\<lambda>t. (1 - (x_star F - tail_quantile F (t * x))
                      / (x_star F - tail_quantile F t)) / (- \<gamma>))
            \<longlongrightarrow> (1 - x powr \<gamma>) / (- \<gamma>)) at_top"
      by (intro tendsto_divide tendsto_diff
          deriv_ratio_regularly_varying_uminus[OF Tpos Uderiv ucont Ult lim2 x] tendsto_const)
         (use gamma in simp_all)
    moreover have "\<forall>\<^sub>F t in at_top. (1 - (x_star F - tail_quantile F (t * x))
                      / (x_star F - tail_quantile F t)) / (- \<gamma>)
            = (tail_quantile F (t * x) - tail_quantile F t) / a t"
      using eventually_gt_at_top[of T]
    proof eventually_elim
      case (elim t)
      show ?case
        using Ult[OF elim] gamma elim by (simp add: a_def field_simps)
    qed
    ultimately have "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
            \<longlongrightarrow> (1 - x powr \<gamma>) / (- \<gamma>)) at_top"
      by (rule Lim_transform_eventually)
    thus ?thesis
      using gamma by (simp add: minus_divide_left field_simps)
  qed
  thus ?thesis
    unfolding MDA_iff_tail_quantile'[OF F] using apos by blast
qed

subsection \<open>Relation to Regularly Varying Functions\<close>
text \<open>We formalize results for $\gamma \neq 0$.\<close>
lemma tail_quantile_S_at_top:
  fixes F :: "real \<Rightarrow> real" and \<rho> :: real
  assumes F: "right_continuous_mono F 0 1"
    and bdd: "bdd_support F"
    and rv: "regularly_varying (\<lambda>s. 1 - F (x_star F - 1 / s)) \<rho>"
    and rho: "\<rho> < 0"
  shows "filterlim (\<lambda>t. 1 / (x_star F - tail_quantile F t)) at_top at_top"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  have phi_to_0: "((\<lambda>s. 1 - F (x_star F - 1 / s)) \<longlongrightarrow> 0) at_top"
    using regularly_varying_neg_at_top[OF rv rho] .
  have Ult: "tail_quantile F t < x_star F"
    if t1[arith]: "1 < t" for t
  proof -
    have ev: "\<forall>\<^sub>F s in at_top. 1 - F (x_star F - 1 / s) < 1 / t \<and> 0 < s"
      using eventually_conj[OF order_tendstoD(2)[OF phi_to_0, of "1 / t"]
              eventually_gt_at_top[of "0::real"]]
      by simp
    then obtain s0 where s0: "1 - F (x_star F - 1 / s0) < 1 / t" "0 < s0"
      using eventually_happens'[OF trivial_limit_at_top_linorder] by blast
    define z where "z = x_star F - 1 / s0"
    have Fz: "1 - 1 / t < F z"
      using s0 by (simp add: z_def)
    have p_bounds: "0 < 1 - 1 / t" "1 - 1 / t < 1"
      using t1 by simp_all
    have "tail_quantile F t \<le> z"
      using ginv_le_iff[OF p_bounds, of z] Fz by simp
    also have "z < x_star F"
      using s0(2) by (simp add: z_def)
    finally show ?thesis .
  qed
  have main: "\<And>M. 0 < M \<Longrightarrow> \<forall>\<^sub>F t in at_top. M \<le> 1 / (x_star F - tail_quantile F t)"
  proof -
    fix M :: real
    assume Mpos: "0 < M"
    define z0 where "z0 = x_star F - 1 / M"
    have z0lt1: "F z0 < 1"
      using regularly_varying_pos[OF rv, of M] Mpos by (simp add: z0_def)
    show "\<forall>\<^sub>F t in at_top. M \<le> 1 / (x_star F - tail_quantile F t)"
      using eventually_gt_at_top[of "1 / (1 - F z0)"] eventually_gt_at_top[of "1::real"]
    proof eventually_elim
      case (elim t)
      hence t1: "1 < t" and t2: "1 / (1 - F z0) < t"
        by auto
      have p_bounds: "0 < 1 - 1 / t" "1 - 1 / t < 1"
        using t1 by simp_all
      have "F z0 < 1 - 1 / t"
        using t1 t2 z0lt1 by (simp add: field_simps)
      hence zlt: "z0 < tail_quantile F t"
        using ginv_le_iff[OF p_bounds, of z0] by linarith
      have lt: "x_star F - tail_quantile F t < 1 / M"
        using zlt by (simp add: z0_def)
      show ?case
        using Ult[OF t1] lt Mpos by (simp add: field_simps)
    qed
  qed
  show ?thesis
    unfolding filterlim_at_top
  proof
    fix M :: real
    show "\<forall>\<^sub>F t in at_top. M \<le> 1 / (x_star F - tail_quantile F t)"
      using main[of "max M 1"] eventually_mono
      by(cases "M \<le> 1") fastforce+
  qed
qed

lemma tail_quantile_diff_scale_ratio:
  fixes U a :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes apos: "\<And>t. 0 < a t"
    and gamma: "\<gamma> \<noteq> 0"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (U (t * x) - U t) / a t) \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
    and y: "0 < y"
  shows "((\<lambda>t. a (t * y) / a t) \<longlongrightarrow> y powr \<gamma>) at_top"
proof -
  define D where "D = (\<lambda>x::real. (x powr \<gamma> - 1) / \<gamma>)"
  have quant': "\<And>x. 0 < x \<Longrightarrow> ((\<lambda>t. (U (t * x) - U t) / a t) \<longlongrightarrow> D x) at_top"
    using quant by (simp add: D_def)
  have D2_ne: "D 2 \<noteq> 0"
    using gamma by(simp add: D_def)
  have R2y: "((\<lambda>t. (U (t * (y * 2)) - U t) / a t) \<longlongrightarrow> D (y * 2)) at_top"
    using quant'[of "y * 2"] y by simp
  have Ry: "((\<lambda>t. (U (t * y) - U t) / a t) \<longlongrightarrow> D y) at_top"
    using quant'[of y] y by simp
  have Rty2: "((\<lambda>t. (U (t * y * 2) - U (t * y)) / a (t * y)) \<longlongrightarrow> D 2) at_top"
    using filterlim_compose[OF quant'[of 2]
        filterlim_tendsto_pos_mult_at_top[OF tendsto_const y filterlim_ident]]
    by (simp add: mult.commute)
  have eq1: "(U (t * (y * 2)) - U t) / a t - (U (t * y) - U t) / a t
              = (U (t * y * 2) - U (t * y)) / a t" for t
    by (simp add: mult.assoc diff_divide_distrib)
  have main: "((\<lambda>t. (U (t * y * 2) - U (t * y)) / a t) \<longlongrightarrow> D (y * 2) - D y) at_top"
    using tendsto_diff[OF R2y Ry] unfolding eq1 .
  note ev_ne = tendsto_imp_eventually_ne[OF Rty2 D2_ne]
  have ratio_eq: "\<forall>\<^sub>F t in at_top.
       ((U (t * y * 2) - U (t * y)) / a t) / ((U (t * y * 2) - U (t * y)) / a (t * y))
       = a (t * y) / a t"
    using apos by(auto intro!: eventually_mono[OF ev_ne])
  have ratio_tendsto: "((\<lambda>t.
       ((U (t * y * 2) - U (t * y)) / a t) / ((U (t * y * 2) - U (t * y)) / a (t * y)))
       \<longlongrightarrow> (D (y * 2) - D y) / D 2) at_top"
    by (intro tendsto_divide main Rty2 D2_ne)
  have final: "((\<lambda>t. a (t * y) / a t) \<longlongrightarrow> (D (y * 2) - D y) / D 2) at_top"
    using Lim_transform_eventually[OF ratio_tendsto ratio_eq] .
  have value_eq: "(D (y * 2) - D y) / D 2 = y powr \<gamma>"
    using gamma y D2_ne by (simp add: D_def powr_mult field_simps)
  show "((\<lambda>t. a (t * y) / a t) \<longlongrightarrow> y powr \<gamma>) at_top"
    using final value_eq by simp
qed

lemma tail_quantile_cont_ratio:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real and a :: "real \<Rightarrow> real"
  assumes apos: "\<And>t. 0 < a t"
    and gamma: "\<gamma> \<noteq> 0"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
          \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
    and Z: "1 < Z"
  shows "((\<lambda>t. (tail_quantile F (t * Z * Z) - tail_quantile F (t * Z))
                 / (tail_quantile F (t * Z) - tail_quantile F t)) \<longlongrightarrow> Z powr \<gamma>) at_top"
proof -
  define D where "D = (\<lambda>x::real. (x powr \<gamma> - 1) / \<gamma>)"
  have Zpos: "0 < Z"
    using Z by simp
  have quant': "\<And>x. 0 < x \<Longrightarrow>
      ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t) \<longlongrightarrow> D x) at_top"
    using quant by (simp add: D_def)
  from tail_quantile_diff_scale_ratio[OF apos gamma quant]
  have a_rv: "\<And>y. 0 < y \<Longrightarrow> ((\<lambda>t. a (t * y) / a t) \<longlongrightarrow> y powr \<gamma>) at_top" .
  have DZ_ne: "D Z \<noteq> 0"
    using gamma Z by(auto simp: D_def)
  have f_lim: "((\<lambda>t. (tail_quantile F (t * Z) - tail_quantile F t) / a t) \<longlongrightarrow> D Z) at_top"
    using quant'[of Z] Z by simp
  have g_lim: "((\<lambda>t. a (t * Z) / a t) \<longlongrightarrow> Z powr \<gamma>) at_top"
    using a_rv[of Z] Z by simp
  have h_lim: "((\<lambda>t. (tail_quantile F (t * Z * Z)
                     - tail_quantile F (t * Z)) / a (t * Z)) \<longlongrightarrow> D Z) at_top"
    using filterlim_compose[OF f_lim filterlim_tendsto_pos_mult_at_top
        [OF tendsto_const Zpos filterlim_ident]]
    by(simp add: mult.commute)
  have ev_ne: "\<forall>\<^sub>F t in at_top. (tail_quantile F (t * Z) - tail_quantile F t) / a t \<noteq> 0"
    by (intro tendsto_imp_eventually_ne[where c="D Z"] f_lim DZ_ne)
  have ratio_eq: "\<forall>\<^sub>F t in at_top. (a (t * Z) / a t) *
               (((tail_quantile F (t * Z * Z) - tail_quantile F (t * Z)) / a (t * Z))
                 / ((tail_quantile F (t * Z) - tail_quantile F t) / a t))
             = (tail_quantile F (t * Z * Z) - tail_quantile F (t * Z))
                 / (tail_quantile F (t * Z) - tail_quantile F t)"
    using apos by(intro eventually_mono[OF ev_ne])
     (smt (verit) Groups.mult_ac(3) divide_divide_eq_left field_class.field_divide_inverse
       nonzero_mult_divide_mult_cancel_left2
        times_divide_eq_right zero_less_divide_iff)
  have ratio_tendsto: "((\<lambda>t.
      (a (t * Z) / a t) *
        (((tail_quantile F (t * Z * Z) - tail_quantile F (t * Z)) / a (t * Z))
          / ((tail_quantile F (t * Z) - tail_quantile F t) / a t))) \<longlongrightarrow> Z powr \<gamma>) at_top"
    using tendsto_mult[OF g_lim] tendsto_divide[OF h_lim f_lim DZ_ne] DZ_ne
    by fastforce
  show ?thesis
    using Lim_transform_eventually[OF ratio_tendsto ratio_eq] .
qed

lemma tail_quantile_diff_geometric_seq:
  fixes F :: "real \<Rightarrow> real" and \<gamma> Z t0 :: real and a :: "real \<Rightarrow> real"
  assumes apos: "\<And>t. 0 < a t"
    and gamma: "\<gamma> \<noteq> 0"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
          \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
    and Z: "1 < Z" and t0: "0 < t0"
  obtains N where
    "\<And>k. tail_quantile F (t0 * Z ^ (N + k)) < tail_quantile F (t0 * Z ^ Suc (N + k))"
    and "(\<lambda>k. (tail_quantile F (t0 * Z ^ Suc (N + Suc k))
                 - tail_quantile F (t0 * Z ^ (N + Suc k)))
               / (tail_quantile F (t0 * Z ^ Suc (N + k)) - tail_quantile F (t0 * Z ^ (N + k))))
           \<longlonglongrightarrow> Z powr \<gamma>"
proof -
  define D where "D = (\<lambda>x::real. (x powr \<gamma> - 1) / \<gamma>)"
  have DZ_pos: "0 < D Z"
  proof (cases "0 < \<gamma>")
    case True
    show ?thesis
      using powr_less_mono2[OF True zero_le_one Z] True by (simp add: D_def)
  next
    case False
    hence neg: "\<gamma> < 0"
      using gamma by simp
    show ?thesis
      using powr_less_mono[OF neg, of Z] Z neg by (simp add: D_def divide_neg_neg)
  qed
  have seq_top: "filterlim (\<lambda>n. t0 * Z ^ n) at_top sequentially"
    using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of t0] t0
        LIMSEQ_power_at_top[OF Z]] .
  have f_lim: "((\<lambda>t. (tail_quantile F (t * Z) - tail_quantile F t) / a t) \<longlongrightarrow> D Z) at_top"
    using quant[of Z] Z by (simp add: D_def)
  define \<Delta> where "\<Delta> = (\<lambda>n. tail_quantile F (t0 * Z ^ Suc n) - tail_quantile F (t0 * Z ^ n))"
  have \<Delta>_ratio: "(\<lambda>n. \<Delta> (Suc n) / \<Delta> n) \<longlonglongrightarrow> Z powr \<gamma>"
    using filterlim_compose[OF tail_quantile_cont_ratio[OF apos gamma quant Z] seq_top]
    by (simp add: algebra_simps \<Delta>_def)
  have \<Delta>_over_a: "(\<lambda>n. \<Delta> n / a (t0 * Z ^ n)) \<longlonglongrightarrow> D Z"
    using filterlim_compose[OF f_lim seq_top] by (simp add: algebra_simps \<Delta>_def)
  obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> 0 < \<Delta> n"
    using order_tendstoD(1)[OF \<Delta>_over_a DZ_pos] apos
    unfolding eventually_sequentially by (auto simp: pos_less_divide_eq)
  show thesis
  proof (rule that)
    show "tail_quantile F (t0 * Z ^ (N + k)) < tail_quantile F (t0 * Z ^ Suc (N + k))" for k
      using N[of "N + k"] by (simp add: \<Delta>_def)
    show "(\<lambda>k. (tail_quantile F (t0 * Z ^ Suc (N + Suc k))
                 - tail_quantile F (t0 * Z ^ (N + Suc k)))
               / (tail_quantile F (t0 * Z ^ Suc (N + k)) - tail_quantile F (t0 * Z ^ (N + k))))
           \<longlonglongrightarrow> Z powr \<gamma>"
      using LIMSEQ_ignore_initial_segment[OF \<Delta>_ratio, of N]
      by (simp add: \<Delta>_def add.commute)
  qed
qed

lemma tail_quantile_neg_gap_power_ratio:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real and a :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1"
    and apos: "\<And>t. 0 < a t"
    and gamma: "\<gamma> < 0"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
     ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
       \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
    and Uconv: "(tail_quantile F \<longlongrightarrow> x_star F) at_top"
    and Z: "1 < Z" and t0: "0 < t0"
  shows "(\<lambda>n. (x_star F - tail_quantile F (t0 * Z ^ Suc n))
                / (x_star F - tail_quantile F (t0 * Z ^ n))) \<longlonglongrightarrow> Z powr \<gamma>"
proof -
  have gamma_ne: "\<gamma> \<noteq> 0"
    using gamma by simp
  have Zg_bounds: "0 < Z powr \<gamma>" "Z powr \<gamma> < 1"
    using powr_less_mono[OF gamma, of Z] Z by simp_all
  obtain N where
    N_pos: "\<And>k. tail_quantile F (t0 * Z ^ (N + k)) < tail_quantile F (t0 * Z ^ Suc (N + k))"
    and N_ratio: "(\<lambda>k. (tail_quantile F (t0 * Z ^ Suc (N + Suc k))
                          - tail_quantile F (t0 * Z ^ (N + Suc k)))
                        / (tail_quantile F (t0 * Z ^ Suc (N + k))
                            - tail_quantile F (t0 * Z ^ (N + k)))) \<longlonglongrightarrow> Z powr \<gamma>"
    using tail_quantile_diff_geometric_seq[OF apos gamma_ne quant Z t0] by blast
  define d where "d = (\<lambda>k. tail_quantile F (t0 * Z ^ Suc (N + k))
                             - tail_quantile F (t0 * Z ^ (N + k)))"
  have d_pos: "0 < d k" for k
    using N_pos by (simp add: d_def)
  have d_eq: "d k = tail_quantile F (t0 * Z ^ Suc (N + k)) - tail_quantile F (t0 * Z ^ (N + k))"
    for k
    by (simp add: d_def)
  have d_ratio: "(\<lambda>k. d (Suc k) / d k) \<longlonglongrightarrow> Z powr \<gamma>"
    using N_ratio by (simp add: d_def)
  note d_summable = geometric_ratio_tailsum_summable[OF d_pos Zg_bounds d_ratio]
  have d_sum_eq: "(\<Sum>k<n. d k)
                    = tail_quantile F (t0 * Z ^ (N + n)) - tail_quantile F (t0 * Z ^ N)" for n
    by (induction n) (auto simp: d_eq)
  have shift_at_top: "filterlim (\<lambda>n::nat. N + n) at_top sequentially"
    by (simp add: Groups.add_ac(2) filterlim_add_const_nat_at_top)
  have Ns_top: "filterlim (\<lambda>n. t0 * Z ^ (N + n)) at_top sequentially"
    using filterlim_compose[OF filterlim_tendsto_pos_mult_at_top
        [OF tendsto_const[of t0] t0 LIMSEQ_power_at_top[OF Z]] shift_at_top] .
  have U_Ns_tendsto: "(\<lambda>n. tail_quantile F (t0 * Z ^ (N + n))) \<longlonglongrightarrow> x_star F"
    using filterlim_compose[OF Uconv Ns_top] .
  have x_star_eq: "x_star F = tail_quantile F (t0 * Z ^ N) + suminf d"
  proof -
    have lim1: "(\<lambda>n. tail_quantile F (t0 * Z ^ N) + (\<Sum>k<n. d k)) \<longlonglongrightarrow> x_star F"
      using U_Ns_tendsto by (simp add: d_sum_eq)
    have lim2: "(\<lambda>n. tail_quantile F (t0 * Z ^ N) + (\<Sum>k<n. d k))
                  \<longlonglongrightarrow> tail_quantile F (t0 * Z ^ N) + suminf d"
      by (intro tendsto_add[OF tendsto_const] summable_LIMSEQ[OF d_summable])
    show ?thesis
      using LIMSEQ_unique[OF lim1 lim2] by simp
  qed
  have gap_eq: "x_star F - tail_quantile F (t0 * Z ^ (N + n)) = (\<Sum>k. d (k + n))" for n
  proof -
    have "x_star F - tail_quantile F (t0 * Z ^ (N + n)) = suminf d - (\<Sum>k<n. d k)"
      using x_star_eq d_sum_eq[of n] by simp
    also have "\<dots> = (\<Sum>k. d (k + n))"
      using suminf_minus_initial_segment[OF d_summable, of n] by simp
    finally show ?thesis .
  qed
  note tailsum_ratio = geometric_ratio_tailsum_ratio[OF d_pos Zg_bounds d_ratio]
  have eq_fun: "\<And>n. (x_star F - tail_quantile F (t0 * Z ^ (N + Suc n)))
                       / (x_star F - tail_quantile F (t0 * Z ^ (N + n)))
                   = (\<Sum>k. d (k + Suc n)) / (\<Sum>k. d (k + n))"
  proof -
    fix n
    have e1: "x_star F - tail_quantile F (t0 * Z ^ (N + Suc n)) = (\<Sum>k. d (k + Suc n))"
      using gap_eq[of "Suc n"] .
    have e2: "x_star F - tail_quantile F (t0 * Z ^ (N + n)) = (\<Sum>k. d (k + n))"
      using gap_eq[of n] .
    show "(x_star F - tail_quantile F (t0 * Z ^ (N + Suc n)))
            / (x_star F - tail_quantile F (t0 * Z ^ (N + n)))
          = (\<Sum>k. d (k + Suc n)) / (\<Sum>k. d (k + n))"
      unfolding e1 e2 ..
  qed
  have gap_ratio_shifted: "(\<lambda>n. (x_star F - tail_quantile F (t0 * Z ^ (N + Suc n)))
                             / (x_star F - tail_quantile F (t0 * Z ^ (N + n)))) \<longlonglongrightarrow> Z powr \<gamma>"
    using tailsum_ratio unfolding eq_fun .
  have gap_ratio_shifted': "(\<lambda>n. (x_star F - tail_quantile F (t0 * Z ^ Suc (n + N)))
                             / (x_star F - tail_quantile F (t0 * Z ^ (n + N)))) \<longlonglongrightarrow> Z powr \<gamma>"
    using gap_ratio_shifted by (simp add: add.commute)
  show ?thesis
    using gap_ratio_shifted' by (rule LIMSEQ_offset)
qed

lemma tail_quantile_neg_gap_ratio_of_power_ratio:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and gamma: "\<gamma> < 0"
    and gap_pos: "\<And>t. 1 < t \<Longrightarrow> 0 < x_star F - tail_quantile F t"
    and gap_power_ratio: "\<And>Z t0. 1 < Z \<Longrightarrow> 0 < t0 \<Longrightarrow>
        (\<lambda>n. (x_star F - tail_quantile F (t0 * Z ^ Suc n))
               / (x_star F - tail_quantile F (t0 * Z ^ n))) \<longlonglongrightarrow> Z powr \<gamma>"
  shows "\<And>y. 0 < y \<Longrightarrow>
      ((\<lambda>t. (x_star F - tail_quantile F (t * y)) / (x_star F - tail_quantile F t))
         \<longlongrightarrow> y powr \<gamma>) at_top"
proof -
  define W where "W = (\<lambda>t. 1 / (x_star F - tail_quantile F t))"
  have Wmono: "W s \<le> W t" if s: "1 < s" and st: "s \<le> t" for s t
    using gap_pos[OF s] gap_pos[OF order.strict_trans2[OF s st]]
      tail_quantile_mono[OF F s st]
    by(auto simp: W_def intro!: divide_left_mono)
  have Wpos: "0 < W t" if t: "1 < t" for t
    using gap_pos[OF t] by (simp add: W_def)
  have Wpos_ev: "\<forall>\<^sub>F t in at_top. 0 < W t"
    by(intro eventually_mono[OF eventually_gt_at_top[of "1::real"]] Wpos)
  have Wratio: "(\<lambda>n. W (t0 * Z ^ Suc n) / W (t0 * Z ^ n)) \<longlonglongrightarrow> Z powr (- \<gamma>)"
    if Z: "1 < Z" and t0: "0 < t0" for Z t0 :: real
    using tendsto_inverse[OF gap_power_ratio[OF Z t0]] Z
    by(simp add: W_def powr_minus)
  fix y :: real
  assume y: "0 < y"
  have main: "((\<lambda>t. W (t * y) / W t) \<longlongrightarrow> y powr (- \<gamma>)) at_top"
    using Wratio y gamma
    by(intro monotone_geometric_ratio_imp_ratio[OF Wmono Wpos_ev]) auto
  have eq: "(\<lambda>t. inverse (W (t * y) / W t))
              = (\<lambda>t. (x_star F - tail_quantile F (t * y)) / (x_star F - tail_quantile F t))"
    by(simp add: W_def)
  show "((\<lambda>t. (x_star F - tail_quantile F (t * y)) / (x_star F - tail_quantile F t))
           \<longlongrightarrow> y powr \<gamma>) at_top"
    using tendsto_inverse[OF main] y
    unfolding eq by (simp add: powr_minus)
qed

lemma tail_quantile_neg_regularly_varying:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real and a :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1"
    and apos: "\<And>t. 0 < a t"
    and gamma: "\<gamma> < 0"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t) \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
  shows tail_quantile_neg_bdd: "bdd_support F"
    and tail_quantile_neg_tendsto: "(tail_quantile F \<longlongrightarrow> x_star F) at_top"
    and tail_quantile_neg_ratio: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (x_star F - tail_quantile F (t * y)) / (x_star F - tail_quantile F t))
           \<longlongrightarrow> y powr \<gamma>) at_top"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  have gamma_ne0: "\<gamma> \<noteq> 0"
    using gamma by simp
  have cont_ratio2: "((\<lambda>t. (tail_quantile F (t * 2 * 2) - tail_quantile F (t * 2))
                         / (tail_quantile F (t * 2) - tail_quantile F t)) \<longlongrightarrow> 2 powr \<gamma>) at_top"
    using tail_quantile_cont_ratio[OF apos gamma_ne0 quant, of 2] by simp
  have Zn_at_top: "filterlim (\<lambda>n::nat. (2::real) ^ n) at_top sequentially"
    using LIMSEQ_power_at_top[of 2] by simp
  have D2_pos: "0 < (2 powr \<gamma> - 1) / \<gamma>"
    using powr_less_mono[OF gamma, of 2]
    by(auto intro!: divide_neg_neg gamma)
  define \<Delta> where "\<Delta> = (\<lambda>n. tail_quantile F (2 ^ Suc n) - tail_quantile F (2 ^ n))"
  have \<Delta>_ratio: "(\<lambda>n. \<Delta> (Suc n) / \<Delta> n) \<longlonglongrightarrow> 2 powr \<gamma>"
  proof -
    have step: "(\<lambda>n. (tail_quantile F (2 ^ n * 2 * 2) - tail_quantile F (2 ^ n * 2))
                        / (tail_quantile F (2 ^ n * 2) - tail_quantile F (2 ^ n)))
                 \<longlonglongrightarrow> 2 powr \<gamma>"
      using filterlim_compose[OF cont_ratio2 Zn_at_top] .
    have eq: "(tail_quantile F (2 ^ n * 2 * 2) - tail_quantile F (2 ^ n * 2))
                / (tail_quantile F (2 ^ n * 2) - tail_quantile F (2 ^ n))
              = \<Delta> (Suc n) / \<Delta> n" for n
      by (simp add: \<Delta>_def algebra_simps)
    show ?thesis
      using step unfolding eq .
  qed
  have \<Delta>_over_a: "(\<lambda>n. \<Delta> n / a (2 ^ n)) \<longlonglongrightarrow> (2 powr \<gamma> - 1) / \<gamma>"
  proof -
    have "((\<lambda>t. (tail_quantile F (t * 2) - tail_quantile F t) / a t)
            \<longlongrightarrow> (2 powr \<gamma> - 1) / \<gamma>) at_top"
      using quant[of 2] by simp
    from filterlim_compose[OF this Zn_at_top]
    show ?thesis
      by (simp add: \<Delta>_def mult.commute)
  qed
  have ev_\<Delta>_pos: "\<forall>\<^sub>F n in sequentially. 0 < \<Delta> n"
  proof -
    have "\<forall>\<^sub>F n in sequentially. 0 < \<Delta> n / a (2 ^ n)"
      using order_tendstoD(1)[OF \<Delta>_over_a D2_pos] by simp
    thus ?thesis
    proof eventually_elim
      case (elim n)
      thus ?case
        using apos[of "2 ^ n"] by (simp add: zero_less_divide_iff)
    qed
  qed
  obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> 0 < \<Delta> n"
    using ev_\<Delta>_pos unfolding eventually_sequentially by blast
  define d where "d = (\<lambda>k. \<Delta> (N + k))"
  have d_pos: "0 < d k" for k
    using N by (simp add: d_def)
  have d_ratio: "(\<lambda>k. d (Suc k) / d k) \<longlonglongrightarrow> 2 powr \<gamma>"
    using LIMSEQ_ignore_initial_segment[OF \<Delta>_ratio, of N]
    by(simp add: d_def add.commute)
  have L_bounds: "0 < 2 powr \<gamma>" "2 powr \<gamma> < 1"
    using powr_less_mono[OF gamma, of 2] by simp_all
  note d_summable = geometric_ratio_tailsum_summable[OF d_pos L_bounds d_ratio]
  have d_sum_eq: "(\<Sum>k<n. d k) = tail_quantile F (2 ^ (N + n)) - tail_quantile F (2 ^ N)" for n
  proof (induction n)
    case (Suc n)
    have "(\<Sum>k<Suc n. d k) = (\<Sum>k<n. d k) + d n"
      by simp
    also have "\<dots> = (tail_quantile F (2 ^ (N + n)) - tail_quantile F (2 ^ N)) + d n"
      using Suc.IH by simp
    also have "\<dots> = tail_quantile F (2 ^ (N + Suc n)) - tail_quantile F (2 ^ N)"
      by (simp add: d_def \<Delta>_def)
    finally show ?case .
  qed simp
  have partial_le: "(\<Sum>k<n. d k) \<le> suminf d" for n
    by(intro sum_le_suminf[OF d_summable finite_lessThan] less_imp_le[OF d_pos])
  define B where "B = tail_quantile F (2 ^ N) + suminf d"
  have U_2pow_le: "tail_quantile F (2 ^ (N + n)) \<le> B" for n
    using partial_le[of n] unfolding d_sum_eq[of n] B_def by simp
  have U_le_B: "tail_quantile F t \<le> B" if t1: "1 < t" for t
  proof -
    obtain n where n: "t \<le> 2 ^ (N + n)"
    proof -
      obtain N0 where N0: "\<forall>k\<ge>N0. t \<le> 2 ^ k"
        using Zn_at_top unfolding filterlim_at_top eventually_sequentially by blast
      have "N0 \<le> N + N0"
        by simp
      hence "t \<le> 2 ^ (N + N0)"
        using N0 by simp
      thus thesis
        using that by blast
    qed
    have "tail_quantile F t \<le> tail_quantile F (2 ^ (N + n))"
      using t1 n by (intro tail_quantile_mono[OF F]) auto
    also have "\<dots> \<le> B"
      by (rule U_2pow_le)
    finally show ?thesis .
  qed
  show bdd: "bdd_support F"
  proof (rule ccontr)
    assume nbdd: "\<not> bdd_support F"
    note unbdd = F_lt_1_unbdd_support[OF F nbdd]
    note U_at_top = tail_quantile_at_top[OF F unbdd]
    obtain t where t: "1 < t" "B < tail_quantile F t"
    proof -
      have "\<forall>\<^sub>F t in at_top. B + 1 \<le> tail_quantile F t \<and> 1 < t"
        using eventually_conj[OF U_at_top[unfolded filterlim_at_top, rule_format, of "B + 1"]
                eventually_gt_at_top[of "1::real"]] .
      then obtain t0 where t0: "B + 1 \<le> tail_quantile F t0" "1 < t0"
        using eventually_happens'[OF trivial_limit_at_top_linorder] by blast
      show thesis
        using that[of t0] t0 by simp
    qed
    show False
      using U_le_B[OF t(1)] t(2) by simp
  qed
  note Fxstar = F_x_star_eq_1[OF F bdd]
  have U_le_xstar: "tail_quantile F t \<le> x_star F" if t1: "1 < t" for t
    using t1 Fxstar by (simp add: field_simps ginv_le_iff)
  show tendsto_goal: "(tail_quantile F \<longlongrightarrow> x_star F) at_top"
    by (rule tail_quantile_tendsto_x_star[OF F bdd])
  have gap_pos: "0 < x_star F - tail_quantile F t" if t1: "1 < t" for t
  proof (rule ccontr)
    assume "\<not> 0 < x_star F - tail_quantile F t"
    hence eq: "tail_quantile F t = x_star F"
      using U_le_xstar[OF t1] by simp
    have const: "tail_quantile F s = x_star F" if s1: "t \<le> s" for s
    proof (rule antisym)
      show "tail_quantile F s \<le> x_star F"
        using U_le_xstar[of s] t1 s1 by simp
      have "tail_quantile F t \<le> tail_quantile F s"
        using tail_quantile_mono[OF F t1 s1] .
      thus "x_star F \<le> tail_quantile F s"
        using eq by simp
    qed
    have ev0: "\<forall>\<^sub>F s in at_top. (tail_quantile F (s * 2) - tail_quantile F s) / a s = 0"
      using const t1 by (auto intro!: eventually_mono[OF eventually_ge_at_top[of t]])
    have ev0': "\<forall>\<^sub>F s in at_top. 0 = (tail_quantile F (s * 2) - tail_quantile F s) / a s"
      using ev0 by eventually_elim simp
    have ratio_to_0: "((\<lambda>s. (tail_quantile F (s * 2) - tail_quantile F s) / a s) \<longlongrightarrow> 0) at_top"
      using Lim_transform_eventually[OF tendsto_const ev0'] .
    have ratio_to_D2: "((\<lambda>s. (tail_quantile F (s * 2) - tail_quantile F s) / a s)
                          \<longlongrightarrow> (2 powr \<gamma> - 1) / \<gamma>) at_top"
      using quant[of 2] by simp
    have "(2 powr \<gamma> - 1) / \<gamma> = 0"
      using tendsto_unique[OF trivial_limit_at_top_linorder ratio_to_D2 ratio_to_0] .
    thus False
      using D2_pos by simp
  qed
  have gap_power_ratio: "\<And>Z t0. 1 < Z \<Longrightarrow> 0 < t0 \<Longrightarrow>
      (\<lambda>n. (x_star F - tail_quantile F (t0 * Z ^ Suc n))
           / (x_star F - tail_quantile F (t0 * Z ^ n)))
        \<longlonglongrightarrow> Z powr \<gamma>"
    using tail_quantile_neg_gap_power_ratio[OF F apos gamma quant tendsto_goal] .
  show "\<And>y. 0 < y \<Longrightarrow>
      ((\<lambda>t. (x_star F - tail_quantile F (t * y)) / (x_star F - tail_quantile F t))
         \<longlongrightarrow> y powr \<gamma>) at_top"
    using tail_quantile_neg_gap_ratio_of_power_ratio[OF F gamma gap_pos gap_power_ratio] .
qed

lemma tail_quantile_gap_ratio_neg_imp_tail_regularly_varying:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and gamma: "\<gamma> < 0"
    and bdd: "bdd_support F"
    and gap_rv: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (x_star F - tail_quantile F (t * y)) / (x_star F - tail_quantile F t))
           \<longlongrightarrow> y powr \<gamma>) at_top"
  shows "regularly_varying (\<lambda>s. 1 - F (x_star F - 1 / s)) (1 / \<gamma>)"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  have phi_pos: "0 < 1 - F (x_star F - 1 / s)" if s: "0 < s" for s
    using s lt_x_star_iff_F_lt_1[OF F bdd, THEN iffD1] by fastforce
  note Fxstar = F_x_star_eq_1[OF F bdd]
  have U_le_xstar: "tail_quantile F t \<le> x_star F" if t1: "1 < t" for t
    using t1 Fxstar by (simp add: field_simps ginv_le_iff)
  note Utend = tail_quantile_tendsto_x_star[OF F bdd]
  have gap_pos: "0 < x_star F - tail_quantile F t" if t1: "1 < t" for t
  proof (rule ccontr)
    assume "\<not> 0 < x_star F - tail_quantile F t"
    hence eq: "tail_quantile F t = x_star F"
      using U_le_xstar[OF t1] by simp
    have const: "tail_quantile F u = x_star F" if u1: "t \<le> u" for u
    proof (rule antisym)
      show "tail_quantile F u \<le> x_star F"
        using U_le_xstar[of u] t1 u1 by simp
      have "tail_quantile F t \<le> tail_quantile F u"
        using tail_quantile_mono[OF F t1 u1] .
      thus "x_star F \<le> tail_quantile F u"
        using eq by simp
    qed
    have ev0: "\<forall>\<^sub>F u in at_top.
                 (x_star F - tail_quantile F (u * 2)) / (x_star F - tail_quantile F u) = 0"
      using const t1 by (auto intro!: eventually_mono[OF eventually_ge_at_top[of t]])
    have ev0': "\<forall>\<^sub>F u in at_top. (0::real)
               = (x_star F - tail_quantile F (u * 2)) / (x_star F - tail_quantile F u)"
      using ev0 by eventually_elim simp
    have ratio_to_0: "((\<lambda>u.
        (x_star F - tail_quantile F (u * 2)) / (x_star F - tail_quantile F u)) \<longlongrightarrow> 0) at_top"
      using Lim_transform_eventually[OF tendsto_const ev0'] .
    have ratio_to_2g: "((\<lambda>u.
        (x_star F - tail_quantile F (u * 2)) / (x_star F - tail_quantile F u))
         \<longlongrightarrow> 2 powr \<gamma>) at_top"
      using gap_rv[of 2] by simp
    have "2 powr \<gamma> = 0"
      using tendsto_unique[OF trivial_limit_at_top_linorder ratio_to_2g ratio_to_0] .
    thus False
      by simp
  qed
  define W where "W = (\<lambda>t::real. 1 / (x_star F - tail_quantile F t))"
  define s where "s = (\<lambda>w::real. 1 / (1 - F (x_star F - 1 / w)))"
  have galois: "W t \<le> w \<longleftrightarrow> t \<le> s w" if t1: "1 < t" for t w
  proof (cases "0 < w")
    case True
    note gpos = gap_pos[OF t1]
    note phipos = phi_pos[OF True]
    have p_bounds: "0 < 1 - 1 / t" "1 - 1 / t < 1"
      using t1 by simp_all
    have "W t \<le> w \<longleftrightarrow> tail_quantile F t \<le> x_star F - 1 / w"
      unfolding W_def using gpos True by (simp add: field_simps)
    also have "... \<longleftrightarrow> 1 - 1 / t \<le> F (x_star F - 1 / w)"
      using ginv_le_iff[OF p_bounds, of "x_star F - 1 / w"] by simp
    also have "... \<longleftrightarrow> t \<le> s w"
      using phipos True t1 by (simp add: s_def field_simps)
    finally show ?thesis .
  next
    case False
    have "\<not> (W t \<le> w)"
    proof -
      note gpos = gap_pos[OF t1]
      hence "0 < W t"
        unfolding W_def by simp
      thus ?thesis
        using False by linarith
    qed
    moreover have "\<not> (t \<le> s w)"
    proof -
      have wle0: "w < 0 \<or> w = 0"
        using False by linarith
      have "1 / w \<le> 0"
        using wle0 by (auto simp: divide_le_0_iff)
      hence "x_star F \<le> x_star F - 1 / w"
        by simp
      hence "F (x_star F) \<le> F (x_star F - 1 / w)"
        by (rule monoD[OF mono])
      hence "F (x_star F - 1 / w) = 1"
        using Fxstar right_continuous_mono.f_le_b[OF F, of "x_star F - 1 / w"] by simp
      hence "s w = 0"
        unfolding s_def by simp
      thus ?thesis
        using t1 by simp
    qed
    ultimately show ?thesis
      by simp
  qed
  have Wtop: "filterlim W at_top at_top"
  proof -
    have gap_tend0: "((\<lambda>t. x_star F - tail_quantile F t) \<longlongrightarrow> 0) at_top"
      using tendsto_diff[OF tendsto_const[of "x_star F"] Utend] by simp
    have gap_pos_ev: "\<forall>\<^sub>F t in at_top. 0 < x_star F - tail_quantile F t"
      using eventually_gt_at_top[of "1::real"] by eventually_elim (rule gap_pos)
    show ?thesis
      unfolding W_def
      using filterlim_inverse_at_top[OF gap_tend0 gap_pos_ev] by (simp add: inverse_eq_divide)
  qed
  have s_top: "filterlim s at_top at_top"
    unfolding filterlim_at_top
  proof
    fix M :: real
    define M' where "M' = max M 2"
    have M'1: "1 < M'"
      unfolding M'_def by simp
    have WM'pos: "0 < W M'"
      unfolding W_def using gap_pos[OF M'1] by simp
    show "\<forall>\<^sub>F w in at_top. M \<le> s w"
      using eventually_ge_at_top[of "W M'"]
      by eventually_elim (use galois[OF M'1] in "simp add: M'_def")
  qed
  have Wrv: "((\<lambda>t. W (t * y) / W t) \<longlongrightarrow> y powr (- \<gamma>)) at_top" if y: "0 < y" for y
  proof -
    have r1: "((\<lambda>t. (x_star F - tail_quantile F (t * y)) / (x_star F - tail_quantile F t))
                 \<longlongrightarrow> y powr \<gamma>) at_top"
      using gap_rv[OF y] .
    have ypow_ne: "y powr \<gamma> \<noteq> 0"
      using y by simp
    note r1inv = tendsto_inverse[OF r1 ypow_ne]
    have ty_top: "filterlim (\<lambda>t::real. t * y) at_top at_top"
      using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of y] y filterlim_ident]
      by(simp add: mult.commute)
    have ev_ty: "\<forall>\<^sub>F t in at_top. 1 < t * y"
      using ty_top[unfolded filterlim_at_top, rule_format, of 2] by eventually_elim simp
    have eq: "\<forall>\<^sub>F t in at_top. inverse ((x_star F - tail_quantile F (t * y))
                         / (x_star F - tail_quantile F t)) = W (t * y) / W t"
      using eventually_gt_at_top[of 1] ev_ty
      by eventually_elim (use gap_pos in "simp add: W_def field_simps")
    have "((\<lambda>t. W (t * y) / W t) \<longlongrightarrow> inverse (y powr \<gamma>)) at_top"
      using Lim_transform_eventually[OF r1inv eq] .
    thus ?thesis
      by (simp add: powr_minus)
  qed
  have s_pos: "0 < s w" if w: "0 < w" for w
    unfolding s_def using phi_pos[OF w] by simp
  have s_ratio: "((\<lambda>u. s (u * x) / s u) \<longlongrightarrow> x powr (- 1 / \<gamma>)) at_top"
    if x: "0 < x" for x
    using galois_inverse_ratio_tendsto[OF Wtop s_top s_pos galois _ Wrv x] gamma
    by simp
  have phi_ratio: "((\<lambda>u. (1 - F (x_star F - 1 / (u * x))) / (1 - F (x_star F - 1 / u)))
                      \<longlongrightarrow> x powr (1 / \<gamma>)) at_top" if x: "0 < x" for x
  proof -
    have same: "(\<lambda>u. s (u * x) / s u)
                  = (\<lambda>u. (1 - F (x_star F - 1 / u)) / (1 - F (x_star F - 1 / (u * x))))"
      using phi_pos x by (auto simp: s_def)
    have main: "((\<lambda>u. (1 - F (x_star F - 1 / u)) / (1 - F (x_star F - 1 / (u * x))))
                   \<longlongrightarrow> x powr (- 1 / \<gamma>)) at_top"
      using s_ratio[OF x] unfolding same .
    have xr_ne: "x powr (- 1 / \<gamma>) \<noteq> 0"
      using x by simp
    have inv: "((\<lambda>u. inverse ((1 - F (x_star F - 1 / u)) / (1 - F (x_star F - 1 / (u * x)))))
                  \<longlongrightarrow> inverse (x powr (- 1 / \<gamma>))) at_top"
      by (intro tendsto_inverse main xr_ne)
    have eq2: "(\<lambda>u. inverse ((1 - F (x_star F - 1 / u)) / (1 - F (x_star F - 1 / (u * x)))))
                 = (\<lambda>u. (1 - F (x_star F - 1 / (u * x))) / (1 - F (x_star F - 1 / u)))"
      by simp
    have lim: "((\<lambda>u. (1 - F (x_star F - 1 / (u * x))) / (1 - F (x_star F - 1 / u)))
                  \<longlongrightarrow> inverse (x powr (- 1 / \<gamma>))) at_top"
      using inv unfolding eq2 .
    have val_eq: "inverse (x powr (- 1 / \<gamma>)) = x powr (1 / \<gamma>)"
      using x by (simp add: powr_minus)
    show ?thesis
      using lim unfolding val_eq .
  qed
  show ?thesis
  proof (rule regularly_varyingI)
    have Fmeas: "F \<in> borel_measurable borel"
      using borel_measurable_mono[OF mono] .
    have cont: "continuous_on {0<..} (\<lambda>s::real. x_star F - 1 / s)"
      by (intro continuous_intros) simp
    have meas1: "(\<lambda>s::real. x_star F - 1 / s) \<in> borel_measurable (restrict_space borel {0<..})"
      using cont by (rule borel_measurable_continuous_on_restrict)
    show "(\<lambda>s. 1 - F (x_star F - 1 / s)) \<in> borel_measurable (restrict_space borel {0<..})"
      using measurable_compose[OF meas1 Fmeas] by simp
  qed(use phi_pos phi_ratio in auto)
qed

lemma tail_quantile_pos_power_ratio:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real and a :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1"
    and apos: "\<And>t. 0 < a t"
    and gamma: "0 < \<gamma>"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
          \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
    and Uinf: "filterlim (tail_quantile F) at_top at_top"
    and Z: "1 < Z" and t0: "0 < t0"
  shows "(\<lambda>n. tail_quantile F (t0 * Z ^ Suc n) / tail_quantile F (t0 * Z ^ n))
           \<longlonglongrightarrow> Z powr \<gamma>"
proof -
  have gamma_ne: "\<gamma> \<noteq> 0"
    using gamma by simp
  have Zg_gt1: "1 < Z powr \<gamma>"
    using powr_less_mono2[OF gamma zero_le_one Z] by simp
  have s_top: "filterlim (\<lambda>n. t0 * Z ^ n) at_top sequentially"
    using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of t0] t0
        LIMSEQ_power_at_top[OF Z]] .
  obtain N where
    N_pos: "\<And>k. tail_quantile F (t0 * Z ^ (N + k)) < tail_quantile F (t0 * Z ^ Suc (N + k))"
    and N_ratio: "(\<lambda>k. (tail_quantile F (t0 * Z ^ Suc (N + Suc k))
                          - tail_quantile F (t0 * Z ^ (N + Suc k)))
                        / (tail_quantile F (t0 * Z ^ Suc (N + k))
                            - tail_quantile F (t0 * Z ^ (N + k)))) \<longlonglongrightarrow> Z powr \<gamma>"
    using tail_quantile_diff_geometric_seq[OF apos gamma_ne quant Z t0] by blast
  define d where "d = (\<lambda>k. tail_quantile F (t0 * Z ^ Suc (N + k))
                             - tail_quantile F (t0 * Z ^ (N + k)))"
  have d_pos: "0 < d k" for k
    using N_pos by (simp add: d_def)
  have d_eq: "d k = tail_quantile F (t0 * Z ^ Suc (N + k)) - tail_quantile F (t0 * Z ^ (N + k))"
    for k
    by (simp add: d_def)
  have d_ratio: "(\<lambda>k. d (Suc k) / d k) \<longlonglongrightarrow> Z powr \<gamma>"
    using N_ratio by (simp add: d_def)
  note d_sum_ratio = geometric_ratio_sum_ratio[OF d_pos Zg_gt1 d_ratio]
  have d_sum_eq: "(\<Sum>j\<le>k. d j)
                    = tail_quantile F (t0 * Z ^ (N + Suc k)) - tail_quantile F (t0 * Z ^ N)" for k
    by (induction k) (auto simp: d_eq)
  define C where "C = tail_quantile F (t0 * Z ^ N)"
  have PQ_ratio: "(\<lambda>k. (tail_quantile F (t0 * Z ^ (N + Suc (Suc k))) - C)
                          / (tail_quantile F (t0 * Z ^ (N + Suc k)) - C)) \<longlonglongrightarrow> Z powr \<gamma>"
  proof -
    have "(\<lambda>k. (tail_quantile F (t0 * Z ^ (N + Suc k)) - tail_quantile F (t0 * Z ^ N)
                  + d (Suc k))
                / (tail_quantile F (t0 * Z ^ (N + Suc k)) - tail_quantile F (t0 * Z ^ N)))
          \<longlonglongrightarrow> Z powr \<gamma>"
      using d_sum_ratio by (simp add: d_sum_eq)
    thus ?thesis
      by (simp add: d_def C_def algebra_simps)
  qed
  have shift1_at_top: "filterlim (\<lambda>k::nat. N + Suc k) at_top sequentially"
    by (intro filterlim_subseq strict_monoI) simp
  note P_seq_at_top = filterlim_compose[OF s_top shift1_at_top]
  note P_at_top = filterlim_compose[OF Uinf P_seq_at_top]
  note invP0 = tendsto_inverse_0_at_top[OF P_at_top]
  have C_over_P: "(\<lambda>k. C / tail_quantile F (t0 * Z ^ (N + Suc k))) \<longlonglongrightarrow> 0"
    using tendsto_mult[OF tendsto_const[of C] invP0] by (simp add: divide_inverse)
  have one_minus_C_over_P: "(\<lambda>k. 1 - C / tail_quantile F (t0 * Z ^ (N + Suc k))) \<longlonglongrightarrow> 1"
    using tendsto_diff[OF tendsto_const[of 1] C_over_P] by simp
  have combo: "(\<lambda>k. (tail_quantile F (t0 * Z ^ (N + Suc (Suc k))) - C)
                       / (tail_quantile F (t0 * Z ^ (N + Suc k)) - C)
                     * (1 - C / tail_quantile F (t0 * Z ^ (N + Suc k)))
                   + C / tail_quantile F (t0 * Z ^ (N + Suc k))) \<longlonglongrightarrow> Z powr \<gamma>"
    using tendsto_add[OF tendsto_mult[OF PQ_ratio one_minus_C_over_P] C_over_P] by simp
  have P_ge: "\<forall>\<^sub>F k in sequentially. \<bar>C\<bar> + 1 \<le> tail_quantile F (t0 * Z ^ (N + Suc k))"
    using P_at_top[unfolded filterlim_at_top, rule_format, of "\<bar>C\<bar> + 1"] by simp
  have combo_eq: "\<forall>\<^sub>F k in sequentially. (tail_quantile F (t0 * Z ^ (N + Suc (Suc k))) - C)
                     / (tail_quantile F (t0 * Z ^ (N + Suc k)) - C)
                     * (1 - C / tail_quantile F (t0 * Z ^ (N + Suc k)))
                   + C / tail_quantile F (t0 * Z ^ (N + Suc k))
                   = tail_quantile F (t0 * Z ^ (N + Suc (Suc k)))
                     / tail_quantile F (t0 * Z ^ (N + Suc k))"
    using P_ge
  proof eventually_elim
    case (elim k)
    have C_lt: "C < tail_quantile F (t0 * Z ^ (N + Suc k))"
      using elim abs_ge_self[of C] by linarith
    have P_pos: "0 < tail_quantile F (t0 * Z ^ (N + Suc k))"
      using elim abs_ge_zero[of C] by linarith
    have p_ne: "tail_quantile F (t0 * Z ^ (N + Suc k)) \<noteq> 0"
      using P_pos by simp
    have pc_ne: "tail_quantile F (t0 * Z ^ (N + Suc k)) - C \<noteq> 0"
      using C_lt by simp
    show ?case
      using p_ne pc_ne by (simp add: field_simps)
  qed
  have shifted_target: "(\<lambda>k. tail_quantile F (t0 * Z ^ (N + Suc (Suc k)))
                                / tail_quantile F (t0 * Z ^ (N + Suc k))) \<longlonglongrightarrow> Z powr \<gamma>"
    using Lim_transform_eventually[OF combo combo_eq] .
  have offset_eq: "tail_quantile F (t0 * Z ^ Suc (k + (N + 1)))
                     / tail_quantile F (t0 * Z ^ (k + (N + 1)))
                   = tail_quantile F (t0 * Z ^ (N + Suc (Suc k)))
                       / tail_quantile F (t0 * Z ^ (N + Suc k))" for k
    by (simp add: add.commute)
  have offset_target: "(\<lambda>k. tail_quantile F (t0 * Z ^ Suc (k + (N + 1)))
                              / tail_quantile F (t0 * Z ^ (k + (N + 1)))) \<longlonglongrightarrow> Z powr \<gamma>"
    unfolding offset_eq using shifted_target .
  show ?thesis
    using offset_target by (rule LIMSEQ_offset)
qed

lemma tail_quantile_pos_ratio_of_power_ratio:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and gamma: "0 < \<gamma>"
    and Uinf: "filterlim (tail_quantile F) at_top at_top"
    and power_ratio: "\<And>Z t0. 1 < Z \<Longrightarrow> 0 < t0 \<Longrightarrow>
        (\<lambda>n. tail_quantile F (t0 * Z ^ Suc n) / tail_quantile F (t0 * Z ^ n)) \<longlonglongrightarrow> Z powr \<gamma>"
  shows "\<And>y. 0 < y \<Longrightarrow>
      ((\<lambda>t. tail_quantile F (t * y) / tail_quantile F t) \<longlongrightarrow> y powr \<gamma>) at_top"
proof -
  have Upos: "\<forall>\<^sub>F t in at_top. 0 < tail_quantile F t"
    using Uinf unfolding filterlim_at_top_dense by blast
  fix y :: real
  assume y: "0 < y"
  show "((\<lambda>t. tail_quantile F (t * y) / tail_quantile F t) \<longlongrightarrow> y powr \<gamma>) at_top"
    using power_ratio y
    by(intro monotone_geometric_ratio_imp_ratio[OF _ Upos gamma])
      (auto intro: tail_quantile_mono[OF F])
qed

lemma tail_quantile_pos_regularly_varying:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real and a :: "real \<Rightarrow> real"
  assumes F: "right_continuous_mono F 0 1"
    and apos: "\<And>t. 0 < a t"
    and gamma: "0 < \<gamma>"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
          \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
  shows tail_quantile_pos_at_top: "filterlim (tail_quantile F) at_top at_top"
    and tail_quantile_pos_ratio: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. tail_quantile F (t * y) / tail_quantile F t) \<longlongrightarrow> y powr \<gamma>) at_top"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  have gamma_ne0: "\<gamma> \<noteq> 0"
    using gamma by simp
  have a_rv: "((\<lambda>t. a (t * y) / a t) \<longlongrightarrow> y powr \<gamma>) at_top" if y: "0 < y" for y
    by (rule tail_quantile_diff_scale_ratio[where U = "tail_quantile F",
          OF apos gamma_ne0 quant y])

  show U_at_top: "filterlim (tail_quantile F) at_top at_top"
  proof -
    have a_rv2: "((\<lambda>t. a (t * 2) / a t) \<longlongrightarrow> 2 powr \<gamma>) at_top"
      using a_rv[of 2] by simp
    have quant2: "((\<lambda>t. (tail_quantile F (t * 2) - tail_quantile F t) / a t)
                     \<longlongrightarrow> (2 powr \<gamma> - 1) / \<gamma>) at_top"
      using quant[of 2] by simp
    define r0 :: real where "r0 = (1 + 2 powr \<gamma>) / 2"
    have r0_bounds: "1 < r0" "r0 < 2 powr \<gamma>"
      using gamma by (simp_all add: r0_def)
    define c :: real where "c = ((2 powr \<gamma> - 1) / \<gamma>) / 2"
    have c_pos: "0 < c"
      using gamma by (simp add: c_def)
    have c_lt_D2: "c < (2 powr \<gamma> - 1) / \<gamma>"
      using gamma by(auto simp: c_def intro!: divide_strict_left_mono)
    have a_ev: "\<forall>\<^sub>F t in at_top. r0 * a t < a (t * 2)"
      using order_tendstoD(1)[OF a_rv2 r0_bounds(2)]
      by eventually_elim (use apos in "simp add: field_simps")
    have U_ev: "\<forall>\<^sub>F t in at_top. c * a t < tail_quantile F (t * 2) - tail_quantile F t"
      using order_tendstoD(1)[OF quant2 c_lt_D2]
      by eventually_elim (use apos in "simp add: field_simps")
    obtain T1 where T1: "\<And>t. T1 \<le> t \<Longrightarrow> r0 * a t < a (t * 2)"
      using a_ev unfolding eventually_at_top_linorder by blast
    obtain T2 where T2: "\<And>t. T2 \<le> t \<Longrightarrow> c * a t < tail_quantile F (t * 2) - tail_quantile F t"
      using U_ev unfolding eventually_at_top_linorder by blast
    define T where "T = max T1 T2"
    have T: "\<And>t. T \<le> t \<Longrightarrow> r0 * a t < a (t * 2)"
      "\<And>t. T \<le> t \<Longrightarrow> c * a t < tail_quantile F (t * 2) - tail_quantile F t"
      using T1 T2 by (auto simp: T_def)
    define t0 :: real where "t0 = max T 2"
    have t0_ge: "T \<le> t0" "2 \<le> t0"
      by (simp_all add: t0_def)
    define tn :: "nat \<Rightarrow> real" where "tn n = t0 * 2 ^ n" for n
    have two_pow_ge1: "(1::real) \<le> 2 ^ n" for n
      by simp
    have t0_le_tn: "t0 \<le> tn n" for n
      using two_pow_ge1[of n] t0_ge(2) by (simp add: tn_def mult_left_mono)
    have tn_ge_T: "T \<le> tn n" for n
      using t0_ge(1) t0_le_tn[of n] by simp
    have tn_gt1: "1 < tn n" for n
      using t0_ge(2) t0_le_tn[of n] by simp
    have tn_Suc: "tn (Suc n) = tn n * 2" for n
      by (simp add: tn_def)
    have tn_mono: "m \<le> n \<Longrightarrow> tn m \<le> tn n" for m n
      using t0_ge(2) by (simp add: tn_def mult_left_mono power_increasing)
    have a_grow: "r0 ^ n * a t0 \<le> a (tn n)" for n
    proof (induction n)
      case 0
      show ?case
        by (simp add: tn_def)
    next
      case (Suc n)
      have "r0 * a (tn n) < a (tn n * 2)"
        using T(1)[OF tn_ge_T[of n]] by simp
      hence step: "r0 * a (tn n) < a (tn (Suc n))"
        by (simp add: tn_Suc)
      have "r0 ^ Suc n * a t0 = r0 * (r0 ^ n * a t0)"
        by simp
      also have "\<dots> \<le> r0 * a (tn n)"
        using Suc.IH r0_bounds(1) by (intro mult_left_mono) auto
      also have "\<dots> < a (tn (Suc n))"
        by (rule step)
      finally show ?case
        by simp
    qed
    note r0n_at_top = LIMSEQ_power_at_top[OF r0_bounds(1)]
    have a_tn_at_top: "filterlim (\<lambda>n. a (tn n)) at_top sequentially"
    proof (rule filterlim_at_top_mono)
      from filterlim_tendsto_pos_mult_at_top[OF tendsto_const apos[of t0] r0n_at_top]
      have "filterlim (\<lambda>n. a t0 * r0 ^ n) at_top sequentially" .
      thus "filterlim (\<lambda>n. r0 ^ n * a t0) at_top sequentially"
        by (simp add: mult.commute)
      show "\<forall>\<^sub>F n in sequentially. r0 ^ n * a t0 \<le> a (tn n)"
        using a_grow by (intro always_eventually) simp
    qed
    have U_mono_seq: "m \<le> n \<Longrightarrow> tail_quantile F (tn m) \<le> tail_quantile F (tn n)" for m n
      using tn_gt1[of m] tn_mono[of m n]
      by (intro tail_quantile_mono[OF \<open>right_continuous_mono F 0 1\<close>]) auto
    have not_bdd: "\<not> bdd_above (range (\<lambda>n. tail_quantile F (tn n)))"
    proof
      assume bdd: "bdd_above (range (\<lambda>n. tail_quantile F (tn n)))"
      have incseq: "incseq (\<lambda>n. tail_quantile F (tn n))"
        using U_mono_seq by (intro incseq_SucI) simp
      obtain B where B: "\<And>n. tail_quantile F (tn n) \<le> B"
        using bdd unfolding bdd_above_def by auto
      obtain L where L: "(\<lambda>n. tail_quantile F (tn n)) \<longlonglongrightarrow> L"
        using incseq_convergent[OF incseq, of B] B by meson
      have diff0: "(\<lambda>n. tail_quantile F (tn (Suc n)) - tail_quantile F (tn n)) \<longlonglongrightarrow> 0"
        using tendsto_diff[OF LIMSEQ_Suc[OF L] L] by simp
      have diff_gt: "\<forall>\<^sub>F n in sequentially. c * a (tn n)
                                    < tail_quantile F (tn (Suc n)) - tail_quantile F (tn n)"
        using T(2)[OF tn_ge_T] by (intro always_eventually) (simp add: tn_Suc)
      have ge1: "\<forall>\<^sub>F n in sequentially. 1 \<le> c * a (tn n)"
        using a_tn_at_top[unfolded filterlim_at_top, rule_format, of "1 / c"]
        by eventually_elim (use c_pos in "simp add: field_simps")
      have gt1_ev: "\<forall>\<^sub>F n in sequentially. 1
                           < tail_quantile F (tn (Suc n)) - tail_quantile F (tn n)"
        using ge1 diff_gt
        by eventually_elim simp
      have lt1_ev:
        "\<forall>\<^sub>F n in sequentially. tail_quantile F (tn (Suc n)) - tail_quantile F (tn n) < 1"
        using order_tendstoD(2)[OF diff0, of 1] by simp
      have "\<forall>\<^sub>F n::nat in sequentially. False"
        using gt1_ev lt1_ev by eventually_elim linarith
      thus False
        by simp
    qed
    have tn_ex: "\<And>M. \<exists>n. M < tail_quantile F (tn n)"
      using not_bdd unfolding bdd_above_def by (auto simp: not_le)
    show ?thesis
      unfolding filterlim_at_top
    proof
      fix M :: real
      obtain n where n: "M < tail_quantile F (tn n)"
        using tn_ex by blast
      show "\<forall>\<^sub>F t in at_top. M \<le> tail_quantile F t"
        using eventually_ge_at_top[of "tn n"]
      proof eventually_elim
        case (elim t)
        have "tail_quantile F (tn n) \<le> tail_quantile F t"
          using tn_gt1[of n] elim
          by (intro tail_quantile_mono[OF \<open>right_continuous_mono F 0 1\<close>]) auto
        with n show ?case
          by simp
      qed
    qed
  qed
  show "\<And>y. 0 < y \<Longrightarrow>
      ((\<lambda>t. tail_quantile F (t * y) / tail_quantile F t) \<longlongrightarrow> y powr \<gamma>) at_top"
    by (intro tail_quantile_pos_ratio_of_power_ratio[OF F gamma U_at_top]
        tail_quantile_pos_power_ratio[OF F apos gamma quant U_at_top])
qed

lemma tail_quantile_ratio_pos_imp_tail_regularly_varying:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and gamma: "0 < \<gamma>"
    and Uinf: "filterlim (tail_quantile F) at_top at_top"
    and Urv: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. tail_quantile F (t * y) / tail_quantile F t) \<longlongrightarrow> y powr \<gamma>) at_top"
  shows "(\<forall>x. F x < 1) \<and> regularly_varying (\<lambda>x. 1 - F x) (- 1 / \<gamma>)"
proof -
  interpret right_continuous_mono F 0 1
    by fact
  have unbdd: "\<not> bdd_support F"
  proof
    assume bdd: "bdd_support F"
    have Fx1: "F (x_star F + 1) = 1"
      using bdd cSup_upper[of "x_star F + 1" "{x. F x < 1}"] f_le_b[of "x_star F + 1"]
      unfolding x_star_def by fastforce
    have le: "tail_quantile F t \<le> x_star F + 1" if t1: "1 < t" for t
      using Fx1 t1 by (simp add: ginv_le_iff)
    have "\<forall>\<^sub>F t in at_top. x_star F + 1 < tail_quantile F t"
      using Uinf[unfolded filterlim_at_top, rule_format, of "x_star F + 2"]
      by eventually_elim simp
    from eventually_gt_at_top[of "1::real"] this
    have "\<forall>\<^sub>F t in at_top. 1 < t \<and> x_star F + 1 < tail_quantile F t"
      by (rule eventually_conj)
    then obtain t where "1 < t" "x_star F + 1 < tail_quantile F t"
      using eventually_happens'[OF trivial_limit_at_top_linorder] by blast
    with le[of t] show False
      by simp
  qed
  have Flt1: "\<forall>x. F x < 1"
    using F_lt_1_unbdd_support[OF \<open>right_continuous_mono F 0 1\<close> unbdd] by blast
  define s where "s = (\<lambda>t::real. 1 / (1 - F t))"
  have Ftop: "(F \<longlongrightarrow> 1) at_top"
    using top by simp
  have s_top: "filterlim s at_top at_top"
  proof -
    have Ftend: "((\<lambda>t. 1 - F t) \<longlongrightarrow> 0) at_top"
      using tendsto_diff[OF tendsto_const[of 1] Ftop] by simp
    have Fpos: "\<forall>\<^sub>F t in at_top. 0 < 1 - F t"
      using Flt1 by (auto intro!: always_eventually)
    from filterlim_inverse_at_top[OF Ftend Fpos]
    show ?thesis
      by (simp add: s_def inverse_eq_divide)
  qed
  have galois: "tail_quantile F t \<le> z \<longleftrightarrow> t \<le> s z" if t1: "1 < t" for t z
  proof -
    have p_bounds: "0 < 1 - 1 / t" "1 - 1 / t < 1"
      using t1 by simp_all
    have "tail_quantile F t \<le> z \<longleftrightarrow> 1 - 1 / t \<le> F z"
      using ginv_le_iff[OF p_bounds, of z] by simp
    also have "\<dots> \<longleftrightarrow> t \<le> s z"
      using Flt1 t1 by (simp add: s_def field_simps)
    finally show ?thesis .
  qed
  have s_pos: "0 < s w" if "0 < w" for w
    using Flt1 by (simp add: s_def)
  have s_ratio: "((\<lambda>u. s (u * x) / s u) \<longlongrightarrow> x powr (1 / \<gamma>)) at_top"
    if x: "0 < x" for x
    using galois_inverse_ratio_tendsto[OF Uinf s_top s_pos galois gamma Urv x] .
  have tail_ratio: "((\<lambda>u. (1 - F (u * x)) / (1 - F u)) \<longlongrightarrow> x powr (- 1 / \<gamma>)) at_top"
    if x: "0 < x" for x
  proof -
    have same: "(\<lambda>u. s (u * x) / s u) = (\<lambda>u. (1 - F u) / (1 - F (u * x)))"
      using Flt1 by (auto simp: s_def)
    have main: "((\<lambda>u. (1 - F u) / (1 - F (u * x))) \<longlongrightarrow> x powr (1 / \<gamma>)) at_top"
      using s_ratio[OF x] unfolding same .
    have xr_ne: "x powr (1 / \<gamma>) \<noteq> 0"
      using x by simp
    have inv: "((\<lambda>u. inverse ((1 - F u) / (1 - F (u * x))))
                  \<longlongrightarrow> inverse (x powr (1 / \<gamma>))) at_top"
      by (intro tendsto_inverse main xr_ne)
    have eq2: "(\<lambda>u. inverse ((1 - F u) / (1 - F (u * x)))) = (\<lambda>u. (1 - F (u * x)) / (1 - F u))"
      by simp
    have lim: "((\<lambda>u. (1 - F (u * x)) / (1 - F u)) \<longlongrightarrow> inverse (x powr (1 / \<gamma>))) at_top"
      using inv unfolding eq2 .
    have val_eq: "inverse (x powr (1 / \<gamma>)) = x powr (- 1 / \<gamma>)"
      using x by (simp add: powr_minus)
    show ?thesis
      using lim unfolding val_eq .
  qed
  have final_rv: "regularly_varying (\<lambda>x. 1 - F x) (- 1 / \<gamma>)"
    using borel_measurable_mono[OF mono] Flt1 tail_ratio
    by(auto intro!: regularly_varyingI measurable_restrict_space1)
  show ?thesis
    using Flt1 final_rv by blast
qed

theorem MDA_regularly_varying_pos:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and gamma[arith]: "0 < \<gamma>"
  shows "domain_of_attraction F (EVD_cdf \<gamma> 0 1)
          \<longleftrightarrow> (\<forall>x. F x < 1) \<and> regularly_varying (\<lambda>x. 1 - F x) (- 1 / \<gamma>)"
proof
  assume dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  obtain a where apos: "\<And>t. 0 < a t"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t) \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of \<gamma>] gamma by auto
  show "(\<forall>x. F x < 1) \<and> regularly_varying (\<lambda>x. 1 - F x) (- 1 / \<gamma>)"
    by (intro tail_quantile_ratio_pos_imp_tail_regularly_varying[OF F gamma]
        tail_quantile_pos_ratio[OF F apos gamma quant]
        tail_quantile_pos_at_top[OF F apos gamma quant])
next
  assume rv: "(\<forall>x. F x < 1) \<and> regularly_varying (\<lambda>x. 1 - F x) (- 1 / \<gamma>)"
  hence unbdd: "\<And>x. F x < 1" and rv': "regularly_varying (\<lambda>x. 1 - F x) (- (1 / \<gamma>))"
    by auto
  have not_bdd: "\<not> bdd_support F"
    by (rule not_bdd_supportI'[OF unbdd])
  have endpoint_eq: "endpoint_filter F = at_top"
    using not_bdd by (simp add: endpoint_filter_def)
  define f where "f = (\<lambda>t::real. \<gamma> * max t 1)"
  have f_pos: "\<And>t. 0 < f t"
    unfolding f_def by simp
  have ratio: "((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t)) \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) at_top"
    if supp: "1 + \<gamma> * x > 0" for x
  proof -
    have eq1: "\<forall>\<^sub>F t in at_top. (1 - F (t * (1 + \<gamma> * x))) / (1 - F t)
                 = (1 - F (t + x * f t)) / (1 - F t)"
      using eventually_ge_at_top[of "1::real"]
      by eventually_elim (simp add: f_def field_simps)
    have main: "((\<lambda>t. (1 - F (t * (1 + \<gamma> * x))) / (1 - F t))
                 \<longlongrightarrow> (1 + \<gamma> * x) powr (- (1 / \<gamma>))) at_top"
      using regularly_varying_lim[OF rv', of "1 + \<gamma> * x"] supp by simp
    thus ?thesis
      using Lim_transform_eventually[OF main eq1]
        ln_EVD_cdf_1[OF zero_less_one, of \<gamma> x 0] supp gamma
      by simp
  qed
  have "\<exists>f. (\<forall>t. 0 < f t) \<and> (\<forall>x. 1 + \<gamma> * x > 0 \<longrightarrow>
              ((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
                \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F))"
    using f_pos ratio endpoint_eq by (intro exI[of _ f]) simp
  thus "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
    using MDA_iff_divide_tail[OF F, of \<gamma>] by simp
qed

theorem MDA_regularly_varying_neg:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and gamma[arith]: "\<gamma> < 0"
  shows "domain_of_attraction F (EVD_cdf \<gamma> 0 1)
          \<longleftrightarrow> bdd_support F \<and>
              regularly_varying (\<lambda>s. 1 - F (x_star F - 1 / s)) (1 / \<gamma>)"
proof
  assume dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  obtain a where apos: "\<And>t. 0 < a t"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
          \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of \<gamma>] gamma by auto
  have bdd: "bdd_support F"
    by (rule tail_quantile_neg_bdd[OF F apos gamma quant])
  have gap_rv: "\<And>y. 0 < y \<Longrightarrow>
      ((\<lambda>t. (x_star F - tail_quantile F (t * y)) / (x_star F - tail_quantile F t))
         \<longlongrightarrow> y powr \<gamma>) at_top"
    by (rule tail_quantile_neg_ratio[OF F apos gamma quant])
  show "bdd_support F \<and> regularly_varying (\<lambda>s. 1 - F (x_star F - 1 / s)) (1 / \<gamma>)"
    using bdd tail_quantile_gap_ratio_neg_imp_tail_regularly_varying[OF F gamma bdd gap_rv]
    by blast
next
  assume rv: "bdd_support F \<and> regularly_varying (\<lambda>s. 1 - F (x_star F - 1 / s)) (1 / \<gamma>)"
  hence bdd: "bdd_support F"
    and rv': "regularly_varying (\<lambda>s. 1 - F (x_star F - 1 / s)) (1 / \<gamma>)"
    by auto
  have lim:"filterlim (\<lambda>t. 1 / (c - t)) at_top (at_left c)" for c :: real
  proof -
    have tendsto0: "((\<lambda>t. c - t) \<longlongrightarrow> 0) (at_left c)"
      by (auto intro!: tendsto_eq_intros)
    show ?thesis
      using filterlim_inverse_at_top[OF tendsto0 eventually_at_leftI[of "c - 1"]]
      by(auto simp: inverse_eq_divide)
  qed
  note Slim = lim[of "x_star F"]
  have endpoint_eq: "endpoint_filter F = at_left (x_star F)"
    using bdd by (simp add: endpoint_filter_def)
  define f where "f = (\<lambda>t::real. if t < x_star F then - \<gamma> * (x_star F - t) else 1)"
  have f_pos: "\<And>t. 0 < f t"
    unfolding f_def using gamma by (auto intro: mult_neg_pos)
  have ratio: "((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
                 \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F)"
    if supp: "1 + \<gamma> * x > 0" for x
  proof -
    have main: "((\<lambda>s. (1 - F (x_star F - 1 / (s * (1 / (1 + \<gamma> * x)))))
                    / (1 - F (x_star F - 1 / s))) \<longlongrightarrow> (1 / (1 + \<gamma> * x)) powr (1 / \<gamma>)) at_top"
      using regularly_varying_lim[OF rv', of "1 / (1 + \<gamma> * x)"] supp by simp
    have comp: "((\<lambda>t. (1 - F (x_star F - 1 / ((1 / (x_star F - t)) * (1 / (1 + \<gamma> * x)))))
                    / (1 - F (x_star F - 1 / (1 / (x_star F - t)))))
                  \<longlongrightarrow> (1 / (1 + \<gamma> * x)) powr (1 / \<gamma>)) (at_left (x_star F))"
      by (rule filterlim_compose[OF main Slim])
    have eq1: "\<forall>\<^sub>F t in at_left (x_star F).
                 (1 - F (x_star F - 1 / ((1 / (x_star F - t)) * (1 / (1 + \<gamma> * x)))))
                   / (1 - F (x_star F - 1 / (1 / (x_star F - t))))
               = (1 - F (t + x * f t)) / (1 - F t)"
    proof (rule eventually_at_leftI[of "x_star F - 1"])
      fix t
      assume "t \<in> {x_star F - 1<..<x_star F}"
      hence tlt: "t < x_star F"
        by simp
      have a1: "t + x * f t = x_star F - (x_star F - t) * (1 + \<gamma> * x)"
        using tlt by (simp add: f_def field_simps)
      have a2: "1 / (1 / (x_star F - t) * (1 / (1 + \<gamma> * x))) = (x_star F - t) * (1 + \<gamma> * x)"
        using tlt supp by (simp add: field_simps)
      have a3: "1 / (1 / (x_star F - t)) = x_star F - t"
        using tlt by simp
      show "(1 - F (x_star F - 1 / (1 / (x_star F - t) * (1 / (1 + \<gamma> * x)))))
              / (1 - F (x_star F - 1 / (1 / (x_star F - t))))
            = (1 - F (t + x * f t)) / (1 - F t)"
        unfolding a2 a3 a1 by simp
    qed simp
    have val_eq: "(1 / (1 + \<gamma> * x)) powr (1 / \<gamma>) = - ln (EVD_cdf \<gamma> 0 1 x)"
      using ln_EVD_cdf_1[OF zero_less_one, of \<gamma> x 0] supp gamma
      by (simp add: powr_divide powr_minus_divide)
    show ?thesis
      unfolding endpoint_eq
      using Lim_transform_eventually[OF comp eq1] val_eq
      by simp
  qed
  have "\<exists>f. (\<forall>t. 0 < f t) \<and> (\<forall>x. 1 + \<gamma> * x > 0 \<longrightarrow>
              ((\<lambda>t. (1 - F (t + x * f t)) / (1 - F t))
            \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 x)) (endpoint_filter F))"
    using f_pos ratio by (intro exI[of _ f]) simp
  thus "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
    using MDA_iff_divide_tail[OF F, of \<gamma>] by simp
qed

text \<open> Corollary 1.2.4 \<close>
lemma MDA_aux_fun_cong:
  fixes F a a' :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes a: "\<And>t. 0 < a t"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
           \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
    and equiv: "((\<lambda>t. a' t / a t) \<longlongrightarrow> 1) at_top"
    and x: "0 < x"
  shows "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a' t)
           \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
proof -
  have anz: "a t \<noteq> 0" for t
    using a[of t] by simp
  show ?thesis
    using equiv
    by(intro asymp_equiv_tendsto_transfer[OF _ quant[OF x]])
      (simp add: asymp_equivI' asymp_equiv_divide asymp_equiv_symI)
qed

lemma MDA_canonical_normalization:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  obtains a :: "real \<Rightarrow> real"
  where "\<And>t. 0 < a t"
    and "\<And>x. 0 < x \<Longrightarrow>
          ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
             \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
    and "\<And>x. (\<lambda>n. F (a (real n) * x + tail_quantile F (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 x"
proof -
  obtain a where apos: "\<And>t. 0 < a t"
    and quant: "\<And>x. 0 < x \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / a t)
           \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of \<gamma>] by auto
  have wit: "(\<lambda>n. F (a (real n) * x + tail_quantile F (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 x" for x
  proof (rule MDA_tail_quantile_witness[where b = "tail_quantile F", OF F apos zero_less_one])
    fix y :: real
    assume y: "0 < y"
    show "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
             \<longlongrightarrow> (if \<gamma> = 0 then 1 * ln y + 0 else 1 * (y powr \<gamma> - 1) / \<gamma> + 0)) at_top"
      using quant[OF y] by (cases "\<gamma> = 0") simp_all
  qed
  show thesis
    by (rule that[of a]) (use apos quant wit in blast)+
qed

lemma tail_quantile_pos_aux:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and gamma: "0 < \<gamma>"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
    and x: "0 < x"
  shows "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t) / (\<gamma> * tail_quantile F t))
           \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
proof -
  obtain a where apos: "\<And>t. 0 < a t"
    and quant0: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
           \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of \<gamma>] by auto
  have quant: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
           \<longlongrightarrow> (y powr \<gamma> - 1) / \<gamma>) at_top"
    using quant0 gamma by simp
  have pos: "\<forall>\<^sub>F t in at_top. 0 < tail_quantile F t"
    using tail_quantile_pos_at_top[OF F apos gamma quant]
    unfolding filterlim_at_top_dense by blast
  have gnz: "\<gamma> \<noteq> 0"
    using gamma by simp
  have "((\<lambda>t. (tail_quantile F (t * x) / tail_quantile F t - 1) / \<gamma>)
          \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
    by (intro tendsto_intros tail_quantile_pos_ratio[OF F apos gamma quant x] gnz)
  moreover have "\<forall>\<^sub>F t in at_top.
      (tail_quantile F (t * x) / tail_quantile F t - 1) / \<gamma>
        = (tail_quantile F (t * x) - tail_quantile F t) / (\<gamma> * tail_quantile F t)"
    using pos by eventually_elim (simp add: field_simps)
  ultimately show ?thesis
    by (rule Lim_transform_eventually)
qed

lemma tail_quantile_neg_gap:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and gamma: "\<gamma> < 0"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  shows tail_quantile_neg_bdd_support: "bdd_support F"
    and tail_quantile_neg_gap_pos: "\<forall>\<^sub>F t in at_top. 0 < x_star F - tail_quantile F t"
proof -
  have gnz: "\<gamma> \<noteq> 0"
    using gamma by simp
  obtain a where apos: "\<And>t. 0 < a t"
    and quant0: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
           \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of \<gamma>] by auto
  have quant: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
           \<longlongrightarrow> (y powr \<gamma> - 1) / \<gamma>) at_top"
    using quant0 gnz by simp
  show bdd: "bdd_support F"
    by (rule tail_quantile_neg_bdd[OF F apos gamma quant])
  obtain f where fpos: "\<And>t. 0 < f t"
    and flim: "\<And>y. 0 < 1 + \<gamma> * y \<Longrightarrow>
        ((\<lambda>t. (1 - F (t + y * f t)) / (1 - F t))
          \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 y)) (endpoint_filter F)"
    using dom MDA_iff_divide_tail[OF F, of \<gamma>] by auto
  have lim': "\<And>y. 0 < 1 + \<gamma> * (y - 0) / 1 \<Longrightarrow>
      ((\<lambda>t. (1 - F (t + (y - 0) * f t)) / (1 - F t))
       \<longlongrightarrow> - ln (EVD_cdf \<gamma> 0 1 y)) (endpoint_filter F)"
    using flim by simp
  have Flim: "(F \<longlongrightarrow> 1) (endpoint_filter F)"
    by (intro F_tendsto_1_endpoint_of_lim[OF F _ _ zero_less_one lim']) (use fpos in auto)
  have gap: "0 < x_star F - tail_quantile F t" if t1: "1 < t" for t
    using tail_quantile_lt_x_star[OF F bdd Flim t1] by simp
  show "\<forall>\<^sub>F t in at_top. 0 < x_star F - tail_quantile F t"
    using eventually_gt_at_top[of 1] by eventually_elim (rule gap)
qed

lemma tail_quantile_neg_aux:
  fixes F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes F: "right_continuous_mono F 0 1" and gamma: "\<gamma> < 0"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
    and x: "0 < x"
  shows "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t)
                 / (- \<gamma> * (x_star F - tail_quantile F t)))
           \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
proof -
  have gnz: "\<gamma> \<noteq> 0" and gnz': "- \<gamma> \<noteq> 0"
    using gamma by simp_all
  obtain a where apos: "\<And>t. 0 < a t"
    and quant0: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
           \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of \<gamma>] by auto
  have quant: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
           \<longlongrightarrow> (y powr \<gamma> - 1) / \<gamma>) at_top"
    using quant0 gnz by simp
  note gapev = tail_quantile_neg_gap_pos[OF F gamma dom]
  have "((\<lambda>t. (1 - (x_star F - tail_quantile F (t * x)) / (x_star F - tail_quantile F t))
               / (- \<gamma>))
          \<longlongrightarrow> (1 - x powr \<gamma>) / (- \<gamma>)) at_top"
    by (intro tendsto_divide tendsto_diff tendsto_const gnz'
              tail_quantile_neg_ratio[OF F apos gamma quant x])
  moreover have "(1 - x powr \<gamma>) / (- \<gamma>) = (x powr \<gamma> - 1) / \<gamma>"
    by (simp add: diff_divide_distrib)
  ultimately have "((\<lambda>t. (1 - (x_star F - tail_quantile F (t * x))
                              / (x_star F - tail_quantile F t)) / (- \<gamma>))
                     \<longlongrightarrow> (x powr \<gamma> - 1) / \<gamma>) at_top"
    by simp
  moreover have "\<forall>\<^sub>F t in at_top.
      (1 - (x_star F - tail_quantile F (t * x)) / (x_star F - tail_quantile F t)) / (- \<gamma>)
        = (tail_quantile F (t * x) - tail_quantile F t)
            / (- \<gamma> * (x_star F - tail_quantile F t))"
    using gapev
  proof eventually_elim
    case (elim t)
    hence ne: "x_star F - tail_quantile F t \<noteq> 0"
      by simp
    have "1 - (x_star F - tail_quantile F (t * x)) / (x_star F - tail_quantile F t)
          = (tail_quantile F (t * x) - tail_quantile F t) / (x_star F - tail_quantile F t)"
      using ne by (simp add: field_simps)
    thus ?case
      by (simp add: mult.commute)
  qed
  ultimately show ?thesis
    by (rule Lim_transform_eventually)
qed

theorem MDA_normalization_pos:
  fixes F :: "real \<Rightarrow> real" and \<gamma> x :: real
  assumes F: "right_continuous_mono F 0 1" and gamma: "0 < \<gamma>"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  shows "(\<lambda>n. F (tail_quantile F (real n) * x) ^ n)
         \<longlonglongrightarrow> (if 0 < x then exp (- (x powr - (1 / \<gamma>))) else 0)"
proof -
  have gnz: "\<gamma> \<noteq> 0"
    using gamma by simp
  obtain a where apos: "\<And>t. 0 < a t"
    and quant0: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
           \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of \<gamma>] by auto
  have quant: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
           \<longlongrightarrow> (y powr \<gamma> - 1) / \<gamma>) at_top"
    using quant0 gnz by simp
  define a' where "a' = (\<lambda>t. \<gamma> * max (tail_quantile F t) 1)"
  have a'pos: "\<And>t. 0 < a' t"
    using gamma by (simp add: a'_def)
  have Uev: "\<forall>\<^sub>F t in at_top. 1 \<le> tail_quantile F t"
    using tail_quantile_pos_at_top[OF F apos gamma quant]
    unfolding filterlim_at_top by blast
  have a'eq: "\<forall>\<^sub>F t in at_top. a' t = \<gamma> * tail_quantile F t"
    using Uev by eventually_elim (simp add: a'_def)
  have quant': "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a' t)
                   \<longlongrightarrow> (if \<gamma> = 0 then 1 * ln y + 0 else 1 * (y powr \<gamma> - 1) / \<gamma> + 0)) at_top"
    if y: "0 < y" for y
  proof -
    have "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / (\<gamma> * tail_quantile F t))
             \<longlongrightarrow> (y powr \<gamma> - 1) / \<gamma>) at_top"
      by (rule tail_quantile_pos_aux[OF F gamma dom y])
    moreover have "\<forall>\<^sub>F t in at_top.
        (tail_quantile F (t * y) - tail_quantile F t) / (\<gamma> * tail_quantile F t)
          = (tail_quantile F (t * y) - tail_quantile F t) / a' t"
      using a'eq by eventually_elim simp
    ultimately show ?thesis
      using gnz by (simp add: Lim_transform_eventually)
  qed
  have wit: "(\<lambda>n. F (a' (real n) * y + tail_quantile F (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 y" for y
    by (rule MDA_tail_quantile_witness[where b = "tail_quantile F",
             OF F a'pos zero_less_one quant'])
  have "\<forall>\<^sub>F n in sequentially.
      F (a' (real n) * ((x - 1) / \<gamma>) + tail_quantile F (real n)) ^ n
        = F (tail_quantile F (real n) * x) ^ n"
    using eventually_compose_filterlim[OF a'eq filterlim_real_sequentially]
    by eventually_elim (simp add: gnz field_simps)
  with wit[of "(x - 1) / \<gamma>"]
  have "(\<lambda>n. F (tail_quantile F (real n) * x) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 ((x - 1) / \<gamma>)"
    by (rule Lim_transform_eventually)
  thus ?thesis
    using gamma by (auto simp: EVD_cdf_def)
qed

theorem MDA_normalization_neg:
  fixes F :: "real \<Rightarrow> real" and \<gamma> x :: real
  assumes F: "right_continuous_mono F 0 1" and gamma: "\<gamma> < 0"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  shows "(\<lambda>n. F ((x_star F - tail_quantile F (real n)) * x + x_star F) ^ n)
           \<longlonglongrightarrow> (if x < 0 then exp (- ((- x) powr - (1 / \<gamma>))) else 1)"
proof -
  have gnz: "\<gamma> \<noteq> 0" and gpos: "0 < - \<gamma>"
    using gamma by simp_all
  note gapev = tail_quantile_neg_gap_pos[OF F gamma dom]
  define a' where
    "a' = (\<lambda>t. if 0 < x_star F - tail_quantile F t
               then - \<gamma> * (x_star F - tail_quantile F t) else 1)"
  have a'pos: "0 < a' t" for t
    using gamma by (auto simp: a'_def intro!: mult_neg_pos)
  have a'eq: "\<forall>\<^sub>F t in at_top. a' t = - \<gamma> * (x_star F - tail_quantile F t)"
    using gapev by eventually_elim (simp add: a'_def)
  have quant': "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a' t)
                   \<longlongrightarrow> (if \<gamma> = 0 then 1 * ln y + 0 else 1 * (y powr \<gamma> - 1) / \<gamma> + 0)) at_top"
    if y: "0 < y" for y
  proof -
    have "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t)
                  / (- \<gamma> * (x_star F - tail_quantile F t)))
             \<longlongrightarrow> (y powr \<gamma> - 1) / \<gamma>) at_top"
      by (rule tail_quantile_neg_aux[OF F gamma dom y])
    moreover have "\<forall>\<^sub>F t in at_top.
        (tail_quantile F (t * y) - tail_quantile F t) / (- \<gamma> * (x_star F - tail_quantile F t))
          = (tail_quantile F (t * y) - tail_quantile F t) / a' t"
      using a'eq by eventually_elim simp
    ultimately show ?thesis
      using gnz by (simp add: Lim_transform_eventually)
  qed
  have wit: "(\<lambda>n. F (a' (real n) * y + tail_quantile F (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 y"
    for y
    by (rule MDA_tail_quantile_witness[where b = "tail_quantile F",
             OF F a'pos zero_less_one quant'])
  have "\<forall>\<^sub>F n in sequentially.
      F (a' (real n) * (- (x + 1) / \<gamma>) + tail_quantile F (real n)) ^ n
        = F ((x_star F - tail_quantile F (real n)) * x + x_star F) ^ n"
    using eventually_compose_filterlim[OF a'eq filterlim_real_sequentially]
  proof eventually_elim
    case (elim n)
    have "a' (real n) * (- (x + 1) / \<gamma>) + tail_quantile F (real n)
          = (x_star F - tail_quantile F (real n)) * x + x_star F"
      unfolding elim using gnz by (simp add: field_simps)
    thus ?case
      by simp
  qed
  with wit[of "- (x + 1) / \<gamma>"]
  have "(\<lambda>n. F ((x_star F - tail_quantile F (real n)) * x + x_star F) ^ n)
          \<longlonglongrightarrow> EVD_cdf \<gamma> 0 1 (- (x + 1) / \<gamma>)"
    by (rule Lim_transform_eventually)
  thus ?thesis
    using gamma by(auto simp: EVD_cdf_def)
qed

lemma tail_quantile_spacing_aux:
  fixes F :: "real \<Rightarrow> real" and \<gamma> c :: real
  assumes F: "right_continuous_mono F 0 1"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
    and c: "1 < c" and x: "0 < x"
  shows "((\<lambda>t. (tail_quantile F (t * x) - tail_quantile F t)
                 / ((tail_quantile F (t * c) - tail_quantile F t)
                     / (if \<gamma> = 0 then ln c else (c powr \<gamma> - 1) / \<gamma>)))
           \<longlongrightarrow> (if \<gamma> = 0 then ln x else (x powr \<gamma> - 1) / \<gamma>)) at_top"
proof -
  have c0: "0 < c"
    using c by simp
  define D where "D = (if \<gamma> = 0 then ln c else (c powr \<gamma> - 1) / \<gamma>)"
  have D_pos: "0 < D"
    using powr_less_mono[of 0 \<gamma> c] powr_less_mono[of \<gamma> 0 c] c
    by(cases "\<gamma> = 0"; cases "0 < \<gamma>")
      (auto simp: D_def intro!: divide_pos_pos divide_neg_neg)
  obtain a where apos: "\<And>t. 0 < a t"
    and quant: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t)
           \<longlongrightarrow> (if \<gamma> = 0 then ln y else (y powr \<gamma> - 1) / \<gamma>)) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of \<gamma>] by auto
  have quantc: "((\<lambda>t. (tail_quantile F (t * c) - tail_quantile F t) / a t) \<longlongrightarrow> D) at_top"
    using quant[OF c0] by(simp add: D_def)
  define a' where "a' t = (tail_quantile F (t * c) - tail_quantile F t) / D" for t
  have equiv: "((\<lambda>t. a' t / a t) \<longlongrightarrow> 1) at_top"
  proof -
    have eq: "(tail_quantile F (t * c) - tail_quantile F t) / a t / D = a' t / a t" for t
      by(simp add: a'_def mult.commute)
    have "((\<lambda>t. (tail_quantile F (t * c) - tail_quantile F t) / a t / D) \<longlongrightarrow> D / D) at_top"
      using D_pos by(intro tendsto_divide[OF quantc tendsto_const]) simp
    thus ?thesis
      using D_pos unfolding eq by simp
  qed
  show ?thesis
    using MDA_aux_fun_cong[OF apos quant equiv x, unfolded a'_def D_def] .
qed

theorem MDA_normalization_zero_spacing:
  fixes F :: "real \<Rightarrow> real" and c x :: real
  assumes F: "right_continuous_mono F 0 1" and c: "1 < c"
    and dom: "domain_of_attraction F (EVD_cdf 0 0 1)"
  shows "(\<lambda>n. F ((tail_quantile F (real n * c) - tail_quantile F (real n)) / ln c * x
                 + tail_quantile F (real n)) ^ n)
           \<longlonglongrightarrow> EVD_cdf 0 0 1 x"
proof -
  have c0: "0 < c"
    using c by simp
  have lnc: "0 < ln c"
    using c by simp
  obtain a where apos: "\<And>t. 0 < a t"
    and quant: "\<And>y. 0 < y \<Longrightarrow>
        ((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a t) \<longlongrightarrow> ln y) at_top"
    using dom MDA_iff_tail_quantile'[OF F, of 0] by auto
  define a' where "a' t = (tail_quantile F (t * c) - tail_quantile F t) / ln c" for t
  have spacing: "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a' t) \<longlongrightarrow> ln y) at_top"
    if y: "0 < y" for y
    using tail_quantile_spacing_aux[OF F dom c y] by(simp add: a'_def)
  have ev: "\<forall>\<^sub>F t in at_top. 0 < a' t"
  proof(safe intro!: eventually_mono[OF order_tendstoD(1)[OF quant[OF c0] lnc]])
    fix t
    assume "0 < (tail_quantile F (t * c) - tail_quantile F t) / a t"
    thus "0 < a' t"
      using apos[of t] lnc by(simp add: a'_def zero_less_divide_iff)
  qed
  define a'' where "a'' t = (if 0 < a' t then a' t else 1)" for t
  have a''_pos: "0 < a'' t" for t
    by(simp add: a''_def)
  have a''_eq: "\<forall>\<^sub>F t in at_top. a'' t = a' t"
    using ev by eventually_elim (simp add: a''_def)
  have quant'': "((\<lambda>t. (tail_quantile F (t * y) - tail_quantile F t) / a'' t) \<longlongrightarrow> ln y) at_top"
    if y: "0 < y" for y
  proof -
    have "\<forall>\<^sub>F t in at_top. (tail_quantile F (t * y) - tail_quantile F t) / a' t
                            = (tail_quantile F (t * y) - tail_quantile F t) / a'' t"
      using a''_eq by eventually_elim simp
    from Lim_transform_eventually[OF spacing[OF y] this]
    show ?thesis .
  qed
  have wit: "(\<lambda>n. F (a'' (real n) * x + tail_quantile F (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf 0 0 1 x"
    by(intro MDA_tail_quantile_witness[where \<gamma> = 0 and \<mu> = 0 and \<sigma> = 1 and a = a''
                                         and b = "tail_quantile F", OF F a''_pos zero_less_one])
      (use quant'' in simp)
  have "\<forall>\<^sub>F n in sequentially.
      F (a'' (real n) * x + tail_quantile F (real n)) ^ n
        = F ((tail_quantile F (real n * c) - tail_quantile F (real n)) / ln c * x
              + tail_quantile F (real n)) ^ n"
    using eventually_compose_filterlim[OF a''_eq filterlim_real_sequentially]
    by eventually_elim (simp add: a'_def)
  with wit show ?thesis
    by (rule Lim_transform_eventually)
qed

end