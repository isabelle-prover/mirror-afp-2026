(*  Title:   Examples.thy
    Author:  Michikazu Hirata
*)
section \<open>Concrete Examples\label{sec:examples}\<close>
theory Examples
imports
   "Peaks_Over_Threshold"
begin

subsection \<open>Maximum of Random Variables\<close>
text \<open>In this subsection, we state results using i.i.d.\ random variables.\<close>

context prob_space
begin

lemma sample_max_measurable[measurable]:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "indep_vars (\<lambda>_::nat. borel) X UNIV"
  shows "(\<lambda>w. MAX i\<in>{..<n::nat}. X i w) \<in> borel_measurable M"
  using assms by (auto simp: indep_vars_def intro!: borel_measurable_Max)

lemma prob_sample_max_le:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes indep: "indep_vars (\<lambda>_. borel) X UNIV"
    and cdf: "\<And>i. cdf (distr M borel (X i)) = F"
    and n: "0 < n"
  shows "prob {w \<in> space M. (MAX i\<in>{..<n::nat}. X i w) \<le> x} = F x ^ n"
proof -
  have "prob {w \<in> space M. (MAX i\<in>{..<n::nat}. X i w) \<le> x}
        = prob {w \<in> space M. \<forall>i\<in>{..<n}. X i w \<le> x}"
    using n by(subst linorder_class.Max_le_iff) auto
  also have "... = prob (\<Inter>i\<in>{..<n::nat}. X i -` {..x} \<inter> space M)"
    using n by(intro arg_cong[where f=prob]) auto
  also have "... = (\<Prod>i\<in>{..<n::nat}. prob (X i -` {..x} \<inter> space M))"
    using n by(intro indep_varsD[OF indep]) auto
  also have "... = (\<Prod>i\<in>{..<n::nat}. cdf (distr M borel (X i)) x)"
    using indep by(simp add: cdf_def measure_distr indep_vars_def)
  also have "... = F x ^ n"
    by(simp add: cdf)
  finally show ?thesis .
qed

corollary cdf_distr_sample_max:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes indep: "indep_vars (\<lambda>_. borel) X UNIV"
    and cdf: "\<And>i. cdf (distr M borel (X i)) = F"
    and n: "0 < n"
  shows "cdf (distr M borel (\<lambda>w. (MAX i\<in>{..<n::nat}. X i w))) x = F x ^ n"
proof -
  have "cdf (distr M borel (\<lambda>w. (MAX i\<in>{..<n::nat}. X i w))) x
        = prob {w \<in> space M. (MAX i\<in>{..<n::nat}. X i w) \<le> x}"
    using indep by(auto simp: cdf_def measure_distr intro!: arg_cong[where f=prob])
  thus ?thesis
    by(simp add: prob_sample_max_le assms)
qed

corollary cdf_distr_sample_max_normalized:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and a b :: "nat \<Rightarrow> real"
  assumes indep: "indep_vars (\<lambda>_. borel) X UNIV"
    and cdf: "\<And>i. cdf (distr M borel (X i)) = F"
    and a: "\<And>n. 0 < a n"
    and n: "0 < n"
  shows "cdf (distr M borel (\<lambda>w. ((MAX i\<in>{..<n::nat}. X i w) - b n) / a n)) x
         = F (a n * x + b n) ^ n"
        (is "?lhs = _")
proof -
  have "?lhs = cdf (distr M borel (\<lambda>w. (MAX i\<in>{..<n::nat}. X i w))) (a n * x + b n)"
    using indep a
    by(auto simp: cdf_def measure_distr pos_divide_le_eq
        mult.commute intro!: arg_cong[where f=prob])
  thus ?thesis
    by(simp add: assms cdf_distr_sample_max)
qed

theorem Fisher_Tippett_Gnedenko_sample_max:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and a b :: "nat \<Rightarrow> real"
  assumes indep: "indep_vars (\<lambda>_. borel) X UNIV"
    and cdf: "\<And>i. cdf (distr M borel (X i)) = F"
    and N: "real_distribution N" and deg: "\<not> degenerate_df (cdf N)"
    and a: "\<And>n. 0 < a n"
    and wcm: "weak_conv_m (\<lambda>n. distr M borel (\<lambda>w. ((MAX i\<in>{..<n::nat}. X i w) - b n) / a n)) N"
  obtains \<gamma> \<mu> \<sigma> where "0 < \<sigma>" and "N = density lborel (EVD_density \<gamma> \<mu> \<sigma>)"
proof -
  interpret N: real_distribution N
    by fact
  have wc:"weak_conv (\<lambda>n x. F (a n * x + b n) ^ n) (cdf N)"
    unfolding weak_conv_def
  proof safe
    fix x
    assume x:"isCont (cdf N) x"
    show "(\<lambda>n. F (a n * x + b n) ^ n) \<longlonglongrightarrow> cdf N x"
      by(rule LIMSEQ_imp_Suc,
          subst cdf_distr_sample_max_normalized[where a=a,OF indep cdf a,symmetric])
        (use wcm x in "auto simp: weak_conv_m_def weak_conv_def dest: LIMSEQ_Suc")
  qed
  have "right_continuous_mono F 0 1"
    unfolding cdf[of 0,symmetric] using indep
    by(auto intro!: right_continuous_mono_cdf simp: indep_vars_def)
  from Fisher_Tippett_Gnedenko[OF this N.right_continuous_mono_axioms deg a wc]
  obtain \<gamma> \<mu> \<sigma> where "0 < \<sigma>" "cdf N = EVD_cdf \<gamma> \<mu> \<sigma>"
    by metis
  thus ?thesis
    by(auto intro!: cdf_unique that N real_distribution_EVD)
qed

end

subsection \<open>Excesses of a Random Variable over a High Threshold\<close>

context prob_space
begin

lemma prob_gt_pos_of_lt_x_star:
  fixes X :: "'a \<Rightarrow> real"
  assumes X[measurable]: "random_variable borel X"
    and cdf: "cdf (distr M borel X) = F"
    and u: "u < x_star F"
  shows "0 < prob {w \<in> space M. u < X w}"
proof -
  have F: "right_continuous_mono F 0 1"
    unfolding cdf[symmetric]
    by(auto intro!: right_continuous_mono_cdf)
  have "F u < 1"
    using F_lt_1_unbdd_support[OF F] lt_x_star_iff_F_lt_1[OF F, THEN iffD1, OF _ u]
    by(cases "bdd_support F") auto
  moreover have "prob {w \<in> space M. u < X w} = 1 - F u"
    unfolding cdf[symmetric]
    by(auto simp: cdf_def measure_distr prob_compl[symmetric] intro!: arg_cong[where f=prob])
  ultimately show ?thesis
    by simp
qed

lemma AE_le_x_star:
  fixes X :: "'a \<Rightarrow> real"
  assumes X[measurable]: "random_variable borel X"
    and cdf: "cdf (distr M borel X) = F"
    and bdd: "bdd_support F"
  shows "AE w in M. X w \<le> x_star F"
proof -
  have F: "right_continuous_mono F 0 1"
    unfolding cdf[symmetric]
    by(auto intro!: right_continuous_mono_cdf)
  have "prob {w \<in> space M. X w \<le> x_star F} = F (x_star F)"
    by(auto simp: cdf[symmetric] cdf_def measure_distr intro!: arg_cong[where f=prob])
  also have "... = 1"
    by(rule F_x_star_eq_1[OF F bdd])
  finally show ?thesis
    by(simp add: prob_Collect_eq_1)
qed

lemma cond_prob_excess_cdf:
  fixes X :: "'a \<Rightarrow> real"
  assumes X[measurable]: "random_variable borel X"
    and cdf: "cdf (distr M borel X) = F"
    and u: "F u < 1" and x:"0 \<le> x"
  shows "\<P>(w in M. X w - u \<le> x \<bar> u < X w) = excess_cdf F u x"
proof -
  have "\<P>(w in M. X w - u \<le> x \<bar> u < X w) =
         prob {\<omega> \<in> space M. X \<omega> - u \<le> x \<and> u < X \<omega>} / prob {\<omega> \<in> space M. u < X \<omega>}"
    by(simp add: cond_prob_def)
  also have "... = prob ({\<omega> \<in> space M. X \<omega> \<le> x + u} - {\<omega> \<in> space M. X \<omega> \<le> u})
                    / prob {\<omega> \<in> space M. u < X \<omega>}"
    by(auto intro!: arg_cong[where f=prob])
  also have "... = (prob {\<omega> \<in> space M. X \<omega> \<le> x + u}
                   - prob ({\<omega> \<in> space M. X \<omega> \<le> x + u} \<inter> {\<omega> \<in> space M. X \<omega> \<le> u}))
                 / prob {\<omega> \<in> space M. u < X \<omega>}"
    by(simp add: finite_measure_Diff')
  also have "... = (prob {\<omega> \<in> space M. X \<omega> \<le> x + u} - prob {\<omega> \<in> space M. X \<omega> \<le> u})
                    / prob {\<omega> \<in> space M. u < X \<omega>}"
    using x by(auto intro!: arg_cong[where f=prob])
  also have "... = (F (x + u) - F u) / prob {\<omega> \<in> space M. u < X \<omega>}"
    by(auto simp: cdf[symmetric] cdf_def measure_distr
        intro!: arg_cong2[OF arg_cong[where f=prob] arg_cong[where f=prob]])
  also have "... = (F (x + u) - F u) / (1 - F u)"
    by(auto simp: cdf[symmetric] cdf_def measure_distr prob_compl[symmetric]
        intro!: arg_cong[where f=prob])
  also have "... = excess_cdf F u x"
    using u by(simp add: excess_cdf_def2 add.commute)
  finally show ?thesis .
qed

lemma cdf_distr_excess:
  fixes X :: "'a \<Rightarrow> real"
  assumes X[measurable]: "random_variable borel X"
    and cdf: "cdf (distr M borel X) = F"
    and u: "F u < 1" and x:"0 \<le> x"
  shows "cdf (distr (uniform_measure M {w \<in> space M. u < X w}) borel (\<lambda>w. X w - u)) x
           = excess_cdf F u x" (is "?lhs = _")
proof -
  have "?lhs = \<P>(\<omega> in uniform_measure M {w \<in> space M. u < X w}. X \<omega> - u\<le> x)"
    by(auto simp: cdf_def measure_distr intro!: arg_cong[where f="measure _"])
  also have "... = \<P>(w in M. X w - u \<le> x \<bar> u < X w)"
    by(subst measure_uniform_measure_eq_cond_prob) auto
  also have "... = excess_cdf F u x"
    by(simp add: cond_prob_excess_cdf assms)
  finally show ?thesis .
qed

theorem Pickands_Balkema_de_Haan_cond_prob:
  fixes X :: "'a \<Rightarrow> real" and F :: "real \<Rightarrow> real" and \<gamma> :: real
  assumes X[measurable]: "random_variable borel X"
    and cdf: "cdf (distr M borel X) = F"
    and dom: "domain_of_attraction F (EVD_cdf \<gamma> 0 1)"
  obtains \<beta> :: "real \<Rightarrow> real"
  where "\<And>u. 0 < \<beta> u"
    and "uniform_limit {0..}
           (\<lambda>u x. \<P>(w in M. X w - u \<le> x \<bar> u < X w) - GPD_cdf \<gamma> 0 (\<beta> u) x)
           (\<lambda>x. 0) (endpoint_filter F)"
proof -
  have F:"right_continuous_mono F 0 1"
    unfolding cdf[symmetric]
    by(auto intro!: right_continuous_mono_cdf)
  from Pickands_Balkema_de_Haan[OF this] dom
  obtain \<beta> where h:"\<And>u. 0 < \<beta> u"
     "uniform_limit {0..} (\<lambda>u x. excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x) (\<lambda>x. 0)
                    (endpoint_filter F)"
    by blast
  have "\<forall>\<^sub>F u in endpoint_filter F. \<forall>x\<in>{0..}.
         \<P>(w in M. X w - u \<le> x \<bar> u < X w) - GPD_cdf \<gamma> 0 (\<beta> u) x
         = excess_cdf F u x - GPD_cdf \<gamma> 0 (\<beta> u) x"
    by(auto intro!: eventually_mono[OF F_lt_1_endpoint[OF F]] simp: cond_prob_excess_cdf assms)
  from h uniform_limit_cong[OF this] that
  show ?thesis
    by blast
qed

end

lemma excess_cdf_GPD:
  fixes \<gamma> \<sigma> u x :: real
  assumes sigma: "0 < \<sigma>" and u: "0 \<le> u" and supp: "0 < \<sigma> + \<gamma> * u" and x: "0 \<le> x"
  shows "excess_cdf (GPD_cdf \<gamma> 0 \<sigma>) u x = GPD_cdf \<gamma> 0 (\<sigma> + \<gamma> * u) x"
proof (cases "\<gamma> = 0")
  case True
  have "excess_cdf (GPD_cdf \<gamma> 0 \<sigma>) u x = 1 - exp (- ((u + x) / \<sigma>)) / exp (- (u / \<sigma>))"
    using True u x by (simp add: excess_cdf_def GPD_cdf_def[OF sigma])
  also have "... = 1 - exp (- (x / \<sigma>))"
    using sigma by (simp add: exp_diff[symmetric] field_simps)
  also have "... = GPD_cdf \<gamma> 0 (\<sigma> + \<gamma> * u) x"
    using True x by (simp add: GPD_cdf_def[OF sigma])
  finally show ?thesis .
next
  case \<gamma>0: False
  define s where "s = \<sigma> + \<gamma> * u"
  have s: "0 < s"
    using supp by (simp add: s_def)
  have ru: "1 + \<gamma> * (u / \<sigma>) = s / \<sigma>"
    using sigma by (simp add: s_def field_simps)
  have rx: "1 + \<gamma> * ((u + x) / \<sigma>) = (s + \<gamma> * x) / \<sigma>"
    using sigma by (simp add: s_def field_simps)
  have pu: "0 < s / \<sigma>"
    using s sigma by simp
  have cond_u: "- 1 \<le> \<gamma> * (u / \<sigma>)"
    using ru pu by linarith
  have tail_u: "1 - GPD_cdf \<gamma> 0 \<sigma> u = (s / \<sigma>) powr (- 1 / \<gamma>)"
    using u \<gamma>0 cond_u ru by (simp add: GPD_cdf_def[OF sigma] Let_def)
  show ?thesis
    unfolding s_def[symmetric]
  proof (cases "0 \<le> s + \<gamma> * x")
    case True
    have nn: "0 \<le> (s + \<gamma> * x) / \<sigma>"
      using True sigma by simp
    have cond_x: "- 1 \<le> \<gamma> * ((u + x) / \<sigma>)"
      using rx nn by linarith
    have tail_x: "1 - GPD_cdf \<gamma> 0 \<sigma> (u + x) = ((s + \<gamma> * x) / \<sigma>) powr (- 1 / \<gamma>)"
      using u x \<gamma>0 cond_x rx by (simp add: GPD_cdf_def[OF sigma] Let_def)
    have base: "(s + \<gamma> * x) / \<sigma> / (s / \<sigma>) = 1 + \<gamma> * (x / s)"
      using s sigma by (simp add: field_simps)
    have div: "((s + \<gamma> * x) / \<sigma>) powr (- 1 / \<gamma>) / (s / \<sigma>) powr (- 1 / \<gamma>)
                 = (1 + \<gamma> * (x / s)) powr (- 1 / \<gamma>)"
    proof -
      have "((s + \<gamma> * x) / \<sigma>) powr (- 1 / \<gamma>) / (s / \<sigma>) powr (- 1 / \<gamma>)
              = ((s + \<gamma> * x) / \<sigma> / (s / \<sigma>)) powr (- 1 / \<gamma>)"
        using nn pu by (intro powr_divide[symmetric])
      also have "... = (1 + \<gamma> * (x / s)) powr (- 1 / \<gamma>)"
        unfolding base ..
      finally show ?thesis .
    qed
    have "excess_cdf (GPD_cdf \<gamma> 0 \<sigma>) u x = 1 - (1 + \<gamma> * (x / s)) powr (- 1 / \<gamma>)"
      using tail_u tail_x div by (simp add: excess_cdf_def)
    also have "... = GPD_cdf \<gamma> 0 s x"
      using x \<gamma>0 True s by (simp add: GPD_cdf_def[OF s] Let_def field_simps)
    finally show "excess_cdf (GPD_cdf \<gamma> 0 \<sigma>) u x = GPD_cdf \<gamma> 0 s x" .
  next
    case False
    have neg: "(s + \<gamma> * x) / \<sigma> < 0"
      using False sigma by (simp add: divide_neg_pos)
    have cond_x: "\<not> - 1 \<le> \<gamma> * ((u + x) / \<sigma>)"
      using rx neg by linarith
    have "GPD_cdf \<gamma> 0 \<sigma> (u + x) = 1"
      using u x \<gamma>0 cond_x by (simp add: GPD_cdf_def[OF sigma] Let_def)
    hence "excess_cdf (GPD_cdf \<gamma> 0 \<sigma>) u x = 1"
      by (simp add: excess_cdf_def)
    also have "... = GPD_cdf \<gamma> 0 s x"
      using x \<gamma>0 False s by (simp add: GPD_cdf_def[OF s] Let_def field_simps)
    finally show "excess_cdf (GPD_cdf \<gamma> 0 \<sigma>) u x = GPD_cdf \<gamma> 0 s x" .
  qed
qed

corollary excess_cdf_exponential:
  fixes u x :: real
  assumes "0 \<le> u" and "0 \<le> x"
  shows "excess_cdf (GPD_cdf 0 0 1) u x = GPD_cdf 0 0 1 x"
  using excess_cdf_GPD[where \<gamma> = 0 and \<sigma> = 1 and u = u and x = x] assms by simp

corollary excess_cdf_Pareto1:
  fixes u x :: real
  assumes u: "1 \<le> u" and x: "0 \<le> x"
  shows "excess_cdf (GPD_cdf 1 1 1) u x = GPD_cdf 1 0 u x"
proof -
  have shift: "GPD_cdf 1 1 1 y = GPD_cdf 1 0 1 (y - 1)" for y
    by (simp add: GPD_cdf_def[OF zero_less_one] Let_def)
  have "excess_cdf (GPD_cdf 1 1 1) u x = excess_cdf (GPD_cdf 1 0 1) (u - 1) x"
    by (simp add: excess_cdf_def shift algebra_simps)
  also have "... = GPD_cdf 1 0 u x"
    using excess_cdf_GPD[where \<gamma> = 1 and \<sigma> = 1 and u = "u - 1" and x = x] u x by simp
  finally show ?thesis .
qed

corollary excess_cdf_uniform:
  fixes u x :: real
  assumes "0 \<le> u" and "u < 1" and "0 \<le> x"
  shows "excess_cdf (GPD_cdf (- 1) 0 1) u x = GPD_cdf (- 1) 0 (1 - u) x"
  using excess_cdf_GPD[where \<gamma> = "- 1" and \<sigma> = 1 and u = u and x = x] assms by simp

lemma excess_cdf_EVD_tendsto_GPD:
  fixes \<gamma> :: real
  obtains \<beta> :: "real \<Rightarrow> real"
  where "\<And>u. 0 < \<beta> u"
    and "uniform_limit {0..}
           (\<lambda>u x. excess_cdf (EVD_cdf \<gamma> 0 1) u x - GPD_cdf \<gamma> 0 (\<beta> u) x)
           (\<lambda>x. 0) (endpoint_filter (EVD_cdf \<gamma> 0 1))"
  using Pickands_Balkema_de_Haan[OF right_continuous_mono_EVD_cdf[OF zero_less_one], of \<gamma>]
        EVD_cdf_MDA[OF zero_less_one, of \<gamma> 0]
  by blast

corollary(in prob_space) cond_prob_excess_GPD:
  fixes X :: "'a \<Rightarrow> real" and \<gamma> \<sigma> u x :: real
  assumes X: "random_variable borel X"
    and X_cdf: "cdf (distr M borel X) = GPD_cdf \<gamma> 0 \<sigma>"
    and sigma: "0 < \<sigma>" and u: "0 \<le> u" and supp: "0 < \<sigma> + \<gamma> * u" and x: "0 \<le> x"
  shows "\<P>(w in M. X w - u \<le> x \<bar> u < X w) = GPD_cdf \<gamma> 0 (\<sigma> + \<gamma> * u) x"
proof -
  have lt1: "GPD_cdf \<gamma> 0 \<sigma> u < 1"
  proof (cases "\<gamma> = 0")
    case True
    thus ?thesis
      using u by (simp add: GPD_cdf_def[OF sigma])
  next
    case False
    have "0 < 1 + \<gamma> * (u / \<sigma>)"
      using supp sigma by (simp add: field_simps)
    thus ?thesis
      using u False by (simp add: GPD_cdf_def[OF sigma] Let_def)
  qed
  have "\<P>(w in M. X w - u \<le> x \<bar> u < X w) = excess_cdf (GPD_cdf \<gamma> 0 \<sigma>) u x"
    by (rule cond_prob_excess_cdf[OF X X_cdf lt1 x])
  also have "... = GPD_cdf \<gamma> 0 (\<sigma> + \<gamma> * u) x"
    by (rule excess_cdf_GPD[OF sigma u supp x])
  finally show ?thesis .
qed

subsection \<open>Domain of Attraction\<close>
text \<open>In this subsection we formalize concrete distributions, and determine the extreme value
      index $\gamma$ of the extreme value distribution they are attracted to.

      The results cover the following distributions, where $\mathcal{D}(G_\gamma)$ denotes
      @{const domain_of_attraction} for @{term "EVD_cdf \<gamma> 0 1"}.
      \begin{itemize}
      \item Normal distribution: $F_{\mathrm{N}} \in \mathcal{D}(G_{0})$.
      \item Erlang distribution: $F_{\mathrm{E}} \in \mathcal{D}(G_{0})$.
      \item Uniform distribution on an interval: $F_{\mathrm{U}} \in \mathcal{D}(G_{-1})$.
      \item Cauchy distribution: $F_{\mathrm{C}} \in \mathcal{D}(G_{1})$.
      \end{itemize}
      \<close>

subsubsection \<open>Normal Distribution\<close>
lemma real_distribution_normal:
  "0 < \<sigma> \<Longrightarrow> real_distribution (density lborel (normal_density \<mu> \<sigma>))"
  by(simp add: real_distribution_def real_distribution_axioms_def prob_space_normal_density)

lemma normal_density_affine_eq:
  assumes sigma: "0 < \<sigma>"
  shows "normal_density \<mu> \<sigma> (\<mu> + \<sigma> * y) = std_normal_density y / \<sigma>"
  using sigma
  by(simp add: normal_density_def real_sqrt_mult field_simps)

lemma std_normal_tail_measure:
  "1 - cdf std_normal_distribution t
     = enn2real (\<integral>\<^sup>+y\<in>{t..}. ennreal (std_normal_density y) \<partial>lborel)"
proof -
  interpret N: real_distribution std_normal_distribution
    by(rule real_distribution_normal) simp
  have "1 - cdf std_normal_distribution t = measure std_normal_distribution (UNIV - {..t})"
    using N.prob_compl[of "{..t}"] by(simp add: cdf_def)
  also have "... = measure std_normal_distribution {t<..}"
    by(rule arg_cong[where f="measure std_normal_distribution"]) auto
  also have "... = enn2real (\<integral>\<^sup>+y\<in>{t<..}. ennreal (std_normal_density y) \<partial>lborel)"
    by(simp add: measure_def emeasure_density)
  also have "... = enn2real (\<integral>\<^sup>+y\<in>{t..}. ennreal (std_normal_density y) \<partial>lborel)"
    by(intro arg_cong[where f=enn2real] nn_integral_cong_AE AE_I[where N="{t}"])
      (auto simp: indicator_def)
  finally show ?thesis .
qed

lemma DERIV_std_normal_density:
  "DERIV std_normal_density y :> - y * std_normal_density y"
  unfolding std_normal_density_def
  by(auto intro!: derivative_eq_intros simp: field_simps)

lemma DERIV_mills_upper:
  fixes y :: real
  assumes y: "0 < y"
  shows "DERIV (\<lambda>z. - (std_normal_density z / z)) y :> std_normal_density y * (1 + 1 / y\<^sup>2)"
  using y
  by(auto intro!: derivative_eq_intros DERIV_std_normal_density
      simp: field_simps power2_eq_square)

lemma DERIV_mills_lower:
  fixes y :: real
  assumes y: "0 < y"
  shows "DERIV (\<lambda>z. std_normal_density z / z ^ 3 - std_normal_density z / z) y
           :> std_normal_density y * (1 - 3 / y ^ 4)"
  using y
  by(auto intro!: derivative_eq_intros DERIV_std_normal_density
      simp: field_simps eval_nat_numeral)

lemma tendsto_mills_upper: "((\<lambda>z::real. - (std_normal_density z / z)) \<longlongrightarrow> 0) at_top"
  unfolding std_normal_density_def by real_asymp

lemma tendsto_mills_lower:
  "((\<lambda>z. std_normal_density z / z ^ 3 - std_normal_density z / z) \<longlongrightarrow> 0) at_top"
  unfolding std_normal_density_def by real_asymp

lemma std_normal_nn_integral_upper:
  fixes t :: real
  assumes t: "0 < t"
  shows "(\<integral>\<^sup>+y\<in>{t..}. ennreal (std_normal_density y * (1 + 1 / y\<^sup>2)) \<partial>lborel)
           = ennreal (std_normal_density t / t)"
proof -
  have "(\<integral>\<^sup>+y\<in>{t..}. ennreal (std_normal_density y * (1 + 1 / y\<^sup>2)) \<partial>lborel)
          = ennreal (0 - (- (std_normal_density t / t)))"
    by(rule nn_integral_FTC_atLeast[where F="\<lambda>z. - (std_normal_density z / z)"])
      (use t in \<open>auto intro!: DERIV_mills_upper tendsto_mills_upper\<close>)
  thus ?thesis
    by simp
qed

lemma std_normal_nn_integral_lower:
  fixes t :: real
  assumes t: "2 \<le> t"
  shows "(\<integral>\<^sup>+y\<in>{t..}. ennreal (std_normal_density y * (1 - 3 / y ^ 4)) \<partial>lborel)
           = ennreal (std_normal_density t / t - std_normal_density t / t ^ 3)"
proof -
  have nonneg: "0 \<le> std_normal_density x * (1 - 3 / x ^ 4)" if x: "t \<le> x" for x
  proof -
    have x2: "2 \<le> x"
      using t x by simp
    hence "(2::real) ^ 4 \<le> x ^ 4"
      by(intro power_mono) auto
    hence "3 / x ^ 4 \<le> 3 / 2 ^ 4"
      using x2 by(intro divide_left_mono) auto
    thus ?thesis
      by(intro mult_nonneg_nonneg normal_density_nonneg) simp
  qed
  have "(\<integral>\<^sup>+y\<in>{t..}. ennreal (std_normal_density y * (1 - 3 / y ^ 4)) \<partial>lborel)
          = ennreal (0 - (std_normal_density t / t ^ 3 - std_normal_density t / t))"
    by(rule nn_integral_FTC_atLeast
        [where F="\<lambda>z. std_normal_density z / z ^ 3 - std_normal_density z / z"])
      (use t nonneg in \<open>auto intro!: DERIV_mills_lower tendsto_mills_lower\<close>)
  thus ?thesis
    by simp
qed

lemma std_normal_tail_bounds:
  fixes t :: real
  assumes t: "2 \<le> t"
  shows std_normal_tail_upper: "1 - cdf std_normal_distribution t \<le> std_normal_density t / t"
    and std_normal_tail_lower:
      "std_normal_density t / t - std_normal_density t / t ^ 3
         \<le> 1 - cdf std_normal_distribution t"
proof -
  have t0: "0 < t"
    using t by simp
  have le: "std_normal_density y \<le> std_normal_density y * (1 + 1 / y\<^sup>2)" for y :: real
    using mult_left_mono[of 1 "1 + 1 / y\<^sup>2" "std_normal_density y"] by simp
  have up: "(\<integral>\<^sup>+y\<in>{t..}. ennreal (std_normal_density y) \<partial>lborel)
              \<le> ennreal (std_normal_density t / t)"
    unfolding std_normal_nn_integral_upper[OF t0, symmetric]
    by(intro nn_integral_mono mult_right_mono ennreal_leI le) simp
  have fin: "(\<integral>\<^sup>+y\<in>{t..}. ennreal (std_normal_density y) \<partial>lborel) < \<top>"
    using up ennreal_less_top by(rule le_less_trans)
  show "1 - cdf std_normal_distribution t \<le> std_normal_density t / t"
    unfolding std_normal_tail_measure
    using enn2real_mono[OF up] t0 by simp
  have cube: "std_normal_density t / t ^ 3 \<le> std_normal_density t / t"
    using t0 t power_increasing[of 1 3 t]
    by(intro divide_left_mono) auto
  have low: "ennreal (std_normal_density t / t - std_normal_density t / t ^ 3)
               \<le> (\<integral>\<^sup>+y\<in>{t..}. ennreal (std_normal_density y) \<partial>lborel)"
    unfolding std_normal_nn_integral_lower[OF t, symmetric]
    by(intro nn_integral_mono mult_right_mono ennreal_leI mult_left_le) auto
  show "std_normal_density t / t - std_normal_density t / t ^ 3
          \<le> 1 - cdf std_normal_distribution t"
    unfolding std_normal_tail_measure
    using enn2real_mono[OF low fin] cube t0 by simp
qed

lemma std_normal_tail_asymp_equiv:
  "(\<lambda>t. 1 - cdf std_normal_distribution t) \<sim>[at_top] (\<lambda>t. std_normal_density t / t)"
proof(rule asymp_equiv_symI[OF asymp_equiv_sandwich_real'
        [where l="\<lambda>t. std_normal_density t / t - std_normal_density t / t ^ 3"
           and u="\<lambda>t. std_normal_density t / t"]])
  show "(\<lambda>t. std_normal_density t / t)
          \<sim>[at_top] (\<lambda>t. std_normal_density t / t - std_normal_density t / t ^ 3)"
    unfolding std_normal_density_def
    by(rule asymp_equivI') real_asymp
next
  show "\<forall>\<^sub>F t in at_top. 1 - cdf std_normal_distribution t
          \<in> {std_normal_density t / t - std_normal_density t / t ^ 3..
              std_normal_density t / t}"
    by(intro eventually_mono[OF eventually_ge_at_top[of "2::real"]])
      (auto simp: std_normal_tail_upper std_normal_tail_lower)
qed simp

lemma std_normal_density_at_normalization:
  fixes x t :: real
  assumes t: "exp 1 < t"
  defines "c \<equiv> sqrt (2 * ln t)"
    and "w \<equiv> x - (ln (ln t) + ln (4 * pi)) / 2"
  shows "std_normal_density (c + w / c)
           = exp (- x) * c * exp (- (w\<^sup>2 / (4 * ln t))) / t"
proof -
  have tpos: "0 < t"
    using t exp_gt_zero[of 1] by linarith
  have lnt: "1 < ln t"
    using t tpos by(simp add: ln_less_cancel_iff[of "exp 1" t, symmetric])
  have cpos: "0 < c"
    using lnt by(simp add: c_def)
  have c2: "c\<^sup>2 = 2 * ln t"
    using lnt by(simp add: c_def)
  have usq: "(c + w / c)\<^sup>2 / 2 = ln t + w + w\<^sup>2 / (4 * ln t)"
  proof -
    have "(c + w / c)\<^sup>2 = c\<^sup>2 + 2 * w + w\<^sup>2 / c\<^sup>2"
      using cpos by(simp add: power2_eq_square field_simps)
    thus ?thesis
      unfolding c2 using lnt by(simp add: field_simps)
  qed
  have expd: "exp ((ln (ln t) + ln (4 * pi)) / 2) = sqrt (4 * pi * ln t)"
    using lnt
    by(intro real_sqrt_unique[symmetric]) (auto simp: power2_eq_square mult_exp_exp exp_add)
  have sq: "sqrt (4 * pi * ln t) = sqrt (2 * pi) * c"
    using lnt by(simp add: c_def real_sqrt_mult[symmetric])
  have expw: "exp (- w) = exp (- x) * sqrt (4 * pi * ln t)"
    unfolding w_def expd[symmetric] by(simp flip: exp_add)
  have "std_normal_density (c + w / c) = 1 / sqrt (2 * pi) * exp (- ((c + w / c)\<^sup>2 / 2))"
    by(simp add: std_normal_density_def)
  also have "... = 1 / sqrt (2 * pi) * exp (- (ln t + w + w\<^sup>2 / (4 * ln t)))"
    unfolding usq ..
  also have "... = 1 / sqrt (2 * pi) * (exp (- ln t) * exp (- w) * exp (- (w\<^sup>2 / (4 * ln t))))"
    by(simp flip: exp_add)
  also have "... = exp (- x) * c * exp (- (w\<^sup>2 / (4 * ln t))) / t"
    unfolding expw sq
    using tpos by(simp add: exp_minus field_simps)
  finally show ?thesis .
qed

lemma normal_cdf_location_scale:
  assumes sigma[arith]: "0 < \<sigma>"
  shows "cdf (density lborel (normal_density \<mu> \<sigma>)) x = cdf std_normal_distribution ((x - \<mu>) / \<sigma>)"
proof -
  have ind: "indicator {..x} (\<mu> + \<sigma> * y) = (indicator {..(x - \<mu>) / \<sigma>} y :: ennreal)" for y
    by(simp add: indicator_def field_simps)
  have "(\<integral>\<^sup>+y\<in>{..x}. ennreal (normal_density \<mu> \<sigma> y) \<partial>lborel)
        = ennreal \<bar>\<sigma>\<bar>
            * (\<integral>\<^sup>+y. ennreal (normal_density \<mu> \<sigma> (\<mu> + \<sigma> * y))
                       * indicator {..x} (\<mu> + \<sigma> * y) \<partial>lborel)"
    by(subst nn_integral_real_affine
        [where t=\<mu> and c=\<sigma> and f="\<lambda>y. ennreal (normal_density \<mu> \<sigma> y) * indicator {..x} y"])
      auto
  also have "... = (\<integral>\<^sup>+y. ennreal \<sigma>
                         * (ennreal (std_normal_density y / \<sigma>)
                             * indicator {..(x - \<mu>) / \<sigma>} y) \<partial>lborel)"
    by(subst nn_integral_cmult) (auto simp: normal_density_affine_eq ind)
  also have "... = (\<integral>\<^sup>+y\<in>{..(x - \<mu>) / \<sigma>}. ennreal (std_normal_density y) \<partial>lborel)"
    by(intro nn_integral_cong)
      (simp add: ennreal_mult'[symmetric] mult.assoc[symmetric])
  finally show ?thesis
    by(simp add: cdf_def measure_def emeasure_density)
qed

theorem std_normal_MDA: "domain_of_attraction (cdf std_normal_distribution) (EVD_cdf 0 0 1)"
proof -
  have F: "right_continuous_mono (cdf std_normal_distribution) 0 1"
    by(auto intro!: right_continuous_mono_cdf real_distribution_normal)
  have pos: "0 < std_normal_density t / t - std_normal_density t / t ^ 3" if t: "2 \<le> t" for t
  proof -
    have "std_normal_density t / t ^ 3 < std_normal_density t / t"
      using t normal_density_pos[where \<sigma>=1 and \<mu>=0 and x=t] power_strict_increasing[of 1 3 t]
      by(intro divide_strict_left_mono) auto
    thus ?thesis
      by simp
  qed
  have unbdd: "\<not> bdd_support (cdf std_normal_distribution)"
  proof(rule not_bdd_supportI)
    fix x :: real
    have s: "2 \<le> max x 2 + 1" "x < max x 2 + 1"
      by auto
    show "\<exists>y>x. cdf std_normal_distribution y < 1"
      using std_normal_tail_lower[OF s(1)] pos[OF s(1)] s by force
  qed
  have ep: "endpoint_filter (cdf std_normal_distribution) = at_top"
    using unbdd by(simp add: endpoint_filter_def)
  have lim: "((\<lambda>t. (1 - cdf std_normal_distribution (t + x * (1 / max t 1)))
                     / (1 - cdf std_normal_distribution t))
               \<longlongrightarrow> - ln (EVD_cdf 0 0 1 x)) at_top" for x
  proof -
    have shift: "filterlim (\<lambda>t::real. t + x / t) at_top at_top"
      by real_asymp
    have "(\<lambda>t. 1 - cdf std_normal_distribution (t + x / t))
            \<sim>[at_top] (\<lambda>t. std_normal_density (t + x / t) / (t + x / t))"
      by(intro asymp_equiv_compose'[OF std_normal_tail_asymp_equiv] shift)
    hence ae: "(\<lambda>t. (1 - cdf std_normal_distribution (t + x / t))
                      / (1 - cdf std_normal_distribution t))
                 \<sim>[at_top] (\<lambda>t. std_normal_density (t + x / t) / (t + x / t)
                                  / (std_normal_density t / t))"
      by(intro asymp_equiv_divide std_normal_tail_asymp_equiv)
    have lim2: "((\<lambda>t. std_normal_density (t + x / t) / (t + x / t)
                        / (std_normal_density t / t)) \<longlongrightarrow> exp (- x)) at_top"
      unfolding std_normal_density_def exp_minus inverse_eq_divide by real_asymp
    from tendsto_asymp_equiv_cong[OF ae] lim2
    have "((\<lambda>t. (1 - cdf std_normal_distribution (t + x / t))
                  / (1 - cdf std_normal_distribution t)) \<longlongrightarrow> exp (- x)) at_top"
      by simp
    moreover have "\<forall>\<^sub>F t in at_top.
        (1 - cdf std_normal_distribution (t + x / t)) / (1 - cdf std_normal_distribution t)
          = (1 - cdf std_normal_distribution (t + x * (1 / max t 1)))
              / (1 - cdf std_normal_distribution t)"
      by(intro eventually_mono[OF eventually_ge_at_top[of "1::real"]]) simp
    ultimately have "((\<lambda>t. (1 - cdf std_normal_distribution (t + x * (1 / max t 1)))
                             / (1 - cdf std_normal_distribution t)) \<longlongrightarrow> exp (- x)) at_top"
      by(rule Lim_transform_eventually)
    thus ?thesis
      by(simp add: EVD_cdf_def)
  qed
  show ?thesis
    unfolding MDA_iff_divide_tail[OF F] ep
    using lim by(auto intro!: exI[where x="\<lambda>t. 1 / max t 1"])
qed

corollary normal_MDA:
  assumes "0 < \<sigma>"
  shows "domain_of_attraction (cdf (density lborel (normal_density \<mu> \<sigma>))) (EVD_cdf 0 0 1)"
  unfolding normal_cdf_location_scale[OF assms]
  by(intro domain_of_attraction_affine assms std_normal_MDA)

theorem std_normal_normalization:
  fixes x :: real and a b :: "nat \<Rightarrow> real"
  defines "a \<equiv> \<lambda>n. 1 / sqrt (2 * ln (real n))"
    and "b \<equiv> \<lambda>n. sqrt (2 * ln (real n))
                   - (ln (ln (real n)) + ln (4 * pi)) / (2 * sqrt (2 * ln (real n)))"
  shows "(\<lambda>n. cdf std_normal_distribution (a n * x + b n) ^ n) \<longlonglongrightarrow> EVD_cdf 0 0 1 x"
proof -
  interpret N: real_distribution std_normal_distribution
    by(rule real_distribution_normal) simp
  define c where "c t = sqrt (2 * ln t)" for t :: real
  define w where "w t = x - (ln (ln t) + ln (4 * pi)) / 2" for t :: real
  define u where "u t = c t + w t / c t" for t :: real
  have u_top: "filterlim u at_top at_top"
    unfolding u_def c_def w_def by real_asymp
  have "(\<lambda>t. 1 - cdf std_normal_distribution (u t))
          \<sim>[at_top] (\<lambda>t. std_normal_density (u t) / u t)"
    by(intro asymp_equiv_compose'[OF std_normal_tail_asymp_equiv] u_top)
  hence ae: "(\<lambda>t. t * (1 - cdf std_normal_distribution (u t)))
               \<sim>[at_top] (\<lambda>t. t * (std_normal_density (u t) / u t))"
    by(intro asymp_equiv_mult asymp_equiv_refl)
  have ev: "\<forall>\<^sub>F t in at_top. t * (std_normal_density (u t) / u t)
                            = exp (- x) * (c t / u t) * exp (- ((w t)\<^sup>2 / (4 * ln t)))"
  proof(intro eventually_mono[OF eventually_gt_at_top[of "exp 1"]])
    fix t :: real
    assume t: "exp 1 < t"
    hence tpos: "0 < t"
      using exp_gt_zero[of 1] by linarith
    show "t * (std_normal_density (u t) / u t)
            = exp (- x) * (c t / u t) * exp (- ((w t)\<^sup>2 / (4 * ln t)))"
      unfolding u_def
      using std_normal_density_at_normalization[OF t, of x] tpos
      by(simp add: c_def w_def)
  qed
  have lim: "((\<lambda>t. exp (- x) * (c t / u t) * exp (- ((w t)\<^sup>2 / (4 * ln t)))) \<longlongrightarrow> exp (- x)) at_top"
    unfolding c_def w_def u_def by real_asymp
  have "(\<lambda>t. t * (1 - cdf std_normal_distribution (u t)))
          \<sim>[at_top] (\<lambda>t. exp (- x) * (c t / u t) * exp (- ((w t)\<^sup>2 / (4 * ln t))))"
    by(rule asymp_equiv_transfer[OF ae _ ev]) simp
  from tendsto_asymp_equiv_cong[OF this] lim
  have "((\<lambda>t. t * (1 - cdf std_normal_distribution (u t))) \<longlongrightarrow> exp (- x)) at_top"
    by simp
  hence tail: "(\<lambda>n. real n * (1 - cdf std_normal_distribution (u (real n)))) \<longlonglongrightarrow> exp (- x)"
    by(rule filterlim_compose[OF _ filterlim_real_sequentially])
  have "(\<lambda>n. cdf std_normal_distribution (u (real n)) ^ n) \<longlonglongrightarrow> EVD_cdf 0 0 1 x
          \<longleftrightarrow> (\<lambda>n. real n * (1 - cdf std_normal_distribution (u (real n))))
                \<longlonglongrightarrow> - ln (EVD_cdf 0 0 1 x)"
    by(intro power_tendsto_iff_tendsto_tail N.cdf_nonneg N.cdf_bounded_prob)
      (auto simp: EVD_cdf_def)
  moreover have "a n * x + b n = u (real n)" for n
    by(simp add: a_def b_def u_def c_def w_def diff_divide_distrib)
  ultimately show ?thesis
    using tail by(simp add: EVD_cdf_def)
qed

subsubsection \<open>Erlang Distribution\<close>
lemma cdf_erlang_density:
  assumes "0 < l"
  shows "cdf (density lborel (erlang_density k l)) = erlang_CDF k l"
  using assms
  by(auto simp: cdf_def measure_def emeasure_erlang_density)

corollary real_distribution_erlang:
  "0 < l \<Longrightarrow> real_distribution (density lborel (erlang_density k l))"
  by(simp add: real_distribution_def real_distribution_axioms_def prob_space_erlang_density)

lemma right_continuous_mono_erlang_CDF:
  assumes l: "0 < l"
  shows "right_continuous_mono (erlang_CDF k l) 0 1"
  using right_continuous_mono_cdf[OF real_distribution_erlang[OF l], of k]
  by(simp add: cdf_erlang_density[OF l])

lemma erlang_CDF_lt_1:
  assumes l[arith]: "0 < l"
  shows "erlang_CDF k l t < 1"
proof(cases "t < 0")
  case t: False
  have "0 < (\<Sum>n\<le>k. (l * t) ^ n * exp (- l * t) / fact n)"
    using t by(intro sum_pos2[where i=0]) auto
  thus ?thesis
    using t by(simp add: erlang_CDF_def)
qed(simp add: erlang_CDF_def)

lemma erlang_density_pos:
  assumes "0 < l" and "0 < x"
  shows "0 < erlang_density k l x"
  using assms by(simp add: erlang_density_def)

lemma DERIV_erlang_sum:
  fixes x :: real
  shows "((\<lambda>y. - (\<Sum>n\<le>k. y ^ n * exp (- y) / fact n)) has_real_derivative
            x ^ k * exp (- x) / fact k) (at x)"
proof(induction k)
  case 0
  show ?case
    by(auto intro!: derivative_eq_intros)
next
  case (Suc k)
  have "((\<lambda>y. - (\<Sum>n\<le>k. y ^ n * exp (- y) / fact n) - y ^ Suc k * exp (- y) / fact (Suc k))
           has_real_derivative
             x ^ k * exp (- x) / fact k
               - (real (Suc k) - x) * x ^ k * exp (- x) / fact (Suc k)) (at x)"
    by(intro DERIV_diff Suc)
      (auto intro!: derivative_eq_intros simp del: fact_Suc power_Suc
        simp add: field_simps power_Suc[symmetric])
  moreover have "x ^ k * exp (- x) / fact k
                   - (real (Suc k) - x) * x ^ k * exp (- x) / fact (Suc k)
                 = x ^ Suc k * exp (- x) / fact (Suc k)"
    by(auto simp: field_simps simp del: fact_Suc) (simp_all add: field_simps)
  ultimately show ?case
    by simp
qed

lemma DERIV_erlang_CDF_1:
  fixes t :: real
  assumes t: "0 < t"
  shows "(erlang_CDF k 1 has_real_derivative erlang_density k 1 t) (at t)"
proof -
  have op: "\<forall>\<^sub>F y in nhds t. y \<in> {0<..}"
    using t by(intro eventually_nhds_in_open) auto
  have ev: "\<forall>\<^sub>F y in nhds t. erlang_CDF k 1 y = 1 + - (\<Sum>n\<le>k. y ^ n * exp (- y) / fact n)"
    using op by eventually_elim (simp add: erlang_CDF_def)
  have "((\<lambda>y. 1 + - (\<Sum>n\<le>k. y ^ n * exp (- y) / fact n)) has_real_derivative
           0 + t ^ k * exp (- t) / fact k) (at t)"
    by(intro DERIV_add DERIV_const DERIV_erlang_sum)
  hence "((\<lambda>y. 1 + - (\<Sum>n\<le>k. y ^ n * exp (- y) / fact n)) has_real_derivative
           erlang_density k 1 t) (at t)"
    using t by(simp add: erlang_density_def)
  thus ?thesis
    using DERIV_cong_ev[OF refl ev refl] by simp
qed

lemma DERIV_erlang_CDF:
  fixes t :: real
  assumes l: "0 < l" and t: "0 < t"
  shows "(erlang_CDF k l has_real_derivative erlang_density k l t) (at t)"
proof -
  have eq: "erlang_CDF k l = (\<lambda>a. erlang_CDF k 1 (l * a))"
    by(rule ext) (rule erlang_CDF_transform[OF l])
  have "((\<lambda>a. erlang_CDF k 1 (l * a)) has_real_derivative
           erlang_density k 1 (l * t) * l) (at t)"
    using l t
    by(intro DERIV_chain2[OF DERIV_erlang_CDF_1]) (auto intro!: derivative_eq_intros)
  moreover have "erlang_density k 1 (l * t) * l = erlang_density k l t"
    using l t by(simp add: erlang_density_def mult_less_0_iff field_simps)
  ultimately show ?thesis
    unfolding eq by simp
qed

lemma DERIV_erlang_density:
  fixes t :: real
  assumes t: "0 < t"
  shows "(erlang_density k l has_real_derivative
            erlang_density k l t * (real k / t - l)) (at t)"
proof -
  have op: "\<forall>\<^sub>F y in nhds t. y \<in> {0<..}"
    using t by(intro eventually_nhds_in_open) auto
  have ev: "\<forall>\<^sub>F y in nhds t. erlang_density k l y = l ^ Suc k * y ^ k * exp (- l * y) / fact k"
    using op by eventually_elim (simp add: erlang_density_def)
  have pow: "real k * t ^ (k - Suc 0) = real k * t ^ k / t"
    by(cases k) (use t in simp_all)
  have "((\<lambda>y. l ^ Suc k * y ^ k * exp (- l * y) / fact k) has_real_derivative
           l ^ Suc k * (real k * t ^ (k - Suc 0) - l * t ^ k) * exp (- l * t) / fact k) (at t)"
    by(auto intro!: derivative_eq_intros simp: field_simps)
  moreover have "l ^ Suc k * (real k * t ^ (k - Suc 0) - l * t ^ k) * exp (- l * t) / fact k
                 = erlang_density k l t * (real k / t - l)"
    unfolding pow using t by(simp add: erlang_density_def field_simps)
  ultimately show ?thesis
    using DERIV_cong_ev[OF refl ev refl] by simp
qed

lemma continuous_on_erlang_density: "continuous_on {0<..} (erlang_density k l)"
proof -
  have eq: "continuous_on {0<..} (erlang_density k l)
              = continuous_on {0<..} (\<lambda>x. l ^ Suc k * x ^ k * exp (- l * x) / fact k)"
    by(intro continuous_on_cong refl) (simp add: erlang_density_def)
  show ?thesis
    unfolding eq by(intro continuous_intros) auto
qed

lemma erlang_tail_ratio:
  fixes t :: real
  assumes l: "0 < l" and t: "0 < t"
  shows "(1 - erlang_CDF k l t) / ((l * t) ^ k * exp (- l * t) / fact k)
           = (\<Sum>n\<le>k. fact k / fact n / (l * t) ^ (k - n))"
proof -
  have lt: "0 < l * t"
    using l t by simp
  have tail: "1 - erlang_CDF k l t = (\<Sum>n\<le>k. (l * t) ^ n * exp (- l * t) / fact n)"
    using t by(simp add: erlang_CDF_def)
  have "(1 - erlang_CDF k l t) / ((l * t) ^ k * exp (- l * t) / fact k)
        = (\<Sum>n\<le>k. ((l * t) ^ n * exp (- l * t) / fact n)
                     / ((l * t) ^ k * exp (- l * t) / fact k))"
    unfolding tail by(rule sum_divide_distrib)
  also have "... = (\<Sum>n\<le>k. fact k / fact n / (l * t) ^ (k - n))"
  proof(intro sum.cong refl)
    fix n :: nat
    assume "n \<in> {..k}"
    hence n: "n \<le> k"
      by simp
    have pow: "(l * t) ^ n * (l * t) ^ (k - n) = (l * t) ^ k"
      using n by(simp flip: power_add)
    have nz: "l \<noteq> 0" "t \<noteq> 0"
      using l t by auto
    show "((l * t) ^ n * exp (- l * t) / fact n) / ((l * t) ^ k * exp (- l * t) / fact k)
           = fact k / fact n / (l * t) ^ (k - n)"
      unfolding pow[symmetric]
      using nz by(simp add: field_simps)
  qed
  finally show ?thesis .
qed

lemma erlang_tail_asymp_equiv:
  assumes l[arith]: "0 < l"
  shows "(\<lambda>t. 1 - erlang_CDF k l t) \<sim>[at_top] (\<lambda>t. (l * t) ^ k * exp (- l * t) / fact k)"
proof(rule asymp_equivI')
  have lt: "filterlim (\<lambda>t::real. l * t) at_top at_top"
    using l by real_asymp
  have lim: "((\<lambda>t. \<Sum>n\<le>k. fact k / fact n / (l * t) ^ (k - n)) \<longlongrightarrow> 1) at_top"
  proof -
    have "((\<lambda>t. \<Sum>n\<le>k. fact k / fact n / (l * t) ^ (k - n))
             \<longlongrightarrow> (\<Sum>n\<le>k. if n = k then 1 else 0)) at_top"
    proof(intro tendsto_sum)
      fix n :: nat
      assume "n \<in> {..k}"
      hence n: "n \<le> k"
        by simp
      show "((\<lambda>t. fact k / fact n / (l * t) ^ (k - n)) \<longlongrightarrow> (if n = k then 1 else 0)) at_top"
      proof(cases "n = k")
        case False
        hence "0 < k - n"
          using n by simp
        from real_tendsto_divide_at_top[OF tendsto_const filterlim_pow_at_top[OF this lt]]
        show ?thesis
          by(simp add: False del: divide_divide_eq_left)
      qed simp
    qed
    thus ?thesis
      by simp
  qed
  have ev: "\<forall>\<^sub>F t in at_top. (\<Sum>n\<le>k. fact k / fact n / (l * t) ^ (k - n))
                            = (1 - erlang_CDF k l t) / ((l * t) ^ k * exp (- l * t) / fact k)"
    by(intro eventually_mono[OF eventually_gt_at_top[of "0::real"]]
        erlang_tail_ratio[OF l, symmetric]) simp
  from Lim_transform_eventually[OF lim ev]
  show "((\<lambda>t. (1 - erlang_CDF k l t) / ((l * t) ^ k * exp (- l * t) / fact k))
          \<longlongrightarrow> 1) at_top" .
qed

lemma erlang_von_Mises_ratio:
  fixes t :: real
  assumes l: "0 < l" and t: "0 < t"
  shows "((l * t) ^ k * exp (- l * t) / fact k)
           * (erlang_density k l t * (real k / t - l)) / (erlang_density k l t)\<^sup>2
         = (real k / t - l) / l"
proof -
  have g0: "(l * t) ^ k * exp (- l * t) / fact k \<noteq> 0"
    using l t by simp
  have f: "erlang_density k l t = l * ((l * t) ^ k * exp (- l * t) / fact k)"
    using l t by(simp add: erlang_density_def field_simps)
  show ?thesis
    unfolding f using g0 l by(simp add: power2_eq_square field_simps)
qed

text \<open>The Erlang distribution is our example of von Mises' condition. Note that the
      characterization by regular variation is available only for $\gamma > 0$, so for
      $\gamma = 0$ the condition on the density is the natural tool.\<close>

theorem erlang_MDA:
  assumes l: "0 < l"
  shows "domain_of_attraction (erlang_CDF k l) (EVD_cdf 0 0 1)"
proof -
  define f' where "f' = (\<lambda>y::real. erlang_density k l y * (real k / y - l))"
  note F = right_continuous_mono_erlang_CDF[OF l]
  have unbdd: "\<not> bdd_support (erlang_CDF k l)"
    by(rule not_bdd_supportI') (rule erlang_CDF_lt_1[OF l])
  have ep: "endpoint_filter (erlang_CDF k l) = at_top"
    using unbdd by(simp add: endpoint_filter)
  have Flim: "(erlang_CDF k l \<longlongrightarrow> 1) (endpoint_filter (erlang_CDF k l))"
    using right_continuous_mono.top[OF F] unbdd by(simp add: endpoint_filter)
  have set_eq: "{y. 0 < y \<and> erlang_CDF k l y < 1} = {0<..}"
    using erlang_CDF_lt_1[OF l] by auto
  have cont: "continuous_on {y. 0 < y \<and> erlang_CDF k l y < 1} f'"
    unfolding set_eq f'_def
    by(intro continuous_intros continuous_on_erlang_density) auto
  have lim: "((\<lambda>y. (1 - erlang_CDF k l y) * f' y / (erlang_density k l y)\<^sup>2)
               \<longlongrightarrow> - 0 - 1) (endpoint_filter (erlang_CDF k l))"
  proof -
    have ae: "(\<lambda>t. (1 - erlang_CDF k l t) * f' t / (erlang_density k l t)\<^sup>2)
                \<sim>[at_top] (\<lambda>t. ((l * t) ^ k * exp (- l * t) / fact k) * f' t
                                 / (erlang_density k l t)\<^sup>2)"
      by(intro asymp_equiv_divide asymp_equiv_mult erlang_tail_asymp_equiv[OF l]
          asymp_equiv_refl)
    have ev: "\<forall>\<^sub>F t in at_top. ((l * t) ^ k * exp (- l * t) / fact k) * f' t
                                 / (erlang_density k l t)\<^sup>2
                              = (real k / t - l) / l"
      unfolding f'_def
      by(intro eventually_mono[OF eventually_gt_at_top[of "0::real"]]
          erlang_von_Mises_ratio[OF l])
    have ae': "(\<lambda>t. (1 - erlang_CDF k l t) * f' t / (erlang_density k l t)\<^sup>2)
                 \<sim>[at_top] (\<lambda>t. (real k / t - l) / l)"
      by(rule asymp_equiv_transfer[OF ae _ ev]) simp
    have "((\<lambda>t. (real k / t - l) / l) \<longlongrightarrow> - 0 - 1) at_top"
      using l by real_asymp
    with tendsto_asymp_equiv_cong[OF ae'] show ?thesis
      unfolding ep by simp
  qed
  show ?thesis
    by(rule von_Mises_condition[OF F _ Flim _ _ _ cont lim])
      (use erlang_CDF_lt_1[OF l] DERIV_erlang_CDF[OF l] DERIV_erlang_density
        erlang_density_pos[OF l] in \<open>auto simp: f'_def\<close>)
qed

theorem erlang_normalization:
  fixes x :: real
  assumes l[arith]: "0 < l"
  shows "(\<lambda>n. erlang_CDF k l
                ((x + ln (real n) + real k * ln (ln (real n)) - ln (fact k)) / l) ^ n)
         \<longlonglongrightarrow> EVD_cdf 0 0 1 x"
proof -
  have lnz: "l \<noteq> 0"
    using l by simp
  define A where "A t = x + ln t + real k * ln (ln t) - ln (fact k)" for t :: real
  have A_top: "filterlim A at_top at_top"
    unfolding A_def by real_asymp
  have b_top: "filterlim (\<lambda>t. A t / l) at_top at_top"
    using filterlim_tendsto_pos_mult_at_top[OF tendsto_const _ A_top, of "1 / l"]
    by(simp add: field_simps)
  have ratio: "((\<lambda>t. A t / ln t) \<longlongrightarrow> 1) at_top"
    unfolding A_def by real_asymp
  have "(\<lambda>t. 1 - erlang_CDF k l (A t / l))
          \<sim>[at_top] (\<lambda>t. (l * (A t / l)) ^ k * exp (- l * (A t / l)) / fact k)"
    by(intro asymp_equiv_compose'[OF erlang_tail_asymp_equiv[OF l]] b_top)
  hence ae: "(\<lambda>t. t * (1 - erlang_CDF k l (A t / l)))
               \<sim>[at_top] (\<lambda>t. t * ((l * (A t / l)) ^ k * exp (- l * (A t / l)) / fact k))"
    by(intro asymp_equiv_mult asymp_equiv_refl)
  have ev: "\<forall>\<^sub>F t in at_top.
      t * ((l * (A t / l)) ^ k * exp (- l * (A t / l)) / fact k)
        = exp (- x) * (A t / ln t) ^ k"
  proof(intro eventually_mono[OF eventually_gt_at_top[of "exp 1"]])
    fix t :: real
    assume t: "exp 1 < t"
    hence tpos: "0 < t"
      using exp_gt_zero[of 1] by linarith
    have lnt: "1 < ln t"
      using t tpos by(simp add: ln_less_cancel_iff[of "exp 1" t, symmetric])
    have elnln: "exp (ln (ln t)) = ln t"
      using lnt by simp
    have expA: "exp (A t) = exp x * t * ln t ^ k / fact k"
      unfolding A_def
      using tpos by(simp add: exp_add exp_diff exp_of_nat_mult elnln)
    have "t * ((l * (A t / l)) ^ k * exp (- l * (A t / l)) / fact k)
            = t * (A t ^ k / (fact k * exp (A t)))"
      using lnz by(simp add: exp_minus field_simps)
    also have "... = exp (- x) * (A t / ln t) ^ k"
      unfolding expA
      using tpos lnt by(simp add: exp_minus field_simps)
    finally show "t * ((l * (A t / l)) ^ k * exp (- l * (A t / l)) / fact k)
                    = exp (- x) * (A t / ln t) ^ k" .
  qed
  from tendsto_mult[OF tendsto_const tendsto_power[OF ratio, of k], of "exp (- x)"]
  have lim: "((\<lambda>t. exp (- x) * (A t / ln t) ^ k) \<longlongrightarrow> exp (- x)) at_top"
    by simp
  have "(\<lambda>t. t * (1 - erlang_CDF k l (A t / l))) \<sim>[at_top] (\<lambda>t. exp (- x) * (A t / ln t) ^ k)"
    by(rule asymp_equiv_transfer[OF ae _ ev]) simp
  from tendsto_asymp_equiv_cong[OF this] lim
  have "((\<lambda>t. t * (1 - erlang_CDF k l (A t / l))) \<longlongrightarrow> exp (- x)) at_top"
    by simp
  hence tail: "(\<lambda>n. real n * (1 - erlang_CDF k l (A (real n) / l))) \<longlonglongrightarrow> exp (- x)"
    by(rule filterlim_compose[OF _ filterlim_real_sequentially])
  have "(\<lambda>n. erlang_CDF k l (A (real n) / l) ^ n) \<longlonglongrightarrow> EVD_cdf 0 0 1 x
          \<longleftrightarrow> (\<lambda>n. real n * (1 - erlang_CDF k l (A (real n) / l)))
                \<longlonglongrightarrow> - ln (EVD_cdf 0 0 1 x)"
    by(intro power_tendsto_iff_tendsto_tail erlang_CDF_nonneg[OF l]
        less_imp_le[OF erlang_CDF_lt_1[OF l]]) (auto simp: EVD_cdf_def)
  thus ?thesis
    using tail by(simp add: A_def EVD_cdf_def)
qed

subsubsection \<open>Uniform Distribution\<close>
lemma uniform_cdf_eq_GPD:
  fixes a b :: real
  assumes [arith]:"a < b"
  shows "cdf (uniform_measure lborel {a..b}) = GPD_cdf (- 1) a (b - a)"
proof
  fix x
  have *:"a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> \<bar>1 + (a - x) / (b - a)\<bar> = 1 + (a - x) / (b - a)"
    by (smt (verit, best) less_divide_eq_1_pos minus_divide_left)
  have "cdf (uniform_measure lborel {a..b}) x =
        (if a \<le> x \<and> x \<le> b then (x - a) / (b - a)
         else if b < x then 1 else 0)"
    by(auto simp: cdf_def)
  also have "... = GPD_cdf (- 1) a (b - a) x"
    using * by(auto simp: GPD_cdf_def minus_divide_left)
  finally show "cdf (uniform_measure lborel {a..b}) x = GPD_cdf (- 1) a (b - a) x" .
qed

theorem uniform_MDA:
  fixes a b :: real
  assumes "a < b"
  shows "domain_of_attraction (cdf (uniform_measure lborel {a..b})) (EVD_cdf (- 1) 0 1)"
  by (simp add: GPD_cdf_MDA assms uniform_cdf_eq_GPD)

subsubsection \<open>Cauchy Distribution\<close>
definition Cauchy_density :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"Cauchy_density \<mu> \<sigma> x \<equiv> \<sigma> / (pi * (\<sigma>\<^sup>2 + (x - \<mu>)\<^sup>2))"

abbreviation std_Cauchy_density :: "real \<Rightarrow> real" where
"std_Cauchy_density \<equiv> Cauchy_density 0 1"

abbreviation std_Cauchy_distribution :: "real measure" where
"std_Cauchy_distribution \<equiv> density lborel std_Cauchy_density"

lemma std_Cauchy_density_def: "std_Cauchy_density x = 1 / (pi * (1 + x\<^sup>2))"
  by(simp add: Cauchy_density_def)

lemma Cauchy_density_nonneg[simp]: "0 < \<sigma> \<Longrightarrow> 0 \<le> Cauchy_density \<mu> \<sigma> x"
  by(simp add: Cauchy_density_def)

lemma Cauchy_density_measurable[measurable]:
  "Cauchy_density \<mu> \<sigma> \<in> borel_measurable borel"
  unfolding Cauchy_density_def by measurable

lemma Cauchy_density_uminus: "Cauchy_density \<mu> \<sigma> (- x) = Cauchy_density (- \<mu>) \<sigma> x"
  by(simp add: Cauchy_density_def power2_eq_square algebra_simps)

lemma arctan_div_pi_bounds:
  shows arctan_div_pi_pos: "0 < 1 / 2 + arctan z / pi"
    and arctan_div_pi_lt_1: "1 / 2 + arctan z / pi < 1"
  using arctan_lbound[of z] arctan_ubound[of z] pi_gt_zero
  by(auto simp: field_simps)

lemma DERIV_Cauchy_cdf:
  assumes sigma[arith]: "0 < \<sigma>"
  shows "DERIV (\<lambda>y. arctan ((y - \<mu>) / \<sigma>) / pi) x :> Cauchy_density \<mu> \<sigma> x"
proof -
  have ne: "\<sigma>\<^sup>2 + (x - \<mu>)\<^sup>2 \<noteq> 0"
    using add_pos_nonneg[of "\<sigma>\<^sup>2" "(x - \<mu>)\<^sup>2"] by simp
  have sq: "1 + ((x - \<mu>) / \<sigma>)\<^sup>2 = (\<sigma>\<^sup>2 + (x - \<mu>)\<^sup>2) / \<sigma>\<^sup>2"
    by(simp add: field_simps)
  have eq: "1 / (1 + ((x - \<mu>) / \<sigma>)\<^sup>2) * (1 / \<sigma>) / pi = Cauchy_density \<mu> \<sigma> x"
    unfolding sq Cauchy_density_def
    using ne by(simp add: field_simps power2_eq_square)
  show ?thesis
    unfolding eq[symmetric]
    by(auto intro!: derivative_eq_intros simp: inverse_eq_divide)
qed

lemma Cauchy_nn_integral_atLeast:
  assumes sigma[arith]: "0 < \<sigma>"
  shows "(\<integral>\<^sup>+y\<in>{x..}. Cauchy_density \<mu> \<sigma> y \<partial>lborel)
          = ennreal (1 / 2 - arctan ((x - \<mu>) / \<sigma>) / pi)"
proof -
  have "((\<lambda>y. arctan ((y - \<mu>) / \<sigma>) / pi) \<longlongrightarrow> pi / 2 / pi) at_top"
    using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of "1 / \<sigma>"] _
        filterlim_tendsto_add_at_top[OF tendsto_const[of "- \<mu>"] filterlim_ident]]
    by(intro tendsto_divide tendsto_const filterlim_compose[OF tendsto_arctan_at_top]) auto
  hence lim: "((\<lambda>y. arctan ((y - \<mu>) / \<sigma>) / pi) \<longlongrightarrow> 1 / 2) at_top"
    by simp
  show ?thesis
    by(subst nn_integral_FTC_atLeast
        [where F="\<lambda>y. arctan ((y - \<mu>) / \<sigma>) / pi" and T="1 / 2"])
      (auto intro!: DERIV_Cauchy_cdf lim)
qed

lemma Cauchy_nn_integral_atMost:
  assumes sigma[arith]: "0 < \<sigma>"
  shows "(\<integral>\<^sup>+y\<in>{..x}. Cauchy_density \<mu> \<sigma> y \<partial>lborel)
          = ennreal (1 / 2 + arctan ((x - \<mu>) / \<sigma>) / pi)"
proof -
  have ind: "indicator {..x} (- y) = (indicator {- x..} y :: ennreal)" for y :: real
    by(simp add: indicator_def)
  have arg: "(- x - - \<mu>) / \<sigma> = - ((x - \<mu>) / \<sigma>)"
    by(simp add: minus_divide_left)
  have "(\<integral>\<^sup>+y\<in>{..x}. Cauchy_density \<mu> \<sigma> y \<partial>lborel)
        = (\<integral>\<^sup>+y\<in>{- x..}. Cauchy_density (- \<mu>) \<sigma> y \<partial>lborel)"
    by(subst nn_integral_real_affine
        [where t=0 and c="- 1" and f="\<lambda>y. ennreal (Cauchy_density \<mu> \<sigma> y) * indicator {..x} y"])
      (simp_all add: ind Cauchy_density_uminus)
  also have "... = ennreal (1 / 2 - arctan ((- x - - \<mu>) / \<sigma>) / pi)"
    by(rule Cauchy_nn_integral_atLeast[OF sigma])
  also have "... = ennreal (1 / 2 + arctan ((x - \<mu>) / \<sigma>) / pi)"
    unfolding arg
    by(simp add: arctan_minus)
  finally show ?thesis .
qed

lemma prob_space_Cauchy_density:
  assumes sigma[arith]: "0 < \<sigma>"
  shows "prob_space (density lborel (Cauchy_density \<mu> \<sigma>))"
proof
  have split: "(\<integral>\<^sup>+y. ennreal (Cauchy_density \<mu> \<sigma> y) \<partial>lborel)
                 = (\<integral>\<^sup>+y\<in>{..0}. Cauchy_density \<mu> \<sigma> y \<partial>lborel)
                    + (\<integral>\<^sup>+y\<in>{0<..}. Cauchy_density \<mu> \<sigma> y \<partial>lborel)"
    by(subst nn_integral_add[symmetric])
      (auto intro!: nn_integral_cong simp: indicator_def)
  have null: "(\<integral>\<^sup>+y\<in>{0<..}. Cauchy_density \<mu> \<sigma> y \<partial>lborel)
                = (\<integral>\<^sup>+y\<in>{0..}. Cauchy_density \<mu> \<sigma> y \<partial>lborel)"
    by(intro nn_integral_cong_AE AE_I[where N="{0}"]) (auto simp: indicator_def)
  have nn1: "0 \<le> 1 / 2 + arctan ((0 - \<mu>) / \<sigma>) / pi"
    using arctan_div_pi_pos[of "(0 - \<mu>) / \<sigma>"] by linarith
  have nn2: "0 \<le> 1 / 2 - arctan ((0 - \<mu>) / \<sigma>) / pi"
    using arctan_div_pi_lt_1[of "(0 - \<mu>) / \<sigma>"] by linarith
  show "emeasure (density lborel (Cauchy_density \<mu> \<sigma>))
          (space (density lborel (Cauchy_density \<mu> \<sigma>))) = 1"
    using nn1 nn2
    by(simp add: emeasure_density split null Cauchy_nn_integral_atMost
        Cauchy_nn_integral_atLeast flip: ennreal_plus)
qed

corollary real_distribution_Cauchy:
  "0 < \<sigma> \<Longrightarrow> real_distribution (density lborel (Cauchy_density \<mu> \<sigma>))"
  by(simp add: real_distribution_def real_distribution_axioms_def prob_space_Cauchy_density)

lemma Cauchy_cdf_def:
  assumes sigma[arith]: "0 < \<sigma>"
  shows "cdf (density lborel (Cauchy_density \<mu> \<sigma>)) x = 1 / 2 + arctan ((x - \<mu>) / \<sigma>) / pi"
  using arctan_div_pi_pos[of "(x - \<mu>) / \<sigma>"]
  by(simp add: cdf_def measure_def emeasure_density Cauchy_nn_integral_atMost)

lemma std_Cauchy_cdf_def: "cdf std_Cauchy_distribution x = 1 / 2 + arctan x / pi"
  by(simp add: Cauchy_cdf_def)


lemma Cauchy_cdf_location_scale:
  assumes sigma: "0 < \<sigma>"
  shows "cdf (density lborel (Cauchy_density \<mu> \<sigma>)) x
           = cdf std_Cauchy_distribution ((x - \<mu>) / \<sigma>)"
  by(simp add: Cauchy_cdf_def[OF sigma] Cauchy_cdf_def[OF zero_less_one])

lemma std_Cauchy_tail_asymp_equiv:
  "(\<lambda>t. 1 - cdf std_Cauchy_distribution t) \<sim>[at_top] (\<lambda>t. 1 / (pi * t))"
proof(rule asymp_equivI')
  have eq: "\<forall>\<^sub>F t in at_top. (1 / 2 - arctan t / pi) * (pi * t)
                             = (1 - cdf std_Cauchy_distribution t) / (1 / (pi * t))"
    using eventually_gt_at_top[of "0::real"]
    by eventually_elim (simp add: std_Cauchy_cdf_def)
  have "((\<lambda>t::real. (1 / 2 - arctan t / pi) * (pi * t)) \<longlongrightarrow> 1) at_top"
    by real_asymp
  from Lim_transform_eventually[OF this eq]
  show "((\<lambda>t. (1 - cdf std_Cauchy_distribution t) / (1 / (pi * t))) \<longlongrightarrow> 1) at_top" .
qed

theorem std_Cauchy_MDA: "domain_of_attraction (cdf std_Cauchy_distribution) (EVD_cdf 1 0 1)"
proof -
  have F: "right_continuous_mono (cdf std_Cauchy_distribution) 0 1"
    by(auto intro!: right_continuous_mono_cdf real_distribution_Cauchy)
  have lt1: "cdf std_Cauchy_distribution x < 1" for x
    using arctan_div_pi_lt_1[of x] by(simp add: std_Cauchy_cdf_def)
  have "regularly_varying (\<lambda>x. 1 - cdf std_Cauchy_distribution x) (- 1)"
  proof(rule regularly_varyingI_total)
    show "(\<lambda>x. 1 - cdf std_Cauchy_distribution x) \<in> borel_measurable borel"
      by(auto intro!: borel_measurable_continuous_onI simp: std_Cauchy_cdf_def)
  next
    fix x :: real
    assume x: "0 < x"
    have "((\<lambda>t. (1 / 2 - arctan (t * x) / pi) / (1 / 2 - arctan t / pi))
            \<longlongrightarrow> x powr (- 1)) at_top"
      using x by(real_asymp simp add: powr_minus)
    thus "((\<lambda>t. (1 - cdf std_Cauchy_distribution (t * x))
                  / (1 - cdf std_Cauchy_distribution t)) \<longlongrightarrow> x powr (- 1)) at_top"
      by(simp add: std_Cauchy_cdf_def)
  qed(use lt1 in simp)
  thus ?thesis
    using MDA_regularly_varying_pos[OF F zero_less_one] lt1 by simp
qed

corollary Cauchy_MDA:
  assumes "0 < \<sigma>"
  shows "domain_of_attraction (cdf (density lborel (Cauchy_density \<mu> \<sigma>))) (EVD_cdf 1 0 1)"
  unfolding Cauchy_cdf_location_scale[OF assms]
  by(intro domain_of_attraction_affine assms std_Cauchy_MDA)

theorem std_Cauchy_normalization:
  fixes x :: real
  shows "(\<lambda>n. cdf std_Cauchy_distribution (real n / pi * x) ^ n) \<longlonglongrightarrow> EVD_cdf 1 1 1 x"
proof -
  interpret C: real_distribution std_Cauchy_distribution
    by(rule real_distribution_Cauchy) simp
  show ?thesis
  proof(cases "0 < x")
    case x: True
    have EVD: "EVD_cdf 1 1 1 x = exp (- (1 / x))"
      using x by(simp add: EVD_cdf_def powr_minus_divide)
    have top: "filterlim (\<lambda>t::real. t / pi * x) at_top at_top"
      using filterlim_at_top_mult_tendsto_pos[OF tendsto_const[of "x / pi"] _ filterlim_ident] x
      by(simp add: field_simps)
    have "(\<lambda>t. 1 - cdf std_Cauchy_distribution (t / pi * x))
            \<sim>[at_top] (\<lambda>t. 1 / (pi * (t / pi * x)))"
      by(intro asymp_equiv_compose'[OF std_Cauchy_tail_asymp_equiv] top)
    hence ae: "(\<lambda>t. t * (1 - cdf std_Cauchy_distribution (t / pi * x)))
                 \<sim>[at_top] (\<lambda>t. t * (1 / (pi * (t / pi * x))))"
      by(intro asymp_equiv_mult asymp_equiv_refl)
    have ev: "\<forall>\<^sub>F t in at_top. t * (1 / (pi * (t / pi * x))) = 1 / x"
      using eventually_gt_at_top[of "0::real"]
      by eventually_elim (use x in \<open>simp add: field_simps\<close>)
    have "(\<lambda>t. t * (1 - cdf std_Cauchy_distribution (t / pi * x))) \<sim>[at_top] (\<lambda>t. 1 / x)"
      by(rule asymp_equiv_transfer[OF ae _ ev]) simp
    from tendsto_asymp_equiv_cong[OF this]
    have "((\<lambda>t. t * (1 - cdf std_Cauchy_distribution (t / pi * x))) \<longlongrightarrow> 1 / x) at_top"
      by simp
    hence tail: "(\<lambda>n. real n * (1 - cdf std_Cauchy_distribution (real n / pi * x)))
                   \<longlonglongrightarrow> 1 / x"
      by(rule filterlim_compose[OF _ filterlim_real_sequentially])
    have "(\<lambda>n. cdf std_Cauchy_distribution (real n / pi * x) ^ n) \<longlonglongrightarrow> exp (- (1 / x))
            \<longleftrightarrow> (\<lambda>n. real n * (1 - cdf std_Cauchy_distribution (real n / pi * x)))
                  \<longlonglongrightarrow> - ln (exp (- (1 / x)))"
      using x
      by(intro power_tendsto_iff_tendsto_tail C.cdf_nonneg C.cdf_bounded_prob) auto
    thus ?thesis
      unfolding EVD
      using tail by simp
  next
    case x: False
    have EVD: "EVD_cdf 1 1 1 x = 0"
      using x by(simp add: EVD_cdf_def)
    have arg: "real n / pi * x \<le> 0" for n
      using x mult_nonneg_nonpos[of "real n" x] by(simp add: divide_nonpos_pos)
    have half: "cdf std_Cauchy_distribution (real n / pi * x) \<le> 1 / 2" for n
      using arctan_monotone'[OF arg, of n] arctan_zero_zero
      by(simp add: std_Cauchy_cdf_def divide_nonpos_pos)
    show ?thesis
      unfolding EVD
    proof(rule tendsto_sandwich[where f="\<lambda>_. 0" and h="\<lambda>n. (1 / 2 :: real) ^ n"])
      show "\<forall>\<^sub>F n in sequentially. cdf std_Cauchy_distribution (real n / pi * x) ^ n
                                   \<le> (1 / 2) ^ n"
        by(intro always_eventually allI power_mono half C.cdf_nonneg)
      show "(\<lambda>n. (1 / 2 :: real) ^ n) \<longlonglongrightarrow> 0"
        by(rule LIMSEQ_realpow_zero) auto
    qed(use C.cdf_nonneg in auto)
  qed
qed

end