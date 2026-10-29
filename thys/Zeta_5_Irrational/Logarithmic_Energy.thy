(*  Title:   Logarithmic_Energy.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Logarithmic_Energy
  imports Laplace_Sin_Cot_Series
begin

section \<open>Logarithmic energy of measures on \<open>\<complex>\<close> and the zero-mass energy
  inequality\<close>

text \<open>The mutual logarithmic energy \<open>I(\<mu>, \<nu>) =
  \<integral>\<integral> ln |z - w| d\<mu>(z) d\<nu>(w)\<close> of finite measures on
  \<open>\<complex>\<close>, the
  two-dimensional Gaussian integral \<open>\<integral>\<^sub>\<complex> exp(-b|v|\<^sup>2) dv =
    \<pi>/b\<close>, the non-negativity of the energy of Gaussian
  kernels, the truncated kernels \<open>K\<^sub>n \<rightarrow> ln |z - w|\<close> obtained
    by integrating the Gaussian against \<open>ds/s\<close>
  (Frullani), and the main result @{text log_energy_zero_mass_nonpos}:
    for measures \<open>\<nu>\<^sub>1, \<nu>\<^sub>2 \<le> \<eta>\<close> of equal mass with
  \<open>ln |z - w|\<close> integrable on \<open>\<eta> \<otimes> \<eta>\<close> and a null
    diagonal, \<open>I(\<nu>\<^sub>1) - 2 I(\<nu>\<^sub>1, \<nu>\<^sub>2) + I(\<nu>\<^sub>2) \<le>
    0\<close>.\<close>

text \<open>Mutual logarithmic energy @{text "integral integral log|z - w| dmu(z) d\<nu>(w)"} on
  \<open>\<complex>\<close>.\<close>
definition logEnergyC :: "complex measure \<Rightarrow> complex measure \<Rightarrow> real" where
  "logEnergyC \<mu> \<nu> = integral\<^sup>L \<mu> (\<lambda>z. integral\<^sup>L \<nu> (\<lambda>w.
    ln (norm (z - w))))"


text \<open>Lemma 6.2 (zero-mass logarithmic energy), in the corrected form of the Lean proof:
  for finite
  measures @{text "\<nu>_1, \<nu>_2 \<le> \<eta>"} on \<open>\<complex>\<close> of equal mass,
    with @{text "log|z-w|"} integrable for
  @{text "\<eta> \<otimes> \<eta>"} and the diagonal @{text "\<eta> \<otimes> \<eta>"}-null,
  @{text "I(\<nu>_1) - 2 I(\<nu>_1,\<nu>_2) + I(\<nu>_2) \<le> 0"}.  (The literal statement with
    @{text "log 0 = 0"} is false
  for point masses; the diagonal hypothesis is what the paper uses.)
  Proof: Gaussian kernels @{text "e^{-s|z-w|^2}"} have nonnegative energy (Fubini), integrate in
  @{text s} against @{text "ds/s"} to reach @{text "log"} (dominated convergence).\<close>
text \<open>The Gaussian integral on @{text \<complex>}:
  @{text "\<integral> e^{-b|v|^2} dv = \<pi>/b"}.\<close>
lemma gauss_nn_C:
  fixes b :: real
  assumes b: "0 < b"
  shows "(\<integral>\<^sup>+ v. ennreal (exp (- b * (norm (v :: complex)) ^ 2)) \<partial>lborel) =
    ennreal (pi / b)"
proof -
  define h :: "real \<Rightarrow> real" where "h r = 2 * b * r * exp (- b * r ^ 2)" for r
  have hm: "h \<in> borel_measurable borel" unfolding h_def
    by simp
  have p2: "filterlim (\<lambda>r :: real. r ^ 2) at_top at_top"
    using filterlim_pow_at_top[OF _ filterlim_ident, of 2]
    by simp
  have l0: "((\<lambda>r :: real. exp (- (b * r ^ 2))) \<longlongrightarrow> 0) at_top"
    using filterlim_compose[OF exp_neg_lim[OF b] p2]
    by simp
  have l1: "((\<lambda>r :: real. exp (- (b * r ^ 2)) * (\<Sum> k \<le>
    1. (b * r ^ 2) ^ k / fact k)) \<longlongrightarrow> 0) at_top"
    using filterlim_compose[OF gam_lim[OF b, of 1] p2]
    by simp
  have lim1: "((\<lambda>r :: real. - exp (- b * r ^ 2)) \<longlongrightarrow> 0) at_top"
    using tendsto_minus[OF l0]
    by simp
  have step1: "ennreal (exp (- b * (norm v) ^ 2)) =
    (\<integral>\<^sup>+ r. ennreal (h r) * indicator {norm v..} r \<partial>lborel)"
    for v :: complex
  proof -
    have D: "DERIV (\<lambda>r :: real. - exp (- b * r ^ 2)) r :> h r" for r unfolding h_def
      by (intro derivative_eq_intros, (rule refl)+) (simp add: algebra_simps power2_eq_square)
    have nn: "0 \<le> h r" if "norm v \<le> r" for r
    proof -
      have r0: "0 \<le> r" using that norm_ge_zero[of v]
        by linarith
      show ?thesis unfolding h_def using r0 b
        using mult_nonneg_nonneg by simp
    qed
    have "(\<integral>\<^sup>+ r. ennreal (h r) * indicator {norm v..} r \<partial>lborel) =
      ennreal (0 - (- exp (- b * (norm v) ^ 2)))"
      using nn_integral_FTC_atLeast[OF hm D nn lim1] .
    thus ?thesis
      by simp
  qed
  have ps: "pair_sigma_finite (lborel :: complex measure) (lborel :: real measure)"
    by (simp add: pair_sigma_finite_def sigma_finite_lborel)
  have jm: "(\<lambda>(v :: complex, r :: real). ennreal (h r) * indicator {norm v..} r) \<in>
    borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  proof -
    have e: "(\<lambda>(v :: complex, r :: real). ennreal (h r) * indicator {norm v..} r) =
      (\<lambda>p. ennreal (h (snd p)) * indicator {p. norm (fst p) \<le> snd p} p)"
      by (simp add: fun_eq_iff indicator_def)
    have mf2: "(\<lambda>p :: complex \<times> real. snd p - norm (fst p)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      by simp
    have eq: "{p :: complex \<times> real. norm (fst p) \<le> snd p} =
      (\<lambda>p. snd p - norm (fst p)) -` {0..} \<inter> space (lborel \<Otimes>\<^sub>M lborel)"
      by (auto simp: space_pair_measure)
    have S: "{p :: complex \<times> real. norm (fst p) \<le> snd p} \<in>
      sets (lborel \<Otimes>\<^sub>M lborel)" unfolding eq using measurable_sets[OF mf2, of "{0..}"]
      by simp
    show ?thesis unfolding e using S hm
      by simp
  qed
  have inner: "(\<integral>\<^sup>+ v. ennreal (h r) *
    indicator {norm v..} r \<partial>(lborel :: complex measure)) =
    ennreal (pi * h r * r ^ 2) * indicator {0..} r" for r :: real
  proof (cases "0 \<le> r")
    case True
    have hn: "0 \<le> h r" unfolding h_def using True b
      by simp
    have ind: "(\<lambda>v :: complex. ennreal (h r) * indicator {norm v..} r) =
      (\<lambda>v. ennreal (h r) * indicator (cball 0 r) v)"
      by (simp add: fun_eq_iff indicator_def)
    have i1: "(\<integral>\<^sup>+ v. ennreal (h r) *
      indicator (cball 0 r) v \<partial>(lborel :: complex measure)) =
      ennreal (h r) * emeasure lborel (cball (0 :: complex) r)"
      using nn_integral_cmult_indicator[of "cball (0 :: complex) r" lborel "ennreal (h r)"] by simp
    have i2: "emeasure lborel (cball (0 :: complex) r) = ennreal (pi * r ^ 2)"
      using emeasure_cball[where c = "0 :: complex" and r = r] True
      by (simp add: unit_ball_vol_2)
    show ?thesis unfolding ind i1 i2 using True hn
      by (simp add: ennreal_mult["symmetric"] mult_ac)
  next
    case False
    have "(\<lambda>v :: complex. ennreal (h r) * indicator {norm v..} r) = (\<lambda>v. 0)"
    proof -
      have "\<not> norm (v :: complex) \<le> r" for v using False norm_ge_zero[of v]
        by linarith
      thus ?thesis
        by (simp add: fun_eq_iff indicator_def)
    qed
    thus ?thesis using False
      by simp
  qed
  have "(\<integral>\<^sup>+ v. ennreal (exp (- b * (norm (v :: complex)) ^ 2)) \<partial>lborel) =
    (\<integral>\<^sup>+ v. (\<integral>\<^sup>+ r. ennreal (h r) *
    indicator {norm (v :: complex)..} r \<partial>lborel) \<partial>lborel)"
    unfolding step1 ..
  also have "\<dots> = (\<integral>\<^sup>+ r. (\<integral>\<^sup>+ v. ennreal (h r) *
    indicator {norm (v :: complex)..} r \<partial>lborel) \<partial>lborel)"
    using pair_sigma_finite.Fubini'[OF ps jm]
    by (simp add: split_beta)
  also have "\<dots> = (\<integral>\<^sup>+ r. ennreal (pi * h r * r ^ 2) *
    indicator {0..} r \<partial>lborel)" unfolding inner ..
  also have "\<dots> = ennreal (pi / b)"
  proof -
    define F :: "real \<Rightarrow> real" where "F r = - pi * (r ^ 2 + 1 / b) * exp (- b * r ^ 2)"
      for r
    have gm: "(\<lambda>r. pi * h r * r ^ 2) \<in> borel_measurable borel" using hm
      by simp
    have D2: "DERIV F r :> pi * h r * r ^ 2" for r unfolding F_def h_def
      by (intro derivative_eq_intros, (rule refl)+) (use b in \<open>simp add: algebra_simps
        power2_eq_square\<close>)
    have nn2: "0 \<le> pi * h r * r ^ 2" if "0 \<le> r" for r unfolding h_def using that b
      by simp
    have e: "(\<lambda>r. - pi * (r ^ 2 + 1 / b) * exp (- b * r ^ 2)) =
      (\<lambda>r. (- pi / b) * (exp (- (b * r ^ 2)) * (\<Sum> k \<le>
      1. (b * r ^ 2) ^ k / fact k)))"
      using b by (simp add: fun_eq_iff algebra_simps)
    have lim2: "(F \<longlongrightarrow> 0) at_top" unfolding F_def e
      using tendsto_mult_left[OF l1, of "- pi / b"]
      by simp
    have "(\<integral>\<^sup>+ r. ennreal (pi * h r * r ^ 2) * indicator {0..} r \<partial>lborel) =
      ennreal (0 - F 0)"
      using nn_integral_FTC_atLeast[OF gm D2 nn2 lim2] .
    also have "0 - F 0 = pi / b" unfolding F_def
      by simp
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma gauss_integral_C:
  assumes "0 < b"
  shows "integral\<^sup>L lborel (\<lambda>v :: complex. exp (- b * (norm v) ^ 2)) = pi / b"
proof -
  have m: "(\<lambda>v :: complex. exp (- b * (norm v) ^ 2)) \<in> borel_measurable lborel"
    by simp
  have "integral\<^sup>L lborel (\<lambda>v :: complex. exp (- b * (norm v) ^ 2)) =
    enn2real (\<integral>\<^sup>+ v. ennreal (exp (- b *
    (norm (v :: complex)) ^ 2)) \<partial>lborel)"
    using integral_eq_nn_integral[OF m]
    by simp
  also have "\<dots> = pi / b" unfolding gauss_nn_C[OF assms] using assms
    by (simp add: enn2real_ennreal)
  finally show ?thesis .
qed

text \<open>Convolution of two Gaussians:
  @{text "\<integral> e^{-2s|z-u|^2} e^{-2s|w-u|^2} du = \<pi>/(4s) e^{-s|z-w|^2}"}.\<close>
lemma gauss_conv:
  assumes "0 < s"
  shows "integral\<^sup>L lborel (\<lambda>u :: complex. exp (- 2 * s * (norm (z - u)) ^ 2) *
    exp (- 2 * s * (norm (w - u)) ^ 2)) = pi / (4 * s) * exp (- s * (norm (z - w)) ^ 2)"
proof -
  define m where "m = (z + w) / 2"
  have par: "2 * (norm (z - u)) ^ 2 + 2 * (norm (w - u)) ^ 2 =
    4 * (norm (u - m)) ^ 2 + (norm (z - w)) ^ 2" for u
    unfolding m_def cmod_power2
    by (simp add: power2_eq_square field_simps)
  have pt: "exp (- 2 * s * (norm (z - u)) ^ 2) * exp (- 2 * s * (norm (w - u)) ^ 2) =
    exp (- s * (norm (z - w)) ^ 2) * exp (- (4 * s) * (norm (u - m)) ^ 2)" for u
  proof -
    have "- 2 * s * (norm (z - u)) ^ 2 + - 2 * s * (norm (w - u)) ^ 2 =
      - s * (norm (z - w)) ^ 2 + - (4 * s) * (norm (u - m)) ^ 2"
      using arg_cong[OF par[of u], of "\<lambda>x. - s * x"]
      by (simp add: algebra_simps)
    thus ?thesis
      by (simp add: mult_exp_exp)
  qed
  have tr: "integral\<^sup>L lborel (\<lambda>u :: complex. exp (- (4 * s) * (norm (u - m)) ^ 2)) =
    integral\<^sup>L lborel (\<lambda>u :: complex. exp (- (4 * s) * (norm u) ^ 2))"
  proof -
    have mf: "(\<lambda>u :: complex. exp (- (4 * s) * (norm (u - m)) ^ 2)) \<in>
      borel_measurable borel"
      by simp
    have "integral\<^sup>L lborel (\<lambda>u :: complex. exp (- (4 * s) * (norm (u - m)) ^ 2)) =
      integral\<^sup>L (distr lborel borel ((+) m)) (\<lambda>u :: complex. exp (- (4 * s) *
      (norm (u - m)) ^ 2))"
      using lborel_distr_plus[of m]
      by simp
    also have "\<dots> = integral\<^sup>L lborel (\<lambda>u :: complex. exp (- (4 * s) * (norm (m +
      u - m)) ^ 2))"
      using integral_distr[OF _ mf, of "(+) m" lborel]
      by simp
    finally show ?thesis
      by simp
  qed
  have s4: "0 < 4 * s" using assms
    by simp
  have "integral\<^sup>L lborel (\<lambda>u :: complex. exp (- 2 * s * (norm (z - u)) ^ 2) *
    exp (- 2 * s * (norm (w - u)) ^ 2))
      = integral\<^sup>L lborel (\<lambda>u :: complex. exp (- s * (norm (z - w)) ^ 2) * exp (- (4 *
        s) * (norm (u - m)) ^ 2))"
    unfolding pt ..
  also have "\<dots> = exp (- s * (norm (z - w)) ^ 2) *
    integral\<^sup>L lborel (\<lambda>u :: complex. exp (- (4 * s) * (norm (u - m)) ^ 2))"
    by simp
  also have "\<dots> = exp (- s * (norm (z - w)) ^ 2) * (pi / (4 * s))"
    unfolding tr gauss_integral_C[OF s4] ..
  finally show ?thesis
    by (simp add: mult_ac)
qed

definition gPhi :: "real \<Rightarrow> complex measure \<Rightarrow> complex \<Rightarrow> real"
  where
  "gPhi s \<mu> u = integral\<^sup>L \<mu> (\<lambda>z. exp (- 2 * s * (norm (z - u)) ^ 2))"

definition Eform :: "complex measure \<Rightarrow> complex measure \<Rightarrow> (complex \<times>
  complex \<Rightarrow> real) \<Rightarrow> real" where
  "Eform \<nu>1 \<nu>2 k = integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) k - 2 *
    integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) k +
    integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) k"

lemma gPhi_nn:
  fixes \<mu> :: "complex measure"
  assumes fm: "finite_measure \<mu>" and sm: "sets \<mu> = sets borel" and s: "0 \<le> s"
  shows "ennreal (gPhi s \<mu> u) = (\<integral>\<^sup>+ z. ennreal (exp (- 2 * s * (norm (z -
    u)) ^ 2)) \<partial>\<mu>)"
proof -
  have m: "(\<lambda>z :: complex. exp (- 2 * s * (norm (z - u)) ^ 2)) \<in>
    borel_measurable \<mu>" unfolding measurable_cong_sets[OF sm refl]
    by simp
  have "norm (exp (- 2 * s * (norm (z - u)) ^ 2)) \<le> 1" for z :: complex using s
    by simp
  hence b: "AE z in \<mu>. norm (exp (- 2 * s * (norm (z - u)) ^ 2)) \<le> 1"
    by simp
  have i: "integrable \<mu> (\<lambda>z :: complex. exp (- 2 * s * (norm (z - u)) ^ 2))"
    using finite_measure.integrable_const_bound[OF fm b m] .
  show ?thesis unfolding gPhi_def using nn_integral_eq_integral[OF i]
    by simp
qed

lemma gPhi_nonneg: "0 \<le> gPhi s \<mu> u"
  unfolding gPhi_def
  by simp

lemma gPhi_meas:
  fixes \<mu> :: "complex measure"
  assumes fm: "finite_measure \<mu>" and sm: "sets \<mu> = sets borel"
  shows "gPhi s \<mu> \<in> borel_measurable borel"
proof -
  have sf: "sigma_finite_measure \<mu>" using fm
    by (simp add: finite_measure_def)
  have j: "(\<lambda>(u, z). exp (- 2 * s * (norm (z - u)) ^ 2)) \<in>
    borel_measurable (borel \<Otimes>\<^sub>M \<mu>)"
    unfolding measurable_cong_sets[OF sets_pair_measure_cong[OF refl sm] refl]
    by simp
  show ?thesis unfolding gPhi_def[abs_def]
    using sigma_finite_measure.borel_measurable_lebesgue_integral[OF sf,
    of "\<lambda>u z. exp (- 2 * s * (norm (z - u)) ^ 2)" borel] j
    by simp
qed

lemma par_exp:
  fixes z w u :: complex
  shows "exp (- 2 * s * (norm (z - u)) ^ 2) * exp (- 2 * s * (norm (w - u)) ^ 2) =
    exp (- s * (norm (z - w)) ^ 2) * exp (- (4 * s) * (norm (u - (z + w) / 2)) ^ 2)"
proof -
  have par: "2 * (norm (z - u)) ^ 2 + 2 * (norm (w - u)) ^ 2 =
    4 * (norm (u - (z + w) / 2)) ^ 2 + (norm (z - w)) ^ 2"
    unfolding cmod_power2
    by (simp add: power2_eq_square field_simps)
  have "- 2 * s * (norm (z - u)) ^ 2 + - 2 * s * (norm (w - u)) ^ 2 =
    - s * (norm (z - w)) ^ 2 + - (4 * s) * (norm (u - (z + w) / 2)) ^ 2"
    using arg_cong[OF par, of "\<lambda>x. - s * x"]
    by (simp add: algebra_simps)
  thus ?thesis
    by (simp add: mult_exp_exp)
qed

lemma gauss_shift_nn:
  fixes b :: real and m :: complex
  assumes b: "0 < b"
  shows "(\<integral>\<^sup>+ u. ennreal (exp (- b * (norm (u - m)) ^ 2)) \<partial>lborel) =
    ennreal (pi / b)"
proof -
  have mf: "(\<lambda>u :: complex. ennreal (exp (- b * (norm (u - m)) ^ 2))) \<in>
    borel_measurable borel"
    by simp
  have "(\<integral>\<^sup>+ u. ennreal (exp (- b * (norm (u - m)) ^ 2)) \<partial>lborel) =
    (\<integral>\<^sup>+ u. ennreal (exp (- b * (norm (u -
    m)) ^ 2)) \<partial>(distr lborel borel ((+) m)))"
    using lborel_distr_plus[of m]
    by simp
  also have "\<dots> = (\<integral>\<^sup>+ u. ennreal (exp (- b * (norm (m + u -
    m)) ^ 2)) \<partial>lborel)"
    using nn_integral_distr[of "(+) m" lborel borel "\<lambda>u. ennreal (exp (- b * (norm (u -
      m)) ^ 2))"] mf
    by simp
  also have "\<dots> = ennreal (pi / b)" using gauss_nn_C[OF b]
    by simp
  finally show ?thesis .
qed

lemma conv_nn:
  fixes z w :: complex
  assumes s: "0 < s"
  shows "(\<integral>\<^sup>+ u. ennreal (exp (- 2 * s * (norm (z - u)) ^ 2) * exp (- 2 * s *
    (norm (w - u)) ^ 2)) \<partial>lborel) =
    ennreal (pi / (4 * s) * exp (- s * (norm (z - w)) ^ 2))"
proof -
  have s4: "0 < 4 * s" using s
    by simp
  have "(\<integral>\<^sup>+ u. ennreal (exp (- 2 * s * (norm (z - u)) ^ 2) * exp (- 2 * s *
    (norm (w - u)) ^ 2)) \<partial>lborel)
      = (\<integral>\<^sup>+ u. ennreal (exp (- s * (norm (z - w)) ^ 2)) * ennreal (exp (- (4 * s) *
        (norm (u - (z + w) / 2)) ^ 2)) \<partial>lborel)"
    unfolding par_exp
    by (simp add: ennreal_mult)
  also have "\<dots> = ennreal (exp (- s * (norm (z - w)) ^ 2)) *
    (\<integral>\<^sup>+ u. ennreal (exp (- (4 * s) * (norm (u - (z + w) /
    2)) ^ 2)) \<partial>lborel)"
    by (simp add: nn_integral_cmult)
  also have "\<dots> = ennreal (exp (- s * (norm (z - w)) ^ 2)) * ennreal (pi / (4 * s))"
    unfolding gauss_shift_nn[OF s4] ..
  also have "\<dots> = ennreal (pi / (4 * s) * exp (- s * (norm (z - w)) ^ 2))" using s
    by (simp add: ennreal_mult["symmetric"] mult_ac)
  finally show ?thesis .
qed

text \<open>Gaussian kernels have nonnegative energy:
  @{text "E(e^{-s|p_1 - p_2|^2}) = (4s/\<pi>) \<integral> (\<Phi>_1 - \<Phi>_2)^2 \<ge> 0"}.\<close>
lemma gauss_pair_nn:
  fixes \<mu> \<nu> :: "complex measure"
  assumes fm: "finite_measure \<mu>" and fn: "finite_measure \<nu>" and sm: "sets \<mu> =
    sets borel" and sn: "sets \<nu> = sets borel" and s: "0 < s"
  shows "(\<integral>\<^sup>+ u. ennreal (gPhi s \<mu> u * gPhi s \<nu> u) \<partial>lborel) =
    ennreal (pi / (4 * s)) * (\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (exp (- s *
    (norm (z - w)) ^ 2)) \<partial>\<nu> \<partial>\<mu>)"
proof -
  have s0: "0 \<le> s" using s
    by simp
  have sfm: "sigma_finite_measure \<mu>" using fm
    by (simp add: finite_measure_def)
  have sfn: "sigma_finite_measure \<nu>" using fn
    by (simp add: finite_measure_def)
  have p1: "pair_sigma_finite \<mu> (lborel :: complex measure)" using sfm
    by (simp add: pair_sigma_finite_def sigma_finite_lborel)
  have p2: "pair_sigma_finite \<nu> (lborel :: complex measure)" using sfn
    by (simp add: pair_sigma_finite_def sigma_finite_lborel)
  have S1: "ennreal (gPhi s \<mu> u * gPhi s \<nu> u) =
    (\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (exp (- 2 * s * (norm (z - u)) ^ 2)) *
    ennreal (exp (- 2 * s * (norm (w - u)) ^ 2)) \<partial>\<nu> \<partial>\<mu>)" for u :: complex
  proof -
    have mf: "(\<lambda>z. ennreal (exp (- 2 * s * (norm (z - u)) ^ 2))) \<in>
      borel_measurable \<mu>" unfolding measurable_cong_sets[OF sm refl]
      by simp
    have mg: "(\<lambda>w. ennreal (exp (- 2 * s * (norm (w - u)) ^ 2))) \<in>
      borel_measurable \<nu>" unfolding measurable_cong_sets[OF sn refl]
      by simp
    have "ennreal (gPhi s \<mu> u * gPhi s \<nu> u) =
      ennreal (gPhi s \<mu> u) * ennreal (gPhi s \<nu> u)" using gPhi_nonneg
      by (simp add: ennreal_mult)
    also have "\<dots> = (\<integral>\<^sup>+ z. ennreal (exp (- 2 * s * (norm (z -
      u)) ^ 2)) \<partial>\<mu>) * (\<integral>\<^sup>+ w. ennreal (exp (- 2 * s * (norm (w -
      u)) ^ 2)) \<partial>\<nu>)"
      unfolding gPhi_nn[OF fm sm s0] gPhi_nn[OF fn sn s0] ..
    also have "\<dots> = (\<integral>\<^sup>+ z. ennreal (exp (- 2 * s * (norm (z - u)) ^ 2)) *
      (\<integral>\<^sup>+ w. ennreal (exp (- 2 * s * (norm (w -
      u)) ^ 2)) \<partial>\<nu>) \<partial>\<mu>)"
      using nn_integral_multc[OF mf, of "\<integral>\<^sup>+ w. ennreal (exp (- 2 * s * (norm (w -
        u)) ^ 2)) \<partial>\<nu>"]
      by simp
    also have "\<dots> = (\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (exp (- 2 * s *
      (norm (z - u)) ^ 2)) * ennreal (exp (- 2 * s * (norm (w -
      u)) ^ 2)) \<partial>\<nu> \<partial>\<mu>)"
      using nn_integral_cmult[OF mg]
      by simp
    finally show ?thesis .
  qed
  have m1: "(\<lambda>(z, u). \<integral>\<^sup>+ w. ennreal (exp (- 2 * s * (norm (z - u)) ^ 2)) *
    ennreal (exp (- 2 * s * (norm (w - u)) ^ 2)) \<partial>\<nu>) \<in>
    borel_measurable (\<mu> \<Otimes>\<^sub>M lborel)"
  proof -
    have jm0: "(\<lambda>p :: (complex \<times> complex) \<times> complex. ennreal (exp (- 2 * s *
      (norm (fst (fst p) - snd (fst p))) ^ 2)) * ennreal (exp (- 2 * s * (norm (snd p -
      snd (fst p))) ^ 2))) \<in> borel_measurable ((borel \<Otimes>\<^sub>M lborel)
      \<Otimes>\<^sub>M borel)"
      by simp
    have e: "(\<lambda>((z :: complex, u :: complex),
      w :: complex). ennreal (exp (- 2 * s * (norm (z - u)) ^ 2)) * ennreal (exp (- 2 * s *
      (norm (w - u)) ^ 2))) = (\<lambda>p. ennreal (exp (- 2 * s * (norm (fst (fst p) -
      snd (fst p))) ^ 2)) * ennreal (exp (- 2 * s * (norm (snd p - snd (fst p))) ^ 2)))"
      by (simp add: fun_eq_iff)
    have jm: "(\<lambda>((z, u), w). ennreal (exp (- 2 * s * (norm (z - u)) ^ 2)) *
      ennreal (exp (- 2 * s * (norm (w - u)) ^ 2))) \<in>
      borel_measurable ((\<mu> \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M \<nu>)"
      unfolding measurable_cong_sets[OF sets_pair_measure_cong[OF sets_pair_measure_cong[OF sm refl]
        sn] refl]
      unfolding e using jm0 .
    show ?thesis using sigma_finite_measure.borel_measurable_nn_integral[OF sfn, of "\<lambda>(z,
      u) w. ennreal (exp (- 2 * s * (norm (z - u)) ^ 2)) * ennreal (exp (- 2 * s * (norm (w -
      u)) ^ 2))" "\<mu> \<Otimes>\<^sub>M lborel"] jm
      by (simp add: split_beta case_prod_beta)
  qed
  have m2: "(\<lambda>(w, u). ennreal (exp (- 2 * s * (norm (z - u)) ^ 2)) * ennreal (exp (- 2 * s *
    (norm (w - u)) ^ 2))) \<in> borel_measurable (\<nu> \<Otimes>\<^sub>M lborel)" for z :: complex
    unfolding measurable_cong_sets[OF sets_pair_measure_cong[OF sn refl] refl]
    by simp
  have "(\<integral>\<^sup>+ u. ennreal (gPhi s \<mu> u * gPhi s \<nu> u) \<partial>lborel) =
    (\<integral>\<^sup>+ u. \<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (exp (- 2 * s *
    (norm (z - u)) ^ 2)) * ennreal (exp (- 2 * s * (norm (w -
    u)) ^ 2)) \<partial>\<nu> \<partial>\<mu> \<partial>lborel)"
    unfolding S1 ..
  also have "\<dots> = (\<integral>\<^sup>+ z. \<integral>\<^sup>+ u. \<integral>\<^sup>+ w. ennreal
    (exp (- 2 * s * (norm (z - u)) ^ 2)) * ennreal (exp (- 2 * s * (norm (w -
    u)) ^ 2)) \<partial>\<nu> \<partial>lborel \<partial>\<mu>)"
    using pair_sigma_finite.Fubini'[OF p1 m1]
    by simp
  also have "\<dots> = (\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. \<integral>\<^sup>+ u. ennreal
    (exp (- 2 * s * (norm (z - u)) ^ 2)) * ennreal (exp (- 2 * s * (norm (w -
    u)) ^ 2)) \<partial>lborel \<partial>\<nu> \<partial>\<mu>)"
  proof (rule nn_integral_cong)
    fix z assume "z \<in> space \<mu>"
    show "(\<integral>\<^sup>+ u. \<integral>\<^sup>+ w. ennreal (exp (- 2 * s * (norm (z -
      u)) ^ 2)) * ennreal (exp (- 2 * s * (norm (w - u)) ^ 2)) \<partial>\<nu> \<partial>lborel) =
      (\<integral>\<^sup>+ w. \<integral>\<^sup>+ u. ennreal (exp (- 2 * s * (norm (z - u)) ^ 2)) *
      ennreal (exp (- 2 * s * (norm (w - u)) ^ 2)) \<partial>lborel \<partial>\<nu>)"
      using pair_sigma_finite.Fubini'[OF p2 m2[of z]]
      by simp
  qed
  also have "\<dots> = (\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (pi / (4 * s)) *
    ennreal (exp (- s * (norm (z - w)) ^ 2)) \<partial>\<nu> \<partial>\<mu>)"
  proof -
    have c: "(\<integral>\<^sup>+ u. ennreal (exp (- 2 * s * (norm (z - u)) ^ 2)) *
      ennreal (exp (- 2 * s * (norm (w - u)) ^ 2)) \<partial>lborel) =
      ennreal (pi / (4 * s)) * ennreal (exp (- s * (norm (z - w)) ^ 2))" for z w :: complex
      using conv_nn[OF s, of z w] s
      by (simp add: ennreal_mult["symmetric"])
    show ?thesis unfolding c ..
  qed
  also have "\<dots> = ennreal (pi / (4 * s)) *
    (\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (exp (- s * (norm (z -
    w)) ^ 2)) \<partial>\<nu> \<partial>\<mu>)"
  proof -
    have in1: "(\<integral>\<^sup>+ w. ennreal (pi / (4 * s)) * ennreal (exp (- s * (norm (z -
      w)) ^ 2)) \<partial>\<nu>) = ennreal (pi / (4 * s)) *
      (\<integral>\<^sup>+ w. ennreal (exp (- s * (norm (z - w)) ^ 2)) \<partial>\<nu>)"
      for z :: complex
      using nn_integral_cmult[of "\<lambda>w. ennreal (exp (- s * (norm (z -
        w)) ^ 2))" \<nu> "ennreal (pi / (4 * s))"] unfolding measurable_cong_sets[OF sn refl]
      by simp
    have jm: "(\<lambda>(z, w). ennreal (exp (- s * (norm (z - w)) ^ 2))) \<in>
      borel_measurable (\<mu> \<Otimes>\<^sub>M \<nu>)"
      unfolding measurable_cong_sets[OF sets_pair_measure_cong[OF sm sn] refl]
      by simp
    have mz: "(\<lambda>z. \<integral>\<^sup>+ w. ennreal (exp (- s * (norm (z -
      w)) ^ 2)) \<partial>\<nu>) \<in> borel_measurable \<mu>"
      using sigma_finite_measure.borel_measurable_nn_integral[OF sfn jm] .
    show ?thesis unfolding in1 using nn_integral_cmult[OF mz, of "ennreal (pi / (4 * s))"] .
  qed
  finally show ?thesis .
qed

lemma gauss_pair:
  assumes "finite_measure \<mu>" "finite_measure \<nu>" "sets \<mu> = sets borel" "sets \<nu> =
    sets borel" "0 < s"
  shows "integral\<^sup>L (\<mu> \<Otimes>\<^sub>M \<nu>) (\<lambda>p. exp (- s * (norm (fst p -
    snd p)) ^ 2)) = 4 * s / pi * integral\<^sup>L lborel (\<lambda>u. gPhi s \<mu> u *
    gPhi s \<nu> u)"
proof -
  have sfn: "sigma_finite_measure \<nu>" using assms(2)
    by (simp add: finite_measure_def)
  have gm: "(\<lambda>p :: complex \<times> complex. exp (- s * (norm (fst p - snd p)) ^ 2)) \<in>
    borel_measurable (\<mu> \<Otimes>\<^sub>M \<nu>)"
    unfolding measurable_cong_sets[OF sets_pair_measure_cong[OF assms(3,4)] refl]
    by simp
  have X: "(\<integral>\<^sup>+ p. ennreal (exp (- s * (norm (fst p -
    snd p)) ^ 2)) \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>)) =
    (\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (exp (- s * (norm (z -
    w)) ^ 2)) \<partial>\<nu> \<partial>\<mu>)"
    using sigma_finite_measure.nn_integral_fst[OF sfn,
      of "\<lambda>p. ennreal (exp (- s * (norm (fst p - snd p)) ^ 2))" \<mu>] gm
    by simp
  have L: "integral\<^sup>L (\<mu> \<Otimes>\<^sub>M \<nu>) (\<lambda>p. exp (- s * (norm (fst p -
    snd p)) ^ 2)) = enn2real (\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (exp (- s *
    (norm (z - w)) ^ 2)) \<partial>\<nu> \<partial>\<mu>)"
    unfolding X[symmetric] using integral_eq_nn_integral[OF gm]
    by simp
  have pm: "(\<lambda>u. gPhi s \<mu> u * gPhi s \<nu> u) \<in> borel_measurable lborel"
    using gPhi_meas[OF assms(1,3)] gPhi_meas[OF assms(2,4)]
    by simp
  have R: "integral\<^sup>L lborel (\<lambda>u. gPhi s \<mu> u * gPhi s \<nu> u) =
    enn2real (\<integral>\<^sup>+ u. ennreal (gPhi s \<mu> u * gPhi s \<nu> u) \<partial>lborel)"
    using integral_eq_nn_integral[OF pm] gPhi_nonneg
    by simp
  show ?thesis unfolding L R gauss_pair_nn[OF assms] using assms(5)
    by (simp add: enn2real_mult)
qed

lemma gPhi_prod_int:
  fixes \<mu> \<nu> :: "complex measure"
  assumes fm: "finite_measure \<mu>" and fn: "finite_measure \<nu>" and sm: "sets \<mu> =
    sets borel" and sn: "sets \<nu> = sets borel" and s: "0 < s"
  shows "integrable lborel (\<lambda>u. gPhi s \<mu> u * gPhi s \<nu> u)"
proof -
  have m: "(\<lambda>u. gPhi s \<mu> u * gPhi s \<nu> u) \<in> borel_measurable lborel"
    using gPhi_meas[OF fm sm] gPhi_meas[OF fn sn]
    by simp
  have le1: "(\<integral>\<^sup>+ w. ennreal (exp (- s * (norm (z - w)) ^ 2)) \<partial>\<nu>) \<le>
    emeasure \<nu> (space \<nu>)" for z :: complex
  proof -
    have "(\<integral>\<^sup>+ w. ennreal (exp (- s * (norm (z - w)) ^ 2)) \<partial>\<nu>) \<le>
      (\<integral>\<^sup>+ w. 1 \<partial>\<nu>)" using s
      by (fastforce intro: nn_integral_mono)
    thus ?thesis
      by simp
  qed
  have le2: "(\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (exp (- s * (norm (z -
    w)) ^ 2)) \<partial>\<nu> \<partial>\<mu>) \<le>
    (\<integral>\<^sup>+ z. emeasure \<nu> (space \<nu>) \<partial>\<mu>)"
    using le1
    by (blast intro: nn_integral_mono)
  have "emeasure \<nu> (space \<nu>) \<noteq> \<infinity>" using fn
    by (simp add: finite_measure.emeasure_finite)
  moreover have "emeasure \<mu> (space \<mu>) \<noteq> \<infinity>" using fm
    by (simp add: finite_measure.emeasure_finite)
  ultimately have fin: "(\<integral>\<^sup>+ z. emeasure \<nu> (space \<nu>) \<partial>\<mu>) <
    \<infinity>"
    by (simp add: ennreal_mult_less_top less_top)
  have fin2: "(\<integral>\<^sup>+ u. ennreal (gPhi s \<mu> u * gPhi s \<nu> u) \<partial>lborel) <
    \<infinity>"
  proof -
    have fin3: "(\<integral>\<^sup>+ z. \<integral>\<^sup>+ w. ennreal (exp (- s * (norm (z -
      w)) ^ 2)) \<partial>\<nu> \<partial>\<mu>) < \<infinity>" using le2 fin
      by simp
    show ?thesis unfolding gauss_pair_nn[OF fm fn sm sn s] using fin3
      by (simp add: ennreal_mult_less_top less_top)
  qed
  have e: "(\<lambda>u. ennreal (norm (gPhi s \<mu> u * gPhi s \<nu> u))) =
    (\<lambda>u. ennreal (gPhi s \<mu> u * gPhi s \<nu> u))" using gPhi_nonneg
    by (simp add: fun_eq_iff)
  show ?thesis unfolding integrable_iff_bounded e using m fin2
    by simp
qed

lemma Eform_gauss_nonneg:
  assumes "finite_measure \<nu>1" "finite_measure \<nu>2" "sets \<nu>1 = sets borel" "sets \<nu>2 =
    sets borel" "0 < s"
  shows "0 \<le> Eform \<nu>1 \<nu>2 (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2))"
proof -
  have i11: "integrable lborel (\<lambda>u. gPhi s \<nu>1 u * gPhi s \<nu>1 u)"
    by (rule gPhi_prod_int[OF assms(1,1,3,3,5)])
  have i12: "integrable lborel (\<lambda>u. gPhi s \<nu>1 u * gPhi s \<nu>2 u)"
    by (rule gPhi_prod_int[OF assms(1,2,3,4,5)])
  have i22: "integrable lborel (\<lambda>u. gPhi s \<nu>2 u * gPhi s \<nu>2 u)"
    by (rule gPhi_prod_int[OF assms(2,2,4,4,5)])
  have "Eform \<nu>1 \<nu>2 (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2)) =
    4 * s / pi * (integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>1 u * gPhi s \<nu>1 u) - 2 *
    integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>1 u * gPhi s \<nu>2 u) +
    integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>2 u * gPhi s \<nu>2 u))"
    unfolding Eform_def gauss_pair[OF assms(1,1,3,3,5)] gauss_pair[OF assms(1,2,3,4,5)]
      gauss_pair[OF assms(2,2,4,4,5)]
    by (simp add: algebra_simps)
  also have "integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>1 u * gPhi s \<nu>1 u) - 2 *
    integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>1 u * gPhi s \<nu>2 u) +
    integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>2 u * gPhi s \<nu>2 u) =
    integral\<^sup>L lborel (\<lambda>u. (gPhi s \<nu>1 u - gPhi s \<nu>2 u) ^ 2)"
  proof -
    have "integral\<^sup>L lborel (\<lambda>u. (gPhi s \<nu>1 u - gPhi s \<nu>2 u) ^ 2) =
      integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>1 u * gPhi s \<nu>1 u - 2 *
      (gPhi s \<nu>1 u * gPhi s \<nu>2 u) + gPhi s \<nu>2 u * gPhi s \<nu>2 u)"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>1 u * gPhi s \<nu>1 u) -
      2 * integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>1 u * gPhi s \<nu>2 u) +
      integral\<^sup>L lborel (\<lambda>u. gPhi s \<nu>2 u * gPhi s \<nu>2 u)"
      using i11 i12 i22
      by (simp add: Bochner_Integration.integral_diff Bochner_Integration.integral_add)
    finally show ?thesis ..
  qed
  finally have E: "Eform \<nu>1 \<nu>2 (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2)) =
    4 * s / pi * integral\<^sup>L lborel (\<lambda>u. (gPhi s \<nu>1 u - gPhi s \<nu>2 u) ^ 2)" .
  have "0 \<le> integral\<^sup>L lborel (\<lambda>u. (gPhi s \<nu>1 u - gPhi s \<nu>2 u) ^ 2)"
    by simp
  thus ?thesis unfolding E using assms(5)
    by (simp add: zero_le_mult_iff)
qed

text \<open>Frullani-type kernel: @{text "K_n(p) =
  (1/2)(\<integral>_{1/(n+1)}^{n+1} e^{-s}/s ds - \<integral>_{1/(n+1)}^{n+1} e^{-s|p_1 -
  p_2|^2}/s ds) \<longrightarrow> log|p_1 - p_2|"}.\<close>
definition Kn :: "nat \<Rightarrow> complex \<times> complex \<Rightarrow> real" where
  "Kn n p = 1 / 2 * (interval_lebesgue_integral lborel (ereal (1 / (real n + 1))) (ereal (real n +
    1)) (\<lambda>s. exp (- s) / s)
                     - interval_lebesgue_integral lborel (ereal (1 / (real n + 1))) (ereal (real n +
                       1)) (\<lambda>s. exp (- s * (norm (fst p - snd p)) ^ 2) / s))"

text \<open>Helpers on @{text "\<integral> e^{-u}/u du"} for the kernels @{text "K_n"}.\<close>
lemma ed_int:
  fixes x y :: real
  assumes "0 < x" "0 < y"
  shows "interval_lebesgue_integrable lborel (ereal x) (ereal y) (\<lambda>u. exp (- u) / u)"
    and "interval_lebesgue_integrable lborel (ereal x) (ereal y) (\<lambda>u. 1 / u)"
proof -
  have p: "0 < u" if "min x y \<le> u" for u using that assms
    by simp
  show "interval_lebesgue_integrable lborel (ereal x) (ereal y) (\<lambda>u. exp (- u) / u)"
    by (rule interval_integrable_isCont) (use p in \<open>auto intro!: continuous_intros\<close>)
  show "interval_lebesgue_integrable lborel (ereal x) (ereal y) (\<lambda>u. 1 / u)"
    by (rule interval_integrable_isCont) (use p in \<open>auto intro!: continuous_intros\<close>)
qed

lemma inv_ftc:
  fixes x y :: real
  assumes x: "0 < x" and y: "0 < y"
  shows "interval_lebesgue_integral lborel (ereal (x)) (ereal (y)) (\<lambda>u. 1 / u) =
    ln y - ln x"
proof (rule interval_integral_FTC_finite)
  show "continuous_on {min x y..max x y} (\<lambda>u. 1 / u)" using x y
    by (force intro: continuous_intros)
  fix u assume "min x y \<le> u" "u \<le> max x y"
  hence u: "0 < u" using x y
    by simp
  show "(ln has_vector_derivative 1 / u) (at u within {min x y..max x y})"
    using has_vector_derivative_at_within[OF DERIV_ln_divide[OF u,
      unfolded has_real_derivative_iff_has_vector_derivative]]
    by simp
qed

lemma ed_le:
  fixes x y :: real
  assumes x: "0 < x" and xy: "x \<le> y"
  shows "0 \<le> interval_lebesgue_integral lborel (ereal (x)) (ereal (y)) (\<lambda>u. exp (- u) /
    u)" and "interval_lebesgue_integral lborel (ereal (x)) (ereal (y)) (\<lambda>u. exp (- u) /
    u) \<le> ln y - ln x"
proof -
  have y: "0 < y" using x xy
    by simp
  have e1: "interval_lebesgue_integral lborel (ereal (x)) (ereal (y)) (\<lambda>u. exp (- u) / u) =
    set_lebesgue_integral lborel {x<..<y} (\<lambda>u. exp (- u) / u)"
    using xy
    by (simp add: interval_lebesgue_integral_le_eq)
  have e2: "interval_lebesgue_integral lborel (ereal (x)) (ereal (y)) (\<lambda>u. 1 / u) =
    set_lebesgue_integral lborel {x<..<y} (\<lambda>u. 1 / u)"
    using xy
    by (simp add: interval_lebesgue_integral_le_eq)
  have i1: "set_integrable lborel {x<..<y} (\<lambda>u. exp (- u) / u)" using ed_int(1)[OF x y] xy
    by (simp add: interval_lebesgue_integrable_def)
  have i2: "set_integrable lborel {x<..<y} (\<lambda>u. 1 / u)" using ed_int(2)[OF x y] xy
    by (simp add: interval_lebesgue_integrable_def)
  have pt: "exp (- u) / u \<le> 1 / u" if "u \<in> {x<..<y}" for u
  proof -
    have u: "0 < u" using that x
      by simp
    show ?thesis using u
      by (simp add: divide_right_mono)
  qed
  show "0 \<le> interval_lebesgue_integral lborel (ereal (x)) (ereal (y)) (\<lambda>u. exp (- u) /
    u)" unfolding e1 set_lebesgue_integral_def using x
    using Bochner_Integration.integral_nonneg by (simp add: indicator_def)
  show "interval_lebesgue_integral lborel (ereal (x)) (ereal (y)) (\<lambda>u. exp (- u) / u) \<le>
    ln y - ln x" unfolding e1 inv_ftc[OF x y, symmetric] e2
    using set_integral_mono[OF i1 i2 pt] .
qed

lemma ed_abs:
  fixes x r :: real
  assumes x: "0 < x" and r: "0 < r"
  shows "\<bar>interval_lebesgue_integral lborel (ereal (x)) (ereal (x *
    r)) (\<lambda>u. exp (- u) / u)\<bar> \<le> \<bar>ln r\<bar>"
proof -
  have xr: "0 < x * r" using x r
    by simp
  have l: "ln (x * r) = ln x + ln r" using x r
    by (simp add: ln_mult)
  show ?thesis
  proof (cases "1 \<le> r")
    case True
    have "x \<le> x * r" using True x
      by simp
    thus ?thesis using ed_le[OF x] l True
      by force
  next
    case False
    have "x * r \<le> x" using False x
      by simp
    hence "0 \<le> interval_lebesgue_integral lborel (ereal (x *
      r)) (ereal (x)) (\<lambda>u. exp (- u) /
      u)" and "interval_lebesgue_integral lborel (ereal (x *
      r)) (ereal (x)) (\<lambda>u. exp (- u) / u) \<le> ln x - ln (x * r)"
      using ed_le[OF xr] by auto
    thus ?thesis using interval_integral_endpoints_reverse[of "ereal x" "ereal (x *
      r)" "\<lambda>u. exp (- u) / u"] l False r
      by simp
  qed
qed

lemma lbint_bound:
  fixes x y C :: real and g :: "real \<Rightarrow> real"
  assumes gi: "interval_lebesgue_integrable lborel (ereal x) (ereal y) g" and b: "\<And>u. min x y
    \<le> u \<Longrightarrow> u \<le> max x y \<Longrightarrow> \<bar>g u\<bar> \<le> C"
  shows "\<bar>interval_lebesgue_integral lborel (ereal (x)) (ereal (y)) (g)\<bar> \<le>
    C * \<bar>y - x\<bar>"
proof -
  have aux: "\<bar>interval_lebesgue_integral lborel (ereal (a)) (ereal (c)) (g)\<bar> \<le>
    C * (c - a)"
    if ac: "a \<le> c" and ga: "interval_lebesgue_integrable lborel (ereal a) (ereal c) g" and ba:
      "\<And>u. a \<le> u \<Longrightarrow> u \<le> c \<Longrightarrow> \<bar>g u\<bar> \<le> C"
      for a c
  proof -
    have e: "interval_lebesgue_integral lborel (ereal (a)) (ereal (c)) (h) =
      set_lebesgue_integral lborel {a<..<c} h" for h :: "real \<Rightarrow> real" using ac
      by (simp add: interval_lebesgue_integral_le_eq)
    have ig: "set_integrable lborel {a<..<c} g" using ga ac
      by (simp add: interval_lebesgue_integrable_def)
    have ic: "set_integrable lborel {a<..<c} (\<lambda>_. k)" for k :: real
      using interval_integral_const(1)[of a c k] ac
      by (simp add: interval_lebesgue_integrable_def)
    have vc: "set_lebesgue_integral lborel {a<..<c} (\<lambda>_. k) = k * (c - a)" for k :: real
      using interval_integral_const(2)[of a c k] e[of "\<lambda>_. k"]
      by simp
    have up: "set_lebesgue_integral lborel {a<..<c} g \<le>
      set_lebesgue_integral lborel {a<..<c} (\<lambda>_. C)"
    proof (rule set_integral_mono[OF ig ic])
      fix u assume "u \<in> {a<..<c}"
      thus "g u \<le> C" using ba[of u]
        by simp
    qed
    have lo: "set_lebesgue_integral lborel {a<..<c} (\<lambda>_. - C) \<le>
      set_lebesgue_integral lborel {a<..<c} g"
    proof (rule set_integral_mono[OF ic ig])
      fix u assume "u \<in> {a<..<c}"
      thus "- C \<le> g u" using ba[of u]
        by simp
    qed
    show ?thesis unfolding e using up lo vc[of C] vc[of "- C"]
      by (simp add: abs_le_iff)
  qed
  show ?thesis
  proof (cases "x \<le> y")
    case True
    show ?thesis using aux[OF True gi] b True
      by simp
  next
    case False
    have gi': "interval_lebesgue_integrable lborel (ereal y) (ereal x) g"
      using gi interval_integrable_endpoints_reverse
      by auto
    have "\<bar>interval_lebesgue_integral lborel (ereal (y)) (ereal (x)) (g)\<bar> \<le>
      C * (x - y)" using aux[OF _ gi'] b False
      by simp
    thus ?thesis using interval_integral_endpoints_reverse[of "ereal x" "ereal y" g] False
      by simp
  qed
qed

lemma Kn_eq:
  assumes "fst p \<noteq> snd p"
  shows "2 * Kn n p = interval_lebesgue_integral lborel (ereal (1 / (real n + 1))) (ereal (1 /
    (real n + 1) * (norm (fst p - snd p)) ^ 2)) (\<lambda>u. exp (- u) / u) -
    interval_lebesgue_integral lborel (ereal (real n + 1)) (ereal ((real n + 1) * (norm (fst p -
    snd p)) ^ 2)) (\<lambda>u. exp (- u) / u)"
proof -
  define a :: real where "a = 1 / (real n + 1)"
  define b :: real where "b = real n + 1"
  define r :: real where "r = (norm (fst p - snd p)) ^ 2"
  have r0: "0 < r" unfolding r_def using assms
    by simp
  have a0: "0 < a" unfolding a_def
    by simp
  have b0: "0 < b" unfolding b_def
    by simp
  have ab: "a \<le> b"
  proof -
    have one: "1 \<le> real n + 1"
      by simp
    have "1 / (real n + 1) \<le> 1" using one
      by simp
    thus ?thesis unfolding a_def b_def using one
      by linarith
  qed
  have ar: "0 < a * r" using a0 r0
    by simp
  have br: "0 < b * r" using b0 r0
    by simp
  have sub0: "interval_lebesgue_integral lborel (ereal (a)) (ereal (b)) (\<lambda>x. r *\<^sub>R exp
    (- (x * r)) / (x * r)) = interval_lebesgue_integral lborel (ereal (a * r)) (ereal (b *
    r)) (\<lambda>u. exp (- u) / u)"
  proof -
    have d: "((\<lambda>s. s * r) has_real_derivative r) (at x within {a..b})" for x
      by (auto intro: derivative_eq_intros)
    have img: "(\<lambda>s. s * r) ` {a..b} \<subseteq> {0<..}" using a0 r0
      by auto
    have c0: "continuous_on {0<..} (\<lambda>u :: real. exp (- u) / u)"
      by (fast intro: continuous_intros)
    have ci: "continuous_on ((\<lambda>s. s * r) ` {a..b}) (\<lambda>u. exp (- u) / u)"
      using continuous_on_subset[OF c0 img] .
    show ?thesis using interval_integral_substitution_finite[OF ab,
      of "\<lambda>s. s * r" "\<lambda>_. r" "\<lambda>u. exp (- u) / u", OF d ci]
      by simp
  qed
  have cg: "interval_lebesgue_integral lborel (ereal (a)) (ereal (b)) (\<lambda>s. exp (- s * r) /
    s) = interval_lebesgue_integral lborel (ereal (a)) (ereal (b)) (\<lambda>x. r *\<^sub>R exp (-
    (x * r)) / (x * r))"
  proof (rule interval_integral_cong)
    fix x assume "x \<in> einterval (min (ereal a) (ereal b)) (max (ereal a) (ereal b))"
    hence "0 < x" using a0 ab
      by simp
    thus "exp (- x * r) / x = r *\<^sub>R exp (- (x * r)) / (x * r)" using r0
      by (simp add: field_simps)
  qed
  have sum1: "interval_lebesgue_integral lborel (ereal (a)) (ereal (a * r)) (\<lambda>u. exp (- u) /
    u) + interval_lebesgue_integral lborel (ereal (a * r)) (ereal (b)) (\<lambda>u. exp (- u) / u) =
    interval_lebesgue_integral lborel (ereal (a)) (ereal (b)) (\<lambda>u. exp (- u) / u)"
    using interval_integral_sum[of "ereal a" "ereal (a * r)" "ereal b" "\<lambda>u. exp (- u) /
      u"] ed_int(1)[of "min a (min (a * r) b)" "max a (max (a * r) b)"] a0 ar b0
    by simp
  have sum2: "interval_lebesgue_integral lborel (ereal (a * r)) (ereal (b)) (\<lambda>u. exp (- u) /
    u) + interval_lebesgue_integral lborel (ereal (b)) (ereal (b * r)) (\<lambda>u. exp (- u) / u) =
    interval_lebesgue_integral lborel (ereal (a * r)) (ereal (b * r)) (\<lambda>u. exp (- u) / u)"
    using interval_integral_sum[of "ereal (a * r)" "ereal b" "ereal (b *
      r)" "\<lambda>u. exp (- u) / u"] ed_int(1)[of "min (a * r) (min b (b * r))" "max (a *
      r) (max b (b * r))"] ar b0 br
    by simp
  have k: "2 * Kn n p = interval_lebesgue_integral lborel (ereal (a)) (ereal (b)) (\<lambda>u. exp
    (- u) / u) - interval_lebesgue_integral lborel (ereal (a)) (ereal (b)) (\<lambda>s. exp (- s *
    r) / s)"
    unfolding Kn_def a_def b_def r_def
    by simp
  have "2 * Kn n p = interval_lebesgue_integral lborel (ereal (a)) (ereal (a *
    r)) (\<lambda>u. exp (- u) / u) - interval_lebesgue_integral lborel (ereal (b)) (ereal (b *
    r)) (\<lambda>u. exp (- u) / u)"
    unfolding k cg sub0 using sum1 sum2
    by simp
  thus ?thesis unfolding a_def b_def r_def .
qed

lemma ed_near:
  fixes x r :: real
  assumes x: "0 < x" and r: "0 < r"
  shows "\<bar>interval_lebesgue_integral lborel (ereal (x)) (ereal (x *
    r)) (\<lambda>u. exp (- u) / u) - ln r\<bar> \<le> x * \<bar>r - 1\<bar>"
proof -
  have xr: "0 < x * r" using x r
    by simp
  have l: "interval_lebesgue_integral lborel (ereal (x)) (ereal (x * r)) (\<lambda>u. 1 / u) =
    ln r" using inv_ftc[OF x xr] x r
    by (simp add: ln_mult)
  have d: "interval_lebesgue_integral lborel (ereal (x)) (ereal (x * r)) (\<lambda>u. exp (- u) /
    u) - interval_lebesgue_integral lborel (ereal (x)) (ereal (x * r)) (\<lambda>u. 1 / u) =
    interval_lebesgue_integral lborel (ereal (x)) (ereal (x * r)) (\<lambda>u. exp (- u) / u - 1 /
    u)"
    using interval_lebesgue_integral_diff(2)[OF ed_int(1)[OF x xr] ed_int(2)[OF x xr]] ..
  have di: "interval_lebesgue_integrable lborel (ereal x) (ereal (x * r)) (\<lambda>u. exp (- u) /
    u - 1 / u)"
    using interval_lebesgue_integral_diff(1)[OF ed_int(1)[OF x xr] ed_int(2)[OF x xr]] .
  have b: "\<bar>exp (- u) / u - 1 / u\<bar> \<le> 1"
    if "min x (x * r) \<le> u" "u \<le> max x (x * r)" for u
  proof -
    have u: "0 < u" using that x xr
      by simp
    have e1: "1 - u \<le> exp (- u)" using exp_ge_add_one_self[of "- u"]
      by simp
    have e2: "exp (- u) \<le> 1" using u
      by simp
    have "\<bar>exp (- u) / u - 1 / u\<bar> = (1 - exp (- u)) / u" using u e2
      by (simp add: field_simps)
    also have "\<dots> \<le> 1" using u e1
      by (simp add: divide_le_eq)
    finally show ?thesis .
  qed
  have "\<bar>interval_lebesgue_integral lborel (ereal (x)) (ereal (x * r)) (\<lambda>u. exp (- u) /
    u - 1 / u)\<bar> \<le> 1 * \<bar>x * r - x\<bar>"
    by (rule lbint_bound[OF di b])
  moreover have "1 * \<bar>x * r - x\<bar> = x * \<bar>r - 1\<bar>"
  proof -
    have "x * r - x = x * (r - 1)"
      by (simp add: algebra_simps)
    thus ?thesis using x
      by (simp add: abs_mult)
  qed
  ultimately show ?thesis unfolding d[symmetric] l
    by simp
qed

lemma ed_far:
  fixes b r :: real
  assumes b: "0 < b" and r: "0 < r"
  shows "\<bar>interval_lebesgue_integral lborel (ereal (b)) (ereal (b *
    r)) (\<lambda>u. exp (- u) / u)\<bar> \<le> \<bar>r - 1\<bar> / (b * (min 1 r) ^ 2)"
proof -
  have br: "0 < b * r" using b r
    by simp
  have m0: "0 < b * min 1 r" using b r
    by simp
  have bd: "\<bar>exp (- u) / u\<bar> \<le> 1 / (b * min 1 r) ^ 2"
    if "min b (b * r) \<le> u" "u \<le> max b (b * r)" for u
  proof -
    have mu: "b * min 1 r \<le> u" using that b r
      by (auto simp: min_def)
    have u: "0 < u" using mu m0
      by simp
    have e1: "exp (- u) \<le> 1 / u"
    proof -
      have "u \<le> exp u" using exp_ge_add_one_self[of u]
        by linarith
      thus ?thesis using u
        by (simp add: exp_minus field_simps)
    qed
    have "\<bar>exp (- u) / u\<bar> = exp (- u) / u" using u
      by simp
    also have "\<dots> \<le> 1 / u / u" using e1 u
      using divide_right_mono[OF e1, of u] by simp
    also have "\<dots> = 1 / u ^ 2"
      by (simp add: power2_eq_square)
    also have "\<dots> \<le> 1 / (b * min 1 r) ^ 2"
      using power_mono[OF mu less_imp_le[OF m0], of 2] m0
      using u mu m0 by (metis \<open>1 / u / u =
        1 / u\<^sup>2\<close> pos_divide_le_eq pos_le_divide_eq power2_eq_square
        times_divide_eq_left mult_1 zero_compare_simps(6))
    finally show ?thesis .
  qed
  have "\<bar>interval_lebesgue_integral lborel (ereal (b)) (ereal (b * r)) (\<lambda>u. exp (- u) /
    u)\<bar> \<le> 1 / (b * min 1 r) ^ 2 * \<bar>b * r - b\<bar>"
    by (rule lbint_bound[OF ed_int(1)[OF b br] bd])
  also have "\<dots> = \<bar>r - 1\<bar> / (b * (min 1 r) ^ 2)"
  proof -
    have "b * r - b = b * (r - 1)"
      by (simp add: algebra_simps)
    hence ab: "\<bar>b * r - b\<bar> = b * \<bar>r - 1\<bar>" using b
      by (simp add: abs_mult)
    show ?thesis unfolding ab using b
      by (simp add: power2_eq_square field_simps)
  qed
  finally show ?thesis .
qed

lemma Kn_bound: "fst p \<noteq> snd p \<Longrightarrow>
  \<bar>Kn n p\<bar> \<le> 2 * \<bar>ln (norm (fst p - snd p))\<bar>"
proof -
  assume ne: "fst p \<noteq> snd p"
  have r0: "0 < (norm (fst p - snd p)) ^ 2" using ne
    by simp
  have a0: "0 < 1 / (real n + 1)"
    by simp
  have b0: "0 < real n + 1"
    by simp
  have e: "2 * Kn n p = interval_lebesgue_integral lborel (ereal (1 / (real n + 1))) (ereal (1 /
    (real n + 1) * (norm (fst p - snd p)) ^ 2)) (\<lambda>u. exp (- u) / u) -
    interval_lebesgue_integral lborel (ereal (real n + 1)) (ereal ((real n + 1) * (norm (fst p -
    snd p)) ^ 2)) (\<lambda>u. exp (- u) / u)" by (rule Kn_eq[OF ne])
  have hA: "\<bar>interval_lebesgue_integral lborel (ereal (1 / (real n + 1))) (ereal (1 / (real n +
    1) * (norm (fst p - snd p)) ^ 2)) (\<lambda>u. exp (- u) / u)\<bar> \<le>
    \<bar>ln ((norm (fst p - snd p)) ^ 2)\<bar>" by (rule ed_abs[OF a0 r0])
  have hB: "\<bar>interval_lebesgue_integral lborel (ereal (real n + 1)) (ereal ((real n + 1) *
    (norm (fst p - snd p)) ^ 2)) (\<lambda>u. exp (- u) / u)\<bar> \<le>
    \<bar>ln ((norm (fst p - snd p)) ^ 2)\<bar>" by (rule ed_abs[OF b0 r0])
  have lr: "ln ((norm (fst p - snd p)) ^ 2) = 2 * ln (norm (fst p - snd p))"
    by (simp add: ln_realpow)
  show "\<bar>Kn n p\<bar> \<le> 2 * \<bar>ln (norm (fst p - snd p))\<bar>" using e hA hB
    unfolding lr
    by simp
qed

lemma Kn_tendsto: "fst p \<noteq> snd p \<Longrightarrow>
  ((\<lambda>n. Kn n p) \<longlongrightarrow> ln (norm (fst p - snd p))) at_top"
proof -
  assume ne: "fst p \<noteq> snd p"
  define r where "r = (norm (fst p - snd p)) ^ 2"
  define K where "K = (\<bar>r - 1\<bar> + \<bar>r - 1\<bar> / (min 1 r) ^ 2) / 2"
  have r0: "0 < r" unfolding r_def using ne
    by simp
  have lr: "ln r = 2 * ln (norm (fst p - snd p))" unfolding r_def
    by (simp add: ln_realpow)
  have bd: "norm (Kn n p - ln (norm (fst p - snd p))) \<le> K * inverse (real (Suc n))" for n
  proof -
    have a0: "0 < 1 / (real n + 1)"
      by simp
    have b0: "0 < real n + 1"
      by simp
    have e: "2 * Kn n p = interval_lebesgue_integral lborel (ereal (1 / (real n + 1))) (ereal (1 /
      (real n + 1) * (norm (fst p - snd p)) ^ 2)) (\<lambda>u. exp (- u) / u) -
      interval_lebesgue_integral lborel (ereal (real n + 1)) (ereal ((real n + 1) * (norm (fst p -
      snd p)) ^ 2)) (\<lambda>u. exp (- u) / u)" by (rule Kn_eq[OF ne])
    have hA: "\<bar>interval_lebesgue_integral lborel (ereal (1 / (real n + 1))) (ereal (1 /
      (real n + 1) * (norm (fst p - snd p)) ^ 2)) (\<lambda>u. exp (- u) / u) - ln r\<bar> \<le>
      1 / (real n + 1) * \<bar>r - 1\<bar>" using ed_near[OF a0 r0] unfolding r_def .
    have hB: "\<bar>interval_lebesgue_integral lborel (ereal (real n + 1)) (ereal ((real n + 1) *
      (norm (fst p - snd p)) ^ 2)) (\<lambda>u. exp (- u) / u)\<bar> \<le>
      \<bar>r - 1\<bar> / ((real n + 1) * (min 1 r) ^ 2)" using ed_far[OF b0 r0] unfolding r_def .
    have "\<bar>Kn n p - ln (norm (fst p - snd p))\<bar> \<le>
      (1 / (real n + 1) * \<bar>r - 1\<bar> + \<bar>r - 1\<bar> / ((real n + 1) * (min 1 r) ^ 2)) /
      2"
      using e hA hB lr
      by argo
    also have "\<dots> = K * inverse (real (Suc n))"
    proof -
      have m: "0 < (min 1 r) ^ 2" using r0
        by simp
      have N: "inverse (real (Suc n)) = 1 / (real n + 1)"
        by (simp add: inverse_eq_divide)
      show ?thesis unfolding K_def N using m
        using field_simps by argo
    qed
    finally show ?thesis
      by simp
  qed
  have z: "((\<lambda>n. K * inverse (real (Suc n))) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult_right_zero[OF LIMSEQ_inverse_real_of_nat, of K]
    by simp
  have ev: "eventually (\<lambda>n. norm (Kn n p - ln (norm (fst p - snd p))) \<le>
    K * inverse (real (Suc n))) sequentially"
    using bd by (simp add: always_eventually)
  have "((\<lambda>n. Kn n p - ln (norm (fst p - snd p))) \<longlongrightarrow> 0) sequentially"
    using Lim_null_comparison[OF ev z] .
  thus "((\<lambda>n. Kn n p) \<longlongrightarrow> ln (norm (fst p - snd p))) sequentially"
    by (simp add: LIM_zero_iff)
qed

lemma Kn_int_P:
  fixes P :: "(complex \<times> complex) measure"
  assumes fP: "finite_measure P" and sP: "sets P = sets (borel \<Otimes>\<^sub>M borel)"
  shows "integral\<^sup>L P (Kn n) = 1 / 2 * (interval_lebesgue_integral lborel (ereal (1 /
    (real n + 1))) (ereal (real n + 1)) (\<lambda>s. exp (- s) / s) * measure P (space P) -
    integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s / s *
    integral\<^sup>L P (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2))))"
    and "integrable lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s / s *
      integral\<^sup>L P (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2)))"
proof -
  define a :: real where "a = 1 / (real n + 1)"
  define b :: real where "b = real n + 1"
  define g where "g p s = indicator {a<..<b} s * (exp (- s * (norm (fst p - snd p)) ^ 2) / s)"
    for p :: "complex \<times> complex" and s :: real
  have a0: "0 < a" unfolding a_def
    by simp
  have ab: "a \<le> b"
  proof -
    have one: "1 \<le> real n + 1"
      by simp
    have "1 / (real n + 1) \<le> 1" using one
      by simp
    thus ?thesis unfolding a_def b_def using one
      by linarith
  qed
  have H: "interval_lebesgue_integral lborel (ereal a) (ereal b) (\<lambda>s. exp (- s *
    (norm (fst p - snd p)) ^ 2) / s) = integral\<^sup>L lborel (g p)" for p
    unfolding g_def using ab
    by (simp add: interval_lebesgue_integral_le_eq set_lebesgue_integral_def)
  have Kg: "Kn n p = 1 / 2 * (interval_lebesgue_integral lborel (ereal (1 / (real n +
    1))) (ereal (real n + 1)) (\<lambda>s. exp (- s) / s) - integral\<^sup>L lborel (g p))" for p
    unfolding Kn_def H[symmetric] a_def b_def ..
  have "sigma_finite_measure P" using fP
    by (simp add: finite_measure_def)
  hence ps: "pair_sigma_finite P lborel"
    by (simp add: pair_sigma_finite_def sigma_finite_lborel)
  have gm: "(\<lambda>x. g (fst x) (snd x)) \<in> borel_measurable (P \<Otimes>\<^sub>M lborel)"
    unfolding g_def measurable_cong_sets[OF sets_pair_measure_cong[OF sP refl] refl]
    by simp
  have gb: "\<bar>g p s\<bar> \<le> indicator {a<..<b} s * (1 / a)" for p s
  proof (cases "s \<in> {a<..<b}")
    case True
    have s0: "0 < s" using True a0
      by simp
    have "exp (- s * (norm (fst p - snd p)) ^ 2) \<le> 1" using s0
      by simp
    hence "\<bar>exp (- s * (norm (fst p - snd p)) ^ 2) / s\<bar> \<le> 1 / s" using s0
      by (simp add: divide_right_mono)
    also have "1 / s \<le> 1 / a" using True a0
      by (simp add: divide_left_mono)
    finally show ?thesis unfolding g_def using True
      by simp
  next
    case False
    thus ?thesis unfolding g_def
      by simp
  qed
  have wint: "integrable (P \<Otimes>\<^sub>M lborel) (\<lambda>x. indicator {a<..<b} (snd x) * (1 /
    a))"
  proof -
    have m: "(\<lambda>x. indicator {a<..<b} (snd x) * (1 / a)) \<in>
      borel_measurable (P \<Otimes>\<^sub>M lborel)"
      unfolding measurable_cong_sets[OF sets_pair_measure_cong[OF sP refl] refl]
      by simp
    have e: "(\<integral>\<^sup>+ x. ennreal (norm (indicator {a<..<b} (snd x) * (1 /
      a))) \<partial>(P \<Otimes>\<^sub>M lborel)) =
      (\<integral>\<^sup>+ p. \<integral>\<^sup>+ s. ennreal (indicator {a<..<b} s * (1 /
      a)) \<partial>lborel \<partial>P)"
      using lborel.nn_integral_fst[of "\<lambda>x. ennreal (norm (indicator {a<..<b} (snd x) * (1 /
        a)))" P] m a0
      by (simp add: split_beta)
    have i: "(\<integral>\<^sup>+ s. ennreal (indicator {a<..<b} s * (1 / a)) \<partial>lborel) =
      ennreal (1 / a) * emeasure lborel {a<..<b}"
    proof -
      have eqf: "(\<lambda>s. ennreal (indicator {a<..<b} s * (1 / a))) =
        (\<lambda>s. ennreal (1 / a) * indicator {a<..<b} s)"
        by (simp add: fun_eq_iff indicator_def)
      show ?thesis unfolding eqf
        by (simp add: nn_integral_cmult_indicator)
    qed
    have f1: "emeasure lborel {a<..<b} \<noteq> \<infinity>"
      using ab by simp
    have f2: "emeasure P (space P) \<noteq> \<infinity>" using fP
      by (simp add: finite_measure.emeasure_finite)
    have "(\<integral>\<^sup>+ x. ennreal (norm (indicator {a<..<b} (snd x) * (1 /
      a))) \<partial>(P \<Otimes>\<^sub>M lborel)) < \<infinity>" unfolding e i using f1 f2
      by (simp add: ennreal_mult_less_top less_top)
    thus ?thesis unfolding integrable_iff_bounded using m
      by simp
  qed
  have gint: "integrable (P \<Otimes>\<^sub>M lborel) (case_prod g)"
  proof -
    have gm': "(\<lambda>(x, y). g x y) \<in> borel_measurable (P \<Otimes>\<^sub>M lborel)"
      using gm
      by (simp add: split_beta)
    have ae: "AE x in P \<Otimes>\<^sub>M lborel. norm (case x of (y, z) \<Rightarrow> g y z) \<le>
      norm (indicator {a<..<b} (snd x) * (1 / a) :: real)"
      using gb a0 by (simp add: split_beta abs_mult)
    show ?thesis using Bochner_Integration.integrable_bound[OF wint gm' ae] .
  qed
  have Fub: "integral\<^sup>L lborel (\<lambda>s. integral\<^sup>L P (\<lambda>p. g p s)) =
    integral\<^sup>L P (\<lambda>p. integral\<^sup>L lborel (g p))"
    using pair_sigma_finite.Fubini_integral[OF ps gint]
    by simp
  have Hint: "integrable P (\<lambda>p. integral\<^sup>L lborel (g p))"
    using pair_sigma_finite.integrable_fst'[OF ps gint]
    by simp
  have Sint: "integrable lborel (\<lambda>s. integral\<^sup>L P (\<lambda>p. g p s))"
    using pair_sigma_finite.integrable_snd[OF ps gint]
    by simp
  have inner: "integral\<^sup>L P (\<lambda>p. g p s) =
    indicator {a<..<b} s / s * integral\<^sup>L P (\<lambda>p. exp (- s * (norm (fst p -
    snd p)) ^ 2))" for s
    unfolding g_def
    by simp
  have ci: "integrable P (\<lambda>p. interval_lebesgue_integral lborel (ereal (1 / (real n +
    1))) (ereal (real n + 1)) (\<lambda>s. exp (- s) / s))" using fP
    by (simp add: finite_measure.integrable_const)
  show "integrable lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s / s *
    integral\<^sup>L P (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2)))" using Sint
    unfolding inner a_def b_def .
  have "integral\<^sup>L P (Kn n) = integral\<^sup>L P (\<lambda>p. 1 / 2 *
    (interval_lebesgue_integral lborel (ereal (1 / (real n + 1))) (ereal (real n +
    1)) (\<lambda>s. exp (- s) / s) - integral\<^sup>L lborel (g p)))"
    unfolding Kg ..
  also have "\<dots> = 1 / 2 * (interval_lebesgue_integral lborel (ereal (1 / (real n +
    1))) (ereal (real n + 1)) (\<lambda>s. exp (- s) / s) * measure P (space P) -
    integral\<^sup>L P (\<lambda>p. integral\<^sup>L lborel (g p)))"
    using ci Hint
    by (simp add: Bochner_Integration.integral_diff)
  finally show "integral\<^sup>L P (Kn n) =
    1 / 2 * (interval_lebesgue_integral lborel (ereal (1 / (real n + 1))) (ereal (real n +
    1)) (\<lambda>s. exp (- s) / s) * measure P (space P) -
    integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s / s *
    integral\<^sup>L P (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2))))"
    unfolding Fub[symmetric] inner a_def b_def .
qed

lemma Eform_Kn_nonpos:
  assumes "finite_measure \<nu>1" "finite_measure \<nu>2" "sets \<nu>1 = sets borel" "sets \<nu>2 =
    sets borel" "emeasure \<nu>1 UNIV = emeasure \<nu>2 UNIV"
  shows "Eform \<nu>1 \<nu>2 (Kn n) \<le> 0"
proof -
  have f11: "finite_measure (\<nu>1 \<Otimes>\<^sub>M \<nu>1)"
    using finite_measure_pair_measure[OF assms(1,1)] .
  have f12: "finite_measure (\<nu>1 \<Otimes>\<^sub>M \<nu>2)"
    using finite_measure_pair_measure[OF assms(2,1)] .
  have f22: "finite_measure (\<nu>2 \<Otimes>\<^sub>M \<nu>2)"
    using finite_measure_pair_measure[OF assms(2,2)] .
  have s11: "sets (\<nu>1 \<Otimes>\<^sub>M \<nu>1) = sets (borel \<Otimes>\<^sub>M borel)"
    using sets_pair_measure_cong[OF assms(3,3)] .
  have s12: "sets (\<nu>1 \<Otimes>\<^sub>M \<nu>2) = sets (borel \<Otimes>\<^sub>M borel)"
    using sets_pair_measure_cong[OF assms(3,4)] .
  have s22: "sets (\<nu>2 \<Otimes>\<^sub>M \<nu>2) = sets (borel \<Otimes>\<^sub>M borel)"
    using sets_pair_measure_cong[OF assms(4,4)] .
  have mP: "measure (\<mu> \<Otimes>\<^sub>M \<nu>) (space (\<mu> \<Otimes>\<^sub>M \<nu>)) =
    measure \<mu> (space \<mu>) * measure \<nu> (space \<nu>)"
    if "finite_measure \<mu>" "finite_measure \<nu>" for \<mu> \<nu> :: "complex measure"
  proof -
    have sf: "sigma_finite_measure \<nu>" using that(2)
      by (simp add: finite_measure_def)
    have "emeasure (\<mu> \<Otimes>\<^sub>M \<nu>) (space \<mu> \<times> space \<nu>) =
      emeasure \<mu> (space \<mu>) * emeasure \<nu> (space \<nu>)"
      using sigma_finite_measure.emeasure_pair_measure_Times[OF sf,
        of "space \<mu>" \<mu> "space \<nu>"]
      by simp
    thus ?thesis unfolding measure_def space_pair_measure
      by (simp add: enn2real_mult)
  qed
  have "space \<nu>1 = UNIV" using sets_eq_imp_space_eq[OF assms(3)]
    by simp
  moreover have "space \<nu>2 = UNIV" using sets_eq_imp_space_eq[OF assms(4)]
    by simp
  ultimately have m12: "measure \<nu>1 (space \<nu>1) = measure \<nu>2 (space \<nu>2)"
    using assms(5)
    by (simp add: measure_def)
  note I11 = Kn_int_P[OF f11 s11, of n] and I12 = Kn_int_P[OF f12 s12, of n] and I22 =
    Kn_int_P[OF f22 s22, of n]
  have nn: "0 \<le> integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n +
    1} s / s * (integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) (\<lambda>p. exp (- s *
    (norm (fst p - snd p)) ^ 2)) - 2 * integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2)
    (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2)) +
    integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s * (norm (fst p -
    snd p)) ^ 2))))"
  proof (rule Bochner_Integration.integral_nonneg)
    fix s :: real
    show "0 \<le> indicator {1 / (real n + 1)<..<real n + 1} s / s *
      (integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) (\<lambda>p. exp (- s * (norm (fst p -
      snd p)) ^ 2)) - 2 * integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s *
      (norm (fst p - snd p)) ^ 2)) + integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p.
      exp (- s * (norm (fst p - snd p)) ^ 2)))"
    proof (cases "s \<in> {1 / (real n + 1)<..<real n + 1}")
      case True
      have p0: "0 < 1 / (real n + 1)"
        by simp
      have "1 / (real n + 1) < s" using True
        by (simp add: greaterThanLessThan_iff)
      hence s0: "0 < s" using p0
        by linarith
      have "0 \<le> Eform \<nu>1 \<nu>2 (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2))"
        by (rule Eform_gauss_nonneg[OF assms(1-4) s0])
      thus ?thesis unfolding Eform_def using s0 True
        by simp
    next
      case False
      thus ?thesis
        by simp
    qed
  qed
  have split: "integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s /
    s * integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) (\<lambda>p. exp (- s * (norm (fst p -
    snd p)) ^ 2))) - 2 * integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n +
    1)<..<real n + 1} s / s * integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (-
    s * (norm (fst p - snd p)) ^ 2))) + integral\<^sup>L lborel (\<lambda>s. indicator {1 /
    (real n + 1)<..<real n + 1} s / s * integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2)
    (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2)))
      = integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s / s *
        (integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) (\<lambda>p. exp (- s * (norm (fst p -
        snd p)) ^ 2)) - 2 * integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s
        * (norm (fst p - snd p)) ^ 2)) +
        integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s * (norm (fst p -
        snd p)) ^ 2))))"
  proof -
    have a: "integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s / s *
      integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) (\<lambda>p. exp (- s * (norm (fst p -
      snd p)) ^ 2)) - 2 * (indicator {1 / (real n + 1)<..<real n + 1} s / s *
      integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s * (norm (fst p -
      snd p)) ^ 2))) + indicator {1 / (real n + 1)<..<real n + 1} s / s *
      integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s * (norm (fst p -
      snd p)) ^ 2))) = integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n +
      1} s / s * integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) (\<lambda>p. exp (- s *
      (norm (fst p - snd p)) ^ 2))) - 2 * integral\<^sup>L lborel (\<lambda>s. indicator {1 /
      (real n + 1)<..<real n + 1} s / s *
      integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s * (norm (fst p -
      snd p)) ^ 2))) + integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n +
      1} s / s * integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s *
      (norm (fst p - snd p)) ^ 2)))"
      using Bochner_Integration.integral_add[OF Bochner_Integration.integrable_diff[OF I11(2)
        integrable_mult_right[where c = 2, OF I12(2)]] I22(2)]
        Bochner_Integration.integral_diff[OF I11(2) integrable_mult_right[where c = 2, OF I12(2)]]
        Bochner_Integration.integral_mult_right[where c = 2, OF I12(2)] by simp
    have b: "(\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s / s *
      integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) (\<lambda>p. exp (- s * (norm (fst p -
      snd p)) ^ 2)) - 2 * (indicator {1 / (real n + 1)<..<real n + 1} s / s *
      integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s * (norm (fst p -
      snd p)) ^ 2))) + indicator {1 / (real n + 1)<..<real n + 1} s / s *
      integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s * (norm (fst p -
      snd p)) ^ 2))) = (\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s / s *
      (integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) (\<lambda>p. exp (- s * (norm (fst p -
      snd p)) ^ 2)) - 2 * integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s *
      (norm (fst p - snd p)) ^ 2)) + integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p.
      exp (- s * (norm (fst p - snd p)) ^ 2))))"
      by (simp add: fun_eq_iff algebra_simps)
    show ?thesis using a unfolding b by simp
  qed
  have "Eform \<nu>1 \<nu>2 (Kn n) = - 1 / 2 * (integral\<^sup>L lborel (\<lambda>s. indicator {1 /
    (real n + 1)<..<real n + 1} s / s * integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1)
    (\<lambda>p. exp (- s * (norm (fst p - snd p)) ^ 2))) - 2 *
    integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n + 1} s / s *
    integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s * (norm (fst p -
    snd p)) ^ 2))) + integral\<^sup>L lborel (\<lambda>s. indicator {1 / (real n + 1)<..<real n +
    1} s / s * integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. exp (- s *
    (norm (fst p - snd p)) ^ 2))))"
    unfolding Eform_def I11(1) I12(1) I22(1) mP[OF assms(1,1)] mP[OF assms(1,2)] mP[OF assms(2,2)]
      m12
    by (simp add: algebra_simps)
  thus ?thesis unfolding split using nn
    by simp
qed

text \<open>Integrability passes to a smaller measure with the same sets.\<close>
lemma integrable_le_measure:
  fixes f :: "'a \<Rightarrow> real"
  assumes PQ: "P \<le> Q" and s: "sets P = sets Q" and fi: "integrable Q f"
  shows "integrable P f"
proof -
  have m: "f \<in> borel_measurable P" using borel_measurable_integrable[OF fi]
    measurable_cong_sets[OF s refl]
    by auto
  have le: "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>P) \<le>
    (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>Q)"
    using nn_integral_mono_measure[OF s PQ]
    by simp
  have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>Q) < \<infinity>" using fi
    unfolding integrable_iff_bounded
    by simp
  thus ?thesis using m le unfolding integrable_iff_bounded
    by simp
qed

lemma Kn_meas: "Kn n \<in> borel_measurable (borel \<Otimes>\<^sub>M borel :: (complex \<times>
  complex) measure)"
  unfolding Kn_def interval_lebesgue_integral_def set_lebesgue_integral_def
  by simp

text \<open>Dominated convergence: @{text "\<integral> K_n dP \<longrightarrow>
  \<integral> log|p_1 - p_2| dP"} for @{text "P \<le>
  Q"} with @{text log} @{text Q}-integrable and the diagonal @{text Q}-null.\<close>
lemma Kn_integral_tendsto:
  assumes "P \<le> Q" "sets P = sets (borel \<Otimes>\<^sub>M borel)" "sets Q =
    sets (borel \<Otimes>\<^sub>M borel)"
    and "integrable Q (\<lambda>p :: complex \<times> complex. ln (norm (fst p -
      snd p)))" "emeasure Q {p. fst p = snd p} = 0"
  shows "((\<lambda>n. integral\<^sup>L P (Kn n)) \<longlongrightarrow> integral\<^sup>L P
    (\<lambda>p. ln (norm (fst p - snd p)))) at_top"
proof -
  define D where "D = {p :: complex \<times> complex. fst p = snd p}"
  have sPQ: "sets P = sets Q" using assms(2,3) by simp
  have mf: "(\<lambda>p :: complex \<times> complex. fst p - snd p) \<in>
    borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by simp
  have eq: "{p :: complex \<times> complex. fst p = snd p} =
    (\<lambda>p. fst p - snd p) -` {0} \<inter> space (borel \<Otimes>\<^sub>M borel)"
    by (auto simp: space_pair_measure)
  have Dm: "D \<in> sets P" unfolding D_def assms(2) eq using measurable_sets[OF mf, of "{0}"]
    by simp
  have "emeasure P D = 0" using le_measureD3[OF assms(1) sPQ, of D] assms(5) unfolding D_def
    by simp
  hence ns: "D \<in> null_sets P" using Dm
    by (simp add: null_sets_def)
  have AE_off: "AE p in P. fst p \<noteq> snd p"
    using AE_I'[OF ns, of "\<lambda>p. fst p \<noteq> snd p"] unfolding D_def
    by auto
  have intQ: "integrable Q (\<lambda>p. 2 * \<bar>ln (norm (fst p - snd p))\<bar>)" using assms(4)
    by simp
  have intP: "integrable P (\<lambda>p. 2 * \<bar>ln (norm (fst p - snd p))\<bar>)"
    by (rule integrable_le_measure[OF assms(1) sPQ intQ])
  have fm: "(\<lambda>p. ln (norm (fst p - snd p))) \<in> borel_measurable P"
    using borel_measurable_integrable[OF integrable_le_measure[OF assms(1) sPQ assms(4)]] .
  have sm: "Kn n \<in> borel_measurable P" for n
    using Kn_meas[of n] measurable_cong_sets[OF assms(2) refl]
    by auto
  have lim: "AE p in P. (\<lambda>n. Kn n p) \<longlonglongrightarrow> ln (norm (fst p - snd p))"
    using AE_off Kn_tendsto
    by (auto elim: AE_mp)
  have bd: "AE p in P. norm (Kn n p) \<le> 2 * \<bar>ln (norm (fst p - snd p))\<bar>" for n
    using AE_off Kn_bound
    by (auto elim: AE_mp)
  show ?thesis by (rule integral_dominated_convergence[OF fm sm intP lim bd])
qed

lemma finite_le_measure:
  assumes "\<nu> \<le> \<eta>" "sets \<nu> = sets \<eta>" "finite_measure \<eta>"
  shows "finite_measure \<nu>"
proof (rule finite_measureI)
  have fe: "emeasure \<eta> (space \<eta>) \<noteq> \<infinity>" using assms(3)
    by (simp add: finite_measure.emeasure_finite)
  have le: "emeasure \<nu> (space \<nu>) \<le> emeasure \<eta> (space \<nu>)"
    using le_measureD3[OF assms(1,2)] .
  have sp: "space \<nu> = space \<eta>" using sets_eq_imp_space_eq[OF assms(2)] .
  show "emeasure \<nu> (space \<nu>) \<noteq> \<infinity>" using le fe unfolding sp
    by (auto simp: top.extremum_unique)
qed

lemma pair_measure_mono:
  assumes "\<nu> \<le> \<eta>" "\<nu>' \<le> \<eta>" "sets \<nu> = sets borel" "sets \<nu>' =
    sets borel" "sets \<eta> = sets borel" "finite_measure \<eta>"
  shows "(\<nu> \<Otimes>\<^sub>M \<nu>') \<le> (\<eta> \<Otimes>\<^sub>M \<eta>)"
proof -
  have s1: "sets (\<nu> \<Otimes>\<^sub>M \<nu>') = sets (\<eta> \<Otimes>\<^sub>M \<eta>)"
    using assms(3,4,5)
    using sets_pair_measure_cong by simp
  have sp: "space (\<nu> \<Otimes>\<^sub>M \<nu>') = space (\<eta> \<Otimes>\<^sub>M \<eta>)"
    using sets_eq_imp_space_eq[OF s1] .
  have "finite_measure \<nu>'" using finite_le_measure[OF assms(2) _ assms(6)] assms(4,5)
    by simp
  hence sfn': "sigma_finite_measure \<nu>'"
    by (simp add: finite_measure_def)
  have sfe: "sigma_finite_measure \<eta>" using assms(6)
    by (simp add: finite_measure_def)
  have em: "emeasure (\<nu> \<Otimes>\<^sub>M \<nu>') X \<le>
    emeasure (\<eta> \<Otimes>\<^sub>M \<eta>) X" for X
  proof (cases "X \<in> sets (\<nu> \<Otimes>\<^sub>M \<nu>')")
    case True
    have X2: "X \<in> sets (\<eta> \<Otimes>\<^sub>M \<eta>)" using True s1
      by simp
    have "emeasure (\<nu> \<Otimes>\<^sub>M \<nu>') X =
      (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator X (x,
      y) \<partial>\<nu>' \<partial>\<nu>)"
      using sigma_finite_measure.emeasure_pair_measure[OF sfn' True] .
    also have "\<dots> \<le> (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator X (x,
      y) \<partial>\<eta> \<partial>\<nu>)"
      using nn_integral_mono_measure[of \<nu>' \<eta>] assms(2,4,5)
      by (auto intro: nn_integral_mono)
    also have "\<dots> \<le> (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator X (x,
      y) \<partial>\<eta> \<partial>\<eta>)"
      using nn_integral_mono_measure[of \<nu> \<eta>] assms(1,3,5)
      using nn_integral_mono by simp
    also have "\<dots> = emeasure (\<eta> \<Otimes>\<^sub>M \<eta>) X"
      using sigma_finite_measure.emeasure_pair_measure[OF sfe X2]
      by simp
    finally show ?thesis .
  next
    case False
    have "emeasure (\<nu> \<Otimes>\<^sub>M \<nu>') X = 0" using False
      by (simp add: emeasure_notin_sets)
    thus ?thesis
      by simp
  qed
  show ?thesis unfolding le_measure_iff using s1 sp em
    by (simp add: le_fun_def)
qed

lemma logEnergyC_prod:
  fixes \<mu> \<nu> :: "complex measure"
  assumes fm: "finite_measure \<mu>" and fn: "finite_measure \<nu>" and int: "integrable (\<mu>
    \<Otimes>\<^sub>M \<nu>) (\<lambda>p. ln (norm (fst p - snd p)))"
  shows "logEnergyC \<mu> \<nu> = integral\<^sup>L (\<mu> \<Otimes>\<^sub>M \<nu>) (\<lambda>p. ln
    (norm (fst p - snd p)))"
proof -
  have ps: "pair_sigma_finite \<mu> \<nu>" using fm fn
    by (simp add: pair_sigma_finite_def finite_measure_def)
  show ?thesis unfolding logEnergyC_def using pair_sigma_finite.integral_fst'[OF ps int]
    by simp
qed

theorem log_energy_zero_mass_nonpos:
  fixes \<nu>1 \<nu>2 \<eta> :: "complex measure"
  assumes "finite_measure \<eta>" "sets \<nu>1 = sets borel" "sets \<nu>2 =
    sets borel" "sets \<eta> = sets borel"
    and "\<nu>1 \<le> \<eta>" "\<nu>2 \<le> \<eta>" "emeasure \<nu>1 UNIV = emeasure \<nu>2 UNIV"
    and "integrable (\<eta> \<Otimes>\<^sub>M \<eta>) (\<lambda>zw. ln (norm (fst zw - snd zw)))"
    and "emeasure (\<eta> \<Otimes>\<^sub>M \<eta>) {zw. fst zw = snd zw} = 0"
  shows "logEnergyC \<nu>1 \<nu>1 - 2 * logEnergyC \<nu>1 \<nu>2 + logEnergyC \<nu>2 \<nu>2 \<le> 0"
proof -
  have f1: "finite_measure \<nu>1" and f2: "finite_measure \<nu>2"
  proof -
    have fe: "emeasure \<eta> (space \<eta>) \<noteq> \<infinity>" using assms(1)
      by (simp add: finite_measure.emeasure_finite)
    show "finite_measure \<nu>1"
    proof (rule finite_measureI)
      have le: "emeasure \<nu>1 (space \<nu>1) \<le> emeasure \<eta> (space \<nu>1)"
        using le_measureD3[OF assms(5)] assms(2,4)
        by simp
      have sp: "space \<nu>1 = space \<eta>" using sets_eq_imp_space_eq assms(2,4)
        by auto
      show "emeasure \<nu>1 (space \<nu>1) \<noteq> \<infinity>" using le fe unfolding sp
        by (auto simp: top.extremum_unique)
    qed
    show "finite_measure \<nu>2"
    proof (rule finite_measureI)
      have le: "emeasure \<nu>2 (space \<nu>2) \<le> emeasure \<eta> (space \<nu>2)"
        using le_measureD3[OF assms(6)] assms(3,4)
        by simp
      have sp: "space \<nu>2 = space \<eta>" using sets_eq_imp_space_eq assms(3,4)
        by auto
      show "emeasure \<nu>2 (space \<nu>2) \<noteq> \<infinity>" using le fe unfolding sp
        by (auto simp: top.extremum_unique)
    qed
  qed
  have E: "logEnergyC \<nu>1 \<nu>1 - 2 * logEnergyC \<nu>1 \<nu>2 + logEnergyC \<nu>2 \<nu>2 =
    Eform \<nu>1 \<nu>2 (\<lambda>p. ln (norm (fst p - snd p)))"
  proof -
    have i: "integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (\<lambda>p. ln (norm (fst p - snd p)))"
      if "\<mu> \<le> \<eta>" "\<nu> \<le> \<eta>" "sets \<mu> = sets borel" "sets \<nu> =
      sets borel" for \<mu> \<nu> :: "complex measure"
    proof (rule integrable_le_measure[OF pair_measure_mono[OF that assms(4,1)] _ assms(8)])
      show "sets (\<mu> \<Otimes>\<^sub>M \<nu>) = sets (\<eta> \<Otimes>\<^sub>M \<eta>)"
        using that assms(4)
        using sets_pair_measure_cong by simp
    qed
    have e11: "logEnergyC \<nu>1 \<nu>1 =
      integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>1) (\<lambda>p. ln (norm (fst p - snd p)))"
      by (rule logEnergyC_prod[OF f1 f1 i[OF assms(5,5,2,2)]])
    have e12: "logEnergyC \<nu>1 \<nu>2 =
      integral\<^sup>L (\<nu>1 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. ln (norm (fst p - snd p)))"
      by (rule logEnergyC_prod[OF f1 f2 i[OF assms(5,6,2,3)]])
    have e22: "logEnergyC \<nu>2 \<nu>2 =
      integral\<^sup>L (\<nu>2 \<Otimes>\<^sub>M \<nu>2) (\<lambda>p. ln (norm (fst p - snd p)))"
      by (rule logEnergyC_prod[OF f2 f2 i[OF assms(6,6,3,3)]])
    show ?thesis unfolding e11 e12 e22 Eform_def ..
  qed
  have lim: "((\<lambda>n. Eform \<nu>1 \<nu>2 (Kn n)) \<longlongrightarrow> Eform \<nu>1 \<nu>2
    (\<lambda>p. ln (norm (fst p - snd p)))) at_top"
    unfolding Eform_def
    by (intro tendsto_intros Kn_integral_tendsto[OF pair_measure_mono[OF _ _ _ _ assms(4,1)]] assms)
      (simp_all add: assms sets_pair_measure)
  have nonpos: "\<And>n. Eform \<nu>1 \<nu>2 (Kn n) \<le> 0"
    by (rule Eform_Kn_nonpos[OF f1 f2 assms(2,3,7)])
  show ?thesis unfolding E by (rule tendsto_upperbound[OF lim]) (simp_all add: nonpos)
qed

end
