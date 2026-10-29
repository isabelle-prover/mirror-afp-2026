(*  Title:   Interval_Integral_Substitutions.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Interval_Integral_Substitutions
  imports "HOL-Analysis.Analysis"
begin

section \<open>Substitutions in interval integrals with finite endpoints\<close>

text \<open>Affine changes of variable and reflections
  for @{const interval_lebesgue_integral} with explicit
  endpoints (HOL-Analysis has the whole-line @{thm [source] lborel_integral_real_affine} and the
  monotone-substitution rules), restriction of integrability to a subinterval, joining of adjacent
  intervals, and the invariance \<open>\<integral>\<^sub>0\<^sup>2\<^sup>\<pi> g(x - \<phi>) dx =
    \<integral>\<^sub>0\<^sup>2\<^sup>\<pi> g\<close> of a \<open>2\<pi>\<close>-periodic
    integrand.\<close>

text \<open>Affine changes of variable in interval integrals with finite endpoints.\<close>
lemma LBINT_affine_ind:
  fixes a b c t x :: real
  assumes c: "0 < c"
  shows "indicator {a<..<b} (t + c * x) = (indicator {(a - t) / c<..<(b - t) / c} x :: real)"
proof -
  have "(t + c * x \<in> {a<..<b}) = (x \<in> {(a - t) / c<..<(b - t) / c})" using c
    by (simp add: field_simps)
  thus ?thesis
    by (simp add: indicator_def)
qed

lemma LBINT_reflect_ind:
  fixes a b t x :: real
  shows "indicator {a<..<b} (t + (- 1) * x) = (indicator {t - b<..<t - a} x :: real)"
proof -
  have "(t + (- 1) * x \<in> {a<..<b}) = (x \<in> {t - b<..<t - a})"
    by auto
  thus ?thesis
    by (simp add: indicator_def)
qed

lemma LBINT_reflect:
  fixes f :: "real \<Rightarrow> real" and a b t :: real
  assumes ab: "a \<le> b"
  shows "interval_lebesgue_integral lborel (ereal a) (ereal b) f
         = interval_lebesgue_integral lborel (ereal (t - b)) (ereal (t - a)) (\<lambda>x. f (t -
           x))"
proof -
  have ab': "t - b \<le> t - a" using ab by simp
  have e: "(\<lambda>x. indicator {a<..<b} (t + (- 1) * x) * f (t + (- 1) * x)) =
    (\<lambda>x. indicator {t - b<..<t - a} x * f (t - x))"
    using LBINT_reflect_ind
    by simp
  have e1: "interval_lebesgue_integral lborel (ereal a) (ereal b) f =
    (\<integral>x. indicator {a<..<b} x * f x \<partial>lborel)"
    using ab
    by (simp add: interval_lebesgue_integral_def set_lebesgue_integral_def)
  have e2: "(\<integral>x. indicator {a<..<b} x * f x \<partial>lborel) =
    (\<integral>x. indicator {a<..<b} (t + (- 1) * x) * f (t + (- 1) * x) \<partial>lborel)"
    using lborel_integral_real_affine[of "- 1" "\<lambda>x. indicator {a<..<b} x * f x" t]
    by simp
  have e4: "(\<integral>x. indicator {t - b<..<t - a} x * f (t - x) \<partial>lborel) =
    interval_lebesgue_integral lborel (ereal (t - b)) (ereal (t - a)) (\<lambda>x. f (t - x))"
    using ab'
    by (simp add: interval_lebesgue_integral_def set_lebesgue_integral_def)
  show ?thesis using e1 e2 e4 unfolding e
    by presburger
qed

lemma LBINT_reflect_int:
  fixes f :: "real \<Rightarrow> real" and a b t :: real
  assumes ab: "a \<le> b"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal b) f
         \<longleftrightarrow> interval_lebesgue_integrable lborel (ereal (t - b)) (ereal (t -
           a)) (\<lambda>x. f (t - x))"
proof -
  have ab': "t - b \<le> t - a" using ab by simp
  have e: "(\<lambda>x. indicator {a<..<b} (t + (- 1) * x) * f (t + (- 1) * x)) =
    (\<lambda>x. indicator {t - b<..<t - a} x * f (t - x))"
    using LBINT_reflect_ind
    by simp
  have e1: "interval_lebesgue_integrable lborel (ereal a) (ereal b) f \<longleftrightarrow>
    integrable lborel (\<lambda>x. indicator {a<..<b} x * f x)"
    using ab
    by (simp add: interval_lebesgue_integrable_def set_integrable_def)
  have e2: "integrable lborel (\<lambda>x. indicator {a<..<b} x * f x) \<longleftrightarrow>
    integrable lborel (\<lambda>x. indicator {a<..<b} (t + (- 1) * x) * f (t + (- 1) * x))"
    using lborel_integrable_real_affine_iff[of "- 1" "\<lambda>x. indicator {a<..<b} x * f x" t]
    by argo
  have e4: "integrable lborel (\<lambda>x. indicator {t - b<..<t - a} x * f (t -
    x)) \<longleftrightarrow> interval_lebesgue_integrable lborel (ereal (t - b)) (ereal (t -
    a)) (\<lambda>x. f (t - x))"
    using ab'
    by (simp add: interval_lebesgue_integrable_def set_integrable_def)
  show ?thesis using e1 e2 e4 unfolding e
    by meson
qed

lemma LBINT_affine_int:
  fixes f :: "real \<Rightarrow> real" and a b c t :: real
  assumes c: "0 < c" and ab: "a \<le> b"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal b) f
         \<longleftrightarrow> interval_lebesgue_integrable lborel (ereal ((a - t) /
           c)) (ereal ((b - t) / c)) (\<lambda>x. f (t + c * x))"
proof -
  have ab': "(a - t) / c \<le> (b - t) / c" using ab c
    by (fastforce intro: divide_right_mono)
  have "interval_lebesgue_integrable lborel (ereal a) (ereal b) f \<longleftrightarrow>
    integrable lborel (\<lambda>x. indicator {a<..<b} x * f x)"
    using ab
    by (simp add: interval_lebesgue_integrable_def set_integrable_def)
  also have "\<dots> \<longleftrightarrow>
    integrable lborel (\<lambda>x. indicator {a<..<b} (t + c * x) * f (t + c * x))"
    using lborel_integrable_real_affine_iff[of c "\<lambda>x. indicator {a<..<b} x * f x" t] c
    by fastforce
  also have "\<dots> \<longleftrightarrow>
    integrable lborel (\<lambda>x. indicator {(a - t) / c<..<(b - t) / c} x * f (t + c * x))"
    using LBINT_affine_ind[OF c]
    by presburger
  also have "\<dots> \<longleftrightarrow>
    interval_lebesgue_integrable lborel (ereal ((a - t) / c)) (ereal ((b - t) /
    c)) (\<lambda>x. f (t + c * x))"
    using ab'
    by (auto simp: interval_lebesgue_integrable_def set_integrable_def)
  finally show ?thesis .
qed

lemma LBINT_affine:
  fixes f :: "real \<Rightarrow> real" and a b c t :: real
  assumes c: "0 < c" and ab: "a \<le> b"
  shows "interval_lebesgue_integral lborel (ereal a) (ereal b) f
         = c * interval_lebesgue_integral lborel (ereal ((a - t) / c)) (ereal ((b - t) /
           c)) (\<lambda>x. f (t + c * x))"
proof -
  have ab': "(a - t) / c \<le> (b - t) / c" using ab c
    by (auto intro: divide_right_mono)
  have "interval_lebesgue_integral lborel (ereal a) (ereal b) f =
    (\<integral>x. indicator {a<..<b} x * f x \<partial>lborel)"
    using ab
    by (simp add: interval_lebesgue_integral_def set_lebesgue_integral_def)
  also have "\<dots> = c * (\<integral>x. indicator {a<..<b} (t + c * x) * f (t + c *
    x) \<partial>lborel)"
    using lborel_integral_real_affine[of c "\<lambda>x. indicator {a<..<b} x * f x" t] c
    by simp
  also have "(\<integral>x. indicator {a<..<b} (t + c * x) * f (t + c * x) \<partial>lborel) =
    (\<integral>x. indicator {(a - t) / c<..<(b - t) / c} x * f (t + c * x) \<partial>lborel)"
    using LBINT_affine_ind[OF c]
    by simp
  also have "\<dots> = interval_lebesgue_integral lborel (ereal ((a - t) / c)) (ereal ((b - t) /
    c)) (\<lambda>x. f (t + c * x))"
    using ab'
    by (simp add: interval_lebesgue_integral_def set_lebesgue_integral_def)
  finally show ?thesis .
qed


lemma interval_integrable_sub:
  fixes f :: "real \<Rightarrow> real" and a b c d :: real
  assumes "a \<le> c" "c \<le> d" "d \<le>
    b" "interval_lebesgue_integrable lborel (ereal a) (ereal b) f"
  shows "interval_lebesgue_integrable lborel (ereal c) (ereal d) f"
proof -
  have s: "set_integrable lborel {a<..<b} f" using assms unfolding interval_lebesgue_integrable_def
    by simp
  have "set_integrable lborel {c<..<d} f" using set_integrable_subset[OF s, of "{c<..<d}"] assms
    by fastforce
  thus ?thesis using assms unfolding interval_lebesgue_integrable_def
    by simp
qed

lemma interval_integrable_join:
  fixes f :: "real \<Rightarrow> real" and a b c :: real
  assumes ab: "a \<le> b" and bc: "b \<le> c"
    and i1: "interval_lebesgue_integrable lborel (ereal a) (ereal b) f"
    and i2: "interval_lebesgue_integrable lborel (ereal b) (ereal c) f"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal c) f"
proof -
  have s1: "set_integrable lborel {a<..<b} f" using i1 ab
    unfolding interval_lebesgue_integrable_def by simp
  have s2: "set_integrable lborel {b<..<c} f" using i2 bc
    unfolding interval_lebesgue_integrable_def by simp
  have u: "set_integrable lborel ({a<..<b} \<union> {b<..<c}) f" using set_integrable_Un[OF s1 s2]
    by simp
  have "set_integrable lborel {a<..<c} f"
    using set_integrable_discrete_difference[where X="{b}" and A="{a<..<b} \<union> {b<..<c}" and
      B="{a<..<c}" and M=lborel and f=f] u ab bc
    by fastforce
  thus ?thesis using ab bc unfolding interval_lebesgue_integrable_def
    by simp
qed

lemma periodic_shift_fun:
  fixes g :: "real \<Rightarrow> real" and \<phi> :: real
  assumes per: "\<And>x. g (x + 2 * pi) = g x"
  shows "(\<lambda>x. g (x - \<phi>)) = (\<lambda>x. g (2 * pi - \<phi> + 1 * x))"
proof
  fix x
  have "g (x - \<phi>) = g (x - \<phi> + 2 * pi)" using per[of "x - \<phi>"] by simp
  thus "g (x - \<phi>) = g (2 * pi - \<phi> + 1 * x)"
    by (simp add: algebra_simps)
qed

lemma periodic_shift_int:
  fixes g :: "real \<Rightarrow> real" and \<phi> :: real
  assumes per: "\<And>x. g (x + 2 * pi) = g x"
    and ig: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 * pi)) g"
    and p0: "0 \<le> \<phi>" "\<phi> \<le> 2 * pi"
  shows "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 * pi)) (\<lambda>x. g (x -
    \<phi>))"
proof -
  have a1: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 * pi - \<phi>)) g"
    using interval_integrable_sub[OF _ _ _ ig, of 0 "2 * pi - \<phi>"] p0
    by simp
  have i1: "interval_lebesgue_integrable lborel (ereal \<phi>) (ereal (2 * pi)) (\<lambda>x. g (x -
    \<phi>))"
    using a1 LBINT_affine_int[of 1 0 "2 * pi - \<phi>" g "- \<phi>"] p0
    by simp
  have a2: "interval_lebesgue_integrable lborel (ereal (2 * pi - \<phi>)) (ereal (2 * pi)) g"
    using interval_integrable_sub[OF _ _ _ ig, of "2 * pi - \<phi>" "2 * pi"] p0
    by simp
  have i2: "interval_lebesgue_integrable lborel (ereal 0) (ereal \<phi>) (\<lambda>x. g (x -
    \<phi>))"
    using a2 LBINT_affine_int[of 1 "2 * pi - \<phi>" "2 * pi" g "2 * pi - \<phi>"] p0
      unfolding periodic_shift_fun[of g \<phi>, OF per]
    by simp
  show ?thesis using interval_integrable_join[OF p0(1) p0(2) i2 i1] .
qed

lemma periodic_shift_eq:
  fixes g :: "real \<Rightarrow> real" and \<phi> :: real
  assumes per: "\<And>x. g (x + 2 * pi) = g x"
    and ig: "interval_lebesgue_integrable lborel (ereal 0) (ereal (2 * pi)) g"
    and p0: "0 \<le> \<phi>" "\<phi> \<le> 2 * pi"
  shows "interval_lebesgue_integral lborel (ereal (0)) (ereal (2 * pi)) (\<lambda>x. g (x -
    \<phi>)) = interval_lebesgue_integral lborel (ereal (0)) (ereal (2 * pi)) g"
proof -
  have "interval_lebesgue_integral lborel (ereal (0)) (ereal (\<phi>)) (\<lambda>x. g (x -
    \<phi>)) + interval_lebesgue_integral lborel (ereal (\<phi>)) (ereal (2 *
    pi)) (\<lambda>x. g (x - \<phi>)) = interval_lebesgue_integral lborel (ereal (0)) (ereal (2 *
    pi)) (\<lambda>x. g (x - \<phi>))"
    using interval_integral_sum[of "ereal 0" "ereal \<phi>" "ereal (2 * pi)" "\<lambda>x. g (x -
      \<phi>)"] periodic_shift_int[OF per ig p0] p0
    by simp
  moreover have "interval_lebesgue_integral lborel (ereal (\<phi>)) (ereal (2 *
    pi)) (\<lambda>x. g (x - \<phi>)) = interval_lebesgue_integral lborel (ereal (0)) (ereal (2 *
    pi - \<phi>)) g"
    using LBINT_affine[of 1 0 "2 * pi - \<phi>" g "- \<phi>"] p0
    by simp
  moreover have "interval_lebesgue_integral lborel (ereal (0)) (ereal (\<phi>)) (\<lambda>x. g (x -
    \<phi>)) = interval_lebesgue_integral lborel (ereal (2 * pi - \<phi>)) (ereal (2 * pi)) g"
    using LBINT_affine[of 1 "2 * pi - \<phi>" "2 * pi" g "2 * pi - \<phi>"] p0
      unfolding periodic_shift_fun[of g \<phi>, OF per]
    by simp
  moreover have "interval_lebesgue_integral lborel (ereal (0)) (ereal (2 * pi - \<phi>)) g +
    interval_lebesgue_integral lborel (ereal (2 * pi - \<phi>)) (ereal (2 * pi)) g =
    interval_lebesgue_integral lborel (ereal (0)) (ereal (2 * pi)) g"
    using interval_integral_sum[of "ereal 0" "ereal (2 * pi - \<phi>)" "ereal (2 * pi)" g] ig p0
    by simp
  ultimately show ?thesis by linarith
qed

end
