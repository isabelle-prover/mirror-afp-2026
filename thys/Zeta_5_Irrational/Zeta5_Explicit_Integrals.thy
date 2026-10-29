(*  Title:   Zeta5_Explicit_Integrals.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Explicit_Integrals
  imports Zeta5_Definitions Piecewise_Interval_Integrals
begin

section \<open>The explicit integrals of Section 5\<close>

text \<open>The closed form \<open>R(x) = x F(x) + Q(x)\<close> with \<open>-1/2 \<le> Q \<le>
  13/8\<close> ((B.1), (5.13)), the exact integrals
  (5.10) and (5.18) as sums of affine pieces (the piece lemmas are generated from exact rational
  tables, mirroring the generated Lean files), the tails (5.14)--(5.17), and continuity of the
  limiting functions off a countable set.  All integrals are @{const interval_lebesgue_integral}
  over @{const lborel}.  Lean theories @{text Integrals5Base}, @{text Integrals5Gam},
  @{text Integrals5}, @{text Integrals5Outer}, @{text Integrals5Inner}, @{text Integrals5Tail},
  @{text RCont}.\<close>

subsection \<open>The closed form @{text "R(x) = x F(x) + Q(x)"} (B.1), (5.13)\<close>

definition ind :: "real \<Rightarrow> real \<Rightarrow> real" where "ind p z = (if p <
  z then 1 else 0)"
definition d0 :: "real \<Rightarrow> real" where "d0 u = min u (1 - u)"
definition es :: "real \<Rightarrow> real" where "es u = (if u \<le> 1 / 2 then 1 else - 1)"

lemma ind_of_lt: "p < z \<Longrightarrow> ind p z = 1" and ind_of_le: "z \<le> p \<Longrightarrow>
  ind p z = 0"
  by (simp_all add: ind_def)

lemma es_cases: "(es u = 1 \<and> d0 u = u) \<or> (es u = - 1 \<and> d0 u = 1 - u)"
  unfolding es_def d0_def by (cases "u \<le> 1 / 2") (auto simp: min_def)

lemma d0_mem: "0 \<le> u \<Longrightarrow> u \<le> 1 \<Longrightarrow> 0 \<le> d0 u \<and>
  d0 u \<le> 1 / 2"
  unfolding d0_def by (auto simp: min_def)

lemma es_pm: "es u = 1 \<or> es u = - 1"
  by (simp add: es_def)

text \<open>Integral over @{text "(0, 1/2)"} of a product of two step functions with steps at
  @{text p} and @{text q}.\<close>
lemma step3:
  fixes h :: "real \<Rightarrow> real"
  assumes p: "0 \<le> p" "p \<le> 1 / 2" and q: "0 \<le> q" "q \<le> 1 / 2"
    and H: "\<And>z. z \<in> {0<..<1 / 2} \<Longrightarrow> z \<noteq> p \<Longrightarrow>
      z \<noteq> q \<Longrightarrow>
              h z = (a0 + a1 * ind q z) * (b0 + b1 * ind q z + b2 * ind p z)"
  shows "interval_lebesgue_integral lborel (ereal 0) (ereal (1 / 2)) h
           = a0 * b0 / 2 + (a0 * b1 + a1 * b0 + a1 * b1) * (1 / 2 - q) + a0 * b2 * (1 / 2 - p) +
             a1 * b2 * (1 / 2 - max p q)"
proof (cases "p \<le> q")
  case True
  have e1: "interval_lebesgue_integrable lborel (ereal 0) (ereal p) h \<and>
    interval_lebesgue_integral lborel (ereal 0) (ereal p) h = (p - 0) * (a0 * b0)"
    by (rule const_piece[OF p(1)]) (use True q H in \<open>auto simp: ind_def\<close>)
  have e2: "interval_lebesgue_integrable lborel (ereal p) (ereal q) h \<and>
    interval_lebesgue_integral lborel (ereal p) (ereal q) h = (q - p) * (a0 * (b0 + b2))"
    by (rule const_piece[OF True]) (use p q H in \<open>auto simp: ind_def\<close>)
  have e3: "interval_lebesgue_integrable lborel (ereal q) (ereal (1 / 2)) h \<and>
    interval_lebesgue_integral lborel (ereal q) (ereal (1 / 2)) h =
    (1 / 2 - q) * ((a0 + a1) * (b0 + b1 + b2))"
    by (rule const_piece[OF q(2)]) (use p q True H in \<open>auto simp: ind_def\<close>)
  from chain[OF p(1) True e1 e2] have e12: "interval_lebesgue_integrable lborel (ereal 0) (ereal q)
    h \<and>
      interval_lebesgue_integral lborel (ereal 0) (ereal q) h =
        (p - 0) * (a0 * b0) + (q - p) * (a0 * (b0 + b2))" .
  from chain[OF q(1) q(2) e12 e3] show ?thesis using True by (simp add: max_def algebra_simps)
next
  case False
  hence qp: "q \<le> p" by simp
  have e1: "interval_lebesgue_integrable lborel (ereal 0) (ereal q) h \<and>
    interval_lebesgue_integral lborel (ereal 0) (ereal q) h = (q - 0) * (a0 * b0)"
    by (rule const_piece[OF q(1)]) (use qp p H in \<open>auto simp: ind_def\<close>)
  have e2: "interval_lebesgue_integrable lborel (ereal q) (ereal p) h \<and>
    interval_lebesgue_integral lborel (ereal q) (ereal p) h = (p - q) * ((a0 + a1) * (b0 + b1))"
    by (rule const_piece[OF qp]) (use p q H in \<open>auto simp: ind_def\<close>)
  have e3: "interval_lebesgue_integrable lborel (ereal p) (ereal (1 / 2)) h \<and>
    interval_lebesgue_integral lborel (ereal p) (ereal (1 / 2)) h =
    (1 / 2 - p) * ((a0 + a1) * (b0 + b1 + b2))"
    by (rule const_piece[OF p(2)]) (use p q qp H in \<open>auto simp: ind_def\<close>)
  from chain[OF q(1) qp e1 e2] have e12: "interval_lebesgue_integrable lborel (ereal 0) (ereal p) h
    \<and>
      interval_lebesgue_integral lborel (ereal 0) (ereal p) h =
        (q - 0) * (a0 * b0) + (p - q) * ((a0 + a1) * (b0 + b1))" .
  from chain[OF p(1) p(2) e12 e3] show ?thesis using False by (simp add: max_def algebra_simps)
qed

text \<open>@{text "l(y, z) = 2\<lfloor>y\<rfloor> + 1 - es{y} \<cdot> ind(d0{y}, z)"}
  for @{text "z \<in> (0, 1/2)"}, @{text "z \<noteq> d0{y}"}.\<close>
lemma ell_step:
  assumes z: "z \<in> {0<..<1 / 2}" and zp: "z \<noteq> d0 (frac y)"
  shows "ell_r y z = 2 * of_int (floor y) + 1 - es (frac y) * ind (d0 (frac y)) z"
proof -
  have y: "y = of_int (floor y) + frac y" by (simp add: frac_def)
  have f: "0 \<le> frac y" "frac y < 1" by (simp_all add: frac_lt_1)
  show ?thesis
  proof (cases "frac y \<le> 1 / 2")
    case True
    have d: "d0 (frac y) = frac y" and e: "es (frac y) = 1" using True unfolding d0_def es_def
      by (auto simp: min_def)
    have h2: "floor (y + z) = floor y" using z True f unfolding frac_def greaterThanLessThan_iff
      by (intro floor_eq_iff[THEN iffD2] conjI) (elim conjE, linarith)+
    show ?thesis
    proof (cases "z < frac y")
      case True
      have h1: "floor (y - z) = floor y" using z True f unfolding frac_def greaterThanLessThan_iff
      by (intro floor_eq_iff[THEN iffD2] conjI) (elim conjE, linarith)+
      show ?thesis unfolding ell_r_def h1 h2 d e using True by (simp add: ind_def)
    next
      case False
      hence lt: "frac y < z" using zp d by auto
      have h1: "floor (y - z) = floor y - 1" using z lt f unfolding frac_def greaterThanLessThan_iff
      by (intro floor_eq_iff[THEN iffD2] conjI) (elim conjE, linarith)+
      show ?thesis unfolding ell_r_def h1 h2 d e using lt by (simp add: ind_def)
    qed
  next
    case False
    have d: "d0 (frac y) = 1 - frac y" and e: "es (frac y) = - 1" using False
      unfolding d0_def es_def by (auto simp: min_def)
    have h1: "floor (y - z) = floor y" using z False f unfolding frac_def greaterThanLessThan_iff
      by (intro floor_eq_iff[THEN iffD2] conjI) (elim conjE, linarith)+
    show ?thesis
    proof (cases "z < 1 - frac y")
      case True
      have h2: "floor (y + z) = floor y" using z True f unfolding frac_def greaterThanLessThan_iff
      by (intro floor_eq_iff[THEN iffD2] conjI) (elim conjE, linarith)+
      show ?thesis unfolding ell_r_def h1 h2 d e using True by (simp add: ind_def)
    next
      case False
      hence lt: "1 - frac y < z" using zp d by auto
      have h2: "floor (y + z) = floor y + 1" using z lt f unfolding frac_def greaterThanLessThan_iff
      by (intro floor_eq_iff[THEN iffD2] conjI) (elim conjE, linarith)+
      show ?thesis unfolding ell_r_def h1 h2 d e using lt by (simp add: ind_def)
    qed
  qed
qed

text \<open>The @{text z}-integral in @{text "\<Gamma>"}.\<close>
lemma gam_int:
  "interval_lebesgue_integral lborel (ereal 0) (ereal (1 / 2))
     (\<lambda>z. (T - 3 * ell_r (alpha_r * x) z) * (T + 3 * ell_r (alpha_r * x) z - ell_r x z - 5))
   = (let p = d0 (frac x); q = d0 (frac (alpha_r * x));
          a0 = T - 3 * (2 * of_int (floor (alpha_r * x)) + 1); a1 = 3 * es (frac (alpha_r * x));
          b0 = T + 3 * (2 * of_int (floor (alpha_r * x)) + 1) - (2 * of_int (floor x) + 1) - 5;
          b1 = - 3 * es (frac (alpha_r * x)); b2 = es (frac x) in
      a0 * b0 / 2 + (a0 * b1 + a1 * b0 + a1 * b1) * (1 / 2 - q) + a0 * b2 * (1 / 2 - p) + a1 * b2 *
        (1 / 2 - max p q))"
proof -
  have hp: "0 \<le> d0 (frac x) \<and> d0 (frac x) \<le> 1 / 2"
    by (rule d0_mem) (simp_all add: frac_lt_1 less_imp_le)
  have hq: "0 \<le> d0 (frac (alpha_r * x)) \<and> d0 (frac (alpha_r * x)) \<le> 1 / 2"
    by (rule d0_mem) (simp_all add: frac_lt_1 less_imp_le)
  show ?thesis
    unfolding Let_def
    by (rule step3[OF conjunct1[OF hp] conjunct2[OF hp] conjunct1[OF hq] conjunct2[OF hq]])
       (simp add: ell_step algebra_simps)
qed

text \<open>@{text "Q = R - x F"}, eq. (5.13) with (B.1);
  arguments @{text "{x}, {\<alpha>x}, {2H_c x}, {2x}, {2\<lambda>x}"}.\<close>
definition Qc :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
  \<Rightarrow> real" where
  "Qc f g \<tau> \<sigma> \<eta> = 9 * (d0 g * (1 - 2 * d0 g))
     - 3 * (es f * es g * (d0 f + d0 g - max (d0 f) (d0 g) - 2 * d0 f * d0 g))
     + ((\<tau> ^ 2 - \<sigma> * \<tau>) / 2 - pos_r ((\<tau> - \<sigma>) / 2)) + (\<eta> -
       \<eta> ^ 2) / 2"

definition Fx :: "real \<Rightarrow> real" where
  "Fx x = 4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x)"

text \<open>The polynomial identities behind the three remaining sign cases of @{text R_eq},
  with the fractional parts, the @{text max} and the @{text pos_r} term as variables.\<close>
lemma R_eq_alg2:
  fixes x fx fa fh f2 fl mx pp :: real
  shows "- ((2 * Hc_r * x - fh - 3 * (2 * (alpha_r * x - fa) + 1)) * (2 * Hc_r * x - fh + 3 * (2 *
    (alpha_r * x - fa) + 1) - (2 * (x - fx) + 1) - 5) / 2 + ((2 * Hc_r * x - fh - 3 * (2 *
    (alpha_r * x - fa) + 1)) * (- 3 * - 1) + 3 * - 1 * (2 * Hc_r * x - fh + 3 * (2 * (alpha_r * x -
    fa) + 1) - (2 * (x - fx) + 1) - 5) + 3 * - 1 * (- 3 * - 1)) * (1 / 2 - (1 - fa)) + (2 * Hc_r *
    x - fh - 3 * (2 * (alpha_r * x - fa) + 1)) * 1 * (1 / 2 - fx) + 3 * - 1 * 1 * (1 / 2 - mx) +
    (Hc_r * x - (2 * Hc_r * x - fh) / 2) * (2 * (2 * Hc_r * x - fh) - (2 * x - f2) - 5) + pp) - (2 *
    lam_r * x * (x - fx) - 12 * lam_r * x * (alpha_r * x - fa) - 2 * ((2 * (lam_r * x) - fl) *
    (lam_r * x) - (2 * (lam_r * x) - fl) * (2 * (lam_r * x) - fl + 1) / 4)) =
    x * (4 * lam_r + 2 * lam_r * fx - 12 * lam_r * fa) + (9 * ((1 - fa) * (1 - 2 * (1 - fa))) - 3 *
    (1 * - 1 * (fx + (1 - fa) - mx - 2 * fx * (1 - fa))) + (((fh)\<^sup>2 - f2 * fh) / 2 - pp) +
    (fl - (fl)\<^sup>2) / 2)"
proof -
  \<comment> \<open>monomial expansions of the products\<close>
  have "(((((2 * (23 / 20)) * x) - fh) - (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) * ((((((2 * (23 /
    20)) * x) - fh) + (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) - ((2 * (x - fx)) + 1)) - 5)) =
    (9) + (- 39 / 5) * (x) + (- 6) * (fx) + (6) * (fh) + (111 / 80) * (x * x) + (37 / 10) * (x *
    fx) + (- 33 / 5) * (x * fa) + (- 13 / 5) * (x * fh) + (12) * (fx * fa) + (- 2) * (fx * fh) +
    (- 36) * (fa * fa) + (1) * (fh * fh)"
    using algebra_simps by argo
  moreover have "((((((((2 * (23 / 20)) * x) - fh) - (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) *
    ((- 3) * (- 1))) + ((3 * (- 1)) * ((((((2 * (23 / 20)) * x) - fh) + (3 * ((2 * (((3 / 40) * x) -
    fa)) + 1))) - ((2 * (x - fx)) + 1)) - 5))) + ((3 * (- 1)) * ((- 3) * (- 1)))) * ((1 / 2) - (1 -
    fa))) = (9 / 2) + (- 33 / 20) * (x) + (3) * (fx) + (- 27) * (fa) + (33 / 10) * (x * fa) +
    (- 6) * (fx * fa) + (36) * (fa * fa)"
    using algebra_simps by argo
  moreover have "((((((2 * (23 / 20)) * x) - fh) - (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) * 1) *
    ((1 / 2) - fx)) = (- 3 / 2) + (37 / 40) * (x) + (3) * (fx) + (3) * (fa) + (- 1 / 2) * (fh) +
    (- 37 / 20) * (x * fx) + (- 6) * (fx * fa) + (1) * (fx * fh)"
    using algebra_simps by argo
  moreover have "((((23 / 20) * x) - ((((2 * (23 / 20)) * x) - fh) / 2)) * (((2 * (((2 * (23 /
    20)) * x) - fh)) - ((2 * x) - f2)) - 5)) =
    (- 5 / 2) * (fh) + (13 / 10) * (x * fh) + (- 1) * (fh * fh) + (1 / 2) * (fh * f2)"
    using algebra_simps by argo
  moreover have "(((2 * (37 / 40)) * x) * (x - fx)) = (37 / 20) * (x * x) + (- 37 / 20) * (x * fx)"
    using algebra_simps by argo
  moreover have "(((12 * (37 / 40)) * x) * (((3 / 40) * x) - fa)) =
    (333 / 400) * (x * x) + (- 111 / 10) * (x * fa)"
    using algebra_simps by argo
  moreover have "(((2 * ((37 / 40) * x)) - fl) * ((37 / 40) * x)) =
    (1369 / 800) * (x * x) + (- 37 / 40) * (x * fl)"
    by (fastforce simp: algebra_simps)
  moreover have "(((2 * ((37 / 40) * x)) - fl) * (((2 * ((37 / 40) * x)) - fl) + 1)) =
    (37 / 20) * (x) + (- 1) * (fl) + (1369 / 400) * (x * x) + (- 37 / 10) * (x * fl) + (1) * (fl *
    fl)"
    by (auto simp: algebra_simps)
  moreover have "(x * (((4 * (37 / 40)) + ((2 * (37 / 40)) * fx)) - ((12 * (37 / 40)) * fa))) =
    (37 / 10) * (x) + (37 / 20) * (x * fx) + (- 111 / 10) * (x * fa)"
    by (simp add: algebra_simps)
  moreover have "((1 - fa) * (1 - (2 * (1 - fa)))) = (- 1) + (3) * (fa) + (- 2) * (fa * fa)"
    by (auto simp: algebra_simps)
  moreover have "((2 * fx) * (1 - fa)) = (2) * (fx) + (- 2) * (fx * fa)"
    by (simp add: algebra_simps)
  moreover have "(f2 * fh) = (1) * (fh * f2)"
    by (auto simp: algebra_simps)
  ultimately show ?thesis unfolding Hc_r_def lam_r_def alpha_r_def power2_eq_square
    by argo
qed

lemma R_eq_alg3:
  fixes x fx fa fh f2 fl mx pp :: real
  shows "- ((2 * Hc_r * x - fh - 3 * (2 * (alpha_r * x - fa) + 1)) * (2 * Hc_r * x - fh + 3 * (2 *
    (alpha_r * x - fa) + 1) - (2 * (x - fx) + 1) - 5) / 2 + ((2 * Hc_r * x - fh - 3 * (2 *
    (alpha_r * x - fa) + 1)) * (- 3 * 1) + 3 * 1 * (2 * Hc_r * x - fh + 3 * (2 * (alpha_r * x -
    fa) + 1) - (2 * (x - fx) + 1) - 5) + 3 * 1 * (- 3 * 1)) * (1 / 2 - fa) + (2 * Hc_r * x - fh -
    3 * (2 * (alpha_r * x - fa) + 1)) * - 1 * (1 / 2 - (1 - fx)) + 3 * 1 * - 1 * (1 / 2 - mx) +
    (Hc_r * x - (2 * Hc_r * x - fh) / 2) * (2 * (2 * Hc_r * x - fh) - (2 * x - f2) - 5) + pp) - (2 *
    lam_r * x * (x - fx) - 12 * lam_r * x * (alpha_r * x - fa) - 2 * ((2 * (lam_r * x) - fl) *
    (lam_r * x) - (2 * (lam_r * x) - fl) * (2 * (lam_r * x) - fl + 1) / 4)) =
    x * (4 * lam_r + 2 * lam_r * fx - 12 * lam_r * fa) + (9 * (fa * (1 - 2 * fa)) - 3 * (- 1 * 1 *
    (1 - fx + fa - mx - 2 * (1 - fx) * fa)) + (((fh)\<^sup>2 - f2 * fh) / 2 - pp) + (fl -
    (fl)\<^sup>2) / 2)"
proof -
  \<comment> \<open>monomial expansions of the products\<close>
  have "(((((2 * (23 / 20)) * x) - fh) - (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) * ((((((2 * (23 /
    20)) * x) - fh) + (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) - ((2 * (x - fx)) + 1)) - 5)) =
    (9) + (- 39 / 5) * (x) + (- 6) * (fx) + (6) * (fh) + (111 / 80) * (x * x) + (37 / 10) * (x *
    fx) + (- 33 / 5) * (x * fa) + (- 13 / 5) * (x * fh) + (12) * (fx * fa) + (- 2) * (fx * fh) +
    (- 36) * (fa * fa) + (1) * (fh * fh)"
    using algebra_simps by argo
  moreover have "((((((((2 * (23 / 20)) * x) - fh) - (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) *
    ((- 3) * 1)) + ((3 * 1) * ((((((2 * (23 / 20)) * x) - fh) + (3 * ((2 * (((3 / 40) * x) - fa)) +
    1))) - ((2 * (x - fx)) + 1)) - 5))) + ((3 * 1) * ((- 3) * 1))) * ((1 / 2) - fa)) =
    (- 9 / 2) + (- 33 / 20) * (x) + (3) * (fx) + (- 9) * (fa) + (33 / 10) * (x * fa) + (- 6) * (fx *
    fa) + (36) * (fa * fa)"
    using algebra_simps by argo
  moreover have "((((((2 * (23 / 20)) * x) - fh) - (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) *
    (- 1)) * ((1 / 2) - (1 - fx))) = (- 3 / 2) + (37 / 40) * (x) + (3) * (fx) + (3) * (fa) + (- 1 /
    2) * (fh) + (- 37 / 20) * (x * fx) + (- 6) * (fx * fa) + (1) * (fx * fh)"
    using algebra_simps by argo
  moreover have "((((23 / 20) * x) - ((((2 * (23 / 20)) * x) - fh) / 2)) * (((2 * (((2 * (23 /
    20)) * x) - fh)) - ((2 * x) - f2)) - 5)) =
    (- 5 / 2) * (fh) + (13 / 10) * (x * fh) + (- 1) * (fh * fh) + (1 / 2) * (fh * f2)"
    using algebra_simps by argo
  moreover have "(((2 * (37 / 40)) * x) * (x - fx)) = (37 / 20) * (x * x) + (- 37 / 20) * (x * fx)"
    using algebra_simps by argo
  moreover have "(((12 * (37 / 40)) * x) * (((3 / 40) * x) - fa)) =
    (333 / 400) * (x * x) + (- 111 / 10) * (x * fa)"
    using algebra_simps by argo
  moreover have "(((2 * ((37 / 40) * x)) - fl) * ((37 / 40) * x)) =
    (1369 / 800) * (x * x) + (- 37 / 40) * (x * fl)"
    by (fastforce simp: algebra_simps)
  moreover have "(((2 * ((37 / 40) * x)) - fl) * (((2 * ((37 / 40) * x)) - fl) + 1)) =
    (37 / 20) * (x) + (- 1) * (fl) + (1369 / 400) * (x * x) + (- 37 / 10) * (x * fl) + (1) * (fl *
    fl)"
    by (auto simp: algebra_simps)
  moreover have "(x * (((4 * (37 / 40)) + ((2 * (37 / 40)) * fx)) - ((12 * (37 / 40)) * fa))) =
    (37 / 10) * (x) + (37 / 20) * (x * fx) + (- 111 / 10) * (x * fa)"
    by (auto simp: algebra_simps)
  moreover have "(fa * (1 - (2 * fa))) = (1) * (fa) + (- 2) * (fa * fa)"
    by (simp add: algebra_simps)
  moreover have "((2 * (1 - fx)) * fa) = (2) * (fa) + (- 2) * (fx * fa)"
    by (auto simp: algebra_simps)
  moreover have "(f2 * fh) = (1) * (fh * f2)"
    by (simp add: algebra_simps)
  ultimately show ?thesis unfolding Hc_r_def lam_r_def alpha_r_def power2_eq_square
    by argo
qed

lemma R_eq_alg4:
  fixes x fx fa fh f2 fl mx pp :: real
  shows "- ((2 * Hc_r * x - fh - 3 * (2 * (alpha_r * x - fa) + 1)) * (2 * Hc_r * x - fh + 3 * (2 *
    (alpha_r * x - fa) + 1) - (2 * (x - fx) + 1) - 5) / 2 + ((2 * Hc_r * x - fh - 3 * (2 *
    (alpha_r * x - fa) + 1)) * (- 3 * - 1) + 3 * - 1 * (2 * Hc_r * x - fh + 3 * (2 * (alpha_r * x -
    fa) + 1) - (2 * (x - fx) + 1) - 5) + 3 * - 1 * (- 3 * - 1)) * (1 / 2 - (1 - fa)) + (2 * Hc_r *
    x - fh - 3 * (2 * (alpha_r * x - fa) + 1)) * - 1 * (1 / 2 - (1 - fx)) + 3 * - 1 * - 1 * (1 / 2 -
    mx) + (Hc_r * x - (2 * Hc_r * x - fh) / 2) * (2 * (2 * Hc_r * x - fh) - (2 * x - f2) - 5) +
    pp) - (2 * lam_r * x * (x - fx) - 12 * lam_r * x * (alpha_r * x - fa) - 2 * ((2 * (lam_r * x) -
    fl) * (lam_r * x) - (2 * (lam_r * x) - fl) * (2 * (lam_r * x) - fl + 1) / 4)) =
    x * (4 * lam_r + 2 * lam_r * fx - 12 * lam_r * fa) + (9 * ((1 - fa) * (1 - 2 * (1 - fa))) - 3 *
    (- 1 * - 1 * (1 - fx + (1 - fa) - mx - 2 * (1 - fx) * (1 - fa))) + (((fh)\<^sup>2 - f2 * fh) /
    2 - pp) + (fl - (fl)\<^sup>2) / 2)"
proof -
  \<comment> \<open>monomial expansions of the products\<close>
  have "(((((2 * (23 / 20)) * x) - fh) - (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) * ((((((2 * (23 /
    20)) * x) - fh) + (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) - ((2 * (x - fx)) + 1)) - 5)) =
    (9) + (- 39 / 5) * (x) + (- 6) * (fx) + (6) * (fh) + (111 / 80) * (x * x) + (37 / 10) * (x *
    fx) + (- 33 / 5) * (x * fa) + (- 13 / 5) * (x * fh) + (12) * (fx * fa) + (- 2) * (fx * fh) +
    (- 36) * (fa * fa) + (1) * (fh * fh)"
    using algebra_simps by argo
  moreover have "((((((((2 * (23 / 20)) * x) - fh) - (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) *
    ((- 3) * (- 1))) + ((3 * (- 1)) * ((((((2 * (23 / 20)) * x) - fh) + (3 * ((2 * (((3 / 40) * x) -
    fa)) + 1))) - ((2 * (x - fx)) + 1)) - 5))) + ((3 * (- 1)) * ((- 3) * (- 1)))) * ((1 / 2) - (1 -
    fa))) = (9 / 2) + (- 33 / 20) * (x) + (3) * (fx) + (- 27) * (fa) + (33 / 10) * (x * fa) +
    (- 6) * (fx * fa) + (36) * (fa * fa)"
    using algebra_simps by argo
  moreover have "((((((2 * (23 / 20)) * x) - fh) - (3 * ((2 * (((3 / 40) * x) - fa)) + 1))) *
    (- 1)) * ((1 / 2) - (1 - fx))) = (- 3 / 2) + (37 / 40) * (x) + (3) * (fx) + (3) * (fa) + (- 1 /
    2) * (fh) + (- 37 / 20) * (x * fx) + (- 6) * (fx * fa) + (1) * (fx * fh)"
    using algebra_simps by argo
  moreover have "((((23 / 20) * x) - ((((2 * (23 / 20)) * x) - fh) / 2)) * (((2 * (((2 * (23 /
    20)) * x) - fh)) - ((2 * x) - f2)) - 5)) =
    (- 5 / 2) * (fh) + (13 / 10) * (x * fh) + (- 1) * (fh * fh) + (1 / 2) * (fh * f2)"
    using algebra_simps by argo
  moreover have "(((2 * (37 / 40)) * x) * (x - fx)) = (37 / 20) * (x * x) + (- 37 / 20) * (x * fx)"
    using algebra_simps by argo
  moreover have "(((12 * (37 / 40)) * x) * (((3 / 40) * x) - fa)) =
    (333 / 400) * (x * x) + (- 111 / 10) * (x * fa)"
    using algebra_simps by argo
  moreover have "(((2 * ((37 / 40) * x)) - fl) * ((37 / 40) * x)) =
    (1369 / 800) * (x * x) + (- 37 / 40) * (x * fl)"
    by (auto simp: algebra_simps)
  moreover have "(((2 * ((37 / 40) * x)) - fl) * (((2 * ((37 / 40) * x)) - fl) + 1)) =
    (37 / 20) * (x) + (- 1) * (fl) + (1369 / 400) * (x * x) + (- 37 / 10) * (x * fl) + (1) * (fl *
    fl)"
    by (simp add: algebra_simps)
  moreover have "(x * (((4 * (37 / 40)) + ((2 * (37 / 40)) * fx)) - ((12 * (37 / 40)) * fa))) =
    (37 / 10) * (x) + (37 / 20) * (x * fx) + (- 111 / 10) * (x * fa)"
    by (force simp: algebra_simps)
  moreover have "((1 - fa) * (1 - (2 * (1 - fa)))) = (- 1) + (3) * (fa) + (- 2) * (fa * fa)"
    by (force simp: algebra_simps)
  moreover have "((2 * (1 - fx)) * (1 - fa)) = (2) + (- 2) * (fx) + (- 2) * (fa) + (2) * (fx * fa)"
    by (simp add: algebra_simps)
  moreover have "(f2 * fh) = (1) * (fh * f2)"
    by (auto simp: algebra_simps)
  ultimately show ?thesis unfolding Hc_r_def lam_r_def alpha_r_def power2_eq_square
    by argo
qed

theorem R_eq:
  "R_r x = x * Fx x + Qc (frac x) (frac (alpha_r * x)) (frac (2 * Hc_r * x)) (frac (2 *
    x)) (frac (2 * (lam_r * x)))"
proof -
  have fl: "\<And>u. of_int (floor u) = u - frac (u :: real)" by (simp add: frac_def)
  have pe: "pos_r (Hc_r * x - (2 * Hc_r * x - frac (2 * Hc_r * x)) / 2 - (2 * x - (2 * x - frac (2 *
    x))) / 2) = pos_r ((frac (2 * Hc_r * x) - frac (2 * x)) / 2)"
    using algebra_simps by argo
  show ?thesis
    using es_cases[of "frac x"] es_cases[of "frac (alpha_r * x)"]
  proof (elim disjE conjE)
    assume "es (frac x) = 1" "d0 (frac x) = frac x"
      and "es (frac (alpha_r * x)) = 1" "d0 (frac (alpha_r * x)) = frac (alpha_r * x)"
    thus ?thesis unfolding R_r_def Gam_r_def Nfun_r_def J_r_def Fx_def Let_def gam_int
      by (simp only: fl pe Qc_def) (auto simp: alpha_r_def lam_r_def Hc_r_def field_simps
        power2_eq_square)
  next
    assume "es (frac x) = 1" "d0 (frac x) = frac x"
      and "es (frac (alpha_r * x)) = - 1" "d0 (frac (alpha_r * x)) = 1 - frac (alpha_r * x)"
    thus ?thesis unfolding R_r_def Gam_r_def Nfun_r_def J_r_def Fx_def Let_def gam_int
      by (simp only: fl pe Qc_def) (use R_eq_alg2 in fast)
  next
    assume "es (frac x) = - 1" "d0 (frac x) = 1 - frac x"
      and "es (frac (alpha_r * x)) = 1" "d0 (frac (alpha_r * x)) = frac (alpha_r * x)"
    thus ?thesis unfolding R_r_def Gam_r_def Nfun_r_def J_r_def Fx_def Let_def gam_int
      by (simp only: fl pe Qc_def) (use R_eq_alg3 in blast)
  next
    assume "es (frac x) = - 1" "d0 (frac x) = 1 - frac x"
      and "es (frac (alpha_r * x)) = - 1" "d0 (frac (alpha_r * x)) = 1 - frac (alpha_r * x)"
    thus ?thesis unfolding R_r_def Gam_r_def Nfun_r_def J_r_def Fx_def Let_def gam_int
      by (simp only: fl pe Qc_def) (use R_eq_alg4 in fast)
  qed
qed

lemma Qc_bounds:
  assumes "0 \<le> f" "f \<le> 1" "0 \<le> g" "g \<le> 1" "0 \<le> \<tau>" "\<tau> \<le> 1" "0 \<le>
    \<sigma>" "\<sigma> \<le> 1" "0 \<le> \<eta>" "\<eta> \<le> 1"
  shows "- 1 / 2 \<le> Qc f g \<tau> \<sigma> \<eta> \<and>
    Qc f g \<tau> \<sigma> \<eta> \<le> 13 / 8"
proof -
  have hp: "0 \<le> d0 f \<and> d0 f \<le> 1 / 2" and hq: "0 \<le> d0 g \<and> d0 g \<le> 1 / 2"
    by (rule d0_mem; simp add: assms)+
  have "0 \<le> d0 g * (1 - 2 * d0 g) \<and> d0 g * (1 - 2 * d0 g) \<le> 1 / 8"
  proof -
    have "d0 g * (1 - 2 * d0 g) = 1 / 8 - 2 * (d0 g - 1 / 4) ^ 2"
      by (simp add: power2_eq_square algebra_simps)
    moreover have "0 \<le> (d0 g - 1 / 4) ^ 2" by simp
    moreover have "0 \<le> d0 g * (1 - 2 * d0 g)" using hq by auto
    ultimately show ?thesis by argo
  qed
  moreover have "0 \<le> d0 f + d0 g - max (d0 f) (d0 g) - 2 * d0 f * d0 g \<and>
    d0 f + d0 g - max (d0 f) (d0 g) - 2 * d0 f * d0 g \<le> 1 / 8"
  proof (cases "d0 f \<le> d0 g")
    case True
    have "d0 f + d0 g - max (d0 f) (d0 g) - 2 * d0 f * d0 g = d0 f * (1 - 2 * d0 g)" using True
      by (simp add: max_def algebra_simps)
    moreover have "d0 f * (1 - 2 * d0 g) \<le> d0 g * (1 - 2 * d0 g)" using True hq
      by (auto intro: mult_right_mono)
    moreover have "d0 g * (1 - 2 * d0 g) = 1 / 8 - 2 * (d0 g - 1 / 4) ^ 2"
      by (simp add: power2_eq_square algebra_simps)
    moreover have "0 \<le> (d0 g - 1 / 4) ^ 2" by simp
    moreover have "0 \<le> d0 f * (1 - 2 * d0 g)" using hp hq by (auto intro: mult_nonneg_nonneg)
    ultimately show ?thesis by argo
  next
    case False
    have "d0 f + d0 g - max (d0 f) (d0 g) - 2 * d0 f * d0 g = d0 g * (1 - 2 * d0 f)" using False
      by (simp add: max_def algebra_simps)
    moreover have "d0 g * (1 - 2 * d0 f) \<le> d0 f * (1 - 2 * d0 f)" using False hp
      by (auto intro: mult_right_mono)
    moreover have "d0 f * (1 - 2 * d0 f) = 1 / 8 - 2 * (d0 f - 1 / 4) ^ 2"
      by (simp add: power2_eq_square algebra_simps)
    moreover have "0 \<le> (d0 f - 1 / 4) ^ 2" by simp
    moreover have "0 \<le> d0 g * (1 - 2 * d0 f)" using hp hq by (auto intro: mult_nonneg_nonneg)
    ultimately show ?thesis by argo
  qed
  hence "- 1 / 8 \<le> es f * es g * (d0 f + d0 g - max (d0 f) (d0 g) - 2 * d0 f * d0 g) \<and>
             es f * es g * (d0 f + d0 g - max (d0 f) (d0 g) - 2 * d0 f * d0 g) \<le> 1 / 8"
    using es_pm[of f] es_pm[of g] by (elim disjE) simp_all
  moreover have "- 1 / 8 \<le> (\<tau> ^ 2 - \<sigma> * \<tau>) / 2 - pos_r ((\<tau> - \<sigma>) /
    2) \<and> (\<tau> ^ 2 - \<sigma> * \<tau>) / 2 - pos_r ((\<tau> - \<sigma>) / 2) \<le> 0"
  proof (cases "\<tau> \<le> \<sigma>")
    case True
    have p: "pos_r ((\<tau> - \<sigma>) / 2) = 0" using True unfolding pos_r_def
      by force
    have "\<tau> ^ 2 - \<sigma> * \<tau> = (\<tau> - \<sigma> / 2) ^ 2 - \<sigma> ^ 2 / 4"
      by (auto simp: power2_eq_square algebra_simps)
    moreover have "0 \<le> (\<tau> - \<sigma> / 2) ^ 2" by simp
    moreover have "\<sigma> ^ 2 \<le> 1" using assms(7,8)
      using power_le_one by blast
    moreover have "\<tau> * (\<tau> - \<sigma>) \<le> 0" using True assms(5)
      by (force simp: mult_nonneg_nonpos)
    moreover have "\<tau> ^ 2 - \<sigma> * \<tau> = \<tau> * (\<tau> - \<sigma>)"
      by (simp add: power2_eq_square algebra_simps)
    ultimately show ?thesis unfolding p
      by argo
  next
    case False
    have p: "pos_r ((\<tau> - \<sigma>) / 2) = (\<tau> - \<sigma>) / 2" using False
      unfolding pos_r_def
      by auto
    have "\<tau> ^ 2 - \<sigma> * \<tau> - (\<tau> - \<sigma>) =
      (\<tau> - (1 + \<sigma>) / 2) ^ 2 - ((1 - \<sigma>) / 2) ^ 2"
      by (simp add: power2_eq_square field_simps)
    moreover have "0 \<le> (\<tau> - (1 + \<sigma>) / 2) ^ 2" by simp
    moreover have "(1 - \<sigma>) ^ 2 \<le> 1" using assms(7,8)
      by (auto simp: power_le_one)
    hence "((1 - \<sigma>) / 2) ^ 2 \<le> 1 / 4"
      by (simp add: power_divide)
    moreover have "(\<tau> - \<sigma>) * (\<tau> - 1) \<le> 0" using False assms(6)
      by (simp add: mult_nonneg_nonpos)
    moreover have "\<tau> ^ 2 - \<sigma> * \<tau> - (\<tau> - \<sigma>) =
      (\<tau> - \<sigma>) * (\<tau> - 1)"
      by (simp add: power2_eq_square algebra_simps)
    ultimately show ?thesis unfolding p
      by argo
  qed
  moreover have "0 \<le> (\<eta> - \<eta> ^ 2) / 2 \<and> (\<eta> - \<eta> ^ 2) / 2 \<le> 1 / 8"
  proof -
    have "\<eta> - \<eta> ^ 2 = \<eta> * (1 - \<eta>)"
      by (force simp: power2_eq_square algebra_simps)
    moreover have "0 \<le> \<eta> * (1 - \<eta>)" using assms(9,10)
      by (auto intro: mult_nonneg_nonneg)
    moreover have "\<eta> - \<eta> ^ 2 = 1 / 4 - (\<eta> - 1 / 2) ^ 2"
      by (fastforce simp: power2_eq_square algebra_simps)
    moreover have "0 \<le> (\<eta> - 1 / 2) ^ 2" by simp
    ultimately show ?thesis by argo
  qed
  ultimately show ?thesis unfolding Qc_def by linarith
qed

text \<open>(5.12)-(5.14) for every real @{text x}.\<close>
theorem R_decomp_bound_all:
  "- 1 / 2 \<le> R_r x - x * (4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r *
    x)) \<and>
   R_r x - x * (4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x)) \<le> 13 / 8"
proof -
  have "- 1 / 2 \<le> Qc (frac x) (frac (alpha_r * x)) (frac (2 * Hc_r * x)) (frac (2 *
    x)) (frac (2 * (lam_r * x))) \<and>
           Qc (frac x) (frac (alpha_r * x)) (frac (2 * Hc_r * x)) (frac (2 * x)) (frac (2 * (lam_r *
             x))) \<le> 13 / 8"
    by (rule Qc_bounds) (simp_all add: frac_lt_1 less_imp_le)
  thus ?thesis unfolding R_eq Fx_def by simp
qed

text \<open>@{text "R(x) = A x + B"} on a piece where the five floors are known.\<close>
lemma R_on_piece:
  fixes k1 k2 k3 k4 k5 :: nat
  assumes "real k1 \<le> x" "x < real k1 + 1" "real k2 \<le> alpha_r * x" "alpha_r * x <
    real k2 + 1"
    "real k3 \<le> 2 * Hc_r * x" "2 * Hc_r * x < real k3 + 1" "real k4 \<le> 2 * x" "2 * x <
      real k4 + 1"
    "real k5 \<le> 2 * (lam_r * x)" "2 * (lam_r * x) < real k5 + 1"
  shows "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real k1) - 12 * lam_r * (alpha_r * x - real k2))
                 + Qc (x - real k1) (alpha_r * x - real k2) (2 * Hc_r * x - real k3) (2 * x -
                   real k4) (2 * (lam_r * x) - real k5)"
  unfolding R_eq Fx_def frac_nat[OF assms(1,2)] frac_nat[OF assms(3,4)] frac_nat[OF assms(5,6)]
    frac_nat[OF assms(7,8)] frac_nat[OF assms(9,10)] ..


subsection \<open>@{text "\<integral>_{1/3}^{1/2} d(y) dy = 9/640"}, the mean of @{text P},
  and @{text "|C| < 16"}\<close>

theorem integral_dfun_eq: "interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (1 /
  2)) dfun_r = 9 / 640"
proof -
  have e1: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (43 / 120)) dfun_r \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (43 / 120)) dfun_r
        = (9 / 40 * (43 / 120) + 0 * (43 / 120) ^ 2 / 2 + 0 * (43 / 120) ^ 3 / 3) - (9 / 40 * (1 /
          3) + 0 * (1 / 3) ^ 2 / 2 + 0 * (1 / 3) ^ 3 / 3)"
  proof (rule piece_quad)
    show "1 / 3 \<le> (43 / 120 :: real)" by simp
  next
    fix y :: real assume "y \<in> {1 / 3<..<43 / 120}"
    thus "dfun_r y = 9 / 40 + 0 * y + 0 * y ^ 2" unfolding dfun_r_def pos_r_def alpha_r_def max_def
      by (force simp: field_simps)
  qed
  have e2: "interval_lebesgue_integrable lborel (ereal (43 / 120)) (ereal (13 / 30)) dfun_r \<and>
      interval_lebesgue_integral lborel (ereal (43 / 120)) (ereal (13 / 30)) dfun_r
        = (13 / 10 * (13 / 30) + (- 3) * (13 / 30) ^ 2 / 2 + 0 * (13 / 30) ^ 3 / 3) - (13 / 10 *
          (43 / 120) + (- 3) * (43 / 120) ^ 2 / 2 + 0 * (43 / 120) ^ 3 / 3)"
  proof (rule piece_quad)
    show "43 / 120 \<le> (13 / 30 :: real)" by simp
  next
    fix y :: real assume "y \<in> {43 / 120<..<13 / 30}"
    thus "dfun_r y = 13 / 10 + (- 3) * y + 0 * y ^ 2"
      unfolding dfun_r_def pos_r_def alpha_r_def max_def by (force simp: field_simps)
  qed
  have e3: "interval_lebesgue_integrable lborel (ereal (13 / 30)) (ereal (1 / 2)) dfun_r \<and>
      interval_lebesgue_integral lborel (ereal (13 / 30)) (ereal (1 / 2)) dfun_r
        = (0 * (1 / 2) + 0 * (1 / 2) ^ 2 / 2 + 0 * (1 / 2) ^ 3 / 3) - (0 * (13 / 30) + 0 * (13 /
          30) ^ 2 / 2 + 0 * (13 / 30) ^ 3 / 3)"
  proof (rule piece_quad)
    show "13 / 30 \<le> (1 / 2 :: real)" by simp
  next
    fix y :: real assume "y \<in> {13 / 30<..<1 / 2}"
    thus "dfun_r y = 0 + 0 * y + 0 * y ^ 2" unfolding dfun_r_def pos_r_def alpha_r_def max_def
      by (force simp: field_simps)
  qed
  from chain[OF _ _ e1 e2] have e12: "interval_lebesgue_integrable lborel (ereal (1 /
    3)) (ereal (13 / 30)) dfun_r \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (13 / 30)) dfun_r =
        9 / 40 * (43 / 120 - 1 / 3) + (13 / 10 * (13 / 30 - 43 / 120) - 3 / 2 * ((13 / 30) ^ 2 -
        (43 / 120) ^ 2))"
    by (simp add: power2_eq_square power3_eq_cube)
  from chain[OF _ _ e12 e3] show ?thesis by (simp add: power2_eq_square power3_eq_cube)
qed

lemma fract_quad_piece: "x \<in> {real n<..<real n + 1} \<Longrightarrow>
  frac x * (1 - frac x) = (- real n - real n ^ 2) + (1 + 2 * real n) * x + (- 1) * x ^ 2"
proof -
  assume x: "x \<in> {real n<..<real n + 1}"
  have f: "frac x = x - real n" using x frac_nat[of n x] by fastforce
  show ?thesis unfolding f by (auto simp: power2_eq_square algebra_simps)
qed

lemma fract_quad_integral:
  "interval_lebesgue_integrable lborel (ereal 0) (ereal (real n)) (\<lambda>x. frac x * (1 -
    frac x)) \<and>
   interval_lebesgue_integral lborel (ereal 0) (ereal (real n)) (\<lambda>x. frac x * (1 -
     frac x)) = real n / 6"
proof (induction n)
  case 0
  show ?case
    by (fastforce simp: interval_lebesgue_integrable_def set_integrable_def
      interval_lebesgue_integral_def set_lebesgue_integral_def)
next
  case (Suc n)
  have piece: "interval_lebesgue_integrable lborel (ereal (real n)) (ereal (real (Suc n)))
    (\<lambda>x. frac x * (1 - frac x)) \<and>
      interval_lebesgue_integral lborel (ereal (real n)) (ereal (real (Suc n))) (\<lambda>x. frac x
        * (1 - frac x)) = 1 / 6"
  proof -
    have e: "real (Suc n) = real n + 1" by simp
    have "interval_lebesgue_integrable lborel (ereal (real n)) (ereal (real n +
      1)) (\<lambda>x. frac x * (1 - frac x)) \<and>
        interval_lebesgue_integral lborel (ereal (real n)) (ereal (real n +
          1)) (\<lambda>x. frac x * (1 - frac x))
          = ((- real n - real n ^ 2) * (real n + 1) + (1 + 2 * real n) * (real n + 1) ^ 2 / 2 +
            (- 1) * (real n + 1) ^ 3 / 3)
            - ((- real n - real n ^ 2) * real n + (1 + 2 * real n) * real n ^ 2 / 2 + (- 1) *
              real n ^ 3 / 3)"
    proof (rule piece_quad)
      show "real n \<le> real n + 1" by simp
    next
      fix x assume "x \<in> {real n<..<real n + 1}"
      thus "frac x * (1 - frac x) = (- real n - real n ^ 2) + (1 + 2 * real n) * x + (- 1) * x ^ 2"
        by (rule fract_quad_piece)
    qed
    moreover have "((- real n - real n ^ 2) * (real n + 1) + (1 + 2 * real n) * (real n + 1) ^ 2 /
      2 + (- 1) * (real n + 1) ^ 3 / 3)
            - ((- real n - real n ^ 2) * real n + (1 + 2 * real n) * real n ^ 2 / 2 + (- 1) *
              real n ^ 3 / 3) = 1 / 6"
      by (simp add: field_simps power2_eq_square power3_eq_cube)
    ultimately show ?thesis unfolding e
      by presburger
  qed
  from chain[OF _ _ Suc piece] show ?case by simp
qed

text \<open>Scaling @{text "x \<mapsto> c x"} in an integral from 0.\<close>
lemma integral_scale:
  fixes g :: "real \<Rightarrow> real"
  assumes c: "0 < c" and b: "0 \<le> b" and "interval_lebesgue_integrable lborel (ereal 0) (ereal (c
    * b)) g"
  shows "interval_lebesgue_integral lborel (ereal 0) (ereal b) (\<lambda>x. g (c * x)) =
    (1 / c) * interval_lebesgue_integral lborel (ereal 0) (ereal (c * b)) g"
proof -
  have "0 \<le> c * b" using c b by simp
  hence L: "interval_lebesgue_integral lborel (ereal 0) (ereal (c * b)) g =
    (\<integral>x. indicator {0<..<c * b} x *\<^sub>R g x \<partial>lborel)"
    unfolding interval_lebesgue_integral_def set_lebesgue_integral_def
    by simp
  have R: "interval_lebesgue_integral lborel (ereal 0) (ereal b) (\<lambda>x. g (c * x)) =
    (\<integral>x. indicator {0<..<b} x *\<^sub>R g (c * x) \<partial>lborel)"
    unfolding interval_lebesgue_integral_def set_lebesgue_integral_def using b
    by simp
  have A: "(\<integral>x. indicator {0<..<c * b} x *\<^sub>R g x \<partial>lborel) =
    \<bar>c\<bar> *\<^sub>R (\<integral>x. indicator {0<..<c * b} (0 + c * x) *\<^sub>R g (0 + c *
    x) \<partial>lborel)"
    using lborel_integral_real_affine[of c "\<lambda>x. indicator {0<..<c * b} x *\<^sub>R g x" 0] c
    by blast
  have I: "\<And>x. (indicator {0<..<c * b} (0 + c * x) :: real) = indicator {0<..<b} x" using c
    by (auto simp: indicator_def zero_less_mult_iff mult_less_cancel_left)
  show ?thesis unfolding L R A I using c
    by (simp add: field_simps)
qed


lemma integrable_scale:
  fixes g :: "real \<Rightarrow> real"
  assumes c: "0 < c" and b: "0 \<le> b" and i: "interval_lebesgue_integrable lborel (ereal 0) (ereal
    (c * b)) g"
  shows "interval_lebesgue_integrable lborel (ereal 0) (ereal b) (\<lambda>x. g (c * x))"
proof -
  have "0 \<le> c * b" using c b by simp
  hence i0: "integrable lborel (\<lambda>x. indicator {0<..<c * b} x *\<^sub>R g x)" using i
    unfolding interval_lebesgue_integrable_def set_integrable_def
    by simp
  have i1: "integrable lborel (\<lambda>x. indicator {0<..<c * b} (0 + c * x) *\<^sub>R g (0 + c *
    x))"
    using lborel_integrable_real_affine[OF i0, of c 0] c
    by blast
  have I: "\<And>x. (indicator {0<..<c * b} (0 + c * x) :: real) = indicator {0<..<b} x" using c
    by (simp add: indicator_def zero_less_mult_iff mult_less_cancel_left)
  show ?thesis unfolding interval_lebesgue_integrable_def set_integrable_def using b i1 unfolding I
    by simp
qed

theorem Pper_mean_eq: "interval_lebesgue_integral lborel (ereal 0) (ereal 40) Pper / 40 =
  2923 / 240"
proof -
  let ?u = "\<lambda>x. frac x * (1 - frac x)"
  have u40: "interval_lebesgue_integral lborel (ereal 0) (ereal 40) ?u = 40 / 6"
    using fract_quad_integral[of 40] by simp
  have u3: "interval_lebesgue_integral lborel (ereal 0) (ereal 40) (\<lambda>x. ?u (alpha_r * x)) =
    (1 / alpha_r) * (3 / 6)"
    using integral_scale[of alpha_r 40 ?u] fract_quad_integral[of 3] by (simp add: alpha_r_def)
  have Pper_eq: "Pper = (\<lambda>x. 74 * ?u (alpha_r * x) - lam_r * ?u x)"
    by (simp add: Pper_def fun_eq_iff algebra_simps)
  have "interval_lebesgue_integral lborel (ereal 0) (ereal 40) Pper =
    74 * ((1 / alpha_r) * (3 / 6)) - lam_r * (40 / 6)"
    unfolding Pper_eq
  proof -
    have j40: "interval_lebesgue_integrable lborel (ereal 0) (ereal 40) ?u"
      using fract_quad_integral[of 40]
      by simp
    have "interval_lebesgue_integrable lborel (ereal 0) (ereal (alpha_r * 40)) ?u"
      using fract_quad_integral[of 3]
      by (simp add: alpha_r_def)
    hence "interval_lebesgue_integrable lborel (ereal 0) (ereal 40) (\<lambda>x. ?u (alpha_r * x))"
      using integrable_scale[of alpha_r 40 ?u]
      using alpha_r_def by linarith
    hence i1: "interval_lebesgue_integrable lborel (ereal 0) (ereal 40) (\<lambda>x. 74 *
      ?u (alpha_r * x))"
      by fast
    have i2: "interval_lebesgue_integrable lborel (ereal 0) (ereal 40) (\<lambda>x. lam_r * ?u x)"
      using j40
      by fast
    have D: "interval_lebesgue_integral lborel (ereal 0) (ereal 40) (\<lambda>x. 74 * ?u (alpha_r *
      x) - lam_r * ?u x)
       = interval_lebesgue_integral lborel (ereal 0) (ereal 40) (\<lambda>x. 74 * ?u (alpha_r *
         x)) - interval_lebesgue_integral lborel (ereal 0) (ereal 40) (\<lambda>x. lam_r * ?u x)"
      by (rule interval_lebesgue_integral_diff(2)[OF i1 i2])
    show "interval_lebesgue_integral lborel (ereal 0) (ereal 40) (\<lambda>x. 74 * ?u (alpha_r *
      x) - lam_r * ?u x) = 74 * ((1 / alpha_r) * (3 / 6)) - lam_r * (40 / 6)"
      unfolding D using u40 u3
      by simp
  qed
  thus ?thesis by (simp add: alpha_r_def lam_r_def)
qed

text \<open>@{text "|G_0(v)| \<le> 81/5000"} on @{text "[0, 1]"} and @{text "|C(x)| < 16"}.\<close>
lemma G0_r_bound:
  assumes "0 \<le> v" "v \<le> 1"
  shows "\<bar>G0_r v\<bar> \<le> 81 / 5000"
proof -
  define w where "w = 2 * v - 1"
  define u where "u = \<bar>w\<bar>"
  have u0: "0 \<le> u" and u1: "u \<le> 1" using assms by (auto simp: u_def w_def)
  \<comment> \<open>cubic bound @{text "u - u^3 \<le> 243/625"} on @{text "[0,1]"},
    via @{text "r = 577/1000 \<approx> 1/\<surd>3"}\<close>
  define r :: real where "r = 577 / 1000"
  have "u ^ 3 - u + 243 / 625 = (u - r)\<^sup>2 * (u + 2 * r) + (3 * r\<^sup>2 - 1) * u + (243 /
    625 - 2 * r ^ 3)"
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
  moreover have "0 \<le> (u - r)\<^sup>2 * (u + 2 * r)" using u0 by (simp add: r_def)
  moreover have "(3 * r\<^sup>2 - 1) * u \<ge> 3 * r\<^sup>2 - 1"
  proof -
    have "3 * r\<^sup>2 - 1 \<le> 0" by (simp add: r_def power2_eq_square)
    thus ?thesis using u1 by (metis mult_left_mono_neg mult.right_neutral)
  qed
  moreover have "0 \<le> (3 * r\<^sup>2 - 1) + (243 / 625 - 2 * r ^ 3)"
    by (simp add: r_def power2_eq_square power3_eq_cube)
  ultimately have cub: "u - u ^ 3 \<le> 243 / 625" by linarith
  have "w - w ^ 3 = 4 * (v * (1 - v) * (2 * v - 1))" unfolding w_def
    by (simp add: power3_eq_cube algebra_simps)
  hence G: "G0_r v = (w - w ^ 3) / 24" by (simp add: G0_r_def)
  have "\<bar>w - w ^ 3\<bar> = u - u ^ 3"
  proof -
    have "w - w ^ 3 = w * (1 - w\<^sup>2)"
      by (simp add: algebra_simps power2_eq_square power3_eq_cube)
    moreover have "0 \<le> 1 - w\<^sup>2" using u1 by (simp add: u_def abs_square_le_1)
    ultimately have "\<bar>w - w ^ 3\<bar> = u * (1 - w\<^sup>2)" by (simp add: abs_mult u_def)
    also have "w\<^sup>2 = u\<^sup>2" by (simp add: u_def)
    finally show ?thesis by (simp add: algebra_simps power2_eq_square power3_eq_cube)
  qed
  thus ?thesis unfolding G using cub by simp
qed

theorem Cper_bound: "\<bar>Cper x\<bar> < 16"
proof -
  have b1: "\<bar>G0_r (frac (alpha_r * x))\<bar> \<le> 81 / 5000"
    by (rule G0_r_bound) (auto simp: frac_ge_0 frac_lt_1 less_imp_le)
  have b2: "\<bar>G0_r (frac x)\<bar> \<le> 81 / 5000"
    by (rule G0_r_bound) (auto simp: frac_ge_0 frac_lt_1 less_imp_le)
  have "\<bar>Cper x\<bar> \<le> 74 / alpha_r * \<bar>G0_r (frac (alpha_r * x))\<bar> + lam_r *
    \<bar>G0_r (frac x)\<bar>"
    unfolding Cper_def alpha_r_def lam_r_def by (simp add: abs_mult)
  also have "\<dots> \<le> 74 / alpha_r * (81 / 5000) + lam_r * (81 / 5000)"
    using b1 b2 by (intro add_mono mult_left_mono) (auto simp: alpha_r_def lam_r_def)
  also have "\<dots> < 16" by (simp add: alpha_r_def lam_r_def)
  finally show ?thesis .
qed


subsection \<open>(5.10): @{text "\<integral>_{1/3}^{2\<lambda>} outerIntegrand = I_out"}
  by 11 affine pieces\<close>

text \<open>On each piece @{text "outerIntegrand y = c0 + c1 y"};
  @{text "\<lfloor>1/y\<rfloor>"} is constant (fact @{text fl}).
  The pieces were generated from Lean's @{text "gen/gen_outer.py"} (29 pieces,
    merged where the formula agrees).\<close>
lemma pos_eq1: "0 \<le> v \<Longrightarrow> pos_r v = v" unfolding pos_r_def by force
lemma pos_eq0: "v \<le> 0 \<Longrightarrow> pos_r v = 0" unfolding pos_r_def by argo

lemma outer_piece_0: "y \<in> {(1 / 3)<..<(43 / 120)} \<Longrightarrow>
  outer_integrand y = (279 / 40) + (- 9) * y"
proof -
  assume y: "y \<in> {(1 / 3)<..<(43 / 120)}"
  have b: "(1 / 3) < y" "y < (43 / 120)" using y by auto
  have "0 < y \<and> of_int 2 * y \<le> 1 \<and> 1 < (of_int 2 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 2" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have cA: "1 / 3 < y \<and> y < 1 / 2" using b by linarith
  have mA: "min alpha_r (1 - 2 * y) = alpha_r"
    by (rule min_absorb1) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pA: "pos_r (1 + alpha_r - 3 * y) = 1 + alpha_r - 3 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pD: "pos_r ((1 + 4 * alpha_r - 3 * y) - (1 + alpha_r - 3 * y)) =
    (1 + 4 * alpha_r - 3 * y) - (1 + alpha_r - 3 * y)"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 2 * lam_r - real 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 2 * lam_r - real 3 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 2 * lam_r - real 4 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 2 * lam_r - real 5 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_P[OF cA] mA pA pD s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_1: "y \<in> {(43 / 120)<..<(37 / 100)} \<Longrightarrow>
  outer_integrand y = (451 / 40) + (- 21) * y"
proof -
  assume y: "y \<in> {(43 / 120)<..<(37 / 100)}"
  have b: "(43 / 120) < y" "y < (37 / 100)" using y by auto
  have "0 < y \<and> of_int 2 * y \<le> 1 \<and> 1 < (of_int 2 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 2" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have cA: "1 / 3 < y \<and> y < 1 / 2" using b by linarith
  have mA: "min alpha_r (1 - 2 * y) = alpha_r"
    by (rule min_absorb1) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pA: "pos_r (1 + alpha_r - 3 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pD: "pos_r ((1 + 4 * alpha_r - 3 * y) - 0) = (1 + 4 * alpha_r - 3 * y) - 0"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 2 * lam_r - real 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 2 * lam_r - real 3 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 2 * lam_r - real 4 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 2 * lam_r - real 5 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_P[OF cA] mA pA pD s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_2: "y \<in> {(37 / 100)<..<(13 / 30)} \<Longrightarrow>
  outer_integrand y = (377 / 40) + (- 16) * y"
proof -
  assume y: "y \<in> {(37 / 100)<..<(13 / 30)}"
  have b: "(37 / 100) < y" "y < (13 / 30)" using y by auto
  have "0 < y \<and> of_int 2 * y \<le> 1 \<and> 1 < (of_int 2 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 2" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have cA: "1 / 3 < y \<and> y < 1 / 2" using b by linarith
  have mA: "min alpha_r (1 - 2 * y) = alpha_r"
    by (rule min_absorb1) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pA: "pos_r (1 + alpha_r - 3 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pD: "pos_r ((1 + 4 * alpha_r - 3 * y) - 0) = (1 + 4 * alpha_r - 3 * y) - 0"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 2 * lam_r - real 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 2 * lam_r - real 3 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 2 * lam_r - real 4 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_P[OF cA] mA pA pD s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_3: "y \<in> {(13 / 30)<..<(37 / 80)} \<Longrightarrow>
  outer_integrand y = (429 / 40) + (- 19) * y"
proof -
  assume y: "y \<in> {(13 / 30)<..<(37 / 80)}"
  have b: "(13 / 30) < y" "y < (37 / 80)" using y by auto
  have "0 < y \<and> of_int 2 * y \<le> 1 \<and> 1 < (of_int 2 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 2" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have cA: "1 / 3 < y \<and> y < 1 / 2" using b by linarith
  have mA: "min alpha_r (1 - 2 * y) = alpha_r"
    by (rule min_absorb1) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pA: "pos_r (1 + alpha_r - 3 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pD: "pos_r ((1 + 4 * alpha_r - 3 * y) - 0) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 2 * lam_r - real 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 2 * lam_r - real 3 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 2 * lam_r - real 4 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_P[OF cA] mA pA pD s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_4: "y \<in> {(37 / 80)<..<(1 / 2)} \<Longrightarrow>
  outer_integrand y = (17 / 4) + (- 5) * y"
proof -
  assume y: "y \<in> {(37 / 80)<..<(1 / 2)}"
  have b: "(37 / 80) < y" "y < (1 / 2)" using y by auto
  have "0 < y \<and> of_int 2 * y \<le> 1 \<and> 1 < (of_int 2 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 2" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have cA: "1 / 3 < y \<and> y < 1 / 2" using b by linarith
  have mA: "min alpha_r (1 - 2 * y) = 1 - 2 * y"
    by (rule min_absorb2) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pA: "pos_r (1 + alpha_r - 3 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pD: "pos_r ((1 + 4 * alpha_r - 3 * y) - 0) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 2 * lam_r - real 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 2 * lam_r - real 3 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_P[OF cA] mA pA pD s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_5: "y \<in> {(1 / 2)<..<(43 / 80)} \<Longrightarrow>
  outer_integrand y = (51 / 10) + (- 3) * y"
proof -
  assume y: "y \<in> {(1 / 2)<..<(43 / 80)}"
  have b: "(1 / 2) < y" "y < (43 / 80)" using y by auto
  have "0 < y \<and> of_int 1 * y \<le> 1 \<and> 1 < (of_int 1 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 1" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have nA: "\<not> (1 / 3 < y \<and> y < 1 / 2)" using b by linarith
  have cB: "1 / 2 < y \<and> y < 1" using b by linarith
  have mB: "min alpha_r (1 - y) = alpha_r"
    by (rule min_absorb1) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pB1: "pos_r (1 + alpha_r - 2 * y) = 1 + alpha_r - 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pB2: "pos_r (1 + 4 * alpha_r - 2 * y) = 1 + 4 * alpha_r - 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 2 * lam_r - real 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 2 * lam_r - real 3 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_not_P[OF nA] if_P[OF cB] mB pB1 pB2 s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_6: "y \<in> {(43 / 80)<..<(37 / 60)} \<Longrightarrow>
  outer_integrand y = (231 / 20) + (- 15) * y"
proof -
  assume y: "y \<in> {(43 / 80)<..<(37 / 60)}"
  have b: "(43 / 80) < y" "y < (37 / 60)" using y by auto
  have "0 < y \<and> of_int 1 * y \<le> 1 \<and> 1 < (of_int 1 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 1" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have nA: "\<not> (1 / 3 < y \<and> y < 1 / 2)" using b by linarith
  have cB: "1 / 2 < y \<and> y < 1" using b by linarith
  have mB: "min alpha_r (1 - y) = alpha_r"
    by (rule min_absorb1) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pB1: "pos_r (1 + alpha_r - 2 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pB2: "pos_r (1 + 4 * alpha_r - 2 * y) = 1 + 4 * alpha_r - 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 2 * lam_r - real 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 2 * lam_r - real 3 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_not_P[OF nA] if_P[OF cB] mB pB1 pB2 s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_7: "y \<in> {(37 / 60)<..<(13 / 20)} \<Longrightarrow>
  outer_integrand y = (97 / 10) + (- 12) * y"
proof -
  assume y: "y \<in> {(37 / 60)<..<(13 / 20)}"
  have b: "(37 / 60) < y" "y < (13 / 20)" using y by auto
  have "0 < y \<and> of_int 1 * y \<le> 1 \<and> 1 < (of_int 1 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 1" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have nA: "\<not> (1 / 3 < y \<and> y < 1 / 2)" using b by linarith
  have cB: "1 / 2 < y \<and> y < 1" using b by linarith
  have mB: "min alpha_r (1 - y) = alpha_r"
    by (rule min_absorb1) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pB1: "pos_r (1 + alpha_r - 2 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pB2: "pos_r (1 + 4 * alpha_r - 2 * y) = 1 + 4 * alpha_r - 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 2 * lam_r - real 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_not_P[OF nA] if_P[OF cB] mB pB1 pB2 s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_8: "y \<in> {(13 / 20)<..<(37 / 40)} \<Longrightarrow>
  outer_integrand y = (42 / 5) + (- 10) * y"
proof -
  assume y: "y \<in> {(13 / 20)<..<(37 / 40)}"
  have b: "(13 / 20) < y" "y < (37 / 40)" using y by auto
  have "0 < y \<and> of_int 1 * y \<le> 1 \<and> 1 < (of_int 1 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 1" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have nA: "\<not> (1 / 3 < y \<and> y < 1 / 2)" using b by linarith
  have cB: "1 / 2 < y \<and> y < 1" using b by linarith
  have mB: "min alpha_r (1 - y) = alpha_r"
    by (rule min_absorb1) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pB1: "pos_r (1 + alpha_r - 2 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pB2: "pos_r (1 + 4 * alpha_r - 2 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 2 * lam_r - real 2 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_not_P[OF nA] if_P[OF cB] mB pB1 pB2 s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_9: "y \<in> {(37 / 40)<..<1} \<Longrightarrow> outer_integrand y = 1 + (- 2) * y"
proof -
  assume y: "y \<in> {(37 / 40)<..<1}"
  have b: "(37 / 40) < y" "y < 1" using y by auto
  have "0 < y \<and> of_int 1 * y \<le> 1 \<and> 1 < (of_int 1 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 1" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have nA: "\<not> (1 / 3 < y \<and> y < 1 / 2)" using b by linarith
  have cB: "1 / 2 < y \<and> y < 1" using b by linarith
  have mB: "min alpha_r (1 - y) = 1 - y"
    by (rule min_absorb2) (use b in \<open>unfold alpha_r_def, linarith\<close>)
  have pB1: "pos_r (1 + alpha_r - 2 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have pB2: "pos_r (1 + 4 * alpha_r - 2 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_not_P[OF nA] if_P[OF cB] mB pB1 pB2 s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

lemma outer_piece_10: "y \<in> {1<..<(37 / 20)} \<Longrightarrow>
  outer_integrand y = (37 / 20) + (- 1) * y"
proof -
  assume y: "y \<in> {1<..<(37 / 20)}"
  have b: "1 < y" "y < (37 / 20)" using y by auto
  have "0 < y \<and> of_int 0 * y \<le> 1 \<and> 1 < (of_int 0 + 1) * y" using b by auto
  hence fl: "floor (1 / y) = 0" using floor_inv_eq by blast
  have s: "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) =
    pos_r (2 * lam_r - real 1 * y) + (pos_r (2 * lam_r - real 2 * y) + (pos_r (2 * lam_r - real 3 *
    y) + (pos_r (2 * lam_r - real 4 * y) + pos_r (2 * lam_r - real 5 * y))))"
    by (auto simp: numeral_eq_Suc atLeastAtMostSuc_conv)
  have nA: "\<not> (1 / 3 < y \<and> y < 1 / 2)" using b by linarith
  have nB: "\<not> (1 / 2 < y \<and> y < 1)" using b by linarith
  have s1: "pos_r (2 * lam_r - real 1 * y) = 2 * lam_r - real 1 * y"
    by (rule pos_eq1) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s2: "pos_r (2 * lam_r - real 2 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s3: "pos_r (2 * lam_r - real 3 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s4: "pos_r (2 * lam_r - real 4 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  have s5: "pos_r (2 * lam_r - real 5 * y) = 0"
    by (rule pos_eq0) (use b in \<open>unfold alpha_r_def lam_r_def of_nat_numeral of_nat_1,
    linarith\<close>)
  show ?thesis unfolding outer_integrand_def fl s R0_r_def dfun_r_def
    unfolding if_not_P[OF nA] if_not_P[OF nB] s1 s2 s3 s4 s5
    by (simp add: alpha_r_def lam_r_def algebra_simps)
qed

text \<open>The pieces chained from @{text "1/3"} to @{text "2\<lambda> = 37/20"}.\<close>
theorem outer_integral_value:
  "interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (2 * lam_r)) outer_integrand =
    of_rat Iout"
proof -
  have "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (43 /
    120)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (43 / 120)) outer_integrand =
        ((279 / 40) * (43 / 120) + (- 9) * (43 / 120) ^ 2 / 2 + 0 * (43 / 120) ^ 3 / 3) - ((279 /
        40) * (1 / 3) + (- 9) * (1 / 3) ^ 2 / 2 + 0 * (1 / 3) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_0)
  hence c0: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (43 /
    120)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (43 / 120)) outer_integrand =
        (309 / 3200)"
    by (simp add: power2_eq_square power3_eq_cube)
  have o1: "interval_lebesgue_integrable lborel (ereal (43 / 120)) (ereal (37 /
    100)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (43 / 120)) (ereal (37 / 100)) outer_integrand =
        ((451 / 40) * (37 / 100) + (- 21) * (37 / 100) ^ 2 / 2 + 0 * (37 / 100) ^ 3 / 3) - ((451 /
        40) * (43 / 120) + (- 21) * (43 / 120) ^ 2 / 2 + 0 * (43 / 120) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_1)
  have c1: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (37 /
    100)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (37 / 100)) outer_integrand =
        (8333 / 60000)"
    using chain[OF _ _ c0 o1] by (simp add: power2_eq_square power3_eq_cube)
  have o2: "interval_lebesgue_integrable lborel (ereal (37 / 100)) (ereal (13 /
    30)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (37 / 100)) (ereal (13 / 30)) outer_integrand =
        ((377 / 40) * (13 / 30) + (- 16) * (13 / 30) ^ 2 / 2 + 0 * (13 / 30) ^ 3 / 3) - ((377 /
        40) * (37 / 100) + (- 16) * (37 / 100) ^ 2 / 2 + 0 * (37 / 100) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_2)
  have c2: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (13 /
    30)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (13 / 30)) outer_integrand =
        (2959 / 9000)"
    using chain[OF _ _ c1 o2] by (simp add: power2_eq_square power3_eq_cube)
  have o3: "interval_lebesgue_integrable lborel (ereal (13 / 30)) (ereal (37 /
    80)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (13 / 30)) (ereal (37 / 80)) outer_integrand =
        ((429 / 40) * (37 / 80) + (- 19) * (37 / 80) ^ 2 / 2 + 0 * (37 / 80) ^ 3 / 3) - ((429 /
        40) * (13 / 30) + (- 19) * (13 / 30) ^ 2 / 2 + 0 * (13 / 30) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_3)
  have c3: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (37 /
    80)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (37 / 80)) outer_integrand =
        (75527 / 192000)"
    using chain[OF _ _ c2 o3] by (simp add: power2_eq_square power3_eq_cube)
  have o4: "interval_lebesgue_integrable lborel (ereal (37 / 80)) (ereal (1 /
    2)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (37 / 80)) (ereal (1 / 2)) outer_integrand =
        ((17 / 4) * (1 / 2) + (- 5) * (1 / 2) ^ 2 / 2 + 0 * (1 / 2) ^ 3 / 3) - ((17 / 4) * (37 /
        80) + (- 5) * (37 / 80) ^ 2 / 2 + 0 * (37 / 80) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_4)
  have c4: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (1 /
    2)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (1 / 2)) outer_integrand =
        (44401 / 96000)"
    using chain[OF _ _ c3 o4] by (simp add: power2_eq_square power3_eq_cube)
  have o5: "interval_lebesgue_integrable lborel (ereal (1 / 2)) (ereal (43 /
    80)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 2)) (ereal (43 / 80)) outer_integrand =
        ((51 / 10) * (43 / 80) + (- 3) * (43 / 80) ^ 2 / 2 + 0 * (43 / 80) ^ 3 / 3) - ((51 / 10) *
        (1 / 2) + (- 3) * (1 / 2) ^ 2 / 2 + 0 * (1 / 2) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_5)
  have c5: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (43 /
    80)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (43 / 80)) outer_integrand =
        (114317 / 192000)"
    using chain[OF _ _ c4 o5] by (simp add: power2_eq_square power3_eq_cube)
  have o6: "interval_lebesgue_integrable lborel (ereal (43 / 80)) (ereal (37 /
    60)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (43 / 80)) (ereal (37 / 60)) outer_integrand =
        ((231 / 20) * (37 / 60) + (- 15) * (37 / 60) ^ 2 / 2 + 0 * (37 / 60) ^ 3 / 3) - ((231 /
        20) * (43 / 80) + (- 15) * (43 / 80) ^ 2 / 2 + 0 * (43 / 80) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_6)
  have c6: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (37 /
    60)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (37 / 60)) outer_integrand =
        (79151 / 96000)"
    using chain[OF _ _ c5 o6] by (simp add: power2_eq_square power3_eq_cube)
  have o7: "interval_lebesgue_integrable lborel (ereal (37 / 60)) (ereal (13 /
    20)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (37 / 60)) (ereal (13 / 20)) outer_integrand =
        ((97 / 10) * (13 / 20) + (- 12) * (13 / 20) ^ 2 / 2 + 0 * (13 / 20) ^ 3 / 3) - ((97 / 10) *
        (37 / 60) + (- 12) * (37 / 60) ^ 2 / 2 + 0 * (37 / 60) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_7)
  have c7: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (13 /
    20)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (13 / 20)) outer_integrand =
        (85871 / 96000)"
    using chain[OF _ _ c6 o7] by (simp add: power2_eq_square power3_eq_cube)
  have o8: "interval_lebesgue_integrable lborel (ereal (13 / 20)) (ereal (37 /
    40)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (13 / 20)) (ereal (37 / 40)) outer_integrand =
        ((42 / 5) * (37 / 40) + (- 10) * (37 / 40) ^ 2 / 2 + 0 * (37 / 40) ^ 3 / 3) - ((42 / 5) *
        (13 / 20) + (- 10) * (13 / 20) ^ 2 / 2 + 0 * (13 / 20) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_8)
  have c8: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (37 /
    40)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (37 / 40)) outer_integrand =
        (99731 / 96000)"
    using chain[OF _ _ c7 o8] by (simp add: power2_eq_square power3_eq_cube)
  have o9: "interval_lebesgue_integrable lborel (ereal (37 / 40)) (ereal 1) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (37 / 40)) (ereal 1) outer_integrand =
        (1 * 1 + (- 2) * 1 ^ 2 / 2 + 0 * 1 ^ 3 / 3) - (1 * (37 / 40) + (- 2) * (37 / 40) ^ 2 / 2 +
        0 * (37 / 40) ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_9)
  have c9: "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal 1) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal 1) outer_integrand = (93071 / 96000)"
    using chain[OF _ _ c8 o9] by (simp add: power2_eq_square power3_eq_cube)
  have o10: "interval_lebesgue_integrable lborel (ereal 1) (ereal (37 / 20)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal 1) (ereal (37 / 20)) outer_integrand =
        ((37 / 20) * (37 / 20) + (- 1) * (37 / 20) ^ 2 / 2 + 0 * (37 / 20) ^ 3 / 3) - ((37 / 20) *
        1 + (- 1) * 1 ^ 2 / 2 + 0 * 1 ^ 3 / 3)"
    by (rule piece_quad) (simp_all add: outer_piece_10)
  have "interval_lebesgue_integrable lborel (ereal (1 / 3)) (ereal (37 / 20)) outer_integrand \<and>
      interval_lebesgue_integral lborel (ereal (1 / 3)) (ereal (37 / 20)) outer_integrand =
        (127751 / 96000)"
    using chain[OF _ _ c9 o10] by (simp add: power2_eq_square power3_eq_cube)
  thus ?thesis by (simp add: lam_r_def Iout_def of_rat_divide)
qed


subsection \<open>(5.18): @{text "\<integral>_3^{20} R(x)/x^3 dx"} by 143 affine pieces\<close>

text \<open>On each piece @{text "R(x) = A x + B"} (Lean @{text "gen/gen_inner.py"};
  breakpoints are the multiples of
  @{text "1/2, 20/3, 20/37, 10/23, 10/3, 20/43"} in @{text "[3, 20]"}).  The first fact of each
    piece gives the floors
  @{text "(\<lfloor>x\<rfloor>, \<lfloor>\<alpha>x\<rfloor>, \<lfloor>2H_c x\<rfloor>,
    \<lfloor>2x\<rfloor>, \<lfloor>2\<lambda>x\<rfloor>)"} to feed @{text "R_on_piece"};
    after that the identity follows
  from @{text "Qc_def"}, @{text "d0_def"}, @{text "es_def"},
    @{text "pos_r_def"} with min/max/if resolved by the linear side conditions.\<close>
lemma inner_piece_0: "x \<in> {3<..<(70 / 23)} \<Longrightarrow> R_r x = (18 / 5) * x + (- 6)"
proof -
  assume x: "x \<in> {3<..<(70 / 23)}"
  have b: "3 < x" "x < (70 / 23)" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 6 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 6 + 1 \<and> real 6 \<le> 2 * x \<and>
      2 * x < real 6 + 1 \<and>
    real 5 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 5 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 6) (2 * x - real 6) (2 *
        (lam_r * x) - real 5)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_1: "x \<in> {(70 / 23)<..<(120 / 37)} \<Longrightarrow>
  R_r x = (49 / 20) * x + (- 5 / 2)"
proof -
  assume x: "x \<in> {(70 / 23)<..<(120 / 37)}"
  have b: "(70 / 23) < x" "x < (120 / 37)" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 7 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 7 + 1 \<and> real 6 \<le> 2 * x \<and>
      2 * x < real 6 + 1 \<and>
    real 5 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 5 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 7) (2 * x - real 6) (2 *
        (lam_r * x) - real 5)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_2: "x \<in> {(120 / 37)<..<(140 / 43)} \<Longrightarrow>
  R_r x = (283 / 40) * x + (- 35 / 2)"
proof -
  assume x: "x \<in> {(120 / 37)<..<(140 / 43)}"
  have b: "(120 / 37) < x" "x < (140 / 43)" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 7 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 7 + 1 \<and> real 6 \<le> 2 * x \<and>
      2 * x < real 6 + 1 \<and>
    real 6 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 6 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 7) (2 * x - real 6) (2 *
        (lam_r * x) - real 6)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_3: "x \<in> {(140 / 43)<..<(10 / 3)} \<Longrightarrow>
  R_r x = (283 / 40) * x + (- 35 / 2)"
proof -
  assume x: "x \<in> {(140 / 43)<..<(10 / 3)}"
  have b: "(140 / 43) < x" "x < (10 / 3)" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 7 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 7 + 1 \<and> real 6 \<le> 2 * x \<and>
      2 * x < real 6 + 1 \<and>
    real 6 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 6 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 7) (2 * x - real 6) (2 *
        (lam_r * x) - real 6)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_4: "x \<in> {(10 / 3)<..<(80 / 23)} \<Longrightarrow>
  R_r x = (277 / 40) * x + (- 17)"
proof -
  assume x: "x \<in> {(10 / 3)<..<(80 / 23)}"
  have b: "(10 / 3) < x" "x < (80 / 23)" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 7 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 7 + 1 \<and> real 6 \<le> 2 * x \<and>
      2 * x < real 6 + 1 \<and>
    real 6 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 6 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 7) (2 * x - real 6) (2 *
        (lam_r * x) - real 6)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_5: "x \<in> {(80 / 23)<..<(7 / 2)} \<Longrightarrow>
  R_r x = (231 / 40) * x + (- 13)"
proof -
  assume x: "x \<in> {(80 / 23)<..<(7 / 2)}"
  have b: "(80 / 23) < x" "x < (7 / 2)" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 8 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 8 + 1 \<and> real 6 \<le> 2 * x \<and>
      2 * x < real 6 + 1 \<and>
    real 6 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 6 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 8) (2 * x - real 6) (2 *
        (lam_r * x) - real 6)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_6: "x \<in> {(7 / 2)<..<(160 / 43)} \<Longrightarrow>
  R_r x = (271 / 40) * x + (- 33 / 2)"
proof -
  assume x: "x \<in> {(7 / 2)<..<(160 / 43)}"
  have b: "(7 / 2) < x" "x < (160 / 43)" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 8 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 8 + 1 \<and> real 7 \<le> 2 * x \<and>
      2 * x < real 7 + 1 \<and>
    real 6 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 6 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 8) (2 * x - real 7) (2 *
        (lam_r * x) - real 6)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_7: "x \<in> {(160 / 43)<..<(140 / 37)} \<Longrightarrow>
  R_r x = (71 / 20) * x + (- 9 / 2)"
proof -
  assume x: "x \<in> {(160 / 43)<..<(140 / 37)}"
  have b: "(160 / 43) < x" "x < (140 / 37)" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 8 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 8 + 1 \<and> real 7 \<le> 2 * x \<and>
      2 * x < real 7 + 1 \<and>
    real 6 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 6 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 8) (2 * x - real 7) (2 *
        (lam_r * x) - real 6)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_8: "x \<in> {(140 / 37)<..<(90 / 23)} \<Longrightarrow>
  R_r x = (27 / 5) * x + (- 23 / 2)"
proof -
  assume x: "x \<in> {(140 / 37)<..<(90 / 23)}"
  have b: "(140 / 37) < x" "x < (90 / 23)" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 8 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 8 + 1 \<and> real 7 \<le> 2 * x \<and>
      2 * x < real 7 + 1 \<and>
    real 7 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 7 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 8) (2 * x - real 7) (2 *
        (lam_r * x) - real 7)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_9: "x \<in> {(90 / 23)<..<4} \<Longrightarrow> R_r x = (17 / 4) * x + (- 7)"
proof -
  assume x: "x \<in> {(90 / 23)<..<4}"
  have b: "(90 / 23) < x" "x < 4" using x by auto
  have "real 3 \<le> x \<and> x < real 3 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 9 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 9 + 1 \<and> real 7 \<le> 2 * x \<and>
      2 * x < real 7 + 1 \<and>
    real 7 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 7 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 3) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 3) (alpha_r * x - real 0) (2 * Hc_r * x - real 9) (2 * x - real 7) (2 *
        (lam_r * x) - real 7)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_10: "x \<in> {4<..<(180 / 43)} \<Longrightarrow> R_r x = (17 / 5) * x + (- 11)"
proof -
  assume x: "x \<in> {4<..<(180 / 43)}"
  have b: "4 < x" "x < (180 / 43)" using x by auto
  have "real 4 \<le> x \<and> x < real 4 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 9 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 9 + 1 \<and> real 8 \<le> 2 * x \<and>
      2 * x < real 8 + 1 \<and>
    real 7 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 7 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 4) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 4) (alpha_r * x - real 0) (2 * Hc_r * x - real 9) (2 * x - real 8) (2 *
        (lam_r * x) - real 7)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_11: "x \<in> {(180 / 43)<..<(160 / 37)} \<Longrightarrow>
  R_r x = (17 / 5) * x + (- 11)"
proof -
  assume x: "x \<in> {(180 / 43)<..<(160 / 37)}"
  have b: "(180 / 43) < x" "x < (160 / 37)" using x by auto
  have "real 4 \<le> x \<and> x < real 4 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 9 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 9 + 1 \<and> real 8 \<le> 2 * x \<and>
      2 * x < real 8 + 1 \<and>
    real 7 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 7 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 4) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 4) (alpha_r * x - real 0) (2 * Hc_r * x - real 9) (2 * x - real 8) (2 *
        (lam_r * x) - real 7)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_12: "x \<in> {(160 / 37)<..<(100 / 23)} \<Longrightarrow>
  R_r x = (321 / 40) * x + (- 31)"
proof -
  assume x: "x \<in> {(160 / 37)<..<(100 / 23)}"
  have b: "(160 / 37) < x" "x < (100 / 23)" using x by auto
  have "real 4 \<le> x \<and> x < real 4 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 9 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 9 + 1 \<and> real 8 \<le> 2 * x \<and>
      2 * x < real 8 + 1 \<and>
    real 8 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 8 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 4) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 4) (alpha_r * x - real 0) (2 * Hc_r * x - real 9) (2 * x - real 8) (2 *
        (lam_r * x) - real 8)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_13: "x \<in> {(100 / 23)<..<(9 / 2)} \<Longrightarrow>
  R_r x = (55 / 8) * x + (- 26)"
proof -
  assume x: "x \<in> {(100 / 23)<..<(9 / 2)}"
  have b: "(100 / 23) < x" "x < (9 / 2)" using x by auto
  have "real 4 \<le> x \<and> x < real 4 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 10 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 10 + 1 \<and> real 8 \<le> 2 * x \<and>
      2 * x < real 8 + 1 \<and>
    real 8 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 8 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 4) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 4) (alpha_r * x - real 0) (2 * Hc_r * x - real 10) (2 * x - real 8) (2 *
        (lam_r * x) - real 8)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_14: "x \<in> {(9 / 2)<..<(200 / 43)} \<Longrightarrow>
  R_r x = (63 / 8) * x + (- 61 / 2)"
proof -
  assume x: "x \<in> {(9 / 2)<..<(200 / 43)}"
  have b: "(9 / 2) < x" "x < (200 / 43)" using x by auto
  have "real 4 \<le> x \<and> x < real 4 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 10 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 10 + 1 \<and> real 9 \<le> 2 * x \<and>
      2 * x < real 9 + 1 \<and>
    real 8 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 8 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 4) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 4) (alpha_r * x - real 0) (2 * Hc_r * x - real 10) (2 * x - real 9) (2 *
        (lam_r * x) - real 8)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_15: "x \<in> {(200 / 43)<..<(110 / 23)} \<Longrightarrow>
  R_r x = (93 / 20) * x + (- 31 / 2)"
proof -
  assume x: "x \<in> {(200 / 43)<..<(110 / 23)}"
  have b: "(200 / 43) < x" "x < (110 / 23)" using x by auto
  have "real 4 \<le> x \<and> x < real 4 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 10 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 10 + 1 \<and> real 9 \<le> 2 * x \<and>
      2 * x < real 9 + 1 \<and>
    real 8 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 8 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 4) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 4) (alpha_r * x - real 0) (2 * Hc_r * x - real 10) (2 * x - real 9) (2 *
        (lam_r * x) - real 8)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_16: "x \<in> {(110 / 23)<..<(180 / 37)} \<Longrightarrow>
  R_r x = (7 / 2) * x + (- 10)"
proof -
  assume x: "x \<in> {(110 / 23)<..<(180 / 37)}"
  have b: "(110 / 23) < x" "x < (180 / 37)" using x by auto
  have "real 4 \<le> x \<and> x < real 4 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 11 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 11 + 1 \<and> real 9 \<le> 2 * x \<and>
      2 * x < real 9 + 1 \<and>
    real 8 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 8 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 4) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 4) (alpha_r * x - real 0) (2 * Hc_r * x - real 11) (2 * x - real 9) (2 *
        (lam_r * x) - real 8)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_17: "x \<in> {(180 / 37)<..<5} \<Longrightarrow> R_r x = (107 / 20) * x + (- 19)"
proof -
  assume x: "x \<in> {(180 / 37)<..<5}"
  have b: "(180 / 37) < x" "x < 5" using x by auto
  have "real 4 \<le> x \<and> x < real 4 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 11 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 11 + 1 \<and> real 9 \<le> 2 * x \<and>
      2 * x < real 9 + 1 \<and>
    real 9 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 9 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 4) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 4) (alpha_r * x - real 0) (2 * Hc_r * x - real 11) (2 * x - real 9) (2 *
        (lam_r * x) - real 9)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_18: "x \<in> {5<..<(220 / 43)} \<Longrightarrow> R_r x = (9 / 2) * x + (- 24)"
proof -
  assume x: "x \<in> {5<..<(220 / 43)}"
  have b: "5 < x" "x < (220 / 43)" using x by auto
  have "real 5 \<le> x \<and> x < real 5 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 11 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 11 + 1 \<and> real 10 \<le> 2 * x \<and>
      2 * x < real 10 + 1 \<and>
    real 9 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 9 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 5) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 5) (alpha_r * x - real 0) (2 * Hc_r * x - real 11) (2 * x - real 10) (2 *
        (lam_r * x) - real 9)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_19: "x \<in> {(220 / 43)<..<(120 / 23)} \<Longrightarrow>
  R_r x = (9 / 2) * x + (- 24)"
proof -
  assume x: "x \<in> {(220 / 43)<..<(120 / 23)}"
  have b: "(220 / 43) < x" "x < (120 / 23)" using x by auto
  have "real 5 \<le> x \<and> x < real 5 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 11 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 11 + 1 \<and> real 10 \<le> 2 * x \<and>
      2 * x < real 10 + 1 \<and>
    real 9 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 9 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 5) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 5) (alpha_r * x - real 0) (2 * Hc_r * x - real 11) (2 * x - real 10) (2 *
        (lam_r * x) - real 9)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_20: "x \<in> {(120 / 23)<..<(200 / 37)} \<Longrightarrow>
  R_r x = (67 / 20) * x + (- 18)"
proof -
  assume x: "x \<in> {(120 / 23)<..<(200 / 37)}"
  have b: "(120 / 23) < x" "x < (200 / 37)" using x by auto
  have "real 5 \<le> x \<and> x < real 5 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 12 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 12 + 1 \<and> real 10 \<le> 2 * x \<and>
      2 * x < real 10 + 1 \<and>
    real 9 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 9 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 5) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 5) (alpha_r * x - real 0) (2 * Hc_r * x - real 12) (2 * x - real 10) (2 *
        (lam_r * x) - real 9)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_21: "x \<in> {(200 / 37)<..<(11 / 2)} \<Longrightarrow>
  R_r x = (319 / 40) * x + (- 43)"
proof -
  assume x: "x \<in> {(200 / 37)<..<(11 / 2)}"
  have b: "(200 / 37) < x" "x < (11 / 2)" using x by auto
  have "real 5 \<le> x \<and> x < real 5 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 12 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 12 + 1 \<and> real 10 \<le> 2 * x \<and>
      2 * x < real 10 + 1 \<and>
    real 10 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 10 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 5) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 5) (alpha_r * x - real 0) (2 * Hc_r * x - real 12) (2 * x - real 10) (2 *
        (lam_r * x) - real 10)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_22: "x \<in> {(11 / 2)<..<(240 / 43)} \<Longrightarrow>
  R_r x = (359 / 40) * x + (- 97 / 2)"
proof -
  assume x: "x \<in> {(11 / 2)<..<(240 / 43)}"
  have b: "(11 / 2) < x" "x < (240 / 43)" using x by auto
  have "real 5 \<le> x \<and> x < real 5 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 12 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 12 + 1 \<and> real 11 \<le> 2 * x \<and>
      2 * x < real 11 + 1 \<and>
    real 10 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 10 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 5) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 5) (alpha_r * x - real 0) (2 * Hc_r * x - real 12) (2 * x - real 11) (2 *
        (lam_r * x) - real 10)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_23: "x \<in> {(240 / 43)<..<(130 / 23)} \<Longrightarrow>
  R_r x = (23 / 4) * x + (- 61 / 2)"
proof -
  assume x: "x \<in> {(240 / 43)<..<(130 / 23)}"
  have b: "(240 / 43) < x" "x < (130 / 23)" using x by auto
  have "real 5 \<le> x \<and> x < real 5 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 12 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 12 + 1 \<and> real 11 \<le> 2 * x \<and>
      2 * x < real 11 + 1 \<and>
    real 10 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 10 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 5) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 5) (alpha_r * x - real 0) (2 * Hc_r * x - real 12) (2 * x - real 11) (2 *
        (lam_r * x) - real 10)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_24: "x \<in> {(130 / 23)<..<(220 / 37)} \<Longrightarrow>
  R_r x = (23 / 5) * x + (- 24)"
proof -
  assume x: "x \<in> {(130 / 23)<..<(220 / 37)}"
  have b: "(130 / 23) < x" "x < (220 / 37)" using x by auto
  have "real 5 \<le> x \<and> x < real 5 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 13 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 13 + 1 \<and> real 11 \<le> 2 * x \<and>
      2 * x < real 11 + 1 \<and>
    real 10 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 10 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 5) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 5) (alpha_r * x - real 0) (2 * Hc_r * x - real 13) (2 * x - real 11) (2 *
        (lam_r * x) - real 10)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_25: "x \<in> {(220 / 37)<..<6} \<Longrightarrow> R_r x = (129 / 20) * x + (- 35)"
proof -
  assume x: "x \<in> {(220 / 37)<..<6}"
  have b: "(220 / 37) < x" "x < 6" using x by auto
  have "real 5 \<le> x \<and> x < real 5 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 13 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 13 + 1 \<and> real 11 \<le> 2 * x \<and>
      2 * x < real 11 + 1 \<and>
    real 11 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 11 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 5) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 5) (alpha_r * x - real 0) (2 * Hc_r * x - real 13) (2 * x - real 11) (2 *
        (lam_r * x) - real 11)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_26: "x \<in> {6<..<(260 / 43)} \<Longrightarrow> R_r x = (28 / 5) * x + (- 41)"
proof -
  assume x: "x \<in> {6<..<(260 / 43)}"
  have b: "6 < x" "x < (260 / 43)" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 13 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 13 + 1 \<and> real 12 \<le> 2 * x \<and>
      2 * x < real 12 + 1 \<and>
    real 11 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 11 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 13) (2 * x - real 12) (2 *
        (lam_r * x) - real 11)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_27: "x \<in> {(260 / 43)<..<(140 / 23)} \<Longrightarrow>
  R_r x = (28 / 5) * x + (- 41)"
proof -
  assume x: "x \<in> {(260 / 43)<..<(140 / 23)}"
  have b: "(260 / 43) < x" "x < (140 / 23)" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 13 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 13 + 1 \<and> real 12 \<le> 2 * x \<and>
      2 * x < real 12 + 1 \<and>
    real 11 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 11 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 13) (2 * x - real 12) (2 *
        (lam_r * x) - real 11)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_28: "x \<in> {(140 / 23)<..<(240 / 37)} \<Longrightarrow>
  R_r x = (89 / 20) * x + (- 34)"
proof -
  assume x: "x \<in> {(140 / 23)<..<(240 / 37)}"
  have b: "(140 / 23) < x" "x < (240 / 37)" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 14 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 14 + 1 \<and> real 12 \<le> 2 * x \<and>
      2 * x < real 12 + 1 \<and>
    real 11 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 11 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 14) (2 * x - real 12) (2 *
        (lam_r * x) - real 11)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_29: "x \<in> {(240 / 37)<..<(13 / 2)} \<Longrightarrow>
  R_r x = (363 / 40) * x + (- 64)"
proof -
  assume x: "x \<in> {(240 / 37)<..<(13 / 2)}"
  have b: "(240 / 37) < x" "x < (13 / 2)" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 14 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 14 + 1 \<and> real 12 \<le> 2 * x \<and>
      2 * x < real 12 + 1 \<and>
    real 12 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 12 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 14) (2 * x - real 12) (2 *
        (lam_r * x) - real 12)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_30: "x \<in> {(13 / 2)<..<(280 / 43)} \<Longrightarrow>
  R_r x = (403 / 40) * x + (- 141 / 2)"
proof -
  assume x: "x \<in> {(13 / 2)<..<(280 / 43)}"
  have b: "(13 / 2) < x" "x < (280 / 43)" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 14 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 14 + 1 \<and> real 13 \<le> 2 * x \<and>
      2 * x < real 13 + 1 \<and>
    real 12 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 12 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 14) (2 * x - real 13) (2 *
        (lam_r * x) - real 12)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_31: "x \<in> {(280 / 43)<..<(150 / 23)} \<Longrightarrow>
  R_r x = (137 / 20) * x + (- 99 / 2)"
proof -
  assume x: "x \<in> {(280 / 43)<..<(150 / 23)}"
  have b: "(280 / 43) < x" "x < (150 / 23)" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 14 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 14 + 1 \<and> real 13 \<le> 2 * x \<and>
      2 * x < real 13 + 1 \<and>
    real 12 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 12 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 14) (2 * x - real 13) (2 *
        (lam_r * x) - real 12)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_32: "x \<in> {(150 / 23)<..<(20 / 3)} \<Longrightarrow>
  R_r x = (57 / 10) * x + (- 42)"
proof -
  assume x: "x \<in> {(150 / 23)<..<(20 / 3)}"
  have b: "(150 / 23) < x" "x < (20 / 3)" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 15 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 15 + 1 \<and> real 13 \<le> 2 * x \<and>
      2 * x < real 13 + 1 \<and>
    real 12 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 12 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 15) (2 * x - real 13) (2 *
        (lam_r * x) - real 12)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_33: "x \<in> {(20 / 3)<..<(160 / 23)} \<Longrightarrow>
  R_r x = (69 / 10) * x + (- 50)"
proof -
  assume x: "x \<in> {(20 / 3)<..<(160 / 23)}"
  have b: "(20 / 3) < x" "x < (160 / 23)" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 15 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 15 + 1 \<and> real 13 \<le> 2 * x \<and>
      2 * x < real 13 + 1 \<and>
    real 12 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 12 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 15) (2 * x - real 13) (2 *
        (lam_r * x) - real 12)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_34: "x \<in> {(160 / 23)<..<(300 / 43)} \<Longrightarrow>
  R_r x = (23 / 4) * x + (- 42)"
proof -
  assume x: "x \<in> {(160 / 23)<..<(300 / 43)}"
  have b: "(160 / 23) < x" "x < (300 / 43)" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 16 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 16 + 1 \<and> real 13 \<le> 2 * x \<and>
      2 * x < real 13 + 1 \<and>
    real 12 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 12 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 16) (2 * x - real 13) (2 *
        (lam_r * x) - real 12)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_35: "x \<in> {(300 / 43)<..<7} \<Longrightarrow> R_r x = (23 / 4) * x + (- 42)"
proof -
  assume x: "x \<in> {(300 / 43)<..<7}"
  have b: "(300 / 43) < x" "x < 7" using x by auto
  have "real 6 \<le> x \<and> x < real 6 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 16 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 16 + 1 \<and> real 13 \<le> 2 * x \<and>
      2 * x < real 13 + 1 \<and>
    real 12 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 12 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 6) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 6) (alpha_r * x - real 0) (2 * Hc_r * x - real 16) (2 * x - real 13) (2 *
        (lam_r * x) - real 12)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_36: "x \<in> {7<..<(260 / 37)} \<Longrightarrow> R_r x = (49 / 10) * x + (- 49)"
proof -
  assume x: "x \<in> {7<..<(260 / 37)}"
  have b: "7 < x" "x < (260 / 37)" using x by auto
  have "real 7 \<le> x \<and> x < real 7 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 16 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 16 + 1 \<and> real 14 \<le> 2 * x \<and>
      2 * x < real 14 + 1 \<and>
    real 12 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 12 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 7) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 7) (alpha_r * x - real 0) (2 * Hc_r * x - real 16) (2 * x - real 14) (2 *
        (lam_r * x) - real 12)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_37: "x \<in> {(260 / 37)<..<(170 / 23)} \<Longrightarrow>
  R_r x = (27 / 4) * x + (- 62)"
proof -
  assume x: "x \<in> {(260 / 37)<..<(170 / 23)}"
  have b: "(260 / 37) < x" "x < (170 / 23)" using x by auto
  have "real 7 \<le> x \<and> x < real 7 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 16 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 16 + 1 \<and> real 14 \<le> 2 * x \<and>
      2 * x < real 14 + 1 \<and>
    real 13 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 13 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 7) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 7) (alpha_r * x - real 0) (2 * Hc_r * x - real 16) (2 * x - real 14) (2 *
        (lam_r * x) - real 13)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_38: "x \<in> {(170 / 23)<..<(320 / 43)} \<Longrightarrow>
  R_r x = (28 / 5) * x + (- 107 / 2)"
proof -
  assume x: "x \<in> {(170 / 23)<..<(320 / 43)}"
  have b: "(170 / 23) < x" "x < (320 / 43)" using x by auto
  have "real 7 \<le> x \<and> x < real 7 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 17 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 17 + 1 \<and> real 14 \<le> 2 * x \<and>
      2 * x < real 14 + 1 \<and>
    real 13 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 13 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 7) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 7) (alpha_r * x - real 0) (2 * Hc_r * x - real 17) (2 * x - real 14) (2 *
        (lam_r * x) - real 13)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_39: "x \<in> {(320 / 43)<..<(15 / 2)} \<Longrightarrow>
  R_r x = (19 / 8) * x + (- 59 / 2)"
proof -
  assume x: "x \<in> {(320 / 43)<..<(15 / 2)}"
  have b: "(320 / 43) < x" "x < (15 / 2)" using x by auto
  have "real 7 \<le> x \<and> x < real 7 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 17 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 17 + 1 \<and> real 14 \<le> 2 * x \<and>
      2 * x < real 14 + 1 \<and>
    real 13 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 13 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 7) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 7) (alpha_r * x - real 0) (2 * Hc_r * x - real 17) (2 * x - real 14) (2 *
        (lam_r * x) - real 13)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_40: "x \<in> {(15 / 2)<..<(280 / 37)} \<Longrightarrow>
  R_r x = (27 / 8) * x + (- 37)"
proof -
  assume x: "x \<in> {(15 / 2)<..<(280 / 37)}"
  have b: "(15 / 2) < x" "x < (280 / 37)" using x by auto
  have "real 7 \<le> x \<and> x < real 7 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 17 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 17 + 1 \<and> real 15 \<le> 2 * x \<and>
      2 * x < real 15 + 1 \<and>
    real 13 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 13 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 7) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 7) (alpha_r * x - real 0) (2 * Hc_r * x - real 17) (2 * x - real 15) (2 *
        (lam_r * x) - real 13)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_41: "x \<in> {(280 / 37)<..<(180 / 23)} \<Longrightarrow> R_r x = 8 * x + (- 72)"
proof -
  assume x: "x \<in> {(280 / 37)<..<(180 / 23)}"
  have b: "(280 / 37) < x" "x < (180 / 23)" using x by auto
  have "real 7 \<le> x \<and> x < real 7 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 17 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 17 + 1 \<and> real 15 \<le> 2 * x \<and>
      2 * x < real 15 + 1 \<and>
    real 14 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 14 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 7) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 7) (alpha_r * x - real 0) (2 * Hc_r * x - real 17) (2 * x - real 15) (2 *
        (lam_r * x) - real 14)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_42: "x \<in> {(180 / 23)<..<(340 / 43)} \<Longrightarrow>
  R_r x = (137 / 20) * x + (- 63)"
proof -
  assume x: "x \<in> {(180 / 23)<..<(340 / 43)}"
  have b: "(180 / 23) < x" "x < (340 / 43)" using x by auto
  have "real 7 \<le> x \<and> x < real 7 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 18 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 18 + 1 \<and> real 15 \<le> 2 * x \<and>
      2 * x < real 15 + 1 \<and>
    real 14 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 14 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 7) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 7) (alpha_r * x - real 0) (2 * Hc_r * x - real 18) (2 * x - real 15) (2 *
        (lam_r * x) - real 14)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_43: "x \<in> {(340 / 43)<..<8} \<Longrightarrow> R_r x = (137 / 20) * x + (- 63)"
proof -
  assume x: "x \<in> {(340 / 43)<..<8}"
  have b: "(340 / 43) < x" "x < 8" using x by auto
  have "real 7 \<le> x \<and> x < real 7 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 18 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 18 + 1 \<and> real 15 \<le> 2 * x \<and>
      2 * x < real 15 + 1 \<and>
    real 14 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 14 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 7) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 7) (alpha_r * x - real 0) (2 * Hc_r * x - real 18) (2 * x - real 15) (2 *
        (lam_r * x) - real 14)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_44: "x \<in> {8<..<(300 / 37)} \<Longrightarrow> R_r x = 6 * x + (- 71)"
proof -
  assume x: "x \<in> {8<..<(300 / 37)}"
  have b: "8 < x" "x < (300 / 37)" using x by auto
  have "real 8 \<le> x \<and> x < real 8 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 18 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 18 + 1 \<and> real 16 \<le> 2 * x \<and>
      2 * x < real 16 + 1 \<and>
    real 14 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 14 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 8) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 8) (alpha_r * x - real 0) (2 * Hc_r * x - real 18) (2 * x - real 16) (2 *
        (lam_r * x) - real 14)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_45: "x \<in> {(300 / 37)<..<(190 / 23)} \<Longrightarrow>
  R_r x = (157 / 20) * x + (- 86)"
proof -
  assume x: "x \<in> {(300 / 37)<..<(190 / 23)}"
  have b: "(300 / 37) < x" "x < (190 / 23)" using x by auto
  have "real 8 \<le> x \<and> x < real 8 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 18 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 18 + 1 \<and> real 16 \<le> 2 * x \<and>
      2 * x < real 16 + 1 \<and>
    real 15 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 15 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 8) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 8) (alpha_r * x - real 0) (2 * Hc_r * x - real 18) (2 * x - real 16) (2 *
        (lam_r * x) - real 15)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_46: "x \<in> {(190 / 23)<..<(360 / 43)} \<Longrightarrow>
  R_r x = (67 / 10) * x + (- 153 / 2)"
proof -
  assume x: "x \<in> {(190 / 23)<..<(360 / 43)}"
  have b: "(190 / 23) < x" "x < (360 / 43)" using x by auto
  have "real 8 \<le> x \<and> x < real 8 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 19 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 19 + 1 \<and> real 16 \<le> 2 * x \<and>
      2 * x < real 16 + 1 \<and>
    real 15 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 15 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 8) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 8) (alpha_r * x - real 0) (2 * Hc_r * x - real 19) (2 * x - real 16) (2 *
        (lam_r * x) - real 15)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_47: "x \<in> {(360 / 43)<..<(17 / 2)} \<Longrightarrow>
  R_r x = (139 / 40) * x + (- 99 / 2)"
proof -
  assume x: "x \<in> {(360 / 43)<..<(17 / 2)}"
  have b: "(360 / 43) < x" "x < (17 / 2)" using x by auto
  have "real 8 \<le> x \<and> x < real 8 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 19 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 19 + 1 \<and> real 16 \<le> 2 * x \<and>
      2 * x < real 16 + 1 \<and>
    real 15 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 15 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 8) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 8) (alpha_r * x - real 0) (2 * Hc_r * x - real 19) (2 * x - real 16) (2 *
        (lam_r * x) - real 15)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_48: "x \<in> {(17 / 2)<..<(320 / 37)} \<Longrightarrow>
  R_r x = (179 / 40) * x + (- 58)"
proof -
  assume x: "x \<in> {(17 / 2)<..<(320 / 37)}"
  have b: "(17 / 2) < x" "x < (320 / 37)" using x by auto
  have "real 8 \<le> x \<and> x < real 8 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 19 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 19 + 1 \<and> real 17 \<le> 2 * x \<and>
      2 * x < real 17 + 1 \<and>
    real 15 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 15 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 8) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 8) (alpha_r * x - real 0) (2 * Hc_r * x - real 19) (2 * x - real 17) (2 *
        (lam_r * x) - real 15)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_49: "x \<in> {(320 / 37)<..<(200 / 23)} \<Longrightarrow>
  R_r x = (91 / 10) * x + (- 98)"
proof -
  assume x: "x \<in> {(320 / 37)<..<(200 / 23)}"
  have b: "(320 / 37) < x" "x < (200 / 23)" using x by auto
  have "real 8 \<le> x \<and> x < real 8 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 19 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 19 + 1 \<and> real 17 \<le> 2 * x \<and>
      2 * x < real 17 + 1 \<and>
    real 16 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 16 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 8) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 8) (alpha_r * x - real 0) (2 * Hc_r * x - real 19) (2 * x - real 17) (2 *
        (lam_r * x) - real 16)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_50: "x \<in> {(200 / 23)<..<(380 / 43)} \<Longrightarrow>
  R_r x = (159 / 20) * x + (- 88)"
proof -
  assume x: "x \<in> {(200 / 23)<..<(380 / 43)}"
  have b: "(200 / 23) < x" "x < (380 / 43)" using x by auto
  have "real 8 \<le> x \<and> x < real 8 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 20 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 20 + 1 \<and> real 17 \<le> 2 * x \<and>
      2 * x < real 17 + 1 \<and>
    real 16 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 16 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 8) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 8) (alpha_r * x - real 0) (2 * Hc_r * x - real 20) (2 * x - real 17) (2 *
        (lam_r * x) - real 16)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_51: "x \<in> {(380 / 43)<..<9} \<Longrightarrow> R_r x = (159 / 20) * x + (- 88)"
proof -
  assume x: "x \<in> {(380 / 43)<..<9}"
  have b: "(380 / 43) < x" "x < 9" using x by auto
  have "real 8 \<le> x \<and> x < real 8 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 20 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 20 + 1 \<and> real 17 \<le> 2 * x \<and>
      2 * x < real 17 + 1 \<and>
    real 16 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 16 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 8) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 8) (alpha_r * x - real 0) (2 * Hc_r * x - real 20) (2 * x - real 17) (2 *
        (lam_r * x) - real 16)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_52: "x \<in> {9<..<(210 / 23)} \<Longrightarrow> R_r x = (71 / 10) * x + (- 97)"
proof -
  assume x: "x \<in> {9<..<(210 / 23)}"
  have b: "9 < x" "x < (210 / 23)" using x by auto
  have "real 9 \<le> x \<and> x < real 9 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 20 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 20 + 1 \<and> real 18 \<le> 2 * x \<and>
      2 * x < real 18 + 1 \<and>
    real 16 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 16 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 9) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 9) (alpha_r * x - real 0) (2 * Hc_r * x - real 20) (2 * x - real 18) (2 *
        (lam_r * x) - real 16)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_53: "x \<in> {(210 / 23)<..<(340 / 37)} \<Longrightarrow>
  R_r x = (119 / 20) * x + (- 173 / 2)"
proof -
  assume x: "x \<in> {(210 / 23)<..<(340 / 37)}"
  have b: "(210 / 23) < x" "x < (340 / 37)" using x by auto
  have "real 9 \<le> x \<and> x < real 9 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 21 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 21 + 1 \<and> real 18 \<le> 2 * x \<and>
      2 * x < real 18 + 1 \<and>
    real 16 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 16 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 9) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 9) (alpha_r * x - real 0) (2 * Hc_r * x - real 21) (2 * x - real 18) (2 *
        (lam_r * x) - real 16)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_54: "x \<in> {(340 / 37)<..<(400 / 43)} \<Longrightarrow>
  R_r x = (39 / 5) * x + (- 207 / 2)"
proof -
  assume x: "x \<in> {(340 / 37)<..<(400 / 43)}"
  have b: "(340 / 37) < x" "x < (400 / 43)" using x by auto
  have "real 9 \<le> x \<and> x < real 9 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 21 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 21 + 1 \<and> real 18 \<le> 2 * x \<and>
      2 * x < real 18 + 1 \<and>
    real 17 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 17 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 9) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 9) (alpha_r * x - real 0) (2 * Hc_r * x - real 21) (2 * x - real 18) (2 *
        (lam_r * x) - real 17)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_55: "x \<in> {(400 / 43)<..<(19 / 2)} \<Longrightarrow>
  R_r x = (183 / 40) * x + (- 147 / 2)"
proof -
  assume x: "x \<in> {(400 / 43)<..<(19 / 2)}"
  have b: "(400 / 43) < x" "x < (19 / 2)" using x by auto
  have "real 9 \<le> x \<and> x < real 9 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 21 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 21 + 1 \<and> real 18 \<le> 2 * x \<and>
      2 * x < real 18 + 1 \<and>
    real 17 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 17 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 9) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 9) (alpha_r * x - real 0) (2 * Hc_r * x - real 21) (2 * x - real 18) (2 *
        (lam_r * x) - real 17)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_56: "x \<in> {(19 / 2)<..<(220 / 23)} \<Longrightarrow>
  R_r x = (223 / 40) * x + (- 83)"
proof -
  assume x: "x \<in> {(19 / 2)<..<(220 / 23)}"
  have b: "(19 / 2) < x" "x < (220 / 23)" using x by auto
  have "real 9 \<le> x \<and> x < real 9 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 21 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 21 + 1 \<and> real 19 \<le> 2 * x \<and>
      2 * x < real 19 + 1 \<and>
    real 17 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 17 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 9) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 9) (alpha_r * x - real 0) (2 * Hc_r * x - real 21) (2 * x - real 19) (2 *
        (lam_r * x) - real 17)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_57: "x \<in> {(220 / 23)<..<(360 / 37)} \<Longrightarrow>
  R_r x = (177 / 40) * x + (- 72)"
proof -
  assume x: "x \<in> {(220 / 23)<..<(360 / 37)}"
  have b: "(220 / 23) < x" "x < (360 / 37)" using x by auto
  have "real 9 \<le> x \<and> x < real 9 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 22 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 22 + 1 \<and> real 19 \<le> 2 * x \<and>
      2 * x < real 19 + 1 \<and>
    real 17 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 17 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 9) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 9) (alpha_r * x - real 0) (2 * Hc_r * x - real 22) (2 * x - real 19) (2 *
        (lam_r * x) - real 17)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_58: "x \<in> {(360 / 37)<..<(420 / 43)} \<Longrightarrow>
  R_r x = (181 / 20) * x + (- 117)"
proof -
  assume x: "x \<in> {(360 / 37)<..<(420 / 43)}"
  have b: "(360 / 37) < x" "x < (420 / 43)" using x by auto
  have "real 9 \<le> x \<and> x < real 9 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 22 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 22 + 1 \<and> real 19 \<le> 2 * x \<and>
      2 * x < real 19 + 1 \<and>
    real 18 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 18 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 9) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 9) (alpha_r * x - real 0) (2 * Hc_r * x - real 22) (2 * x - real 19) (2 *
        (lam_r * x) - real 18)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_59: "x \<in> {(420 / 43)<..<10} \<Longrightarrow>
  R_r x = (181 / 20) * x + (- 117)"
proof -
  assume x: "x \<in> {(420 / 43)<..<10}"
  have b: "(420 / 43) < x" "x < 10" using x by auto
  have "real 9 \<le> x \<and> x < real 9 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 22 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 22 + 1 \<and> real 19 \<le> 2 * x \<and>
      2 * x < real 19 + 1 \<and>
    real 18 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 18 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 9) - 12 * lam_r * (alpha_r * x - real 0))
      + Qc (x - real 9) (alpha_r * x - real 0) (2 * Hc_r * x - real 22) (2 * x - real 19) (2 *
        (lam_r * x) - real 18)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_60: "x \<in> {10<..<(440 / 43)} \<Longrightarrow> R_r x = (69 / 10) * x + (- 114)"
proof -
  assume x: "x \<in> {10<..<(440 / 43)}"
  have b: "10 < x" "x < (440 / 43)" using x by auto
  have "real 10 \<le> x \<and> x < real 10 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 23 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 23 + 1 \<and> real 20 \<le> 2 * x \<and>
      2 * x < real 20 + 1 \<and>
    real 18 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 18 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 10) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 10) (alpha_r * x - real 0) (2 * Hc_r * x - real 23) (2 * x - real 20) (2 *
        (lam_r * x) - real 18)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_61: "x \<in> {(440 / 43)<..<(380 / 37)} \<Longrightarrow>
  R_r x = (147 / 40) * x + (- 81)"
proof -
  assume x: "x \<in> {(440 / 43)<..<(380 / 37)}"
  have b: "(440 / 43) < x" "x < (380 / 37)" using x by auto
  have "real 10 \<le> x \<and> x < real 10 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 23 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 23 + 1 \<and> real 20 \<le> 2 * x \<and>
      2 * x < real 20 + 1 \<and>
    real 18 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 18 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 10) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 10) (alpha_r * x - real 0) (2 * Hc_r * x - real 23) (2 * x - real 20) (2 *
        (lam_r * x) - real 18)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_62: "x \<in> {(380 / 37)<..<(240 / 23)} \<Longrightarrow>
  R_r x = (221 / 40) * x + (- 100)"
proof -
  assume x: "x \<in> {(380 / 37)<..<(240 / 23)}"
  have b: "(380 / 37) < x" "x < (240 / 23)" using x by auto
  have "real 10 \<le> x \<and> x < real 10 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 23 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 23 + 1 \<and> real 20 \<le> 2 * x \<and>
      2 * x < real 20 + 1 \<and>
    real 19 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 19 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 10) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 10) (alpha_r * x - real 0) (2 * Hc_r * x - real 23) (2 * x - real 20) (2 *
        (lam_r * x) - real 19)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_63: "x \<in> {(240 / 23)<..<(21 / 2)} \<Longrightarrow>
  R_r x = (35 / 8) * x + (- 88)"
proof -
  assume x: "x \<in> {(240 / 23)<..<(21 / 2)}"
  have b: "(240 / 23) < x" "x < (21 / 2)" using x by auto
  have "real 10 \<le> x \<and> x < real 10 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 24 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 24 + 1 \<and> real 20 \<le> 2 * x \<and>
      2 * x < real 20 + 1 \<and>
    real 19 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 19 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 10) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 10) (alpha_r * x - real 0) (2 * Hc_r * x - real 24) (2 * x - real 20) (2 *
        (lam_r * x) - real 19)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_64: "x \<in> {(21 / 2)<..<(460 / 43)} \<Longrightarrow>
  R_r x = (43 / 8) * x + (- 197 / 2)"
proof -
  assume x: "x \<in> {(21 / 2)<..<(460 / 43)}"
  have b: "(21 / 2) < x" "x < (460 / 43)" using x by auto
  have "real 10 \<le> x \<and> x < real 10 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 24 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 24 + 1 \<and> real 21 \<le> 2 * x \<and>
      2 * x < real 21 + 1 \<and>
    real 19 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 19 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 10) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 10) (alpha_r * x - real 0) (2 * Hc_r * x - real 24) (2 * x - real 21) (2 *
        (lam_r * x) - real 19)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_65: "x \<in> {(460 / 43)<..<(400 / 37)} \<Longrightarrow>
  R_r x = (43 / 8) * x + (- 197 / 2)"
proof -
  assume x: "x \<in> {(460 / 43)<..<(400 / 37)}"
  have b: "(460 / 43) < x" "x < (400 / 37)" using x by auto
  have "real 10 \<le> x \<and> x < real 10 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 24 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 24 + 1 \<and> real 21 \<le> 2 * x \<and>
      2 * x < real 21 + 1 \<and>
    real 19 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 19 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 10) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 10) (alpha_r * x - real 0) (2 * Hc_r * x - real 24) (2 * x - real 21) (2 *
        (lam_r * x) - real 19)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_66: "x \<in> {(400 / 37)<..<(250 / 23)} \<Longrightarrow>
  R_r x = 10 * x + (- 297 / 2)"
proof -
  assume x: "x \<in> {(400 / 37)<..<(250 / 23)}"
  have b: "(400 / 37) < x" "x < (250 / 23)" using x by auto
  have "real 10 \<le> x \<and> x < real 10 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 24 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 24 + 1 \<and> real 21 \<le> 2 * x \<and>
      2 * x < real 21 + 1 \<and>
    real 20 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 20 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 10) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 10) (alpha_r * x - real 0) (2 * Hc_r * x - real 24) (2 * x - real 21) (2 *
        (lam_r * x) - real 20)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_67: "x \<in> {(250 / 23)<..<11} \<Longrightarrow>
  R_r x = (177 / 20) * x + (- 136)"
proof -
  assume x: "x \<in> {(250 / 23)<..<11}"
  have b: "(250 / 23) < x" "x < 11" using x by auto
  have "real 10 \<le> x \<and> x < real 10 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 25 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 25 + 1 \<and> real 21 \<le> 2 * x \<and>
      2 * x < real 21 + 1 \<and>
    real 20 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 20 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 10) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 10) (alpha_r * x - real 0) (2 * Hc_r * x - real 25) (2 * x - real 21) (2 *
        (lam_r * x) - real 20)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_68: "x \<in> {11<..<(480 / 43)} \<Longrightarrow> R_r x = 8 * x + (- 147)"
proof -
  assume x: "x \<in> {11<..<(480 / 43)}"
  have b: "11 < x" "x < (480 / 43)" using x by auto
  have "real 11 \<le> x \<and> x < real 11 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 25 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 25 + 1 \<and> real 22 \<le> 2 * x \<and>
      2 * x < real 22 + 1 \<and>
    real 20 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 20 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 11) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 11) (alpha_r * x - real 0) (2 * Hc_r * x - real 25) (2 * x - real 22) (2 *
        (lam_r * x) - real 20)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_69: "x \<in> {(480 / 43)<..<(260 / 23)} \<Longrightarrow>
  R_r x = (191 / 40) * x + (- 111)"
proof -
  assume x: "x \<in> {(480 / 43)<..<(260 / 23)}"
  have b: "(480 / 43) < x" "x < (260 / 23)" using x by auto
  have "real 11 \<le> x \<and> x < real 11 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 25 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 25 + 1 \<and> real 22 \<le> 2 * x \<and>
      2 * x < real 22 + 1 \<and>
    real 20 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 20 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 11) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 11) (alpha_r * x - real 0) (2 * Hc_r * x - real 25) (2 * x - real 22) (2 *
        (lam_r * x) - real 20)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_70: "x \<in> {(260 / 23)<..<(420 / 37)} \<Longrightarrow>
  R_r x = (29 / 8) * x + (- 98)"
proof -
  assume x: "x \<in> {(260 / 23)<..<(420 / 37)}"
  have b: "(260 / 23) < x" "x < (420 / 37)" using x by auto
  have "real 11 \<le> x \<and> x < real 11 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 26 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 26 + 1 \<and> real 22 \<le> 2 * x \<and>
      2 * x < real 22 + 1 \<and>
    real 20 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 20 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 11) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 11) (alpha_r * x - real 0) (2 * Hc_r * x - real 26) (2 * x - real 22) (2 *
        (lam_r * x) - real 20)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_71: "x \<in> {(420 / 37)<..<(23 / 2)} \<Longrightarrow>
  R_r x = (219 / 40) * x + (- 119)"
proof -
  assume x: "x \<in> {(420 / 37)<..<(23 / 2)}"
  have b: "(420 / 37) < x" "x < (23 / 2)" using x by auto
  have "real 11 \<le> x \<and> x < real 11 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 26 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 26 + 1 \<and> real 22 \<le> 2 * x \<and>
      2 * x < real 22 + 1 \<and>
    real 21 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 21 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 11) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 11) (alpha_r * x - real 0) (2 * Hc_r * x - real 26) (2 * x - real 22) (2 *
        (lam_r * x) - real 21)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_72: "x \<in> {(23 / 2)<..<(500 / 43)} \<Longrightarrow>
  R_r x = (259 / 40) * x + (- 261 / 2)"
proof -
  assume x: "x \<in> {(23 / 2)<..<(500 / 43)}"
  have b: "(23 / 2) < x" "x < (500 / 43)" using x by auto
  have "real 11 \<le> x \<and> x < real 11 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 26 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 26 + 1 \<and> real 23 \<le> 2 * x \<and>
      2 * x < real 23 + 1 \<and>
    real 21 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 21 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 11) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 11) (alpha_r * x - real 0) (2 * Hc_r * x - real 26) (2 * x - real 23) (2 *
        (lam_r * x) - real 21)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_73: "x \<in> {(500 / 43)<..<(270 / 23)} \<Longrightarrow>
  R_r x = (259 / 40) * x + (- 261 / 2)"
proof -
  assume x: "x \<in> {(500 / 43)<..<(270 / 23)}"
  have b: "(500 / 43) < x" "x < (270 / 23)" using x by auto
  have "real 11 \<le> x \<and> x < real 11 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 26 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 26 + 1 \<and> real 23 \<le> 2 * x \<and>
      2 * x < real 23 + 1 \<and>
    real 21 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 21 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 11) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 11) (alpha_r * x - real 0) (2 * Hc_r * x - real 26) (2 * x - real 23) (2 *
        (lam_r * x) - real 21)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_74: "x \<in> {(270 / 23)<..<(440 / 37)} \<Longrightarrow>
  R_r x = (213 / 40) * x + (- 117)"
proof -
  assume x: "x \<in> {(270 / 23)<..<(440 / 37)}"
  have b: "(270 / 23) < x" "x < (440 / 37)" using x by auto
  have "real 11 \<le> x \<and> x < real 11 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 27 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 27 + 1 \<and> real 23 \<le> 2 * x \<and>
      2 * x < real 23 + 1 \<and>
    real 21 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 21 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 11) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 11) (alpha_r * x - real 0) (2 * Hc_r * x - real 27) (2 * x - real 23) (2 *
        (lam_r * x) - real 21)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_75: "x \<in> {(440 / 37)<..<12} \<Longrightarrow>
  R_r x = (199 / 20) * x + (- 172)"
proof -
  assume x: "x \<in> {(440 / 37)<..<12}"
  have b: "(440 / 37) < x" "x < 12" using x by auto
  have "real 11 \<le> x \<and> x < real 11 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 27 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 27 + 1 \<and> real 23 \<le> 2 * x \<and>
      2 * x < real 23 + 1 \<and>
    real 22 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 22 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 11) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 11) (alpha_r * x - real 0) (2 * Hc_r * x - real 27) (2 * x - real 23) (2 *
        (lam_r * x) - real 22)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_76: "x \<in> {12<..<(520 / 43)} \<Longrightarrow> R_r x = (91 / 10) * x + (- 184)"
proof -
  assume x: "x \<in> {12<..<(520 / 43)}"
  have b: "12 < x" "x < (520 / 43)" using x by auto
  have "real 12 \<le> x \<and> x < real 12 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 27 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 27 + 1 \<and> real 24 \<le> 2 * x \<and>
      2 * x < real 24 + 1 \<and>
    real 22 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 22 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 12) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 12) (alpha_r * x - real 0) (2 * Hc_r * x - real 27) (2 * x - real 24) (2 *
        (lam_r * x) - real 22)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_77: "x \<in> {(520 / 43)<..<(280 / 23)} \<Longrightarrow>
  R_r x = (47 / 8) * x + (- 145)"
proof -
  assume x: "x \<in> {(520 / 43)<..<(280 / 23)}"
  have b: "(520 / 43) < x" "x < (280 / 23)" using x by auto
  have "real 12 \<le> x \<and> x < real 12 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 27 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 27 + 1 \<and> real 24 \<le> 2 * x \<and>
      2 * x < real 24 + 1 \<and>
    real 22 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 22 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 12) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 12) (alpha_r * x - real 0) (2 * Hc_r * x - real 27) (2 * x - real 24) (2 *
        (lam_r * x) - real 22)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_78: "x \<in> {(280 / 23)<..<(460 / 37)} \<Longrightarrow>
  R_r x = (189 / 40) * x + (- 131)"
proof -
  assume x: "x \<in> {(280 / 23)<..<(460 / 37)}"
  have b: "(280 / 23) < x" "x < (460 / 37)" using x by auto
  have "real 12 \<le> x \<and> x < real 12 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 28 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 28 + 1 \<and> real 24 \<le> 2 * x \<and>
      2 * x < real 24 + 1 \<and>
    real 22 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 22 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 12) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 12) (alpha_r * x - real 0) (2 * Hc_r * x - real 28) (2 * x - real 24) (2 *
        (lam_r * x) - real 22)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_79: "x \<in> {(460 / 37)<..<(25 / 2)} \<Longrightarrow>
  R_r x = (263 / 40) * x + (- 154)"
proof -
  assume x: "x \<in> {(460 / 37)<..<(25 / 2)}"
  have b: "(460 / 37) < x" "x < (25 / 2)" using x by auto
  have "real 12 \<le> x \<and> x < real 12 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 28 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 28 + 1 \<and> real 24 \<le> 2 * x \<and>
      2 * x < real 24 + 1 \<and>
    real 23 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 23 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 12) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 12) (alpha_r * x - real 0) (2 * Hc_r * x - real 28) (2 * x - real 24) (2 *
        (lam_r * x) - real 23)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_80: "x \<in> {(25 / 2)<..<(540 / 43)} \<Longrightarrow>
  R_r x = (303 / 40) * x + (- 333 / 2)"
proof -
  assume x: "x \<in> {(25 / 2)<..<(540 / 43)}"
  have b: "(25 / 2) < x" "x < (540 / 43)" using x by auto
  have "real 12 \<le> x \<and> x < real 12 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 28 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 28 + 1 \<and> real 25 \<le> 2 * x \<and>
      2 * x < real 25 + 1 \<and>
    real 23 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 23 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 12) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 12) (alpha_r * x - real 0) (2 * Hc_r * x - real 28) (2 * x - real 25) (2 *
        (lam_r * x) - real 23)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_81: "x \<in> {(540 / 43)<..<(290 / 23)} \<Longrightarrow>
  R_r x = (303 / 40) * x + (- 333 / 2)"
proof -
  assume x: "x \<in> {(540 / 43)<..<(290 / 23)}"
  have b: "(540 / 43) < x" "x < (290 / 23)" using x by auto
  have "real 12 \<le> x \<and> x < real 12 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 28 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 28 + 1 \<and> real 25 \<le> 2 * x \<and>
      2 * x < real 25 + 1 \<and>
    real 23 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 23 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 12) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 12) (alpha_r * x - real 0) (2 * Hc_r * x - real 28) (2 * x - real 25) (2 *
        (lam_r * x) - real 23)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_82: "x \<in> {(290 / 23)<..<(480 / 37)} \<Longrightarrow>
  R_r x = (257 / 40) * x + (- 152)"
proof -
  assume x: "x \<in> {(290 / 23)<..<(480 / 37)}"
  have b: "(290 / 23) < x" "x < (480 / 37)" using x by auto
  have "real 12 \<le> x \<and> x < real 12 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 29 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 29 + 1 \<and> real 25 \<le> 2 * x \<and>
      2 * x < real 25 + 1 \<and>
    real 23 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 23 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 12) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 12) (alpha_r * x - real 0) (2 * Hc_r * x - real 29) (2 * x - real 25) (2 *
        (lam_r * x) - real 23)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_83: "x \<in> {(480 / 37)<..<13} \<Longrightarrow>
  R_r x = (221 / 20) * x + (- 212)"
proof -
  assume x: "x \<in> {(480 / 37)<..<13}"
  have b: "(480 / 37) < x" "x < 13" using x by auto
  have "real 12 \<le> x \<and> x < real 12 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 29 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 29 + 1 \<and> real 25 \<le> 2 * x \<and>
      2 * x < real 25 + 1 \<and>
    real 24 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 24 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 12) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 12) (alpha_r * x - real 0) (2 * Hc_r * x - real 29) (2 * x - real 25) (2 *
        (lam_r * x) - real 24)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_84: "x \<in> {13<..<(560 / 43)} \<Longrightarrow> R_r x = (51 / 5) * x + (- 225)"
proof -
  assume x: "x \<in> {13<..<(560 / 43)}"
  have b: "13 < x" "x < (560 / 43)" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 29 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 29 + 1 \<and> real 26 \<le> 2 * x \<and>
      2 * x < real 26 + 1 \<and>
    real 24 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 24 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 13) (alpha_r * x - real 0) (2 * Hc_r * x - real 29) (2 * x - real 26) (2 *
        (lam_r * x) - real 24)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_85: "x \<in> {(560 / 43)<..<(300 / 23)} \<Longrightarrow>
  R_r x = (279 / 40) * x + (- 183)"
proof -
  assume x: "x \<in> {(560 / 43)<..<(300 / 23)}"
  have b: "(560 / 43) < x" "x < (300 / 23)" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 29 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 29 + 1 \<and> real 26 \<le> 2 * x \<and>
      2 * x < real 26 + 1 \<and>
    real 24 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 24 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 13) (alpha_r * x - real 0) (2 * Hc_r * x - real 29) (2 * x - real 26) (2 *
        (lam_r * x) - real 24)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_86: "x \<in> {(300 / 23)<..<(40 / 3)} \<Longrightarrow>
  R_r x = (233 / 40) * x + (- 168)"
proof -
  assume x: "x \<in> {(300 / 23)<..<(40 / 3)}"
  have b: "(300 / 23) < x" "x < (40 / 3)" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 0 \<le> alpha_r * x \<and>
    alpha_r * x < real 0 + 1 \<and>
    real 30 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 30 + 1 \<and> real 26 \<le> 2 * x \<and>
      2 * x < real 26 + 1 \<and>
    real 24 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 24 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 0))
      + Qc (x - real 13) (alpha_r * x - real 0) (2 * Hc_r * x - real 30) (2 * x - real 26) (2 *
        (lam_r * x) - real 24)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_87: "x \<in> {(40 / 3)<..<(310 / 23)} \<Longrightarrow>
  R_r x = (145 / 8) * x + (- 184)"
proof -
  assume x: "x \<in> {(40 / 3)<..<(310 / 23)}"
  have b: "(40 / 3) < x" "x < (310 / 23)" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 30 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 30 + 1 \<and> real 26 \<le> 2 * x \<and>
      2 * x < real 26 + 1 \<and>
    real 24 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 24 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 13) (alpha_r * x - real 1) (2 * Hc_r * x - real 30) (2 * x - real 26) (2 *
        (lam_r * x) - real 24)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_88: "x \<in> {(310 / 23)<..<(580 / 43)} \<Longrightarrow>
  R_r x = (679 / 40) * x + (- 337 / 2)"
proof -
  assume x: "x \<in> {(310 / 23)<..<(580 / 43)}"
  have b: "(310 / 23) < x" "x < (580 / 43)" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 31 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 31 + 1 \<and> real 26 \<le> 2 * x \<and>
      2 * x < real 26 + 1 \<and>
    real 24 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 24 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 13) (alpha_r * x - real 1) (2 * Hc_r * x - real 31) (2 * x - real 26) (2 *
        (lam_r * x) - real 24)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_89: "x \<in> {(580 / 43)<..<(27 / 2)} \<Longrightarrow>
  R_r x = (679 / 40) * x + (- 337 / 2)"
proof -
  assume x: "x \<in> {(580 / 43)<..<(27 / 2)}"
  have b: "(580 / 43) < x" "x < (27 / 2)" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 31 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 31 + 1 \<and> real 26 \<le> 2 * x \<and>
      2 * x < real 26 + 1 \<and>
    real 24 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 24 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 13) (alpha_r * x - real 1) (2 * Hc_r * x - real 31) (2 * x - real 26) (2 *
        (lam_r * x) - real 24)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_90: "x \<in> {(27 / 2)<..<(500 / 37)} \<Longrightarrow>
  R_r x = (719 / 40) * x + (- 182)"
proof -
  assume x: "x \<in> {(27 / 2)<..<(500 / 37)}"
  have b: "(27 / 2) < x" "x < (500 / 37)" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 31 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 31 + 1 \<and> real 27 \<le> 2 * x \<and>
      2 * x < real 27 + 1 \<and>
    real 24 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 24 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 13) (alpha_r * x - real 1) (2 * Hc_r * x - real 31) (2 * x - real 27) (2 *
        (lam_r * x) - real 24)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_91: "x \<in> {(500 / 37)<..<(320 / 23)} \<Longrightarrow>
  R_r x = (793 / 40) * x + (- 207)"
proof -
  assume x: "x \<in> {(500 / 37)<..<(320 / 23)}"
  have b: "(500 / 37) < x" "x < (320 / 23)" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 31 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 31 + 1 \<and> real 27 \<le> 2 * x \<and>
      2 * x < real 27 + 1 \<and>
    real 25 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 25 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 13) (alpha_r * x - real 1) (2 * Hc_r * x - real 31) (2 * x - real 27) (2 *
        (lam_r * x) - real 25)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_92: "x \<in> {(320 / 23)<..<(600 / 43)} \<Longrightarrow>
  R_r x = (747 / 40) * x + (- 191)"
proof -
  assume x: "x \<in> {(320 / 23)<..<(600 / 43)}"
  have b: "(320 / 23) < x" "x < (600 / 43)" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 32 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 32 + 1 \<and> real 27 \<le> 2 * x \<and>
      2 * x < real 27 + 1 \<and>
    real 25 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 25 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 13) (alpha_r * x - real 1) (2 * Hc_r * x - real 32) (2 * x - real 27) (2 *
        (lam_r * x) - real 25)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_93: "x \<in> {(600 / 43)<..<14} \<Longrightarrow>
  R_r x = (309 / 20) * x + (- 146)"
proof -
  assume x: "x \<in> {(600 / 43)<..<14}"
  have b: "(600 / 43) < x" "x < 14" using x by auto
  have "real 13 \<le> x \<and> x < real 13 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 32 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 32 + 1 \<and> real 27 \<le> 2 * x \<and>
      2 * x < real 27 + 1 \<and>
    real 25 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 25 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 13) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 13) (alpha_r * x - real 1) (2 * Hc_r * x - real 32) (2 * x - real 27) (2 *
        (lam_r * x) - real 25)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_94: "x \<in> {14<..<(520 / 37)} \<Longrightarrow> R_r x = (73 / 5) * x + (- 160)"
proof -
  assume x: "x \<in> {14<..<(520 / 37)}"
  have b: "14 < x" "x < (520 / 37)" using x by auto
  have "real 14 \<le> x \<and> x < real 14 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 32 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 32 + 1 \<and> real 28 \<le> 2 * x \<and>
      2 * x < real 28 + 1 \<and>
    real 25 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 25 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 14) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 14) (alpha_r * x - real 1) (2 * Hc_r * x - real 32) (2 * x - real 28) (2 *
        (lam_r * x) - real 25)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_95: "x \<in> {(520 / 37)<..<(330 / 23)} \<Longrightarrow>
  R_r x = (769 / 40) * x + (- 225)"
proof -
  assume x: "x \<in> {(520 / 37)<..<(330 / 23)}"
  have b: "(520 / 37) < x" "x < (330 / 23)" using x by auto
  have "real 14 \<le> x \<and> x < real 14 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 32 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 32 + 1 \<and> real 28 \<le> 2 * x \<and>
      2 * x < real 28 + 1 \<and>
    real 26 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 26 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 14) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 14) (alpha_r * x - real 1) (2 * Hc_r * x - real 32) (2 * x - real 28) (2 *
        (lam_r * x) - real 26)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_96: "x \<in> {(330 / 23)<..<(620 / 43)} \<Longrightarrow>
  R_r x = (723 / 40) * x + (- 417 / 2)"
proof -
  assume x: "x \<in> {(330 / 23)<..<(620 / 43)}"
  have b: "(330 / 23) < x" "x < (620 / 43)" using x by auto
  have "real 14 \<le> x \<and> x < real 14 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 33 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 33 + 1 \<and> real 28 \<le> 2 * x \<and>
      2 * x < real 28 + 1 \<and>
    real 26 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 26 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 14) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 14) (alpha_r * x - real 1) (2 * Hc_r * x - real 33) (2 * x - real 28) (2 *
        (lam_r * x) - real 26)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_97: "x \<in> {(620 / 43)<..<(29 / 2)} \<Longrightarrow>
  R_r x = (723 / 40) * x + (- 417 / 2)"
proof -
  assume x: "x \<in> {(620 / 43)<..<(29 / 2)}"
  have b: "(620 / 43) < x" "x < (29 / 2)" using x by auto
  have "real 14 \<le> x \<and> x < real 14 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 33 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 33 + 1 \<and> real 28 \<le> 2 * x \<and>
      2 * x < real 28 + 1 \<and>
    real 26 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 26 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 14) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 14) (alpha_r * x - real 1) (2 * Hc_r * x - real 33) (2 * x - real 28) (2 *
        (lam_r * x) - real 26)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_98: "x \<in> {(29 / 2)<..<(540 / 37)} \<Longrightarrow>
  R_r x = (763 / 40) * x + (- 223)"
proof -
  assume x: "x \<in> {(29 / 2)<..<(540 / 37)}"
  have b: "(29 / 2) < x" "x < (540 / 37)" using x by auto
  have "real 14 \<le> x \<and> x < real 14 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 33 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 33 + 1 \<and> real 29 \<le> 2 * x \<and>
      2 * x < real 29 + 1 \<and>
    real 26 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 26 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 14) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 14) (alpha_r * x - real 1) (2 * Hc_r * x - real 33) (2 * x - real 29) (2 *
        (lam_r * x) - real 26)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_99: "x \<in> {(540 / 37)<..<(340 / 23)} \<Longrightarrow>
  R_r x = (837 / 40) * x + (- 250)"
proof -
  assume x: "x \<in> {(540 / 37)<..<(340 / 23)}"
  have b: "(540 / 37) < x" "x < (340 / 23)" using x by auto
  have "real 14 \<le> x \<and> x < real 14 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 33 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 33 + 1 \<and> real 29 \<le> 2 * x \<and>
      2 * x < real 29 + 1 \<and>
    real 27 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 27 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 14) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 14) (alpha_r * x - real 1) (2 * Hc_r * x - real 33) (2 * x - real 29) (2 *
        (lam_r * x) - real 27)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_100: "x \<in> {(340 / 23)<..<(640 / 43)} \<Longrightarrow>
  R_r x = (791 / 40) * x + (- 233)"
proof -
  assume x: "x \<in> {(340 / 23)<..<(640 / 43)}"
  have b: "(340 / 23) < x" "x < (640 / 43)" using x by auto
  have "real 14 \<le> x \<and> x < real 14 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 34 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 34 + 1 \<and> real 29 \<le> 2 * x \<and>
      2 * x < real 29 + 1 \<and>
    real 27 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 27 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 14) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 14) (alpha_r * x - real 1) (2 * Hc_r * x - real 34) (2 * x - real 29) (2 *
        (lam_r * x) - real 27)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_101: "x \<in> {(640 / 43)<..<15} \<Longrightarrow>
  R_r x = (331 / 20) * x + (- 185)"
proof -
  assume x: "x \<in> {(640 / 43)<..<15}"
  have b: "(640 / 43) < x" "x < 15" using x by auto
  have "real 14 \<le> x \<and> x < real 14 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 34 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 34 + 1 \<and> real 29 \<le> 2 * x \<and>
      2 * x < real 29 + 1 \<and>
    real 27 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 27 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 14) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 14) (alpha_r * x - real 1) (2 * Hc_r * x - real 34) (2 * x - real 29) (2 *
        (lam_r * x) - real 27)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_102: "x \<in> {15<..<(560 / 37)} \<Longrightarrow>
  R_r x = (157 / 10) * x + (- 200)"
proof -
  assume x: "x \<in> {15<..<(560 / 37)}"
  have b: "15 < x" "x < (560 / 37)" using x by auto
  have "real 15 \<le> x \<and> x < real 15 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 34 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 34 + 1 \<and> real 30 \<le> 2 * x \<and>
      2 * x < real 30 + 1 \<and>
    real 27 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 27 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 15) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 15) (alpha_r * x - real 1) (2 * Hc_r * x - real 34) (2 * x - real 30) (2 *
        (lam_r * x) - real 27)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_103: "x \<in> {(560 / 37)<..<(350 / 23)} \<Longrightarrow>
  R_r x = (813 / 40) * x + (- 270)"
proof -
  assume x: "x \<in> {(560 / 37)<..<(350 / 23)}"
  have b: "(560 / 37) < x" "x < (350 / 23)" using x by auto
  have "real 15 \<le> x \<and> x < real 15 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 34 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 34 + 1 \<and> real 30 \<le> 2 * x \<and>
      2 * x < real 30 + 1 \<and>
    real 28 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 28 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 15) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 15) (alpha_r * x - real 1) (2 * Hc_r * x - real 34) (2 * x - real 30) (2 *
        (lam_r * x) - real 28)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_104: "x \<in> {(350 / 23)<..<(660 / 43)} \<Longrightarrow>
  R_r x = (767 / 40) * x + (- 505 / 2)"
proof -
  assume x: "x \<in> {(350 / 23)<..<(660 / 43)}"
  have b: "(350 / 23) < x" "x < (660 / 43)" using x by auto
  have "real 15 \<le> x \<and> x < real 15 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 35 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 35 + 1 \<and> real 30 \<le> 2 * x \<and>
      2 * x < real 30 + 1 \<and>
    real 28 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 28 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 15) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 15) (alpha_r * x - real 1) (2 * Hc_r * x - real 35) (2 * x - real 30) (2 *
        (lam_r * x) - real 28)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_105: "x \<in> {(660 / 43)<..<(31 / 2)} \<Longrightarrow>
  R_r x = (767 / 40) * x + (- 505 / 2)"
proof -
  assume x: "x \<in> {(660 / 43)<..<(31 / 2)}"
  have b: "(660 / 43) < x" "x < (31 / 2)" using x by auto
  have "real 15 \<le> x \<and> x < real 15 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 35 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 35 + 1 \<and> real 30 \<le> 2 * x \<and>
      2 * x < real 30 + 1 \<and>
    real 28 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 28 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 15) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 15) (alpha_r * x - real 1) (2 * Hc_r * x - real 35) (2 * x - real 30) (2 *
        (lam_r * x) - real 28)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_106: "x \<in> {(31 / 2)<..<(360 / 23)} \<Longrightarrow>
  R_r x = (807 / 40) * x + (- 268)"
proof -
  assume x: "x \<in> {(31 / 2)<..<(360 / 23)}"
  have b: "(31 / 2) < x" "x < (360 / 23)" using x by auto
  have "real 15 \<le> x \<and> x < real 15 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 35 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 35 + 1 \<and> real 31 \<le> 2 * x \<and>
      2 * x < real 31 + 1 \<and>
    real 28 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 28 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 15) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 15) (alpha_r * x - real 1) (2 * Hc_r * x - real 35) (2 * x - real 31) (2 *
        (lam_r * x) - real 28)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_107: "x \<in> {(360 / 23)<..<(580 / 37)} \<Longrightarrow>
  R_r x = (761 / 40) * x + (- 250)"
proof -
  assume x: "x \<in> {(360 / 23)<..<(580 / 37)}"
  have b: "(360 / 23) < x" "x < (580 / 37)" using x by auto
  have "real 15 \<le> x \<and> x < real 15 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 36 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 36 + 1 \<and> real 31 \<le> 2 * x \<and>
      2 * x < real 31 + 1 \<and>
    real 28 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 28 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 15) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 15) (alpha_r * x - real 1) (2 * Hc_r * x - real 36) (2 * x - real 31) (2 *
        (lam_r * x) - real 28)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_108: "x \<in> {(580 / 37)<..<(680 / 43)} \<Longrightarrow>
  R_r x = (167 / 8) * x + (- 279)"
proof -
  assume x: "x \<in> {(580 / 37)<..<(680 / 43)}"
  have b: "(580 / 37) < x" "x < (680 / 43)" using x by auto
  have "real 15 \<le> x \<and> x < real 15 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 36 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 36 + 1 \<and> real 31 \<le> 2 * x \<and>
      2 * x < real 31 + 1 \<and>
    real 29 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 29 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 15) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 15) (alpha_r * x - real 1) (2 * Hc_r * x - real 36) (2 * x - real 31) (2 *
        (lam_r * x) - real 29)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_109: "x \<in> {(680 / 43)<..<16} \<Longrightarrow>
  R_r x = (353 / 20) * x + (- 228)"
proof -
  assume x: "x \<in> {(680 / 43)<..<16}"
  have b: "(680 / 43) < x" "x < 16" using x by auto
  have "real 15 \<le> x \<and> x < real 15 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 36 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 36 + 1 \<and> real 31 \<le> 2 * x \<and>
      2 * x < real 31 + 1 \<and>
    real 29 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 29 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 15) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 15) (alpha_r * x - real 1) (2 * Hc_r * x - real 36) (2 * x - real 31) (2 *
        (lam_r * x) - real 29)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_110: "x \<in> {16<..<(370 / 23)} \<Longrightarrow> R_r x = (84 / 5) * x + (- 244)"
proof -
  assume x: "x \<in> {16<..<(370 / 23)}"
  have b: "16 < x" "x < (370 / 23)" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 36 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 36 + 1 \<and> real 32 \<le> 2 * x \<and>
      2 * x < real 32 + 1 \<and>
    real 29 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 29 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 36) (2 * x - real 32) (2 *
        (lam_r * x) - real 29)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_111: "x \<in> {(370 / 23)<..<(600 / 37)} \<Longrightarrow>
  R_r x = (313 / 20) * x + (- 451 / 2)"
proof -
  assume x: "x \<in> {(370 / 23)<..<(600 / 37)}"
  have b: "(370 / 23) < x" "x < (600 / 37)" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 37 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 37 + 1 \<and> real 32 \<le> 2 * x \<and>
      2 * x < real 32 + 1 \<and>
    real 29 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 29 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 37) (2 * x - real 32) (2 *
        (lam_r * x) - real 29)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_112: "x \<in> {(600 / 37)<..<(700 / 43)} \<Longrightarrow>
  R_r x = (811 / 40) * x + (- 601 / 2)"
proof -
  assume x: "x \<in> {(600 / 37)<..<(700 / 43)}"
  have b: "(600 / 37) < x" "x < (700 / 43)" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 37 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 37 + 1 \<and> real 32 \<le> 2 * x \<and>
      2 * x < real 32 + 1 \<and>
    real 30 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 30 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 37) (2 * x - real 32) (2 *
        (lam_r * x) - real 30)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_113: "x \<in> {(700 / 43)<..<(33 / 2)} \<Longrightarrow>
  R_r x = (811 / 40) * x + (- 601 / 2)"
proof -
  assume x: "x \<in> {(700 / 43)<..<(33 / 2)}"
  have b: "(700 / 43) < x" "x < (33 / 2)" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 37 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 37 + 1 \<and> real 32 \<le> 2 * x \<and>
      2 * x < real 32 + 1 \<and>
    real 30 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 30 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 37) (2 * x - real 32) (2 *
        (lam_r * x) - real 30)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_114: "x \<in> {(33 / 2)<..<(380 / 23)} \<Longrightarrow>
  R_r x = (851 / 40) * x + (- 317)"
proof -
  assume x: "x \<in> {(33 / 2)<..<(380 / 23)}"
  have b: "(33 / 2) < x" "x < (380 / 23)" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 37 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 37 + 1 \<and> real 33 \<le> 2 * x \<and>
      2 * x < real 33 + 1 \<and>
    real 30 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 30 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 37) (2 * x - real 33) (2 *
        (lam_r * x) - real 30)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_115: "x \<in> {(380 / 23)<..<(50 / 3)} \<Longrightarrow>
  R_r x = (161 / 8) * x + (- 298)"
proof -
  assume x: "x \<in> {(380 / 23)<..<(50 / 3)}"
  have b: "(380 / 23) < x" "x < (50 / 3)" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 38 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 38 + 1 \<and> real 33 \<le> 2 * x \<and>
      2 * x < real 33 + 1 \<and>
    real 30 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 30 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 38) (2 * x - real 33) (2 *
        (lam_r * x) - real 30)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_116: "x \<in> {(50 / 3)<..<(720 / 43)} \<Longrightarrow>
  R_r x = (799 / 40) * x + (- 591 / 2)"
proof -
  assume x: "x \<in> {(50 / 3)<..<(720 / 43)}"
  have b: "(50 / 3) < x" "x < (720 / 43)" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 38 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 38 + 1 \<and> real 33 \<le> 2 * x \<and>
      2 * x < real 33 + 1 \<and>
    real 30 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 30 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 38) (2 * x - real 33) (2 *
        (lam_r * x) - real 30)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_117: "x \<in> {(720 / 43)<..<(620 / 37)} \<Longrightarrow>
  R_r x = (67 / 4) * x + (- 483 / 2)"
proof -
  assume x: "x \<in> {(720 / 43)<..<(620 / 37)}"
  have b: "(720 / 43) < x" "x < (620 / 37)" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 38 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 38 + 1 \<and> real 33 \<le> 2 * x \<and>
      2 * x < real 33 + 1 \<and>
    real 30 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 30 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 38) (2 * x - real 33) (2 *
        (lam_r * x) - real 30)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_118: "x \<in> {(620 / 37)<..<(390 / 23)} \<Longrightarrow>
  R_r x = (93 / 5) * x + (- 545 / 2)"
proof -
  assume x: "x \<in> {(620 / 37)<..<(390 / 23)}"
  have b: "(620 / 37) < x" "x < (390 / 23)" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 38 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 38 + 1 \<and> real 33 \<le> 2 * x \<and>
      2 * x < real 33 + 1 \<and>
    real 31 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 31 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 38) (2 * x - real 33) (2 *
        (lam_r * x) - real 31)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_119: "x \<in> {(390 / 23)<..<17} \<Longrightarrow>
  R_r x = (349 / 20) * x + (- 253)"
proof -
  assume x: "x \<in> {(390 / 23)<..<17}"
  have b: "(390 / 23) < x" "x < 17" using x by auto
  have "real 16 \<le> x \<and> x < real 16 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 39 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 39 + 1 \<and> real 33 \<le> 2 * x \<and>
      2 * x < real 33 + 1 \<and>
    real 31 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 31 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 16) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 16) (alpha_r * x - real 1) (2 * Hc_r * x - real 39) (2 * x - real 33) (2 *
        (lam_r * x) - real 31)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_120: "x \<in> {17<..<(740 / 43)} \<Longrightarrow> R_r x = (83 / 5) * x + (- 270)"
proof -
  assume x: "x \<in> {17<..<(740 / 43)}"
  have b: "17 < x" "x < (740 / 43)" using x by auto
  have "real 17 \<le> x \<and> x < real 17 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 39 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 39 + 1 \<and> real 34 \<le> 2 * x \<and>
      2 * x < real 34 + 1 \<and>
    real 31 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 31 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 17) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 17) (alpha_r * x - real 1) (2 * Hc_r * x - real 39) (2 * x - real 34) (2 *
        (lam_r * x) - real 31)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_121: "x \<in> {(740 / 43)<..<(640 / 37)} \<Longrightarrow>
  R_r x = (83 / 5) * x + (- 270)"
proof -
  assume x: "x \<in> {(740 / 43)<..<(640 / 37)}"
  have b: "(740 / 43) < x" "x < (640 / 37)" using x by auto
  have "real 17 \<le> x \<and> x < real 17 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 39 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 39 + 1 \<and> real 34 \<le> 2 * x \<and>
      2 * x < real 34 + 1 \<and>
    real 31 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 31 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 17) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 17) (alpha_r * x - real 1) (2 * Hc_r * x - real 39) (2 * x - real 34) (2 *
        (lam_r * x) - real 31)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_122: "x \<in> {(640 / 37)<..<(400 / 23)} \<Longrightarrow>
  R_r x = (849 / 40) * x + (- 350)"
proof -
  assume x: "x \<in> {(640 / 37)<..<(400 / 23)}"
  have b: "(640 / 37) < x" "x < (400 / 23)" using x by auto
  have "real 17 \<le> x \<and> x < real 17 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 39 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 39 + 1 \<and> real 34 \<le> 2 * x \<and>
      2 * x < real 34 + 1 \<and>
    real 32 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 32 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 17) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 17) (alpha_r * x - real 1) (2 * Hc_r * x - real 39) (2 * x - real 34) (2 *
        (lam_r * x) - real 32)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_123: "x \<in> {(400 / 23)<..<(35 / 2)} \<Longrightarrow>
  R_r x = (803 / 40) * x + (- 330)"
proof -
  assume x: "x \<in> {(400 / 23)<..<(35 / 2)}"
  have b: "(400 / 23) < x" "x < (35 / 2)" using x by auto
  have "real 17 \<le> x \<and> x < real 17 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 40 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 40 + 1 \<and> real 34 \<le> 2 * x \<and>
      2 * x < real 34 + 1 \<and>
    real 32 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 32 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 17) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 17) (alpha_r * x - real 1) (2 * Hc_r * x - real 40) (2 * x - real 34) (2 *
        (lam_r * x) - real 32)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_124: "x \<in> {(35 / 2)<..<(760 / 43)} \<Longrightarrow>
  R_r x = (843 / 40) * x + (- 695 / 2)"
proof -
  assume x: "x \<in> {(35 / 2)<..<(760 / 43)}"
  have b: "(35 / 2) < x" "x < (760 / 43)" using x by auto
  have "real 17 \<le> x \<and> x < real 17 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 40 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 40 + 1 \<and> real 35 \<le> 2 * x \<and>
      2 * x < real 35 + 1 \<and>
    real 32 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 32 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 17) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 17) (alpha_r * x - real 1) (2 * Hc_r * x - real 40) (2 * x - real 35) (2 *
        (lam_r * x) - real 32)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_125: "x \<in> {(760 / 43)<..<(410 / 23)} \<Longrightarrow>
  R_r x = (357 / 20) * x + (- 581 / 2)"
proof -
  assume x: "x \<in> {(760 / 43)<..<(410 / 23)}"
  have b: "(760 / 43) < x" "x < (410 / 23)" using x by auto
  have "real 17 \<le> x \<and> x < real 17 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 40 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 40 + 1 \<and> real 35 \<le> 2 * x \<and>
      2 * x < real 35 + 1 \<and>
    real 32 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 32 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 17) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 17) (alpha_r * x - real 1) (2 * Hc_r * x - real 40) (2 * x - real 35) (2 *
        (lam_r * x) - real 32)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_126: "x \<in> {(410 / 23)<..<(660 / 37)} \<Longrightarrow>
  R_r x = (167 / 10) * x + (- 270)"
proof -
  assume x: "x \<in> {(410 / 23)<..<(660 / 37)}"
  have b: "(410 / 23) < x" "x < (660 / 37)" using x by auto
  have "real 17 \<le> x \<and> x < real 17 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 41 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 41 + 1 \<and> real 35 \<le> 2 * x \<and>
      2 * x < real 35 + 1 \<and>
    real 32 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 32 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 17) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 17) (alpha_r * x - real 1) (2 * Hc_r * x - real 41) (2 * x - real 35) (2 *
        (lam_r * x) - real 32)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_127: "x \<in> {(660 / 37)<..<18} \<Longrightarrow>
  R_r x = (371 / 20) * x + (- 303)"
proof -
  assume x: "x \<in> {(660 / 37)<..<18}"
  have b: "(660 / 37) < x" "x < 18" using x by auto
  have "real 17 \<le> x \<and> x < real 17 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 41 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 41 + 1 \<and> real 35 \<le> 2 * x \<and>
      2 * x < real 35 + 1 \<and>
    real 33 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 33 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 17) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 17) (alpha_r * x - real 1) (2 * Hc_r * x - real 41) (2 * x - real 35) (2 *
        (lam_r * x) - real 33)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_128: "x \<in> {18<..<(780 / 43)} \<Longrightarrow>
  R_r x = (177 / 10) * x + (- 321)"
proof -
  assume x: "x \<in> {18<..<(780 / 43)}"
  have b: "18 < x" "x < (780 / 43)" using x by auto
  have "real 18 \<le> x \<and> x < real 18 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 41 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 41 + 1 \<and> real 36 \<le> 2 * x \<and>
      2 * x < real 36 + 1 \<and>
    real 33 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 33 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 18) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 18) (alpha_r * x - real 1) (2 * Hc_r * x - real 41) (2 * x - real 36) (2 *
        (lam_r * x) - real 33)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_129: "x \<in> {(780 / 43)<..<(420 / 23)} \<Longrightarrow>
  R_r x = (177 / 10) * x + (- 321)"
proof -
  assume x: "x \<in> {(780 / 43)<..<(420 / 23)}"
  have b: "(780 / 43) < x" "x < (420 / 23)" using x by auto
  have "real 18 \<le> x \<and> x < real 18 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 41 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 41 + 1 \<and> real 36 \<le> 2 * x \<and>
      2 * x < real 36 + 1 \<and>
    real 33 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 33 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 18) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 18) (alpha_r * x - real 1) (2 * Hc_r * x - real 41) (2 * x - real 36) (2 *
        (lam_r * x) - real 33)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_130: "x \<in> {(420 / 23)<..<(680 / 37)} \<Longrightarrow>
  R_r x = (331 / 20) * x + (- 300)"
proof -
  assume x: "x \<in> {(420 / 23)<..<(680 / 37)}"
  have b: "(420 / 23) < x" "x < (680 / 37)" using x by auto
  have "real 18 \<le> x \<and> x < real 18 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 42 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 42 + 1 \<and> real 36 \<le> 2 * x \<and>
      2 * x < real 36 + 1 \<and>
    real 33 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 33 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 18) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 18) (alpha_r * x - real 1) (2 * Hc_r * x - real 42) (2 * x - real 36) (2 *
        (lam_r * x) - real 33)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_131: "x \<in> {(680 / 37)<..<(37 / 2)} \<Longrightarrow>
  R_r x = (847 / 40) * x + (- 385)"
proof -
  assume x: "x \<in> {(680 / 37)<..<(37 / 2)}"
  have b: "(680 / 37) < x" "x < (37 / 2)" using x by auto
  have "real 18 \<le> x \<and> x < real 18 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 42 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 42 + 1 \<and> real 36 \<le> 2 * x \<and>
      2 * x < real 36 + 1 \<and>
    real 34 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 34 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 18) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 18) (alpha_r * x - real 1) (2 * Hc_r * x - real 42) (2 * x - real 36) (2 *
        (lam_r * x) - real 34)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_132: "x \<in> {(37 / 2)<..<(800 / 43)} \<Longrightarrow>
  R_r x = (887 / 40) * x + (- 807 / 2)"
proof -
  assume x: "x \<in> {(37 / 2)<..<(800 / 43)}"
  have b: "(37 / 2) < x" "x < (800 / 43)" using x by auto
  have "real 18 \<le> x \<and> x < real 18 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 42 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 42 + 1 \<and> real 37 \<le> 2 * x \<and>
      2 * x < real 37 + 1 \<and>
    real 34 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 34 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 18) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 18) (alpha_r * x - real 1) (2 * Hc_r * x - real 42) (2 * x - real 37) (2 *
        (lam_r * x) - real 34)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_133: "x \<in> {(800 / 43)<..<(430 / 23)} \<Longrightarrow>
  R_r x = (379 / 20) * x + (- 687 / 2)"
proof -
  assume x: "x \<in> {(800 / 43)<..<(430 / 23)}"
  have b: "(800 / 43) < x" "x < (430 / 23)" using x by auto
  have "real 18 \<le> x \<and> x < real 18 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 42 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 42 + 1 \<and> real 37 \<le> 2 * x \<and>
      2 * x < real 37 + 1 \<and>
    real 34 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 34 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 18) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 18) (alpha_r * x - real 1) (2 * Hc_r * x - real 42) (2 * x - real 37) (2 *
        (lam_r * x) - real 34)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_134: "x \<in> {(430 / 23)<..<(700 / 37)} \<Longrightarrow>
  R_r x = (89 / 5) * x + (- 322)"
proof -
  assume x: "x \<in> {(430 / 23)<..<(700 / 37)}"
  have b: "(430 / 23) < x" "x < (700 / 37)" using x by auto
  have "real 18 \<le> x \<and> x < real 18 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 43 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 43 + 1 \<and> real 37 \<le> 2 * x \<and>
      2 * x < real 37 + 1 \<and>
    real 34 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 34 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 18) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 18) (alpha_r * x - real 1) (2 * Hc_r * x - real 43) (2 * x - real 37) (2 *
        (lam_r * x) - real 34)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_135: "x \<in> {(700 / 37)<..<19} \<Longrightarrow>
  R_r x = (393 / 20) * x + (- 357)"
proof -
  assume x: "x \<in> {(700 / 37)<..<19}"
  have b: "(700 / 37) < x" "x < 19" using x by auto
  have "real 18 \<le> x \<and> x < real 18 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 43 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 43 + 1 \<and> real 37 \<le> 2 * x \<and>
      2 * x < real 37 + 1 \<and>
    real 35 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 35 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 18) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 18) (alpha_r * x - real 1) (2 * Hc_r * x - real 43) (2 * x - real 37) (2 *
        (lam_r * x) - real 35)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_136: "x \<in> {19<..<(820 / 43)} \<Longrightarrow> R_r x = (94 / 5) * x + (- 376)"
proof -
  assume x: "x \<in> {19<..<(820 / 43)}"
  have b: "19 < x" "x < (820 / 43)" using x by auto
  have "real 19 \<le> x \<and> x < real 19 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 43 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 43 + 1 \<and> real 38 \<le> 2 * x \<and>
      2 * x < real 38 + 1 \<and>
    real 35 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 35 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 19) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 19) (alpha_r * x - real 1) (2 * Hc_r * x - real 43) (2 * x - real 38) (2 *
        (lam_r * x) - real 35)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_137: "x \<in> {(820 / 43)<..<(440 / 23)} \<Longrightarrow>
  R_r x = (94 / 5) * x + (- 376)"
proof -
  assume x: "x \<in> {(820 / 43)<..<(440 / 23)}"
  have b: "(820 / 43) < x" "x < (440 / 23)" using x by auto
  have "real 19 \<le> x \<and> x < real 19 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 43 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 43 + 1 \<and> real 38 \<le> 2 * x \<and>
      2 * x < real 38 + 1 \<and>
    real 35 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 35 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 19) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 19) (alpha_r * x - real 1) (2 * Hc_r * x - real 43) (2 * x - real 38) (2 *
        (lam_r * x) - real 35)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_138: "x \<in> {(440 / 23)<..<(720 / 37)} \<Longrightarrow>
  R_r x = (353 / 20) * x + (- 354)"
proof -
  assume x: "x \<in> {(440 / 23)<..<(720 / 37)}"
  have b: "(440 / 23) < x" "x < (720 / 37)" using x by auto
  have "real 19 \<le> x \<and> x < real 19 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 44 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 44 + 1 \<and> real 38 \<le> 2 * x \<and>
      2 * x < real 38 + 1 \<and>
    real 35 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 35 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 19) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 19) (alpha_r * x - real 1) (2 * Hc_r * x - real 44) (2 * x - real 38) (2 *
        (lam_r * x) - real 35)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_139: "x \<in> {(720 / 37)<..<(39 / 2)} \<Longrightarrow>
  R_r x = (891 / 40) * x + (- 444)"
proof -
  assume x: "x \<in> {(720 / 37)<..<(39 / 2)}"
  have b: "(720 / 37) < x" "x < (39 / 2)" using x by auto
  have "real 19 \<le> x \<and> x < real 19 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 44 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 44 + 1 \<and> real 38 \<le> 2 * x \<and>
      2 * x < real 38 + 1 \<and>
    real 36 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 36 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 19) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 19) (alpha_r * x - real 1) (2 * Hc_r * x - real 44) (2 * x - real 38) (2 *
        (lam_r * x) - real 36)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_140: "x \<in> {(39 / 2)<..<(840 / 43)} \<Longrightarrow>
  R_r x = (931 / 40) * x + (- 927 / 2)"
proof -
  assume x: "x \<in> {(39 / 2)<..<(840 / 43)}"
  have b: "(39 / 2) < x" "x < (840 / 43)" using x by auto
  have "real 19 \<le> x \<and> x < real 19 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 44 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 44 + 1 \<and> real 39 \<le> 2 * x \<and>
      2 * x < real 39 + 1 \<and>
    real 36 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 36 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 19) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 19) (alpha_r * x - real 1) (2 * Hc_r * x - real 44) (2 * x - real 39) (2 *
        (lam_r * x) - real 36)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_141: "x \<in> {(840 / 43)<..<(450 / 23)} \<Longrightarrow>
  R_r x = (401 / 20) * x + (- 801 / 2)"
proof -
  assume x: "x \<in> {(840 / 43)<..<(450 / 23)}"
  have b: "(840 / 43) < x" "x < (450 / 23)" using x by auto
  have "real 19 \<le> x \<and> x < real 19 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 44 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 44 + 1 \<and> real 39 \<le> 2 * x \<and>
      2 * x < real 39 + 1 \<and>
    real 36 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 36 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 19) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 19) (alpha_r * x - real 1) (2 * Hc_r * x - real 44) (2 * x - real 39) (2 *
        (lam_r * x) - real 36)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

lemma inner_piece_142: "x \<in> {(450 / 23)<..<20} \<Longrightarrow>
  R_r x = (189 / 10) * x + (- 378)"
proof -
  assume x: "x \<in> {(450 / 23)<..<20}"
  have b: "(450 / 23) < x" "x < 20" using x by auto
  have "real 19 \<le> x \<and> x < real 19 + 1 \<and> real 1 \<le> alpha_r * x \<and>
    alpha_r * x < real 1 + 1 \<and>
    real 45 \<le> 2 * Hc_r * x \<and> 2 * Hc_r * x < real 45 + 1 \<and> real 39 \<le> 2 * x \<and>
      2 * x < real 39 + 1 \<and>
    real 36 \<le> 2 * (lam_r * x) \<and> 2 * (lam_r * x) < real 36 + 1"
    using b unfolding alpha_r_def Hc_r_def lam_r_def by linarith
  hence R: "R_r x = x * (4 * lam_r + 2 * lam_r * (x - real 19) - 12 * lam_r * (alpha_r * x -
    real 1))
      + Qc (x - real 19) (alpha_r * x - real 1) (2 * Hc_r * x - real 45) (2 * x - real 39) (2 *
        (lam_r * x) - real 36)"
    using R_on_piece by blast
  show ?thesis unfolding R Qc_def d0_def es_def pos_r_def min_def max_def alpha_r_def Hc_r_def
    lam_r_def
    using b by (simp add: field_simps power2_eq_square)
qed

theorem R_integral_3_20:
  "interval_lebesgue_integral lborel (ereal 3) (ereal 20) (\<lambda>x. R_r x / x ^ 3) =
    322437603634266857629 / 7535670527041937280000"
proof -
  have "interval_lebesgue_integrable lborel (ereal 3) (ereal (70 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (70 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (- (18 / 5) / (70 / 23) - (- 6) / (2 * (70 / 23) ^ 2)) - (- (18 / 5) / 3 - (- 6) / (2 *
        3 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_0)
  hence s0: "interval_lebesgue_integrable lborel (ereal 3) (ereal (70 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (70 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (113 / 14700)"
    by (simp add: power2_eq_square power3_eq_cube)
  have r1: "interval_lebesgue_integrable lborel (ereal (70 / 23)) (ereal (120 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (70 / 23)) (ereal (120 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (49 / 20) / (120 / 37) - (- 5 / 2) / (2 * (120 / 37) ^ 2)) - (- (49 / 20) /
        (70 / 23) - (- 5 / 2) / (2 * (70 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_1)
  have s1: "interval_lebesgue_integrable lborel (ereal 3) (ereal (120 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (120 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (3319 / 80640)"
    using chain[OF _ _ s0 r1] by (simp add: power2_eq_square power3_eq_cube)
  have r2: "interval_lebesgue_integrable lborel (ereal (120 / 37)) (ereal (140 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (120 / 37)) (ereal (140 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (283 / 40) / (140 / 43) - (- 35 / 2) / (2 * (140 / 43) ^ 2)) - (- (283 / 40) /
        (120 / 37) - (- 35 / 2) / (2 * (120 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_2)
  have s2: "interval_lebesgue_integrable lborel (ereal 3) (ereal (140 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (140 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (967 / 22400)"
    using chain[OF _ _ s1 r2] by (simp add: power2_eq_square power3_eq_cube)
  have r3: "interval_lebesgue_integrable lborel (ereal (140 / 43)) (ereal (10 /
    3)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (140 / 43)) (ereal (10 / 3)) (\<lambda>x. R_r x /
        x ^ 3) = (- (283 / 40) / (10 / 3) - (- 35 / 2) / (2 * (10 / 3) ^ 2)) - (- (283 / 40) /
        (140 / 43) - (- 35 / 2) / (2 * (140 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_3)
  have s3: "interval_lebesgue_integrable lborel (ereal 3) (ereal (10 / 3)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (10 / 3)) (\<lambda>x. R_r x / x ^ 3) =
        (1249 / 22400)"
    using chain[OF _ _ s2 r3] by (simp add: power2_eq_square power3_eq_cube)
  have r4: "interval_lebesgue_integrable lborel (ereal (10 / 3)) (ereal (80 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (10 / 3)) (ereal (80 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (277 / 40) / (80 / 23) - (- 17) / (2 * (80 / 23) ^ 2)) - (- (277 / 40) / (10 /
        3) - (- 17) / (2 * (10 / 3) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_4)
  have s4: "interval_lebesgue_integrable lborel (ereal 3) (ereal (80 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (80 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (7159 / 89600)"
    using chain[OF _ _ s3 r4] by (simp add: power2_eq_square power3_eq_cube)
  have r5: "interval_lebesgue_integrable lborel (ereal (80 / 23)) (ereal (7 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (80 / 23)) (ereal (7 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (231 / 40) / (7 / 2) - (- 13) / (2 * (7 / 2) ^ 2)) - (- (231 / 40) / (80 / 23) -
        (- 13) / (2 * (80 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_5)
  have s5: "interval_lebesgue_integrable lborel (ereal 3) (ereal (7 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (7 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (6551 / 78400)"
    using chain[OF _ _ s4 r5] by (simp add: power2_eq_square power3_eq_cube)
  have r6: "interval_lebesgue_integrable lborel (ereal (7 / 2)) (ereal (160 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (7 / 2)) (ereal (160 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (271 / 40) / (160 / 43) - (- 33 / 2) / (2 * (160 / 43) ^ 2)) - (- (271 / 40) /
        (7 / 2) - (- 33 / 2) / (2 * (7 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_6)
  have s6: "interval_lebesgue_integrable lborel (ereal 3) (ereal (160 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (160 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (17331 / 143360)"
    using chain[OF _ _ s5 r6] by (simp add: power2_eq_square power3_eq_cube)
  have r7: "interval_lebesgue_integrable lborel (ereal (160 / 43)) (ereal (140 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (160 / 43)) (ereal (140 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (71 / 20) / (140 / 37) - (- 9 / 2) / (2 * (140 / 37) ^ 2)) - (- (71 / 20) /
        (160 / 43) - (- 9 / 2) / (2 * (160 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_7)
  have s7: "interval_lebesgue_integrable lborel (ereal 3) (ereal (140 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (140 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (16481 / 125440)"
    using chain[OF _ _ s6 r7] by (simp add: power2_eq_square power3_eq_cube)
  have r8: "interval_lebesgue_integrable lborel (ereal (140 / 37)) (ereal (90 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (140 / 37)) (ereal (90 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (27 / 5) / (90 / 23) - (- 23 / 2) / (2 * (90 / 23) ^ 2)) - (- (27 / 5) / (140 /
        37) - (- 23 / 2) / (2 * (140 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_8)
  have s8: "interval_lebesgue_integrable lborel (ereal 3) (ereal (90 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (90 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (1106299 / 7257600)"
    using chain[OF _ _ s7 r8] by (simp add: power2_eq_square power3_eq_cube)
  have r9: "interval_lebesgue_integrable lborel (ereal (90 / 23)) (ereal 4) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (90 / 23)) (ereal 4) (\<lambda>x. R_r x / x ^ 3) =
        (- (17 / 4) / 4 - (- 7) / (2 * 4 ^ 2)) - (- (17 / 4) / (90 / 23) - (- 7) / (2 * (90 /
        23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_9)
  have s9: "interval_lebesgue_integrable lborel (ereal 3) (ereal 4) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 4) (\<lambda>x. R_r x / x ^ 3) =
        (26807 / 161280)"
    using chain[OF _ _ s8 r9] by (simp add: power2_eq_square power3_eq_cube)
  have r10: "interval_lebesgue_integrable lborel (ereal 4) (ereal (180 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 4) (ereal (180 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- (17 / 5) / (180 / 43) - (- 11) / (2 * (180 / 43) ^ 2)) - (- (17 / 5) / 4 - (- 11) / (2 *
        4 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_10)
  have s10: "interval_lebesgue_integrable lborel (ereal 3) (ereal (180 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (180 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (1263659 / 7257600)"
    using chain[OF _ _ s9 r10] by (simp add: power2_eq_square power3_eq_cube)
  have r11: "interval_lebesgue_integrable lborel (ereal (180 / 43)) (ereal (160 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (180 / 43)) (ereal (160 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (17 / 5) / (160 / 37) - (- 11) / (2 * (160 / 37) ^ 2)) - (- (17 / 5) / (180 /
        43) - (- 11) / (2 * (180 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_11)
  have s11: "interval_lebesgue_integrable lborel (ereal 3) (ereal (160 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (160 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (581689 / 3225600)"
    using chain[OF _ _ s10 r11] by (simp add: power2_eq_square power3_eq_cube)
  have r12: "interval_lebesgue_integrable lborel (ereal (160 / 37)) (ereal (100 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (160 / 37)) (ereal (100 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (321 / 40) / (100 / 23) - (- 31) / (2 * (100 / 23) ^ 2)) - (- (321 / 40) /
        (160 / 37) - (- 31) / (2 * (160 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_12)
  have s12: "interval_lebesgue_integrable lborel (ereal 3) (ereal (100 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (100 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (1828811 / 10080000)"
    using chain[OF _ _ s11 r12] by (simp add: power2_eq_square power3_eq_cube)
  have r13: "interval_lebesgue_integrable lborel (ereal (100 / 23)) (ereal (9 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (100 / 23)) (ereal (9 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (55 / 8) / (9 / 2) - (- 26) / (2 * (9 / 2) ^ 2)) - (- (55 / 8) / (100 / 23) -
        (- 26) / (2 * (100 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_13)
  have s13: "interval_lebesgue_integrable lborel (ereal 3) (ereal (9 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (9 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (3432431 / 18144000)"
    using chain[OF _ _ s12 r13] by (simp add: power2_eq_square power3_eq_cube)
  have r14: "interval_lebesgue_integrable lborel (ereal (9 / 2)) (ereal (200 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (9 / 2)) (ereal (200 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (63 / 8) / (200 / 43) - (- 61 / 2) / (2 * (200 / 43) ^ 2)) - (- (63 / 8) / (9 /
        2) - (- 61 / 2) / (2 * (9 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_14)
  have s14: "interval_lebesgue_integrable lborel (ereal 3) (ereal (200 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (200 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (332467 / 1680000)"
    using chain[OF _ _ s13 r14] by (simp add: power2_eq_square power3_eq_cube)
  have r15: "interval_lebesgue_integrable lborel (ereal (200 / 43)) (ereal (110 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (200 / 43)) (ereal (110 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (93 / 20) / (110 / 23) - (- 31 / 2) / (2 * (110 / 23) ^ 2)) - (- (93 / 20) /
        (200 / 43) - (- 31 / 2) / (2 * (200 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_15)
  have s15: "interval_lebesgue_integrable lborel (ereal 3) (ereal (110 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (110 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (16746439 / 81312000)"
    using chain[OF _ _ s14 r15] by (simp add: power2_eq_square power3_eq_cube)
  have r16: "interval_lebesgue_integrable lborel (ereal (110 / 23)) (ereal (180 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (110 / 23)) (ereal (180 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (7 / 2) / (180 / 37) - (- 10) / (2 * (180 / 37) ^ 2)) - (- (7 / 2) / (110 /
        23) - (- 10) / (2 * (110 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_16)
  have s16: "interval_lebesgue_integrable lborel (ereal 3) (ereal (180 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (180 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (42111623 / 199584000)"
    using chain[OF _ _ s15 r16] by (simp add: power2_eq_square power3_eq_cube)
  have r17: "interval_lebesgue_integrable lborel (ereal (180 / 37)) (ereal 5) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (180 / 37)) (ereal 5) (\<lambda>x. R_r x / x ^ 3) =
        (- (107 / 20) / 5 - (- 19) / (2 * 5 ^ 2)) - (- (107 / 20) / (180 / 37) - (- 19) / (2 *
        (180 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_17)
  have s17: "interval_lebesgue_integrable lborel (ereal 3) (ereal 5) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 5) (\<lambda>x. R_r x / x ^ 3) =
        (4863527 / 22176000)"
    using chain[OF _ _ s16 r17] by (simp add: power2_eq_square power3_eq_cube)
  have r18: "interval_lebesgue_integrable lborel (ereal 5) (ereal (220 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 5) (ereal (220 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- (9 / 2) / (220 / 43) - (- 24) / (2 * (220 / 43) ^ 2)) - (- (9 / 2) / 5 - (- 24) / (2 *
        5 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_18)
  have s18: "interval_lebesgue_integrable lborel (ereal 3) (ereal (220 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (220 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (53226637 / 243936000)"
    using chain[OF _ _ s17 r18] by (simp add: power2_eq_square power3_eq_cube)
  have r19: "interval_lebesgue_integrable lborel (ereal (220 / 43)) (ereal (120 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (220 / 43)) (ereal (120 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (9 / 2) / (120 / 23) - (- 24) / (2 * (120 / 23) ^ 2)) - (- (9 / 2) / (220 /
        43) - (- 24) / (2 * (220 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_19)
  have s19: "interval_lebesgue_integrable lborel (ereal 3) (ereal (120 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (120 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (4826567 / 22176000)"
    using chain[OF _ _ s18 r19] by (simp add: power2_eq_square power3_eq_cube)
  have r20: "interval_lebesgue_integrable lborel (ereal (120 / 23)) (ereal (200 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (120 / 23)) (ereal (200 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (67 / 20) / (200 / 37) - (- 18) / (2 * (200 / 37) ^ 2)) - (- (67 / 20) / (120 /
        23) - (- 18) / (2 * (120 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_20)
  have s20: "interval_lebesgue_integrable lborel (ereal 3) (ereal (200 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (200 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (24103267 / 110880000)"
    using chain[OF _ _ s19 r20] by (simp add: power2_eq_square power3_eq_cube)
  have r21: "interval_lebesgue_integrable lborel (ereal (200 / 37)) (ereal (11 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (200 / 37)) (ereal (11 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (319 / 40) / (11 / 2) - (- 43) / (2 * (11 / 2) ^ 2)) - (- (319 / 40) / (200 /
        37) - (- 43) / (2 * (200 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_21)
  have s21: "interval_lebesgue_integrable lborel (ereal 3) (ereal (11 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (11 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (53095807 / 243936000)"
    using chain[OF _ _ s20 r21] by (simp add: power2_eq_square power3_eq_cube)
  have r22: "interval_lebesgue_integrable lborel (ereal (11 / 2)) (ereal (240 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (11 / 2)) (ereal (240 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (359 / 40) / (240 / 43) - (- 97 / 2) / (2 * (240 / 43) ^ 2)) - (- (359 / 40) /
        (11 / 2) - (- 97 / 2) / (2 * (11 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_22)
  have s22: "interval_lebesgue_integrable lborel (ereal 3) (ereal (240 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (240 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (6453191 / 29568000)"
    using chain[OF _ _ s21 r22] by (simp add: power2_eq_square power3_eq_cube)
  have r23: "interval_lebesgue_integrable lborel (ereal (240 / 43)) (ereal (130 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (240 / 43)) (ereal (130 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (23 / 4) / (130 / 23) - (- 61 / 2) / (2 * (130 / 23) ^ 2)) - (- (23 / 4) /
        (240 / 43) - (- 61 / 2) / (2 * (240 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_23)
  have s23: "interval_lebesgue_integrable lborel (ereal 3) (ereal (130 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (130 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (205157387 / 936936000)"
    using chain[OF _ _ s22 r23] by (simp add: power2_eq_square power3_eq_cube)
  have r24: "interval_lebesgue_integrable lborel (ereal (130 / 23)) (ereal (220 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (130 / 23)) (ereal (220 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (23 / 5) / (220 / 37) - (- 24) / (2 * (220 / 37) ^ 2)) - (- (23 / 5) / (130 /
        23) - (- 24) / (2 * (130 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_24)
  have s24: "interval_lebesgue_integrable lborel (ereal 3) (ereal (220 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (220 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (176773789 / 792792000)"
    using chain[OF _ _ s23 r24] by (simp add: power2_eq_square power3_eq_cube)
  have r25: "interval_lebesgue_integrable lborel (ereal (220 / 37)) (ereal 6) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (220 / 37)) (ereal 6) (\<lambda>x. R_r x / x ^ 3) =
        (- (129 / 20) / 6 - (- 35) / (2 * 6 ^ 2)) - (- (129 / 20) / (220 / 37) - (- 35) / (2 *
        (220 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_25)
  have s25: "interval_lebesgue_integrable lborel (ereal 3) (ereal 6) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 6) (\<lambda>x. R_r x / x ^ 3) =
        (488933 / 2184000)"
    using chain[OF _ _ s24 r25] by (simp add: power2_eq_square power3_eq_cube)
  have r26: "interval_lebesgue_integrable lborel (ereal 6) (ereal (260 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 6) (ereal (260 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- (28 / 5) / (260 / 43) - (- 41) / (2 * (260 / 43) ^ 2)) - (- (28 / 5) / 6 - (- 41) / (2 *
        6 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_26)
  have s26: "interval_lebesgue_integrable lborel (ereal 3) (ereal (260 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (260 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (18936577 / 85176000)"
    using chain[OF _ _ s25 r26] by (simp add: power2_eq_square power3_eq_cube)
  have r27: "interval_lebesgue_integrable lborel (ereal (260 / 43)) (ereal (140 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (260 / 43)) (ereal (140 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (28 / 5) / (140 / 23) - (- 41) / (2 * (140 / 23) ^ 2)) - (- (28 / 5) / (260 /
        43) - (- 41) / (2 * (260 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_27)
  have s27: "interval_lebesgue_integrable lborel (ereal 3) (ereal (140 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (140 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (10138243 / 45864000)"
    using chain[OF _ _ s26 r27] by (simp add: power2_eq_square power3_eq_cube)
  have r28: "interval_lebesgue_integrable lborel (ereal (140 / 23)) (ereal (240 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (140 / 23)) (ereal (240 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (89 / 20) / (240 / 37) - (- 34) / (2 * (240 / 37) ^ 2)) - (- (89 / 20) / (140 /
        23) - (- 34) / (2 * (140 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_28)
  have s28: "interval_lebesgue_integrable lborel (ereal 3) (ereal (240 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (240 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (5537711 / 26208000)"
    using chain[OF _ _ s27 r28] by (simp add: power2_eq_square power3_eq_cube)
  have r29: "interval_lebesgue_integrable lborel (ereal (240 / 37)) (ereal (13 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (240 / 37)) (ereal (13 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (363 / 40) / (13 / 2) - (- 64) / (2 * (13 / 2) ^ 2)) - (- (363 / 40) / (240 /
        37) - (- 64) / (2 * (240 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_29)
  have s29: "interval_lebesgue_integrable lborel (ereal 3) (ereal (13 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (13 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (71904913 / 340704000)"
    using chain[OF _ _ s28 r29] by (simp add: power2_eq_square power3_eq_cube)
  have r30: "interval_lebesgue_integrable lborel (ereal (13 / 2)) (ereal (280 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (13 / 2)) (ereal (280 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (403 / 40) / (280 / 43) - (- 141 / 2) / (2 * (280 / 43) ^ 2)) - (- (403 / 40) /
        (13 / 2) - (- 141 / 2) / (2 * (13 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_30)
  have s30: "interval_lebesgue_integrable lborel (ereal 3) (ereal (280 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (280 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (9669913 / 45864000)"
    using chain[OF _ _ s29 r30] by (simp add: power2_eq_square power3_eq_cube)
  have r31: "interval_lebesgue_integrable lborel (ereal (280 / 43)) (ereal (150 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (280 / 43)) (ereal (150 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (137 / 20) / (150 / 23) - (- 99 / 2) / (2 * (150 / 23) ^ 2)) - (- (137 / 20) /
        (280 / 43) - (- 99 / 2) / (2 * (280 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_31)
  have s31: "interval_lebesgue_integrable lborel (ereal 3) (ereal (150 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (150 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (27605051 / 131040000)"
    using chain[OF _ _ s30 r31] by (simp add: power2_eq_square power3_eq_cube)
  have r32: "interval_lebesgue_integrable lborel (ereal (150 / 23)) (ereal (20 /
    3)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (150 / 23)) (ereal (20 / 3)) (\<lambda>x. R_r x /
        x ^ 3) = (- (57 / 10) / (20 / 3) - (- 42) / (2 * (20 / 3) ^ 2)) - (- (57 / 10) / (150 /
        23) - (- 42) / (2 * (150 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_32)
  have s32: "interval_lebesgue_integrable lborel (ereal 3) (ereal (20 / 3)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (20 / 3)) (\<lambda>x. R_r x / x ^ 3) =
        (5462479 / 26208000)"
    using chain[OF _ _ s31 r32] by (simp add: power2_eq_square power3_eq_cube)
  have r33: "interval_lebesgue_integrable lborel (ereal (20 / 3)) (ereal (160 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (20 / 3)) (ereal (160 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (69 / 10) / (160 / 23) - (- 50) / (2 * (160 / 23) ^ 2)) - (- (69 / 10) / (20 /
        3) - (- 50) / (2 * (20 / 3) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_33)
  have s33: "interval_lebesgue_integrable lborel (ereal 3) (ereal (160 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (160 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (21559171 / 104832000)"
    using chain[OF _ _ s32 r33] by (simp add: power2_eq_square power3_eq_cube)
  have r34: "interval_lebesgue_integrable lborel (ereal (160 / 23)) (ereal (300 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (160 / 23)) (ereal (300 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (23 / 4) / (300 / 43) - (- 42) / (2 * (300 / 43) ^ 2)) - (- (23 / 4) / (160 /
        23) - (- 42) / (2 * (160 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_34)
  have s34: "interval_lebesgue_integrable lborel (ereal 3) (ereal (300 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (300 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (1683359 / 8190000)"
    using chain[OF _ _ s33 r34] by (simp add: power2_eq_square power3_eq_cube)
  have r35: "interval_lebesgue_integrable lborel (ereal (300 / 43)) (ereal 7) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (300 / 43)) (ereal 7) (\<lambda>x. R_r x / x ^ 3) =
        (- (23 / 4) / 7 - (- 42) / (2 * 7 ^ 2)) - (- (23 / 4) / (300 / 43) - (- 42) / (2 * (300 /
        43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_35)
  have s35: "interval_lebesgue_integrable lborel (ereal 3) (ereal 7) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 7) (\<lambda>x. R_r x / x ^ 3) =
        (48067 / 234000)"
    using chain[OF _ _ s34 r35] by (simp add: power2_eq_square power3_eq_cube)
  have r36: "interval_lebesgue_integrable lborel (ereal 7) (ereal (260 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 7) (ereal (260 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (- (49 / 10) / (260 / 37) - (- 49) / (2 * (260 / 37) ^ 2)) - (- (49 / 10) / 7 - (- 49) /
        (2 * 7 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_36)
  have s36: "interval_lebesgue_integrable lborel (ereal 3) (ereal (260 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (260 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (1242767 / 6084000)"
    using chain[OF _ _ s35 r36] by (simp add: power2_eq_square power3_eq_cube)
  have r37: "interval_lebesgue_integrable lborel (ereal (260 / 37)) (ereal (170 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (260 / 37)) (ereal (170 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (27 / 4) / (170 / 23) - (- 62) / (2 * (170 / 23) ^ 2)) - (- (27 / 4) / (260 /
        37) - (- 62) / (2 * (260 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_37)
  have s37: "interval_lebesgue_integrable lborel (ereal 3) (ereal (170 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (170 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (25867391 / 135252000)"
    using chain[OF _ _ s36 r37] by (simp add: power2_eq_square power3_eq_cube)
  have r38: "interval_lebesgue_integrable lborel (ereal (170 / 23)) (ereal (320 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (170 / 23)) (ereal (320 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (28 / 5) / (320 / 43) - (- 107 / 2) / (2 * (320 / 43) ^ 2)) - (- (28 / 5) /
        (170 / 23) - (- 107 / 2) / (2 * (170 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_38)
  have s38: "interval_lebesgue_integrable lborel (ereal 3) (ereal (320 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (320 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (773023451 / 4073472000)"
    using chain[OF _ _ s37 r38] by (simp add: power2_eq_square power3_eq_cube)
  have r39: "interval_lebesgue_integrable lborel (ereal (320 / 43)) (ereal (15 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (320 / 43)) (ereal (15 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (19 / 8) / (15 / 2) - (- 59 / 2) / (2 * (15 / 2) ^ 2)) - (- (19 / 8) / (320 /
        43) - (- 59 / 2) / (2 * (320 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_39)
  have s39: "interval_lebesgue_integrable lborel (ereal 3) (ereal (15 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (15 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (47896621 / 254592000)"
    using chain[OF _ _ s38 r39] by (simp add: power2_eq_square power3_eq_cube)
  have r40: "interval_lebesgue_integrable lborel (ereal (15 / 2)) (ereal (280 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (15 / 2)) (ereal (280 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (27 / 8) / (280 / 37) - (- 37) / (2 * (280 / 37) ^ 2)) - (- (27 / 8) / (15 /
        2) - (- 37) / (2 * (15 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_40)
  have s40: "interval_lebesgue_integrable lborel (ereal 3) (ereal (280 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (280 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (2324118389 / 12475008000)"
    using chain[OF _ _ s39 r40] by (simp add: power2_eq_square power3_eq_cube)
  have r41: "interval_lebesgue_integrable lborel (ereal (280 / 37)) (ereal (180 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (280 / 37)) (ereal (180 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- 8 / (180 / 23) - (- 72) / (2 * (180 / 23) ^ 2)) - (- 8 / (280 / 37) - (- 72) /
        (2 * (280 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_41)
  have s41: "interval_lebesgue_integrable lborel (ereal 3) (ereal (180 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (180 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (321459427 / 1782144000)"
    using chain[OF _ _ s40 r41] by (simp add: power2_eq_square power3_eq_cube)
  have r42: "interval_lebesgue_integrable lborel (ereal (180 / 23)) (ereal (340 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (180 / 23)) (ereal (340 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (137 / 20) / (340 / 43) - (- 63) / (2 * (340 / 43) ^ 2)) - (- (137 / 20) /
        (180 / 23) - (- 63) / (2 * (180 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_42)
  have s42: "interval_lebesgue_integrable lborel (ereal 3) (ereal (340 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (340 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (1806305713 / 10098816000)"
    using chain[OF _ _ s41 r42] by (simp add: power2_eq_square power3_eq_cube)
  have r43: "interval_lebesgue_integrable lborel (ereal (340 / 43)) (ereal 8) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (340 / 43)) (ereal 8) (\<lambda>x. R_r x / x ^ 3) =
        (- (137 / 20) / 8 - (- 63) / (2 * 8 ^ 2)) - (- (137 / 20) / (340 / 43) - (- 63) / (2 *
        (340 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_43)
  have s43: "interval_lebesgue_integrable lborel (ereal 3) (ereal 8) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 8) (\<lambda>x. R_r x / x ^ 3) =
        (105317369 / 594048000)"
    using chain[OF _ _ s42 r43] by (simp add: power2_eq_square power3_eq_cube)
  have r44: "interval_lebesgue_integrable lborel (ereal 8) (ereal (300 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 8) (ereal (300 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (- 6 / (300 / 37) - (- 71) / (2 * (300 / 37) ^ 2)) - (- 6 / 8 - (- 71) / (2 * 8 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_44)
  have s44: "interval_lebesgue_integrable lborel (ereal 3) (ereal (300 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (300 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (1537942031 / 8910720000)"
    using chain[OF _ _ s43 r44] by (simp add: power2_eq_square power3_eq_cube)
  have r45: "interval_lebesgue_integrable lborel (ereal (300 / 37)) (ereal (190 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (300 / 37)) (ereal (190 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (157 / 20) / (190 / 23) - (- 86) / (2 * (190 / 23) ^ 2)) - (- (157 / 20) /
        (300 / 37) - (- 86) / (2 * (300 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_45)
  have s45: "interval_lebesgue_integrable lborel (ereal 3) (ereal (190 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (190 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (2380854663 / 14296755200)"
    using chain[OF _ _ s44 r45] by (simp add: power2_eq_square power3_eq_cube)
  have r46: "interval_lebesgue_integrable lborel (ereal (190 / 23)) (ereal (360 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (190 / 23)) (ereal (360 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (67 / 10) / (360 / 43) - (- 153 / 2) / (2 * (360 / 43) ^ 2)) - (- (67 / 10) /
        (190 / 23) - (- 153 / 2) / (2 * (190 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_46)
  have s46: "interval_lebesgue_integrable lborel (ereal 3) (ereal (360 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (360 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (1100556809 / 6772147200)"
    using chain[OF _ _ s45 r46] by (simp add: power2_eq_square power3_eq_cube)
  have r47: "interval_lebesgue_integrable lborel (ereal (360 / 43)) (ereal (17 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (360 / 43)) (ereal (17 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (139 / 40) / (17 / 2) - (- 99 / 2) / (2 * (17 / 2) ^ 2)) - (- (139 / 40) /
        (360 / 43) - (- 99 / 2) / (2 * (360 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_47)
  have s47: "interval_lebesgue_integrable lborel (ereal 3) (ereal (17 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (17 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (6071429023 / 38375500800)"
    using chain[OF _ _ s46 r47] by (simp add: power2_eq_square power3_eq_cube)
  have r48: "interval_lebesgue_integrable lborel (ereal (17 / 2)) (ereal (320 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (17 / 2)) (ereal (320 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (179 / 40) / (320 / 37) - (- 58) / (2 * (320 / 37) ^ 2)) - (- (179 / 40) / (17 /
        2) - (- 58) / (2 * (17 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_48)
  have s48: "interval_lebesgue_integrable lborel (ereal 3) (ereal (320 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (320 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (1386762179 / 9029529600)"
    using chain[OF _ _ s47 r48] by (simp add: power2_eq_square power3_eq_cube)
  have r49: "interval_lebesgue_integrable lborel (ereal (320 / 37)) (ereal (200 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (320 / 37)) (ereal (200 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (91 / 10) / (200 / 23) - (- 98) / (2 * (200 / 23) ^ 2)) - (- (91 / 10) / (320 /
        37) - (- 98) / (2 * (320 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_49)
  have s49: "interval_lebesgue_integrable lborel (ereal 3) (ereal (200 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (200 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (4294822027 / 28217280000)"
    using chain[OF _ _ s48 r49] by (simp add: power2_eq_square power3_eq_cube)
  have r50: "interval_lebesgue_integrable lborel (ereal (200 / 23)) (ereal (380 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (200 / 23)) (ereal (380 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (159 / 20) / (380 / 43) - (- 88) / (2 * (380 / 43) ^ 2)) - (- (159 / 20) /
        (200 / 23) - (- 88) / (2 * (200 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_50)
  have s50: "interval_lebesgue_integrable lborel (ereal 3) (ereal (380 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (380 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (15907712813 / 107225664000)"
    using chain[OF _ _ s49 r50] by (simp add: power2_eq_square power3_eq_cube)
  have r51: "interval_lebesgue_integrable lborel (ereal (380 / 43)) (ereal 9) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (380 / 43)) (ereal 9) (\<lambda>x. R_r x / x ^ 3) =
        (- (159 / 20) / 9 - (- 88) / (2 * 9 ^ 2)) - (- (159 / 20) / (380 / 43) - (- 88) / (2 *
        (380 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_51)
  have s51: "interval_lebesgue_integrable lborel (ereal 3) (ereal 9) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 9) (\<lambda>x. R_r x / x ^ 3) =
        (22007571589 / 152373312000)"
    using chain[OF _ _ s50 r51] by (simp add: power2_eq_square power3_eq_cube)
  have r52: "interval_lebesgue_integrable lborel (ereal 9) (ereal (210 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 9) (ereal (210 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (- (71 / 10) / (210 / 23) - (- 97) / (2 * (210 / 23) ^ 2)) - (- (71 / 10) / 9 - (- 97) /
        (2 * 9 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_52)
  have s52: "interval_lebesgue_integrable lborel (ereal 3) (ereal (210 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (210 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (16439636107 / 118512576000)"
    using chain[OF _ _ s51 r52] by (simp add: power2_eq_square power3_eq_cube)
  have r53: "interval_lebesgue_integrable lborel (ereal (210 / 23)) (ereal (340 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (210 / 23)) (ereal (340 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (119 / 20) / (340 / 37) - (- 173 / 2) / (2 * (340 / 37) ^ 2)) - (- (119 / 20) /
        (210 / 23) - (- 173 / 2) / (2 * (210 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_53)
  have s53: "interval_lebesgue_integrable lborel (ereal 3) (ereal (340 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (340 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (622550859 / 4568512000)"
    using chain[OF _ _ s52 r53] by (simp add: power2_eq_square power3_eq_cube)
  have r54: "interval_lebesgue_integrable lborel (ereal (340 / 37)) (ereal (400 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (340 / 37)) (ereal (400 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (39 / 5) / (400 / 43) - (- 207 / 2) / (2 * (400 / 43) ^ 2)) - (- (39 / 5) /
        (340 / 37) - (- 207 / 2) / (2 * (340 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_54)
  have s54: "interval_lebesgue_integrable lborel (ereal 3) (ereal (400 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (400 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (354131967 / 2687360000)"
    using chain[OF _ _ s53 r54] by (simp add: power2_eq_square power3_eq_cube)
  have r55: "interval_lebesgue_integrable lborel (ereal (400 / 43)) (ereal (19 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (400 / 43)) (ereal (19 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (183 / 40) / (19 / 2) - (- 147 / 2) / (2 * (19 / 2) ^ 2)) - (- (183 / 40) /
        (400 / 43) - (- 147 / 2) / (2 * (400 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_55)
  have s55: "interval_lebesgue_integrable lborel (ereal 3) (ereal (19 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (19 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (635799579 / 5105984000)"
    using chain[OF _ _ s54 r55] by (simp add: power2_eq_square power3_eq_cube)
  have r56: "interval_lebesgue_integrable lborel (ereal (19 / 2)) (ereal (220 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (19 / 2)) (ereal (220 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (223 / 40) / (220 / 23) - (- 83) / (2 * (220 / 23) ^ 2)) - (- (223 / 40) / (19 /
        2) - (- 83) / (2 * (19 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_56)
  have s56: "interval_lebesgue_integrable lborel (ereal 3) (ereal (220 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (220 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (3975944721 / 32517056000)"
    using chain[OF _ _ s55 r56] by (simp add: power2_eq_square power3_eq_cube)
  have r57: "interval_lebesgue_integrable lborel (ereal (220 / 23)) (ereal (360 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (220 / 23)) (ereal (360 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (177 / 40) / (360 / 37) - (- 72) / (2 * (360 / 37) ^ 2)) - (- (177 / 40) /
        (220 / 23) - (- 72) / (2 * (220 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_57)
  have s57: "interval_lebesgue_integrable lborel (ereal 3) (ereal (360 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (360 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (3110142259 / 26604864000)"
    using chain[OF _ _ s56 r57] by (simp add: power2_eq_square power3_eq_cube)
  have r58: "interval_lebesgue_integrable lborel (ereal (360 / 37)) (ereal (420 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (360 / 37)) (ereal (420 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (181 / 20) / (420 / 43) - (- 117) / (2 * (420 / 43) ^ 2)) - (- (181 / 20) /
        (360 / 37) - (- 117) / (2 * (360 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_58)
  have s58: "interval_lebesgue_integrable lborel (ereal 3) (ereal (420 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (420 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (150869962351 / 1303638336000)"
    using chain[OF _ _ s57 r58] by (simp add: power2_eq_square power3_eq_cube)
  have r59: "interval_lebesgue_integrable lborel (ereal (420 / 43)) (ereal 10) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (420 / 43)) (ereal 10) (\<lambda>x. R_r x / x ^ 3) =
        (- (181 / 20) / 10 - (- 117) / (2 * 10 ^ 2)) - (- (181 / 20) / (420 / 43) - (- 117) / (2 *
        (420 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_59)
  have s59: "interval_lebesgue_integrable lborel (ereal 3) (ereal 10) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 10) (\<lambda>x. R_r x / x ^ 3) =
        (2902291759 / 26604864000)"
    using chain[OF _ _ s58 r59] by (simp add: power2_eq_square power3_eq_cube)
  have r60: "interval_lebesgue_integrable lborel (ereal 10) (ereal (440 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 10) (ereal (440 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- (69 / 10) / (440 / 43) - (- 114) / (2 * (440 / 43) ^ 2)) - (- (69 / 10) / 10 - (- 114) /
        (2 * 10 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_60)
  have s60: "interval_lebesgue_integrable lborel (ereal 3) (ereal (440 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (440 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (29018325629 / 292653504000)"
    using chain[OF _ _ s59 r60] by (simp add: power2_eq_square power3_eq_cube)
  have r61: "interval_lebesgue_integrable lborel (ereal (440 / 43)) (ereal (380 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (440 / 43)) (ereal (380 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (147 / 40) / (380 / 37) - (- 81) / (2 * (380 / 37) ^ 2)) - (- (147 / 40) /
        (440 / 43) - (- 81) / (2 * (440 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_61)
  have s61: "interval_lebesgue_integrable lborel (ereal 3) (ereal (380 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (380 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (49355911441 / 505492416000)"
    using chain[OF _ _ s60 r61] by (simp add: power2_eq_square power3_eq_cube)
  have r62: "interval_lebesgue_integrable lborel (ereal (380 / 37)) (ereal (240 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (380 / 37)) (ereal (240 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (221 / 40) / (240 / 23) - (- 100) / (2 * (240 / 23) ^ 2)) - (- (221 / 40) /
        (380 / 37) - (- 100) / (2 * (380 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_62)
  have s62: "interval_lebesgue_integrable lborel (ereal 3) (ereal (240 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (240 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (809599753 / 8868288000)"
    using chain[OF _ _ s61 r62] by (simp add: power2_eq_square power3_eq_cube)
  have r63: "interval_lebesgue_integrable lborel (ereal (240 / 23)) (ereal (21 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (240 / 23)) (ereal (21 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (35 / 8) / (21 / 2) - (- 88) / (2 * (21 / 2) ^ 2)) - (- (35 / 8) / (240 / 23) -
        (- 88) / (2 * (240 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_63)
  have s63: "interval_lebesgue_integrable lborel (ereal 3) (ereal (21 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (21 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (38627440277 / 434546112000)"
    using chain[OF _ _ s62 r63] by (simp add: power2_eq_square power3_eq_cube)
  have r64: "interval_lebesgue_integrable lborel (ereal (21 / 2)) (ereal (460 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (21 / 2)) (ereal (460 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (43 / 8) / (460 / 43) - (- 197 / 2) / (2 * (460 / 43) ^ 2)) - (- (43 / 8) /
        (21 / 2) - (- 197 / 2) / (2 * (21 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_64)
  have s64: "interval_lebesgue_integrable lborel (ereal 3) (ereal (460 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (460 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (8077887148897 / 98517811392000)"
    using chain[OF _ _ s63 r64] by (simp add: power2_eq_square power3_eq_cube)
  have r65: "interval_lebesgue_integrable lborel (ereal (460 / 43)) (ereal (400 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (460 / 43)) (ereal (400 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (43 / 8) / (400 / 37) - (- 197 / 2) / (2 * (400 / 37) ^ 2)) - (- (43 / 8) /
        (460 / 43) - (- 197 / 2) / (2 * (460 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_65)
  have s65: "interval_lebesgue_integrable lborel (ereal 3) (ereal (400 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (400 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (145806399481 / 1862340480000)"
    using chain[OF _ _ s64 r65] by (simp add: power2_eq_square power3_eq_cube)
  have r66: "interval_lebesgue_integrable lborel (ereal (400 / 37)) (ereal (250 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (400 / 37)) (ereal (250 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- 10 / (250 / 23) - (- 297 / 2) / (2 * (250 / 23) ^ 2)) - (- 10 / (400 / 37) -
        (- 297 / 2) / (2 * (400 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_66)
  have s66: "interval_lebesgue_integrable lborel (ereal 3) (ereal (250 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (250 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (1779523554587 / 23279256000000)"
    using chain[OF _ _ s65 r66] by (simp add: power2_eq_square power3_eq_cube)
  have r67: "interval_lebesgue_integrable lborel (ereal (250 / 23)) (ereal 11) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (250 / 23)) (ereal 11) (\<lambda>x. R_r x / x ^ 3) =
        (- (177 / 20) / 11 - (- 136) / (2 * 11 ^ 2)) - (- (177 / 20) / (250 / 23) - (- 136) / (2 *
        (250 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_67)
  have s67: "interval_lebesgue_integrable lborel (ereal 3) (ereal 11) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 11) (\<lambda>x. R_r x / x ^ 3) =
        (742899929809 / 10242872640000)"
    using chain[OF _ _ s66 r67] by (simp add: power2_eq_square power3_eq_cube)
  have r68: "interval_lebesgue_integrable lborel (ereal 11) (ereal (480 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 11) (ereal (480 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- 8 / (480 / 43) - (- 147) / (2 * (480 / 43) ^ 2)) - (- 8 / 11 - (- 147) / (2 * 11 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_68)
  have s68: "interval_lebesgue_integrable lborel (ereal 3) (ereal (480 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (480 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (244140840701 / 3724680960000)"
    using chain[OF _ _ s67 r68] by (simp add: power2_eq_square power3_eq_cube)
  have r69: "interval_lebesgue_integrable lborel (ereal (480 / 43)) (ereal (260 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (480 / 43)) (ereal (260 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (191 / 40) / (260 / 23) - (- 111) / (2 * (260 / 23) ^ 2)) - (- (191 / 40) /
        (480 / 43) - (- 111) / (2 * (480 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_69)
  have s69: "interval_lebesgue_integrable lborel (ereal 3) (ereal (260 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (260 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (45257113067 / 756575820000)"
    using chain[OF _ _ s68 r69] by (simp add: power2_eq_square power3_eq_cube)
  have r70: "interval_lebesgue_integrable lborel (ereal (260 / 23)) (ereal (420 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (260 / 23)) (ereal (420 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (29 / 8) / (420 / 37) - (- 98) / (2 * (420 / 37) ^ 2)) - (- (29 / 8) / (260 /
        23) - (- 98) / (2 * (260 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_70)
  have s70: "interval_lebesgue_integrable lborel (ereal 3) (ereal (420 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (420 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (3374166109 / 58198140000)"
    using chain[OF _ _ s69 r70] by (simp add: power2_eq_square power3_eq_cube)
  have r71: "interval_lebesgue_integrable lborel (ereal (420 / 37)) (ereal (23 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (420 / 37)) (ereal (23 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (219 / 40) / (23 / 2) - (- 119) / (2 * (23 / 2) ^ 2)) - (- (219 / 40) / (420 /
        37) - (- 119) / (2 * (420 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_71)
  have s71: "interval_lebesgue_integrable lborel (ereal 3) (ereal (23 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (23 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (1611729740561 / 30786816060000)"
    using chain[OF _ _ s70 r71] by (simp add: power2_eq_square power3_eq_cube)
  have r72: "interval_lebesgue_integrable lborel (ereal (23 / 2)) (ereal (500 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (23 / 2)) (ereal (500 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (259 / 40) / (500 / 43) - (- 261 / 2) / (2 * (500 / 43) ^ 2)) - (- (259 / 40) /
        (23 / 2) - (- 261 / 2) / (2 * (23 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_72)
  have s72: "interval_lebesgue_integrable lborel (ereal 3) (ereal (500 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (500 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (3195807504629 / 66927861000000)"
    using chain[OF _ _ s71 r72] by (simp add: power2_eq_square power3_eq_cube)
  have r73: "interval_lebesgue_integrable lborel (ereal (500 / 43)) (ereal (270 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (500 / 43)) (ereal (270 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (259 / 40) / (270 / 23) - (- 261 / 2) / (2 * (270 / 23) ^ 2)) - (- (259 / 40) /
        (500 / 43) - (- 261 / 2) / (2 * (500 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_73)
  have s73: "interval_lebesgue_integrable lborel (ereal 3) (ereal (270 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (270 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (529160461763 / 12047014980000)"
    using chain[OF _ _ s72 r73] by (simp add: power2_eq_square power3_eq_cube)
  have r74: "interval_lebesgue_integrable lborel (ereal (270 / 23)) (ereal (440 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (270 / 23)) (ereal (440 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (213 / 40) / (440 / 37) - (- 117) / (2 * (440 / 37) ^ 2)) - (- (213 / 40) /
        (270 / 23) - (- 117) / (2 * (270 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_74)
  have s74: "interval_lebesgue_integrable lborel (ereal 3) (ereal (440 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (440 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (6875944213399 / 176689553040000)"
    using chain[OF _ _ s73 r74] by (simp add: power2_eq_square power3_eq_cube)
  have r75: "interval_lebesgue_integrable lborel (ereal (440 / 37)) (ereal 12) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (440 / 37)) (ereal 12) (\<lambda>x. R_r x / x ^ 3) =
        (- (199 / 20) / 12 - (- 172) / (2 * 12 ^ 2)) - (- (199 / 20) / (440 / 37) - (- 172) / (2 *
        (440 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_75)
  have s75: "interval_lebesgue_integrable lborel (ereal 3) (ereal 12) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 12) (\<lambda>x. R_r x / x ^ 3) =
        (570953551109 / 16062686640000)"
    using chain[OF _ _ s74 r75] by (simp add: power2_eq_square power3_eq_cube)
  have r76: "interval_lebesgue_integrable lborel (ereal 12) (ereal (520 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 12) (ereal (520 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- (91 / 10) / (520 / 43) - (- 184) / (2 * (520 / 43) ^ 2)) - (- (91 / 10) / 12 - (- 184) /
        (2 * 12 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_76)
  have s76: "interval_lebesgue_integrable lborel (ereal 3) (ereal (520 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (520 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (6595922886017 / 208814926320000)"
    using chain[OF _ _ s75 r76] by (simp add: power2_eq_square power3_eq_cube)
  have r77: "interval_lebesgue_integrable lborel (ereal (520 / 43)) (ereal (280 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (520 / 43)) (ereal (280 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (47 / 8) / (280 / 23) - (- 145) / (2 * (280 / 23) ^ 2)) - (- (47 / 8) / (520 /
        43) - (- 145) / (2 * (520 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_77)
  have s77: "interval_lebesgue_integrable lborel (ereal 3) (ereal (280 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (280 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (3176305988663 / 112438806480000)"
    using chain[OF _ _ s76 r77] by (simp add: power2_eq_square power3_eq_cube)
  have r78: "interval_lebesgue_integrable lborel (ereal (280 / 23)) (ereal (460 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (280 / 23)) (ereal (460 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (189 / 40) / (460 / 37) - (- 131) / (2 * (460 / 37) ^ 2)) - (- (189 / 40) /
        (280 / 23) - (- 131) / (2 * (280 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_78)
  have s78: "interval_lebesgue_integrable lborel (ereal 3) (ereal (460 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (460 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (478449408113 / 26388699480000)"
    using chain[OF _ _ s77 r78] by (simp add: power2_eq_square power3_eq_cube)
  have r79: "interval_lebesgue_integrable lborel (ereal (460 / 37)) (ereal (25 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (460 / 37)) (ereal (25 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (263 / 40) / (25 / 2) - (- 154) / (2 * (25 / 2) ^ 2)) - (- (263 / 40) / (460 /
        37) - (- 154) / (2 * (460 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_79)
  have s79: "interval_lebesgue_integrable lborel (ereal 3) (ereal (25 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (25 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (17919605149 / 1147334760000)"
    using chain[OF _ _ s78 r79] by (simp add: power2_eq_square power3_eq_cube)
  have r80: "interval_lebesgue_integrable lborel (ereal (25 / 2)) (ereal (540 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (25 / 2)) (ereal (540 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (303 / 40) / (540 / 43) - (- 333 / 2) / (2 * (540 / 43) ^ 2)) - (- (303 / 40) /
        (25 / 2) - (- 333 / 2) / (2 * (25 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_80)
  have s80: "interval_lebesgue_integrable lborel (ereal 3) (ereal (540 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (540 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (11618575517 / 860501070000)"
    using chain[OF _ _ s79 r80] by (simp add: power2_eq_square power3_eq_cube)
  have r81: "interval_lebesgue_integrable lborel (ereal (540 / 43)) (ereal (290 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (540 / 43)) (ereal (290 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (303 / 40) / (290 / 23) - (- 333 / 2) / (2 * (290 / 23) ^ 2)) - (- (303 / 40) /
        (540 / 43) - (- 333 / 2) / (2 * (540 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_81)
  have s81: "interval_lebesgue_integrable lborel (ereal 3) (ereal (290 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (290 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (11285560024021 / 964908533160000)"
    using chain[OF _ _ s80 r81] by (simp add: power2_eq_square power3_eq_cube)
  have r82: "interval_lebesgue_integrable lborel (ereal (290 / 23)) (ereal (480 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (290 / 23)) (ereal (480 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (257 / 40) / (480 / 37) - (- 152) / (2 * (480 / 37) ^ 2)) - (- (257 / 40) /
        (290 / 23) - (- 152) / (2 * (290 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_82)
  have s82: "interval_lebesgue_integrable lborel (ereal 3) (ereal (480 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (480 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (- 3872453569 / 8318177010000)"
    using chain[OF _ _ s81 r82] by (simp add: power2_eq_square power3_eq_cube)
  have r83: "interval_lebesgue_integrable lborel (ereal (480 / 37)) (ereal 13) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (480 / 37)) (ereal 13) (\<lambda>x. R_r x / x ^ 3) =
        (- (221 / 20) / 13 - (- 212) / (2 * 13 ^ 2)) - (- (221 / 20) / (480 / 37) - (- 212) / (2 *
        (480 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_83)
  have s83: "interval_lebesgue_integrable lborel (ereal 3) (ereal 13) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 13) (\<lambda>x. R_r x / x ^ 3) =
        (- 4535988527729 / 3460361636160000)"
    using chain[OF _ _ s82 r83] by (simp add: power2_eq_square power3_eq_cube)
  have r84: "interval_lebesgue_integrable lborel (ereal 13) (ereal (560 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 13) (ereal (560 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- (51 / 5) / (560 / 43) - (- 225) / (2 * (560 / 43) ^ 2)) - (- (51 / 5) / 13 - (- 225) /
        (2 * 13 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_84)
  have s84: "interval_lebesgue_integrable lborel (ereal 3) (ereal (560 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (560 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- 1862730944387 / 815181346980000)"
    using chain[OF _ _ s83 r84] by (simp add: power2_eq_square power3_eq_cube)
  have r85: "interval_lebesgue_integrable lborel (ereal (560 / 43)) (ereal (300 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (560 / 43)) (ereal (300 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (279 / 40) / (300 / 23) - (- 183) / (2 * (300 / 23) ^ 2)) - (- (279 / 40) /
        (560 / 43) - (- 183) / (2 * (560 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_85)
  have s85: "interval_lebesgue_integrable lborel (ereal 3) (ereal (300 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (300 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (- 1165002666109 / 372654330048000)"
    using chain[OF _ _ s84 r85] by (simp add: power2_eq_square power3_eq_cube)
  have r86: "interval_lebesgue_integrable lborel (ereal (300 / 23)) (ereal (40 /
    3)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (300 / 23)) (ereal (40 / 3)) (\<lambda>x. R_r x /
        x ^ 3) = (- (233 / 40) / (40 / 3) - (- 168) / (2 * (40 / 3) ^ 2)) - (- (233 / 40) / (300 /
        23) - (- 168) / (2 * (300 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_86)
  have s86: "interval_lebesgue_integrable lborel (ereal 3) (ereal (40 / 3)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (40 / 3)) (\<lambda>x. R_r x / x ^ 3) =
        (- 27299219099561 / 1863271650240000)"
    using chain[OF _ _ s85 r86] by (simp add: power2_eq_square power3_eq_cube)
  have r87: "interval_lebesgue_integrable lborel (ereal (40 / 3)) (ereal (310 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (40 / 3)) (ereal (310 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (145 / 8) / (310 / 23) - (- 184) / (2 * (310 / 23) ^ 2)) - (- (145 / 8) / (40 /
        3) - (- 184) / (2 * (40 / 3) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_87)
  have s87: "interval_lebesgue_integrable lborel (ereal 3) (ereal (310 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (310 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (- 19881957772141121 / 1790604055880640000)"
    using chain[OF _ _ s86 r87] by (simp add: power2_eq_square power3_eq_cube)
  have r88: "interval_lebesgue_integrable lborel (ereal (310 / 23)) (ereal (580 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (310 / 23)) (ereal (580 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (679 / 40) / (580 / 43) - (- 337 / 2) / (2 * (580 / 43) ^ 2)) - (- (679 / 40) /
        (310 / 23) - (- 337 / 2) / (2 * (310 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_88)
  have s88: "interval_lebesgue_integrable lborel (ereal 3) (ereal (580 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (580 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- 18182057508830539 / 1675081213565760000)"
    using chain[OF _ _ s87 r88] by (simp add: power2_eq_square power3_eq_cube)
  have r89: "interval_lebesgue_integrable lborel (ereal (580 / 43)) (ereal (27 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (580 / 43)) (ereal (27 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (679 / 40) / (27 / 2) - (- 337 / 2) / (2 * (27 / 2) ^ 2)) - (- (679 / 40) /
        (580 / 43) - (- 337 / 2) / (2 * (580 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_89)
  have s89: "interval_lebesgue_integrable lborel (ereal 3) (ereal (27 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (27 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (- 16481154814890757 / 1559558371250880000)"
    using chain[OF _ _ s88 r89] by (simp add: power2_eq_square power3_eq_cube)
  have r90: "interval_lebesgue_integrable lborel (ereal (27 / 2)) (ereal (500 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (27 / 2)) (ereal (500 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (719 / 40) / (500 / 37) - (- 182) / (2 * (500 / 37) ^ 2)) - (- (719 / 40) /
        (27 / 2) - (- 182) / (2 * (27 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_90)
  have s90: "interval_lebesgue_integrable lborel (ereal 3) (ereal (500 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (500 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (- 547368726821237 / 53482797368000000)"
    using chain[OF _ _ s89 r90] by (simp add: power2_eq_square power3_eq_cube)
  have r91: "interval_lebesgue_integrable lborel (ereal (500 / 37)) (ereal (320 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (500 / 37)) (ereal (320 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (793 / 40) / (320 / 23) - (- 207) / (2 * (320 / 23) ^ 2)) - (- (793 / 40) /
        (500 / 37) - (- 207) / (2 * (500 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_91)
  have s91: "interval_lebesgue_integrable lborel (ereal 3) (ereal (320 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (320 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (- 6494602107759 / 34228990315520000)"
    using chain[OF _ _ s90 r91] by (simp add: power2_eq_square power3_eq_cube)
  have r92: "interval_lebesgue_integrable lborel (ereal (320 / 23)) (ereal (600 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (320 / 23)) (ereal (600 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (747 / 40) / (600 / 43) - (- 191) / (2 * (600 / 43) ^ 2)) - (- (747 / 40) /
        (320 / 23) - (- 191) / (2 * (320 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_92)
  have s92: "interval_lebesgue_integrable lborel (ereal 3) (ereal (600 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (600 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (6355291472 / 7521018379875)"
    using chain[OF _ _ s91 r92] by (simp add: power2_eq_square power3_eq_cube)
  have r93: "interval_lebesgue_integrable lborel (ereal (600 / 43)) (ereal 14) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (600 / 43)) (ereal 14) (\<lambda>x. R_r x / x ^ 3) =
        (- (309 / 20) / 14 - (- 146) / (2 * 14 ^ 2)) - (- (309 / 20) / (600 / 43) - (- 146) / (2 *
        (600 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_93)
  have s93: "interval_lebesgue_integrable lborel (ereal 3) (ereal 14) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 14) (\<lambda>x. R_r x / x ^ 3) =
        (3812015306609 / 1871897907880000)"
    using chain[OF _ _ s92 r93] by (simp add: power2_eq_square power3_eq_cube)
  have r94: "interval_lebesgue_integrable lborel (ereal 14) (ereal (520 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 14) (ereal (520 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (- (73 / 5) / (520 / 37) - (- 160) / (2 * (520 / 37) ^ 2)) - (- (73 / 5) / 14 - (- 160) /
        (2 * 14 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_94)
  have s94: "interval_lebesgue_integrable lborel (ereal 3) (ereal (520 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (520 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (10129319814931 / 3476381828920000)"
    using chain[OF _ _ s93 r94] by (simp add: power2_eq_square power3_eq_cube)
  have r95: "interval_lebesgue_integrable lborel (ereal (520 / 37)) (ereal (330 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (520 / 37)) (ereal (330 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (769 / 40) / (330 / 23) - (- 225) / (2 * (330 / 23) ^ 2)) - (- (769 / 40) /
        (520 / 37) - (- 225) / (2 * (520 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_95)
  have s95: "interval_lebesgue_integrable lborel (ereal 3) (ereal (330 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (330 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (138316892681717 / 17649323131440000)"
    using chain[OF _ _ s94 r95] by (simp add: power2_eq_square power3_eq_cube)
  have r96: "interval_lebesgue_integrable lborel (ereal (330 / 23)) (ereal (620 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (330 / 23)) (ereal (620 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (723 / 40) / (620 / 43) - (- 417 / 2) / (2 * (620 / 43) ^ 2)) - (- (723 / 40) /
        (330 / 23) - (- 417 / 2) / (2 * (330 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_96)
  have s96: "interval_lebesgue_integrable lborel (ereal 3) (ereal (620 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (620 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (40973121188137 / 4521727413840000)"
    using chain[OF _ _ s95 r96] by (simp add: power2_eq_square power3_eq_cube)
  have r97: "interval_lebesgue_integrable lborel (ereal (620 / 43)) (ereal (29 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (620 / 43)) (ereal (29 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (723 / 40) / (29 / 2) - (- 417 / 2) / (2 * (29 / 2) ^ 2)) - (- (723 / 40) /
        (620 / 43) - (- 417 / 2) / (2 * (620 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_97)
  have s97: "interval_lebesgue_integrable lborel (ereal 3) (ereal (29 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (29 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (44349030780233 / 4230003064560000)"
    using chain[OF _ _ s96 r97] by (simp add: power2_eq_square power3_eq_cube)
  have r98: "interval_lebesgue_integrable lborel (ereal (29 / 2)) (ereal (540 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (29 / 2)) (ereal (540 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (763 / 40) / (540 / 37) - (- 223) / (2 * (540 / 37) ^ 2)) - (- (763 / 40) /
        (29 / 2) - (- 223) / (2 * (29 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_98)
  have s98: "interval_lebesgue_integrable lborel (ereal 3) (ereal (540 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (540 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (430957159001711 / 35444508437520000)"
    using chain[OF _ _ s97 r98] by (simp add: power2_eq_square power3_eq_cube)
  have r99: "interval_lebesgue_integrable lborel (ereal (540 / 37)) (ereal (340 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (540 / 37)) (ereal (340 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (837 / 40) / (340 / 23) - (- 250) / (2 * (340 / 23) ^ 2)) - (- (837 / 40) /
        (540 / 37) - (- 250) / (2 * (540 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_99)
  have s99: "interval_lebesgue_integrable lborel (ereal 3) (ereal (340 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (340 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (347275409950381 / 22316912719920000)"
    using chain[OF _ _ s98 r99] by (simp add: power2_eq_square power3_eq_cube)
  have r100: "interval_lebesgue_integrable lborel (ereal (340 / 23)) (ereal (640 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (340 / 23)) (ereal (640 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (791 / 40) / (640 / 43) - (- 233) / (2 * (640 / 43) ^ 2)) - (- (791 / 40) /
        (340 / 23) - (- 233) / (2 * (340 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_100)
  have s100: "interval_lebesgue_integrable lborel (ereal 3) (ereal (640 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (640 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (5857641039199583 / 336066450370560000)"
    using chain[OF _ _ s99 r100] by (simp add: power2_eq_square power3_eq_cube)
  have r101: "interval_lebesgue_integrable lborel (ereal (640 / 43)) (ereal 15) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (640 / 43)) (ereal 15) (\<lambda>x. R_r x / x ^ 3) =
        (- (331 / 20) / 15 - (- 185) / (2 * 15 ^ 2)) - (- (331 / 20) / (640 / 43) - (- 185) / (2 *
        (640 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_101)
  have s101: "interval_lebesgue_integrable lborel (ereal 3) (ereal 15) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 15) (\<lambda>x. R_r x / x ^ 3) =
        (411704436619163 / 21004153148160000)"
    using chain[OF _ _ s100 r101] by (simp add: power2_eq_square power3_eq_cube)
  have r102: "interval_lebesgue_integrable lborel (ereal 15) (ereal (560 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 15) (ereal (560 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (- (157 / 10) / (560 / 37) - (- 200) / (2 * (560 / 37) ^ 2)) - (- (157 / 10) / 15 -
        (- 200) / (2 * 15 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_102)
  have s102: "interval_lebesgue_integrable lborel (ereal 3) (ereal (560 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (560 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (3094264707702941 / 147029072037120000)"
    using chain[OF _ _ s101 r102] by (simp add: power2_eq_square power3_eq_cube)
  have r103: "interval_lebesgue_integrable lborel (ereal (560 / 37)) (ereal (350 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (560 / 37)) (ereal (350 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (813 / 40) / (350 / 23) - (- 270) / (2 * (350 / 23) ^ 2)) - (- (813 / 40) /
        (560 / 37) - (- 270) / (2 * (560 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_103)
  have s103: "interval_lebesgue_integrable lborel (ereal 3) (ereal (350 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (350 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (3227322267154901 / 147029072037120000)"
    using chain[OF _ _ s102 r103] by (simp add: power2_eq_square power3_eq_cube)
  have r104: "interval_lebesgue_integrable lborel (ereal (350 / 23)) (ereal (660 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (350 / 23)) (ereal (660 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (767 / 40) / (660 / 43) - (- 505 / 2) / (2 * (660 / 43) ^ 2)) - (- (767 / 40) /
        (350 / 23) - (- 505 / 2) / (2 * (350 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_104)
  have s104: "interval_lebesgue_integrable lborel (ereal 3) (ereal (660 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (660 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (59581386442537163 / 2541502530927360000)"
    using chain[OF _ _ s103 r104] by (simp add: power2_eq_square power3_eq_cube)
  have r105: "interval_lebesgue_integrable lborel (ereal (660 / 43)) (ereal (31 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (660 / 43)) (ereal (31 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (767 / 40) / (31 / 2) - (- 505 / 2) / (2 * (31 / 2) ^ 2)) - (- (767 / 40) /
        (660 / 43) - (- 505 / 2) / (2 * (660 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_105)
  have s105: "interval_lebesgue_integrable lborel (ereal 3) (ereal (31 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (31 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (16424908746219293 / 651128747592960000)"
    using chain[OF _ _ s104 r105] by (simp add: power2_eq_square power3_eq_cube)
  have r106: "interval_lebesgue_integrable lborel (ereal (31 / 2)) (ereal (360 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (31 / 2)) (ereal (360 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (807 / 40) / (360 / 23) - (- 268) / (2 * (360 / 23) ^ 2)) - (- (807 / 40) /
        (31 / 2) - (- 268) / (2 * (31 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_106)
  have s106: "interval_lebesgue_integrable lborel (ereal 3) (ereal (360 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (360 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (1706843121663209 / 63012459444480000)"
    using chain[OF _ _ s105 r106] by (simp add: power2_eq_square power3_eq_cube)
  have r107: "interval_lebesgue_integrable lborel (ereal (360 / 23)) (ereal (580 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (360 / 23)) (ereal (580 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (761 / 40) / (580 / 37) - (- 250) / (2 * (580 / 37) ^ 2)) - (- (761 / 40) /
        (360 / 23) - (- 250) / (2 * (360 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_107)
  have s107: "interval_lebesgue_integrable lborel (ereal 3) (ereal (580 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (580 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (16678296005188087 / 609120441296640000)"
    using chain[OF _ _ s106 r107] by (simp add: power2_eq_square power3_eq_cube)
  have r108: "interval_lebesgue_integrable lborel (ereal (580 / 37)) (ereal (680 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (580 / 37)) (ereal (680 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (167 / 8) / (680 / 43) - (- 279) / (2 * (680 / 43) ^ 2)) - (- (167 / 8) / (580 /
        37) - (- 279) / (2 * (580 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_108)
  have s108: "interval_lebesgue_integrable lborel (ereal 3) (ereal (680 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (680 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (10405244655250051 / 357070603518720000)"
    using chain[OF _ _ s107 r108] by (simp add: power2_eq_square power3_eq_cube)
  have r109: "interval_lebesgue_integrable lborel (ereal (680 / 43)) (ereal 16) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (680 / 43)) (ereal 16) (\<lambda>x. R_r x / x ^ 3) =
        (- (353 / 20) / 16 - (- 228) / (2 * 16 ^ 2)) - (- (353 / 20) / (680 / 43) - (- 228) / (2 *
        (680 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_109)
  have s109: "interval_lebesgue_integrable lborel (ereal 3) (ereal 16) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 16) (\<lambda>x. R_r x / x ^ 3) =
        (663289007996003 / 21004153148160000)"
    using chain[OF _ _ s108 r109] by (simp add: power2_eq_square power3_eq_cube)
  have r110: "interval_lebesgue_integrable lborel (ereal 16) (ereal (370 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 16) (ereal (370 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (- (84 / 5) / (370 / 23) - (- 244) / (2 * (370 / 23) ^ 2)) - (- (84 / 5) / 16 - (- 244) /
        (2 * 16 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_110)
  have s110: "interval_lebesgue_integrable lborel (ereal 3) (ereal (370 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (370 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (923500395904002107 / 28754685659831040000)"
    using chain[OF _ _ s109 r110] by (simp add: power2_eq_square power3_eq_cube)
  have r111: "interval_lebesgue_integrable lborel (ereal (370 / 23)) (ereal (600 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (370 / 23)) (ereal (600 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (313 / 20) / (600 / 37) - (- 451 / 2) / (2 * (600 / 37) ^ 2)) - (- (313 / 20) /
        (370 / 23) - (- 451 / 2) / (2 * (370 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_111)
  have s111: "interval_lebesgue_integrable lborel (ereal 3) (ereal (600 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (600 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (25609594035043943 / 777153666481920000)"
    using chain[OF _ _ s110 r111] by (simp add: power2_eq_square power3_eq_cube)
  have r112: "interval_lebesgue_integrable lborel (ereal (600 / 37)) (ereal (700 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (600 / 37)) (ereal (700 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (811 / 40) / (700 / 43) - (- 601 / 2) / (2 * (700 / 43) ^ 2)) - (- (811 / 40) /
        (600 / 37) - (- 601 / 2) / (2 * (600 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_112)
  have s112: "interval_lebesgue_integrable lborel (ereal 3) (ereal (700 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (700 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (181572637023959273 / 5440075665373440000)"
    using chain[OF _ _ s111 r112] by (simp add: power2_eq_square power3_eq_cube)
  have r113: "interval_lebesgue_integrable lborel (ereal (700 / 43)) (ereal (33 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (700 / 43)) (ereal (33 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (811 / 40) / (33 / 2) - (- 601 / 2) / (2 * (33 / 2) ^ 2)) - (- (811 / 40) /
        (700 / 43) - (- 601 / 2) / (2 * (700 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_113)
  have s113: "interval_lebesgue_integrable lborel (ereal 3) (ereal (33 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (33 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (3288608185470880631 / 94035593644312320000)"
    using chain[OF _ _ s112 r113] by (simp add: power2_eq_square power3_eq_cube)
  have r114: "interval_lebesgue_integrable lborel (ereal (33 / 2)) (ereal (380 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (33 / 2)) (ereal (380 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (851 / 40) / (380 / 23) - (- 317) / (2 * (380 / 23) ^ 2)) - (- (851 / 40) /
        (33 / 2) - (- 317) / (2 * (33 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_114)
  have s114: "interval_lebesgue_integrable lborel (ereal 3) (ereal (380 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (380 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (5707206507596333599 / 162425116294721280000)"
    using chain[OF _ _ s113 r114] by (simp add: power2_eq_square power3_eq_cube)
  have r115: "interval_lebesgue_integrable lborel (ereal (380 / 23)) (ereal (50 /
    3)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (380 / 23)) (ereal (50 / 3)) (\<lambda>x. R_r x /
        x ^ 3) = (- (161 / 8) / (50 / 3) - (- 298) / (2 * (50 / 3) ^ 2)) - (- (161 / 8) / (380 /
        23) - (- 298) / (2 * (380 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_115)
  have s115: "interval_lebesgue_integrable lborel (ereal 3) (ereal (50 / 3)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (50 / 3)) (\<lambda>x. R_r x / x ^ 3) =
        (310127401715264389 / 8548690331301120000)"
    using chain[OF _ _ s114 r115] by (simp add: power2_eq_square power3_eq_cube)
  have r116: "interval_lebesgue_integrable lborel (ereal (50 / 3)) (ereal (720 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (50 / 3)) (ereal (720 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (799 / 40) / (720 / 43) - (- 591 / 2) / (2 * (720 / 43) ^ 2)) - (- (799 / 40) /
        (50 / 3) - (- 591 / 2) / (2 * (50 / 3) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_116)
  have s116: "interval_lebesgue_integrable lborel (ereal 3) (ereal (720 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (720 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (315555919018815731 / 8548690331301120000)"
    using chain[OF _ _ s115 r116] by (simp add: power2_eq_square power3_eq_cube)
  have r117: "interval_lebesgue_integrable lborel (ereal (720 / 43)) (ereal (620 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (720 / 43)) (ereal (620 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (67 / 4) / (620 / 37) - (- 483 / 2) / (2 * (620 / 37) ^ 2)) - (- (67 / 4) /
        (720 / 43) - (- 483 / 2) / (2 * (720 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_117)
  have s117: "interval_lebesgue_integrable lborel (ereal 3) (ereal (620 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (620 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (9809927604509515411 / 265009400270334720000)"
    using chain[OF _ _ s116 r117] by (simp add: power2_eq_square power3_eq_cube)
  have r118: "interval_lebesgue_integrable lborel (ereal (620 / 37)) (ereal (390 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (620 / 37)) (ereal (390 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (93 / 5) / (390 / 23) - (- 545 / 2) / (2 * (390 / 23) ^ 2)) - (- (93 / 5) /
        (620 / 37) - (- 545 / 2) / (2 * (620 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_118)
  have s118: "interval_lebesgue_integrable lborel (ereal 3) (ereal (390 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (390 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (4303992980933782153 / 111132974306914560000)"
    using chain[OF _ _ s117 r118] by (simp add: power2_eq_square power3_eq_cube)
  have r119: "interval_lebesgue_integrable lborel (ereal (390 / 23)) (ereal 17) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (390 / 23)) (ereal 17) (\<lambda>x. R_r x / x ^ 3) =
        (- (349 / 20) / 17 - (- 253) / (2 * 17 ^ 2)) - (- (349 / 20) / (390 / 23) - (- 253) / (2 *
        (390 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_119)
  have s119: "interval_lebesgue_integrable lborel (ereal 3) (ereal 17) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 17) (\<lambda>x. R_r x / x ^ 3) =
        (5684162388119036477 / 145327735632119040000)"
    using chain[OF _ _ s118 r119] by (simp add: power2_eq_square power3_eq_cube)
  have r120: "interval_lebesgue_integrable lborel (ereal 17) (ereal (740 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 17) (ereal (740 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- (83 / 5) / (740 / 43) - (- 270) / (2 * (740 / 43) ^ 2)) - (- (83 / 5) / 17 - (- 270) /
        (2 * 17 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_120)
  have s120: "interval_lebesgue_integrable lborel (ereal 3) (ereal (740 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (740 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (12555663195326239297 / 316301542258141440000)"
    using chain[OF _ _ s119 r120] by (simp add: power2_eq_square power3_eq_cube)
  have r121: "interval_lebesgue_integrable lborel (ereal (740 / 43)) (ereal (640 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (740 / 43)) (ereal (640 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (83 / 5) / (640 / 37) - (- 270) / (2 * (640 / 37) ^ 2)) - (- (83 / 5) / (740 /
        43) - (- 270) / (2 * (740 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_121)
  have s121: "interval_lebesgue_integrable lborel (ereal 3) (ereal (640 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (640 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (2733958174246260623 / 68389522650408960000)"
    using chain[OF _ _ s120 r121] by (simp add: power2_eq_square power3_eq_cube)
  have r122: "interval_lebesgue_integrable lborel (ereal (640 / 37)) (ereal (400 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (640 / 37)) (ereal (400 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (849 / 40) / (400 / 23) - (- 350) / (2 * (400 / 23) ^ 2)) - (- (849 / 40) /
        (640 / 37) - (- 350) / (2 * (640 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_122)
  have s122: "interval_lebesgue_integrable lborel (ereal 3) (ereal (400 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (400 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (172268644150069133 / 4274345165650560000)"
    using chain[OF _ _ s121 r122] by (simp add: power2_eq_square power3_eq_cube)
  have r123: "interval_lebesgue_integrable lborel (ereal (400 / 23)) (ereal (35 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (400 / 23)) (ereal (35 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (803 / 40) / (35 / 2) - (- 330) / (2 * (35 / 2) ^ 2)) - (- (803 / 40) / (400 /
        23) - (- 330) / (2 * (400 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_123)
  have s123: "interval_lebesgue_integrable lborel (ereal 3) (ereal (35 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (35 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (1218264660892033991 / 29920416159553920000)"
    using chain[OF _ _ s122 r123] by (simp add: power2_eq_square power3_eq_cube)
  have r124: "interval_lebesgue_integrable lborel (ereal (35 / 2)) (ereal (760 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (35 / 2)) (ereal (760 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (843 / 40) / (760 / 43) - (- 695 / 2) / (2 * (760 / 43) ^ 2)) - (- (843 / 40) /
        (35 / 2) - (- 695 / 2) / (2 * (35 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_124)
  have s124: "interval_lebesgue_integrable lborel (ereal 3) (ereal (760 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (760 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (3366979142827744247 / 81212558147360640000)"
    using chain[OF _ _ s123 r124] by (simp add: power2_eq_square power3_eq_cube)
  have r125: "interval_lebesgue_integrable lborel (ereal (760 / 43)) (ereal (410 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (760 / 43)) (ereal (410 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (357 / 20) / (410 / 23) - (- 581 / 2) / (2 * (410 / 23) ^ 2)) - (- (357 / 20) /
        (760 / 43) - (- 581 / 2) / (2 * (760 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_125)
  have s125: "interval_lebesgue_integrable lborel (ereal 3) (ereal (410 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (410 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (303021066443711433353 / 7185174223458591360000)"
    using chain[OF _ _ s124 r125] by (simp add: power2_eq_square power3_eq_cube)
  have r126: "interval_lebesgue_integrable lborel (ereal (410 / 23)) (ereal (660 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (410 / 23)) (ereal (660 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (167 / 10) / (660 / 37) - (- 270) / (2 * (660 / 37) ^ 2)) - (- (167 / 10) /
        (410 / 23) - (- 270) / (2 * (410 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_126)
  have s126: "interval_lebesgue_integrable lborel (ereal 3) (ereal (660 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (660 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (81409371519421251563 / 1927729669708402560000)"
    using chain[OF _ _ s125 r126] by (simp add: power2_eq_square power3_eq_cube)
  have r127: "interval_lebesgue_integrable lborel (ereal (660 / 37)) (ereal 18) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (660 / 37)) (ereal 18) (\<lambda>x. R_r x / x ^ 3) =
        (- (371 / 20) / 18 - (- 303) / (2 * 18 ^ 2)) - (- (371 / 20) / (660 / 37) - (- 303) / (2 *
        (660 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_127)
  have s127: "interval_lebesgue_integrable lborel (ereal 3) (ereal 18) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 18) (\<lambda>x. R_r x / x ^ 3) =
        (2515340133869434411 / 58416050597224320000)"
    using chain[OF _ _ s126 r127] by (simp add: power2_eq_square power3_eq_cube)
  have r128: "interval_lebesgue_integrable lborel (ereal 18) (ereal (780 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 18) (ereal (780 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- (177 / 10) / (780 / 43) - (- 321) / (2 * (780 / 43) ^ 2)) - (- (177 / 10) / 18 -
        (- 321) / (2 * 18 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_128)
  have s128: "interval_lebesgue_integrable lborel (ereal 3) (ereal (780 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (780 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (98035230807336150829 / 2278225973291748480000)"
    using chain[OF _ _ s127 r128] by (simp add: power2_eq_square power3_eq_cube)
  have r129: "interval_lebesgue_integrable lborel (ereal (780 / 43)) (ereal (420 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (780 / 43)) (ereal (420 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (177 / 10) / (420 / 23) - (- 321) / (2 * (420 / 23) ^ 2)) - (- (177 / 10) /
        (780 / 43) - (- 321) / (2 * (780 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_129)
  have s129: "interval_lebesgue_integrable lborel (ereal 3) (ereal (420 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (420 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (52816347568143318631 / 1226737062541710720000)"
    using chain[OF _ _ s128 r129] by (simp add: power2_eq_square power3_eq_cube)
  have r130: "interval_lebesgue_integrable lborel (ereal (420 / 23)) (ereal (680 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (420 / 23)) (ereal (680 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (331 / 20) / (680 / 37) - (- 300) / (2 * (680 / 37) ^ 2)) - (- (331 / 20) /
        (420 / 23) - (- 300) / (2 * (420 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_130)
  have s130: "interval_lebesgue_integrable lborel (ereal 3) (ereal (680 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (680 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (128449727084362846961 / 2979218580458440320000)"
    using chain[OF _ _ s129 r130] by (simp add: power2_eq_square power3_eq_cube)
  have r131: "interval_lebesgue_integrable lborel (ereal (680 / 37)) (ereal (37 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (680 / 37)) (ereal (37 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (847 / 40) / (37 / 2) - (- 385) / (2 * (37 / 2) ^ 2)) - (- (847 / 40) / (680 /
        37) - (- 385) / (2 * (680 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_131)
  have s131: "interval_lebesgue_integrable lborel (ereal 3) (ereal (37 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (37 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (280252059175511707021 / 6484181616291899520000)"
    using chain[OF _ _ s130 r131] by (simp add: power2_eq_square power3_eq_cube)
  have r132: "interval_lebesgue_integrable lborel (ereal (37 / 2)) (ereal (800 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (37 / 2)) (ereal (800 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (887 / 40) / (800 / 43) - (- 807 / 2) / (2 * (800 / 43) ^ 2)) - (- (887 / 40) /
        (37 / 2) - (- 807 / 2) / (2 * (37 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_132)
  have s132: "interval_lebesgue_integrable lborel (ereal 3) (ereal (800 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (800 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (30388217670048789739 / 700992607166691840000)"
    using chain[OF _ _ s131 r132] by (simp add: power2_eq_square power3_eq_cube)
  have r133: "interval_lebesgue_integrable lborel (ereal (800 / 43)) (ereal (430 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (800 / 43)) (ereal (430 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (379 / 20) / (430 / 23) - (- 687 / 2) / (2 * (430 / 23) ^ 2)) - (- (379 / 20) /
        (800 / 43) - (- 687 / 2) / (2 * (800 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_133)
  have s133: "interval_lebesgue_integrable lborel (ereal 3) (ereal (430 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (430 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (14092038464086667615347 / 324033832662803303040000)"
    using chain[OF _ _ s132 r133] by (simp add: power2_eq_square power3_eq_cube)
  have r134: "interval_lebesgue_integrable lborel (ereal (430 / 23)) (ereal (700 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (430 / 23)) (ereal (700 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (89 / 5) / (700 / 37) - (- 322) / (2 * (700 / 37) ^ 2)) - (- (89 / 5) / (430 /
        23) - (- 322) / (2 * (430 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_134)
  have s134: "interval_lebesgue_integrable lborel (ereal 3) (ereal (700 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (700 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (330948661396284592537 / 7535670527041937280000)"
    using chain[OF _ _ s133 r134] by (simp add: power2_eq_square power3_eq_cube)
  have r135: "interval_lebesgue_integrable lborel (ereal (700 / 37)) (ereal 19) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (700 / 37)) (ereal 19) (\<lambda>x. R_r x / x ^ 3) =
        (- (393 / 20) / 19 - (- 357) / (2 * 19 ^ 2)) - (- (393 / 20) / (700 / 37) - (- 357) / (2 *
        (700 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_135)
  have s135: "interval_lebesgue_integrable lborel (ereal 3) (ereal 19) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 19) (\<lambda>x. R_r x / x ^ 3) =
        (6314515564686688895611 / 143177740013796808320000)"
    using chain[OF _ _ s134 r135] by (simp add: power2_eq_square power3_eq_cube)
  have r136: "interval_lebesgue_integrable lborel (ereal 19) (ereal (820 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 19) (ereal (820 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (- (94 / 5) / (820 / 43) - (- 376) / (2 * (820 / 43) ^ 2)) - (- (94 / 5) / 19 - (- 376) /
        (2 * 19 ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_136)
  have s136: "interval_lebesgue_integrable lborel (ereal 3) (ereal (820 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (820 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (13569347630600699631329 / 308962491608719428480000)"
    using chain[OF _ _ s135 r136] by (simp add: power2_eq_square power3_eq_cube)
  have r137: "interval_lebesgue_integrable lborel (ereal (820 / 43)) (ereal (440 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (820 / 43)) (ereal (440 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (94 / 5) / (440 / 23) - (- 376) / (2 * (440 / 23) ^ 2)) - (- (94 / 5) / (820 /
        43) - (- 376) / (2 * (820 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_137)
  have s137: "interval_lebesgue_integrable lborel (ereal 3) (ereal (440 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (440 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (3628346009801718502259 / 82892375797461310080000)"
    using chain[OF _ _ s136 r137] by (simp add: power2_eq_square power3_eq_cube)
  have r138: "interval_lebesgue_integrable lborel (ereal (440 / 23)) (ereal (720 /
    37)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (440 / 23)) (ereal (720 / 37)) (\<lambda>x. R_r x /
        x ^ 3) = (- (353 / 20) / (720 / 37) - (- 354) / (2 * (720 / 37) ^ 2)) - (- (353 / 20) /
        (440 / 23) - (- 354) / (2 * (440 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_138)
  have s138: "interval_lebesgue_integrable lborel (ereal 3) (ereal (720 / 37)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (720 / 37)) (\<lambda>x. R_r x / x ^ 3) =
        (325200031085559118469 / 7535670527041937280000)"
    using chain[OF _ _ s137 r138] by (simp add: power2_eq_square power3_eq_cube)
  have r139: "interval_lebesgue_integrable lborel (ereal (720 / 37)) (ereal (39 /
    2)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (720 / 37)) (ereal (39 / 2)) (\<lambda>x. R_r x /
        x ^ 3) = (- (891 / 40) / (39 / 2) - (- 444) / (2 * (39 / 2) ^ 2)) - (- (891 / 40) / (720 /
        37) - (- 444) / (2 * (720 / 37) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_139)
  have s139: "interval_lebesgue_integrable lborel (ereal 3) (ereal (39 / 2)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (39 / 2)) (\<lambda>x. R_r x / x ^ 3) =
        (4222179444545094496897 / 97963716851545184640000)"
    using chain[OF _ _ s138 r139] by (simp add: power2_eq_square power3_eq_cube)
  have r140: "interval_lebesgue_integrable lborel (ereal (39 / 2)) (ereal (840 /
    43)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (39 / 2)) (ereal (840 / 43)) (\<lambda>x. R_r x /
        x ^ 3) = (- (931 / 40) / (840 / 43) - (- 927 / 2) / (2 * (840 / 43) ^ 2)) - (- (931 / 40) /
        (39 / 2) - (- 927 / 2) / (2 * (39 / 2) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_140)
  have s140: "interval_lebesgue_integrable lborel (ereal 3) (ereal (840 / 43)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (840 / 43)) (\<lambda>x. R_r x / x ^ 3) =
        (2271196345609880684383 / 52749693689293560960000)"
    using chain[OF _ _ s139 r140] by (simp add: power2_eq_square power3_eq_cube)
  have r141: "interval_lebesgue_integrable lborel (ereal (840 / 43)) (ereal (450 /
    23)) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (840 / 43)) (ereal (450 / 23)) (\<lambda>x. R_r x /
        x ^ 3) = (- (401 / 20) / (450 / 23) - (- 801 / 2) / (2 * (450 / 23) ^ 2)) - (- (401 / 20) /
        (840 / 43) - (- 801 / 2) / (2 * (840 / 43) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_141)
  have s141: "interval_lebesgue_integrable lborel (ereal 3) (ereal (450 / 23)) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal (450 / 23)) (\<lambda>x. R_r x / x ^ 3) =
        (324195926757243309661 / 7535670527041937280000)"
    using chain[OF _ _ s140 r141] by (simp add: power2_eq_square power3_eq_cube)
  have r142: "interval_lebesgue_integrable lborel (ereal (450 / 23)) (ereal 20) (\<lambda>x. R_r x /
    x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal (450 / 23)) (ereal 20) (\<lambda>x. R_r x / x ^ 3) =
        (- (189 / 10) / 20 - (- 378) / (2 * 20 ^ 2)) - (- (189 / 10) / (450 / 23) - (- 378) / (2 *
        (450 / 23) ^ 2))"
    by (rule piece_rat) (simp_all add: inner_piece_142)
  have "interval_lebesgue_integrable lborel (ereal 3) (ereal 20) (\<lambda>x. R_r x / x ^ 3) \<and>
      interval_lebesgue_integral lborel (ereal 3) (ereal 20) (\<lambda>x. R_r x / x ^ 3) =
        (322437603634266857629 / 7535670527041937280000)"
    using chain[OF _ _ s141 r142] by (simp add: power2_eq_square power3_eq_cube)
  thus ?thesis by simp
qed


subsection \<open>Integrability on @{text "[3, \<infinity>)"} and the tails (5.14)-(5.17)\<close>

text \<open>The exceptional set @{text "S = \<int> \<union> (40/3)\<int>"} where the fractional
  parts jump.\<close>
definition Sx :: "real set" where "Sx = {x. x \<in> \<int> \<or> alpha_r * x \<in> \<int>}"

text \<open>(5.15): @{text "\<Phi>(x) = (P(x) - 2923/240)/x^2 + \<lambda>/x + 2C(x)/x^3"}.\<close>
definition Phi :: "real \<Rightarrow> real" where
  "Phi x = (Pper x - 2923 / 240) / x ^ 2 + lam_r / x + 2 * Cper x / x ^ 3"

lemma frac_measurable [measurable]: "(frac :: real \<Rightarrow> real) \<in> borel_measurable borel"
proof -
  have e: "(frac :: real \<Rightarrow> real) = (\<lambda>x. x - real_of_int \<lfloor>x\<rfloor>)"
    using frac_def fun_eq_iff by blast
  show ?thesis unfolding e using borel_measurable_real_floor by simp
qed

lemma es_measurable [measurable]: "es \<in> borel_measurable borel"
proof -
  have e: "es = (\<lambda>u. if u \<le> 1 / 2 then 1 else - 1)" by (simp add: fun_eq_iff es_def)
  show ?thesis unfolding e by measurable
qed

lemma d0_measurable [measurable]: "d0 \<in> borel_measurable borel"
proof -
  have e: "d0 = (\<lambda>u. min u (1 - u))" by (simp add: fun_eq_iff d0_def)
  show ?thesis unfolding e by measurable
qed

lemma pos_measurable [measurable]: "pos_r \<in> borel_measurable borel"
proof -
  have e: "pos_r = (\<lambda>u. max u 0)" by (simp add: fun_eq_iff pos_r_def)
  show ?thesis unfolding e by measurable
qed

lemma R_measurable [measurable]: "R_r \<in> borel_measurable borel"
proof -
  have e: "R_r = (\<lambda>x. x * Fx x + Qc (frac x) (frac (alpha_r * x)) (frac (2 * Hc_r *
    x)) (frac (2 * x)) (frac (2 * (lam_r * x))))"
    by (simp add: fun_eq_iff R_eq)
  show ?thesis unfolding e Fx_def Qc_def by measurable
qed

lemma Fx_bounds: "- 37 / 5 \<le> Fx x \<and> Fx x \<le> 111 / 20"
  unfolding Fx_def lam_r_def using frac_ge_0[of x] frac_lt_1[of x] frac_ge_0[of "alpha_r *
    x"] frac_lt_1[of "alpha_r * x"] by linarith

lemma Q_bounds: "- 1 / 2 \<le> R_r x - x * Fx x \<and> R_r x - x * Fx x \<le> 13 / 8"
  unfolding Fx_def by (rule R_decomp_bound_all)

lemma R_abs_le: "3 \<le> x \<Longrightarrow> \<bar>R_r x\<bar> \<le> 9 * x"
proof -
  assume x: "3 \<le> x"
  have F: "- 37 / 5 \<le> Fx x \<and> Fx x \<le> 111 / 20" by (rule Fx_bounds)
  have "- 1 / 2 \<le> R_r x - x * Fx x \<and> R_r x - x * Fx x \<le> 13 / 8" by (rule Q_bounds)
  moreover have "x * (- 37 / 5) \<le> x * Fx x" using F x by (fastforce intro: mult_left_mono)
  moreover have "x * Fx x \<le> x * (111 / 20)" using F x by (auto intro: mult_left_mono)
  ultimately show ?thesis using x abs_le_iff by linarith
qed

lemma R_div_bound: "3 \<le> x \<Longrightarrow> \<bar>R_r x / x ^ 3\<bar> \<le> 9 / x ^ 2"
proof -
  assume x: "3 \<le> x"
  have p: "0 < x ^ 3" using x by simp
  have "\<bar>R_r x / x ^ 3\<bar> = \<bar>R_r x\<bar> / x ^ 3" using p by (simp add: abs_divide)
  moreover have "\<bar>R_r x\<bar> / x ^ 3 \<le> 9 * x / x ^ 3" using R_abs_le[OF x] p
    by (fastforce intro: divide_right_mono)
  moreover have "9 * x / x ^ 3 = 9 / x ^ 2" using x by (simp add: power3_eq_cube power2_eq_square)
  ultimately show ?thesis by linarith
qed

lemma inv_sq_integrable: "set_integrable lborel {3..} (\<lambda>x :: real. 9 / x ^ 2)"
proof -
  have "((\<lambda>x::real. 1 / x ^ 2) has_integral 1 / (real (2 - 1) * 3 ^ (2 - 1))) {3..}"
    using has_integral_inverse_power_to_inf[of 2 3] by simp
  hence i0: "(\<lambda>x::real. 1 / x ^ 2) integrable_on {3..}"
    by (blast intro: has_integral_integrable)
  have i: "(\<lambda>x::real. 9 * (1 / x ^ 2)) integrable_on {3..}"
    using integrable_on_cmult_left[OF i0, of 9] by simp
  have a: "(\<lambda>x::real. 9 * (1 / x ^ 2)) absolutely_integrable_on {3..}"
    using nonnegative_absolutely_integrable_1[OF i] by simp
  have m: "(\<lambda>x::real. indicator {3..} x *\<^sub>R (9 * (1 / x ^ 2))) \<in>
    borel_measurable lborel" by measurable
  have "integrable lborel (\<lambda>x::real. indicator {3..} x *\<^sub>R (9 * (1 / x ^ 2)))"
    using a integrable_completion[OF m] unfolding set_integrable_def by blast
  thus ?thesis unfolding set_integrable_def by simp
qed

theorem R_div_cube_integrable: "set_integrable lborel {3..} (\<lambda>x. R_r x / x ^ 3)"
proof -
  have m: "set_borel_measurable lborel {3..} (\<lambda>x. R_r x / x ^ 3)"
    unfolding set_borel_measurable_def by measurable
  have ae: "AE x in lborel. x \<in> {3..} \<longrightarrow>
    norm (R_r x / x ^ 3) \<le> norm (9 / x ^ 2)"
  proof (rule AE_I2)
    fix x :: real
    show "x \<in> {3..} \<longrightarrow> norm (R_r x / x ^ 3) \<le> norm (9 / x ^ 2)"
      using R_div_bound[of x]
      by simp
  qed
  show ?thesis by (rule set_integrable_bound[OF inv_sq_integrable m ae])
qed

text \<open>Derivatives of the fractional part off the integers.\<close>
lemma frac_has_derivative: "x \<notin> \<int> \<Longrightarrow> (frac has_real_derivative 1) (at x)"
proof -
  assume x: "x \<notin> \<int>"
  have e: "frac = (\<lambda>x::real. x - real_of_int \<lfloor>x\<rfloor>)"
    using frac_def fun_eq_iff by blast
  have fl: "((\<lambda>x. real_of_int \<lfloor>id x\<rfloor>) has_real_derivative 0) (at x)"
    using floor_has_real_derivative[where f = id and x = x] x by auto
  show ?thesis unfolding e using DERIV_diff[OF DERIV_ident fl] by force
qed

lemma frac_scaled_has_derivative: "c * x \<notin> \<int> \<Longrightarrow>
  ((\<lambda>x. frac (c * x)) has_real_derivative c) (at x)"
proof -
  assume h: "c * x \<notin> \<int>"
  have d: "(frac has_real_derivative 1) (at (c * x))" by (rule frac_has_derivative[OF h])
  show ?thesis using DERIV_chain2[OF d DERIV_cmult_Id[of c x]] by force
qed

lemma Pper_deriv: "x \<notin> Sx \<Longrightarrow> (Pper has_real_derivative (Fx x + lam_r)) (at x)"
proof -
  assume x: "x \<notin> Sx"
  have n1: "x \<notin> \<int>" and n2: "alpha_r * x \<notin> \<int>" using x
    by (simp_all add: Sx_def)
  have d1: "(frac has_real_derivative 1) (at x)" by (rule frac_has_derivative[OF n1])
  have d2: "((\<lambda>x. frac (alpha_r * x)) has_real_derivative alpha_r) (at x)"
    by (rule frac_scaled_has_derivative[OF n2])
  have e: "Pper = (\<lambda>x. 74 * frac (alpha_r * x) * (1 - frac (alpha_r * x)) - lam_r * frac x *
    (1 - frac x))"
    by (simp add: Pper_def fun_eq_iff)
  note D = DERIV_diff[OF DERIV_mult[OF DERIV_cmult[where c =
    74, OF d2] DERIV_diff[OF DERIV_const[where k = 1] d2]]
                         DERIV_mult[OF DERIV_cmult[where c =
                           lam_r, OF d1] DERIV_diff[OF DERIV_const[where k = 1] d1]]]
  have v: "74 * alpha_r * (1 - frac (alpha_r * x)) + (0 - alpha_r) * (74 * frac (alpha_r * x)) -
    (lam_r * 1 * (1 - frac x) + (0 - 1) * (lam_r * frac x)) = Fx x + lam_r"
    unfolding Fx_def alpha_r_def lam_r_def using algebra_simps by argo
  show ?thesis unfolding e using DERIV_cong[OF D v] by blast
qed

lemma G0_eq: "G0_r = (\<lambda>v. v * (1 - v) * (2 * v - 1) / 6)"
  by (simp add: fun_eq_iff G0_r_def)

lemma G0_deriv:
  "(G0_r has_real_derivative (v * (1 - v) - 1 / 6)) (at v)"
proof -
  note D = DERIV_cdivide[OF DERIV_mult[OF DERIV_mult[OF DERIV_ident DERIV_diff[OF DERIV_const[where
    k = 1] DERIV_ident]]
             DERIV_diff[OF DERIV_cmult[where c = 2, OF DERIV_ident] DERIV_const[where k =
               1]]], where c = 6]
  have v: "((1 * (1 - v) + (0 - 1) * v) * (2 * v - 1) + (2 * 1 - 0) * (v * (1 - v))) / 6 =
    v * (1 - v) - 1 / 6"
    using algebra_simps by argo
  show ?thesis unfolding G0_eq using DERIV_cong[OF D v] by blast
qed

lemma Cper_deriv: "x \<notin> Sx \<Longrightarrow>
  (Cper has_real_derivative (Pper x - 2923 / 240)) (at x)"
proof -
  assume x: "x \<notin> Sx"
  have n1: "x \<notin> \<int>" and n2: "alpha_r * x \<notin> \<int>" using x
    by (simp_all add: Sx_def)
  have d1: "(frac has_real_derivative 1) (at x)" by (rule frac_has_derivative[OF n1])
  have d2: "((\<lambda>x. frac (alpha_r * x)) has_real_derivative alpha_r) (at x)"
    by (rule frac_scaled_has_derivative[OF n2])
  have g1: "((\<lambda>x. G0_r (frac x)) has_real_derivative ((frac x * (1 - frac x) - 1 / 6) *
    1)) (at x)"
    by (rule DERIV_chain2[OF G0_deriv d1])
  have g2: "((\<lambda>x. G0_r (frac (alpha_r * x))) has_real_derivative ((frac (alpha_r * x) * (1 -
    frac (alpha_r * x)) - 1 / 6) * alpha_r)) (at x)"
    by (rule DERIV_chain2[OF G0_deriv d2])
  have e: "Cper = (\<lambda>x. 74 / alpha_r * G0_r (frac (alpha_r * x)) - lam_r * G0_r (frac x))"
    by (simp add: fun_eq_iff Cper_def)
  note D = DERIV_diff[OF DERIV_cmult[where c = "74 / alpha_r", OF g2] DERIV_cmult[where c =
    lam_r, OF g1]]
  have v: "74 / alpha_r * ((frac (alpha_r * x) * (1 - frac (alpha_r * x)) - 1 / 6) * alpha_r) -
    lam_r * ((frac x * (1 - frac x) - 1 / 6) * 1) = Pper x - 2923 / 240"
    unfolding Pper_def alpha_r_def lam_r_def using algebra_simps by argo
  show ?thesis unfolding e using DERIV_cong[OF D v] by blast
qed

lemma comp_frac_piece:
  fixes g :: "real \<Rightarrow> real" and m :: int
  assumes "continuous_on {0..1} g" "g 0 = g 1"
  shows "continuous_on {of_int m..of_int m + 1} (\<lambda>x. g (frac x))"
proof -
  have c: "continuous_on {of_int m..of_int m + 1} (\<lambda>y. g (y - of_int m))"
  proof (rule continuous_on_compose2[OF assms(1)])
    show "continuous_on {of_int m..of_int m + 1} (\<lambda>y::real. y - of_int m)"
      by (auto intro: continuous_intros)
    show "(\<lambda>y::real. y - of_int m) ` {of_int m..of_int m + 1} \<subseteq> {0..1}"
      by (auto simp: image_subset_iff)
  qed
  have e: "g (frac y) = g (y - of_int m)" if y: "y \<in> {of_int m..of_int m + 1}" for y
  proof (cases "y = of_int m + 1")
    case True
    have f: "frac y = 0" unfolding True by simp
    show ?thesis unfolding f True using assms(2) by simp
  next
    case False
    have f: "frac y = y - of_int m" using y False
      by (simp add: frac_def floor_eq_iff)
    show ?thesis unfolding f ..
  qed
  show ?thesis using continuous_on_cong[OF refl e] c by fast
qed

lemma comp_frac_isCont:
  fixes g :: "real \<Rightarrow> real"
  assumes "continuous_on {0..1} g" "g 0 = g 1"
  shows "isCont (\<lambda>x. g (frac x)) x"
proof -
  define n where "n = \<lfloor>x\<rfloor>"
  have c1: "continuous_on {of_int (n - 1)..of_int (n - 1) + 1} (\<lambda>x. g (frac x))"
    by (rule comp_frac_piece[OF assms])
  have c2: "continuous_on {of_int n..of_int n + 1} (\<lambda>x. g (frac x))"
    by (rule comp_frac_piece[OF assms])
  have u: "{of_int (n - 1)..of_int (n - 1) + 1} \<union> {of_int n..of_int n + 1} =
    {of_int n - 1..of_int n + (1::real)}"
    by fastforce
  have c: "continuous_on {of_int n - 1..of_int n + (1::real)} (\<lambda>x. g (frac x))"
    using continuous_on_closed_Un[OF closed_atLeastAtMost closed_atLeastAtMost c1 c2] unfolding u .
  have "of_int n - 1 < x" unfolding n_def using of_int_floor_le[of x] by linarith
  moreover have "x < of_int n + 1" unfolding n_def using real_of_int_floor_add_one_gt[of x]
    by linarith
  ultimately have xi: "x \<in> interior {of_int n - 1..of_int n + (1::real)}" by simp
  show ?thesis by (rule continuous_on_interior[OF c xi])
qed

text \<open>@{text "g \<circ> frac"} is continuous when @{text g} is continuous on @{text "[0,1]"}
  with @{text "g 0 = g 1"} (Lean @{text "ContinuousOn.comp_fract''"}).\<close>
lemma comp_frac_cont:
  fixes g :: "real \<Rightarrow> real"
  assumes "continuous_on {0..1} g" "g 0 = g 1"
  shows "continuous_on UNIV (\<lambda>x. g (frac x))"
proof -
  have "isCont (\<lambda>x. g (frac x)) x" for x
  proof (cases "x \<in> \<int>")
    case False
    thus ?thesis
      using comp_frac_isCont[OF assms, of x] by blast
  next
    case True
    show ?thesis
      using comp_frac_isCont[OF assms, of x] by blast
  qed
  thus ?thesis by (simp add: continuous_at_imp_continuous_on)
qed

lemma u_cont: "continuous_on UNIV (\<lambda>x::real. frac x * (1 - frac x))"
proof -
  have c: "continuous_on {0..1} (\<lambda>v::real. v * (1 - v))"
    by (fastforce intro: continuous_intros)
  show ?thesis using comp_frac_cont[OF c] by simp
qed

lemma u_cont_a: "continuous_on UNIV (\<lambda>x. frac (alpha_r * x) * (1 - frac (alpha_r * x)))"
proof -
  have c: "continuous_on UNIV (\<lambda>x. alpha_r * x)" by (auto intro: continuous_intros)
  show ?thesis using continuous_on_compose2[OF u_cont c] by blast
qed

lemma Pper_cont: "continuous_on UNIV Pper"
proof -
  have e: "Pper = (\<lambda>x. 74 * (frac (alpha_r * x) * (1 - frac (alpha_r * x))) - lam_r *
    (frac x * (1 - frac x)))"
    unfolding fun_eq_iff Pper_def by (simp add: mult.assoc)
  show ?thesis unfolding e using u_cont u_cont_a by (fast intro: continuous_intros)
qed

lemma G0_cont: "continuous_on {0..1} G0_r"
  unfolding G0_eq by (fastforce intro: continuous_intros)

lemma G0_frac_cont: "continuous_on UNIV (\<lambda>x. G0_r (frac x))"
  using comp_frac_cont[OF G0_cont] by (simp add: G0_r_def)

lemma Cper_cont: "continuous_on UNIV Cper"
proof -
  have c: "continuous_on UNIV (\<lambda>x. alpha_r * x)" by (auto intro: continuous_intros)
  have a: "continuous_on UNIV (\<lambda>x. G0_r (frac (alpha_r * x)))"
    using continuous_on_compose2[OF G0_frac_cont c] by blast
  have e: "Cper = (\<lambda>x. 74 / alpha_r * G0_r (frac (alpha_r * x)) - lam_r * G0_r (frac x))"
    by (simp add: fun_eq_iff Cper_def)
  show ?thesis unfolding e using a G0_frac_cont by (fast intro: continuous_intros)
qed

lemma uq_bounds: "0 \<le> (v::real) \<Longrightarrow> v \<le> 1 \<Longrightarrow>
  0 \<le> v * (1 - v) \<and> v * (1 - v) \<le> 1 / 4"
proof -
  assume v: "0 \<le> v" "v \<le> 1"
  have "0 \<le> v * (1 - v)" using v by simp
  moreover have "v * (1 - v) = 1 / 4 - (v - 1 / 2) ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  moreover have "0 \<le> (v - 1 / 2) ^ 2" by simp
  ultimately show ?thesis by linarith
qed

lemma Pper_abs_le: "\<bar>Pper x - 2923 / 240\<bar> \<le> 32"
proof -
  have e: "Pper x = 74 * (frac (alpha_r * x) * (1 - frac (alpha_r * x))) - lam_r * (frac x * (1 -
    frac x))"
    unfolding Pper_def by (simp add: mult.assoc)
  have "0 \<le> frac (alpha_r * x) * (1 - frac (alpha_r * x)) \<and>
    frac (alpha_r * x) * (1 - frac (alpha_r * x)) \<le> 1 / 4"
    by (rule uq_bounds) (simp_all add: frac_lt_1 less_imp_le)
  moreover have "0 \<le> frac x * (1 - frac x) \<and> frac x * (1 - frac x) \<le> 1 / 4"
    by (rule uq_bounds) (simp_all add: frac_lt_1 less_imp_le)
  ultimately show ?thesis unfolding e lam_r_def by linarith
qed

lemma Phi_deriv: "0 < x \<Longrightarrow> x \<notin> Sx \<Longrightarrow>
  (Phi has_real_derivative (Fx x / x ^ 2 - 6 * Cper x / x ^ 4)) (at x)"
proof -
  assume x0: "0 < x" and x: "x \<notin> Sx"
  have nz: "x \<noteq> 0" and n2: "x ^ 2 \<noteq> 0" and n3: "x ^ 3 \<noteq> 0" using x0 by simp_all
  have e: "Phi = (\<lambda>x. (Pper x - 2923 / 240) / x ^ 2 + lam_r / x + 2 * Cper x / x ^ 3)"
    by (simp add: fun_eq_iff Phi_def)
  note D = DERIV_add[OF DERIV_add[OF DERIV_divide[OF DERIV_diff[OF Pper_deriv[OF x]
    DERIV_const[where k = "2923 / 240"]] DERIV_pow[of 2] n2]
              DERIV_divide[OF DERIV_const[where k = lam_r] DERIV_ident nz]]
              DERIV_divide[OF DERIV_cmult[where c = 2, OF Cper_deriv[OF x]] DERIV_pow[of 3] n3]]
  have v: "((Fx x + lam_r - 0) * x\<^sup>2 - (Pper x - 2923 / 240) * (real 2 * x ^ (2 - Suc 0))) /
    (x\<^sup>2 * x\<^sup>2) + (0 * x - lam_r * 1) / (x * x) + (2 * (Pper x - 2923 / 240) * x ^ 3 -
    2 * Cper x * (real 3 * x ^ (3 - Suc 0))) / (x ^ 3 * x ^ 3) = Fx x / x ^ 2 - 6 * Cper x / x ^ 4"
    using nz by (simp add: field_simps eval_nat_numeral)
  show ?thesis unfolding e using DERIV_cong[OF D v] by blast
qed

lemma Phi_cont: "0 < a \<Longrightarrow> continuous_on {a..b} Phi"
proof -
  assume a: "0 < a"
  have e: "Phi = (\<lambda>x. (Pper x - 2923 / 240) / x ^ 2 + lam_r / x + 2 * Cper x / x ^ 3)"
    by (simp add: fun_eq_iff Phi_def)
  have P: "continuous_on {a..b} Pper" using continuous_on_subset[OF Pper_cont] by blast
  have C: "continuous_on {a..b} Cper" using continuous_on_subset[OF Cper_cont] by blast
  have nz1: "\<forall>x\<in>{a..b}. x \<noteq> 0" and nz2: "\<forall>x\<in>{a..b}. x ^ 2 \<noteq>
    0" and nz3: "\<forall>x\<in>{a..b}. x ^ 3 \<noteq> 0" using a by auto
  have "continuous_on {a..b} (\<lambda>x. (Pper x - 2923 / 240) / x ^ 2)" using P nz2
    by (fast intro: continuous_on_divide continuous_on_diff continuous_on_const continuous_on_power
      continuous_on_id)
  moreover have "continuous_on {a..b} (\<lambda>x. lam_r / x)" using nz1
    by (fast intro: continuous_on_divide continuous_on_const continuous_on_id)
  moreover have "continuous_on {a..b} (\<lambda>x. 2 * Cper x / x ^ 3)" using C nz3
    by (fast intro: continuous_on_divide continuous_on_mult continuous_on_const continuous_on_power
      continuous_on_id)
  ultimately show ?thesis unfolding e
    by (fast intro: continuous_on_add)
qed

lemma Phi_abs_le: "1 \<le> x \<Longrightarrow> \<bar>Phi x\<bar> \<le> 65 / x"
proof -
  assume x: "1 \<le> x"
  have x0: "0 < x" using x by simp
  have xx: "x \<le> x ^ 2" using x by (simp add: power2_eq_square)
  have xxx: "x \<le> x ^ 3" using x power_increasing[of 1 3 x]
    by simp
  have p2: "0 < x ^ 2" and p3: "0 < x ^ 3" using x0 by simp_all
  have a1a: "\<bar>(Pper x - 2923 / 240) / x ^ 2\<bar> = \<bar>Pper x - 2923 / 240\<bar> / x ^ 2"
    using p2 by (simp add: abs_divide)
  have a1b: "\<bar>Pper x - 2923 / 240\<bar> / x ^ 2 \<le> 32 / x ^ 2" using Pper_abs_le[of x] p2
    by (force intro: divide_right_mono)
  have a1c: "32 / x ^ 2 \<le> 32 / x" using divide_left_mono[OF xx, of 32] x0 p2 by simp
  have "\<bar>lam_r / x\<bar> = lam_r / x" using x0
    by (simp add: lam_r_def)
  moreover have "lam_r / x \<le> 1 / x" using x0 divide_right_mono[of lam_r 1 x]
    by (simp add: lam_r_def)
  ultimately have a2: "\<bar>lam_r / x\<bar> \<le> 1 / x" by linarith
  have a3a: "\<bar>2 * Cper x / x ^ 3\<bar> = 2 * \<bar>Cper x\<bar> / x ^ 3" using p3
    by (simp add: abs_divide abs_mult)
  have a3b: "2 * \<bar>Cper x\<bar> / x ^ 3 \<le> 32 / x ^ 3" using Cper_bound[of x] p3
    by (force intro: divide_right_mono)
  have a3c: "32 / x ^ 3 \<le> 32 / x" using divide_left_mono[OF xxx, of 32] x0 p3 by simp
  have t: "\<bar>(Pper x - 2923 / 240) / x ^ 2 + lam_r / x + 2 * Cper x / x ^ 3\<bar> \<le>
    \<bar>(Pper x - 2923 / 240) / x ^ 2\<bar> + \<bar>lam_r / x\<bar> + \<bar>2 * Cper x /
    x ^ 3\<bar>"
    by argo
  have s: "32 / x + 1 / x + 32 / x = 65 / x" by (simp add: add_divide_distrib[symmetric])
  show ?thesis unfolding Phi_def using t a1a a1b a1c a2 a3a a3b a3c s by linarith
qed

lemma Sx_finite: "finite (Sx \<inter> {M..N})"
proof -
  have s: "Sx \<inter> {M..N} \<subseteq>
    (of_int ` {\<lceil>M\<rceil>..\<lfloor>N\<rfloor>}) \<union> ((\<lambda>n. of_int n /
    alpha_r) ` {\<lceil>alpha_r * M\<rceil>..\<lfloor>alpha_r * N\<rfloor>})"
  proof
    fix x assume x: "x \<in> Sx \<inter> {M..N}"
    have xm: "M \<le> x" "x \<le> N" using x by auto
    show "x \<in> (of_int ` {\<lceil>M\<rceil>..\<lfloor>N\<rfloor>}) \<union> ((\<lambda>n. of_int
      n / alpha_r) ` {\<lceil>alpha_r * M\<rceil>..\<lfloor>alpha_r * N\<rfloor>})"
    proof (cases "x \<in> \<int>")
      case True
      then obtain n where n: "x = of_int n" by (auto elim: Ints_cases)
      have "n \<in> {\<lceil>M\<rceil>..\<lfloor>N\<rfloor>}" using xm unfolding n
        by (simp add: ceiling_le_iff le_floor_iff)
      thus ?thesis unfolding n by blast
    next
      case False
      hence "alpha_r * x \<in> \<int>" using x by (simp add: Sx_def)
      then obtain n where n: "alpha_r * x = of_int n" by (auto elim: Ints_cases)
      have xe: "x = of_int n / alpha_r" using n by (simp add: alpha_r_def field_simps)
      have "alpha_r * M \<le> alpha_r * x" using xm by (simp add: alpha_r_def)
      moreover have "alpha_r * x \<le> alpha_r * N" using xm by (simp add: alpha_r_def)
      ultimately have "n \<in> {\<lceil>alpha_r * M\<rceil>..\<lfloor>alpha_r * N\<rfloor>}"
        unfolding n by (simp add: ceiling_le_iff le_floor_iff)
      thus ?thesis unfolding xe by blast
    qed
  qed
  show ?thesis using finite_subset[OF s] by blast
qed

lemma set_integrable_bounded:
  fixes f :: "real \<Rightarrow> real"
  assumes A: "A \<in> sets lborel" "emeasure lborel A < \<infinity>" and f: "f \<in>
    borel_measurable borel"
    and b: "\<And>x. x \<in> A \<Longrightarrow> \<bar>f x\<bar> \<le> Bd"
  shows "set_integrable lborel A f"
proof -
  have m: "f \<in> borel_measurable lborel" using f
    by simp
  have ae: "AE x in lborel. x \<in> A \<longrightarrow> norm (f x) \<le> Bd"
  proof (rule AE_I2)
    fix x show "x \<in> A \<longrightarrow> norm (f x) \<le> Bd" using b[of x]
      by simp
  qed
  show ?thesis unfolding set_integrable_def
    using integrableI_bounded_set_indicator[OF A(1) m A(2) ae]
    by fast
qed

lemma interval_integrable_bounded:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "f \<in> borel_measurable borel" "\<And>x. x \<in> {a..b} \<Longrightarrow>
    \<bar>f x\<bar> \<le> Bd"
  shows "interval_lebesgue_integrable lborel (ereal a) (ereal b) f"
proof -
  have "set_integrable lborel {a<..<b} f"
  proof (rule set_integrable_bounded[OF _ _ assms(2)])
    show "{a<..<b} \<in> sets lborel"
      by simp
    show "emeasure lborel {a<..<b} < \<infinity>" using assms(1)
      by simp
    show "\<And>x. x \<in> {a<..<b} \<Longrightarrow> \<bar>f x\<bar> \<le> Bd" using assms(3)
      by simp
  qed
  thus ?thesis unfolding interval_lebesgue_integrable_def using assms(1)
    by simp
qed

text \<open>Measurability, bounds and integrability of the two parts of the tail integrand.\<close>
lemma Fx_measurable [measurable]: "Fx \<in> borel_measurable borel"
proof -
  have e: "Fx = (\<lambda>x. 4 * lam_r + 2 * lam_r * frac x - 12 * lam_r * frac (alpha_r * x))"
    by (simp add: fun_eq_iff Fx_def)
  show ?thesis unfolding e by measurable
qed

lemma Cper_measurable [measurable]: "Cper \<in> borel_measurable borel"
  using borel_measurable_continuous_onI[OF Cper_cont]
  by blast

lemma abs_div_ge1:
  fixes a d B :: real
  assumes d: "1 \<le> d" and a: "\<bar>a\<bar> \<le> B"
  shows "\<bar>a / d\<bar> \<le> B"
proof -
  have "\<bar>a / d\<bar> = \<bar>a\<bar> / d" using d
    by (simp add: abs_divide)
  moreover have "\<bar>a\<bar> / d \<le> \<bar>a\<bar>"
    using divide_left_mono[of 1 d "\<bar>a\<bar>"] d
    by linarith
  ultimately show ?thesis using a by linarith
qed

lemma g_bound: "3 \<le> x \<Longrightarrow> \<bar>Fx x / x ^ 2 - 6 * Cper x / x ^ 4\<bar> \<le> 104"
proof -
  assume x: "3 \<le> x"
  have x2: "1 \<le> x ^ 2" using x by (simp add: one_le_power)
  have x4: "1 \<le> x ^ 4" using x by (simp add: one_le_power)
  have F: "\<bar>Fx x\<bar> \<le> 8" using Fx_bounds[of x]
    by linarith
  have C: "\<bar>6 * Cper x\<bar> \<le> 96" using Cper_bound[of x]
    by linarith
  have "\<bar>Fx x / x ^ 2\<bar> \<le> 8" by (rule abs_div_ge1[OF x2 F])
  moreover have "\<bar>6 * Cper x / x ^ 4\<bar> \<le> 96" by (rule abs_div_ge1[OF x4 C])
  ultimately show ?thesis using abs_triangle_ineq4[of "Fx x / x ^ 2" "6 * Cper x / x ^ 4"]
    by linarith
qed

lemma h_bound: "3 \<le> x \<Longrightarrow>
  \<bar>6 * Cper x / x ^ 4 + (R_r x - x * Fx x) / x ^ 3\<bar> \<le> 98"
proof -
  assume x: "3 \<le> x"
  have x3: "1 \<le> x ^ 3" using x by (simp add: one_le_power)
  have x4: "1 \<le> x ^ 4" using x by (simp add: one_le_power)
  have Q: "\<bar>R_r x - x * Fx x\<bar> \<le> 2" using Q_bounds[of x]
    by linarith
  have C: "\<bar>6 * Cper x\<bar> \<le> 96" using Cper_bound[of x]
    by linarith
  have "\<bar>6 * Cper x / x ^ 4\<bar> \<le> 96" by (rule abs_div_ge1[OF x4 C])
  moreover have "\<bar>(R_r x - x * Fx x) / x ^ 3\<bar> \<le> 2" by (rule abs_div_ge1[OF x3 Q])
  ultimately show ?thesis using abs_triangle_ineq[of "6 * Cper x / x ^ 4" "(R_r x - x * Fx x) /
    x ^ 3"]
    by argo
qed

lemma g_meas: "(\<lambda>x. Fx x / x ^ 2 - 6 * Cper x / x ^ 4) \<in> borel_measurable borel"
  by measurable
lemma h_meas: "(\<lambda>x. 6 * Cper x / x ^ 4 + (R_r x - x * Fx x) / x ^ 3) \<in>
  borel_measurable borel" by measurable

lemma g_integrable:
  assumes M: "3 \<le> M" and MN: "M \<le> N"
  shows "interval_lebesgue_integrable lborel (ereal M) (ereal N) (\<lambda>x. Fx x / x ^ 2 - 6 *
    Cper x / x ^ 4)"
proof (rule interval_integrable_bounded[OF MN g_meas])
  fix x assume "x \<in> {M..N}"
  thus "\<bar>Fx x / x ^ 2 - 6 * Cper x / x ^ 4\<bar> \<le> 104" using g_bound[of x] M
    by fastforce
qed

lemma h_integrable:
  assumes M: "3 \<le> M" and MN: "M \<le> N"
  shows "interval_lebesgue_integrable lborel (ereal M) (ereal N) (\<lambda>x. 6 * Cper x / x ^ 4 +
    (R_r x - x * Fx x) / x ^ 3)"
proof (rule interval_integrable_bounded[OF MN h_meas])
  fix x assume "x \<in> {M..N}"
  thus "\<bar>6 * Cper x / x ^ 4 + (R_r x - x * Fx x) / x ^ 3\<bar> \<le> 98" using h_bound[of x] M
    by fastforce
qed

lemma g_set_integrable:
  assumes M: "3 \<le> M" and MN: "M \<le> N"
  shows "set_integrable lborel {M..N} (\<lambda>x. Fx x / x ^ 2 - 6 * Cper x / x ^ 4)"
proof (rule set_integrable_bounded[OF _ _ g_meas])
  show "{M..N} \<in> sets lborel"
    by simp
  show "emeasure lborel {M..N} < \<infinity>" using MN
    by simp
  fix x assume "x \<in> {M..N}"
  thus "\<bar>Fx x / x ^ 2 - 6 * Cper x / x ^ 4\<bar> \<le> 104" using g_bound[of x] M
    by fastforce
qed

lemma interval_integral_mono_real:
  fixes f g :: "real \<Rightarrow> real"
  assumes ab: "a \<le> b" and f: "interval_lebesgue_integrable lborel (ereal a) (ereal b) f"
    and g: "interval_lebesgue_integrable lborel (ereal a) (ereal b) g" and fg: "\<And>x. x \<in>
      {a<..<b} \<Longrightarrow> f x \<le> g x"
  shows "interval_lebesgue_integral lborel (ereal a) (ereal b) f \<le>
    interval_lebesgue_integral lborel (ereal a) (ereal b) g"
proof -
  have i1: "set_integrable lborel {a<..<b} f" using ab f unfolding interval_lebesgue_integrable_def
    by simp
  have i2: "set_integrable lborel {a<..<b} g" using ab g unfolding interval_lebesgue_integrable_def
    by simp
  show ?thesis unfolding interval_lebesgue_integral_def using ab set_integral_mono[OF i1 i2 fg]
    by fastforce
qed

lemma pt_upper: "3 \<le> x \<Longrightarrow>
  6 * Cper x / x ^ 4 + (R_r x - x * Fx x) / x ^ 3 \<le> 96 / x ^ 4 + 13 / 8 / x ^ 3"
proof -
  assume x: "3 \<le> x"
  have p3: "0 < x ^ 3" and p4: "0 < x ^ 4" using x by simp_all
  have "6 * Cper x / x ^ 4 \<le> 96 / x ^ 4" using Cper_bound[of x] p4
    by (auto intro: divide_right_mono)
  moreover have "(R_r x - x * Fx x) / x ^ 3 \<le> 13 / 8 / x ^ 3" using Q_bounds[of x] p3
    by (fastforce intro: divide_right_mono)
  ultimately show ?thesis by linarith
qed

lemma pt_lower: "3 \<le> x \<Longrightarrow>
  (- 96) / x ^ 4 + (- 1 / 2) / x ^ 3 \<le> 6 * Cper x / x ^ 4 + (R_r x - x * Fx x) / x ^ 3"
proof -
  assume x: "3 \<le> x"
  have p3: "0 < x ^ 3" and p4: "0 < x ^ 4" using x by simp_all
  have "(- 96) / x ^ 4 \<le> 6 * Cper x / x ^ 4" using Cper_bound[of x] p4
    by (fastforce intro: divide_right_mono)
  moreover have "(- 1 / 2) / x ^ 3 \<le> (R_r x - x * Fx x) / x ^ 3" using Q_bounds[of x] p3
    by (fastforce intro: divide_right_mono)
  ultimately show ?thesis by linarith
qed

lemma inv34_integrable:
  assumes M: "0 < M" and MN: "M \<le> N"
  shows "interval_lebesgue_integrable lborel (ereal M) (ereal N) (\<lambda>x. a / x ^ 4 + b /
    x ^ 3)"
proof (rule interval_integrable_continuous[OF MN])
  have "\<forall>x\<in>{M..N}. x ^ 4 \<noteq> 0" and "\<forall>x\<in>{M..N}. x ^ 3 \<noteq> 0"
    using M by auto
  thus "continuous_on {M..N} (\<lambda>x. a / x ^ 4 + b / x ^ 3)"
    by (fast intro: continuous_on_add continuous_on_divide continuous_on_const continuous_on_power
      continuous_on_id)
qed

text \<open>(5.15): @{text "\<integral>_M^N R/x^3 =
  \<Phi>(N) - \<Phi>(M) + \<integral>_M^N (6C/x^4 + Q/x^3)"}.\<close>
lemma tail_identity:
  assumes M: "3 \<le> M" and MN: "M \<le> N"
  shows "interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. R_r x / x ^ 3)
           = Phi N - Phi M + interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. 6 *
             Cper x / x ^ 4 + (R_r x - x * Fx x) / x ^ 3)"
proof -
  let ?g = "\<lambda>x. Fx x / x ^ 2 - 6 * Cper x / x ^ 4"
  let ?h = "\<lambda>x. 6 * Cper x / x ^ 4 + (R_r x - x * Fx x) / x ^ 3"
  have split: "\<And>x. x \<in> {M<..<N} \<Longrightarrow> R_r x / x ^ 3 = ?g x + ?h x"
  proof -
    fix x assume x: "x \<in> {M<..<N}"
    have x0: "x \<noteq> 0" using x M by auto
    have q: "(R_r x - x * Fx x) / x ^ 3 = R_r x / x ^ 3 - Fx x / x ^ 2" using x0
      by (simp add: diff_divide_distrib power2_eq_square power3_eq_cube)
    show "R_r x / x ^ 3 = ?g x + ?h x" unfolding q
      by simp
  qed
  have ig: "interval_lebesgue_integrable lborel (ereal M) (ereal N) ?g"
    by (rule g_integrable[OF M MN])
  have ih: "interval_lebesgue_integrable lborel (ereal M) (ereal N) ?h"
    by (rule h_integrable[OF M MN])
  have ftc: "interval_lebesgue_integral lborel (ereal M) (ereal N) ?g = Phi N - Phi M"
  proof -
    have hk: "(?g has_integral (Phi N - Phi M)) {M..N}"
    proof (rule fundamental_theorem_of_calculus_interior_strong[OF countable_finite[OF Sx_finite[of
      M N]] MN])
      fix x assume x: "x \<in> {M<..<N} - Sx \<inter> {M..N}"
      have x0: "0 < x" and xS: "x \<notin> Sx" using x M by auto
      show "(Phi has_vector_derivative ?g x) (at x)" using Phi_deriv[OF x0 xS]
        unfolding has_real_derivative_iff_has_vector_derivative .
    next
      show "continuous_on {M..N} Phi" using Phi_cont[of M N] M
        by linarith
    qed
    have si: "set_integrable lborel {M..N} ?g" by (rule g_set_integrable[OF M MN])
    have e: "interval_lebesgue_integral lborel (ereal M) (ereal N) ?g = integral {M..N} ?g"
      by (rule interval_integral_eq_integral[OF MN si])
    show ?thesis unfolding e using integral_unique[OF hk]
      by linarith
  qed
  have "interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. R_r x / x ^ 3) =
    interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. ?g x + ?h x)"
    by (rule interval_integral_cong_Ioo[OF MN split])
  also have "\<dots> = interval_lebesgue_integral lborel (ereal M) (ereal N) ?g +
    interval_lebesgue_integral lborel (ereal M) (ereal N) ?h"
    by (rule interval_lebesgue_integral_add[OF ig ih])
  finally show ?thesis unfolding ftc .
qed

lemma integral_inv34:
  assumes "0 < M" "M \<le> N"
  shows "interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. a / x ^ 4 + b / x ^ 3)
           = (- a / (3 * N ^ 3) - b / (2 * N ^ 2)) - (- a / (3 * M ^ 3) - b / (2 * M ^ 2))"
proof -
  let ?g = "\<lambda>x. a / x ^ 4 + b / x ^ 3"
  let ?F = "\<lambda>x. - a / (3 * x ^ 3) - b / (2 * x ^ 2)"
  have "\<forall>x\<in>{M..N}. x ^ 4 \<noteq> 0" and "\<forall>x\<in>{M..N}. x ^ 3 \<noteq> 0"
    using assms(1) by auto
  hence cont: "continuous_on {M..N} ?g"
    by (fast intro: continuous_on_add continuous_on_divide continuous_on_const continuous_on_power
      continuous_on_id)
  have D: "\<And>x. x \<in> {M..N} \<Longrightarrow>
    (?F has_vector_derivative ?g x) (at x within {M..N})"
  proof -
    fix x assume x: "x \<in> {M..N}"
    have x0: "x \<noteq> 0" using assms(1) x by auto
    have n3: "3 * x ^ 3 \<noteq> 0" and n2: "2 * x ^ 2 \<noteq> 0" using x0 by simp_all
    note DD = DERIV_diff[OF DERIV_divide[OF DERIV_const[of "- a"] DERIV_cmult[OF DERIV_pow[of 3]]
      n3]
                            DERIV_divide[OF DERIV_const[of b] DERIV_cmult[OF DERIV_pow[of 2]] n2]]
    have v: "(0 * (3 * x ^ 3) - - a * (3 * (real 3 * x ^ (3 - Suc 0)))) / (3 * x ^ 3 * (3 *
      x ^ 3)) - (0 * (2 * x ^ 2) - b * (2 * (real 2 * x ^ (2 - Suc 0)))) / (2 * x ^ 2 * (2 *
      x ^ 2)) = a / x ^ 4 + b / x ^ 3"
      using x0
      by (simp add: field_simps eval_nat_numeral)
    have "(?F has_real_derivative (a / x ^ 4 + b / x ^ 3)) (at x within {M..N})"
      using DERIV_cong[OF DD v]
      by blast
    thus "(?F has_vector_derivative ?g x) (at x within {M..N})"
      unfolding has_real_derivative_iff_has_vector_derivative .
  qed
  have mm1: "min M N = M" using assms(2) by simp
  have mm2: "max M N = N" using assms(2) by simp
  show ?thesis using interval_integral_FTC_finite[of M N ?g ?F] cont D unfolding mm1 mm2
    by presburger
qed


text \<open>The tail bounds, uniformly in @{text "M \<ge> 3"}.\<close>
lemma tail_bounds:
  assumes M: "3 \<le> M"
  shows "- Phi M - 32 / M ^ 3 - 1 / (4 * M ^ 2) \<le>
    set_lebesgue_integral lborel {M<..} (\<lambda>x. R_r x / x ^ 3)"
    and "set_lebesgue_integral lborel {M<..} (\<lambda>x. R_r x / x ^ 3) \<le>
      - Phi M + 32 / M ^ 3 + 13 / (16 * M ^ 2)"
proof -
  let ?f = "\<lambda>x. R_r x / x ^ 3"
  have fin: "\<And>N. M \<le> N \<Longrightarrow>
      interval_lebesgue_integral lborel (ereal M) (ereal N) ?f \<le>
        Phi N - Phi M + ((- 96 / (3 * N ^ 3) - 13 / 8 / (2 * N ^ 2)) - (- 96 / (3 * M ^ 3) - 13 /
        8 / (2 * M ^ 2))) \<and>
      Phi N - Phi M + ((96 / (3 * N ^ 3) - (- 1 / 2) / (2 * N ^ 2)) - (96 / (3 * M ^ 3) - (- 1 /
        2) / (2 * M ^ 2))) \<le> interval_lebesgue_integral lborel (ereal M) (ereal N) ?f"
  proof -
    fix N assume MN: "M \<le> N"
    have M0: "0 < M" using M by simp
    let ?h = "\<lambda>x. 6 * Cper x / x ^ 4 + (R_r x - x * Fx x) / x ^ 3"
    have T: "interval_lebesgue_integral lborel (ereal M) (ereal N) ?f =
      Phi N - Phi M + interval_lebesgue_integral lborel (ereal M) (ereal N) ?h"
      by (rule tail_identity[OF M MN])
    have ih: "interval_lebesgue_integrable lborel (ereal M) (ereal N) ?h"
      by (rule h_integrable[OF M MN])
    have "interval_lebesgue_integral lborel (ereal M) (ereal N) ?h \<le>
      interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. 96 / x ^ 4 + 13 / 8 /
      x ^ 3)"
    proof (rule interval_integral_mono_real[OF MN ih inv34_integrable[OF M0 MN]])
      fix x assume "x \<in> {M<..<N}"
      thus "?h x \<le> 96 / x ^ 4 + 13 / 8 / x ^ 3" using pt_upper[of x] M
        by fastforce
    qed
    moreover have "interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. (- 96) /
      x ^ 4 + (- 1 / 2) / x ^ 3) \<le> interval_lebesgue_integral lborel (ereal M) (ereal N) ?h"
    proof (rule interval_integral_mono_real[OF MN inv34_integrable[OF M0 MN] ih])
      fix x assume "x \<in> {M<..<N}"
      thus "(- 96) / x ^ 4 + (- 1 / 2) / x ^ 3 \<le> ?h x" using pt_lower[of x] M
        by fastforce
    qed
    moreover have "interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. 96 / x ^ 4 +
      13 / 8 / x ^ 3) = (- 96 / (3 * N ^ 3) - 13 / 8 / (2 * N ^ 2)) - (- 96 / (3 * M ^ 3) - 13 / 8 /
      (2 * M ^ 2))"
      by (rule integral_inv34[OF M0 MN])
    moreover have "interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. (- 96) /
      x ^ 4 + (- 1 / 2) / x ^ 3) = (- (- 96) / (3 * N ^ 3) - (- 1 / 2) / (2 * N ^ 2)) - (- (- 96) /
      (3 * M ^ 3) - (- 1 / 2) / (2 * M ^ 2))"
      by (rule integral_inv34[OF M0 MN])
    hence "interval_lebesgue_integral lborel (ereal M) (ereal N) (\<lambda>x. (- 96) / x ^ 4 +
      (- 1 / 2) / x ^ 3) = (96 / (3 * N ^ 3) - (- 1 / 2) / (2 * N ^ 2)) - (96 / (3 * M ^ 3) - (- 1 /
      2) / (2 * M ^ 2))"
      by simp
    ultimately show "interval_lebesgue_integral lborel (ereal M) (ereal N) ?f \<le>
      Phi N - Phi M + ((- 96 / (3 * N ^ 3) - 13 / 8 / (2 * N ^ 2)) - (- 96 / (3 * M ^ 3) - 13 / 8 /
      (2 * M ^ 2))) \<and>
      Phi N - Phi M + ((96 / (3 * N ^ 3) - (- 1 / 2) / (2 * N ^ 2)) - (96 / (3 * M ^ 3) - (- 1 /
        2) / (2 * M ^ 2))) \<le> interval_lebesgue_integral lborel (ereal M) (ereal N) ?f"
      using T by linarith
  qed
  have lim: "((\<lambda>N. interval_lebesgue_integral lborel (ereal M) (ereal N) ?f)
    \<longlongrightarrow> set_lebesgue_integral lborel {M<..} ?f) at_top"
  proof -
    have int: "set_integrable lborel {M..} ?f"
      using set_integrable_subset[OF R_div_cube_integrable, of "{M..}"] M
      by auto
    have T: "((\<lambda>b. set_lebesgue_integral lborel {M..b} ?f) \<longlongrightarrow>
      set_lebesgue_integral lborel {M..} ?f) at_top"
      using tendsto_set_lebesgue_integral_at_top[OF _ int]
      by simp
    have E1: "set_lebesgue_integral lborel {M..} ?f = set_lebesgue_integral lborel {M<..} ?f"
      using set_integral_discrete_difference[where X = "{M}" and A = "{M..}" and B =
        "{M<..}" and M = lborel and f = ?f]
      by fastforce
    have E2: "eventually (\<lambda>N. set_lebesgue_integral lborel {M..N} ?f =
      interval_lebesgue_integral lborel (ereal M) (ereal N) ?f) at_top"
    proof (rule eventually_at_top_linorderI[of M])
      fix N assume "M \<le> N"
      thus "set_lebesgue_integral lborel {M..N} ?f =
        interval_lebesgue_integral lborel (ereal M) (ereal N) ?f"
        using interval_integral_Icc[of M N ?f]
        by argo
    qed
    show ?thesis using tendsto_cong[OF E2] T E1
      by simp
  qed
  have PhiN: "((\<lambda>N. Phi N) \<longlongrightarrow> 0) at_top" and N3: "((\<lambda>N :: real. 1
    / N ^ 3) \<longlongrightarrow> 0) at_top" and N2: "((\<lambda>N :: real. 1 /
    N ^ 2) \<longlongrightarrow> 0) at_top"
  proof -
    have ev: "eventually (\<lambda>N. norm (Phi N) \<le> 65 / N) at_top"
    proof (rule eventually_at_top_linorderI[of 1])
      fix N :: real assume "1 \<le> N"
      thus "norm (Phi N) \<le> 65 / N" using Phi_abs_le[of N]
        by simp
    qed
    have l65: "((\<lambda>N::real. 65 / N) \<longlongrightarrow> 0) at_top"
      using real_tendsto_divide_at_top[OF tendsto_const filterlim_ident]
      by auto
    show "((\<lambda>N. Phi N) \<longlongrightarrow> 0) at_top" using Lim_null_comparison[OF ev l65]
      by simp
    have p3: "filterlim (\<lambda>N::real. N ^ 3) at_top at_top"
      using filterlim_pow_at_top[OF _ filterlim_ident, of 3]
      by simp
    have p2: "filterlim (\<lambda>N::real. N ^ 2) at_top at_top"
      using filterlim_pow_at_top[OF _ filterlim_ident, of 2]
      by auto
    show "((\<lambda>N :: real. 1 / N ^ 3) \<longlongrightarrow> 0) at_top"
      using real_tendsto_divide_at_top[OF tendsto_const p3]
      by blast
    show "((\<lambda>N :: real. 1 / N ^ 2) \<longlongrightarrow> 0) at_top"
      using real_tendsto_divide_at_top[OF tendsto_const p2]
      by auto
  qed
  show "- Phi M - 32 / M ^ 3 - 1 / (4 * M ^ 2) \<le> set_lebesgue_integral lborel {M<..} ?f"
  proof -
    let ?K = "96 / (3 * M ^ 3) - (- 1 / 2) / (2 * M ^ 2)"
    have eq: "\<And>N::real. 96 / (3 * N ^ 3) - (- 1 / 2) / (2 * N ^ 2) =
      32 * (1 / N ^ 3) + 1 / 4 * (1 / N ^ 2)"
      by (simp add: field_simps)
    note G = tendsto_add[OF tendsto_diff[OF PhiN tendsto_const[of "Phi M"]] tendsto_diff[OF
      tendsto_add[OF tendsto_mult[OF tendsto_const[of 32] N3] tendsto_mult[OF tendsto_const[of "1 /
      4"] N2]] tendsto_const[of ?K]]]
    have gl: "((\<lambda>N. Phi N - Phi M + ((96 / (3 * N ^ 3) - (- 1 / 2) / (2 * N ^ 2)) -
      ?K)) \<longlongrightarrow> 0 - Phi M + ((32 * 0 + 1 / 4 * 0) - ?K)) at_top"
      unfolding eq using G
      by auto
    have ev: "eventually (\<lambda>N. Phi N - Phi M + ((96 / (3 * N ^ 3) - (- 1 / 2) / (2 *
      N ^ 2)) - ?K) \<le> interval_lebesgue_integral lborel (ereal M) (ereal N) ?f) at_top"
    proof (rule eventually_at_top_linorderI[of M])
      fix N assume "M \<le> N"
      thus "Phi N - Phi M + ((96 / (3 * N ^ 3) - (- 1 / 2) / (2 * N ^ 2)) - ?K) \<le>
        interval_lebesgue_integral lborel (ereal M) (ereal N) ?f"
        using fin[of N]
        by linarith
    qed
    have "0 - Phi M + ((32 * 0 + 1 / 4 * 0) - ?K) \<le> set_lebesgue_integral lborel {M<..} ?f"
      by (rule tendsto_le[OF trivial_limit_at_top_linorder lim gl ev])
    moreover have "0 - Phi M + ((32 * 0 + 1 / 4 * 0) - ?K) = - Phi M - 32 / M ^ 3 - 1 / (4 * M ^ 2)"
      by (simp add: field_simps)
    ultimately show ?thesis by linarith
  qed
  show "set_lebesgue_integral lborel {M<..} ?f \<le> - Phi M + 32 / M ^ 3 + 13 / (16 * M ^ 2)"
  proof -
    let ?K = "- 96 / (3 * M ^ 3) - 13 / 8 / (2 * M ^ 2)"
    have eq: "\<And>N::real. - 96 / (3 * N ^ 3) - 13 / 8 / (2 * N ^ 2) =
      (- 32) * (1 / N ^ 3) + (- 13 / 16) * (1 / N ^ 2)"
      by (simp add: field_simps)
    note G = tendsto_add[OF tendsto_diff[OF PhiN tendsto_const[of "Phi M"]] tendsto_diff[OF
      tendsto_add[OF tendsto_mult[OF tendsto_const[of "- 32"] N3] tendsto_mult[OF tendsto_const[of
      "- 13 / 16"] N2]] tendsto_const[of ?K]]]
    have gl: "((\<lambda>N. Phi N - Phi M + ((- 96 / (3 * N ^ 3) - 13 / 8 / (2 * N ^ 2)) -
      ?K)) \<longlongrightarrow> 0 - Phi M + (((- 32) * 0 + (- 13 / 16) * 0) - ?K)) at_top"
      unfolding eq using G
      by simp
    have ev: "eventually (\<lambda>N. interval_lebesgue_integral lborel (ereal M) (ereal N) ?f \<le>
      Phi N - Phi M + ((- 96 / (3 * N ^ 3) - 13 / 8 / (2 * N ^ 2)) - ?K)) at_top"
    proof (rule eventually_at_top_linorderI[of M])
      fix N assume "M \<le> N"
      thus "interval_lebesgue_integral lborel (ereal M) (ereal N) ?f \<le>
        Phi N - Phi M + ((- 96 / (3 * N ^ 3) - 13 / 8 / (2 * N ^ 2)) - ?K)"
        using fin[of N]
        by linarith
    qed
    have "set_lebesgue_integral lborel {M<..} ?f \<le>
      0 - Phi M + (((- 32) * 0 + (- 13 / 16) * 0) - ?K)"
      by (rule tendsto_le[OF trivial_limit_at_top_linorder gl lim ev])
    moreover have "0 - Phi M + (((- 32) * 0 + (- 13 / 16) * 0) - ?K) =
      - Phi M + 32 / M ^ 3 + 13 / (16 * M ^ 2)"
      by (simp add: field_simps)
    ultimately show ?thesis by linarith
  qed
qed

lemma Phi_20: "Phi 20 = (37 / 2 - 2923 / 240) / 400 + 37 / 800"
proof -
  have a: "alpha_r * 20 = 3 / 2" by (simp add: alpha_r_def)
  have f1: "frac (20 :: real) = 0"
    by fastforce
  have fl: "\<lfloor>3 / 2 :: real\<rfloor> = 1"
    by (force simp: floor_eq_iff)
  have f2: "frac (3 / 2 :: real) = 1 / 2" unfolding frac_def fl
    by simp
  show ?thesis unfolding Phi_def Pper_def Cper_def G0_r_def a f1 f2
    by (simp add: lam_r_def alpha_r_def)
qed

text \<open>(5.16) (tight: @{text "P(20) = 37/2"}, @{text "C(20) = 0"}).\<close>
theorem R_tail_20_bound: "set_lebesgue_integral lborel {20<..} (\<lambda>x. R_r x / x ^ 3) \<le>
  - 2689 / 48000"
  using tail_bounds(2)[of 20] unfolding Phi_20 by simp

text \<open>(5.17): for @{text "40 | M"},
  @{text "\<Phi>(M) = -(2923/240)/M^2 + \<lambda>/M"}.\<close>
theorem R_tail_M_bound:
  assumes "40 dvd M" "0 < M"
  shows "- lam_r / real M + (2923 / 240 - 1 / 4) / real M ^ 2 - 32 / real M ^ 3
           \<le> set_lebesgue_integral lborel {real M<..} (\<lambda>x. R_r x / x ^ 3)"
proof -
  have M3: "3 \<le> real M" using assms by (auto elim!: dvdE)
  have fr: "frac (real M) = 0" "frac (alpha_r * real M) = 0"
  proof -
    obtain k where k: "M = 40 * k" using assms(1) by (elim dvdE)
    have e: "alpha_r * real M = real (3 * k)" unfolding k alpha_r_def by auto
    show "frac (real M) = 0" "frac (alpha_r * real M) = 0" unfolding e by (auto simp: frac_def)
  qed
  have PhiM: "Phi (real M) = - (2923 / 240) / real M ^ 2 + lam_r / real M"
    unfolding Phi_def Pper_def Cper_def G0_r_def fr by simp
  show ?thesis using tail_bounds(1)[OF M3] unfolding PhiM by (simp add: field_simps)
qed


subsection \<open>Continuity off a countable set, and boundedness\<close>

text \<open>@{text "D_R"}: the points where some @{text "c x"}
  (@{text "c \<in> {1, 2, \<alpha>, 2\<alpha>, 2H_c, 2\<lambda>}"}) is an integer.\<close>
definition DR :: "real set" where
  "DR = (\<Union> c \<in> {1, 2, alpha_r, 2 * alpha_r, 2 * Hc_r,
    2 * lam_r}. (\<lambda>n :: int. of_int n / c) ` UNIV)"

lemma DR_countable: "countable DR"
  unfolding DR_def by (intro countable_UN countable_image) simp_all

text \<open>A function that agrees with a continuous one on an open neighbourhood is continuous
  there.\<close>
lemma isCont_local:
  fixes f g :: "real \<Rightarrow> real"
  assumes "open S" "y \<in> S" "\<And>z. z \<in> S \<Longrightarrow> f z = g z" "isCont g y"
  shows "isCont f y"
proof -
  have ev0: "eventually (\<lambda>z. z \<in> S) (nhds y)"
    using eventually_nhds_in_open[OF assms(1,2)]
    by presburger
  have ev: "eventually (\<lambda>z. f z = g z) (nhds y)" using eventually_mono[OF ev0] assms(3)
    by force
  show ?thesis using isCont_cong[OF ev] assms(4)
    by fastforce
qed

lemma frac_isCont: "(y :: real) \<notin> \<int> \<Longrightarrow> isCont frac y"
  using continuous_frac[of y] by blast

lemma es_isCont: "u \<noteq> 1 / 2 \<Longrightarrow> isCont es u"
proof -
  assume u: "u \<noteq> 1 / 2"
  show ?thesis
  proof (cases "u < 1 / 2")
    case True
    show ?thesis
    proof (rule isCont_local[of "{..<1 / 2}" u es "\<lambda>_. 1"])
      show "open {..<1 / 2 :: real}"
        by force
      show "u \<in> {..<1 / 2}" using True
        by force
      show "\<And>z. z \<in> {..<1 / 2} \<Longrightarrow> es z = 1" unfolding es_def
        by fastforce
      show "isCont (\<lambda>_. 1 :: real) u"
        by simp
    qed
  next
    case False
    hence g: "1 / 2 < u" using u
      by auto
    show ?thesis
    proof (rule isCont_local[of "{1 / 2<..}" u es "\<lambda>_. - 1"])
      show "open {1 / 2 :: real<..}"
        by auto
      show "u \<in> {1 / 2<..}" using g
        by blast
      show "\<And>z. z \<in> {1 / 2<..} \<Longrightarrow> es z = - 1" unfolding es_def
        by force
      show "isCont (\<lambda>_. - 1 :: real) u"
        by auto
    qed
  qed
qed

lemma d0_cont: "isCont d0 u" and pos_cont: "isCont pos_r u"
  unfolding d0_def pos_r_def by (intro continuous_intros)+

lemma isCont_R_form:
  fixes a b c d e :: "real \<Rightarrow> real" and x :: real
  assumes "isCont a x" "isCont b x" "isCont c x" "isCont d x" "isCont e x"
    "isCont (\<lambda>x. es (a x)) x" "isCont (\<lambda>x. es (b x)) x"
  shows "isCont (\<lambda>x. x * (4 * lam_r + 2 * lam_r * a x - 12 * lam_r * b x) +
    Qc (a x) (b x) (c x) (d x) (e x)) x"
proof -
  have d1: "isCont (\<lambda>x. d0 (a x)) x" by (rule isCont_o2[OF assms(1) d0_cont])
  have da: "isCont (\<lambda>x. d0 (b x)) x" by (rule isCont_o2[OF assms(2) d0_cont])
  have pp0: "isCont (\<lambda>x. (c x - d x) / 2) x" using assms(3,4)
    by (auto intro: continuous_intros)
  have pp: "isCont (\<lambda>x. pos_r ((c x - d x) / 2)) x" by (rule isCont_o2[OF pp0 pos_cont])
  show ?thesis unfolding Qc_def
    by (fastforce intro: continuous_intros assms d1 da pp)
qed

text \<open>Every ingredient of @{text "R_eq"} is continuous at @{text "x \<notin> D_R"}.\<close>
theorem R_isCont_off_countable: "\<exists>D. countable D \<and> (\<forall>x. 0 < x \<longrightarrow>
  x \<notin> D \<longrightarrow> isCont R_r x)"
proof (intro exI[of _ DR] conjI allI impI DR_countable)
  fix x :: real assume x: "0 < x" "x \<notin> DR"
  have nI: "c * x \<notin> \<int>" if "c \<in> {1, 2, alpha_r, 2 * alpha_r, 2 * Hc_r, 2 * lam_r}"
    for c
  proof
    assume "c * x \<in> \<int>"
    then obtain n where n: "c * x = of_int n" by (auto elim: Ints_cases)
    have "c \<noteq> 0" using that by (force simp: alpha_r_def Hc_r_def lam_r_def)
    hence "x = of_int n / c" using n by (auto simp: field_simps)
    hence "x \<in> DR" unfolding DR_def using that by fast
    thus False using x(2) by simp
  qed
  have fc: "isCont (\<lambda>x. frac (c * x)) x"
    if "c \<in> {1, 2, alpha_r, 2 * alpha_r, 2 * Hc_r, 2 * lam_r}" for c
  proof -
    have cm: "isCont (\<lambda>x. c * x) x" by (auto intro: continuous_intros)
    show ?thesis using isCont_o2[OF cm frac_isCont[OF nI[OF that]]] by presburger
  qed
  have ec: "isCont (\<lambda>x. es (frac (c * x))) x" if "c \<in> {1, alpha_r}" for c
  proof -
    have c1: "c \<in> {1, 2, alpha_r, 2 * alpha_r, 2 * Hc_r, 2 * lam_r}" using that
      by fastforce
    have c2: "2 * c \<in> {1, 2, alpha_r, 2 * alpha_r, 2 * Hc_r, 2 * lam_r}" using that
      by auto
    have h: "frac (c * x) \<noteq> 1 / 2"
    proof
      assume h: "frac (c * x) = 1 / 2"
      have e: "2 * c * x = of_int (2 * \<lfloor>c * x\<rfloor> + 1)" using h unfolding frac_def
        by (auto simp: field_simps)
      have "2 * c * x \<in> \<int>" unfolding e by (rule Ints_of_int)
      thus False using nI[OF c2]
        by meson
    qed
    show ?thesis using isCont_o2[OF fc[OF c1] es_isCont[OF h]]
      by fastforce
  qed
  have e: "R_r = (\<lambda>x. x * Fx x + Qc (frac x) (frac (alpha_r * x)) (frac (2 * Hc_r *
    x)) (frac (2 * x)) (frac (2 * (lam_r * x))))"
    by (simp add: fun_eq_iff R_eq)
  have f1: "isCont frac x" using fc[of 1]
    by fastforce
  have fa: "isCont (\<lambda>x. frac (alpha_r * x)) x" using fc[of alpha_r]
    by fastforce
  have fH: "isCont (\<lambda>x. frac (2 * Hc_r * x)) x" using fc[of "2 * Hc_r"]
    by fast
  have f2: "isCont (\<lambda>x. frac (2 * x)) x" using fc[of 2]
    by fastforce
  have fl: "isCont (\<lambda>x. frac (2 * (lam_r * x))) x" using fc[of "2 * lam_r"]
    unfolding mult.assoc
    by fastforce
  have e1: "isCont (\<lambda>x. es (frac x)) x" using ec[of 1]
    by fastforce
  have ea: "isCont (\<lambda>x. es (frac (alpha_r * x))) x" using ec[of alpha_r]
    by fastforce
  show "isCont R_r x" unfolding e Fx_def using isCont_R_form[OF f1 fa fH f2 fl e1 ea]
    by meson
qed

definition DO :: "real set" where "DO = {1 / 3, 1 / 2,
  1} \<union> range (\<lambda>n :: nat. 1 / real n)"

lemma DO_countable: "countable DO"
  unfolding DO_def by (intro countable_Un countable_image) simp_all

theorem outer_integrand_isCont_off_countable: "\<exists>D. countable D \<and>
  (\<forall>y. 0 < y \<longrightarrow> y \<notin> D \<longrightarrow> isCont outer_integrand y)"
proof (intro exI[of _ DO] conjI allI impI DO_countable)
  fix y :: real assume y: "0 < y" "y \<notin> DO"
  have R0: "isCont R0_r y"
  proof -
    have "y \<noteq> 1 / 3" using y(2) unfolding DO_def
      by fast
    moreover have "y \<noteq> 1 / 2" using y(2) unfolding DO_def
      by fastforce
    moreover have "y \<noteq> 1" using y(2) unfolding DO_def
      by force
    ultimately consider (A) "1 / 3 < y \<and> y < 1 / 2" | (B) "1 / 2 < y \<and>
      y < 1" | (C) "y \<in> - {1 / 3..1}"
      by fastforce
    thus ?thesis
    proof cases
      case A
      show ?thesis
      proof (rule isCont_local[of "{1 / 3<..<1 / 2}" y R0_r "\<lambda>y. 8 - 9 * y - 8 * alpha_r -
        5 * min alpha_r (1 - 2 * y) - 5 * pos_r (1 + alpha_r - 3 * y)"])
        show "open {1 / 3<..<1 / 2 :: real}"
          by force
        show "y \<in> {1 / 3<..<1 / 2}" using A
          by simp
        show "\<And>z. z \<in> {1 / 3<..<1 / 2} \<Longrightarrow>
          R0_r z = 8 - 9 * z - 8 * alpha_r - 5 * min alpha_r (1 - 2 * z) - 5 * pos_r (1 + alpha_r -
          3 * z)"
          unfolding R0_r_def
          by force
        show "isCont (\<lambda>y. 8 - 9 * y - 8 * alpha_r - 5 * min alpha_r (1 - 2 * y) - 5 *
          pos_r (1 + alpha_r - 3 * y)) y"
          unfolding pos_r_def
          by (fast intro: continuous_intros)
      qed
    next
      case B
      show ?thesis
      proof (rule isCont_local[of "{1 / 2<..<1}" y R0_r "\<lambda>y. 7 * (1 - y) - 6 *
        min alpha_r (1 - y) - 6 * pos_r (1 + alpha_r - 2 * y) + pos_r (1 + 4 * alpha_r - 2 * y)"])
        show "open {1 / 2<..<1 :: real}"
          by force
        show "y \<in> {1 / 2<..<1}" using B
          by auto
        show "\<And>z. z \<in> {1 / 2<..<1} \<Longrightarrow>
          R0_r z = 7 * (1 - z) - 6 * min alpha_r (1 - z) - 6 * pos_r (1 + alpha_r - 2 * z) +
          pos_r (1 + 4 * alpha_r - 2 * z)"
          unfolding R0_r_def
          by fastforce
        show "isCont (\<lambda>y. 7 * (1 - y) - 6 * min alpha_r (1 - y) - 6 * pos_r (1 + alpha_r -
          2 * y) + pos_r (1 + 4 * alpha_r - 2 * y)) y"
          unfolding pos_r_def
          by (fast intro: continuous_intros)
      qed
    next
      case C
      show ?thesis
      proof (rule isCont_local[of "- {1 / 3..1}" y R0_r "\<lambda>_. 0"])
        show "open (- {1 / 3..1 :: real})"
          by fastforce
        show "y \<in> - {1 / 3..1}" using C
          by fast
        show "\<And>z. z \<in> - {1 / 3..1} \<Longrightarrow> R0_r z = 0"
          unfolding R0_r_def
          by auto
        show "isCont (\<lambda>_. 0 :: real) y"
          by auto
      qed
    qed
  qed
  have d: "isCont dfun_r y"
  proof (cases "1 / 3 < y \<and> y < 1 / 2")
    case True
    show ?thesis
    proof (rule isCont_local[of "{1 / 3<..<1 / 2}" y dfun_r "\<lambda>y. pos_r ((1 + 4 * alpha_r -
      3 * y) - pos_r (1 + alpha_r - 3 * y))"])
      show "open {1 / 3<..<1 / 2 :: real}"
        by force
      show "y \<in> {1 / 3<..<1 / 2}" using True
        by simp
      show "\<And>z. z \<in> {1 / 3<..<1 / 2} \<Longrightarrow>
        dfun_r z = pos_r ((1 + 4 * alpha_r - 3 * z) - pos_r (1 + alpha_r - 3 * z))"
        unfolding dfun_r_def
        by force
      show "isCont (\<lambda>y. pos_r ((1 + 4 * alpha_r - 3 * y) - pos_r (1 + alpha_r - 3 * y))) y"
        unfolding pos_r_def
        by (fast intro: continuous_intros)
    qed
  next
    case False
    have ne1: "y \<noteq> 1 / 3" using y(2) unfolding DO_def
      by fast
    have ne2: "y \<noteq> 1 / 2" using y(2) unfolding DO_def
      by fastforce
    note ne = ne1 ne2
    show ?thesis
    proof (rule isCont_local[of "- {1 / 3..1 / 2}" y dfun_r "\<lambda>_. 0"])
      show "open (- {1 / 3..1 / 2 :: real})"
        by fast
      show "y \<in> - {1 / 3..1 / 2}" using False ne
        by force
      show "\<And>z. z \<in> - {1 / 3..1 / 2} \<Longrightarrow> dfun_r z = 0"
        unfolding dfun_r_def
        by fastforce
      show "isCont (\<lambda>_. 0 :: real) y"
        by auto
    qed
  qed
  have fl: "isCont (\<lambda>y. of_int (floor (1 / y)) :: real) y"
  proof -
    have nI: "1 / y \<notin> \<int>"
    proof
      assume "1 / y \<in> \<int>"
      then obtain n where n: "1 / y = of_int n" by (auto elim: Ints_cases)
      have p: "0 < 1 / y" using y(1)
        by auto
      have "0 < n" using n p
        by presburger
      hence r: "real (nat n) = of_int n"
        by fastforce
      have "y = 1 / real (nat n)" unfolding r n[symmetric]
        by simp
      hence "y \<in> DO" unfolding DO_def
        by fast
      thus False using y(2)
        by meson
    qed
    have c1: "isCont (\<lambda>y. 1 / y) y" using y(1)
      by (fast intro: continuous_intros)
    have c2: "isCont (real_of_int \<circ> floor) (1 / y)" by (rule continuous_floor[OF nI])
    show ?thesis using isCont_o2[OF c1 c2]
      by (force simp: o_def)
  qed
  show "isCont outer_integrand y"
    unfolding outer_integrand_def pos_r_def using R0 d fl
    by (fast intro: continuous_intros)
qed

theorem outer_integrand_bounded: "\<exists>Bd. \<forall>y \<in>
  {1 / 3..2 * lam_r}. \<bar>outer_integrand y\<bar> \<le> Bd"
proof (intro exI[of _ 100] ballI)
  fix y :: real assume y: "y \<in> {1 / 3..2 * lam_r}"
  have R0: "\<bar>R0_r y\<bar> \<le> 20" and d: "\<bar>dfun_r y\<bar> \<le> 20"
  proof -
    have y1a: "1 / 3 \<le> y" using y unfolding lam_r_def
      by presburger
    have y1b: "y \<le> 37 / 20" using y unfolding lam_r_def
      by force
    note y1 = y1a y1b
    show "\<bar>R0_r y\<bar> \<le> 20" using y1 unfolding R0_r_def pos_r_def alpha_r_def
      by argo
    show "\<bar>dfun_r y\<bar> \<le> 20" using y1 unfolding dfun_r_def pos_r_def alpha_r_def
      by fastforce
  qed
  have fl: "\<bar>of_int (floor (1 / y))\<bar> \<le> (4 :: real)"
  proof -
    have y0: "0 < y" using y
      by force
    have a: "1 / y \<le> 3" using y y0
      by (auto simp: field_simps)
    have b: "0 \<le> 1 / y" using y0
      by simp
    have c: "of_int (floor (1 / y)) \<le> 1 / y" by (rule of_int_floor_le)
    have d: "0 \<le> floor (1 / y)" using b
      by simp
    show ?thesis using a c d
      by fastforce
  qed
  have s: "\<bar>\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)\<bar> \<le> 10"
  proof -
    have t: "0 \<le> pos_r (2 * lam_r - real j * y) \<and> pos_r (2 * lam_r - real j * y) \<le> 2"
      if j: "j \<in> {1..5::nat}" for j
    proof -
      have jy: "0 \<le> real j * y" using y
        by auto
      show ?thesis using jy unfolding pos_r_def lam_r_def
        by linarith
    qed
    have "(\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y)) \<le> of_nat (card {1..5::nat}) * 2"
      using sum_bounded_above[of "{1..5::nat}" "\<lambda>j. pos_r (2 * lam_r - real j * y)" 2] t
      by blast
    moreover have "0 \<le> (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y))"
      using sum_nonneg[of "{1..5::nat}" "\<lambda>j. pos_r (2 * lam_r - real j * y)"] t
      by blast
    ultimately show ?thesis
      by simp
  qed
  show "\<bar>outer_integrand y\<bar> \<le> 100"
  proof -
    have l: "\<bar>2 * lam_r * of_int (floor (1 / y))\<bar> \<le> 8"
      using fl[unfolded abs_le_iff] unfolding abs_le_iff lam_r_def
      by linarith
    show ?thesis
      unfolding outer_integrand_def abs_le_iff
        using R0[unfolded abs_le_iff] d[unfolded abs_le_iff] l[unfolded abs_le_iff] s[unfolded
        abs_le_iff]
      by linarith
  qed
qed

end




