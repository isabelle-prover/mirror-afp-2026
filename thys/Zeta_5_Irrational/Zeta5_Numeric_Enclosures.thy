(*  Title:   Zeta5_Numeric_Enclosures.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Numeric_Enclosures
  imports Zeta5_Equilibrium_Measure "HOL-Decision_Procs.Approximation"
begin

section \<open>Numeric enclosures: (A.9), (A.10) and Lemma 6.1\<close>

text \<open>The explicit numeric inequalities of Appendix A: the sixteen-term enclosures (A.10) of
  the energy
  of \<open>\<rho>\<close> and the region check (A.9) of the potential inequality on \<open>[0,
    2]\<close>, followed by the
  statements that depend on them (Lemma 6.1, (6.4), (6.7)).  Every numeric fact is marked
  \<open>(* numeric *)\<close> and is proved
    by the @{text approximation} method of HOL-Decision\_Procs, whose
  certified interval arithmetic runs through the @{text holds} oracle of code evaluation; these 72
  facts are the only source of the oracle in the final theorem
    (@{text "thm_oracles zeta5_irrational"}
  lists only @{text holds}).  The Lean formalisation performs the same checks by kernel computation
  on 1052 dyadic intervals (Lean theories @{text Lemma61Check}, @{text Lemma61Final}).\<close>

subsection \<open>Elementary enclosures (A.10)\<close>

definition eterm :: "nat \<Rightarrow> real" where
  "eterm j = (Spart (j + 1) ^ 2 - Spart j ^ 2) * ln ((tB (table1 ! j) - tA (table1 ! j)) / 4)"

lemma eterm_0: "- 737284788112975 / 1000000000000000000 < eterm 0 \<and>
  eterm 0 < - 737284788112774 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma eterm_1: "- 8523957090042450 / 1000000000000000000 < eterm 1 \<and>
  eterm 1 < - 8523957090042249 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma eterm_2: "- 26925610911599487 / 1000000000000000000 < eterm 2 \<and>
  eterm 2 < - 26925610911599286 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma eterm_3: "- 59722954555535072 / 1000000000000000000 < eterm 3 \<and>
  eterm 3 < - 59722954555534871 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma ln_split_4: "ln (65272891657 / 4000000000000 :: real) =
  ln (65272891657 / 62500000000) - 6 * ln 2"
proof -
  have e: "(65272891657 / 4000000000000 :: real) = (65272891657 / 62500000000) / 2 ^ 6" by simp
  have d: "ln ((65272891657 / 62500000000) / 2 ^ 6 :: real) =
    ln (65272891657 / 62500000000) - ln (2 ^ 6)"
    using ln_divide_pos[of "65272891657 / 62500000000" "2 ^ 6"]
    by fastforce
  have p: "ln (2 ^ 6 :: real) = 6 * ln 2" using ln_realpow[of 2 6]
    by force
  show ?thesis unfolding e d p ..
qed

lemma eterm_4: "- 99809230236437933 / 1000000000000000000 < eterm 4 \<and>
  eterm 4 < - 99809230236429932 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  unfolding ln_split_4
  by (approximation 60) (* numeric *)

lemma eterm_5: "- 145606013686162115 / 1000000000000000000 < eterm 5 \<and>
  eterm 5 < - 145606013686161914 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma ln_split_6: "ln (144041816267 / 4000000000000 :: real) =
  ln (144041816267 / 125000000000) - 5 * ln 2"
proof -
  have e: "(144041816267 / 4000000000000 :: real) = (144041816267 / 125000000000) / 2 ^ 5" by simp
  have d: "ln ((144041816267 / 125000000000) / 2 ^ 5 :: real) =
    ln (144041816267 / 125000000000) - ln (2 ^ 5)"
    using ln_divide_pos[of "144041816267 / 125000000000" "2 ^ 5"]
    by fastforce
  have p: "ln (2 ^ 5 :: real) = 5 * ln 2" using ln_realpow[of 2 5]
    by auto
  show ?thesis unfolding e d p ..
qed

lemma eterm_6: "- 186983992097036267 / 1000000000000000000 < eterm 6 \<and>
  eterm 6 < - 186983992097028266 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  unfolding ln_split_6
  by (approximation 60) (* numeric *)

lemma eterm_7: "- 221100588014681656 / 1000000000000000000 < eterm 7 \<and>
  eterm 7 < - 221100588014681455 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma ln_split_8: "ln (269180899217 / 4000000000000 :: real) =
  ln (269180899217 / 250000000000) - 4 * ln 2"
proof -
  have e: "(269180899217 / 4000000000000 :: real) = (269180899217 / 250000000000) / 2 ^ 4" by simp
  have d: "ln ((269180899217 / 250000000000) / 2 ^ 4 :: real) =
    ln (269180899217 / 250000000000) - ln (2 ^ 4)"
    using ln_divide_pos[of "269180899217 / 250000000000" "2 ^ 4"]
    by fastforce
  have p: "ln (2 ^ 4 :: real) = 4 * ln 2" using ln_realpow[of 2 4]
    by force
  show ?thesis unfolding e d p ..
qed

lemma eterm_8: "- 241370916063655491 / 1000000000000000000 < eterm 8 \<and>
  eterm 8 < - 241370916063647490 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  unfolding ln_split_8
  by (approximation 60) (* numeric *)

lemma eterm_9: "- 247972224603869700 / 1000000000000000000 < eterm 9 \<and>
  eterm 9 < - 247972224603869499 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma eterm_10: "- 237562912254961608 / 1000000000000000000 < eterm 10 \<and>
  eterm 10 < - 237562912254961407 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma ln_split_11: "ln (128866386789 / 1000000000000 :: real) =
  ln (128866386789 / 125000000000) - 3 * ln 2"
proof -
  have e: "(128866386789 / 1000000000000 :: real) = (128866386789 / 125000000000) / 2 ^ 3" by simp
  have d: "ln ((128866386789 / 125000000000) / 2 ^ 3 :: real) =
    ln (128866386789 / 125000000000) - ln (2 ^ 3)"
    using ln_divide_pos[of "128866386789 / 125000000000" "2 ^ 3"]
    by fastforce
  have p: "ln (2 ^ 3 :: real) = 3 * ln 2" using ln_realpow[of 2 3]
    by fastforce
  show ?thesis unfolding e d p ..
qed

lemma eterm_11: "- 216269698612393279 / 1000000000000000000 < eterm 11 \<and>
  eterm 11 < - 216269698612385278 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  unfolding ln_split_11
  by (approximation 60) (* numeric *)

lemma eterm_12: "- 182633164362425959 / 1000000000000000000 < eterm 12 \<and>
  eterm 12 < - 182633164362425758 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma eterm_13: "- 138201939148464454 / 1000000000000000000 < eterm 13 \<and>
  eterm 13 < - 138201939148464253 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma eterm_14: "- 94725877510899352 / 1000000000000000000 < eterm 14 \<and>
  eterm 14 < - 94725877510899151 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma eterm_15: "- 18447081210789815 / 1000000000000000000 < eterm 15 \<and>
  eterm 15 < - 18447081210789614 / 1000000000000000000"
  unfolding eterm_def
  apply (simp add: Spart_def table1_def tA_def tB_def tC_def)
  by (approximation 80) (* numeric *)

lemma logEnergy_eterm: "logEnergy rho = (\<Sum> j < 16. eterm j)"
  unfolding logEnergy_explicit eterm_def ..

theorem enclosures_A10:
  "- 2126593445148 / 10 ^ 12 < logEnergy rho \<and> logEnergy rho < - 2126593445147 / 10 ^ 12 \<and>
   2653035990340 / 10 ^ 12 < Cstar \<and> Cstar < 2653035990341 / 10 ^ 12"
proof -
  have I: "- 2126593445148 / 10 ^ 12 < logEnergy rho \<and>
    logEnergy rho < - 2126593445147 / 10 ^ 12"
  proof -
    have lo: "- 2126593445148 / 1000000000000 < logEnergy rho" unfolding logEnergy_eterm sum16
      using eterm_0[THEN conjunct1] eterm_1[THEN conjunct1] eterm_2[THEN conjunct1] eterm_3[THEN
      conjunct1] eterm_4[THEN conjunct1] eterm_5[THEN conjunct1] eterm_6[THEN conjunct1]
      eterm_7[THEN conjunct1] eterm_8[THEN conjunct1] eterm_9[THEN conjunct1] eterm_10[THEN
      conjunct1] eterm_11[THEN conjunct1] eterm_12[THEN conjunct1] eterm_13[THEN conjunct1]
      eterm_14[THEN conjunct1] eterm_15[THEN conjunct1]
      by linarith
    have hi: "logEnergy rho < - 2126593445147 / 1000000000000" unfolding logEnergy_eterm sum16
      using eterm_0[THEN conjunct2] eterm_1[THEN conjunct2] eterm_2[THEN conjunct2] eterm_3[THEN
      conjunct2] eterm_4[THEN conjunct2] eterm_5[THEN conjunct2] eterm_6[THEN conjunct2]
      eterm_7[THEN conjunct2] eterm_8[THEN conjunct2] eterm_9[THEN conjunct2] eterm_10[THEN
      conjunct2] eterm_11[THEN conjunct2] eterm_12[THEN conjunct2] eterm_13[THEN conjunct2]
      eterm_14[THEN conjunct2] eterm_15[THEN conjunct2]
      by linarith
    show ?thesis using lo hi
      by auto
  qed \<comment> \<open>evaluate the sixteen summands symbolically:
    @{text "simp add: table1_def Spart_def tA_def tB_def tC_def"} leaves an expression in
    @{text "ln"} of explicit rationals;
      then the numeric fact by @{text "approximation 120"} (* numeric *) -
        Lean proves the same enclosures from 22 terms of the atanh series
        (@{text "log_series_bounds"}) per logarithm; that route (bounds by simp on rationals) is the
      kernel-only alternative if @{text approximation} is too slow: 19 logarithms,
        each via @{text "log_series_bounds"} [of z 22] with @{text "z = (y - 1)/(y + 1)"},
        @{text "y = (b-a)/4 \<cdot> 2^e \<in> (1, 2)"}, and ln 2 (z = 1/3)\<close>
  have C: "2653035990340 / 10 ^ 12 < Cstar \<and> Cstar < 2653035990341 / 10 ^ 12"
    unfolding Cstar_def lam_r_def alpha_r_def
    by (approximation 60) (* numeric *) \<comment> \<open>@{text "approximation 80"} (* numeric *)
      on the explicit expression in @{text "ln (3/40)"} and @{text "ln (37/20)"};
      or @{text "log_series_bounds"} with @{text "ln (3/40) = ln (6/5) - 4 ln 2"} (z =
      1/11) and @{text "ln (37/20)"} (z = 17/57)\<close>
  show ?thesis using I C by simp
qed

subsection \<open>(A.9): the region check on [0, 2]\<close>

text \<open>(A.9) on @{text "[0, 2]"}.  Lean checks 1052 dyadic intervals with certified rational
  bounds for @{text "\<surd>, log, arctan"}
  (@{text "decide +kernel"}).  Isabelle route: @{text "2 U^\<rho>(t) - V(t)"} is an explicit
    expression in @{text "ln, sqrt, arctan"} of @{text t}
  on each of the 33 regions cut out by the table endpoints
    @{text "a_16 < \<dots> < a_1 < b_1 < \<dots> < b_16"} (@{text "Uk_eq"}, @{text "Vf_closed"});
    on each region the
  inequality @{text "\<forall>t \<in> [l, r]. expr(t) \<le> Bd"} is proved
    by @{text "approximation N (splitting: t = k)"} (* numeric *).\<close>
lemma Uk_max:
  assumes k: "k < 16"
  shows "Uk k t = ln (max ((tB (table1 ! k) - tA (table1 ! k)) / 4)
           ((\<bar>t - (tA (table1 ! k) + tB (table1 ! k)) / 2\<bar> + sqrt (max 0 ((t -
             tA (table1 ! k)) * (t - tB (table1 ! k))))) / 2))"
proof -
  define a where "a = tA (table1 ! k)"
  define b where "b = tB (table1 ! k)"
  have ab: "a < b" using table1_nth[OF k] unfolding a_def b_def by auto
  show ?thesis
  proof (cases "a \<le> t \<and> t \<le> b")
    case True
    have p: "(t - a) * (t - b) \<le> 0" using True by (simp add: mult_nonneg_nonpos)
    have m: "\<bar>t - (a + b) / 2\<bar> / 2 \<le> (b - a) / 4" using True
      using abs_le_iff by argo
    have e1: "max 0 ((t - a) * (t - b)) = 0" using p by simp
    have e2: "max ((b - a) / 4) ((\<bar>t - (a + b) / 2\<bar> + sqrt 0) / 2) = (b - a) / 4" using m
      by simp
    have "Uk k t = Lk k" using Uk_const[OF k] True unfolding a_def b_def by blast
    thus ?thesis unfolding Lk_def a_def[symmetric] b_def[symmetric] e1 e2
      by meson
  next
    case False
    have p: "0 \<le> (t - a) * (t - b)" using False ab
      by (fastforce intro: mult_nonneg_nonneg mult_nonpos_nonpos)
    have far: "(b - a) / 2 \<le> \<bar>t - (a + b) / 2\<bar>" using False by argo
    have e1: "max 0 ((t - a) * (t - b)) = (t - a) * (t - b)" using p by simp
    have e2: "max ((b - a) / 4) ((\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2) =
      (\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2"
      using far real_sqrt_ge_zero[OF p]
      using max_def by argo
    have "Uk k t = ln ((\<bar>t - (a + b) / 2\<bar> + sqrt ((t - a) * (t - b))) / 2)"
      using Uk_eq[OF k, of t] False unfolding a_def b_def by presburger
    thus ?thesis unfolding a_def[symmetric] b_def[symmetric] e1 e2
      by meson
  qed
qed

definition Vc :: "real \<Rightarrow> real" where
  "Vc t = 2 * pi * sqrt t + (ln (t + 1) - 2 + 2 * sqrt t * (pi / 2 - arctan (sqrt t)))
          - 6 * (3 / 40 * ln (t + (3 / 40) ^ 2) - 2 * (3 / 40) + 2 * sqrt t * (pi / 2 -
            arctan (sqrt t / (3 / 40))))"

lemma Vf_Vc: assumes "0 \<le> t" shows "Vf t = Vc t"
proof (cases "t = 0")
  case True
  have l: "ln ((3 / 40 :: real) ^ 2) = 2 * ln (3 / 40)" by (simp add: ln_realpow)
  show ?thesis unfolding True Vf_zero Vc_def using l
    by (simp add: algebra_simps)
next
  case False
  hence t0: "0 < t" using assms by simp
  have s0: "0 < sqrt t" using t0 by simp
  have a1: "arctan (1 / sqrt t) = pi / 2 - arctan (sqrt t)" using arctan_inverse[of "sqrt t"] s0
    by (simp add: inverse_eq_divide)
  have pos: "0 < sqrt t / (3 / 40)" using s0 by simp
  have inv: "inverse (sqrt t / (3 / 40)) = 3 / 40 / sqrt t"
    by simp
  have a2: "arctan (3 / 40 / sqrt t) = pi / 2 - arctan (sqrt t / (3 / 40))"
    using arctan_inverse[of "sqrt t / (3 / 40)"] pos unfolding inv
    by fast
  show ?thesis unfolding Vf_closed[OF t0] Vc_def a1 a2 ..
qed

definition Eb :: "real \<Rightarrow> real" where
  "Eb t = 2 * (10515596180 / 1000000000000 * ln (max (5085947445 / 4000000000000) ((\<bar>t -
    12899443617 / 2000000000000\<bar> + sqrt (max 0 ((t - 3906748086 / 1000000000000) * (t -
    8992695531 / 1000000000000)))) / 2)) +
      29471737793 / 1000000000000 * ln (max (13028749591 / 4000000000000) ((\<bar>t - 17653246119 /
        2000000000000\<bar> + sqrt (max 0 ((t - 2312248264 / 1000000000000) * (t - 15340997855 /
        1000000000000)))) / 2)) +
      42934365099 / 1000000000000 * ln (max (24327894059 / 4000000000000) ((\<bar>t - 27132467389 /
        2000000000000\<bar> + sqrt (max 0 ((t - 1402286665 / 1000000000000) * (t - 25730180724 /
        1000000000000)))) / 2)) +
      58204231966 / 1000000000000 * ln (max (41027852890 / 4000000000000) ((\<bar>t - 42791303602 /
        2000000000000\<bar> + sqrt (max 0 ((t - 881725356 / 1000000000000) * (t - 41909578246 /
        1000000000000)))) / 2)) +
      69037621310 / 1000000000000 * ln (max (65272891657 / 4000000000000) ((\<bar>t - 66429287469 /
        2000000000000\<bar> + sqrt (max 0 ((t - 578197906 / 1000000000000) * (t - 65851089563 /
        1000000000000)))) / 2)) +
      78873099189 / 1000000000000 * ln (max (99084713271 / 4000000000000) ((\<bar>t - 99877362497 /
        2000000000000\<bar> + sqrt (max 0 ((t - 396324613 / 1000000000000) * (t - 99481037884 /
        1000000000000)))) / 2)) +
      84856120711 / 1000000000000 * ln (max (144041816267 / 4000000000000) ((\<bar>t -
        144609638649 / 2000000000000\<bar> + sqrt (max 0 ((t - 283911191 / 1000000000000) * (t -
        144325727458 / 1000000000000)))) / 2)) +
      88396082127 / 1000000000000 * ln (max (200893556541 / 4000000000000) ((\<bar>t -
        201317968917 / 2000000000000\<bar> + sqrt (max 0 ((t - 212206188 / 1000000000000) * (t -
        201105762729 / 1000000000000)))) / 2)) +
      88303382125 / 1000000000000 * ln (max (269180899217 / 4000000000000) ((\<bar>t -
        269511094589 / 2000000000000\<bar> + sqrt (max 0 ((t - 165097686 / 1000000000000) * (t -
        269345996903 / 1000000000000)))) / 2)) +
      85472321255 / 1000000000000 * ln (max (346956207024 / 4000000000000) ((\<bar>t -
        347222901288 / 2000000000000\<bar> + sqrt (max 0 ((t - 133347132 / 1000000000000) * (t -
        347089554156 / 1000000000000)))) / 2)) +
      78899184238 / 1000000000000 * ln (max (430695182301 / 4000000000000) ((\<bar>t -
        430918226529 / 2000000000000\<bar> + sqrt (max 0 ((t - 111522114 / 1000000000000) * (t -
        430806704415 / 1000000000000)))) / 2)) +
      70353471918 / 1000000000000 * ln (max (515465547156 / 4000000000000) ((\<bar>t -
        515658245866 / 2000000000000\<bar> + sqrt (max 0 ((t - 96349355 / 1000000000000) * (t -
        515561896511 / 1000000000000)))) / 2)) +
      58838976615 / 1000000000000 * ln (max (595362962907 / 4000000000000) ((\<bar>t -
        595534594185 / 2000000000000\<bar> + sqrt (max 0 ((t - 85815639 / 1000000000000) * (t -
        595448778546 / 1000000000000)))) / 2)) +
      44421321106 / 1000000000000 * ln (max (664162715772 / 4000000000000) ((\<bar>t -
        664320051194 / 2000000000000\<bar> + sqrt (max 0 ((t - 78667711 / 1000000000000) * (t -
        664241383483 / 1000000000000)))) / 2)) +
      30462865791 / 1000000000000 * ln (max (716086447547 / 4000000000000) ((\<bar>t -
        716234706677 / 2000000000000\<bar> + sqrt (max 0 ((t - 74129565 / 1000000000000) * (t -
        716160577112 / 1000000000000)))) / 2)) +
      5959622577 / 1000000000000 * ln (max (746565554359 / 4000000000000) ((\<bar>t - 746709036979 /
        2000000000000\<bar> + sqrt (max 0 ((t - 71741310 / 1000000000000) * (t - 746637295669 /
        1000000000000)))) / 2))) - Vc t"

lemma Eb_eq: assumes "0 \<le> t" shows "2 * logPot rho t - Vf t = Eb t"
  by (simp add: logPot_rho Vf_Vc[OF assms] sum16 Uk_max cK_def table1_def tA_def tB_def tC_def
    Eb_def)

lemma Eb_R29: "595448778546 / 1000000000000 \<le> t \<and>
  t \<le> 664241383483 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R28: "515561896511 / 1000000000000 \<le> t \<and>
  t \<le> 595448778546 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R30: "664241383483 / 1000000000000 \<le> t \<and>
  t \<le> 716160577112 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R23: "144325727458 / 1000000000000 \<le> t \<and>
  t \<le> 201105762729 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R24: "201105762729 / 1000000000000 \<le> t \<and>
  t \<le> 269345996903 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R25: "269345996903 / 1000000000000 \<le> t \<and>
  t \<le> 347089554156 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R26: "347089554156 / 1000000000000 \<le> t \<and>
  t \<le> 430806704415 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R27: "430806704415 / 1000000000000 \<le> t \<and>
  t \<le> 515561896511 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R31: "716160577112 / 1000000000000 \<le> t \<and>
  t \<le> 746637295669 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R16: "3906748086 / 1000000000000 \<le> t \<and>
  t \<le> 8992695531 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R18: "15340997855 / 1000000000000 \<le> t \<and>
  t \<le> 25730180724 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R19: "25730180724 / 1000000000000 \<le> t \<and>
  t \<le> 41909578246 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R20: "41909578246 / 1000000000000 \<le> t \<and>
  t \<le> 65851089563 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R21: "65851089563 / 1000000000000 \<le> t \<and>
  t \<le> 99481037884 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R22: "99481037884 / 1000000000000 \<le> t \<and>
  t \<le> 144325727458 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_Q0: "8992695531 / 1000000000000 \<le> t \<and>
  t \<le> 9786233321 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 7) (* numeric *)

lemma Eb_Q2: "10579771112 / 1000000000000 \<le> t \<and>
  t \<le> 11373308902 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 7) (* numeric *)

lemma Eb_Q3: "11373308902 / 1000000000000 \<le> t \<and>
  t \<le> 12166846693 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 7) (* numeric *)

lemma Eb_P0: "9786233321 / 1000000000000 \<le> t \<and>
  t \<le> 9984617768 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 6) (* numeric *)

lemma Eb_P2: "10183002216 / 1000000000000 \<le> t \<and>
  t \<le> 10381386664 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 6) (* numeric *)

lemma Eb_P3: "10381386664 / 1000000000000 \<le> t \<and>
  t \<le> 10579771112 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 6) (* numeric *)

lemma ln_shift64: assumes "0 \<le> t" shows "ln (t + (3 / 40) ^ 2) =
  ln (64 * (t + (3 / 40) ^ 2)) - 6 * ln (2 :: real)"
proof -
  have p: "0 < t + (3 / 40 :: real) ^ 2" using assms by (simp add: add_nonneg_pos)
  have "ln (64 * (t + (3 / 40) ^ 2)) = ln 64 + ln (t + (3 / 40 :: real) ^ 2)"
    using ln_mult[of 64 "t + (3 / 40) ^ 2"] p
    by force
  moreover have "ln (64 :: real) = 6 * ln 2" using ln_realpow[of 2 6]
    by auto
  ultimately show ?thesis by simp
qed

lemma Eb_P1: "9984617768 / 1000000000000 \<le> t \<and>
  t \<le> 10183002216 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
proof -
  assume h: "9984617768 / 1000000000000 \<le> t \<and> t \<le> 10183002216 / 1000000000000"
  have e: "ln (t + (3 / 40) ^ 2) = ln (64 * (t + (3 / 40) ^ 2)) - 6 * ln (2 :: real)" using h
    by (intro ln_shift64) simp
  show ?thesis unfolding Eb_def Vc_def e using h
    by (approximation 30 splitting: t = 6) (* numeric *)
qed

lemma Eb_T17b: "12166846693 / 1000000000000 \<le> t \<and>
  t \<le> 15340997855 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_R11: "396324613 / 1000000000000 \<le> t \<and>
  t \<le> 578197906 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R12: "578197906 / 1000000000000 \<le> t \<and>
  t \<le> 881725356 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R13: "881725356 / 1000000000000 \<le> t \<and>
  t \<le> 1402286665 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R14: "1402286665 / 1000000000000 \<le> t \<and>
  t \<le> 2312248264 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 7) (* numeric *)

lemma Eb_R15: "2312248264 / 1000000000000 \<le> t \<and>
  t \<le> 3906748086 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 6) (* numeric *)

lemma Eb_R0: "0 \<le> t \<and> t \<le> 71741310 / 1000000000000 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R1: "71741310 / 1000000000000 \<le> t \<and>
  t \<le> 74129565 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R2: "74129565 / 1000000000000 \<le> t \<and>
  t \<le> 78667711 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R3: "78667711 / 1000000000000 \<le> t \<and>
  t \<le> 85815639 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R4: "85815639 / 1000000000000 \<le> t \<and>
  t \<le> 96349355 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R5: "96349355 / 1000000000000 \<le> t \<and>
  t \<le> 111522114 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R6: "111522114 / 1000000000000 \<le> t \<and>
  t \<le> 133347132 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R7: "133347132 / 1000000000000 \<le> t \<and>
  t \<le> 165097686 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R8: "165097686 / 1000000000000 \<le> t \<and>
  t \<le> 212206188 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R9: "212206188 / 1000000000000 \<le> t \<and>
  t \<le> 283911191 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_R10: "283911191 / 1000000000000 \<le> t \<and>
  t \<le> 396324613 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 5) (* numeric *)

lemma Eb_S0: "746637295669 / 1000000000000 \<le> t \<and>
  t \<le> 800000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S1: "800000000000 / 1000000000000 \<le> t \<and>
  t \<le> 900000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S2: "900000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1000000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S3: "1000000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1100000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S4: "1100000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1200000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S5: "1200000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1300000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S6: "1300000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1400000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S7: "1400000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1500000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S8: "1500000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1600000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S9: "1600000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1700000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S10: "1700000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1800000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S11: "1800000000000 / 1000000000000 \<le> t \<and>
  t \<le> 1900000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_S12: "1900000000000 / 1000000000000 \<le> t \<and>
  t \<le> 2000000000000 / 1000000000000 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  unfolding Eb_def Vc_def
  by (approximation 30 splitting: t = 9) (* numeric *)

lemma Eb_from_51: "1900000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S12[of t] by linarith

lemma Eb_from_50: "1800000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S11[of t] Eb_from_51[of t] by linarith

lemma Eb_from_49: "1700000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S10[of t] Eb_from_50[of t] by linarith

lemma Eb_from_48: "1600000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S9[of t] Eb_from_49[of t] by linarith

lemma Eb_from_47: "1500000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S8[of t] Eb_from_48[of t] by linarith

lemma Eb_from_46: "1400000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S7[of t] Eb_from_47[of t] by linarith

lemma Eb_from_45: "1300000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S6[of t] Eb_from_46[of t] by linarith

lemma Eb_from_44: "1200000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S5[of t] Eb_from_45[of t] by linarith

lemma Eb_from_43: "1100000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S4[of t] Eb_from_44[of t] by linarith

lemma Eb_from_42: "1000000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S3[of t] Eb_from_43[of t] by linarith

lemma Eb_from_41: "900000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S2[of t] Eb_from_42[of t] by linarith

lemma Eb_from_40: "800000000000 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S1[of t] Eb_from_41[of t] by linarith

lemma Eb_from_39: "746637295669 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_S0[of t] Eb_from_40[of t] by linarith

lemma Eb_from_38: "716160577112 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R31[of t] Eb_from_39[of t] by linarith

lemma Eb_from_37: "664241383483 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R30[of t] Eb_from_38[of t] by linarith

lemma Eb_from_36: "595448778546 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R29[of t] Eb_from_37[of t] by linarith

lemma Eb_from_35: "515561896511 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R28[of t] Eb_from_36[of t] by linarith

lemma Eb_from_34: "430806704415 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R27[of t] Eb_from_35[of t] by linarith

lemma Eb_from_33: "347089554156 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R26[of t] Eb_from_34[of t] by linarith

lemma Eb_from_32: "269345996903 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R25[of t] Eb_from_33[of t] by linarith

lemma Eb_from_31: "201105762729 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R24[of t] Eb_from_32[of t] by linarith

lemma Eb_from_30: "144325727458 / 1000000000000 \<le> t \<Longrightarrow>
  t \<le> 2 \<Longrightarrow> Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R23[of t] Eb_from_31[of t] by linarith

lemma Eb_from_29: "99481037884 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R22[of t] Eb_from_30[of t] by linarith

lemma Eb_from_28: "65851089563 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R21[of t] Eb_from_29[of t] by linarith

lemma Eb_from_27: "41909578246 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R20[of t] Eb_from_28[of t] by linarith

lemma Eb_from_26: "25730180724 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R19[of t] Eb_from_27[of t] by linarith

lemma Eb_from_25: "15340997855 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R18[of t] Eb_from_26[of t] by linarith

lemma Eb_from_24: "12166846693 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_T17b[of t] Eb_from_25[of t] by linarith

lemma Eb_from_23: "11373308902 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_Q3[of t] Eb_from_24[of t] by linarith

lemma Eb_from_22: "10579771112 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_Q2[of t] Eb_from_23[of t] by linarith

lemma Eb_from_21: "10381386664 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_P3[of t] Eb_from_22[of t] by linarith

lemma Eb_from_20: "10183002216 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_P2[of t] Eb_from_21[of t] by linarith

lemma Eb_from_19: "9984617768 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_P1[of t] Eb_from_20[of t] by linarith

lemma Eb_from_18: "9786233321 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_P0[of t] Eb_from_19[of t] by linarith

lemma Eb_from_17: "8992695531 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_Q0[of t] Eb_from_18[of t] by linarith

lemma Eb_from_16: "3906748086 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R16[of t] Eb_from_17[of t] by linarith

lemma Eb_from_15: "2312248264 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R15[of t] Eb_from_16[of t] by linarith

lemma Eb_from_14: "1402286665 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R14[of t] Eb_from_15[of t] by linarith

lemma Eb_from_13: "881725356 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R13[of t] Eb_from_14[of t] by linarith

lemma Eb_from_12: "578197906 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R12[of t] Eb_from_13[of t] by linarith

lemma Eb_from_11: "396324613 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R11[of t] Eb_from_12[of t] by linarith

lemma Eb_from_10: "283911191 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R10[of t] Eb_from_11[of t] by linarith

lemma Eb_from_9: "212206188 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R9[of t] Eb_from_10[of t] by linarith

lemma Eb_from_8: "165097686 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R8[of t] Eb_from_9[of t] by linarith

lemma Eb_from_7: "133347132 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R7[of t] Eb_from_8[of t] by linarith

lemma Eb_from_6: "111522114 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R6[of t] Eb_from_7[of t] by linarith

lemma Eb_from_5: "96349355 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R5[of t] Eb_from_6[of t] by linarith

lemma Eb_from_4: "85815639 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R4[of t] Eb_from_5[of t] by linarith

lemma Eb_from_3: "78667711 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R3[of t] Eb_from_4[of t] by linarith

lemma Eb_from_2: "74129565 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R2[of t] Eb_from_3[of t] by linarith

lemma Eb_from_1: "71741310 / 1000000000000 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R1[of t] Eb_from_2[of t] by linarith

lemma Eb_from_0: "0 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  Eb t \<le> - 66451 / 10 ^ 4"
  using Eb_R0[of t] Eb_from_1[of t] by linarith

lemma potential_bound_0_2: "0 \<le> t \<Longrightarrow> t \<le> 2 \<Longrightarrow>
  2 * logPot rho t - Vf t \<le> - 66451 / 10 ^ 4"
  using Eb_eq[of t] Eb_from_0[of t]
  by linarith

text \<open>(A.9) with (6.8): @{text "2U^\<rho>(t) - V(t) < -6645002/10^6 < M_0"}
  for @{text "t \<ge> 0"}.\<close>
theorem potential_A9: "0 \<le> t \<Longrightarrow> 2 * logPot rho t - Vf t < - 6645002 / 10 ^ 6"
proof -
  assume t: "0 \<le> t"
  show "2 * logPot rho t - Vf t < - 6645002 / 10 ^ 6"
  proof (cases "t \<le> 2")
    case True
    thus ?thesis using potential_bound_0_2[OF t True] by simp
  next
    case False
    thus ?thesis by (intro tail_bound) simp
  qed
qed

text \<open>(6.4).\<close>
theorem rho_energy_bound: "lam_r * of_rat M0c - logEnergy rho + Cstar \<le> of_rat Ubar"
  using enclosures_A10 by (simp add: lam_r_def M0c_def Ubar_def of_rat_divide of_rat_minus)

text \<open>Lemma 6.1: @{text \<rho>} has mass @{text \<lambda>}, is supported in @{text "(0, 2)"},
  satisfies (6.2) and (6.4).\<close>
theorem rho_properties:
  "emeasure rho UNIV = ennreal lam_r \<and> emeasure rho (- {0<..<2}) = 0 \<and>
   (\<forall>t. 0 \<le> t \<longrightarrow> 2 * logPot rho t - Vf t \<le> of_rat M0c) \<and>
   lam_r * of_rat M0c - logEnergy rho + Cstar \<le> of_rat Ubar"
proof (intro conjI allI impI)
  fix t :: real assume "0 \<le> t"
  hence "2 * logPot rho t - Vf t < - 6645002 / 10 ^ 6" by (rule potential_A9)
  thus "2 * logPot rho t - Vf t \<le> of_rat M0c" by (simp add: M0c_def of_rat_divide of_rat_minus)
qed (simp_all add: rho_univ rho_compl rho_energy_bound)

subsection \<open>(6.9) ingredient\<close>

text \<open>(6.7): @{text "2U^\<rho>(t) - V(t) + \<surd>t/K \<le> M_0 + \<surd>2/K"}
  for @{text "t \<ge> 0"}, @{text "K \<ge> 40"}.\<close>
lemma field_bound: "40 \<le> K \<Longrightarrow> 0 \<le> t \<Longrightarrow>
  2 * logPot rho t - Vf t + sqrt t / K \<le> of_rat M0c + sqrt 2 / K"
proof -
  assume K: "40 \<le> K" and t: "0 \<le> t"
  show ?thesis
  proof (cases "t \<le> 2")
    case True
    have "2 * logPot rho t - Vf t \<le> of_rat M0c" using potential_A9[OF t]
      by (simp add: M0c_def of_rat_divide of_rat_minus)
    moreover have "sqrt t / K \<le> sqrt 2 / K" using True K
      by (intro divide_right_mono real_sqrt_le_mono) auto
    ultimately show ?thesis by linarith
  next
    case False
    hence t2: "2 \<le> t" by simp
    have U: "logPot rho t \<le> lam_r * ln t" by (rule logPot_le_of_two_le[OF t2])
    have V: "2 * pi * sqrt t + (1 - 6 * alpha_r) * ln t - 2 * alpha_r ^ 3 / t \<le> Vf t"
      by (rule V_lower[OF t2])
    define s where "s = sqrt t"
    have t0: "0 < t" using t2 by simp
    have s0: "0 < s" using t0 unfolding s_def by simp
    have s2: "sqrt 2 \<le> s" unfolding s_def using t2 real_sqrt_le_mono by blast
    have r2: "1.4 \<le> sqrt (2::real)" using real_le_rsqrt[of "1.4" 2]
      by (simp add: power2_eq_square)
    have lt: "ln t \<le> 2 * (s - 1)"
    proof -
      have "ln t = 2 * ln s" unfolding s_def using ln_sqrt[of t] t0 by linarith
      moreover have "ln s \<le> s - 1" using ln_le_minus_one[OF s0] .
      ultimately show ?thesis by simp
    qed
    have a3: "2 * alpha_r ^ 3 / t \<le> alpha_r ^ 3" using t2 unfolding alpha_r_def
      by (simp add: field_simps)
    have sK: "s / K \<le> s / 40" using K s0
      by (fastforce intro: divide_left_mono)
    have K0: "0 \<le> sqrt 2 / K" using K
      by simp
    have M: "of_rat M0c = (- 1329 / 200 :: real)" unfolding M0c_def
      by (simp add: of_rat_divide of_rat_minus)
    have pis: "3 * s \<le> pi * s" using pi_gt3 s0
      by simp
    have c3: "(3 / 40 :: real) ^ 3 = 27 / 64000" by (simp add: power3_eq_cube)
    show ?thesis unfolding M s_def[symmetric] using U V lt a3 sK K0 pis s2 r2
      unfolding lam_r_def alpha_r_def s_def[symmetric]
      using c3
      by argo
  qed
qed







end
