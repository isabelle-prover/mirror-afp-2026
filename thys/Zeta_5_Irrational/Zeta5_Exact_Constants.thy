(*  Title:   Zeta5_Exact_Constants.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Exact_Constants
  imports Zeta5_Definitions
begin

section \<open>Exact rational constants\<close>

text \<open>Appendix B of the paper: the exact rational values of \<open>A\<^sup>*\<close>,
  \<open>A\<^sub>M\<close> and the margins in (7.2),
  by rational arithmetic (Lean theory @{text AppendixB}).\<close>

lemma Hc_eq: "Hc_q = 23 / 20" by (simp add: Hc_q_def alpha_q_def)

text \<open>The cancellation of the quadratic coefficient of @{text R} (Appendix B.1).\<close>
lemma quadratic_cancellation:
  "2 * lam_q - 12 * lam_q * alpha_q + 2 * (Hc_q ^ 2 - Hc_q - lam_q ^ 2) - 18 * alpha_q ^ 2 + 6 *
    alpha_q = 0" by (simp add: lam_q_def alpha_q_def Hc_q_def power2_eq_square)

lemma lam_M0: "lam_q * M0c = - 49173 / 8000" by (simp add: lam_q_def M0c_def)

text \<open>(5.19): @{text "A* = I_out + \<integral>\<^sub>3^{20} R/x^3 - 2689/48000"}.\<close>
lemma Astar_eq: "Astar = Iout + 322437603634266857629 / 7535670527041937280000 - 2689 / 48000"
  by (simp add: Astar_def Iout_def)

lemma A200_eq: "AM 200 = 127125602969131786927559 / 94195881588024216000000"
  by (simp add: AM_def Astar_def lam_q_def)

lemma A100000_eq: "AM 100000 = 7756864096839411316755964319057 / 5887242599251513500000000000000"
  by (simp add: AM_def Astar_def lam_q_def)

text \<open>(7.2), @{text "M = 200"}: @{text "-1600(A\<^sub>2_0_0 + Ubar) > 139/5"},
  with the exact margin.\<close>
lemma margin_200:
  "- 1600 * (AM 200 + Ubar) - 139 / 5 = 3089837638249482469 / 58872425992515135000 \<and>
   139 / 5 < - 1600 * (AM 200 + Ubar)" by (simp add: AM_def Astar_def lam_q_def Ubar_def)

text \<open>(7.2), @{text "M = 100000"}: @{text "-1600(A_1_0_0_0_0_0 + Ubar) > 7907/100"}.\<close>
lemma margin_100000:
  "- 1600 * (AM 100000 + Ubar) - 7907 / 100 =
    29873543950273155160680943 / 3679526624532195937500000000 \<and>
   7907 / 100 < - 1600 * (AM 100000 + Ubar)" by (simp add: AM_def Astar_def lam_q_def Ubar_def)

text \<open>(6.4): @{text "Ubar < -136699/100000"}.\<close>
lemma U_lt: "Ubar < - 136699 / 100000" by (simp add: Ubar_def)

end
