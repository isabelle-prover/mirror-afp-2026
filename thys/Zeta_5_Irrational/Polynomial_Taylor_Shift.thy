(*  Title:   Polynomial_Taylor_Shift.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Polynomial_Taylor_Shift
  imports Rational_Padic_Valuations
begin

section \<open>Taylor coefficients of a rational polynomial at a point\<close>

text \<open>@{text "tay P r i"} is the coefficient of \<open>X\<^sup>i\<close> in \<open>P(X +
  r)\<close>.  Linearity, the binomial formula
  for monomials, the behaviour under multiplication
    by \<open>(X - r)\<^sup>n\<close>, and \<open>p\<close>-integrality of the
  Taylor coefficients of a \<open>p\<close>-integral polynomial at a \<open>p\<close>-integral
    point.\<close>

text \<open>The @{text i}-th Taylor coefficient of @{text P} at @{text r}:
  @{text "P(X + r) = \<Sum>_i tay P r i X^i"}.\<close>
definition tay :: "rat poly \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> rat" where
  "tay P r i = Polynomial.coeff (pcompose P (pX + [:r:])) i"

lemma tay_add: "tay (P + Q) r i = tay P r i + tay Q r i"
  by (simp add: tay_def pcompose_add)

lemma tay_smult: "tay (Polynomial.smult c P) r i = c * tay P r i"
  by (simp add: tay_def pcompose_smult)

lemma tay_shift_lib: "pcompose ((pX - [:r:]) ^ n * Q) (pX + [:r:]) =
  Polynomial.monom 1 n * pcompose Q (pX + [:r:])"
proof -
  have a: "pcompose (pX - [:r:]) (pX + [:r:]) = pX" using pcompose_diff pcompose_pX pcompose_const
    by (simp add: pcompose_diff pcompose_pX)
  have b: "(pX :: rat poly) ^ n = Polynomial.monom 1 n"  by (simp add: monom_power)
  show ?thesis unfolding pcompose_mult pcompose_power_left a b  by simp
qed

lemma tay_sum: "tay (\<Sum> d \<in> I. f d) r i = (\<Sum> d \<in> I. tay (f d) r i)"
   by (simp add: tay_def pcompose_sum coeff_sum)

lemma tay_pX_pow: "tay (pX ^ d) r i = (if i \<le> d then of_nat (d choose i) * r ^ (d - i) else 0)"
proof -
  have c: "pX + [:r:] = [:r, 1:]"  by (simp add: monom_Suc)
  have e: "tay (pX ^ d) r i = Polynomial.coeff ([:r, 1:] ^ d) i"
    unfolding tay_def pcompose_power_left pcompose_pX c  by simp
  show ?thesis
  proof (cases "i \<le> d")
    case True
    thus ?thesis unfolding e using coeff_linear_poly_power[OF True, of r "1::rat"]  by simp
  next
    case False
    have dg: "degree ([:r, 1:] ^ d) < i" using degree_power_le[of "[:r, 1:]" d] False by simp
    have "Polynomial.coeff ([:r, 1:] ^ d) i = 0" using coeff_eq_0[OF dg] by blast
    thus ?thesis unfolding e using False by simp
  qed
qed

lemma tay_eq_sum: "degree P < h \<Longrightarrow>
  tay P r i = (\<Sum> d < h. Polynomial.coeff P d * tay (pX ^ d) r i)"
proof -
  assume dg: "degree P < h"
  have m: "Polynomial.monom c d = Polynomial.smult c (pX ^ d)" for c :: rat and d
    using smult_monom monom_power  by (simp add: smult_monom monom_power)
  have s1: "(\<Sum> d \<le> h - 1. Polynomial.monom (Polynomial.coeff P d) d) = P"
    using poly_as_sum_of_monoms'[of P "h - 1"] dg  by simp
  have s2: "{..h - 1} = {..<h}" using dg  by auto
  have s3: "(\<Sum> d < h. Polynomial.monom (Polynomial.coeff P d) d) = P" using s1 unfolding s2
    by blast
  have e: "P = (\<Sum> d < h. Polynomial.smult (Polynomial.coeff P d) (pX ^ d))"
    unfolding m[symmetric] using s3[symmetric] by blast
  have "tay P r i = tay (\<Sum> d < h. Polynomial.smult (Polynomial.coeff P d) (pX ^ d)) r i"
    using arg_cong[where f = "\<lambda>Q. tay Q r i", OF e]  by simp
  also have "\<dots> = (\<Sum> d < h. Polynomial.coeff P d * tay (pX ^ d) r i)"
    unfolding tay_sum tay_smult  by simp
  finally show ?thesis .
qed

lemma tay_0_eq_poly: "tay P r 0 = poly P r"
  unfolding tay_def using poly_0_coeff_0[symmetric] poly_pcompose poly_monom  by simp

text \<open>@{text "(X - r)^n Q"} has vanishing Taylor coefficients of order @{text "< n"} at
  @{text r}, and the shifted ones are those of @{text Q}.\<close>
lemma tay_pow_mult: "tay ((pX - [:r:]) ^ n * Q) r (n + i) = tay Q r i"
  unfolding tay_def tay_shift_lib coeff_monom_mult  by simp

lemma tay_pow_mult_lt: "i < n \<Longrightarrow> tay ((pX - [:r:]) ^ n * Q) r i = 0"
  unfolding tay_def tay_shift_lib coeff_monom_mult  by simp

lemma vpGge_pcompose: "prime p \<Longrightarrow> vpGge p P 0 \<Longrightarrow>
  vpGge p Q 0 \<Longrightarrow> vpGge p (pcompose P Q) 0"
proof -
  assume p: "prime p" and hP: "vpGge p P 0" and hQ: "vpGge p Q 0"
  show ?thesis using hP
  proof (induction P rule: pCons_induct)
    case 0
    show ?case using vpGge_zero  by simp
  next
    case (pCons a P)
    have "vge p (Polynomial.coeff (pCons a P) 0) 0" using pCons.prems unfolding vpGge_iff by blast
    hence a: "vge p a 0" by simp
    have "vpGge p P 0" unfolding vpGge_iff
    proof
      fix k
      have "vge p (Polynomial.coeff (pCons a P) (Suc k)) 0" using pCons.prems unfolding vpGge_iff
        by blast
      thus "vge p (Polynomial.coeff P k) 0" by simp
    qed
    hence "vpGge p (pcompose P Q) 0" using pCons.IH  by simp
    hence "vpGge p (Q * pcompose P Q) (0 + 0)" by (rule vpGge_mul[OF p hQ])
    hence "vpGge p ([:a:] + Q * pcompose P Q) 0" using vpGge_add[OF p vpGge_C[OF a]] by simp
    thus ?case using pcompose_pCons  by metis
  qed
qed

lemma vge_tay: "prime p \<Longrightarrow> vpGge p P 0 \<Longrightarrow> vge p r 0 \<Longrightarrow>
  vge p (tay P r i) 0"
proof -
  assume p: "prime p" and hP: "vpGge p P 0" and hr: "vge p r 0"
  have X0: "vpGge p (pX :: rat poly) 0" unfolding vpGge_iff using vge_one vge_zero
    by (simp add: coeff_monom)
  have "vpGge p (pX + [:r:]) 0" using vpGge_add[OF p X0 vpGge_C[OF hr]]  by simp
  hence "vpGge p (pcompose P (pX + [:r:])) 0" by (rule vpGge_pcompose[OF p hP])
  thus ?thesis unfolding tay_def vpGge_iff  by simp
qed

end
