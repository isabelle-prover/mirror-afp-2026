(*  Title:   Legendre_Factorial_Valuation.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Legendre_Factorial_Valuation
  imports Rational_Padic_Valuations "Prime_Number_Theorem.Prime_Counting_Functions"
begin

section \<open>Legendre's formula for the \<open>p\<close>-adic valuation of
  \<open>n!\<close>\<close>

text \<open>\<open>v\<^sub>p(n!) = \<Sum>\<^sub>a\<^sub>\<ge>\<^sub>1 \<lfloor>n /
  p\<^sup>a\<rfloor>\<close>, derived from the Legendre identity of the AFP entry
  Prime\_Number\_Theorem, in the two forms used later: with the @{text legendre_aux}
  function of that entry and with an explicit finite range of summation.\<close>

text \<open>Legendre's formula @{text "v_p(n!) = \<Sum>_{a\<ge>1} \<lfloor>n/p^a\<rfloor>"};
  exists as
  @{text IMO2019_Q4.multiplicity_prime_fact} with @{text legendre_aux}.\<close>
lemma legendre_fact:
  fixes p :: nat
  assumes "prime p"
  shows "multiplicity p (fact n) = legendre_aux (real n) p"
proof (cases "p \<le> n")
  case True
  have "fact n = (\<Prod>p | prime p \<and> p \<le> n. p ^ legendre_aux n p)"
    using legendre_identity'[of "real n"] by simp
  also have "multiplicity p \<dots> = (\<Sum>q | prime q \<and>
    q \<le> n. multiplicity p (q ^ legendre_aux n q))"
    using assms by (subst prime_elem_multiplicity_prod_distrib) auto
  also have "\<dots> = (\<Sum>q\<in>{p}. legendre_aux n q)"
    using assms \<open>p \<le> n\<close> prime_multiplicity_other[of p]
    by (intro sum.mono_neutral_cong_right)
       (auto simp: prime_elem_multiplicity_power_distrib prime_multiplicity_prime split: if_splits)
  finally show ?thesis by simp
next
  case False
  hence "multiplicity p (fact n) = 0"
    using assms by (intro not_dvd_imp_multiplicity_0) (auto simp: prime_dvd_fact_iff)
  moreover from False have "legendre_aux (real n) p = 0"
    by (intro legendre_aux_eq_0) auto
  ultimately show ?thesis by simp
qed

text \<open>Legendre's formula with any upper limit @{text "B \<ge> n"} on the sum.\<close>
lemma legendre_sum:
  assumes "prime p" "n \<le> B"
  shows "multiplicity p (fact n) = (\<Sum> a = 1..B. n div p ^ a)"
proof -
  have p2: "2 \<le> p" using prime_ge_2_nat[OF assms(1)] .
  have "multiplicity p (fact n) = (\<Sum> m | 0 < m \<and>
    real (p ^ m) \<le> real n. nat \<lfloor>real n / real (p ^ m)\<rfloor>)"
    using legendre_fact[OF assms(1), of n] assms(1) by (simp add: legendre_aux_def)
  also have "\<dots> = (\<Sum> m | 0 < m \<and> p ^ m \<le> n. n div p ^ m)"
  proof (rule sum.cong)
    show "{m. 0 < m \<and> real (p ^ m) \<le> real n} = {m. 0 < m \<and> p ^ m \<le> n}"
      by (simp only: of_nat_le_iff)
  next
    fix m show "nat \<lfloor>real n / real (p ^ m)\<rfloor> = n div p ^ m"
      by (simp only: floor_divide_of_nat_eq nat_int)
  qed
  also have "\<dots> = (\<Sum> a = 1..B. n div p ^ a)"
  proof (rule sum.mono_neutral_left)
    show "{m. 0 < m \<and> p ^ m \<le> n} \<subseteq> {1..B}"
    proof
      fix m assume m: "m \<in> {m. 0 < m \<and> p ^ m \<le> n}"
      have "m < 2 ^ m" by (rule less_exp)
      also have "(2::nat) ^ m \<le> p ^ m" using p2 by (rule power_mono) simp
      finally show "m \<in> {1..B}" using m assms(2) by auto
    qed
  next
    show "\<forall>i \<in> {1..B} - {m. 0 < m \<and> p ^ m \<le> n}. n div p ^ i = 0"
    proof
      fix i assume "i \<in> {1..B} - {m. 0 < m \<and> p ^ m \<le> n}"
      hence "n < p ^ i" by auto
      thus "n div p ^ i = 0" by (rule div_less)
    qed
  qed simp
  finally show ?thesis .
qed


end
