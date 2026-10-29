(*  Title:   Zeta5_Definitions.thy
    Author:  Alex Hyman, University of Edinburgh, 2026
*)
theory Zeta5_Definitions
  imports Rational_Padic_Valuations Arcsine_Distribution Logarithmic_Energy
    "Zeta_Function.Zeta_Function"
    "Kummer_Congruence.Rat_Congruence"
    "Jordan_Normal_Form.Determinant"
    "Jordan_Normal_Form.DL_Rank"
    "HOL-Computational_Algebra.Polynomial_FPS"
    "HOL-Library.Log_Nat"
begin

section \<open>Definitions of the construction\<close>

text \<open>All definitions of the proof, transcribed from the Lean 4 theory @{text Defs} of the
  domino14/zeta5 formalisation, which fixed the conventions used throughout:
  \<^item> A rational function in \<open>t\<close> is a numerator polynomial together with a finite
    set of simple
    poles: @{text "muX S P"} is \<open>\<mu>\<^sub>X(P(t) / \<Prod>\<^sub>j\<^sub>\<in>\<^sub>S (t +
      j\<^sup>2))\<close> and @{text "tauX S P"} is
    \<open>\<tau>\<^sub>X(P(x) / \<Prod>\<^sub>r\<^sub>\<in>\<^sub>S (x -
      r))\<close>.  Values are polynomials in \<open>\<rat>[X]\<close>;
      the indeterminate \<open>X\<close> is
    later specialised to \<open>\<zeta>(5)\<close>.
  \<^item> The \<open>p\<close>-adic field \<open>\<rat>\<^sub>p\<close> of the paper's Sections
    3.1--3.2 is not used.  Every \<open>p\<close>-adically
    convergent series is replaced by its partial sum of length \<open>M\<close> (the @{text "_tr"}
      definitions)
    and the identities become congruences modulo high powers of \<open>p\<close>, so that the whole
    development stays in HOL over \<open>\<rat>\<close>.
  \<^item> Matrices are those of the Jordan\_Normal\_Form library, indexed
    by explicit lists of index
    pairs instead of Lean's \<open>\<Sigma>\<close>-types.
  Equation and section numbers refer to Fauzan's paper.\<close>

subsection \<open>Generic helpers\<close>

text \<open>Evaluation of a rational polynomial at a real (Lean: @{text "aeval x P"}).\<close>
definition real_eval :: "rat poly \<Rightarrow> real \<Rightarrow> real" where
  "real_eval P x = poly (map_poly of_rat P) x"


subsection \<open>Section 2.1 Parameters (2.1)\<close>

definition Nof :: "nat \<Rightarrow> nat" where "Nof K = 3 * K div 40"
definition hof :: "nat \<Rightarrow> nat" where "hof K = 37 * K div 40"
definition alpha_q :: rat where "alpha_q = 3 / 40"
definition lam_q :: rat where "lam_q = 37 / 40"
definition Hc_q :: rat where "Hc_q = 1 + 2 * alpha_q"

text \<open>The real number \<open>\<zeta>(5)\<close>;
  @{text zeta} is the AFP's Riemann zeta function.\<close>
definition zeta5 :: real where "zeta5 = Re (zeta 5)"

text \<open>@{text "H_j^{(5)} = \<Sum>_{v=1}^j v^{-5}"}.\<close>
definition H5 :: "nat \<Rightarrow> rat" where "H5 j = (\<Sum> v = 1..j. 1 / of_nat v ^ 5)"

text \<open>@{text "D_m(t) = \<Prod>_{j=1}^m (t + j^2)"}.\<close>
definition Dm :: "nat \<Rightarrow> rat poly" where "Dm m = (\<Prod> j =
  1..m. pX + [:of_nat j ^ 2:])"


subsection \<open>Section 2.1 The functional mu\_X (2.2), (2.3)\<close>

text \<open>(2.2): @{text "mu(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5)/24"},
  with @{text "B_1 = -1/2"}
  (both Mathlib's @{text bernoulli} and the AFP's polymorphic @{const bernoulli} use this
    convention).\<close>
definition muMono :: "nat \<Rightarrow> rat" where
  "muMono e = (-1) ^ e * bernoulli (2 * e + 2) *
     ((2 * of_nat e + 3) * (2 * of_nat e + 4) * (2 * of_nat e + 5)) / 24"

definition muPoly :: "rat poly \<Rightarrow> rat" where
  "muPoly P = (\<Sum> e \<le> degree P. Polynomial.coeff P e * muMono e)"

text \<open>(2.3): @{text "mu_X(1/(t+j^2)) = j^4(X - H_j) - 1/4 + 1/(2j)"}.\<close>
definition muPole :: "nat \<Rightarrow> rat poly" where
  "muPole j = [:of_nat j ^ 4:] * (pX - [:H5 j:]) - [:1 / 4:] + [:1 / (2 * of_nat j):]"

definition sqPoleProd :: "nat set \<Rightarrow> rat poly" where
  "sqPoleProd S = (\<Prod> j \<in> S. pX + [:of_nat j ^ 2:])"

text \<open>Residue of @{text "P/\<Prod>_{k\<in>S}(t+k^2)"} at @{text "t = -j^2"}.\<close>
definition sqResidue :: "nat set \<Rightarrow> rat poly \<Rightarrow> nat \<Rightarrow> rat" where
  "sqResidue S P j = poly P (- (of_nat j ^ 2)) / (\<Prod> k \<in>
    S - {j}. of_nat k ^ 2 - (of_nat j ^ 2))"

text \<open>@{text "mu_X(P(t)/\<Prod>_{j\<in>S}(t+j^2))"}
  by polynomial division and simple partial fractions
  (meaningful for finite @{text S} with @{text "0 \<notin> S"}).\<close>
definition muX :: "nat set \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "muX S P = [:muPoly (P div sqPoleProd S):] + (\<Sum> j \<in> S. [:sqResidue S P j:] * muPole j)"


subsection \<open>Section 2.1 The matrix, determinant and normalisation (2.4), (2.5)\<close>

text \<open>(2.4): @{text "G_K(X) = [mu_X(D_N(t)^6 t^{i+j} / D_K(t))]_{0 \<le> i,j < h}"}.\<close>
definition GK :: "nat \<Rightarrow> rat poly mat" where
  "GK K = Matrix.mat (hof K) (hof K) (\<lambda>(i, j). muX {1..K} (Dm (Nof K) ^ 6 * pX ^ (i + j)))"

definition DeltaK :: "nat \<Rightarrow> rat poly" where "DeltaK K = Determinant.det (GK K)"

text \<open>(2.5): @{text "S_K = (K!)^{2h} 4^{h-1} /
  ((N!)^{12h} \<Prod>_{i=1}^{h-1} ((2i)!)^2)"}.\<close>
definition SK :: "nat \<Rightarrow> rat" where
  "SK K = (fact K ^ (2 * hof K) * 4 ^ (hof K - 1)) /
          (fact (Nof K) ^ (12 * hof K) * (\<Prod> i = 1..hof K - 1. fact (2 * i) ^ 2))"

definition FK :: "nat \<Rightarrow> rat poly" where "FK K = [:SK K:] * DeltaK K"


subsection \<open>Section 3 The functional \<open>\<tau>\<^sub>X\<close>\<close>

text \<open>@{text "L(x^k) = B_k"}, extended linearly.\<close>
definition Lfun :: "rat poly \<Rightarrow> rat" where
  "Lfun P = (\<Sum> k \<le> degree P. Polynomial.coeff P k * bernoulli k)"

text \<open>@{text "\<tau>(P) = L(P''')/24"} on polynomials.\<close>
definition tau :: "rat poly \<Rightarrow> rat" where
  "tau P = Lfun ((pderiv ^^ 3) P) / 24"

text \<open>@{text "d(r) = r"} for @{text "r \<ge> 0"} and @{text "-r-1"}
  for @{text "r < 0"}.\<close>
definition dIdx :: "int \<Rightarrow> nat" where
  "dIdx r = (if 0 \<le> r then nat r else nat (- r - 1))"

text \<open>@{text "\<tau>_X(1/(x-r)) = H_{d(r)} - X"}.\<close>
definition tauPole :: "int \<Rightarrow> rat poly" where
  "tauPole r = [:H5 (dIdx r):] - pX"

definition linPoleProd :: "int set \<Rightarrow> rat poly" where
  "linPoleProd S = (\<Prod> r \<in> S. pX - [:of_int r:])"

definition linResidue :: "int set \<Rightarrow> rat poly \<Rightarrow> int \<Rightarrow> rat" where
  "linResidue S P r = poly P (of_int r) / (\<Prod> s \<in> S - {r}. of_int r - of_int s)"

text \<open>@{text "\<tau>_X(P(x)/\<Prod>_{r\<in>S}(x-r))"}
  by polynomial division and simple partial fractions.\<close>
definition tauX :: "int set \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "tauX S P = [:tau (P div linPoleProd S):] + (\<Sum> r \<in> S. [:linResidue S P r:] * tauPole r)"

text \<open>The fourth Taylor coefficient @{text "g''''(0)/24"} of @{text "g = P/Q"} at 0 (needs
  @{text "Q(0) \<noteq> 0"}).\<close>
definition taylor4 :: "rat poly \<Rightarrow> rat poly \<Rightarrow> rat" where
  "taylor4 P Q = fps_nth (fps_of_poly P * inverse (fps_of_poly Q)) 4"

text \<open>The poles @{text "\<plusminus>j"},
  @{text "j \<in> S"} (Lean: @{text signedPoles}).\<close>
definition signedPoles :: "nat set \<Rightarrow> int set" where
  "signedPoles S = int ` S \<union> (\<lambda>j. - int j) ` S"

text \<open>The poles @{text "-K \<le> r \<le> K"}, @{text "r \<noteq> 0"}, of Lemma 3.3.\<close>
definition symPoles :: "nat \<Rightarrow> int set" where
  "symPoles K = {r. - int K \<le> r \<and> r \<le> int K \<and> r \<noteq> 0}"

text \<open>@{text A} is @{text p}-integer-valued on \<open>\<int>\<close> (Lean:
  @{text IntValuedAt}).\<close>
definition IntValuedAt :: "nat \<Rightarrow> rat poly \<Rightarrow> bool" where
  "IntValuedAt p A \<longleftrightarrow>
    (\<forall>x::int. poly A (of_int x) \<noteq> 0 \<longrightarrow>
    0 \<le> vp p (poly A (of_int x)))"


subsection \<open>Section 3.1-3.2 The @{text p}-adic extension, in truncated rational form\<close>

text \<open>@{text "\<kappa>_d = d(d-1)(d-2) B_{d-3}/24"},
  so that @{text "\<tau>(z^d) = \<kappa>_d"}; it is 0 for @{text "d < 3"}.\<close>
definition kappa :: "nat \<Rightarrow> rat" where
  "kappa d = of_nat d * (of_nat d - 1) * (of_nat d - 2) * bernoulli (d - 3) / 24"

text \<open>@{text \<tau>} on polynomials through @{text \<kappa>} (equal to @{const tau}).\<close>
definition tauK :: "rat poly \<Rightarrow> rat" where
  "tauK Q = (\<Sum> d \<le> degree Q. Polynomial.coeff Q d * kappa d)"

text \<open>(3.5), truncated: the partial sum of length @{text M} of
  @{text "\<tau>^{an}(1/(z-s)) = -(1/4) \<Sum>_{k\<ge>0} C(k+3,3) B_k s^{-k-4}"} (for
    @{text "v_p(s) < 0"}
  the @{text k}-th term has valuation @{text "\<ge> k+3"},
    so the tail is @{text "\<equiv> 0 mod p^{M+3}"}).\<close>
definition tauAnPole_tr :: "nat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> rat" where
  "tauAnPole_tr p s M =
     - (1 / 4) * (\<Sum> k < M. of_nat ((k + 3) choose 3) * bernoulli k * s powi (- (int k + 4)))"

text \<open>(3.6), truncated: @{text "C_p = \<Sum>_{a=1}^{p-1} \<tau>^{an}(1/(x + a/p))"}.\<close>
definition Cp_tr :: "nat \<Rightarrow> nat \<Rightarrow> rat" where
  "Cp_tr p M = (\<Sum> a = 1..p - 1. tauAnPole_tr p (- of_nat a / of_nat p) M)"

text \<open>(3.6): @{text "Y = p^5 X + C_p"}.\<close>
definition Yp_tr :: "nat \<Rightarrow> nat \<Rightarrow> rat poly" where
  "Yp_tr p M = [:of_nat p ^ 5:] * pX + [:Cp_tr p M:]"

text \<open>Value of @{text "\<tau>_Y^{ext}"} on the simple pole @{text "1/(z-s)"}: near (integer)
  poles take
  @{text "H_{d(s)} - Y"}, far poles the truncated series.\<close>
definition tauPoleP_tr :: "nat \<Rightarrow> rat poly \<Rightarrow> rat \<Rightarrow> nat
  \<Rightarrow> rat poly" where
  "tauPoleP_tr p Y s M =
     (if snd (quotient_of s) = 1 then [:H5 (dIdx (fst (quotient_of s))):] - Y
      else [:tauAnPole_tr p s M:])"

definition qPoleProd :: "rat set \<Rightarrow> rat poly" where
  "qPoleProd S = (\<Prod> s \<in> S. pX - [:s:])"

definition qRes :: "rat set \<Rightarrow> rat poly \<Rightarrow> rat \<Rightarrow> rat" where
  "qRes S P s = poly P s / (\<Prod> s' \<in> S - {s}. s - s')"

text \<open>@{text "\<tau>_Y^{ext}(U(z)/\<Prod>_{s\<in>S}(z-s))"}
  for distinct rational poles @{text S}, truncated at @{text M}.\<close>
definition tauExt_tr :: "nat \<Rightarrow> rat poly \<Rightarrow> rat poly \<Rightarrow> rat set
  \<Rightarrow> nat \<Rightarrow> rat poly" where
  "tauExt_tr p Y U S M =
     [:tauK (U div qPoleProd S):] + (\<Sum> s \<in> S. [:qRes S U s:] * tauPoleP_tr p Y s M)"

text \<open>@{text "g(a + p x)"} written as @{text "U(x)/\<Prod>(x - s)"}: the numerator
  @{text "p^{-|S|} P(a + p x)"}.\<close>
definition distribNum :: "nat \<Rightarrow> int set \<Rightarrow> rat poly \<Rightarrow> nat
  \<Rightarrow> rat poly" where
  "distribNum p S P a =
     [:of_nat p powi (- int (card S)):] * pcompose P ([:of_nat a:] + [:of_nat p:] * pX)"

text \<open>The poles @{text "(r - a)/p"} of @{text "g(a + p x)"}.\<close>
definition distribPoles :: "nat \<Rightarrow> int set \<Rightarrow> nat \<Rightarrow> rat set" where
  "distribPoles p S a = (\<lambda>r. (of_int r - of_nat a) / of_nat p) ` S"

text \<open>The Taylor coefficients of the analytic part
  @{text "Q + \<Sum>_{s\<in>F} \<rho>_s/(z-s)"}.\<close>
definition fCoeff :: "rat poly \<Rightarrow> rat set \<Rightarrow> (rat \<Rightarrow> rat)
  \<Rightarrow> nat \<Rightarrow> rat" where
  "fCoeff Q F \<rho> d = Polynomial.coeff Q d - (\<Sum> s \<in> F. \<rho> s * inverse s ^ (d + 1))"


subsection \<open>Section 3.3 Small primes\<close>

text \<open>@{text "q_0 = 1"}, @{text "q_i(t) = (-1)^i 2t D_{i-1}(t)/(2i)!"}.\<close>
definition qBasis :: "nat \<Rightarrow> rat poly" where
  "qBasis i = (if i = 0 then 1 else [:(-1) ^ i * 2 / fact (2 * i):] * pX * Dm (i - 1))"

text \<open>@{text "f_i(t) = (D_N(t)/(N!)^2)^3 q_i(t)"}.\<close>
definition fBasis :: "nat \<Rightarrow> nat \<Rightarrow> rat poly" where
  "fBasis K i = ([:1 / fact (Nof K) ^ 2:] * Dm (Nof K)) ^ 3 * qBasis i"


subsection \<open>Section 4.1 The inner range\<close>

text \<open>@{text "l_A(a) = #{1 \<le> j \<le> A : j \<equiv> \<plusminus>a (mod p)}"}.\<close>
definition ell :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ell p A a = card {j \<in> {1..A}. j mod p = a mod p \<or> (j + a) mod p = 0}"

definition mHalf :: "nat \<Rightarrow> nat" where "mHalf p = (p - 1) div 2"
definition L0 :: "nat \<Rightarrow> nat" where "L0 M = 4 * M + 10"

text \<open>Right-hand side of (4.4): @{text "h - L_0 + 3(N - m_N)"}.\<close>
definition rhs44 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "rhs44 K M p = int (hof K) - int (L0 M) + 3 * (int (Nof K) - int (Nof K div p))"

text \<open>(4.4): @{text T} and @{text E} (integer division
  by the positive number @{text "m = (p-1)/2"}).\<close>
definition Tin :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where "Tin K M p =
  rhs44 K M p div int (mHalf p)"
definition Ein :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where "Ein K M p =
  rhs44 K M p mod int (mHalf p)"

text \<open>@{text "b_a = 3 l_N(a)"}.\<close>
definition bIn :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where "bIn K p a =
  3 * int (ell p (Nof K) a)"

text \<open>Position of class @{text a} in the ordering by decreasing @{text "l_K"}, ties
  by increasing @{text a}.\<close>
definition defaultPos :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "defaultPos K p a = card {c \<in> {1..mHalf p}. ell p K a < ell p K c \<or>
    (ell p K c = ell p K a \<and> c < a)}"

text \<open>@{text "\<epsilon>_a = 1"} for the first @{text E} classes in that ordering.\<close>
definition epsIn :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where
  "epsIn K M p a =
     (if int (card {c \<in> {1..mHalf p}. defaultPos K p c < defaultPos K p a}) <
       Ein K M p then 1 else 0)"

text \<open>@{text "L_a = T - b_a + \<epsilon>_a"}
  for @{text "a \<ge> 1"}, and @{text "L_0 = 4M + 10"}.\<close>
definition Lin :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where
  "Lin K M p a = (if a = 0 then int (L0 M) else Tin K M p - bIn K p a + epsIn K M p a)"

text \<open>@{text "Z_a = T + \<epsilon>_a"}.\<close>
definition Zin :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where "Zin K M p a = Tin K M p + epsIn K M p a"

text \<open>(4.6), (4.7): the row weights @{text "w_{a,i}"}.\<close>
definition wIn :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> rat" where
  "wIn K M p a i =
     (if a = 0 then
        Min (insert (2 * of_nat i + 6 * of_nat (Nof K div p) - of_nat (K div p) + 1 / 2)
                    ((\<lambda>c. of_int (Zin K M p c) - (of_nat (ell p K c) + 4) /
                      2) ` {1..mHalf p}))
      else of_nat i + of_int (bIn K p a) - (of_nat (ell p K a) + 4) / 2)"

text \<open>(4.8): @{text "\<gamma>_p^in = 2 \<Sum>_{a=0}^m \<Sum>_{i<L_a} w_{a,i}"}.\<close>
definition gammaIn :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat" where
  "gammaIn K M p = 2 * (\<Sum> a \<le> mHalf p. \<Sum> i < nat (Lin K M p a). wIn K M p a i)"

text \<open>Index list of the inner basis: pairs @{text "(a, i)"} with @{text "0 \<le> a \<le> m"},
  @{text "i < L_a"}
  (Lean's \<open>\<Sigma>\<close>-type @{text InnerIdx}, enumerated).\<close>
definition inner_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times>
  nat) list" where
  "inner_idx K M p = concat (map (\<lambda>a. map (\<lambda>i. (a,
    i)) [0..<nat (Lin K M p a)]) [0..<mHalf p + 1])"

text \<open>(4.5): @{text "E_{a,i}(t) = \<Prod>_{c \<noteq>
  a} (t + c^2)^{L_c} (t + a^2)^i"}.\<close>
definition innerBasis :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times>
  nat \<Rightarrow> rat poly" where
  "innerBasis K M p x =
     (\<Prod> c \<in> {0..mHalf p} - {fst x}. (pX + [:of_nat c ^ 2:]) ^ nat (Lin K M p c)) *
     (pX + [:of_nat (fst x) ^ 2:]) ^ snd x"

text \<open>The Gram matrix of @{text "mu_X(D_N^6 \<cdot> / D_K)"} in the inner basis.\<close>
definition innerGram :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat poly mat" where
  "innerGram K M p = (let idx = inner_idx K M p in
     Matrix.mat (length idx) (length idx)
       (\<lambda>(x, y). muX {1..K} (Dm (Nof K) ^ 6 * innerBasis K M p (idx ! x) *
         innerBasis K M p (idx ! y))))"

definition wInIdx :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times>
  nat \<Rightarrow> rat" where
  "wInIdx K M p x = wIn K M p (fst x) (snd x)"


subsection \<open>Section 4.2 The outer range\<close>

text \<open>@{text "r_p = max(0, K + 4N - 2p + 2)"} from (4.10) (truncated subtraction).\<close>
definition rOut :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "rOut K p =
  K + 4 * Nof K + 2 - 2 * p"

text \<open>(4.14): @{text "\<gamma>_p^out"}, with @{text "v = K - p\<lfloor>K/p\<rfloor>"},
  @{text "u = max(0, N+v-p+1)"},
  @{text "t_p = min(N, v) + u"}.\<close>
definition gammaOut :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "gammaOut K p = (let v = K mod p; u = Nof K + v + 1 - p; tp = min (Nof K) v + u in
     if K < 2 * p
     then - 7 * (int K - int p) + 6 * int tp - 1 - min (int (rOut K p)) (int p - 1 - int (Nof K) +
       int u)
     else - 7 * (int K - int p) + 3 + 12 * int (Nof K) + 5 * int tp - min (int (rOut K p)) (int p +
       int u))"

text \<open>(4.9): the hypotheses of the outer-range estimate.\<close>
definition OuterHyp :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "OuterHyp K p \<longleftrightarrow> 7 \<le> p \<and> p \<le> K \<and> K < 3 * p \<and>
    2 * K < p ^ 2 \<and> 2 * Nof K < p \<and> 5 * Nof K \<le> 2 * p - 2"

text \<open>The poles of @{text "D_tail"} in the class @{text "\<plusminus>a (mod p)"}
  (@{text "a = 0"}: multiples of @{text p}).\<close>
definition outerClassPoles :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "outerClassPoles K p a = {j \<in> {Nof K + 1..K}. j mod p = a mod p \<or> (j + a) mod p = 0}"

definition outerCount :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "outerCount K p a = card (outerClassPoles K p a)"

definition outer_idx :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "outer_idx K p = concat (map (\<lambda>a. map (\<lambda>i. (a,
    i)) [0..<outerCount K p a]) [0..<mHalf p + 1])"

text \<open>(4.11): rows @{text "P_a q_{a,i}"} with @{text "P_a = D_tail/Q_a"};
  the zero class is read as
  @{text "P_0 (t + p^2)^i"} (ambiguity recorded in the Lean NOTES, finding 1).\<close>
definition outerBasis :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times>
  nat \<Rightarrow> rat poly" where
  "outerBasis K p x = (let a = fst x; i = snd x;
       Pa = sqPoleProd ({Nof K + 1..K} - outerClassPoles K p a) in
     if a = 0 then Pa * (pX + [:of_nat p ^ 2:]) ^ i
     else (let l = ell p K a in
       if i < l - 2 then Pa * (pX + [:of_nat a ^ 2:]) ^ i
       else Pa * sqPoleProd {j \<in> outerClassPoles K p a. p <
         j} * (pX + [:of_nat a ^ 2:]) ^ (i - (l - 2))))"

text \<open>(4.12) and the zero-class weights.\<close>
definition wOut :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> rat" where
  "wOut K p x = (let a = fst x; i = snd x in
     if a = 0 then (if outerCount K p 0 = 1 then - 1 / 2 else if i = 0 then - 2 else 0)
     else (let l = ell p K a; d = (if a \<le> Nof K then 1 else 0 :: rat) in
       if i < l - 2 then min 0 (of_nat i + 3 * d - (of_nat l + 4) / 2) else 0))"

text \<open>The integer @{text "c_e \<equiv> p mu(t^e) (mod p)"} in @{text "[0, p)"},
  with @{text "c_e = 0"} for @{text "e < 2p-3"}
  (@{const qmod} is the AFP's residue of a rational modulo an integer).\<close>
definition cCorr :: "nat \<Rightarrow> nat \<Rightarrow> rat" where
  "cCorr p e = (if e < 2 * p - 3 then 0 else of_int ((of_nat p * muMono e) qmod int p))"

text \<open>@{text "mu_X"} with the polynomial moments replaced
  by @{text "mu^0(t^e) = mu(t^e) - c_e/p"}.\<close>
definition muXmod :: "nat \<Rightarrow> nat set \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "muXmod p S P =
     [:\<Sum> e \<le> degree (P div sqPoleProd S). Polynomial.coeff (P div sqPoleProd S) e *
       (muMono e - cCorr p e / of_nat p):]
     + (\<Sum> j \<in> S. [:sqResidue S P j:] * muPole j)"

text \<open>The matrix @{text A} of (4.10).\<close>
definition Aout :: "nat \<Rightarrow> nat \<Rightarrow> rat poly mat" where
  "Aout K p = Matrix.mat (hof K) (hof K) (\<lambda>(i,
    j). muXmod p {1..K} (Dm (Nof K) ^ 6 * pX ^ (i + j)))"

text \<open>@{text A} in the outer basis.\<close>
definition outerGram :: "nat \<Rightarrow> nat \<Rightarrow> rat poly mat" where
  "outerGram K p = (let idx = outer_idx K p in
     Matrix.mat (length idx) (length idx)
       (\<lambda>(x, y). muXmod p {1..K} (Dm (Nof K) ^ 6 * outerBasis K p (idx ! x) *
         outerBasis K p (idx ! y))))"


subsection \<open>Section 5 Normalisation (5.1), (5.2), (2.6)\<close>

definition vpS :: "nat \<Rightarrow> nat \<Rightarrow> int" where "vpS K p = vp p (SK K)"

text \<open>(5.1): @{text "L_p(K, M)"}; @{text "\<gamma>_p^in"} is an integer (Lean
  @{text gammaIn_isInt}), the floor
  just keeps the definition total.\<close>
definition Lp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "Lp K M p =
     (if p * M \<le> K then - 6 * int (hof K) * int (nat_log p (5 * K)) - int (hof K) *
       int (multiplicity p (24::nat))
      else if 3 * p \<le> K then vpS K p + floor (gammaIn K M p)
      else if p \<le> K then vpS K p + gammaOut K p
      else vpS K p)"

text \<open>(5.2): @{text "m_{K,M} = \<Prod>_{p \<le> 2h} p^{-L_p(K,M)}"}.\<close>
definition mKM :: "nat \<Rightarrow> nat \<Rightarrow> rat" where
  "mKM K M = (\<Prod> p \<in> {p. p \<le> 2 * hof K \<and> prime p}. of_nat p powi (- Lp K M p))"

text \<open>(2.6): @{text "Q_{K,M} = m_{K,M} F_K"}.\<close>
definition QKM :: "nat \<Rightarrow> nat \<Rightarrow> rat poly" where "QKM K M =
  [:mKM K M:] * FK K"


subsection \<open>Section 5.1-5.3 Limiting functions (real-valued;
  Lean namespace @{text Lim})\<close>

definition alpha_r :: real where "alpha_r = 3 / 40"
definition lam_r :: real where "lam_r = 37 / 40"
definition Hc_r :: real where "Hc_r = 23 / 20"
definition pos_r :: "real \<Rightarrow> real" where "pos_r v = max v 0"

text \<open>@{text "l(x, z) = \<lfloor>x - z\<rfloor> + \<lfloor>x + z\<rfloor> + 1"}.\<close>
definition ell_r :: "real \<Rightarrow> real \<Rightarrow> real" where
  "ell_r x z = of_int (floor (x - z)) + of_int (floor (x + z)) + 1"

text \<open>(5.4): @{text "\<Gamma>(x)"}.\<close>
definition Gam_r :: "real \<Rightarrow> real" where
  "Gam_r x = (let T = of_int (floor (2 * Hc_r * x)); s = Hc_r * x - T / 2;
                  q = of_int (floor (2 * x)); nplus = (2 * x - q) / 2 in
     interval_lebesgue_integral lborel (ereal 0) (ereal (1 / 2))
       (\<lambda>z. (T - 3 * ell_r (alpha_r * x) z) * (T + 3 * ell_r (alpha_r * x) z - ell_r x z -
         5))
     + s * (2 * T - q - 5) + pos_r (s - nplus))"

text \<open>@{text "J(u) = m u - m(m+1)/4"}, @{text "m = \<lfloor>2u\<rfloor>"}.\<close>
definition J_r :: "real \<Rightarrow> real" where
  "J_r u = of_int (floor (2 * u)) * u - of_int (floor (2 * u)) * (of_int (floor (2 * u)) + 1) / 4"

text \<open>(5.5): @{text "N(x)"}.\<close>
definition Nfun_r :: "real \<Rightarrow> real" where
  "Nfun_r x = 2 * lam_r * x * of_int (floor x) - 12 * lam_r * x * of_int (floor (alpha_r * x))
              - 2 * J_r (lam_r * x)"

text \<open>(5.6): @{text "R(x) = -\<Gamma>(x) - N(x)"}.\<close>
definition R_r :: "real \<Rightarrow> real" where "R_r x = - Gam_r x - Nfun_r x"

text \<open>(5.8): @{text "R_0(y)"}.\<close>
definition R0_r :: "real \<Rightarrow> real" where
  "R0_r y =
     (if 1 / 3 < y \<and> y < 1 / 2 then
        8 - 9 * y - 8 * alpha_r - 5 * min alpha_r (1 - 2 * y) - 5 * pos_r (1 + alpha_r - 3 * y)
      else if 1 / 2 < y \<and> y < 1 then
        7 * (1 - y) - 6 * min alpha_r (1 - y) - 6 * pos_r (1 + alpha_r - 2 * y) + pos_r (1 + 4 *
          alpha_r - 2 * y)
      else 0)"

text \<open>(5.9): @{text "d(y)"}.\<close>
definition dfun_r :: "real \<Rightarrow> real" where
  "dfun_r y = (if 1 / 3 < y \<and> y < 1 / 2 then pos_r ((1 + 4 * alpha_r - 3 * y) - pos_r (1 +
    alpha_r - 3 * y)) else 0)"

text \<open>Integrand of (5.10).\<close>
definition outer_integrand :: "real \<Rightarrow> real" where
  "outer_integrand y = R0_r y - dfun_r y - 2 * lam_r * of_int (floor (1 / y))
                       + (\<Sum> j = 1..5. pos_r (2 * lam_r - real j * y))"

text \<open>(5.12)-(5.13): fractional parts and the pieces @{text P}, @{text C} of the tail.\<close>
definition G0_r :: "real \<Rightarrow> real" where "G0_r v = v * (1 - v) * (2 * v - 1) / 6"
definition Pper :: "real \<Rightarrow> real" where
  "Pper x = 74 * frac (alpha_r * x) * (1 - frac (alpha_r * x)) - lam_r * frac x * (1 - frac x)"
definition Cper :: "real \<Rightarrow> real" where
  "Cper x = 74 / alpha_r * G0_r (frac (alpha_r * x)) - lam_r * G0_r (frac x)"

text \<open>(5.10): @{text "I_out = 127751/96000"}.\<close>
definition Iout :: rat where "Iout = 127751 / 96000"
text \<open>(5.19).\<close>
definition Astar :: rat where "Astar = 9928298118277006344769 / 7535670527041937280000"
text \<open>(5.20).\<close>
definition AM :: "nat \<Rightarrow> rat" where
  "AM M = Astar + 7 * lam_q / of_nat M - (2923 / 240 - 1 / 4) / of_nat M ^ 2 + 32 / of_nat M ^ 3"
text \<open>(6.4): the constant @{text "Ubar"}.\<close>
definition Ubar :: rat where "Ubar = - 2733991 / 2000000"


subsection \<open>Section 6 The real determinant\<close>

text \<open>(2.10): @{text "w(y) = (2\<pi>)^4 y^5/12 \<cdot> \<Sum>_{l\<ge>1} l^4 e^{-2\<pi>ly}"}
  (@{text suminf}; summable for @{text "y > 0"}).\<close>
definition weight :: "real \<Rightarrow> real" where
  "weight y = (2 * pi) ^ 4 * y ^ 5 / 12 * suminf (\<lambda>l. real (l + 1) ^ 4 * exp (- 2 * pi *
    real (l + 1) * y))"

text \<open>(6.1): the external field @{text V}.\<close>
definition Vf :: "real \<Rightarrow> real" where
  "Vf t = 2 * pi * sqrt t + integral {0..1} (\<lambda>u. ln (t + u ^ 2)) - 6 * integral {0..3 /
    40} (\<lambda>u. ln (t + u ^ 2))"

text \<open>Table 1, scaled by @{text "10^1^2"}: @{text "(a_j, b_j, c_j)"}
  for @{text "j = 1, \<dots>, 16"}.\<close>
definition table1 :: "(nat \<times> nat \<times> nat) list" where
  "table1 =
   [(3906748086, 8992695531, 10515596180), (2312248264, 15340997855, 29471737793),
    (1402286665, 25730180724, 42934365099), (881725356, 41909578246, 58204231966),
    (578197906, 65851089563, 69037621310), (396324613, 99481037884, 78873099189),
    (283911191, 144325727458, 84856120711), (212206188, 201105762729, 88396082127),
    (165097686, 269345996903, 88303382125), (133347132, 347089554156, 85472321255),
    (111522114, 430806704415, 78899184238), (96349355, 515561896511, 70353471918),
    (85815639, 595448778546, 58838976615), (78667711, 664241383483, 44421321106),
    (74129565, 716160577112, 30462865791), (71741310, 746637295669, 5959622577)]"

definition tA :: "nat \<times> nat \<times> nat \<Rightarrow> real" where "tA e =
  real (fst e) / 10 ^ 12"
definition tB :: "nat \<times> nat \<times> nat \<Rightarrow> real" where "tB e =
  real (fst (snd e)) / 10 ^ 12"
definition tC :: "nat \<times> nat \<times> nat \<Rightarrow> real" where "tC e =
  real (snd (snd e)) / 10 ^ 12"

text \<open>The comparison measure @{text "\<rho> = \<Sum> c_j \<omega>_{[a_j,b_j]}"} of Lemma 6.1,
  as one density w.r.t.
  Lebesgue measure (Lean sums the sixteen scaled measures; the two agree).\<close>
definition rho :: "real measure" where
  "rho = density lborel (\<lambda>t. ennreal (\<Sum> e \<leftarrow> table1. tC e *
    arcsine_dens (tA e) (tB e) t))"

text \<open>@{text "I(mu) = integral integral log|t - u| dmu(t) dmu(u)"}.\<close>
definition logEnergy :: "real measure \<Rightarrow> real" where
  "logEnergy \<mu> = integral\<^sup>L \<mu> (\<lambda>t. logPot \<mu> t)"

text \<open>@{text "M_0 = -1329/200"}.\<close>
definition M0c :: rat where "M0c = - 1329 / 200"

text \<open>(6.3): @{text "C* = -2\<lambda> + 12\<alpha>\<lambda>(1 - log \<alpha>) + 3\<lambda>^2 -
  2\<lambda>^2 log(2\<lambda>)"}.\<close>
definition Cstar :: real where
  "Cstar = - 2 * lam_r + 12 * alpha_r * lam_r * (1 - ln alpha_r) + 3 * lam_r ^ 2 - 2 * lam_r ^ 2 *
    ln (2 * lam_r)"

text \<open>The partial masses @{text "S_j = \<Sum>_{i \<le> j} c_i"} of Appendix A.\<close>
definition Spart :: "nat \<Rightarrow> real" where "Spart j =
  (\<Sum> e \<leftarrow> take j table1. tC e)"

end
