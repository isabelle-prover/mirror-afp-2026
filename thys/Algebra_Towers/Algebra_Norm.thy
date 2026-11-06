theory Algebra_Norm
  imports Algebra_Trace
begin

section \<open>Algebra norm\<close>

text \<open>
Simultaneously reindexing the rows and columns of a matrix along a bijection
does not change its determinant.  Isabelle's @{const map_permutation}
transports the permutations in the Leibniz formula and preserves their signs.
\<close>

lemma bij_betw_map_permutations:
  assumes h: "bij_betw h A B"
  shows "bij_betw (map_permutation A h)
    {p. p permutes A} {q. q permutes B}"
  apply (rule bij_betwI[where g = "map_permutation B (inv_into A h)"])
  apply (simp add: h map_permutation_permutes)
  apply (simp add: bij_betw_inv_into h map_permutation_permutes)
  using bij_betw_imp_inj_on h map_permutation_compose_inv apply fastforce
  using bij_betw_inv_into bij_betw_inv_into_right h map_permutation_compose_inv by fastforce

theorem det_reindex_bij:
  fixes A :: "'r::comm_ring_1^'j::finite^'j"
    and index_iso :: "'i::finite \<Rightarrow> 'j"
  assumes index_iso_bij: "bij index_iso"
  shows "det (\<chi> i k. A $ index_iso i $ index_iso k) = det A"
proof -
  let ?P = "{p :: 'i \<Rightarrow> 'i. p permutes UNIV}"
  let ?Q = "{q :: 'j \<Rightarrow> 'j. q permutes UNIV}"
  let ?F = "map_permutation (UNIV :: 'i set) index_iso"
  have index_betw:
    "bij_betw index_iso (UNIV :: 'i set) (UNIV :: 'j set)"
    using index_iso_bij
    by (simp add: bij_betw_def bij_def)
  have index_inj: "inj_on index_iso (UNIV :: 'i set)"
    using index_betw by (simp add: bij_betw_def)
  have permutation_betw: "bij_betw ?F ?P ?Q"
    by (rule bij_betw_map_permutations[OF index_betw])
  have sign_reindexed:
    "sign (?F p) = sign p" if "p \<in> ?P" for p
  proof -
    have "p permutes (UNIV :: 'i set)"
      using that by simp
    show ?thesis
      apply (rule sign_map_permutation)
        apply (fact index_inj)
       apply fact
      apply simp
      done
  qed
  have product_reindexed:
    "(\<Prod>i\<in>UNIV.
        A $ index_iso i $ index_iso (p i)) =
      (\<Prod>j\<in>UNIV. A $ j $ ?F p j)"
    for p
  proof -
    have "(\<Prod>i\<in>UNIV.
        A $ index_iso i $ ?F p (index_iso i)) =
      (\<Prod>j\<in>UNIV. A $ j $ ?F p j)"
      by (rule prod.reindex_bij_betw[OF index_betw])
    then show ?thesis
      using index_inj
      by (simp add: map_permutation_apply)
  qed
  have summand_reindexed:
    "(of_int (sign p) :: 'r) *
        (\<Prod>i\<in>UNIV.
          A $ index_iso i $ index_iso (p i)) =
      of_int (sign (?F p)) *
        (\<Prod>j\<in>UNIV. A $ j $ ?F p j)"
    if "p \<in> ?P" for p
    using sign_reindexed[OF that] product_reindexed
    by simp
  have sum_reindexed:
    "(\<Sum>p\<in>?P.
        (of_int (sign p) :: 'r) *
          (\<Prod>i\<in>UNIV.
            A $ index_iso i $ index_iso (p i))) =
      (\<Sum>q\<in>?Q.
        of_int (sign q) * (\<Prod>j\<in>UNIV. A $ j $ q j))"
  proof -
    have "(\<Sum>p\<in>?P.
        (of_int (sign p) :: 'r) *
          (\<Prod>i\<in>UNIV.
            A $ index_iso i $ index_iso (p i))) =
      (\<Sum>p\<in>?P.
        ((\<lambda>q. of_int (sign q) *
          (\<Prod>j\<in>UNIV. A $ j $ q j)) \<circ> ?F) p)"
    proof (rule sum.cong)
      show "?P = ?P"
        by simp
      fix p
      assume "p \<in> ?P"
      then show "(of_int (sign p) :: 'r) *
          (\<Prod>i\<in>UNIV.
            A $ index_iso i $ index_iso (p i)) =
        ((\<lambda>q. of_int (sign q) *
          (\<Prod>j\<in>UNIV. A $ j $ q j)) \<circ> ?F) p"
        by (simp only: o_apply summand_reindexed)
    qed
    also have "\<dots> =
      (\<Sum>q\<in>?Q.
        of_int (sign q) * (\<Prod>j\<in>UNIV. A $ j $ q j))"
      unfolding o_def
      by (rule sum.reindex_bij_betw[OF permutation_betw])
    finally show ?thesis .
  qed
  show ?thesis
    unfolding det_def
    by (simp only: vec_lambda_beta sum_reindexed)
qed

text \<open>
The Cartesian-space library provides matrix induction by elementary operations
only for real matrices.  The proof uses no order or topology, so we expose the
same argument over an arbitrary field.
\<close>

lemma induct_matrix_row_operations_field:
  fixes P :: "'a::field^'n^'n \<Rightarrow> bool"
  assumes zero_row: "\<And>A i. row i A = 0 \<Longrightarrow> P A"
    and diagonal: "\<And>A. (\<And>i j. i \<noteq> j \<Longrightarrow> A$i$j = 0) \<Longrightarrow> P A"
    and swap_cols: "\<And>A m n. \<lbrakk>P A; m \<noteq> n\<rbrakk> \<Longrightarrow>
      P (\<chi> i j. A $ i $ Transposition.transpose m n j)"
    and row_op: "\<And>A m n c. \<lbrakk>P A; m \<noteq> n\<rbrakk> \<Longrightarrow>
      P (\<chi> i. if i = m then row m A + c *s row n A else row i A)"
  shows "P A"
proof -
  have "P A" if zeros:
    "\<And>i j. \<lbrakk>j \<in> -K; i \<noteq> j\<rbrakk> \<Longrightarrow> A$i$j = 0"
    for A K
  proof -
    have "finite K"
      by simp
    then show ?thesis using zeros
    proof (induction arbitrary: A rule: finite_induct)
      case empty
      with diagonal show ?case
        by simp
    next
      case (insert k K)
      note insertK = insert
      have pivot: "P A" if nonzero: "A$k$k \<noteq> 0"
        and outside:
          "\<And>i j. \<lbrakk>j \<in> - insert k K; i \<noteq> j\<rbrakk> \<Longrightarrow>
            A$i$j = 0"
          "\<And>i. \<lbrakk>i \<in> -L; i \<noteq> k\<rbrakk> \<Longrightarrow> A$i$k = 0"
        for A L
      proof -
        have "finite L"
          by simp
        then show ?thesis using outside nonzero
        proof (induction arbitrary: A rule: finite_induct)
          case (empty B)
          show ?case
          proof (rule insertK)
            fix i j
            assume "i \<in> - K" "j \<noteq> i"
            show "B $ j $ i = 0"
              using \<open>j \<noteq> i\<close> \<open>i \<in> - K\<close> empty
              by (metis ComplD ComplI Compl_eq_Diff_UNIV Diff_empty
                UNIV_I insert_iff)
          qed
        next
          case (insert l L B)
          show ?case
          proof (cases "k = l")
            case True
            with insert show ?thesis
              by auto
          next
            case False
            let ?C = "\<chi> i.
              if i = l
              then row l B - (B $ l $ k / B $ k $ k) *s row k B
              else row i B"
            have first_zero:
              "\<lbrakk>j \<in> - insert k K; i \<noteq> j\<rbrakk> \<Longrightarrow>
                ?C $ i $ j = 0"
              for j i
              by (auto simp: insert.prems(1) row_def)
            have column_zero: "?C $ i $ k = 0"
              if "i \<in> - L" "i \<noteq> k" for i
            proof (cases "i = l")
              case True
              with that insert.prems show ?thesis
                by (simp add: row_def)
            next
              case False
              with that show ?thesis
                by (simp add: insert.prems(2) row_def)
            qed
            have pivot_nonzero: "?C $ k $ k \<noteq> 0"
              by (auto simp: insert.prems row_def \<open>k \<noteq> l\<close>)
            have "P ?C"
              using insert.IH[OF first_zero column_zero pivot_nonzero]
              by auto
            moreover have "(\<chi> i.
                if i = l
                then row l ?C + (B $ l $ k / B $ k $ k) *s row k ?C
                else row i ?C) = B"
              using \<open>k \<noteq> l\<close>
              by (simp add: vec_eq_iff row_def)
            ultimately show ?thesis
              using row_op[of ?C l k "B$l$k / B$k$k"] \<open>k \<noteq> l\<close>
              by (simp add: cong: if_cong)
          qed
        qed
      qed
      then have nonzero_case: "P A"
        if "A$k$k \<noteq> 0"
          "\<And>i j. j \<in> - insert k K \<and> i \<noteq> j \<Longrightarrow>
            A$i$j = 0"
        for A
        using that by auto
      show ?case
      proof (cases "row k A = 0")
        case True
        with zero_row show ?thesis
          by auto
      next
        case False
        then obtain l where l: "A$k$l \<noteq> 0"
          by (auto simp: row_def zero_vec_def vec_eq_iff)
        show ?thesis
        proof (cases "k = l")
          case True
          with l nonzero_case insert.prems show ?thesis
            by blast
        next
          case False
          have swapped_zero:
            "A $ i $ Transposition.transpose k l j = 0"
            if "j \<noteq> k" "j \<notin> K" "i \<noteq> j" for i j
            using False l insert.prems that
            by (auto simp add: Transposition.transpose_def)
          have "P (\<chi> i j.
              (\<chi> i j. A $ i $ Transposition.transpose k l j) $
                i $ Transposition.transpose k l j)"
            by (rule swap_cols[OF nonzero_case False])
              (auto simp: l swapped_zero)
          moreover have "(\<chi> i j.
              (\<chi> i j. A $ i $ Transposition.transpose k l j) $
                i $ Transposition.transpose k l j) = A"
            by simp
          ultimately show ?thesis
            by simp
        qed
      qed
    qed
  qed
  then show ?thesis
    by blast
qed

lemma induct_matrix_elementary_field:
  fixes P :: "'a::field^'n^'n \<Rightarrow> bool"
  assumes mult: "\<And>A B. \<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P (A ** B)"
    and zero_row: "\<And>A i. row i A = 0 \<Longrightarrow> P A"
    and diagonal: "\<And>A. (\<And>i j. i \<noteq> j \<Longrightarrow> A$i$j = 0) \<Longrightarrow> P A"
    and swap: "\<And>m n. m \<noteq> n \<Longrightarrow>
      P (\<chi> i j. mat 1 $ i $ Transposition.transpose m n j)"
    and add: "\<And>m n c. m \<noteq> n \<Longrightarrow>
      P (\<chi> i j.
        if i = m \<and> j = n then c else of_bool (i = j))"
  shows "P A"
proof -
  have swap_columns:
    "P (\<chi> i j. A $ i $ Transposition.transpose m n j)"
    if "P A" "m \<noteq> n" for A m n
  proof -
    have "A ** (\<chi> i j.
        mat 1 $ i $ Transposition.transpose m n j) =
      (\<chi> i j. A $ i $ Transposition.transpose m n j)"
      by (simp add: matrix_matrix_mult_def mat_def vec_eq_iff
        if_distrib sum.delta_remove)
    then show ?thesis
      using mult swap that by metis
  qed
  have add_row:
    "P (\<chi> i.
      if i = m then row m A + c *s row n A else row i A)"
    if "P A" "m \<noteq> n" for A m n c
  proof -
    let ?B = "\<chi> i j.
      if i = m \<and> j = n then c else of_bool (i = j)"
    have "?B ** A =
      (\<chi> i. if i = m then row m A + c *s row n A else row i A)"
      using \<open>m \<noteq> n\<close>
      unfolding matrix_matrix_mult_def row_def of_bool_def
      by (auto simp: vec_eq_iff
        if_distrib[of "\<lambda>x. x * y" for y] sum.remove
        cong: if_cong)
    then show ?thesis
      by (rule subst) (auto simp: that mult add)
  qed
  show ?thesis
    by (rule induct_matrix_row_operations_field[
      OF zero_row diagonal swap_columns add_row])
qed

definition block_embed ::
    "'j::finite \<Rightarrow> 'r::zero_neq_one^'i::finite^'i \<Rightarrow>
      'r^('i \<times> 'j)^('i \<times> 'j)"
  where "block_embed j B =
    (\<chi> ik hl.
      if snd ik = j \<and> snd hl = j
      then B $ fst ik $ fst hl
      else of_bool (ik = hl))"

lemma sum_UNIV_prod:
  fixes f :: "('a::finite \<times> 'b::finite) \<Rightarrow> 'c::comm_monoid_add"
  shows "(\<Sum>x\<in>UNIV. f x) =
    (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV. f (a, b))"
  by (simp only: UNIV_Times_UNIV[symmetric] sum.cartesian_product')

lemma cartesian_matrix_mult_component:
  fixes B C :: "'r::comm_ring_1^'i::finite^'i"
  shows "(B ** C) $ i $ h = (\<Sum>a\<in>UNIV. B $ i $ a * C $ a $ h)"
  by (simp only: matrix_matrix_mult_def vec_lambda_beta)

lemma block_embed_component [simp]:
  fixes j :: "'j::finite"
    and B :: "'r::zero_neq_one^'i::finite^'i"
  shows "block_embed j B $ (i, k) $ (h, l) =
    (if k = j \<and> l = j then B $ i $ h
     else of_bool ((i, k) = (h, l)))"
  by (simp add: block_embed_def)

lemma block_embed_one [simp]:
  fixes j :: "'j::finite"
  shows "block_embed j (mat 1 :: 'r::comm_ring_1^'i^'i) =
    (mat 1 :: 'r^('i \<times> 'j)^('i \<times> 'j))"
  by (vector block_embed_def mat_def of_bool_def)

lemma sum_of_bool_left:
  fixes f :: "'a::finite \<Rightarrow> 'r::comm_ring_1"
  shows "(\<Sum>x\<in>UNIV. of_bool (x = p) * f x) = f p"
  by (subst sum.remove[of UNIV p]) (auto simp: of_bool_def)

lemma sum_of_bool_right:
  fixes f :: "'a::finite \<Rightarrow> 'r::comm_ring_1"
  shows "(\<Sum>x\<in>UNIV. f x * of_bool (x = p)) = f p"
  by (subst sum.remove[of UNIV p]) (auto simp: of_bool_def)

lemma prod_if_eq:
  fixes j :: "'a::finite"
    and x :: "'r::comm_monoid_mult"
  shows "(\<Prod>k\<in>UNIV. if k = j then x else 1) = x"
  by (subst prod.remove[of UNIV j]) simp_all

lemma block_embed_row_outside:
  fixes j :: "'j::finite"
    and B :: "'r::zero_neq_one^'i::finite^'i"
  assumes "k \<noteq> j"
  shows "block_embed j B $ (i, k) $ (h, l) =
    of_bool ((i, k) = (h, l))"
proof -
  have outside: "\<not> (k = j \<and> l = j)"
    using assms by blast
  show ?thesis
    apply (subst block_embed_component)
    apply (subst if_not_P[OF outside])
    apply (rule refl)
    done
qed

lemma block_embed_column_outside:
  fixes j :: "'j::finite"
    and B :: "'r::zero_neq_one^'i::finite^'i"
  assumes "l \<noteq> j"
  shows "block_embed j B $ (i, k) $ (h, l) =
    of_bool ((i, k) = (h, l))"
proof -
  have outside: "\<not> (k = j \<and> l = j)"
    using assms by blast
  show ?thesis
    apply (subst block_embed_component)
    apply (subst if_not_P[OF outside])
    apply (rule refl)
    done
qed

lemma block_embed_mult:
  fixes j :: "'j::finite"
    and B C :: "'r::comm_ring_1^'i::finite^'i"
  shows "block_embed j (B ** C) = block_embed j B ** block_embed j C"
proof -
  have entry:
    "block_embed j (B ** C) $ ik $ hl =
      (block_embed j B ** block_embed j C) $ ik $ hl"
    for ik hl
  proof -
    obtain i k where ik_eq: "ik = (i, k)"
      by (cases ik) blast
    obtain h l where hl_eq: "hl = (h, l)"
      by (cases hl) blast
    have equal_case:
      "block_embed j (B ** C) $ (i, k) $ (h, l) =
        (block_embed j B ** block_embed j C) $ (i, k) $ (h, l)"
      if k_eq: "k = j"
    proof (cases "l = j")
        case True
        have inner:
          "(\<Sum>b\<in>UNIV.
              block_embed j B $ (i, j) $ (a, b) *
              block_embed j C $ (a, b) $ (h, j)) =
            B $ i $ a * C $ a $ h"
          for a
        proof -
          have selected:
            "block_embed j B $ (i, j) $ (a, j) *
                block_embed j C $ (a, j) $ (h, j) =
              B $ i $ a * C $ a $ h"
          proof -
            have first:
              "block_embed j B $ (i, j) $ (a, j) = B $ i $ a"
              apply (subst block_embed_component)
              apply (subst if_P)
               apply blast
              apply (rule refl)
              done
            have second:
              "block_embed j C $ (a, j) $ (h, j) = C $ a $ h"
              apply (subst block_embed_component)
              apply (subst if_P)
               apply blast
              apply (rule refl)
              done
            show ?thesis
              apply (subst first)
              apply (subst second)
              apply (rule refl)
              done
          qed
          have off:
            "block_embed j B $ (i, j) $ (a, b) *
                block_embed j C $ (a, b) $ (h, j) = 0"
            if "b \<in> UNIV - {j}" for b
          proof -
            have b_ne: "b \<noteq> j"
              using that by blast
            have outside: "\<not> (j = j \<and> b = j)"
              using b_ne by blast
            have unequal: "(i, j) \<noteq> (a, b)"
              using b_ne by blast
            have first_zero:
              "block_embed j B $ (i, j) $ (a, b) = 0"
              apply (subst block_embed_component)
              apply (subst if_not_P[OF outside])
              apply (simp only: of_bool_def unequal if_False)
              done
            show ?thesis
              apply (subst first_zero)
              apply simp
              done
          qed
          have off_sum:
            "(\<Sum>b\<in>UNIV - {j}.
                block_embed j B $ (i, j) $ (a, b) *
                block_embed j C $ (a, b) $ (h, j)) = 0"
            by (intro sum.neutral ballI; rule off)
          have split:
            "(\<Sum>b\<in>UNIV.
                block_embed j B $ (i, j) $ (a, b) *
                block_embed j C $ (a, b) $ (h, j)) =
              block_embed j B $ (i, j) $ (a, j) *
                block_embed j C $ (a, j) $ (h, j) +
              (\<Sum>b\<in>UNIV - {j}.
                block_embed j B $ (i, j) $ (a, b) *
                block_embed j C $ (a, b) $ (h, j))"
            by (subst sum.remove[of UNIV j])
              simp_all
          have reduced:
            "block_embed j B $ (i, j) $ (a, j) *
                block_embed j C $ (a, j) $ (h, j) +
              (\<Sum>b\<in>UNIV - {j}.
                block_embed j B $ (i, j) $ (a, b) *
                block_embed j C $ (a, b) $ (h, j)) =
              B $ i $ a * C $ a $ h"
            apply (subst selected)
            apply (subst off_sum)
            apply simp
            done
          show ?thesis
            by (rule trans[OF split reduced])
        qed
        have lhs:
          "block_embed j (B ** C) $ (i, k) $ (h, l) =
            (\<Sum>a\<in>UNIV. B $ i $ a * C $ a $ h)"
        proof -
          have block:
            "block_embed j (B ** C) $ (i, k) $ (h, l) =
              (B ** C) $ i $ h"
            apply (subst block_embed_component)
            apply (subst if_P)
             using True k_eq apply blast
            apply (rule refl)
            done
          show ?thesis
            by (rule trans[OF block cartesian_matrix_mult_component])
        qed
        have rhs:
          "(block_embed j B ** block_embed j C) $ (i, k) $ (h, l) =
            (\<Sum>a\<in>UNIV. B $ i $ a * C $ a $ h)"
        proof -
          have "(block_embed j B ** block_embed j C) $ (i, k) $ (h, l) =
              (\<Sum>x\<in>UNIV.
                block_embed j B $ (i, k) $ x *
                block_embed j C $ x $ (h, l))"
            by (rule cartesian_matrix_mult_component)
          also have "\<dots> =
              (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
                block_embed j B $ (i, j) $ (a, b) *
                block_embed j C $ (a, b) $ (h, j))"
            apply (subst sum_UNIV_prod)
            apply (subst k_eq)
            apply (subst True)
            apply (rule refl)
            done
          also have "\<dots> =
              (\<Sum>a\<in>UNIV. B $ i $ a * C $ a $ h)"
          proof (rule sum.cong)
            show "(UNIV :: 'i set) = UNIV"
              by simp
            fix a
            assume "a \<in> (UNIV :: 'i set)"
            show "(\<Sum>b\<in>UNIV.
                block_embed j B $ (i, j) $ (a, b) *
                block_embed j C $ (a, b) $ (h, j)) =
              B $ i $ a * C $ a $ h"
              by (rule inner)
          qed
          finally show ?thesis .
        qed
        show ?thesis
          apply (rule trans[OF lhs])
          apply (rule rhs[symmetric])
          done
      next
        case False
        have column:
          "block_embed j C $ x $ (h, l) =
            of_bool (x = (h, l))"
          for x
        proof -
          obtain a b where x_eq: "x = (a, b)"
            by (cases x) blast
          have pair:
            "block_embed j C $ (a, b) $ (h, l) =
              of_bool ((a, b) = (h, l))"
            by (rule block_embed_column_outside[OF False])
          show ?thesis
            using pair by (simp only: x_eq)
        qed
        have rhs:
          "(block_embed j B ** block_embed j C) $ (i, k) $ (h, l) =
            block_embed j B $ (i, k) $ (h, l)"
        proof -
          have "(block_embed j B ** block_embed j C) $ (i, k) $ (h, l) =
              (\<Sum>x\<in>UNIV.
                block_embed j B $ (i, k) $ x *
                block_embed j C $ x $ (h, l))"
            by (rule cartesian_matrix_mult_component)
          also have "\<dots> =
              (\<Sum>x\<in>UNIV.
                block_embed j B $ (i, k) $ x *
                of_bool (x = (h, l)))"
          proof (rule sum.cong)
            show "(UNIV :: ('i \<times> 'j) set) = UNIV"
              by simp
            fix x
            assume "x \<in> (UNIV :: ('i \<times> 'j) set)"
            show "block_embed j B $ (i, k) $ x *
                block_embed j C $ x $ (h, l) =
              block_embed j B $ (i, k) $ x *
                of_bool (x = (h, l))"
              by (subst column) (rule refl)
          qed
          also have "\<dots> = block_embed j B $ (i, k) $ (h, l)"
            by (rule sum_of_bool_right)
          finally show ?thesis .
        qed
        have lhs_delta:
          "block_embed j (B ** C) $ (i, k) $ (h, l) =
            of_bool ((i, k) = (h, l))"
          by (rule block_embed_column_outside[OF False])
        have rhs_delta:
          "block_embed j B $ (i, k) $ (h, l) =
            of_bool ((i, k) = (h, l))"
          by (rule block_embed_column_outside[OF False])
        have outside:
          "block_embed j (B ** C) $ (i, k) $ (h, l) =
            block_embed j B $ (i, k) $ (h, l)"
          by (rule trans[OF lhs_delta rhs_delta[symmetric]])
        show ?thesis
          by (rule trans[OF outside rhs[symmetric]])
    qed
    have unequal_case:
      "block_embed j (B ** C) $ (i, k) $ (h, l) =
        (block_embed j B ** block_embed j C) $ (i, k) $ (h, l)"
      if k_ne: "k \<noteq> j"
    proof -
      have row:
        "block_embed j B $ (i, k) $ x = of_bool (x = (i, k))"
        for x
      proof -
        obtain a b where x_eq: "x = (a, b)"
          by (cases x) blast
        have "block_embed j B $ (i, k) $ (a, b) =
            of_bool ((i, k) = (a, b))"
          by (rule block_embed_row_outside[OF k_ne])
        also have "\<dots> = of_bool ((a, b) = (i, k))"
          by (simp only: eq_commute)
        finally have pair:
          "block_embed j B $ (i, k) $ (a, b) =
            of_bool ((a, b) = (i, k))" .
        show ?thesis
          using pair by (simp only: x_eq)
      qed
      have rhs:
        "(block_embed j B ** block_embed j C) $ (i, k) $ (h, l) =
          block_embed j C $ (i, k) $ (h, l)"
      proof -
        have "(block_embed j B ** block_embed j C) $ (i, k) $ (h, l) =
            (\<Sum>x\<in>UNIV.
              block_embed j B $ (i, k) $ x *
              block_embed j C $ x $ (h, l))"
          by (rule cartesian_matrix_mult_component)
        also have "\<dots> =
            (\<Sum>x\<in>UNIV.
              of_bool (x = (i, k)) *
              block_embed j C $ x $ (h, l))"
        proof (rule sum.cong)
          show "(UNIV :: ('i \<times> 'j) set) = UNIV"
            by simp
          fix x
          assume "x \<in> (UNIV :: ('i \<times> 'j) set)"
          show "block_embed j B $ (i, k) $ x *
                block_embed j C $ x $ (h, l) =
              of_bool (x = (i, k)) *
                block_embed j C $ x $ (h, l)"
            by (subst row) (rule refl)
        qed
        also have "\<dots> = block_embed j C $ (i, k) $ (h, l)"
          by (rule sum_of_bool_left)
        finally show ?thesis .
      qed
      have lhs_delta:
        "block_embed j (B ** C) $ (i, k) $ (h, l) =
          of_bool ((i, k) = (h, l))"
        by (rule block_embed_row_outside[OF k_ne])
      have rhs_delta:
        "block_embed j C $ (i, k) $ (h, l) =
          of_bool ((i, k) = (h, l))"
        by (rule block_embed_row_outside[OF k_ne])
      have outside:
        "block_embed j (B ** C) $ (i, k) $ (h, l) =
          block_embed j C $ (i, k) $ (h, l)"
        by (rule trans[OF lhs_delta rhs_delta[symmetric]])
      show ?thesis
        by (rule trans[OF outside rhs[symmetric]])
    qed
    have pair_entry:
      "block_embed j (B ** C) $ (i, k) $ (h, l) =
      (block_embed j B ** block_embed j C) $ (i, k) $ (h, l)"
    proof (cases "k = j")
      case True
      then show ?thesis by (rule equal_case)
    next
      case False
      then show ?thesis by (rule unequal_case)
    qed
    show ?thesis
      using pair_entry by (simp only: ik_eq hl_eq)
  qed
  show ?thesis
    apply (subst vec_eq_iff)
    apply (rule allI)
    apply (subst vec_eq_iff)
    apply (rule allI)
    apply (rule entry)
    done
qed

theorem det_block_embed:
  fixes j :: "'j::finite"
    and B :: "'r::field^'i::finite^'i"
  shows "det (block_embed j B) = det B"
proof (rule induct_matrix_elementary_field)
  fix C D :: "'r^'i^'i"
  assume C: "det (block_embed j C) = det C"
    and D: "det (block_embed j D) = det D"
  show "det (block_embed j (C ** D)) = det (C ** D)"
    by (simp only: block_embed_mult det_mul C D)
next
  fix C :: "'r^'i^'i" and i
  assume zero: "row i C = 0"
  have embedded_zero: "row (i, j) (block_embed j C) = 0"
    using zero
    by (auto simp: row_def vec_eq_iff block_embed_def of_bool_def
      split: prod.splits)
  have "det (block_embed j C) = 0"
    by (rule det_zero_row(2)[OF embedded_zero])
  moreover have "det C = 0"
    by (rule det_zero_row(2)[OF zero])
  ultimately show "det (block_embed j C) = det C"
    by simp
next
  fix C :: "'r^'i^'i"
  assume diagonal: "\<And>i h. i \<noteq> h \<Longrightarrow> C $ i $ h = 0"
  have embedded_diagonal:
    "block_embed j C $ ik $ hl = 0" if "ik \<noteq> hl" for ik hl
  proof -
    obtain i k where ik: "ik = (i, k)"
      by (cases ik) blast
    obtain h l where hl: "hl = (h, l)"
      by (cases hl) blast
    show ?thesis
      using that diagonal
      by (auto simp: ik hl block_embed_def of_bool_def)
  qed
  have pair_product:
    "(\<Prod>ik\<in>(UNIV :: ('i \<times> 'j) set).
        block_embed j C $ ik $ ik) =
      (\<Prod>i\<in>UNIV. C $ i $ i)"
  proof -
    have diagonal_entry:
      "block_embed j C $ (i, k) $ (i, k) =
        (if k = j then C $ i $ i else 1)" for i k
      by (cases "k = j")
        (simp_all add: of_bool_def)
    have "(\<Prod>ik\<in>(UNIV :: ('i \<times> 'j) set).
        block_embed j C $ ik $ ik) =
      (\<Prod>i\<in>UNIV. \<Prod>k\<in>UNIV.
        block_embed j C $ (i, k) $ (i, k))"
      by (simp only: UNIV_Times_UNIV[symmetric]
        prod.cartesian_product')
    also have "\<dots> =
      (\<Prod>i\<in>UNIV. \<Prod>k\<in>UNIV.
        if k = j then C $ i $ i else 1)"
      by (intro prod.cong refl; rule diagonal_entry)
    also have "\<dots> = (\<Prod>i\<in>UNIV. C $ i $ i)"
      by (simp only: prod_if_eq)
    finally show ?thesis .
  qed
  have "det (block_embed j C) =
      (\<Prod>ik\<in>UNIV. block_embed j C $ ik $ ik)"
    by (rule det_diagonal) (rule embedded_diagonal)
  also have "\<dots> = (\<Prod>i\<in>UNIV. C $ i $ i)"
    by (rule pair_product)
  also have "\<dots> = det C"
    by (rule det_diagonal[OF diagonal, symmetric])
  finally show "det (block_embed j C) = det C" .
next
  fix m n :: 'i
  assume mn: "m \<noteq> n"
  let ?C = "\<chi> i h.
    mat 1 $ i $ Transposition.transpose m n h :: 'r^'i^'i"
  let ?D = "\<chi> ik hl.
    mat 1 $ ik $ Transposition.transpose (m, j) (n, j) hl ::
      'r^('i \<times> 'j)^('i \<times> 'j)"
  have embedded: "block_embed j ?C = ?D"
    using mn
    by (auto simp: vec_eq_iff block_embed_def mat_def of_bool_def
      Transposition.transpose_def split: prod.splits)
  have permutes_C:
    "Transposition.transpose m n permutes (UNIV :: 'i set)"
    by (rule permutes_swap_id) simp_all
  have sign_C: "sign (Transposition.transpose m n) = -1"
    by (simp add: sign_swap_id mn)
  have det_C: "det ?C = -1"
    using det_permute_columns[OF permutes_C,
      of "mat 1 :: 'r^'i^'i"]
    by (simp add: sign_C)
  have pair_ne: "(m, j) \<noteq> (n, j)"
    using mn by simp
  have permutes_D:
    "Transposition.transpose (m, j) (n, j) permutes
      (UNIV :: ('i \<times> 'j) set)"
    by (rule permutes_swap_id) simp_all
  have sign_D:
    "sign (Transposition.transpose (m, j) (n, j)) = -1"
  proof -
    have "sign (Transposition.transpose (m, j) (n, j)) =
      (if (m, j) = (n, j) then 1 else -1)"
      by (rule sign_swap_id)
    then show ?thesis
      using pair_ne by simp
  qed
  have det_D: "det ?D = -1"
    using det_permute_columns[OF permutes_D,
      of "mat 1 :: 'r^('i \<times> 'j)^('i \<times> 'j)"]
    by (simp add: sign_D)
  show "det (block_embed j ?C) = det ?C"
    by (simp only: embedded det_C det_D)
next
  fix m n :: 'i and c :: 'r
  assume mn: "m \<noteq> n"
  let ?C = "\<chi> i h.
    if i = m \<and> h = n then c else of_bool (i = h) :: 'r^'i^'i"
  let ?D = "\<chi> ik hl.
    if ik = (m, j) \<and> hl = (n, j)
    then c else of_bool (ik = hl) ::
      'r^('i \<times> 'j)^('i \<times> 'j)"
  have embedded: "block_embed j ?C = ?D"
    using mn
    by (auto simp: vec_eq_iff block_embed_def of_bool_def
      split: prod.splits)
  have C_row:
    "?C = (\<chi> i.
      if i = m
      then row m (mat 1) + c *s row n (mat 1)
      else row i (mat 1))"
    using mn
    by (auto simp: vec_eq_iff row_def mat_def of_bool_def)
  have D_row:
    "?D = (\<chi> ik.
      if ik = (m, j)
      then row (m, j) (mat 1) + c *s row (n, j) (mat 1)
      else row ik (mat 1))"
    using mn
    by (auto simp: vec_eq_iff row_def mat_def of_bool_def
      split: prod.splits)
  have det_C: "det ?C = 1"
    unfolding C_row
    by (subst det_row_operation[OF mn]) simp
  have det_D: "det ?D = 1"
    unfolding D_row
    by (subst det_row_operation)
      (simp_all add: mn)
  show "det (block_embed j ?C) = det ?C"
    by (simp only: embedded det_C det_D)
qed

definition block_swap_entries ::
    "'i::finite set \<Rightarrow> 'j::finite \<Rightarrow> 'j \<Rightarrow>
      'r::comm_ring_1^('i \<times> 'j)^('i \<times> 'j)"
  where "block_swap_entries X m n =
    (\<chi> ik hl. mat 1 $ ik $
      (if fst hl \<in> X
       then (fst hl, Transposition.transpose m n (snd hl))
       else hl))"

definition block_swap ::
    "'j::finite \<Rightarrow> 'j \<Rightarrow>
      'r::comm_ring_1^('i::finite \<times> 'j)^('i \<times> 'j)"
  where "block_swap m n = block_swap_entries UNIV m n"

lemma block_swap_entries_empty [simp]:
  "block_swap_entries {} m n =
    (mat 1 :: 'r::comm_ring_1^('i::finite \<times> 'j::finite)^
      ('i \<times> 'j))"
  by (vector block_swap_entries_def)

lemma block_swap_entries_insert:
  fixes X :: "'i::finite set"
    and m n :: "'j::finite"
  assumes "a \<notin> X"
  shows "block_swap_entries (insert a X) m n =
    (\<chi> ik hl. block_swap_entries X m n $ ik $
      Transposition.transpose (a, m) (a, n) hl)"
  using assms
  by (auto simp: vec_eq_iff block_swap_entries_def mat_def
    Transposition.transpose_def split: prod.splits)

lemma det_block_swap_entries:
  fixes X :: "'i::finite set"
    and m n :: "'j::finite"
  assumes "m \<noteq> n"
  shows "det (block_swap_entries X m n ::
      'r::field^('i \<times> 'j)^('i \<times> 'j)) =
    (-1) ^ card X"
proof -
  have "finite X"
    by simp
  then show ?thesis
  proof (induction X rule: finite_induct)
    case empty
    show ?case
      by simp
  next
    case (insert a X)
    have pair_ne: "(a, m) \<noteq> (a, n)"
      using assms by simp
    have permutes:
      "Transposition.transpose (a, m) (a, n) permutes
        (UNIV :: ('i \<times> 'j) set)"
      by (rule permutes_swap_id) simp_all
    have sign:
      "sign (Transposition.transpose (a, m) (a, n)) = -1"
    proof -
      have "sign (Transposition.transpose (a, m) (a, n)) =
        (if (a, m) = (a, n) then 1 else -1)"
        by (rule sign_swap_id)
      then show ?thesis
        using pair_ne by simp
    qed
    have "det (block_swap_entries (insert a X) m n ::
        'r^('i \<times> 'j)^('i \<times> 'j)) =
      det (\<chi> ik hl. block_swap_entries X m n $ ik $
        Transposition.transpose (a, m) (a, n) hl)"
      by (simp only: block_swap_entries_insert[OF insert.hyps(2)])
    also have "\<dots> =
      of_int (sign (Transposition.transpose (a, m) (a, n))) *
        det (block_swap_entries X m n)"
      by (rule det_permute_columns[OF permutes])
    also have "\<dots> = (-1) ^ card (insert a X)"
      by (simp add: sign insert.hyps insert.IH)
    finally show ?case .
  qed
qed

theorem det_block_swap:
  fixes m n :: "'j::finite"
  assumes "m \<noteq> n"
  shows "det (block_swap m n ::
      'r::field^('i::finite \<times> 'j)^('i \<times> 'j)) =
    (-1) ^ CARD('i)"
  unfolding block_swap_def
  by (simp add: det_block_swap_entries[OF assms])

definition block_shear_entries ::
    "('i::finite \<times> 'i) set \<Rightarrow> 'j::finite \<Rightarrow> 'j \<Rightarrow>
      'r::comm_ring_1^'i^'i \<Rightarrow>
      'r^('i \<times> 'j)^('i \<times> 'j)"
  where "block_shear_entries X m n B =
    (\<chi> ik hl.
      if snd ik = m \<and> snd hl = n \<and> (fst ik, fst hl) \<in> X
      then B $ fst ik $ fst hl
      else of_bool (ik = hl))"

definition block_shear ::
    "'j::finite \<Rightarrow> 'j \<Rightarrow> 'r::comm_ring_1^'i::finite^'i \<Rightarrow>
      'r^('i \<times> 'j)^('i \<times> 'j)"
  where "block_shear m n B = block_shear_entries UNIV m n B"

lemma block_shear_entries_empty [simp]:
  "block_shear_entries {} m n B =
    (mat 1 :: 'r::comm_ring_1^('i::finite \<times> 'j::finite)^
      ('i \<times> 'j))"
  by (vector block_shear_entries_def mat_def of_bool_def)

lemma block_shear_entries_insert:
  fixes X :: "('i::finite \<times> 'i) set"
    and m n :: "'j::finite"
    and B :: "'r::comm_ring_1^'i^'i"
  assumes pair_out: "(i, h) \<notin> X"
    and mn: "m \<noteq> n"
  shows "block_shear_entries (insert (i, h) X) m n B =
    (\<chi> ik.
      if ik = (i, m)
      then row (i, m) (block_shear_entries X m n B) +
        (B $ i $ h) *s row (h, n) (block_shear_entries X m n B)
      else row ik (block_shear_entries X m n B))"
  using pair_out mn
  by (auto simp: vec_eq_iff row_def block_shear_entries_def
    of_bool_def split: prod.splits)

lemma det_block_shear_entries:
  fixes X :: "('i::finite \<times> 'i) set"
    and m n :: "'j::finite"
    and B :: "'r::field^'i^'i"
  assumes "m \<noteq> n"
  shows "det (block_shear_entries X m n B) = 1"
proof -
  have "finite X"
    by simp
  then show ?thesis
  proof (induction X rule: finite_induct)
    case empty
    show ?case
      by simp
  next
    case (insert ih X)
    obtain i h where ih: "ih = (i, h)"
      by (cases ih) blast
    have pair_out: "(i, h) \<notin> X"
      using insert.hyps(2) ih by simp
    have row_form:
      "block_shear_entries (insert ih X) m n B =
        (\<chi> ik.
          if ik = (i, m)
          then row (i, m) (block_shear_entries X m n B) +
            (B $ i $ h) *s row (h, n)
              (block_shear_entries X m n B)
          else row ik (block_shear_entries X m n B))"
      unfolding ih
      by (rule block_shear_entries_insert[OF pair_out assms])
    have pair_ne: "(i, m) \<noteq> (h, n)"
      using assms by auto
    have "det (block_shear_entries (insert ih X) m n B) =
      det (block_shear_entries X m n B)"
      unfolding row_form
      by (rule det_row_operation[OF pair_ne])
    also have "\<dots> = 1"
      by (rule insert.IH)
    finally show ?case .
  qed
qed

theorem det_block_shear:
  fixes m n :: "'j::finite"
    and B :: "'r::field^'i::finite^'i"
  assumes "m \<noteq> n"
  shows "det (block_shear m n B) = 1"
  unfolding block_shear_def
  by (rule det_block_shear_entries[OF assms])

context indexed_algebra
begin

lemma regular_matrix_sum:
  "regular_matrix (\<Sum>x\<in>X. f x) =
    (\<Sum>x\<in>X. regular_matrix (f x))"
  by (induction X rule: infinite_finite_induct)
    (simp_all add: regular_matrix_add)

definition algebra_norm :: "'a \<Rightarrow> 'r"
  where "algebra_norm a = det (regular_matrix a)"

lemma algebra_norm_zero [simp]:
  "algebra_norm 0 = 0"
proof -
  have zero_matrix: "(0 :: 'r^'i^'i) = mat 0"
    by (vector mat_def)
  have "regular_matrix 0 = (mat 0 :: 'r^'i^'i)"
    by (simp only: regular_matrix_zero zero_matrix)
  then show ?thesis
    by (simp only: algebra_norm_def det_0)
qed

lemma algebra_norm_one [simp]:
  "algebra_norm 1 = 1"
  by (simp add: algebra_norm_def)

theorem algebra_norm_mult:
  "algebra_norm (a * b) = algebra_norm a * algebra_norm b"
  by (simp add: algebra_norm_def regular_matrix_mult det_mul)

lemma algebra_norm_scalar:
  "algebra_norm (scale r 1) = r ^ CARD('i)"
proof -
  have "det (mat r :: 'r^'i^'i) =
    (\<Prod>i\<in>UNIV. (mat r :: 'r^'i^'i) $ i $ i)"
    by (rule det_diagonal) (simp add: mat_def)
  also have "\<dots> = r ^ CARD('i)"
    by (simp add: mat_def)
  finally show ?thesis
    by (simp add: algebra_norm_def regular_matrix_scalar_embed)
qed

end

context indexed_algebra_reindex
begin

theorem algebra_norm_reindexed:
  "reindexed.algebra_norm a = original.algebra_norm a"
proof -
  have matrix_reindexed:
    "reindexed.regular_matrix a =
      (\<chi> i k. original.regular_matrix a $
        index_iso i $ index_iso k)"
    by (vector regular_matrix_reindexed_component)
  show ?thesis
    unfolding reindexed.algebra_norm_def original.algebra_norm_def
    unfolding matrix_reindexed
    by (rule det_reindex_bij[OF index_iso_bij])
qed

end

context indexed_basis_pair
begin

theorem det_matrix_change_basis:
  assumes "module_hom scale scale f"
  shows "det (second.matrix_of f) = det (first.matrix_of f)"
proof -
  have inverse_determinants:
    "det to_first * det to_second = 1"
  proof -
    have "det (to_first ** to_second) =
      det (mat 1 :: 'r^'i^'i)"
      by (simp only: to_first_to_second)
    then show ?thesis
      by (simp add: det_mul)
  qed
  have "det (second.matrix_of f) =
    det ((to_second ** first.matrix_of f) ** to_first)"
    by (simp only: matrix_change_basis[OF assms])
  also have "\<dots> =
    det to_second * det (first.matrix_of f) * det to_first"
    by (simp add: det_mul)
  also have "\<dots> =
    det (first.matrix_of f) * (det to_first * det to_second)"
    by (simp only: mult.assoc mult.left_commute mult.commute)
  also have "\<dots> = det (first.matrix_of f)"
    by (simp add: inverse_determinants)
  finally show ?thesis .
qed

end

context indexed_algebra
begin

theorem algebra_norm_basis_independent:
  fixes other_basis :: "'i \<Rightarrow> 'a"
  assumes other_inj: "inj other_basis"
    and other_independent: "independent (range other_basis)"
    and other_span: "span (range other_basis) = UNIV"
  shows "algebra_norm a =
    indexed_algebra.algebra_norm scale other_basis a"
proof -
  interpret other: indexed_algebra scale other_basis
    by unfold_locales
      (fact other_inj other_independent other_span)+
  interpret change: indexed_basis_pair scale basis other_basis
    by unfold_locales
      (fact basis_inj basis_independent basis_span
        other_inj other_independent other_span)+
  have "det (other.regular_matrix a) = det (regular_matrix a)"
    unfolding other.regular_matrix_def regular_matrix_def
    by (rule change.det_matrix_change_basis)
      (rule left_multiplication_module_hom)
  then show ?thesis
    by (simp add: algebra_norm_def other.algebra_norm_def)
qed

theorem algebra_norm_basis_independent_bij:
  fixes other_basis :: "'j::finite \<Rightarrow> 'a"
    and index_iso :: "'i \<Rightarrow> 'j"
  assumes other_inj: "inj other_basis"
    and other_independent: "independent (range other_basis)"
    and other_span: "span (range other_basis) = UNIV"
    and index_iso_bij: "bij index_iso"
  shows "algebra_norm a =
    indexed_algebra.algebra_norm scale other_basis a"
proof -
  interpret other: indexed_algebra scale other_basis
    by unfold_locales
      (fact other_inj other_independent other_span)+
  interpret reindex:
    indexed_algebra_reindex scale other_basis index_iso
    by unfold_locales
      (fact other_inj other_independent other_span index_iso_bij)+
  have "algebra_norm a = reindex.reindexed.algebra_norm a"
    by (rule algebra_norm_basis_independent)
      (fact reindex.reindexed.basis_inj
        reindex.reindexed.basis_independent
        reindex.reindexed.basis_span)+
  also have "\<dots> = other.algebra_norm a"
    by (rule reindex.algebra_norm_reindexed)
  finally show ?thesis .
qed

end

context indexed_algebra_isomorphism
begin

theorem algebra_norm_iso:
  "target.algebra_norm (iso a) = source.algebra_norm a"
  by (simp add: target.algebra_norm_def source.algebra_norm_def
    regular_matrix_iso)

end

context indexed_algebra_isomorphism_general
begin

theorem algebra_norm_iso:
  "target.algebra_norm (iso a) = source.algebra_norm a"
proof -
  have basis_change:
    "transported.algebra_norm (iso a) =
      target.algebra_norm (iso a)"
    by (rule transported.algebra_norm_basis_independent_bij)
      (fact target.basis_inj target.basis_independent
        target.basis_span index_iso_bij)+
  have transported:
    "transported.algebra_norm (iso a) =
      source.algebra_norm a"
    by (rule basis_iso.algebra_norm_iso)
  show ?thesis
    using basis_change transported by simp
qed

end

locale indexed_field_algebra_tower =
  indexed_algebra_tower rS sA rA lower_basis upper_basis
  for rS :: "'r::field \<Rightarrow> 's::field \<Rightarrow> 's"
    and sA :: "'s \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and rA :: "'r \<Rightarrow> 'a \<Rightarrow> 'a"
    and lower_basis :: "'i::finite \<Rightarrow> 's"
    and upper_basis :: "'j::finite \<Rightarrow> 'a"
begin

definition restricted_matrix ::
    "'s^'j^'j \<Rightarrow> 'r^('i \<times> 'j)^('i \<times> 'j)"
  where "restricted_matrix M =
    (\<chi> ik hl.
      lower_algebra.regular_matrix (M $ snd ik $ snd hl) $
        fst ik $ fst hl)"

lemma restricted_matrix_component [simp]:
  "restricted_matrix M $ (i, j) $ (h, l) =
    lower_algebra.regular_matrix (M $ j $ l) $ i $ h"
  by (simp add: restricted_matrix_def)

lemma restricted_matrix_zero [simp]:
  "restricted_matrix 0 = 0"
  by (auto simp: vec_eq_iff restricted_matrix_def split: prod.splits)

lemma restricted_matrix_one [simp]:
  "restricted_matrix (mat 1) = mat 1"
  by (auto simp: vec_eq_iff restricted_matrix_def mat_def of_bool_def
    split: prod.splits)

lemma restricted_matrix_mult:
  "restricted_matrix (B ** C) =
    restricted_matrix B ** restricted_matrix C"
proof -
  have entry:
    "restricted_matrix (B ** C) $ (i, j) $ (h, l) =
      (restricted_matrix B ** restricted_matrix C) $ (i, j) $ (h, l)"
    for i j h l
  proof -
    have lhs:
      "restricted_matrix (B ** C) $ (i, j) $ (h, l) =
        (\<Sum>k\<in>UNIV. \<Sum>a\<in>UNIV.
          lower_algebra.regular_matrix (B $ j $ k) $ i $ a *
          lower_algebra.regular_matrix (C $ k $ l) $ a $ h)"
    proof -
      have "restricted_matrix (B ** C) $ (i, j) $ (h, l) =
        lower_algebra.regular_matrix ((B ** C) $ j $ l) $ i $ h"
        by (rule restricted_matrix_component)
      also have "\<dots> =
        lower_algebra.regular_matrix
          (\<Sum>k\<in>UNIV. B $ j $ k * C $ k $ l) $ i $ h"
        by (simp only: matrix_matrix_mult_def vec_lambda_beta)
      also have "\<dots> =
        (\<Sum>k\<in>UNIV.
          lower_algebra.regular_matrix (B $ j $ k * C $ k $ l)) $ i $ h"
        by (simp only: lower_algebra.regular_matrix_sum)
      also have "\<dots> =
        (\<Sum>k\<in>UNIV.
          lower_algebra.regular_matrix (B $ j $ k * C $ k $ l) $
            i $ h)"
        by simp
      also have "\<dots> =
        (\<Sum>k\<in>UNIV.
          (lower_algebra.regular_matrix (B $ j $ k) **
            lower_algebra.regular_matrix (C $ k $ l)) $ i $ h)"
      proof (rule sum.cong)
        show "(UNIV :: 'j set) = UNIV"
          by simp
        fix k
        assume "k \<in> (UNIV :: 'j set)"
        show "lower_algebra.regular_matrix
              (B $ j $ k * C $ k $ l) $ i $ h =
            (lower_algebra.regular_matrix (B $ j $ k) **
              lower_algebra.regular_matrix (C $ k $ l)) $ i $ h"
          by (simp only: lower_algebra.regular_matrix_mult)
      qed
      also have "\<dots> =
        (\<Sum>k\<in>UNIV. \<Sum>a\<in>UNIV.
          lower_algebra.regular_matrix (B $ j $ k) $ i $ a *
          lower_algebra.regular_matrix (C $ k $ l) $ a $ h)"
        by (simp only: matrix_matrix_mult_def vec_lambda_beta)
      finally show ?thesis .
    qed
    have rhs:
      "(restricted_matrix B ** restricted_matrix C) $ (i, j) $ (h, l) =
        (\<Sum>a\<in>UNIV. \<Sum>k\<in>UNIV.
          lower_algebra.regular_matrix (B $ j $ k) $ i $ a *
          lower_algebra.regular_matrix (C $ k $ l) $ a $ h)"
    proof -
      have "(restricted_matrix B ** restricted_matrix C) $
          (i, j) $ (h, l) =
        (\<Sum>x\<in>UNIV.
          restricted_matrix B $ (i, j) $ x *
          restricted_matrix C $ x $ (h, l))"
        by (simp add: matrix_matrix_mult_def)
      also have "\<dots> =
        (\<Sum>a\<in>UNIV. \<Sum>k\<in>UNIV.
          restricted_matrix B $ (i, j) $ (a, k) *
          restricted_matrix C $ (a, k) $ (h, l))"
        by (simp only: sum_UNIV_prod)
      also have "\<dots> =
        (\<Sum>a\<in>UNIV. \<Sum>k\<in>UNIV.
          lower_algebra.regular_matrix (B $ j $ k) $ i $ a *
          lower_algebra.regular_matrix (C $ k $ l) $ a $ h)"
        by (simp only: restricted_matrix_component)
      finally show ?thesis .
    qed
    have swapped:
      "(\<Sum>k\<in>UNIV. \<Sum>a\<in>UNIV.
          lower_algebra.regular_matrix (B $ j $ k) $ i $ a *
          lower_algebra.regular_matrix (C $ k $ l) $ a $ h) =
        (\<Sum>a\<in>UNIV. \<Sum>k\<in>UNIV.
          lower_algebra.regular_matrix (B $ j $ k) $ i $ a *
          lower_algebra.regular_matrix (C $ k $ l) $ a $ h)"
      by (rule sum.swap)
    show ?thesis
      by (rule trans[OF lhs trans[OF swapped rhs[symmetric]]])
  qed
  show ?thesis
  proof (subst vec_eq_iff, intro allI)
    fix ik :: "'i \<times> 'j"
    obtain i j where ik: "ik = (i, j)"
      by (cases ik) blast
    show "restricted_matrix (B ** C) $ ik =
      (restricted_matrix B ** restricted_matrix C) $ ik"
    proof (subst vec_eq_iff, intro allI)
      fix hl :: "'i \<times> 'j"
      obtain h l where hl: "hl = (h, l)"
        by (cases hl) blast
      show "restricted_matrix (B ** C) $ ik $ hl =
        (restricted_matrix B ** restricted_matrix C) $ ik $ hl"
        unfolding ik hl
        by (rule entry)
    qed
  qed
qed

definition diagonal_factor :: "'j \<Rightarrow> 's \<Rightarrow> 's^'j^'j"
  where "diagonal_factor j x =
    (\<chi> k l. if k = j \<and> l = j then x else of_bool (k = l))"

definition partial_diagonal :: "'j set \<Rightarrow> 's^'j^'j \<Rightarrow> 's^'j^'j"
  where "partial_diagonal X M =
    (\<chi> k l.
      if k = l
      then if k \<in> X then M $ k $ k else 1
      else 0)"

lemma det_diagonal_factor:
  "det (diagonal_factor j x) = x"
proof -
  have diagonal:
    "diagonal_factor j x $ k $ l = 0" if "k \<noteq> l" for k l
    using that
    by (auto simp: diagonal_factor_def of_bool_def)
  have entry:
    "diagonal_factor j x $ k $ k =
      (if k = j then x else 1)" for k
    by (cases "k = j")
      (simp_all add: diagonal_factor_def of_bool_def)
  have "det (diagonal_factor j x) =
    (\<Prod>k\<in>UNIV. diagonal_factor j x $ k $ k)"
    by (rule det_diagonal[OF diagonal])
  also have "\<dots> =
    (\<Prod>k\<in>UNIV. if k = j then x else 1)"
    by (intro prod.cong refl; rule entry)
  also have "\<dots> = x"
    by (rule prod_if_eq)
  finally show ?thesis .
qed

lemma diagonal_factor_component_alt:
  "diagonal_factor j x $ k $ l =
    of_bool (k = l) * (if k = j then x else 1)"
  by (auto simp: diagonal_factor_def of_bool_def)

lemma restricted_diagonal_factor:
  "restricted_matrix (diagonal_factor j x) =
    block_embed j (lower_algebra.regular_matrix x)"
  by (auto simp: vec_eq_iff restricted_matrix_def diagonal_factor_def
    block_embed_def of_bool_def mat_def split: prod.splits)

lemma partial_diagonal_empty [simp]:
  "partial_diagonal {} M = mat 1"
  by (vector partial_diagonal_def mat_def)

lemma partial_diagonal_UNIV:
  assumes diagonal: "\<And>k l. k \<noteq> l \<Longrightarrow> M $ k $ l = 0"
  shows "partial_diagonal UNIV M = M"
  using diagonal
  by (auto simp: vec_eq_iff partial_diagonal_def)

lemma partial_diagonal_insert:
  assumes "j \<notin> X"
  shows "partial_diagonal (insert j X) M =
    diagonal_factor j (M $ j $ j) ** partial_diagonal X M"
proof -
  have mult_entry:
    "(diagonal_factor j (M $ j $ j) ** partial_diagonal X M) $
        k $ l =
      (if k = j then M $ j $ j else 1) *
        partial_diagonal X M $ k $ l" for k l
  proof -
    have "(diagonal_factor j (M $ j $ j) ** partial_diagonal X M) $
        k $ l =
      (\<Sum>a\<in>UNIV.
        diagonal_factor j (M $ j $ j) $ k $ a *
        partial_diagonal X M $ a $ l)"
      by (simp only: matrix_matrix_mult_def vec_lambda_beta)
    also have "\<dots> =
      diagonal_factor j (M $ j $ j) $ k $ k *
        partial_diagonal X M $ k $ l"
      by (subst sum.remove[of UNIV k])
        (auto simp: diagonal_factor_component_alt of_bool_def)
    also have "\<dots> =
      (if k = j then M $ j $ j else 1) *
        partial_diagonal X M $ k $ l"
      by (simp add: diagonal_factor_component_alt of_bool_def)
    finally show ?thesis .
  qed
  show ?thesis
  proof (subst vec_eq_iff, intro allI)
    fix k
    show "partial_diagonal (insert j X) M $ k =
      (diagonal_factor j (M $ j $ j) ** partial_diagonal X M) $ k"
    proof (subst vec_eq_iff, intro allI)
      fix l
      show "partial_diagonal (insert j X) M $ k $ l =
        (diagonal_factor j (M $ j $ j) ** partial_diagonal X M) $ k $ l"
        using assms
        by (subst mult_entry)
          (auto simp: partial_diagonal_def)
    qed
  qed
qed

lemma restricted_swap:
  assumes "m \<noteq> n"
  shows "restricted_matrix
      (\<chi> j l. mat 1 $ j $ Transposition.transpose m n l) =
    block_swap m n"
  using assms
  by (auto simp: vec_eq_iff restricted_matrix_def block_swap_def
    block_swap_entries_def mat_def of_bool_def
    Transposition.transpose_def split: prod.splits)

lemma restricted_shear:
  assumes "m \<noteq> n"
  shows "restricted_matrix
      (\<chi> j l. if j = m \<and> l = n then c else of_bool (j = l)) =
    block_shear m n (lower_algebra.regular_matrix c)"
  using assms
  by (auto simp: vec_eq_iff restricted_matrix_def block_shear_def
    block_shear_entries_def of_bool_def mat_def split: prod.splits)

theorem det_restrict_scalars:
  "det (restricted_matrix M) =
    lower_algebra.algebra_norm (det M)"
proof -
  let ?P = "\<lambda>M. det (restricted_matrix M) =
    lower_algebra.algebra_norm (det M)"
  have mult_P: "?P (B ** C)" if "?P B" "?P C" for B C
    using that
    by (simp only: restricted_matrix_mult det_mul
      lower_algebra.algebra_norm_mult)
  have one_P: "?P (mat 1)"
    by simp
  show "?P M"
  proof (rule induct_matrix_elementary_field[where P = ?P])
    fix B C :: "'s^'j^'j"
    assume "?P B" "?P C"
    then show "?P (B ** C)"
      by (rule mult_P)
  next
    fix B :: "'s^'j^'j" and j
    assume zero: "row j B = 0"
    have zero_entry: "B $ j $ l = 0" for l
      using zero
      by (simp add: row_def vec_eq_iff)
    have restricted_zero:
      "row (undefined, j) (restricted_matrix B) = 0"
      using zero_entry
      by (auto simp: row_def vec_eq_iff restricted_matrix_def split: prod.splits)
    have det_restricted: "det (restricted_matrix B) = 0"
      by (rule det_zero_row(2)[OF restricted_zero])
    have det_B: "det B = 0"
      by (rule det_zero_row(2)[OF zero])
    show "?P B"
      by (simp only: det_restricted det_B
        lower_algebra.algebra_norm_zero)
  next
    fix B :: "'s^'j^'j"
    assume diagonal: "\<And>j l. j \<noteq> l \<Longrightarrow> B $ j $ l = 0"
    have factor_P:
      "?P (diagonal_factor j (B $ j $ j))" for j
      unfolding lower_algebra.algebra_norm_def
      by (simp only: restricted_diagonal_factor det_block_embed
        det_diagonal_factor)
    have partial_P: "?P (partial_diagonal X B)" for X
    proof -
      have "finite X"
        by simp
      then show ?thesis
      proof (induction X rule: finite_induct)
        case empty
        show ?case
          by (simp only: partial_diagonal_empty one_P)
      next
        case (insert j X)
        have "?P
          (diagonal_factor j (B $ j $ j) ** partial_diagonal X B)"
          by (rule mult_P[OF factor_P insert.IH])
        then show ?case
          by (simp only: partial_diagonal_insert[OF insert.hyps(2)])
      qed
    qed
    have partial_eq:
      "partial_diagonal (UNIV :: 'j set) B = B"
      by (rule partial_diagonal_UNIV[OF diagonal])
    have partial_result:
      "?P (partial_diagonal (UNIV :: 'j set) B)"
      by (rule partial_P)
    from partial_result show "?P B"
      unfolding partial_eq .
  next
    fix m n :: 'j
    assume mn: "m \<noteq> n"
    let ?B = "\<chi> j l.
      mat 1 $ j $ Transposition.transpose m n l :: 's^'j^'j"
    have permutes:
      "Transposition.transpose m n permutes (UNIV :: 'j set)"
      by (rule permutes_swap_id) simp_all
    have sign: "sign (Transposition.transpose m n) = -1"
      by (simp add: sign_swap_id mn)
    have det_B: "det ?B = -1"
      using det_permute_columns[OF permutes,
        of "mat 1 :: 's^'j^'j"]
      by (simp add: sign)
    have norm_neg_one:
      "lower_algebra.algebra_norm (-1) =
        (-1 :: 'r) ^ CARD('i)"
    proof -
      have "lower_algebra.algebra_norm (rS (-1) 1) =
        (-1 :: 'r) ^ CARD('i)"
        by (rule lower_algebra.algebra_norm_scalar)
      then show ?thesis
        by simp
    qed
    have det_restricted:
      "det (restricted_matrix ?B) = (-1 :: 'r) ^ CARD('i)"
      by (simp only: restricted_swap[OF mn] det_block_swap[OF mn])
    show "?P ?B"
      by (simp only: det_restricted det_B norm_neg_one)
  next
    fix m n :: 'j and c :: 's
    assume mn: "m \<noteq> n"
    let ?B = "\<chi> j l.
      if j = m \<and> l = n then c else of_bool (j = l) :: 's^'j^'j"
    have B_row:
      "?B = (\<chi> j.
        if j = m
        then row m (mat 1) + c *s row n (mat 1)
        else row j (mat 1))"
      using mn
      by (auto simp: vec_eq_iff row_def mat_def of_bool_def)
    have det_B: "det ?B = 1"
      unfolding B_row
      by (subst det_row_operation[OF mn]) simp
    have det_restricted: "det (restricted_matrix ?B) = 1"
      by (simp only: restricted_shear[OF mn]
        det_block_shear[OF mn])
    show "?P ?B"
      by (simp only: det_restricted det_B
        lower_algebra.algebra_norm_one)
  qed
qed

theorem matrix_restrict_scalars:
  assumes f: "module_hom sA sA f"
  shows "composed.matrix_of f =
    restricted_matrix (upper.matrix_of f)"
proof -
  interpret f: module_hom sA sA f
    by fact
  have entry:
    "composed.matrix_of f $ (i, j) $ (h, l) =
      restricted_matrix (upper.matrix_of f) $ (i, j) $ (h, l)"
    for i j h l
  proof -
    have "composed.matrix_of f $ (i, j) $ (h, l) =
      composed.coordinate (f (tower_basis (h, l))) (i, j)"
      by simp
    also have "\<dots> =
      tower_coordinate (f (tower_basis (h, l))) (i, j)"
      by (rule composed_coordinate)
    also have "\<dots> =
      tower_coordinate
        (f (sA (lower_basis h) (upper_basis l))) (i, j)"
      by (simp only: tower_basis_def fst_conv snd_conv)
    also have "\<dots> =
      tower_coordinate
        (sA (lower_basis h) (f (upper_basis l))) (i, j)"
      by (simp only: f.scale)
    also have "\<dots> =
      lower.coordinate
        (lower_basis h *
          upper.coordinate (f (upper_basis l)) j) i"
      by (simp add: tower_coordinate_def)
    also have "\<dots> =
      lower.coordinate
        (upper.coordinate (f (upper_basis l)) j *
          lower_basis h) i"
      by (simp only: mult.commute)
    also have "\<dots> =
      lower_algebra.regular_matrix
        (upper.matrix_of f $ j $ l) $ i $ h"
      by (simp add: lower_algebra.regular_matrix_def
        RS.left_multiplication_def)
    also have "\<dots> =
      restricted_matrix (upper.matrix_of f) $ (i, j) $ (h, l)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (subst vec_eq_iff, intro allI)
    fix ik :: "'i \<times> 'j"
    obtain i j where ik: "ik = (i, j)"
      by (cases ik) blast
    show "composed.matrix_of f $ ik =
      restricted_matrix (upper.matrix_of f) $ ik"
    proof (subst vec_eq_iff, intro allI)
      fix hl :: "'i \<times> 'j"
      obtain h l where hl: "hl = (h, l)"
        by (cases hl) blast
      show "composed.matrix_of f $ ik $ hl =
        restricted_matrix (upper.matrix_of f) $ ik $ hl"
        unfolding ik hl
        by (rule entry)
    qed
  qed
qed

theorem algebra_norm_trans:
  "tower_algebra.algebra_norm a =
    lower_algebra.algebra_norm (upper_algebra.algebra_norm a)"
  by (simp add: SA.left_multiplication_module_hom
      det_restrict_scalars indexed_algebra.algebra_norm_def
      matrix_restrict_scalars tower_algebra.algebra_norm_def
      tower_algebra.regular_matrix_def
      upper_algebra.indexed_algebra_axioms
      upper_algebra.regular_matrix_def)

end

end
