(* License: LGPL *)

theory TSP_Dyn_Prog
imports Main
begin


section \<open>The Bellman–-Held–-Karp approach to TSP\<close>


subsection \<open>Hamiltonian paths\<close>

text \<open>A Hamiltonian path from a vertex $s$ to a vertex $t$ via a (finite) set $V$ has to pass 
      through each vertex in $V$ exactly once.
      This can be captured by a list that starts with $s$, ends with $t$ and has a distinct list
      containing all vertices from $V$ (i.e. essentially the same as a permutation on $V$) in-between.

      In particular, with $s = t$ one gets a representation of a Hamiltonian cycle from $s$ via $V$.

      Also note that $s$ or $t$ might in principle occur in $V$ as well.\<close>

definition
"Hamiltonian_paths s V t = {s#vs@[t] |vs. distinct vs \<and> set vs = V}"


text \<open>By the above definition, a Hamiltonian path exists only for a finite $V$:\<close>
lemma Hamiltonian_paths_not_empty :
"finite V = (\<exists>p. p \<in> Hamiltonian_paths s V t)"
  using Hamiltonian_paths_def finite_distinct_list by fastforce


lemma Hamiltonian_paths_finite :
"finite(Hamiltonian_paths s V t)"
proof(cases "finite V")
  case a:True
  show ?thesis
  proof(rule_tac B="(\<lambda>vs. s#vs@[t]) ` {vs. set vs \<subseteq> V \<and> distinct vs}" in finite_subset)
    show "Hamiltonian_paths s V t \<subseteq> (\<lambda>vs. s # vs @ [t]) ` {vs. set vs \<subseteq> V \<and> distinct vs}"
      by(clarsimp simp: Hamiltonian_paths_def)
  next
    from a show "finite ((\<lambda>vs. s#vs@[t]) ` {vs. set vs \<subseteq> V \<and> distinct vs})"
      by (simp add: finite_subset_distinct)
  qed
next
  case False
  then show ?thesis
    by (metis Hamiltonian_paths_not_empty equals0I finite.emptyI)
qed



lemma Hamiltonian_paths0 :
"Hamiltonian_paths s {} t = {[s, t]}"
  by(clarsimp simp: Hamiltonian_paths_def)


text \<open>If $V$ is not empty then the tail of any Hamiltonian path from $s$ to $t$ via $V$ 
      is in turn a Hamiltonian path starting with a vertex in $V$:\<close>
lemma Hamiltonian_pathsD :
  assumes "p \<in> Hamiltonian_paths s V t"
      and "V \<noteq> {}"
    shows "\<exists>v\<in>V. \<exists>p'\<in> Hamiltonian_paths v (V - {v}) t. p = s#p'"
  using assms Hamiltonian_paths_def hd_Cons_tl set_empty
proof(clarsimp simp: Hamiltonian_paths_def) 
qed(case_tac vs; clarsimp+)


lemma Hamiltonian_pathsI :
  assumes "p \<in> Hamiltonian_paths v (V - {v}) t"
      and "v \<in> V"
    shows "s#p \<in> Hamiltonian_paths s V t"
  using assms
  by(clarsimp simp: Hamiltonian_paths_def insert_absorb)




subsection \<open>Optimal Hamiltonian paths\<close>


text \<open>Extending an edge distance function $\delta$ to paths:\<close>
fun path_distance where
"path_distance \<delta> [] = (0 :: 'a :: linordered_ab_group_add)" |
"path_distance \<delta> [v] = 0" |
"path_distance \<delta> (v1#v2#vs) = \<delta> v1 v2 + path_distance \<delta> (v2#vs)"



lemma Hamiltonian_path_distance_Cons_le :
  assumes "p \<in> Hamiltonian_paths s V t"
      and "p' \<in> Hamiltonian_paths s V t"
    shows "(path_distance \<delta> p \<le> path_distance \<delta> p') = 
           (path_distance \<delta> (v#p) \<le> path_distance \<delta> (v#p'))"
  using assms by(clarsimp simp: Hamiltonian_paths_def)



text \<open>A Hamiltonian path is optimal with respect to the given edge distance function $\delta$ 
      if its @{term path_distance} is minimal:\<close>
definition 
"opt_Hamiltonian_paths \<delta> s V t = {p. p \<in> Hamiltonian_paths s V t \<and> 
  (\<forall>p'\<in>Hamiltonian_paths s V t. path_distance \<delta> p \<le> path_distance \<delta> p')}"


lemma opt_Hamiltonian_paths0 :
"opt_Hamiltonian_paths \<delta> s {} t = {[s, t]}"
  by(fastforce simp: opt_Hamiltonian_paths_def Hamiltonian_paths0)
 

lemma opt_Hamiltonian_pathsD :
"opt_Hamiltonian_paths \<delta> s V t \<subseteq> Hamiltonian_paths s V t"
  by(clarsimp simp: opt_Hamiltonian_paths_def)


lemma opt_Hamiltonian_paths_same_distance :
  assumes "p \<in> opt_Hamiltonian_paths \<delta> s V t"
      and "p' \<in> opt_Hamiltonian_paths \<delta> s V t"
    shows "path_distance \<delta> p = path_distance \<delta> p'"
  using assms
  by (simp add: Orderings.order_eq_iff opt_Hamiltonian_paths_def)



lemma opt_Hamiltonian_paths_not_empty :
  assumes "finite V"
  shows "\<exists>p. p \<in> opt_Hamiltonian_paths \<delta> s V t"
proof -
  have "Hamiltonian_paths s V t \<noteq> {}"
    by (metis Hamiltonian_paths_not_empty assms empty_iff)
  with obtains_MIN[where f="path_distance \<delta>"] show ?thesis
    by (smt (verit, best) Hamiltonian_paths_finite Min.bounded_iff empty_iff finite_imageI image_eqI
        mem_Collect_eq nle_le opt_Hamiltonian_paths_def)
qed



lemma opt_Hamiltonian_pathsI :
  assumes "p \<in> Hamiltonian_paths s V t"
  and "\<forall>p'\<in>opt_Hamiltonian_paths \<delta> s V t. path_distance \<delta> p \<le> path_distance \<delta> p'"
  shows "p \<in> opt_Hamiltonian_paths \<delta> s V t"
  by (smt (z3) Hamiltonian_paths_not_empty assms mem_Collect_eq opt_Hamiltonian_paths_def
      opt_Hamiltonian_paths_not_empty order_trans)



subsection \<open>Minimal distance extensions\<close>

definition Min_distance_ext where 
"Min_distance_ext \<delta> v S = {v#p |p. p \<in> S \<and> 
 (\<forall>p'\<in>S. path_distance \<delta> (v#p) \<le> path_distance \<delta> (v#p'))}"


lemma Min_distance_ext :
"(p \<in> Min_distance_ext \<delta> v S) = 
 (\<exists>p'\<in>S. p = v#p' \<and> (\<forall>p''\<in>S. path_distance \<delta> (v#p') \<le> path_distance \<delta> (v#p'')))"
proof(rule iffI) 
qed(clarsimp simp: Min_distance_ext_def)+


lemma Min_distance_ext_eq' :
  assumes "S \<subseteq> T" 
      and "\<forall>p'\<in>T - S. \<exists>p\<in>S. path_distance \<delta> (v#p) < path_distance \<delta> (v#p')"
    shows "(p \<in> Min_distance_ext \<delta> v S) = (p \<in> Min_distance_ext \<delta> v T)" 
  (is "?L = ?R")
proof
  assume ?L with assms show ?R
    by (smt (verit, del_insts) DiffI Min_distance_ext nless_le order.strict_trans1 subset_iff)
next
  assume ?R with assms show ?L
    by (smt (verit, del_insts) DiffI Min_distance_ext nle_le nless_le subset_iff)
qed


corollary Min_distance_ext_eq :
  assumes "S \<subseteq> T" 
      and "\<forall>p'\<in>T - S. \<exists>p\<in>S. path_distance \<delta> (v#p) < path_distance \<delta> (v#p')"
    shows "Min_distance_ext \<delta> v S = Min_distance_ext \<delta> v T" 
proof(rule set_eqI)
qed(simp add: Min_distance_ext_eq' assms)



subsection \<open>@{term opt_Hamiltonian_paths} as a fixed point\<close>


theorem opt_Hamiltonian_paths_fix :
  assumes "V \<noteq> {}"
  shows "opt_Hamiltonian_paths \<delta> s V t = 
         Min_distance_ext \<delta> s (\<Union>v\<in>V. opt_Hamiltonian_paths \<delta> v (V - {v}) t)"
(is "?L = ?R") 
proof
  show "?L \<subseteq> ?R"
  proof
    fix p assume a: "p \<in> opt_Hamiltonian_paths \<delta> s V t"
    with assms obtain v p' where b: "v \<in> V" "p' \<in> Hamiltonian_paths v (V - {v}) t" "p = s#p'"
      by (meson Hamiltonian_pathsD opt_Hamiltonian_pathsD subsetD)
    have "p' \<in> opt_Hamiltonian_paths \<delta> v (V - {v}) t"
    proof(rule opt_Hamiltonian_pathsI)
      show "p' \<in> Hamiltonian_paths v (V - {v}) t" by(rule b)
    next
      from a and b 
      show "\<forall>p''\<in>opt_Hamiltonian_paths \<delta> v (V - {v}) t. path_distance \<delta> p' \<le> path_distance \<delta> p''"
        by (metis (no_types, lifting) Hamiltonian_path_distance_Cons_le Hamiltonian_pathsI 
            mem_Collect_eq opt_Hamiltonian_paths_def)
    qed
    with a show "p \<in> Min_distance_ext \<delta> s (\<Union>v\<in>V. opt_Hamiltonian_paths \<delta> v (V - {v}) t)"
    proof(clarsimp simp: Min_distance_ext)
    qed(metis (no_types, lifting) Hamiltonian_pathsI b(1,3) mem_Collect_eq opt_Hamiltonian_paths_def)
  qed
next
  show "?R \<subseteq> ?L"
  proof(clarsimp simp: Min_distance_ext)
    fix v p
    assume 1: "v \<in> V"
       and 2: "p \<in> opt_Hamiltonian_paths \<delta> v (V - {v}) t"
       and 3: "\<forall>v\<in>V. \<forall>p'\<in>opt_Hamiltonian_paths \<delta> v (V - {v}) t. 
                   path_distance \<delta> (s#p) \<le> path_distance \<delta> (s#p')" 
    show "s#p \<in> opt_Hamiltonian_paths \<delta> s V t"
    proof(rule opt_Hamiltonian_pathsI)
      from 1 and 2 show "s#p \<in> Hamiltonian_paths s V t"
        by (meson Hamiltonian_pathsI opt_Hamiltonian_pathsD subsetD)
    next
      show "\<forall>p'\<in>opt_Hamiltonian_paths \<delta> s V t. path_distance \<delta> (s#p) \<le> path_distance \<delta> p'"
      proof
        fix p' assume a:"p' \<in> opt_Hamiltonian_paths \<delta> s V t"
        with 1 obtain v' p'' where "p''\<in> Hamiltonian_paths v' (V - {v'}) t" "v' \<in> V" "p' = s#p''"
          by (metis Hamiltonian_pathsD emptyE in_mono opt_Hamiltonian_pathsD)
        with 3 and a show "path_distance \<delta> (s#p) \<le> path_distance \<delta> p'"
          by (smt (verit) Hamiltonian_path_distance_Cons_le Hamiltonian_pathsI
              mem_Collect_eq opt_Hamiltonian_paths_def)
      qed
    qed
  qed
qed



section \<open>An implementation using dynamic programming\<close>


subsection \<open>A few preparations\<close>


text \<open>Membership test for lists with a (strictly) descending order of elements:\<close>
fun memS where
"memS a [] = False" |
"memS a (x#xs) = (a \<le> x \<and> (a = x \<or> memS a xs))"


lemma memS :
  assumes "sorted_wrt (>) xs"
  shows "memS (a :: 'a :: linorder) xs = (a \<in> set xs)"
  using assms
proof(induct xs) 
qed(fastforce+)


text \<open>Removal from lists with a strictly descending order of elements:\<close>
fun rem1S where
"rem1S (a :: 'a :: linorder) [] = []" |
"rem1S a (x#xs) = (if a = x then xs else (if a < x then x#rem1S a xs else x#xs))"

lemma rem1S :
  assumes "sorted_wrt (>) xs" 
  shows "set(rem1S a xs) = set xs - {a}"
  using assms
proof(induct xs)
qed(force+)


lemma rem1S_length :
  assumes "sorted_wrt (>) xs"
      and "a \<in> set xs"
    shows "length(rem1S a xs) + 1 = length xs"
  using assms
proof(induct xs)
qed(fastforce+)


corollary rem1S_length' :
  assumes "sorted_wrt (>) xs"
      and "a \<in> set xs"
    shows "length(rem1S a xs) < length xs"
  using assms rem1S_length by fastforce


lemma sorted_wrt_rem1S :
  assumes "sorted_wrt (>) xs" 
  shows "sorted_wrt (>) (rem1S a xs)"
  using assms
proof(induct xs) 
qed(clarsimp simp: rem1S)+



lemma sorted_lists_eq :
  assumes "sorted_wrt (>) (as :: 'a :: linorder list)"
      and "sorted_wrt (>) bs"
      and "set as \<subseteq> set bs" 
      and "length as = length bs"
    shows "as = bs"
  using assms
proof(induct bs arbitrary: as)
  case Nil
  then show ?case
    by simp 
next
  case 1:(Cons b bs)
  then show ?case 
  proof(cases as)
    case Nil
    then show ?thesis
      using 1(5) by fastforce 
  next
    case (Cons a as')
    with 1 show ?thesis
    proof(clarsimp)
    qed(metis not_less_iff_gr_or_eq subset_insert_iff)
  qed
qed



subsection \<open>Indexing subsets of $\{0,\ldots,n\}$ represented by sorted lists\<close>


fun nat2list :: "nat \<Rightarrow> nat \<Rightarrow> nat list" 
  where
"nat2list c ix = (if ix = 0 then []
                  else (if even ix then nat2list (c+1) (ix div 2)
                        else nat2list (c+1) (ix div 2) @ [c]))"


lemma nat2list_Nil :
"(nat2list c ix = []) = (ix = 0)"
proof(induct c ix rule: nat2list.induct)
  case (1 c ix)
  then show ?case
  proof(cases ix)
    case 0
    then show ?thesis
      by simp 
  next
    case (Suc n)
    with 1 show ?thesis 
    proof(subst nat2list.simps)
    qed(clarsimp simp del: nat2list.simps)
  qed
qed


abbreviation pow2 :: "nat \<Rightarrow> nat"  ("2\<^bsup>_\<^esup>" 80)
  where "pow2 n \<equiv> 2^n"



lemma nat2list_ub :
  assumes "ix < 2\<^bsup>b\<^esup>"
  shows "\<forall>i\<in>set(nat2list c ix). i < b + c"
  using assms
proof(induct c ix arbitrary: b rule: nat2list.induct)
  case (1 c ix)
  show ?case
  proof(cases b)
    case 0
    with 1 show ?thesis by simp 
  next
    case (Suc n)
    with 1 show ?thesis 
    proof(subst nat2list.simps)
    qed(clarsimp simp del: nat2list.simps)
  qed
qed


lemma nat2list_lb :
"\<forall>i\<in>set(nat2list c ix). c \<le> i"
proof(induct c ix rule: nat2list.induct)
  case (1 c ix)
  hence "ix > 0 \<Longrightarrow> \<forall>i\<in>set (nat2list (c + 1) (ix div 2)). c \<le> i" by fastforce
  then show ?case
  proof(subst nat2list.simps)
  qed(simp del: nat2list.simps)
qed



lemma nat2list_sorted :
"sorted_wrt (>) (nat2list c ix)"
proof(induct c ix rule: nat2list.induct)
  case (1 c ix)
  have "ix > 0 \<Longrightarrow> \<forall>i\<in>set (nat2list (c + 1) (ix div 2)). c < i"
    by (meson less_iff_succ_less_eq nat2list_lb)
  with 1 show ?case 
  proof(subst nat2list.simps)
  qed(simp add: sorted_wrt_append del: nat2list.simps)
qed


lemma nat2list_pow2[OF refl] :
  assumes "b = 2\<^bsup>n\<^esup>"
  shows "nat2list c b = [c+n]"
  using assms
proof(induct c b arbitrary: n rule: nat2list.induct)
  case (1 c ix)
  then show ?case 
  proof(cases "n")
    case 0
    with 1(3) and nat2list_Nil show ?thesis
      by simp 
  next
    case (Suc m)
    with 1 show ?thesis 
    proof(subst nat2list.simps)
    qed(simp del: nat2list.simps)
  qed
qed



lemma pow2_div2 :
  assumes "n > 0"
  shows "(2\<^bsup>n\<^esup> + x) div 2 = 2\<^bsup>n-1\<^esup> + x div 2"
  by (metis assms add_self_div_2 div_plus_div_distrib_dvd_left dvd_power mult_2_right power_minus_mult)


lemma pow2pred_div2 :
"(2\<^bsup>n\<^esup> - 1) div 2 = 2\<^bsup>n-1\<^esup> - 1"
  by (metis mask_half mask_nat_def)


lemma nat2list_pred_pow2 :
  assumes "b = 2\<^bsup>n\<^esup> - 1" 
  shows "nat2list c b = rev [c..<n+c]"
  using assms
proof(induct c b arbitrary: n rule: nat2list.induct)
  case (1 c ix)
  then show ?case
  proof(cases "n = 0")
    case True
    with 1 show ?thesis by simp 
  next
    case a:False
    then show ?thesis
    proof(cases "n = 1")
      case True
      with 1 show ?thesis by simp 
    next
      from a have b : "2\<^bsup>n\<^esup> > 1" by (simp add: less_trans_Suc)
      case False
      with 1 and a and b and pow2pred_div2[of n] show ?thesis 
      proof(subst nat2list.simps)
      qed(simp add: bot_nat_0.not_eq_extremum upt_rec)
    qed
  qed
qed


corollary nat2list_pred_pow2' :
"nat2list 0 (2\<^bsup>n\<^esup> - 1) = rev [0..<n]"
  using nat2list_pred_pow2 by fastforce



lemma nat2list_shift :
  assumes "ix < 2\<^bsup>b\<^esup>"
  shows "nat2list c (2\<^bsup>b\<^esup> + ix) = (c + b)#(nat2list c ix)"
  using assms
proof(induct c ix arbitrary: b rule: nat2list.induct)
  case (1 c ix)
  then show ?case 
  proof(cases "b = 0")
    case True
    with 1 show ?thesis by simp
  next
    case 2:False
    show ?thesis 
    proof(cases "even ix")
      case 3:True
      show ?thesis
      proof(cases "ix = 0")
        case True
        with 2 show ?thesis
          by (metis add.right_neutral nat2list_Nil nat2list_pow2)  
      next
        case 4:False
        note pow2_div2[where x=ix and n=b]
        with 1(1)[where b="b-1"] and 1(3) and 2 and 3 and 4 show ?thesis
          by (simp add: div_greater_zero_iff div_less_iff_less_mult dvd_add_left_iff power_eq_if)
      qed
    next
      case 3:False
      hence "ix > 0" by (meson odd_pos) 

      with 1(2)[where b="b-1"] and 1(3) and 2 and 3 
      have "nat2list (c+1) (2\<^bsup>b - 1\<^esup> + ix div 2) @ [c] = (c + b) # nat2list c ix"
      proof(subst nat2list.simps[where ix=ix])
      qed(smt (verit, best) One_nat_def Suc_pred append_Cons even_add even_power group_cancel.add1
          less_mult_imp_div_less mult_2_right plus_1_eq_Suc power_commutes power_eq_if)

      with 2 and 3 show ?thesis
        by (simp add: pow2_div2)
    qed
  qed
qed




lemma nat2list_inj :
  assumes "ix \<noteq> ix'"
  shows "nat2list c ix \<noteq> nat2list c ix'"
  using assms
proof(induct c ix arbitrary: ix' rule: nat2list.induct)
  case (1 c ix)
  then show ?case 
  proof(cases "even ix")
    case 2:True
    then show ?thesis 
    proof(cases "even ix'")
      case True
      with 1 and 2 show ?thesis
        by (metis dvd_div_eq_iff nat2list.simps nat2list_Nil) 
    next
      case False
      with 1 and 2 show ?thesis
        by (metis add_le_same_cancel1 in_set_conv_decomp nat2list.simps nat2list_lb not_one_le_zero)
    qed
  next
    case 2:False
    show ?thesis 
    proof(cases "even ix'")
      case True
      with 1 and 2 show ?thesis
        by (metis add_le_same_cancel1 even_zero in_set_conv_decomp nat2list.simps nat2list_lb not_one_le_zero)
    next
      have 3:"\<And>n m. n \<noteq> m \<Longrightarrow> odd n \<Longrightarrow> odd m \<Longrightarrow> n div 2 \<noteq> m div 2"
        by (metis mod2_eq_if mult_div_mod_eq) 
      case False
      with 1(2)[where ix'="ix' div 2"] and 1(3) and 2 show ?thesis 
        by(simp add: 3) 
    qed
  qed
qed




fun list2nat :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat"
  where
"list2nat r b [] = 2\<^bsup>b\<^esup> * r" |
"list2nat r b (e#l) = (if b > 0 then 
                        (if b-1 = e then list2nat (2*r + 1) (b-1) l 
                         else list2nat (2*r) (b-1) (e#l))
                       else r)"



lemma list2nat_eq :
"list2nat r b l = 2\<^bsup>b\<^esup>*r + list2nat 0 b l"                            
proof(induct b arbitrary:l r rule: less_induct)
  case (less x)
  then show ?case
  proof(cases l)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a xs)
    then show ?thesis
    proof(cases "x - 1 = a")
      case 1:True
      note less[of "x-1" "2*r+1" "xs"] and less[of "x-1" "1" "xs"]
      with Cons and 1 show ?thesis
        by (simp add: power_eq_if)
    next
      case 1:False
      note less[of "x-1" "2*r" "a#xs"]
      with Cons and 1 show ?thesis
        by (simp add: power_eq_if)
    qed
  qed
qed



lemma list2nat_gr0 :
  assumes "sorted_wrt (>) l"
      and "length l > 0"
      and "\<forall>x\<in>set l. x < b"
    shows "list2nat r b l > 0"
  using assms
proof(induct r b l rule: list2nat.induct)
  case (1 r b)
  then show ?case by simp
next
  case (2 r b x l)
  then show ?case
  proof(cases "l = []")
    case True
    with 2(5) show ?thesis
    proof(clarsimp simp del: list2nat.simps)
      have "x < b \<Longrightarrow> 0 < list2nat 0 b [x]"
      proof(induct b rule: less_induct)
        case (less v)
        then show ?case
        proof(subst list2nat.simps)
        qed(simp del: list2nat.simps(2))
      qed      
      thus "x < b \<Longrightarrow> 0 < list2nat r b [x]"
        by (metis add_is_0 gr_zeroI list2nat_eq)
    qed
  next
    from 2 have a:"b - 1 \<noteq> x \<Longrightarrow> 0 < list2nat (2 * r) (b - 1) (x # l)" by fastforce
    case False
    with 2 and a show ?thesis
    proof(subst list2nat.simps)
    qed(simp del: list2nat.simps)
  qed
qed



lemma list2nat_ub :
  assumes "\<forall>x\<in>set l. x < b"
      and "sorted_wrt (>) l"
    shows "list2nat r b l < 2\<^bsup>b\<^esup> * r + 2\<^bsup>b\<^esup>"
  using assms
proof(induct r b l rule: list2nat.induct)
  case (1 r b)
  then show ?case by simp
next
  case (2 r b x l)
  then show ?case 
  proof(cases "b - 1 = x")
    case True
    with 2 show ?thesis 
    proof(subst list2nat.simps)
    qed(clarsimp simp del: list2nat.simps simp add: power_eq_if)
  next
    case a:False
    with 2(4) have b:"\<forall>x\<in>set (x # l). x < b - 1" using 2(3) by fastforce
    hence c:"b > 0"
      by (simp add: less_diff_conv)
    hence "list2nat (2 * r) (b - 1) (x # l) < 2 ^ (b - 1) * (2 * r) + 2 ^ (b - 1)"
      using 2 and a and b by blast
    with a and c show ?thesis
      by (smt (z3) ab_semigroup_mult_class.mult_ac(1) add.commute left_add_mult_distrib 
          list2nat.simps(2) mult_2_right mult_numeral_1_right power_minus_mult trans_less_add2)
  qed
qed


lemmas list2nat_ub0 = list2nat_ub[where r=0, simplified]


lemma list2nat_inj :
  assumes "\<forall>x\<in>set l. x < b"
      and "sorted_wrt (>) l"
    shows "nat2list 0 (list2nat 0 b l) = l"
  using assms
proof(induct b arbitrary: l rule: less_induct)
  case (less b)
  then show ?case 
  proof(cases "l")
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ls)
    with less(2) have a:"b > 0" by simp 
    show ?thesis
    proof(cases "b - 1 = y")
      case b:True
      with less(2, 3) and Cons and a have c:"\<forall>x\<in>set ls. x < b-1 \<and> sorted_wrt (>) ls"
        by (meson sorted_wrt.simps(2))

      with Cons and a and b 
      have d:"nat2list 0 (list2nat 1 (b - 1) ls) = 
              (b - 1) # nat2list 0 (list2nat 0 (b - 1) ls)"
      proof(subst list2nat_eq)
      qed(metis add.commute add_0 lambda_one less.prems(2) list2nat_ub mult_0_right mult_Suc_right 
          nat2list_shift sorted_wrt.simps(2))

      note less(1)[where y="b-1" and l=ls]
      with a and b and c have "nat2list 0 (list2nat 0 (b - 1) ls) = ls"
        by (metis diff_less less_numeral_extra(1) nth_mem sorted_wrt_iff_nth_less)
      with a and b and d and Cons and list2nat.simps show ?thesis 
        by simp
    next
      case b:False
      have "nat2list 0 (list2nat 0 (b - 1) (y # ls)) = y # ls"
      proof(rule less(1))
        from a show "b - 1 < b" by simp
      next
        from less(2,3) and a and b and Cons show "\<forall>x\<in>set (y # ls). x < b - 1" by fastforce
      next
        from less(3) Cons show "sorted_wrt (>) (y # ls)" by simp
      qed
      with a and b and Cons and list2nat.simps show ?thesis
        by simp 
    qed
  qed
qed


corollary list2nat_surj :
  assumes "ix < 2\<^bsup>b\<^esup>"
  shows "list2nat 0 b (nat2list 0 ix) = ix"
  by (metis assms add.right_neutral list2nat_inj nat2list_inj nat2list_sorted nat2list_ub)



lemma list2nat_mono :
  assumes "\<forall>x\<in>set l. x < b"
      and "sorted_wrt (>) l" 
      and "length l' < length l"
      and "set l' \<subseteq> set l"
      and "sorted_wrt (>) l'"
    shows "list2nat r b l' < list2nat r b l"
  using assms
proof(induct r b l arbitrary: l' rule: list2nat.induct)
  case (1 r b)
  then show ?case by simp
next
  case (2 r b x l)
  hence a:"b > 0" by simp
  show ?case
  proof(cases "b - 1 = x")
    case b:True
    with 2(3, 4) and a have c:"(\<forall>x\<in>set l. x < b-1) \<and> sorted_wrt (>) l" by simp
    have "list2nat r b l' < list2nat (2 * r + 1) x l"
    proof(cases l')
      case Nil
      with 2 and a and b show ?thesis
      proof(subst list2nat_eq[where l=l])
      qed(smt (verit) ab_semigroup_mult_class.mult_ac(1) less_add_same_cancel1 list2nat.simps(1) mult.commute
          mult_less_mono1 power_minus_mult trans_less_add1 zero_less_numeral zero_less_one zero_less_power)
    next
      case (Cons a l'')
      show ?thesis
      proof(cases "b-1 = a")
        case d:True
        have "list2nat (2 * r + 1) (b - 1) l'' < list2nat (2 * r + 1) (b - 1) l"
        proof(rule 2(1))
          from a show "b > 0" .
        next
          from b show "b - 1 = x" .
        next
          from c show "\<forall>x'\<in>set l. x' < b - 1" by simp
        next
          from c show "sorted_wrt (>) l" by simp
        next
          from 2(5) and Cons show "length l'' < length l" by simp
        next
          from 2(6, 7) and Cons and b and d show "set l'' \<subseteq> set l"
            using set_subset_Cons by fastforce
        next
          from 2(7) and Cons show "sorted_wrt (>) l''" by simp
        qed
        with a and b and d and Cons show ?thesis by simp
      next
        case d:False
        show ?thesis
        proof(cases "length l'' + 1 = length l")
          case e:True
          have "l' = l"
          proof(rule sorted_lists_eq)
            show "sorted_wrt (>) l" using 2(4) by fastforce
          next
            show "set l' \<subseteq> set l" using b c d Cons 2(6) 2(7) by fastforce
          next
            show "length l' = length l" using Cons e by fastforce
          qed(simp add: 2)
          with a and b and d and Cons show ?thesis
            by (smt (verit, del_insts) add.commute add_less_cancel_left less_add_same_cancel1 list2nat.simps(2)
                list2nat_eq mult.commute mult_less_mono1 zero_less_numeral zero_less_one zero_less_power)
        next
          case e:False
          have f:"list2nat (2 * r + 1) (b - 1) (a # l'') < list2nat (2 * r + 1) (b - 1) l"
          proof(rule 2(1))
            from a show "b > 0" .
          next
            from b show "b - 1 = x" .
          next
            from c show "\<forall>x\<in>set l. x < b - 1" by simp
          next
            from c show "sorted_wrt (>) l" by simp
          next
            from Cons and e and 2(5) show "length (a # l'') < length l" by fastforce
          next
            from 2(6, 7) and Cons and b c d e  show "set (a # l'') \<subseteq> set l"
            proof(clarsimp)
            qed(metis less_imp_add_positive not_add_less1 subset_iff subset_insert)
          next
            from 2(7) and Cons show "sorted_wrt (>) (a # l'')" by simp
          qed

          have "list2nat (2 * r) (b - 1) (a # l'') < list2nat (2 * r + 1) (b - 1) l"
          proof(rule less_trans)
            from list2nat_eq show "list2nat (2 * r) (b - 1) (a # l'') < list2nat (2 * r + 1) (b - 1) (a # l'')"
              by (metis Suc_eq_plus1 add.commute add_less_cancel_left lessI mult.commute 
                  mult_less_mono1 zero_less_numeral zero_less_power)
          next
            from f show "list2nat (2 * r + 1) (b - 1) (a # l'') < list2nat (2 * r + 1) (b - 1) l"
              by simp
          qed

          with a and b and d and Cons show ?thesis by simp
        qed
      qed
    qed
    with a and b show ?thesis by simp
  next
    case b:False
    with 2(3, 4) and a have c:"\<forall>x\<in>set(x#l). x < b - 1"
      using less_imp_diff_less by force

    have "list2nat r b l' < list2nat (2 * r) (b - 1) (x # l)" 
    proof(cases l')
      case Nil
      with 2 and a and b and c show ?thesis
        by (smt (verit, ccfv_threshold) One_nat_def Suc_le_eq ab_semigroup_mult_class.mult_ac(1) 
            le_add_diff_inverse2 list2nat.simps(1) power_Suc0_right power_add) 
    next
      case (Cons a l'')
      then show ?thesis 
      proof(cases "b-1 = a")
        case True
        with a and b and c and Cons and 2(6) show ?thesis
          by (metis less_not_refl list.set_intros(1) subset_iff)
      next
        case False
        with a and b and c and Cons and 2 show ?thesis
          by (metis list2nat.simps(2))
      qed
    qed
    with a b c and 2 show ?thesis
      by (metis list2nat.simps(2))
  qed
qed


declare list2nat.simps[simp del] nat2list.simps[simp del]



corollary list2nat_rem1S :
  assumes "sorted_wrt (>) l"
      and "\<forall>x\<in>set l. x < b" 
      and "u \<in> set l"
 shows "list2nat r b (rem1S u l) < list2nat r b l"
proof(rule list2nat_mono)
qed(simp_all add: assms rem1S sorted_wrt_rem1S rem1S_length')


corollary list2nat_rem1S_not_in :
  assumes "u \<in> set (nat2list 0 ix)" 
      and "ix < 2\<^bsup>N\<^esup>"
    shows "u \<notin> set(nat2list 0 (list2nat 0 N (rem1S u (nat2list 0 ix))))"
  using assms nat2list_sorted[of 0 ix] nat2list_ub[of ix N 0] sorted_wrt_rem1S rem1S list2nat_inj
  by (metis Diff_iff add_cancel_right_right insert_iff)


corollary list2nat_rem1S_less :
  assumes "u \<in> set (nat2list 0 ix)" 
      and "ix < 2\<^bsup>N\<^esup>"
    shows "list2nat 0 N (rem1S u (nat2list 0 ix)) < ix"
  by (metis assms add.right_neutral list2nat_rem1S list2nat_surj nat2list_sorted nat2list_ub) 




subsection \<open>Computing minimal distance extensions\<close>


fun min_distance_ext'
  where
"min_distance_ext' \<delta> v (md :: 'a :: linordered_ab_group_add) mps [] = (md, mps)" |
"min_distance_ext' \<delta> v md mps ((h, (d, ps))#xs) = 
(let dp = \<delta> v h + d in
  if md < dp then min_distance_ext' \<delta> v md mps xs
  else (if md = dp then min_distance_ext' \<delta> v md ((map ((#) h) ps)@mps) xs
        else min_distance_ext' \<delta> v dp (map ((#) h) ps) xs))"


definition "min_distance_ext \<delta> v xs = 
 (case xs of 
   [] \<Rightarrow> (0, [])
 | (h, (d, ps))#xs' \<Rightarrow> min_distance_ext' \<delta> v (\<delta> v h + d) (map ((#) h) ps) xs')"


lemma min_distance_ext'1 :
  assumes "\<delta> v h + d > md"
  shows "min_distance_ext' \<delta> v md mps ((h, d, ps)#xs) = 
         min_distance_ext' \<delta> v md mps xs"
  by(simp add: assms)

lemma min_distance_ext'2 :
  assumes "\<delta> v h + d = md"
  shows "min_distance_ext' \<delta> v md mps ((h, d, ps)#xs) = 
         min_distance_ext' \<delta> v md (map ((#) h) ps@mps) xs"
  by(simp add: assms)


lemma min_distance_ext'3 :
  assumes "\<delta> v h + d < md"
  shows "min_distance_ext' \<delta> v md mps ((h, d, ps)#xs) = 
         min_distance_ext' \<delta> v (\<delta> v h + d) (map ((#) h) ps) xs"
  using assms by(fastforce simp add: Let_def)


declare min_distance_ext'.simps(2)[simp del]



definition 
"min_distance_ext_inv \<delta> h = (\<lambda>(d, ps). length ps > 0 \<and> (\<forall>p\<in>set ps. path_distance \<delta> (h#p) = d))" 


lemma min_distance_ext_invD :
  assumes "min_distance_ext_inv \<delta> h (d, ps)"  
  shows "\<exists>p. p \<in> set ps" and "\<forall>p\<in>set ps. path_distance \<delta> (h#p) = d" 
  using assms last_in_set 
  unfolding min_distance_ext_inv_def
  by blast+


lemma min_distance_ext'_inv :
  assumes "min_distance_ext' \<delta> v md mps xs = (d, ps)"
      and "min_distance_ext_inv \<delta> v (md, mps)"
      and "\<forall>(h, d, ps)\<in>set xs. min_distance_ext_inv \<delta> h (d, ps)"
    shows "min_distance_ext_inv \<delta> v (d, ps)"
  using assms
proof(induct xs arbitrary: md mps)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof clarsimp
    fix h d' l
    assume a: "a = (h, d', l)"
       and b: "min_distance_ext_inv \<delta> h (d', l)"
    show ?thesis
    proof(cases "\<delta> v h + d' > md")
      case True
      with Cons and a and b show ?thesis
        by (metis list.set_intros(2) min_distance_ext'1) 
    next
      case c:False
      show ?thesis
      proof(cases "\<delta> v h + d' < md")
        from Cons(4) and a have d: "min_distance_ext_inv \<delta> v (\<delta> v h + d', map ((#) h) l)" 
          by(clarsimp simp: min_distance_ext_inv_def)
        case True
        with Cons and a and d show ?thesis
          by (simp add: min_distance_ext'3)
      next
        case False
        with c have d:"\<delta> v h + d' = md" by simp
        with Cons(3,4) and a have "min_distance_ext_inv \<delta> v (md, map ((#) h) l @ mps)" 
        proof(clarsimp simp: min_distance_ext_inv_def)
        qed(fastforce)
        with Cons and a and d show ?thesis 
          by(clarsimp simp: min_distance_ext'2)
      qed
    qed
  qed
qed




lemma min_distance_ext'_eq :
  assumes "min_distance_ext' \<delta> v md mps xs = (d, ps)"
      and "min_distance_ext_inv \<delta> v (md, mps)"
      and "\<forall>(h, d', l)\<in>set xs. min_distance_ext_inv \<delta> h (d', l)"
    shows "(#) v ` set ps = Min_distance_ext \<delta> v {p. p \<in> set mps \<or> (\<exists>(h, d', l)\<in>set xs. p \<in> (#) h ` set l)}"
 (is "_ = Min_distance_ext \<delta> v (?s mps xs)")
  using assms
proof(induct xs arbitrary: md mps)
  case Nil
  then show ?case 
  proof(clarsimp simp: min_distance_ext_inv_def Min_distance_ext_def)
  qed(fastforce)
next
  case (Cons a xs)
  then show ?case
  proof clarsimp
    fix h d' l
    assume a: "a = (h, d', l)"
       and b: "min_distance_ext_inv \<delta> h (d', l)"
    show "(#) v ` set ps = Min_distance_ext \<delta> v {p. p \<in> set mps \<or> p \<in> (#) h ` set l \<or> 
                                                 (\<exists>(h, d', l)\<in>set xs. p \<in> (#) h ` set l)}"
    (is "_ = Min_distance_ext \<delta> v ?t")
    proof(cases "\<delta> v h + d' > md")
      case c:True
      with Cons a and b show ?thesis
      proof(clarsimp simp: min_distance_ext'1)
        show "Min_distance_ext \<delta> v (?s mps xs) = Min_distance_ext \<delta> v ?t"
        proof(rule Min_distance_ext_eq, fast)
          from Cons(3,4) and b and c 
          show "\<forall>p'\<in> ?t - ?s mps xs. \<exists>p\<in>?s mps xs. path_distance \<delta> (v#p) < path_distance \<delta> (v#p')"
          proof(clarsimp)
          qed(metis (mono_tags, opaque_lifting) min_distance_ext_invD)
        qed
      qed
    next
      case c:False
      show ?thesis
      proof(cases "\<delta> v h + d' < md")
        case d:True
        with Cons and a and b show ?thesis
        proof(clarsimp simp: min_distance_ext'3 min_distance_ext_inv_def)
          show "Min_distance_ext \<delta> v {p. p \<in> (#) h ` set l \<or> (\<exists>(h, d', l)\<in>set xs. p \<in> (#) h ` set l)} =
                Min_distance_ext \<delta> v ?t"  (is "Min_distance_ext \<delta> v ?u = _")
          proof(rule Min_distance_ext_eq, fast)
            from Cons(3,4) and b and d
            show "\<forall>p'\<in> ?t - ?u. \<exists>p\<in>?u. path_distance \<delta> (v#p) < path_distance \<delta> (v#p')"
            proof(clarsimp)
            qed(metis (no_types, opaque_lifting) image_eqI min_distance_ext_invD path_distance.simps(3))
          qed
        qed
      next
        case False
        with c have d:"\<delta> v h + d' = md" by simp
        with Cons(3,4) and a have "min_distance_ext_inv \<delta> v (md, map ((#) h) l @ mps)" 
        proof(clarsimp simp: min_distance_ext_inv_def)
        qed(fastforce)
        with Cons(1,2,4) and a and d show ?thesis
        proof(clarsimp simp: min_distance_ext'2)
        qed(meson)
      qed
    qed
  qed
qed
            


lemma min_distance_ext :
  assumes "min_distance_ext \<delta> v xs = (d, rs)" 
      and "\<forall>(h, d', l)\<in>set xs. min_distance_ext_inv \<delta> h (d', l)"
      and "length xs > 0"
    shows "min_distance_ext_inv \<delta> v (d, rs) \<and> 
           (#) v ` set rs = Min_distance_ext \<delta> v {p. \<exists>(h, d', l)\<in>set xs. p \<in> (#) h ` set l}"
    (is "?A \<and> ?B")
proof(cases xs)
  case Nil
  with assms(3) show ?thesis by simp 
next
  case (Cons a ls)
  show ?thesis 
  proof
    from assms(1, 2) and Cons show "?A"
    proof(clarsimp simp: min_distance_ext_def)
    qed(smt (verit) Collect_cong case_prodI2 case_prod_conv image_iff length_greater_0_conv list.distinct(1)
        list.map_disc_iff list.set_map min_distance_ext'_inv min_distance_ext_inv_def path_distance.simps(3))
  next
    from assms(1, 2) and Cons show "?B"
    proof(clarsimp simp: min_distance_ext_def)
    qed(smt (verit) Collect_cong case_prodI2 case_prod_conv image_iff length_greater_0_conv list.distinct(1)
        list.map_disc_iff list.set_map min_distance_ext'_eq min_distance_ext_inv_def path_distance.simps(3))
  qed
qed



subsection \<open>Tables\<close>

type_synonym vertex = nat

text \<open>For simplicity distances shall be represented by integers below:\<close> 
type_synonym distance = int 

type_synonym table = "vertex \<times> nat \<Rightarrow> distance \<times> (vertex list) list"


text \<open>The table invariant condition:\<close>
definition table_inv :: "(vertex \<Rightarrow> vertex \<Rightarrow> distance) \<Rightarrow> nat \<Rightarrow> vertex \<Rightarrow> table \<Rightarrow> nat \<Rightarrow> bool"
  where
"table_inv \<delta> N t T ix = 
 (\<forall>i\<le>ix. \<forall>v\<in>{0..<N} - set(nat2list 0 i). 
  min_distance_ext_inv \<delta> v (T(v, i)) \<and>
  (#) v ` set(snd(T(v, i))) = opt_Hamiltonian_paths \<delta> v (set(nat2list 0 i)) t)"


text \<open>Initialising a table with edge distances from each of $\{0,\ldots,N-1\}$ to
      the destination $t$:\<close>
fun init_tab :: "(vertex \<Rightarrow> vertex \<Rightarrow> distance) \<Rightarrow> nat \<Rightarrow> vertex \<Rightarrow> table"
  where
"init_tab \<delta> N t = (if N = 0 then (\<lambda>x. (0, [])) 
                   else (init_tab \<delta> (N-1) t)((N-1, 0) := (\<delta> (N-1) t, [[t]])))"



lemma table_inv_init :
"table_inv \<delta> N t (init_tab \<delta> N t) 0"
proof(induct N)
qed(clarsimp simp: min_distance_ext_inv_def table_inv_def nat2list.simps opt_Hamiltonian_paths0)+


declare init_tab.simps[simp del]


text \<open>Update a table along the column $ix$ using the values in the preceding columns:\<close>
definition upd_tab :: "(vertex \<Rightarrow> vertex \<Rightarrow> distance) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> table \<Rightarrow> table" 
  where
"upd_tab \<delta> N ix =
(let vs = nat2list 0 ix in
 let V = [0..<N] in
foldr (\<lambda>v T. T((v, ix) := min_distance_ext \<delta> v (map (\<lambda>w. (w, T(w, list2nat 0 N (rem1S w vs)))) vs)))
                   (filter (\<lambda>v. \<not> memS v vs) V))" 


lemma foldr_upd1 :
  assumes "\<forall>v\<in>set xs. f v \<noteq> x"
  shows "foldr (\<lambda>v T. T(f v := g v T)) xs T x = T x"
  using assms
proof(induct xs)
qed(fastforce+)


lemma foldr_upd2 :
  assumes "x \<in> set xs"
      and "\<forall>xs. m (foldr (\<lambda>v T. T((v, vs) := g v (m T))) xs T) = m T"
    shows "foldr (\<lambda>v T. T((v, vs) := g v (m T))) xs T (x, vs) = g x (m T)"
  using assms
proof(induct xs)
qed(clarsimp+)


lemma table_inv_upd :
  assumes "table_inv \<delta> N t T ix"
      and "ix < ix'"
    shows "table_inv \<delta> N t (upd_tab \<delta> N ix' T) ix"
  using assms 
proof(clarsimp simp add: Let_def table_inv_def upd_tab_def)
qed(simp add: foldr_upd1[where f="\<lambda>x. (x, ix')"])



lemma upd_tab_app :
  assumes "vs = nat2list 0 ix"
      and "v \<in> {0..<N} - set vs" 
      and "ix < 2\<^bsup>N\<^esup>"
    shows "upd_tab \<delta> N ix T (v, ix) = 
           min_distance_ext \<delta> v (map (\<lambda>w. (w, T(w, list2nat 0 N (rem1S w vs)))) vs)"
  using assms unfolding upd_tab_def Let_def
proof(subst foldr_upd2; clarsimp simp add: memS nat2list_sorted)
qed(rule foldr_upd1; metis Pair_inject list2nat_rem1S_not_in)



lemma table_inv_upd_ext :
  assumes "table_inv \<delta> N t T ix"
      and "ix + 1 < 2\<^bsup>N\<^esup>"
    shows "table_inv \<delta> N t (upd_tab \<delta> N (ix+1) T) (ix+1)"
proof(clarsimp simp: table_inv_def)
  fix v i
  define vs where "vs = nat2list 0 i"
  define pix where "pix = (\<lambda>w. list2nat 0 N (rem1S w vs))"
 
  assume 1:"i \<le> Suc ix"
     and 2:"v < N"
     and 3:"v \<notin> set vs"
  show "min_distance_ext_inv \<delta> v (upd_tab \<delta> N (Suc ix) T (v, i)) \<and>
   (#) v ` set (snd (upd_tab \<delta> N (Suc ix) T (v, i))) = opt_Hamiltonian_paths \<delta> v (set vs) t"
  proof(cases "i < ix+1")
    case True
    with vs_def and table_inv_upd and assms(1) and 2 and 3 show ?thesis
      by (metis Diff_iff Suc_eq_plus1 atLeastLessThan_iff lessI less_Suc_eq_le less_eq_nat.simps(1)
          table_inv_def)
  next
    case False
    with 1 have 4: "i = ix+1" by simp
    show ?thesis
    proof(cases "upd_tab \<delta> N i T (v, i)")
      case 5:(Pair d rs)
      with 4 show ?thesis 
      proof(clarsimp)
        note upd_tab_app[OF refl]
        with vs_def pix_def have a:"min_distance_ext \<delta> v (map (\<lambda>w. (w, T (w, pix w))) vs) = (d, rs)"
          using "2" "3" "4" "5" assms(2) by fastforce
        from 4 and assms(2)  
        have b:"\<forall>x\<in>set vs. pix x < i \<and> pix x \<le> ix \<and> x \<notin> set(nat2list 0 (pix x))"
          by (metis less_eq_iff_succ_less list2nat_rem1S_less list2nat_rem1S_not_in pix_def vs_def)

        with 4 and pix_def and vs_def have pix_set: "\<forall>x. set vs - {x} = set(nat2list 0 (pix x))"
          by (metis Diff_iff add.right_neutral assms(2) list2nat_inj nat2list_sorted nat2list_ub rem1S
              sorted_wrt_rem1S)

        from b and 1 and 4 and assms have 
        c:"\<forall>(h, d', l)\<in>set (map (\<lambda>w. (w, T(w, pix w))) vs). min_distance_ext_inv \<delta> h (d', l) "
        proof(clarsimp simp: table_inv_def pix_def vs_def)
        qed(metis DiffI add_cancel_right_right atLeastLessThan_iff bot_nat_0.extremum nat2list_ub)

        note min_distance_ext[OF a c]
        with nat2list_Nil and 4 have d:
        "min_distance_ext_inv \<delta> v (d, rs) \<and> (#) v ` set rs = 
         Min_distance_ext \<delta> v {p. \<exists>x\<in>set vs. case T(x, pix x) of (d', l) \<Rightarrow> p \<in> (#) x ` set l}" 
          by(simp add: pix_def vs_def)

        have "Min_distance_ext \<delta> v {p. \<exists>x\<in>set vs. case T(x, pix x) of (d', l) \<Rightarrow> p \<in> (#) x ` set l} =
              Min_distance_ext \<delta> v (\<Union>x\<in>set vs. opt_Hamiltonian_paths \<delta> x (set vs - {x}) t)"
                    (is "Min_distance_ext \<delta> v ?l = Min_distance_ext \<delta> v ?r") 
        proof -
          have e: "\<forall>x\<in>set vs. (#) x ` set(snd(T(x, pix x))) = 
                  opt_Hamiltonian_paths \<delta> x (set(nat2list 0 (pix x))) t"
            by (metis "4" Diff_iff add.right_neutral assms(1,2) atLeastLessThan_iff b le0 nat2list_ub table_inv_def
                vs_def)
          have "\<forall>p. (p \<in> ?l) = (p \<in> ?r)"
          proof(clarsimp)
          qed(metis (lifting) case_prodE case_prodI2 e pix_set snd_eqD) 
          thus ?thesis
            by (metis (mono_tags, lifting) Collect_cong Sup_set_def mem_Collect_eq)
        qed

        with 4 and d 
        show "min_distance_ext_inv \<delta> v (d, rs) \<and> (#) v ` set rs = opt_Hamiltonian_paths \<delta> v (set vs) t"
          by (simp add: SUP_cong Union_eq nat2list_Nil opt_Hamiltonian_paths_fix plus_1_eq_Suc vs_def)
      qed
    qed
  qed
qed


corollary table_inv_upd_ext' :
  assumes "table_inv \<delta> N t T (ix-1)"
      and "ix < 2\<^bsup>N\<^esup>"
      and "ix > 0" 
    shows "table_inv \<delta> N t (upd_tab \<delta> N ix T) ix"
  by (metis One_nat_def assms le_add_diff_inverse2 less_eq_Suc_le table_inv_upd_ext)


text \<open>Successively update the columns up to $2^n-1$ using @{term "upd_tab"}:\<close>
function fill_tab :: "(vertex \<Rightarrow> vertex \<Rightarrow> distance) \<Rightarrow> nat \<Rightarrow> table \<Rightarrow> nat \<Rightarrow> table" 
  where
"fill_tab \<delta> N T ix = (if ix < 2\<^bsup>N\<^esup> - 1 then fill_tab \<delta> N (upd_tab \<delta> N ix T) (ix+1)
                      else T)"
  by pat_completeness auto
termination
  by(relation "measure (\<lambda>(a, b, c, d). 2\<^bsup>b\<^esup> - d)", fastforce+)

declare fill_tab.simps[simp del]


lemma fill_tab :
  assumes "N > 0"
      and "ix > 0"
      and "\<forall>ix'<ix. table_inv \<delta> N t T ix'"
    shows "table_inv \<delta> N t (fill_tab \<delta> N T ix) (2\<^bsup>N\<^esup>-2)"
  using assms
proof(induct ix arbitrary: T rule: wf_induct[where r="measure(\<lambda>x. 2\<^bsup>N\<^esup> - x)"])
  show "wf (measure ((-) (2\<^bsup>N\<^esup>)))" by simp
next
  case h:(2 x)
  have "table_inv \<delta> N t (fill_tab \<delta> N (upd_tab \<delta> N x T) (x+1)) (2\<^bsup>N\<^esup> - 2)"
           if a: "x < 2\<^bsup>N\<^esup> - 1"
  proof(rule h(1)[rule_format, simplified])
    show "2\<^bsup>N\<^esup> - (x+1) < 2\<^bsup>N\<^esup> - x"
      using a by linarith
    next
      show "0 < N" by(rule h(2))
    next
      show "0 < x+1" by simp
    next
      fix ix' assume "ix' < x+1"
      thus "table_inv \<delta> N t (upd_tab \<delta> N x T) ix'"
        by (metis One_nat_def Suc_eq_plus1 Suc_pred h.prems(2,3) less_imp_diff_less not_less_iff_gr_or_eq
            not_less_less_Suc_eq table_inv_upd table_inv_upd_ext' that)
    qed
    with h(3,4) show ?case by(simp add: fill_tab.simps)
qed




subsection \<open>Summing up\<close>

definition
"tsp \<delta> N = 
 (if N = 0 then (\<delta> N N, [[N, N]])
  else (let T = init_tab \<delta> N N in
        let T' = fill_tab \<delta> N T 1 in
        let vs = nat2list 0 (2\<^bsup>N\<^esup>-1) in
        let (d, ps) = min_distance_ext \<delta> N (map (\<lambda>w. (w, T'(w, list2nat 0 N (rem1S w vs)))) vs) in
        (d, map ((#) N) ps)))"




text \<open>Without loss of generality, the salesman is assumed to reside in the location/vertex $N$
      and has to visit each of the locations $0\ldots N-1$ returning subsequently to $N$.
      Now the list(s) forming the value @{term "tsp \<delta> N"} represent all of such Hamiltonian cycles 
      that are minimal with respect to $\delta$ as the following theorem shows:\<close>

theorem tsp :
  assumes "tsp \<delta> N = (d, ps)"
  shows "set ps = opt_Hamiltonian_paths \<delta> N {0..<N} N \<and>
         (\<forall>p\<in>set ps. path_distance \<delta> p = d)"
proof(cases "N = 0")
  case True
  with assms and opt_Hamiltonian_paths0 show ?thesis
    by(fastforce simp: tsp_def)
next
  define vs where "vs = nat2list 0 (2\<^bsup>N\<^esup> - 1)"
  define pix where "pix = (\<lambda>w. list2nat 0 N (rem1S w vs))"
  define T where "T = fill_tab \<delta> N (init_tab \<delta> N N) 1"
  have vs1:"vs = rev[0..<N]"
    using nat2list_pred_pow2' vs_def by blast
  have pix1:"\<forall>x\<in>set vs. pix x < 2\<^bsup>N\<^esup> - 1 \<and> x \<notin> set(nat2list 0 (pix x))"
    by (simp add: list2nat_rem1S_less list2nat_rem1S_not_in pix_def vs_def)
  with pix_def and vs_def have pix_set: "\<forall>x. set vs - {x} = set(nat2list 0 (pix x))"
    by (metis Diff_iff add.right_neutral diff_less list2nat_inj nat2list_sorted nat2list_ub
        nat_zero_less_power_iff rem1S sorted_wrt_rem1S zero_less_numeral zero_less_one)
  have pix2:"\<forall>x\<in>set vs. pix x \<le> 2\<^bsup>N\<^esup> - 2"
    using length_pos_if_in_set pix1 by fastforce 
  from pix1 vs1 pix_set have pix3: "\<forall>x\<in>set vs. {0..<N} - set (nat2list 0 (pix x)) = {x}"
    by fastforce

  case a:False
  with T_def have inv:"table_inv \<delta> N N T (2\<^bsup>N\<^esup> - 2)"
    by (simp add: fill_tab table_inv_init)

  note inv[simplified table_inv_def]
  with vs1 pix1 pix2 pix_set have 
  c:"\<forall>(h, d', l)\<in>set (map (\<lambda>v. (v, T(v, pix v))) vs). min_distance_ext_inv \<delta> h (d', l)" 
    by clarsimp

  from a and assms obtain ps' where 
  d:"min_distance_ext \<delta> N (map (\<lambda>v. (v, T(v, pix v))) vs) = (d, ps') \<and> ps = map ((#) N) ps'"
    by(clarsimp simp: tsp_def Let_def split_def T_def pix_def vs_def)

  note min_distance_ext[OF d[THEN conjunct1]]
  with a and c and d and vs1 have e:"min_distance_ext_inv \<delta> N (d, ps') \<and>
  set ps = Min_distance_ext \<delta> N {p. \<exists>(h, d', l)\<in>set (map (\<lambda>v. (v, T(v, pix v))) vs). p \<in> (#) h ` set l}"
    by simp

  with d have 1:"\<forall>p\<in>set ps. path_distance \<delta> p = d"
    by (smt (verit) imageE image_set min_distance_ext_invD)

  from vs1 pix_set pix2 pix3 set_rev[of vs] inv[simplified table_inv_def]
  have f:"\<forall>p. (\<exists>v\<in>{0..<N}. case T(v, pix v) of (d', l) \<Rightarrow> p \<in> (#) v ` set l) =
            (\<exists>v\<in>{0..<N}. p \<in> opt_Hamiltonian_paths \<delta> v ({0..<N} - {v}) N)"
    by (smt (verit) atLeastLessThan_upt case_prodE case_prodI2 insertCI rev_rev_ident snd_eqD)

  have "{p. \<exists>x\<in>set vs. case T (x, pix x) of (d', l) \<Rightarrow> p \<in> (#) x ` set l} =
        (\<Union>v\<in>{0..<N}. opt_Hamiltonian_paths \<delta> v ({0..<N} - {v}) N)"
  proof(rule set_eqI)
  qed(clarsimp simp: f vs1)

  with a and e and 1 show ?thesis
  proof(subst opt_Hamiltonian_paths_fix) 
  qed(simp+)

qed




subsection \<open>An example\<close>

text \<open>An asymmetric edge distance function:\<close>
definition "\<delta> (u :: vertex) (v :: vertex) = 
(if u = 0 then (if v = 1 then 9
                else (if v = 2 then 10
                      else (if v = 3 then 5 else 0)))
 else (if u = 1 then (if v = 0 then 13
                      else (if v = 2 then 12
                            else (if v = 3 then 6 else 0)))
       else (if u = 2 then (if v = 0 then 8
                            else (if v = 1 then 9
                                  else (if v = 3 then 8 else 0)))
             else (if u = 3 then (if v = 0 then 10
                                  else (if v = 1 then 15
                                        else (if v = 2 then 20 else 0)))
                   else 0))))"

text \<open>For this $\delta$ there is exactly one optimal Hamiltonian cycle that starts/ends in $3$ 
      passing through each of the vertices $0, 1, 2$ once:\<close>
value "tsp \<delta> 3"


end