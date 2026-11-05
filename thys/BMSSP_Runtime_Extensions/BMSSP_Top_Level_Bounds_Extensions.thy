theory BMSSP_Top_Level_Bounds_Extensions
  imports "BMSSP_Correctness.BMSSP_Top_Level_Bounds"
    BMSSP_Strict_Tie_Breaking_Extensions
begin

context strict_tie_breaking_digraph
begin

theorem charged_direct_insert_algorithm_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run:
      "charged_direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d'"
proof
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule charged_direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  show "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  show "sssp_correct d'"
    by (rule finite_initial_label_charged_direct_insert_costed_top_level_correct
      [OF all_reachable run])
qed

theorem charged_direct_insert_algorithm_reachable_correct:
  assumes run:
      "charged_direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "sssp_correct d'"
  by (rule finite_initial_label_charged_direct_insert_costed_top_level_reachable_correct[OF run])

definition charged_direct_insert_top_level_run ::
  "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> bool" where
  "charged_direct_insert_top_level_run D N d' U c \<longleftrightarrow>
     (let p = sssp_log_one_third_param N;
          q = sssp_log_two_thirds_param N
      in charged_direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c)"

definition charged_direct_insert_top_level_cost :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "charged_direct_insert_top_level_cost D N c \<longleftrightarrow>
     (\<exists>d' U. charged_direct_insert_top_level_run D N d' U c)"

definition charged_direct_insert_top_level_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "charged_direct_insert_top_level_time D N =
     (LEAST c. charged_direct_insert_top_level_cost D N c)"

definition charged_direct_insert_closed_refined_bound_log_params_fixed_degree ::
  "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N \<longleftrightarrow>
     (let p = sssp_log_one_third_param N;
          q = sssp_log_two_thirds_param N
      in \<forall>d' U c.
        charged_direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
          (bmssp_level_cap p q p) p
          finite_initial_label {s} Infinity d' Infinity U c \<longrightarrow>
        c \<le> bmssp_refined_graph_time_bound
          (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
          (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count)"

theorem charged_direct_insert_top_level_run_correct:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and run: "charged_direct_insert_top_level_run D N d' U c"
  shows "U = V \<and> sssp_correct d'"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  have run':
    "charged_direct_insert_costed_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p
      (bmssp_level_cap ?p ?q ?p) ?p
      finite_initial_label {s} Infinity d' Infinity U c"
    using run unfolding charged_direct_insert_top_level_run_def
    by (simp add: Let_def)
  show ?thesis
    by (rule charged_direct_insert_algorithm_correct[OF all_reachable run'])
qed

lemma charged_direct_insert_top_level_cost_exists_from_initial_loop:
  fixes D N p q cap l :: nat
    and d_fp :: "'a \<Rightarrow> real"
    and P :: "'a set"
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
    and cap_def: "cap \<equiv> bmssp_level_cap p q p"
    and l_def: "l \<equiv> p - 1"
    and d_fp_def:
      "d_fp \<equiv> find_pivots_label_capped p cap finite_initial_label {s}
        Infinity"
    and P_def:
      "P \<equiv> find_pivots_pivots_capped p cap finite_initial_label {s}
        Infinity"
  assumes loop:
      "\<exists>d' a betas bs charged_Us child_outputs U_loop c_loop
          child_costs_loop c_insert.
        charged_direct_insert_costed_partition_loop_state D
          (bmssp_level_cap p q) q p p cap l d_fp P Infinity d'
          (label_partition_view d_fp P) a betas bs Infinity charged_Us
          child_outputs U_loop c_loop child_costs_loop \<and>
        complete_on d'
          {v \<in> bound_tree {s} Infinity. d_fp v = dist s v} \<and>
        partition_initial_insert_cost_bound c_insert q P"
  shows "\<exists>c. charged_direct_insert_top_level_cost D N c"
proof -
  have p_eq: "p = Suc l"
    using sssp_log_one_third_param_pos[of N]
    unfolding p_def l_def by simp
  obtain d' a betas bs charged_Us child_outputs U_loop c_loop
      child_costs_loop c_insert where
    loop_run:
      "charged_direct_insert_costed_partition_loop_state D
        (bmssp_level_cap p q) q p p cap l d_fp P Infinity d'
        (label_partition_view d_fp P) a betas bs Infinity charged_Us
        child_outputs U_loop c_loop child_costs_loop"
    and complete:
      "complete_on d' {v \<in> bound_tree {s} Infinity. d_fp v = dist s v}"
    and insert: "partition_initial_insert_cost_bound c_insert q P"
    using loop by blast
  let ?U =
    "U_loop \<union> {v \<in> bound_tree {s} Infinity. d_fp v = dist s v}"
  let ?c =
    "fp_iter_capped_scan_cost p cap finite_initial_label {s} {s} Infinity +
      c_insert + c_loop"
  have root_run:
    "charged_direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p cap
      p finite_initial_label {s} Infinity d' Infinity ?U ?c"
  proof -
    have step_run:
      "charged_direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p cap
        (Suc l) finite_initial_label {s} Infinity d' Infinity ?U ?c"
      by (rule charged_direct_insert_costed_bmssp_step_with_insert_cost
        [where D = "label_partition_view d_fp P"])
        (use loop_run complete insert in \<open>simp_all add: d_fp_def P_def\<close>)
    then show ?thesis
      using p_eq by simp
  qed
  have "charged_direct_insert_top_level_run D N d' ?U ?c"
    unfolding charged_direct_insert_top_level_run_def
    using root_run unfolding p_def q_def cap_def by (simp add: Let_def)
  then have "charged_direct_insert_top_level_cost D N ?c"
    unfolding charged_direct_insert_top_level_cost_def by blast
  then show ?thesis
    by blast
qed

lemma charged_direct_insert_top_level_time_witness:
  assumes "charged_direct_insert_top_level_cost D N c"
  shows "charged_direct_insert_top_level_cost D N
    (charged_direct_insert_top_level_time D N)"
  unfolding charged_direct_insert_top_level_time_def
  by (rule LeastI_ex) (use assms in blast)

lemma charged_direct_insert_top_level_time_le:
  assumes "charged_direct_insert_top_level_cost D N c"
  shows "charged_direct_insert_top_level_time D N \<le> c"
  unfolding charged_direct_insert_top_level_time_def
  by (rule Least_le) (rule assms)

theorem charged_direct_insert_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree_from_closed_bound:
  fixes N D p q :: nat
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and closed_bound:
      "charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N"
    and run:
      "charged_direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
        (bmssp_level_cap p q p) p
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count"
proof -
  have UV_correct: "U = V \<and> sssp_correct d'"
    by (rule charged_direct_insert_algorithm_correct[OF all_reachable run])
  have cost:
    "c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * p) (\<lambda>_. q) (\<lambda>_. p)
      (\<lambda>_. p) (\<lambda>_. q) (\<lambda>_. edge_count) vertex_count"
    using closed_bound run
    unfolding charged_direct_insert_closed_refined_bound_log_params_fixed_degree_def
      p_def q_def
    by (simp add: Let_def)
  show ?thesis
    using UV_correct cost by blast
qed

theorem charged_direct_insert_top_level_run_correct_and_refined_bound_log_params_fixed_degree_from_closed_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and closed_bound:
      "charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N"
    and run: "charged_direct_insert_top_level_run D N d' U c"
  shows "U = V \<and> sssp_correct d' \<and>
    c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. edge_count) vertex_count"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  have run':
    "charged_direct_insert_costed_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p
      (bmssp_level_cap ?p ?q ?p) ?p
      finite_initial_label {s} Infinity d' Infinity U c"
    using run unfolding charged_direct_insert_top_level_run_def
    by (simp add: Let_def)
  show ?thesis
    by (rule charged_direct_insert_algorithm_correct_and_refined_graph_bound_log_params_fixed_degree_from_closed_bound
      [OF all_reachable closed_bound run'])
qed

theorem charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree_from_closed_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and closed_bound:
      "charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N"
    and cost: "charged_direct_insert_top_level_cost D N c"
  shows "c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. edge_count) vertex_count"
proof -
  obtain d' U where run: "charged_direct_insert_top_level_run D N d' U c"
    using cost unfolding charged_direct_insert_top_level_cost_def by blast
  show ?thesis
    using charged_direct_insert_top_level_run_correct_and_refined_bound_log_params_fixed_degree_from_closed_bound
      [OF all_reachable closed_bound run]
    by blast
qed

theorem charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and closed_bound:
      "charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N"
    and cost: "charged_direct_insert_top_level_cost D N c"
  shows "c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. edge_count) vertex_count"
  by (rule charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree_from_closed_bound
    [OF all_reachable closed_bound cost])

theorem charged_direct_insert_top_level_time_refined_bound_log_params_fixed_degree_from_closed_bound:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and closed_bound:
      "charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N"
    and run_exists: "charged_direct_insert_top_level_cost D N c"
  shows "charged_direct_insert_top_level_time D N \<le>
    bmssp_refined_graph_time_bound
      (\<lambda>_. Suc D * sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. edge_count) vertex_count"
proof -
  have cost:
    "charged_direct_insert_top_level_cost D N
      (charged_direct_insert_top_level_time D N)"
    by (rule charged_direct_insert_top_level_time_witness[OF run_exists])
  show ?thesis
    by (rule charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree_from_closed_bound
      [OF all_reachable closed_bound cost])
qed

lemma charged_direct_insert_top_level_cost_exists_if_source_pivot_finishes:
  fixes D N p q cap l :: nat
    and d_fp :: "'a \<Rightarrow> real"
    and P :: "'a set"
    and Bmax :: real
  defines p_def: "p \<equiv> sssp_log_one_third_param N"
    and q_def: "q \<equiv> sssp_log_two_thirds_param N"
    and cap_def: "cap \<equiv> bmssp_level_cap p q p"
    and l_def: "l \<equiv> p - 1"
    and d_fp_def:
      "d_fp \<equiv> find_pivots_label_capped p cap finite_initial_label {s}
        Infinity"
    and P_def:
      "P \<equiv> find_pivots_pivots_capped p cap finite_initial_label {s}
        Infinity"
  assumes P_source: "P = {s}"
    and source_below: "d_fp s < Bmax"
    and Bmax_nonneg: "0 \<le> Bmax"
    and child_pre: "bmssp_pre_full d_fp {s} (Fin Bmax)"
    and below_threshold: "card (bound_tree P (Fin 0)) < p * cap"
    and child:
      "charged_direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
        cap l d_fp {s} (Fin Bmax) (dist s) (Fin Bmax) U_child c_child"
    and direct_empty:
      "edge_relaxation_pairs_in_bound (dist s) (range_tree P 0 (Fin Bmax))
        Bmax Infinity = []"
  shows "\<exists>c. charged_direct_insert_top_level_cost D N c"
proof -
  let ?D = "label_partition_view d_fp P"
  let ?D_pull = "label_partition_view d_fp {}"
  let ?tail_U =
    "bound_tree P (Fin Bmax) \<union> \<Union>(set [range_tree P Bmax Infinity])"
  let ?W = "\<lambda>B. {v \<in> bound_tree {s} B. d_fp v = dist s v}"
  have p_pos: "0 < p"
    using sssp_log_one_third_param_pos[of N] unfolding p_def .
  have p_eq: "p = Suc l"
    using sssp_log_one_third_param_pos[of N]
    unfolding p_def l_def by simp
  have M_pos: "0 < bmssp_level_cap p q l"
    using p_pos unfolding bmssp_level_cap_def by simp
  have pull:
    "pull_separates ?D (bmssp_level_cap p q l) Bmax {s} Bmax ?D_pull"
    unfolding pull_separates_def
    using P_source M_pos by simp
  have split: "{s} = split_below d_fp P Bmax"
    using P_source source_below unfolding split_below_def by auto
  have source_reaches: "\<forall>x\<in>{s}. reachable s x"
    using reachable_refl[OF source_in_V] by simp
  have preserved: "complete_preserved (dist s) (dist s) U_child"
    unfolding complete_preserved_def by simp
  have complete_prefix: "complete_on (dist s) (bound_tree P (Fin 0))"
    unfolding complete_on_def by simp
  have tail:
    "charged_direct_insert_costed_partition_loop_state D
      (bmssp_level_cap p q) q p p cap l d_fp P Infinity (dist s)
      (batch_min_update ?D_pull
        (edge_relaxation_pairs_in_bound (dist s)
           (range_tree P 0 (Fin Bmax)) Bmax Infinity @
         edge_relaxation_pairs_between (dist s)
           (range_tree P 0 (Fin Bmax)) Bmax Bmax @
         label_pairs_between d_fp {s} Bmax Bmax))
      Bmax [] [] Infinity [range_tree P Bmax Infinity] []
      ?tail_U 0 []"
  proof -
    have lower_empty:
      "edge_relaxation_pairs_between (dist s)
        (range_tree P 0 (Fin Bmax)) Bmax Bmax = []"
      unfolding edge_relaxation_pairs_between_def
      by (auto simp: filter_empty_conv split: prod.splits)
    have source_empty: "label_pairs_between d_fp {s} Bmax Bmax = []"
      unfolding label_pairs_between_def
      by (simp add: filter_empty_conv)
    have D_next:
      "batch_min_update ?D_pull
        (edge_relaxation_pairs_in_bound (dist s)
           (range_tree P 0 (Fin Bmax)) Bmax Infinity @
         edge_relaxation_pairs_between (dist s)
           (range_tree P 0 (Fin Bmax)) Bmax Bmax @
         label_pairs_between d_fp {s} Bmax Bmax) = ?D_pull"
      using direct_empty lower_empty source_empty
      unfolding batch_min_update_def by simp
    have empty: "keys_of ?D_pull = {}"
      by simp
    have complete: "complete_on (dist s) (bound_tree P Infinity)"
      unfolding complete_on_def by simp
    have run:
      "charged_direct_insert_costed_partition_loop_state D
        (bmssp_level_cap p q) q p p cap l d_fp P Infinity (dist s)
        ?D_pull Bmax [] [] Infinity [range_tree P Bmax Infinity] []
        ?tail_U 0 []"
      by (rule Charged_Direct_Insert_State_Done)
        (use empty complete in simp_all)
    then show ?thesis
      using D_next by simp
  qed
  let ?charged_child = "range_tree P 0 (Fin Bmax)"
  let ?direct =
    "edge_relaxation_pairs_in_bound (dist s) ?charged_child Bmax Infinity"
  let ?lower =
    "edge_relaxation_pairs_between (dist s) ?charged_child Bmax Bmax"
  let ?sources = "label_pairs_between d_fp {s} Bmax Bmax"
  let ?batch = "?direct @ ?lower @ ?sources"
  have step_exists:
    "\<exists>c_loop child_costs_loop.
      charged_direct_insert_costed_partition_loop_state D
        (bmssp_level_cap p q) q p p cap l d_fp P Infinity (dist s) ?D
        0 [Bmax] [Bmax] Infinity [?charged_child, range_tree P Bmax Infinity]
        [U_child]
        (bound_tree P (Fin 0) \<union>
          \<Union>(set [?charged_child, range_tree P Bmax Infinity]))
        c_loop child_costs_loop"
    by (rule charged_direct_insert_partition_loop_state_step_exists
      [where \<Delta> = D and M_of = "bmssp_level_cap p q" and t = q and h = p
        and k = p and cap = cap and l = l and d = d_fp and P = P
        and B = Infinity and d' = "dist s" and D = ?D and a = 0
        and Bmax = Bmax and S_pull = "{s}" and beta = Bmax
        and D_pull = ?D_pull and d_child = "dist s" and b = Bmax
        and U_child = U_child and c_child = c_child and betas = "[]"
        and bs = "[]" and B' = Infinity
        and charged_tail = "[range_tree P Bmax Infinity]"
        and child_outputs_tail = "[]" and U_tail = ?tail_U and c_tail = 0
        and child_costs_tail = "[]"])
      (use pull child_pre split source_reaches complete_prefix Bmax_nonneg below_threshold
        child preserved tail in simp_all)
  then obtain c_loop child_costs_loop where loop:
    "charged_direct_insert_costed_partition_loop_state D
      (bmssp_level_cap p q) q p p cap l d_fp P Infinity (dist s) ?D
      0 [Bmax] [Bmax] Infinity [?charged_child, range_tree P Bmax Infinity]
      [U_child]
      (bound_tree P (Fin 0) \<union>
        \<Union>(set [?charged_child, range_tree P Bmax Infinity]))
      c_loop child_costs_loop"
    by blast
  have completeW: "complete_on (dist s) (?W Infinity)"
    unfolding complete_on_def by simp
  have insert: "partition_initial_insert_cost_bound 0 q P"
    unfolding partition_initial_insert_cost_bound_def by simp
  let ?U = "(bound_tree P (Fin 0) \<union>
      \<Union>(set [?charged_child, range_tree P Bmax Infinity])) \<union> ?W Infinity"
  let ?c = "fp_iter_capped_scan_cost p cap finite_initial_label {s} {s}
      Infinity + 0 + c_loop"
  have root_suc:
    "charged_direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p cap
      (Suc l) finite_initial_label {s} Infinity (dist s) Infinity ?U ?c"
  proof (rule charged_direct_insert_costed_bmssp_step_with_insert_cost
      [where D = ?D and c_insert = 0])
    show "?D =
        label_partition_view
          (find_pivots_label_capped p cap finite_initial_label {s} Infinity)
          (find_pivots_pivots_capped p cap finite_initial_label {s} Infinity)"
      unfolding d_fp_def P_def by simp
    show "partition_initial_insert_cost_bound 0 q
        (find_pivots_pivots_capped p cap finite_initial_label {s} Infinity)"
      using insert unfolding P_def .
    show "charged_direct_insert_costed_partition_loop_state D
        (bmssp_level_cap p q) q p p cap l
        (find_pivots_label_capped p cap finite_initial_label {s} Infinity)
        (find_pivots_pivots_capped p cap finite_initial_label {s} Infinity)
        Infinity (dist s) ?D 0 [Bmax] [Bmax] Infinity
        [?charged_child, range_tree P Bmax Infinity] [U_child]
        (bound_tree P (Fin 0) \<union>
          \<Union>(set [?charged_child, range_tree P Bmax Infinity]))
        c_loop child_costs_loop"
      using loop unfolding d_fp_def P_def .
    show "complete_on (dist s)
        {v \<in> bound_tree {s} Infinity.
          find_pivots_label_capped p cap finite_initial_label {s} Infinity v =
          dist s v}"
      using completeW unfolding d_fp_def .
    show "?U =
        (bound_tree P (Fin 0) \<union>
          \<Union>(set [?charged_child, range_tree P Bmax Infinity])) \<union>
        {v \<in> bound_tree {s} Infinity.
          find_pivots_label_capped p cap finite_initial_label {s} Infinity v =
          dist s v}"
      unfolding d_fp_def by simp
    show "?c = fp_iter_capped_scan_cost p cap finite_initial_label {s} {s}
        Infinity + 0 + c_loop"
      by simp
  qed
  then have root:
    "charged_direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p cap
      p finite_initial_label {s} Infinity (dist s) Infinity ?U ?c"
    using p_eq by simp
  have "charged_direct_insert_top_level_run D N (dist s) ?U ?c"
    unfolding charged_direct_insert_top_level_run_def
    using root unfolding p_def q_def cap_def by (simp add: Let_def)
  then show ?thesis
    unfolding charged_direct_insert_top_level_cost_def by blast
qed

definition charged_direct_insert_source_pivot_finishes :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "charged_direct_insert_source_pivot_finishes D N \<longleftrightarrow>
     (let p = sssp_log_one_third_param N;
          q = sssp_log_two_thirds_param N;
          cap = bmssp_level_cap p q p;
          l = p - 1;
          d_fp = find_pivots_label_capped p cap finite_initial_label {s}
            Infinity;
          P = find_pivots_pivots_capped p cap finite_initial_label {s}
            Infinity
      in \<exists>Bmax U_child c_child.
        P = {s} \<and>
        d_fp s < Bmax \<and>
        0 \<le> Bmax \<and>
        bmssp_pre_full d_fp {s} (Fin Bmax) \<and>
        card (bound_tree P (Fin 0)) < p * cap \<and>
        charged_direct_insert_costed_bmssp D (bmssp_level_cap p q) q p p
          cap l d_fp {s} (Fin Bmax) (dist s) (Fin Bmax)
          U_child c_child \<and>
        edge_relaxation_pairs_in_bound (dist s) (range_tree P 0 (Fin Bmax))
          Bmax Infinity = [])"

lemma charged_direct_insert_top_level_cost_exists_if_source_pivot_finishes_pred:
  assumes "charged_direct_insert_source_pivot_finishes D N"
  shows "\<exists>c. charged_direct_insert_top_level_cost D N c"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  let ?l = "?p - 1"
  let ?d_fp =
    "find_pivots_label_capped ?p ?cap finite_initial_label {s} Infinity"
  let ?P =
    "find_pivots_pivots_capped ?p ?cap finite_initial_label {s} Infinity"
  obtain Bmax U_child c_child where
    P_source: "?P = {s}"
    and source_below: "?d_fp s < Bmax"
    and Bmax_nonneg: "0 \<le> Bmax"
    and child_pre: "bmssp_pre_full ?d_fp {s} (Fin Bmax)"
    and below_threshold: "card (bound_tree ?P (Fin 0)) < ?p * ?cap"
    and child:
      "charged_direct_insert_costed_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p
        ?cap ?l ?d_fp {s} (Fin Bmax) (dist s) (Fin Bmax)
        U_child c_child"
    and direct_empty:
      "edge_relaxation_pairs_in_bound (dist s) (range_tree ?P 0 (Fin Bmax))
        Bmax Infinity = []"
    using assms unfolding charged_direct_insert_source_pivot_finishes_def
    by (auto simp: Let_def)
  show ?thesis
  proof (rule charged_direct_insert_top_level_cost_exists_if_source_pivot_finishes)
    show "?P = {s}"
      by (rule P_source)
    show "?d_fp s < Bmax"
      by (rule source_below)
    show "0 \<le> Bmax"
      by (rule Bmax_nonneg)
    show "bmssp_pre_full ?d_fp {s} (Fin Bmax)"
      by (rule child_pre)
    show "card (bound_tree ?P (Fin 0)) < ?p * ?cap"
      by (rule below_threshold)
    show "charged_direct_insert_costed_bmssp D (bmssp_level_cap ?p ?q) ?q
        ?p ?p ?cap ?l ?d_fp {s} (Fin Bmax) (dist s) (Fin Bmax)
        U_child c_child"
      by (rule child)
    show "edge_relaxation_pairs_in_bound (dist s) (range_tree ?P 0 (Fin Bmax))
        Bmax Infinity = []"
      by (rule direct_empty)
  qed
qed

lemma eventually_charged_direct_insert_top_level_cost_if_source_pivot_finishes:
  assumes
    "eventually (\<lambda>N. charged_direct_insert_source_pivot_finishes D N) at_top"
  shows "eventually (\<lambda>N. \<exists>c. charged_direct_insert_top_level_cost D N c)
    at_top"
  using assms
proof eventually_elim
  case (elim N)
  show ?case
    by (rule charged_direct_insert_top_level_cost_exists_if_source_pivot_finishes_pred
      [OF elim])
qed

lemma charged_direct_insert_top_level_cost_exists_if_top_pivots_empty:
  assumes pivots_empty:
    "find_pivots_pivots_capped (sssp_log_one_third_param N)
      (bmssp_level_cap (sssp_log_one_third_param N)
        (sssp_log_two_thirds_param N) (sssp_log_one_third_param N))
      finite_initial_label {s} Infinity = {}"
  shows "\<exists>c. charged_direct_insert_top_level_cost D N c"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  let ?l = "?p - 1"
  let ?d_fp = "find_pivots_label_capped ?p ?cap finite_initial_label {s} Infinity"
  let ?P = "find_pivots_pivots_capped ?p ?cap finite_initial_label {s} Infinity"
  let ?D = "label_partition_view ?d_fp ?P"
  let ?U_loop = "bound_tree ?P (Fin 0) \<union> \<Union>(set [range_tree ?P 0 Infinity])"
  let ?W = "{v \<in> bound_tree {s} Infinity. ?d_fp v = dist s v}"
  let ?U = "?U_loop \<union> ?W"
  let ?c = "fp_iter_capped_scan_cost ?p ?cap finite_initial_label {s} {s} Infinity"
  have p_eq: "?p = Suc ?l"
    using sssp_log_one_third_param_pos[of N] by simp
  have empty: "keys_of ?D = {}"
    using pivots_empty unfolding label_partition_view_def by simp
  have loop:
    "charged_direct_insert_costed_partition_loop_state D
      (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap ?l ?d_fp ?P Infinity
      (dist s) ?D 0 [] [] Infinity [range_tree ?P 0 Infinity] []
      ?U_loop 0 []"
    by (rule Charged_Direct_Insert_State_Done)
      (use empty complete_on_dist in simp_all)
  have complete: "complete_on (dist s) ?W"
    by (rule complete_on_dist)
  have insert: "partition_initial_insert_cost_bound 0 ?q ?P"
    unfolding partition_initial_insert_cost_bound_def by simp
  have root_suc:
    "charged_direct_insert_costed_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p
      ?cap (Suc ?l) finite_initial_label {s} Infinity (dist s) Infinity
      ?U ?c"
    by (rule charged_direct_insert_costed_bmssp_step_with_insert_cost
      [where D = ?D and c_insert = 0])
      (use loop complete insert in simp_all)
  then have root:
    "charged_direct_insert_costed_bmssp D (bmssp_level_cap ?p ?q) ?q ?p ?p
      ?cap ?p finite_initial_label {s} Infinity (dist s) Infinity ?U ?c"
    using p_eq by simp
  have "charged_direct_insert_top_level_run D N (dist s) ?U ?c"
    unfolding charged_direct_insert_top_level_run_def
    using root by (simp add: Let_def)
  then have "charged_direct_insert_top_level_cost D N ?c"
    unfolding charged_direct_insert_top_level_cost_def by blast
  then show ?thesis
    by blast
qed

lemma eventually_charged_direct_insert_top_level_cost_from_empty_top_pivots:
  "eventually (\<lambda>N. \<exists>c. charged_direct_insert_top_level_cost D N c) at_top"
  using eventually_top_level_pivots_empty
    [of finite_initial_label Infinity]
proof eventually_elim
  case (elim N)
  show ?case
    by (rule charged_direct_insert_top_level_cost_exists_if_top_pivots_empty
      [OF elim])
qed

end

end
