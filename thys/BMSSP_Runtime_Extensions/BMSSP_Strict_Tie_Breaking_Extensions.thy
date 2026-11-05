theory BMSSP_Strict_Tie_Breaking_Extensions
  imports "BMSSP_Correctness.BMSSP_Strict_Tie_Breaking"
    BMSSP_Direct_Insert_Extensions
begin

context strict_tie_breaking_digraph
begin

theorem charged_direct_insert_costed_step_seen_success:
  assumes loop:
      "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        charged_Us child_outputs U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and success: "B' = B"
  shows "card (find_pivots_seen_capped k cap d S B) \<le> card U"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF sound S_reaches])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF sound pre S_reaches] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S S_reaches by blast
  have trace:
    "concrete_partition_loop_trace ?P B a bs d' B' charged_Us U_loop"
    by (rule charged_direct_insert_costed_partition_loop_state_trace
      [OF loop sound_fp pivot_pre P_reaches])
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF trace])
  have assembly:
    "U_loop \<union>
      {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
        dist s v} =
      bound_tree S B'"
    by (rule concrete_capped_find_pivots_final_tree_assembly
      [OF sound pre S_reaches loop_post])
  have U_tree: "U = bound_tree S B"
    using U_def assembly success by simp
  have seen_subset:
    "find_pivots_seen_capped k cap d S B \<subseteq> U"
    using find_pivots_seen_capped_subset_bound_tree
      [OF sound pre S_reaches below] U_tree by simp
  have finite_U: "finite U"
    unfolding U_tree bound_tree_def using finite_V by auto
  show ?thesis
    by (rule card_mono[OF finite_U seen_subset])
qed

theorem charged_direct_insert_costed_capped_step_threshold_if_not_success:
  assumes loop:
      "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        charged_Us child_outputs U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and not_success: "B' \<noteq> B"
  shows "k * cap \<le> card U"
proof -
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  have sound_fp: "sound_label ?d_fp"
    unfolding find_pivots_label_capped_def
    by (rule fp_iter_capped_label_sound[OF sound S_reaches])
  have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
    using find_pivots_capped_establishes_pivot_pre_concrete
      [OF sound pre S_reaches] .
  have P_subset_S: "?P \<subseteq> S"
    unfolding find_pivots_pivots_capped_def by auto
  have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
    using P_subset_S S_reaches by blast
  have loop_class:
    "B' = B \<or> k * cap \<le> card U_loop"
    by (rule charged_direct_insert_costed_partition_loop_state_success_or_threshold
      [OF loop sound_fp pivot_pre P_reaches])
  have threshold_loop: "k * cap \<le> card U_loop"
    using loop_class not_success by blast
  have trace:
    "concrete_partition_loop_trace ?P B a bs d' B' charged_Us U_loop"
    by (rule charged_direct_insert_costed_partition_loop_state_trace
      [OF loop sound_fp pivot_pre P_reaches])
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF trace])
  have finite_U_loop: "finite U_loop"
    using loop_post unfolding bmssp_post_full_def by simp
  have finite_U: "finite U"
    unfolding U_def using finite_U_loop by simp
  have U_loop_subset: "U_loop \<subseteq> U"
    unfolding U_def by blast
  have "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  then show ?thesis
    using threshold_loop by linarith
qed

theorem charged_direct_insert_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold:
  assumes degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and insert:
      "partition_initial_insert_cost_bound c_insert t
        (find_pivots_pivots_capped k cap d S B)"
    and loop:
      "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
        (find_pivots_label_capped k cap d S B)
        (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
        charged_Us child_outputs U_loop c_loop child_costs"
    and U_def:
      "U = U_loop \<union>
        {v \<in> bound_tree S B'. find_pivots_label_capped k cap d S B v =
          dist s v}"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and S_k_cap: "k * card S \<le> cap"
    and anti: "tree_antichain S"
    and k_pos: "0 < k"
    and seen_success:
      "B' = B \<Longrightarrow>
       card (find_pivots_seen_capped k cap d S B) \<le> card U"
  shows "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le>
    2 * A * card U"
proof (cases "B' = B")
  case True
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  show ?thesis
    by (rule find_pivots_scan_and_initial_insert_budget_from_seen_scaled
      [OF S_subset degree anti S_k_cap insert insert_scaled_factor
        seen_scaled_factor seen_success[OF True]])
next
  case False
  have S_subset: "S \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have S_cap: "card S \<le> cap"
  proof -
    have "card S \<le> k * card S"
      using k_pos by (cases k) simp_all
    then show ?thesis
      using S_k_cap by linarith
  qed
  have progress: "k * cap \<le> card U"
    by (rule charged_direct_insert_costed_capped_step_threshold_if_not_success
      [OF loop U_def sound pre S_reaches False])
  show ?thesis
    by (rule find_pivots_scan_and_initial_insert_budget_from_progress
      [OF S_subset degree S_cap insert degree_factor insert_factor progress])
qed

theorem charged_direct_insert_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_budget:
  assumes run:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child charged_child U_child S_child B_child d_child B_child'.
        \<lbrakk>charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L charged_child"
    and source_factor: "Suc h \<le> A"
    and source_progress:
      "\<And>child_sources.
        list_all2
          (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
            charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
              d_child B_child' U_child c_child \<and>
            bmssp_pre_full d S_child B_child \<and>
            (\<forall>x\<in>S_child. reachable s x) \<and>
            card S_child \<le> M_of l \<and>
            (\<forall>x\<in>S_child. below_bound (d x) B_child))
          child_sources (range_tree_child_list P a bs) \<Longrightarrow>
        sum_list (map card child_sources) \<le>
          card (range_tree_chain P a bs B')"
    and edge_budget:
      "t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
       h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))
       \<le> H * card (outgoing_edges U)"
  shows "c \<le> A * Suc L * card U + (R + H) * card (outgoing_edges U)"
proof -
  have loop:
    "c \<le>
      A * Suc L * card U + R * card (outgoing_edges U) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))"
    by (rule charged_direct_insert_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_ranges
      [OF run sound pre P_reaches P_k_cap P_anti child_bound source_factor
        source_progress])
  have "c \<le> A * Suc L * card U + R * card (outgoing_edges U) +
      H * card (outgoing_edges U)"
    using loop edge_budget by linarith
  also have "\<dots> = A * Suc L * card U + (R + H) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem charged_direct_insert_costed_nonbase_step_closes_level_bound_from_child_bound_with_invariants_and_edge_budget:
  assumes loop:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and P_k_cap: "k * card P \<le> cap"
    and P_anti: "tree_antichain P"
    and child_bound:
      "\<And>c_child charged_child U_child S_child B_child d_child B_child'.
        \<lbrakk>charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> level_range_cost_bound A R L charged_child"
    and source_factor: "Suc h \<le> A"
    and source_progress:
      "\<And>child_sources.
        list_all2
          (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
            charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
              d_child B_child' U_child c_child \<and>
            bmssp_pre_full d S_child B_child \<and>
            (\<forall>x\<in>S_child. reachable s x) \<and>
            card S_child \<le> M_of l \<and>
            (\<forall>x\<in>S_child. below_bound (d x) B_child))
          child_sources (range_tree_child_list P a bs) \<Longrightarrow>
        sum_list (map card child_sources) \<le>
          card (range_tree_chain P a bs B')"
    and edge_budget:
      "t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
       h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))
       \<le> H * card (outgoing_edges U_loop)"
    and U_def: "U = U_loop \<union> W"
    and finite_U: "finite U"
    and scan_insert: "c_scan_insert \<le> A * card U"
    and c_def: "c = c_scan_insert + c_loop"
  shows "c \<le> A * Suc (Suc L) * card U +
    (R + H) * card (outgoing_edges U)"
proof -
  have loop_bound:
    "c_loop \<le> A * Suc L * card U_loop +
      (R + H) * card (outgoing_edges U_loop)"
    by (rule charged_direct_insert_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_budget
      [OF loop sound pre P_reaches P_k_cap P_anti child_bound source_factor
        source_progress edge_budget])
  have U_loop_subset: "U_loop \<subseteq> U"
    using U_def by blast
  have card_loop_le: "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  have outgoing_subset: "outgoing_edges U_loop \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF U_loop_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le:
    "card (outgoing_edges U_loop) \<le> card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have "c \<le>
      A * card U +
      (A * Suc L * card U + (R + H) * card (outgoing_edges U))"
  proof -
    have loop_to_U:
      "c_loop \<le> A * Suc L * card U +
        (R + H) * card (outgoing_edges U)"
    proof -
      have "A * Suc L * card U_loop \<le> A * Suc L * card U"
        using card_loop_le by simp
      moreover have "(R + H) * card (outgoing_edges U_loop) \<le>
          (R + H) * card (outgoing_edges U)"
        using card_out_le by simp
      ultimately show ?thesis
        using loop_bound by linarith
    qed
    show ?thesis
      using scan_insert loop_to_U c_def by linarith
  qed
  also have "\<dots> =
      A * Suc (Suc L) * card U + (R + H) * card (outgoing_edges U)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

end

end
