theory BMSSP_Path_Family
  imports BMSSP_Verified_Runtime
begin

section \<open>A Size-Parametric BMSSP Running-Time Bound over a Growing Graph Family\<close>

text \<open>
  The headline @{thm [source] bmssp_runtime_headline_instance.bmssp_runtime_bigo_target}
  is stated for a graph fixed by the locale, with the asymptotic variable
  feeding only the internal logarithmic schedule; the edge-count factor in its
  target is a constant.  This theory removes that limitation by exhibiting a
  genuine \emph{family} of graphs whose size grows without bound: the
  unit-weight directed path \<open>P\<^sub>k\<close> on vertices \<open>0, \<dots>, k\<close> with edges
  \<open>i \<rightarrow> i + 1\<close>.  For this family \<open>card (E\<^sub>k) = k\<close> and
  \<open>card (V\<^sub>k) = k + 1\<close> both grow with \<open>k\<close>, so \<open>k\<close> is a true graph-size
  variable, and we prove the BMSSP running time is
  \<open>O(k \<cdot> (ln k)\<^bsup>2/3\<^esup>)\<close>.
\<close>

subsection \<open>The path family\<close>

definition path_k_V :: "nat \<Rightarrow> nat set" where
  "path_k_V k = {0..k}"

definition path_k_E :: "nat \<Rightarrow> (nat \<times> nat) set" where
  "path_k_E k = (\<lambda>i. (i, Suc i)) ` {0..<k}"

definition path_k_weight :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "path_k_weight k u v = (if (u, v) \<in> path_k_E k then 1 else 0)"

subsection \<open>Structural and cardinality lemmas\<close>

lemma path_k_V_eq: "path_k_V k = {0..k}"
  unfolding path_k_V_def ..

lemma path_k_E_iff: "(u, v) \<in> path_k_E k \<longleftrightarrow> v = Suc u \<and> u < k"
  unfolding path_k_E_def by auto

lemma path_k_no_incoming_0: "(u, 0) \<notin> path_k_E k"
  by (simp add: path_k_E_iff)

lemma path_k_incoming_unique:
  "(u, j) \<in> path_k_E k \<longleftrightarrow> (0 < j \<and> j \<le> k \<and> u = j - 1)"
  by (auto simp: path_k_E_iff)

lemma path_k_card_V: "card (path_k_V k) = Suc k"
  unfolding path_k_V_eq by simp

lemma path_k_card_E: "card (path_k_E k) = k"
proof -
  have "inj_on (\<lambda>i. (i, Suc i)) {0..<k}"
    by (rule inj_onI) auto
  then show ?thesis
    unfolding path_k_E_def by (simp add: card_image)
qed

lemma path_k_finite_V: "finite (path_k_V k)"
  unfolding path_k_V_eq by simp

lemma path_k_finite_E: "finite (path_k_E k)"
  unfolding path_k_E_def by simp

subsection \<open>Easy locale obligations, uniform in \<open>k\<close>\<close>

lemma path_k_finite_weighted_digraph:
  "finite_weighted_digraph (path_k_V k) (path_k_E k) (path_k_weight k) 0"
proof
  show "finite (path_k_V k)"
    by (rule path_k_finite_V)
  show "0 \<in> path_k_V k"
    unfolding path_k_V_eq by simp
  show "\<And>u v. (u, v) \<in> path_k_E k \<Longrightarrow> u \<in> path_k_V k \<and> v \<in> path_k_V k"
    by (auto simp: path_k_E_iff path_k_V_eq)
  show "\<And>u v. (u, v) \<in> path_k_E k \<Longrightarrow> 0 \<le> path_k_weight k u v"
    by (simp add: path_k_weight_def)
qed

lemma path_k_positive_weight:
  "(u, v) \<in> path_k_E k \<Longrightarrow> 0 < path_k_weight k u v"
  by (simp add: path_k_weight_def)

subsection \<open>The unconditional cost-recurrence bound (FLOOR)\<close>

text \<open>
  The function @{term path_size_cost} is exactly the closed cost expression
  that bounds a BMSSP run on \<open>P\<^sub>k\<close> at schedule parameter \<open>k\<close>, with the graph
  cardinalities substituted: edge slot \<open>k\<close> and vertex slot \<open>Suc k\<close>.  Its
  asymptotic bound holds unconditionally --- no run existence and no
  shortest-walk uniqueness are required --- and already exhibits a genuine
  size-parametric \<open>O(k \<cdot> (ln k)\<^bsup>2/3\<^esup>)\<close> growth in which both the edge
  count \<open>k\<close> and the vertex count \<open>Suc k\<close> grow with the asymptotic variable.
\<close>

definition path_size_cost :: "nat \<Rightarrow> nat" where
  "path_size_cost k =
     bmssp_refined_graph_time_bound
       (\<lambda>_. Suc 1 * sssp_log_one_third_param k)
       (\<lambda>_. sssp_log_two_thirds_param k)
       (\<lambda>_. sssp_log_one_third_param k)
       (\<lambda>_. sssp_log_one_third_param k)
       (\<lambda>_. sssp_log_two_thirds_param k)
       (\<lambda>_. k) (Suc k)"

theorem path_size_cost_bigo_size:
  "(\<lambda>k. real (path_size_cost k))
     \<in> O(\<lambda>k. real k * (ln (real k + 2)) powr (2 / 3))"
proof -
  have "(\<lambda>k. real (path_size_cost k))
      \<in> O(\<lambda>k. sssp_time_target (\<lambda>k. k) k)"
  proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_slack
      [where D = 1 and Cn = 2 and Cm = 1
        and v = "\<lambda>k. Suc k" and m' = "\<lambda>k. k" and m = "\<lambda>k. k"])
    show "0 < (2 :: real)" by simp
    show "0 < (1 :: real)" by simp
    show "eventually (\<lambda>k. real (Suc k) \<le> 2 * real k) at_top"
      by (rule eventually_at_top_linorderI[of 1]) simp
    show "eventually (\<lambda>k. real k \<le> 1 * real k) at_top"
      by simp
    show "eventually
        (\<lambda>k. path_size_cost k \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>_. Suc 1 * sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_two_thirds_param k)
            (\<lambda>_. sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_two_thirds_param k)
            (\<lambda>_. k) (Suc k)) at_top"
      by (simp add: path_size_cost_def)
  qed
  then show ?thesis
    unfolding sssp_time_target_def sssp_log_factor_def by simp
qed

subsection \<open>The forced-degenerate (empty-pivot) regime is provably avoided\<close>

text \<open>
  The only unconditional source of run existence in the development,
  @{thm [source] strict_tie_breaking_digraph.eventually_exact_concrete_top_level_cost_from_empty_top_pivots},
  fires through @{thm [source]
  unique_shortest_digraph.find_pivots_pivots_capped_singleton_empty_if_params_exceed_vertex_count},
  whose hypothesis requires the schedule parameter to \emph{exceed} the vertex
  count.  On \<open>P\<^sub>k\<close> at schedule \<open>k\<close> this hypothesis is
  \<open>Suc k < sssp_log_one_third_param k\<close>, which fails for all large \<open>k\<close>
  because the one-third logarithmic factor grows far slower than \<open>k\<close>.  Hence
  the empty-pivot no-op cannot be the run whose cost the family bound governs:
  any such run does genuine top-level work.
\<close>

lemma sssp_log_one_third_param_le_linear:
  "eventually (\<lambda>k. sssp_log_one_third_param k \<le> Suc k) at_top"
proof (rule eventually_at_top_linorderI[of 1])
  fix k :: nat assume k1: "1 \<le> k"
  have pos: "(0::real) < real k + 2" by simp
  have ge1: "1 \<le> ln (real k + 2)"
  proof -
    have "exp 1 \<le> (3::real)" using exp_le by simp
    also have "(3::real) \<le> real k + 2" using k1 by simp
    finally have "exp 1 \<le> real k + 2" .
    then show ?thesis using ln_ge_iff[of "real k + 2"] by simp
  qed
  have ln_le: "ln (real k + 2) \<le> real k + 1"
    using ln_le_minus_one[OF pos] by simp
  have "sssp_log_factor_one_third k = (ln (real k + 2)) powr (1/3)"
    unfolding sssp_log_factor_one_third_def ..
  also have "\<dots> \<le> (ln (real k + 2)) powr 1"
    by (rule powr_mono[OF _ ge1]) simp
  also have "\<dots> = ln (real k + 2)" by simp
  also have "\<dots> \<le> real k + 1" using ln_le .
  finally have factor_le: "sssp_log_factor_one_third k \<le> real k + 1" .
  have ceil_nonneg: "0 \<le> \<lceil>sssp_log_factor_one_third k\<rceil>"
  proof -
    have "(0::real) \<le> sssp_log_factor_one_third k"
      using sssp_log_factor_one_third_pos[of k] by (rule order_less_imp_le)
    then have "\<lceil>(0::real)\<rceil> \<le> \<lceil>sssp_log_factor_one_third k\<rceil>"
      by (rule ceiling_mono)
    then show ?thesis by simp
  qed
  have "real (sssp_log_one_third_param k) =
      real (nat \<lceil>sssp_log_factor_one_third k\<rceil>)"
    unfolding sssp_log_one_third_param_def ..
  also have "\<dots> = real_of_int \<lceil>sssp_log_factor_one_third k\<rceil>"
    using ceil_nonneg by simp
  also have "\<dots> \<le> real k + 1"
  proof -
    have "\<lceil>sssp_log_factor_one_third k\<rceil> \<le> \<lceil>real k + 1\<rceil>"
      by (rule ceiling_mono[OF factor_le])
    also have "\<dots> = int k + 1" by simp
    finally show ?thesis by simp
  qed
  finally have "real (sssp_log_one_third_param k) \<le> real (Suc k)"
    by simp
  then show "sssp_log_one_third_param k \<le> Suc k"
    by linarith
qed

theorem path_family_not_forced_degenerate:
  "eventually
    (\<lambda>k. \<not> (card (path_k_V k) < sssp_log_one_third_param k)) at_top"
proof -
  have "eventually (\<lambda>k. sssp_log_one_third_param k \<le> Suc k) at_top"
    by (rule sssp_log_one_third_param_le_linear)
  then show ?thesis
    by (auto elim: eventually_mono simp: path_k_card_V)
qed

subsection \<open>Unique shortest walks on the path family\<close>

context fixes k :: nat begin

interpretation pk: finite_weighted_digraph
  "path_k_V k" "path_k_E k" "path_k_weight k" 0
  by (rule path_k_finite_weighted_digraph)

lemma path_k_canonical_walk:
  "j \<le> k \<Longrightarrow> pk.simple_walk_betw 0 [0..<Suc j] j"
proof (induction j)
  case 0
  have "(0::nat) \<in> path_k_V k"
    by (simp add: path_k_V_eq)
  then have "pk.walk [0]" by simp
  then show ?case
    by (simp add: pk.simple_walk_betw_def pk.walk_betw_def)
next
  case (Suc j)
  from Suc.prems have jk: "j \<le> k" and jlt: "j < k" by simp_all
  have ih: "pk.simple_walk_betw 0 [0..<Suc j] j"
    using Suc.IH jk by blast
  have edge: "(j, Suc j) \<in> path_k_E k"
    using jlt by (simp add: path_k_E_iff)
  have fresh: "Suc j \<notin> set [0..<Suc j]" by simp
  have "pk.simple_walk_betw 0 ([0..<Suc j] @ [Suc j]) (Suc j)"
    using pk.simple_walk_snoc[OF ih edge fresh] .
  moreover have "[0..<Suc j] @ [Suc j] = [0..<Suc (Suc j)]"
    by (simp add: upt_Suc_append)
  ultimately show ?case by simp
qed

lemma path_k_all_reachable:
  "v \<in> path_k_V k \<Longrightarrow> pk.reachable 0 v"
proof -
  assume "v \<in> path_k_V k"
  then have "v \<le> k" by (simp add: path_k_V_eq)
  then have "pk.simple_walk_betw 0 [0..<Suc v] v"
    by (rule path_k_canonical_walk)
  then show "pk.reachable 0 v"
    unfolding pk.reachable_def by blast
qed

lemma path_k_simple_walk_unique:
  "pk.simple_walk_betw 0 p j \<Longrightarrow> j \<le> k \<Longrightarrow> p = [0..<Suc j]"
proof (induction j arbitrary: p rule: less_induct)
  case (less j)
  from less.prems have sw: "pk.simple_walk_betw 0 p j" and jk: "j \<le> k"
    by blast+
  from sw have walk_p: "pk.walk p" and ne: "p \<noteq> []" and hd_p: "hd p = 0"
      and last_p: "last p = j" and dist_p: "distinct p"
    unfolding pk.simple_walk_betw_def pk.walk_betw_def by auto
  show ?case
  proof (cases j)
    case 0
    have len1: "length p = 1"
    proof (rule ccontr)
      assume "length p \<noteq> 1"
      from ne have "length p \<ge> 1" by (cases p) auto
      with \<open>length p \<noteq> 1\<close> have len2: "2 \<le> length p" by linarith
      have idx: "Suc (length p - 2) < length p" using len2 by linarith
      have e: "(p ! (length p - 2), p ! Suc (length p - 2)) \<in> path_k_E k"
        using pk.walk_nth_edge[OF walk_p idx] .
      have suceq: "Suc (length p - 2) = length p - 1" using len2 by linarith
      have "p ! (length p - 1) = last p"
        using ne by (simp add: last_conv_nth)
      with last_p 0 have "p ! (length p - 1) = 0" by simp
      with e suceq have "(p ! (length p - 2), 0) \<in> path_k_E k" by simp
      with path_k_no_incoming_0 show False by simp
    qed
    from len1 ne obtain x where "p = [x]" by (cases p) auto
    with hd_p have "p = [0]" by simp
    then show ?thesis using 0 by simp
  next
    case (Suc j')
    have j'k: "j' \<le> k" using jk Suc by simp
    have j'lt: "j' < j" using Suc by simp
    have ne1: "length p \<noteq> 1"
    proof
      assume "length p = 1"
      with ne obtain x where "p = [x]" by (cases p) auto
      with hd_p last_p Suc show False by simp
    qed
    from ne have "length p \<ge> 1" by (cases p) auto
    with ne1 have len2: "2 \<le> length p" by linarith
    have idx: "Suc (length p - 2) < length p" using len2 by linarith
    have e: "(p ! (length p - 2), p ! Suc (length p - 2)) \<in> path_k_E k"
      using pk.walk_nth_edge[OF walk_p idx] .
    have suceq: "Suc (length p - 2) = length p - 1" using len2 by linarith
    have last_nth: "p ! (length p - 1) = Suc j'"
    proof -
      have "p ! (length p - 1) = last p"
        using ne by (simp add: last_conv_nth)
      with last_p Suc show ?thesis by simp
    qed
    from e suceq last_nth
    have edge_last: "(p ! (length p - 2), Suc j') \<in> path_k_E k" by simp
    have nth_n2: "p ! (length p - 2) = j'"
      using edge_last unfolding path_k_incoming_unique by simp
    have idx2: "length p - 2 < length p" using len2 by linarith
    have pref: "pk.simple_walk_betw 0 (take (Suc (length p - 2)) p)
        (p ! (length p - 2))"
      using pk.simple_walk_prefix[OF sw idx2] .
    have pref2: "pk.simple_walk_betw 0 (take (length p - 1) p) j'"
      using pref suceq nth_n2 by simp
    have take_eq: "take (length p - 1) p = [0..<Suc j']"
      using less.IH[OF j'lt pref2 j'k] .
    have pbl: "p = butlast p @ [last p]"
      using append_butlast_last_id[OF ne] by simp
    have bl: "butlast p = take (length p - 1) p"
      by (rule butlast_conv_take)
    have "p = [0..<Suc j'] @ [Suc j']"
      using pbl bl last_p take_eq Suc by simp
    then show ?thesis using Suc by (simp add: upt_Suc_append)
  qed
qed

lemma path_k_unique_shortest_walk:
  "pk.shortest_walk 0 p v \<Longrightarrow> pk.shortest_walk 0 q v \<Longrightarrow> p = q"
proof -
  assume sp: "pk.shortest_walk 0 p v" and sq: "pk.shortest_walk 0 q v"
  have swp: "pk.simple_walk_betw 0 p v"
    using sp unfolding pk.shortest_walk_def by blast
  have swq: "pk.simple_walk_betw 0 q v"
    using sq unfolding pk.shortest_walk_def by blast
  have walk_p: "pk.walk p" and ne_p: "p \<noteq> []" and last_pv: "last p = v"
    using swp unfolding pk.simple_walk_betw_def pk.walk_betw_def by auto
  have v_in: "v \<in> set p"
    using last_in_set[OF ne_p] last_pv by simp
  have "set p \<subseteq> path_k_V k"
    using pk.walk_set_subset[OF walk_p] .
  with v_in have "v \<in> path_k_V k" by blast
  then have vk: "v \<le> k" by (simp add: path_k_V_eq)
  have "p = [0..<Suc v]"
    using path_k_simple_walk_unique[OF swp vk] .
  moreover have "q = [0..<Suc v]"
    using path_k_simple_walk_unique[OF swq vk] .
  ultimately show "p = q" by simp
qed

lemma path_k_bounded_instance:
  "bounded_reduced_positive_instance (path_k_V k) (path_k_E k)
     (path_k_weight k) 0 1"
proof -
  interpret usd: unique_shortest_digraph
    "path_k_V k" "path_k_E k" "path_k_weight k" 0
    by unfold_locales (rule path_k_unique_shortest_walk)
  have outdeg: "usd.edge_outdegree_le 1"
    unfolding usd.edge_outdegree_le_def
  proof
    fix u :: nat
    assume "u \<in> path_k_V k"
    show "card (usd.outgoing_edges {u}) \<le> 1"
    proof (cases "u < k")
      case True
      then have "usd.outgoing_edges {u} = {(u, Suc u)}"
        unfolding usd.outgoing_edges_def by (auto simp: path_k_E_iff)
      then show ?thesis by simp
    next
      case False
      then have "usd.outgoing_edges {u} = {}"
        unfolding usd.outgoing_edges_def by (auto simp: path_k_E_iff)
      then show ?thesis by simp
    qed
  qed
  show ?thesis
  proof
    show "\<And>u v. (u, v) \<in> path_k_E k \<Longrightarrow> 0 < path_k_weight k u v"
      by (rule path_k_positive_weight)
    show "\<And>v. v \<in> path_k_V k \<Longrightarrow> pk.reachable 0 v"
      by (rule path_k_all_reachable)
    show "usd.edge_outdegree_le 1"
      by (rule outdeg)
  qed
qed

interpretation bpi: bounded_reduced_positive_instance
  "path_k_V k" "path_k_E k" "path_k_weight k" 0 1
  by (rule path_k_bounded_instance)

lemma path_k_charged_top_level_cost_exists_if_root_run:
  assumes root:
      "\<exists>d' U c.
        bpi.charged_direct_insert_costed_bmssp (Suc 0)
          (bmssp_level_cap (sssp_log_one_third_param k)
            (sssp_log_two_thirds_param k))
          (sssp_log_two_thirds_param k) (sssp_log_one_third_param k)
          (sssp_log_one_third_param k)
          (bmssp_level_cap (sssp_log_one_third_param k)
            (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
          (sssp_log_one_third_param k)
          pk.finite_initial_label {0} Infinity d' Infinity U c"
  shows "\<exists>c. strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
    (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k c"
proof -
  let ?p = "sssp_log_one_third_param k"
  let ?q = "sssp_log_two_thirds_param k"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  show ?thesis
    using root
    unfolding bpi.charged_direct_insert_top_level_cost_def
      bpi.charged_direct_insert_top_level_run_def
    by (auto simp: Let_def)
qed

lemma path_k_charged_root_run_exists_if_initial_loop:
  assumes loop:
      "\<exists>d' a betas bs charged_Us child_outputs U_loop c_loop
          child_costs_loop c_insert.
        bpi.charged_direct_insert_costed_partition_loop_state
          (Suc 0)
          (bmssp_level_cap (sssp_log_one_third_param k)
            (sssp_log_two_thirds_param k))
          (sssp_log_two_thirds_param k) (sssp_log_one_third_param k)
          (sssp_log_one_third_param k)
          (bmssp_level_cap (sssp_log_one_third_param k)
            (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
          (sssp_log_one_third_param k - 1)
          (bpi.find_pivots_label_capped (sssp_log_one_third_param k)
            (bmssp_level_cap (sssp_log_one_third_param k)
              (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
            pk.finite_initial_label {0} Infinity)
          (bpi.find_pivots_pivots_capped (sssp_log_one_third_param k)
            (bmssp_level_cap (sssp_log_one_third_param k)
              (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
            pk.finite_initial_label {0} Infinity)
          Infinity d'
          (bpi.label_partition_view
            (bpi.find_pivots_label_capped (sssp_log_one_third_param k)
              (bmssp_level_cap (sssp_log_one_third_param k)
                (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
              pk.finite_initial_label {0} Infinity)
            (bpi.find_pivots_pivots_capped (sssp_log_one_third_param k)
              (bmssp_level_cap (sssp_log_one_third_param k)
                (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
              pk.finite_initial_label {0} Infinity))
          a betas bs Infinity charged_Us child_outputs U_loop c_loop
          child_costs_loop \<and>
        pk.complete_on d'
          {v \<in> pk.bound_tree {0} Infinity.
            bpi.find_pivots_label_capped (sssp_log_one_third_param k)
              (bmssp_level_cap (sssp_log_one_third_param k)
                (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
              pk.finite_initial_label {0} Infinity v = pk.dist 0 v} \<and>
        bpi.partition_initial_insert_cost_bound c_insert
          (sssp_log_two_thirds_param k)
          (bpi.find_pivots_pivots_capped (sssp_log_one_third_param k)
            (bmssp_level_cap (sssp_log_one_third_param k)
              (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
            pk.finite_initial_label {0} Infinity)"
  shows "\<exists>d' U c.
    bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap (sssp_log_one_third_param k)
        (sssp_log_two_thirds_param k))
      (sssp_log_two_thirds_param k) (sssp_log_one_third_param k)
      (sssp_log_one_third_param k)
      (bmssp_level_cap (sssp_log_one_third_param k)
        (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
      (sssp_log_one_third_param k)
      pk.finite_initial_label {0} Infinity d' Infinity U c"
proof -
  let ?p = "sssp_log_one_third_param k"
  let ?q = "sssp_log_two_thirds_param k"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  have root_suc:
    "\<exists>d' U c.
      bpi.charged_direct_insert_costed_bmssp (Suc 0)
        (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap (Suc (?p - 1))
        pk.finite_initial_label {0} Infinity d' Infinity U c"
    by (rule bpi.charged_direct_insert_costed_bmssp_Suc_exists_from_initial_loop_at_bound_with_insert)
      (rule loop)
  then show ?thesis
    using sssp_log_one_third_param_pos[of k] by simp
qed

lemma path_k_charged_top_level_cost_exists_if_initial_loop:
  assumes loop:
      "\<exists>d' a betas bs charged_Us child_outputs U_loop c_loop
          child_costs_loop c_insert.
        bpi.charged_direct_insert_costed_partition_loop_state
          (Suc 0)
          (bmssp_level_cap (sssp_log_one_third_param k)
            (sssp_log_two_thirds_param k))
          (sssp_log_two_thirds_param k) (sssp_log_one_third_param k)
          (sssp_log_one_third_param k)
          (bmssp_level_cap (sssp_log_one_third_param k)
            (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
          (sssp_log_one_third_param k - 1)
          (bpi.find_pivots_label_capped (sssp_log_one_third_param k)
            (bmssp_level_cap (sssp_log_one_third_param k)
              (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
            pk.finite_initial_label {0} Infinity)
          (bpi.find_pivots_pivots_capped (sssp_log_one_third_param k)
            (bmssp_level_cap (sssp_log_one_third_param k)
              (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
            pk.finite_initial_label {0} Infinity)
          Infinity d'
          (bpi.label_partition_view
            (bpi.find_pivots_label_capped (sssp_log_one_third_param k)
              (bmssp_level_cap (sssp_log_one_third_param k)
                (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
              pk.finite_initial_label {0} Infinity)
            (bpi.find_pivots_pivots_capped (sssp_log_one_third_param k)
              (bmssp_level_cap (sssp_log_one_third_param k)
                (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
              pk.finite_initial_label {0} Infinity))
          a betas bs Infinity charged_Us child_outputs U_loop c_loop
          child_costs_loop \<and>
        pk.complete_on d'
          {v \<in> pk.bound_tree {0} Infinity.
            bpi.find_pivots_label_capped (sssp_log_one_third_param k)
              (bmssp_level_cap (sssp_log_one_third_param k)
                (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
              pk.finite_initial_label {0} Infinity v = pk.dist 0 v} \<and>
        bpi.partition_initial_insert_cost_bound c_insert
          (sssp_log_two_thirds_param k)
          (bpi.find_pivots_pivots_capped (sssp_log_one_third_param k)
            (bmssp_level_cap (sssp_log_one_third_param k)
              (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
            pk.finite_initial_label {0} Infinity)"
  shows "\<exists>c. strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
    (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k c"
proof -
  have root:
    "\<exists>d' U c.
      bpi.charged_direct_insert_costed_bmssp (Suc 0)
        (bmssp_level_cap (sssp_log_one_third_param k)
          (sssp_log_two_thirds_param k))
        (sssp_log_two_thirds_param k) (sssp_log_one_third_param k)
        (sssp_log_one_third_param k)
        (bmssp_level_cap (sssp_log_one_third_param k)
          (sssp_log_two_thirds_param k) (sssp_log_one_third_param k))
        (sssp_log_one_third_param k)
        pk.finite_initial_label {0} Infinity d' Infinity U c"
    by (rule path_k_charged_root_run_exists_if_initial_loop[OF loop])
  show ?thesis
    by (rule path_k_charged_top_level_cost_exists_if_root_run[OF root])
qed

end

subsection \<open>The exact-concrete algorithm-level running-time bound\<close>

text \<open>
  Unlike the unconditional floor @{thm [source] path_size_cost_bigo_size},
  which bounds the closed cost expression with the graph cardinalities
  substituted, this theorem bounds the least exact-concrete top-level cost
  @{term path_T_bmssp}.  Its hypothesis is intentionally explicit: for all but
  finitely many \<open>k\<close>, at least one exact-concrete top-level run must exist on
  \<open>P\<^sub>k\<close>.  The separate totality-obstruction theory shows that this hypothesis
  is not dischargeable for the exact-concrete relation on this family; the
  theorem is therefore retained as a conditional comparison result, not as a
  non-vacuous algorithm-level claim.
\<close>

definition path_T_bmssp :: "nat \<Rightarrow> nat" where
  "path_T_bmssp k = strict_tie_breaking_digraph.T_bmssp
     (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k"

theorem eventually_path_family_charged_direct_insert_top_level_cost_if_source_pivot_finishes:
  assumes source_pivot_finishes:
    "eventually
      (\<lambda>k. strict_tie_breaking_digraph.charged_direct_insert_source_pivot_finishes
        (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k) at_top"
  shows "eventually
    (\<lambda>k. \<exists>c. strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
      (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k c) at_top"
  using source_pivot_finishes
proof eventually_elim
  case (elim k)
  interpret bpi: bounded_reduced_positive_instance
    "path_k_V k" "path_k_E k" "path_k_weight k" 0 1
    by (rule path_k_bounded_instance)
  have "bpi.charged_direct_insert_source_pivot_finishes 1 k"
    using elim .
  then show ?case
    by (rule bpi.charged_direct_insert_top_level_cost_exists_if_source_pivot_finishes_pred)
qed

theorem bmssp_path_family_runtime_bigo_size:
  assumes runs_exist:
    "eventually (\<lambda>k. \<exists>c. strict_tie_breaking_digraph.exact_concrete_top_level_cost
        (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k c) at_top"
  shows "(\<lambda>k. real (path_T_bmssp k))
     \<in> O(\<lambda>k. real k * (ln (real k + 2)) powr (2 / 3))"
proof -
  have "(\<lambda>k. real (path_T_bmssp k))
      \<in> O(\<lambda>k. sssp_time_target (\<lambda>k. k) k)"
  proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_slack
      [where D = 1 and Cn = 2 and Cm = 1
        and v = "\<lambda>k. Suc k" and m' = "\<lambda>k. k" and m = "\<lambda>k. k"])
    show "0 < (2 :: real)" by simp
    show "0 < (1 :: real)" by simp
    show "eventually (\<lambda>k. real (Suc k) \<le> 2 * real k) at_top"
      by (rule eventually_at_top_linorderI[of 1]) simp
    show "eventually (\<lambda>k. real k \<le> 1 * real k) at_top"
      by simp
    show "eventually
        (\<lambda>k. path_T_bmssp k \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>_. Suc 1 * sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_two_thirds_param k)
            (\<lambda>_. sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_two_thirds_param k)
            (\<lambda>_. k) (Suc k)) at_top"
      using runs_exist
    proof eventually_elim
      case (elim k)
      then obtain c where cost:
        "strict_tie_breaking_digraph.exact_concrete_top_level_cost
           (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k c"
        by blast
      interpret bpi: bounded_reduced_positive_instance
        "path_k_V k" "path_k_E k" "path_k_weight k" 0 1
        by (rule path_k_bounded_instance)
      have cost': "bpi.exact_concrete_top_level_cost 1 k c"
        using cost .
      have key: "bpi.T_bmssp 1 k \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>_. Suc 1 * sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_two_thirds_param k)
            (\<lambda>_. sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_two_thirds_param k)
            (\<lambda>_. bpi.edge_count) bpi.vertex_count"
        by (rule bpi.T_bmssp_refined_bound_log_params_fixed_degree
          [OF bpi.all_vertices_reachable bpi.bounded_edge_outdegree cost'])
      have ec: "bpi.edge_count = k"
        by (simp add: bpi.edge_count_def path_k_card_E)
      have vc: "bpi.vertex_count = Suc k"
        by (simp add: bpi.vertex_count_def path_k_card_V)
      have tb: "bpi.T_bmssp 1 k = path_T_bmssp k"
        by (simp add: path_T_bmssp_def)
      show ?case
        using key[unfolded ec vc] tb by simp
    qed
  qed
  then show ?thesis
    unfolding sssp_time_target_def sssp_log_factor_def by simp
qed

subsection \<open>A charged path-family theorem waiting on charged cost bounds\<close>

text \<open>
  The charged direct-insert top-level relation is the intended successor for
  the path-family integration.  On this branch we can already state and check
  the exact conditional bridge needed by downstream JAR-facing documentation:
  if charged top-level runs eventually exist on \<open>P\<^sub>k\<close> and every such charged
  cost is bounded by the same refined graph-time expression, then the least
  charged cost has the size-parametric target.  The second assumption is the
  charged analogue of the refined-bound theorem still expected from the runtime
  proof branch.
\<close>

definition path_charged_direct_insert_time :: "nat \<Rightarrow> nat" where
  "path_charged_direct_insert_time k =
     strict_tie_breaking_digraph.charged_direct_insert_top_level_time
       (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k"

theorem bmssp_path_family_charged_direct_insert_runtime_bigo_size_if_cost_bounded:
  assumes charged_runs_exist:
    "eventually
      (\<lambda>k. \<exists>c.
        strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
          (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k c) at_top"
    and charged_cost_bound:
    "eventually
      (\<lambda>k. \<forall>c.
        strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
          (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k c \<longrightarrow>
        c \<le> bmssp_refined_graph_time_bound
          (\<lambda>_. Suc 1 * sssp_log_one_third_param k)
          (\<lambda>_. sssp_log_two_thirds_param k)
          (\<lambda>_. sssp_log_one_third_param k)
          (\<lambda>_. sssp_log_one_third_param k)
          (\<lambda>_. sssp_log_two_thirds_param k)
          (\<lambda>_. k) (Suc k)) at_top"
  shows "(\<lambda>k. real (path_charged_direct_insert_time k))
     \<in> O(\<lambda>k. real k * (ln (real k + 2)) powr (2 / 3))"
proof -
  have "(\<lambda>k. real (path_charged_direct_insert_time k))
      \<in> O(\<lambda>k. sssp_time_target (\<lambda>k. k) k)"
  proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_slack
      [where D = 1 and Cn = 2 and Cm = 1
        and v = "\<lambda>k. Suc k" and m' = "\<lambda>k. k" and m = "\<lambda>k. k"])
    show "0 < (2 :: real)" by simp
    show "0 < (1 :: real)" by simp
    show "eventually (\<lambda>k. real (Suc k) \<le> 2 * real k) at_top"
      by (rule eventually_at_top_linorderI[of 1]) simp
    show "eventually (\<lambda>k. real k \<le> 1 * real k) at_top"
      by simp
    show "eventually
        (\<lambda>k. path_charged_direct_insert_time k \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>_. Suc 1 * sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_two_thirds_param k)
            (\<lambda>_. sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_one_third_param k)
            (\<lambda>_. sssp_log_two_thirds_param k)
            (\<lambda>_. k) (Suc k)) at_top"
      using charged_runs_exist charged_cost_bound
    proof eventually_elim
      case (elim k)
      then obtain c where cost:
        "strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
           (path_k_V k) (path_k_E k) (path_k_weight k) 0 1 k c"
        by blast
      interpret bpi: bounded_reduced_positive_instance
        "path_k_V k" "path_k_E k" "path_k_weight k" 0 1
        by (rule path_k_bounded_instance)
      have cost': "bpi.charged_direct_insert_top_level_cost 1 k c"
        using cost .
      have time_le_c: "bpi.charged_direct_insert_top_level_time 1 k \<le> c"
        unfolding bpi.charged_direct_insert_top_level_time_def
        by (rule Least_le) (rule cost')
      have c_le:
        "c \<le> bmssp_refined_graph_time_bound
          (\<lambda>_. Suc 1 * sssp_log_one_third_param k)
          (\<lambda>_. sssp_log_two_thirds_param k)
          (\<lambda>_. sssp_log_one_third_param k)
          (\<lambda>_. sssp_log_one_third_param k)
          (\<lambda>_. sssp_log_two_thirds_param k)
          (\<lambda>_. k) (Suc k)"
        using elim(2) cost by blast
      have tb:
        "bpi.charged_direct_insert_top_level_time 1 k =
          path_charged_direct_insert_time k"
        by (simp add: path_charged_direct_insert_time_def)
      show ?case
        using time_le_c c_le tb by linarith
    qed
  qed
  then show ?thesis
    unfolding sssp_time_target_def sssp_log_factor_def by simp
qed

end
