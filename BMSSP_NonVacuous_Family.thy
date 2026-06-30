theory BMSSP_NonVacuous_Family
  imports BMSSP_Path_Family BMSSP_Cost_Totality
begin

section \<open>An unconditional, non-vacuous size-parametric BMSSP running-time bound\<close>

text \<open>
  The conditional charged headline
  @{thm [source] bmssp_path_family_charged_direct_insert_runtime_bigo_size_if_cost_bounded}
  runs the path \<open>P\<^sub>k\<close> at the \<^emph>\<open>same\<close> index \<open>k\<close> that also fixes the internal
  logarithmic schedule.  On that diagonal the top-level bucket cap
  \<open>cap k = p k \<cdot> 2\<^bsup>p k \<cdot> q k\<^esup>\<close> with \<open>p k = sssp_log_one_third_param k\<close> and
  \<open>q k = sssp_log_two_thirds_param k\<close> is sublinear in \<open>k\<close>, so it eventually
  fails to cover the \<open>k + 1\<close> path vertices and no charged top-level run can
  exist --- the diagonal family is vacuous.

  This theory \<^emph>\<open>decouples\<close> the graph size from the schedule index: it keeps the
  genuine growing graph \<open>P\<^sub>n\<close> (with \<open>card (path_k_V n) = Suc n \<rightarrow> \<infinity>\<close>)
  but runs it at the \<^emph>\<open>inflated\<close> schedule index \<open>n \<cdot> n\<close>.  Because
  \<open>cap (n \<cdot> n) \<ge> (n\<^sup>2 + 2)\<^bsup>ln 2\<^esup> \<ge> n\<^bsup>2 ln 2\<^esup>\<close> and \<open>2 ln 2 > 1\<close>, the cap now
  covers the path for all but finitely many \<open>n\<close>, while \<open>ln (n \<cdot> n) = 2 ln n\<close>
  keeps the schedule polylog in \<open>\<Theta>(ln n)\<close>.  This is milestone \textbf{B0}: the
  arithmetic that de-risks the whole construction.
\<close>

subsection \<open>Elementary analytic facts\<close>

text \<open>A power with exponent \<open>> 1\<close> eventually dominates the successor function.\<close>

lemma real_Suc_le_powr_eventually:
  fixes c :: real
  assumes c1: "1 < c"
  shows "eventually (\<lambda>n::nat. real (Suc n) \<le> (real n) powr c) at_top"
proof -
  have cpos: "0 < c - 1"
    using c1 by simp
  have ln_top: "filterlim (\<lambda>n::nat. ln (real n)) at_top at_top"
    by (rule filterlim_compose[OF ln_at_top filterlim_real_sequentially])
  have ev_ln: "eventually (\<lambda>n::nat. ln 2 / (c - 1) \<le> ln (real n)) at_top"
    using ln_top unfolding filterlim_at_top by blast
  have ev_n: "eventually (\<lambda>n::nat. (1::nat) \<le> n) at_top"
    by (rule eventually_ge_at_top)
  from ev_ln ev_n show ?thesis
  proof eventually_elim
    case (elim n)
    have n1: "1 \<le> real n"
      using elim(2) by simp
    have npos: "0 < real n"
      using n1 by simp
    have two_le: "(2::real) \<le> (real n) powr (c - 1)"
    proof -
      have le1: "ln 2 \<le> (c - 1) * ln (real n)"
      proof -
        have "ln 2 = (c - 1) * (ln 2 / (c - 1))"
          using cpos by simp
        also have "\<dots> \<le> (c - 1) * ln (real n)"
          using elim(1) cpos by (intro mult_left_mono) auto
        finally show ?thesis .
      qed
      have ex: "(2::real) \<le> exp ((c - 1) * ln (real n))"
      proof -
        have "exp (ln (2::real)) \<le> exp ((c - 1) * ln (real n))"
          using le1 by (simp only: exp_le_cancel_iff)
        thus ?thesis by simp
      qed
      have "(real n) powr (c - 1) = exp ((c - 1) * ln (real n))"
        using npos by (simp add: powr_def)
      with ex show ?thesis by simp
    qed
    have key: "(real n) powr c = real n * (real n) powr (c - 1)"
    proof -
      have "(real n) powr c = (real n) powr (1 + (c - 1))"
        by simp
      also have "\<dots> = (real n) powr 1 * (real n) powr (c - 1)"
        by (rule powr_add)
      also have "\<dots> = real n * (real n) powr (c - 1)"
        by (simp add: powr_one n1)
      finally show ?thesis .
    qed
    have sucle: "real (Suc n) \<le> real n * 2"
    proof -
      have "real (Suc n) = real n + 1"
        by simp
      thus ?thesis using n1 by linarith
    qed
    have "real (Suc n) \<le> real n * 2"
      by (rule sucle)
    also have "\<dots> \<le> real n * (real n) powr (c - 1)"
      by (rule mult_left_mono[OF two_le]) (simp add: npos)
    also have "\<dots> = (real n) powr c"
      by (simp add: key)
    finally show ?case .
  qed
qed

text \<open>The slope \<open>2 ln 2\<close> obtained from squaring the schedule exceeds \<open>1\<close>.\<close>

lemma one_less_two_ln_two: "1 < 2 * ln (2::real)"
proof -
  have exp_half_lt: "exp (1 / 2 :: real) < 2"
  proof (rule power_less_imp_less_base[where n = 2])
    have "(exp (1 / 2 :: real)) ^ 2 = exp 1"
      by (simp add: power2_eq_square flip: exp_add)
    also have "\<dots> \<le> 3"
      by (rule exp_le)
    also have "\<dots> < 2 ^ 2"
      by simp
    finally show "(exp (1 / 2 :: real)) ^ 2 < 2 ^ 2" .
    show "0 \<le> (2::real)"
      by simp
  qed
  have "exp (1 / 2 :: real) < exp (ln 2)"
    using exp_half_lt by simp
  then have "1 / 2 < ln (2::real)"
    by (simp only: exp_less_cancel_iff)
  then show ?thesis
    by simp
qed

subsection \<open>A reusable ``the source is the sole pivot'' brick\<close>

text \<open>
  The dual of @{thm [source]
  unique_shortest_digraph.find_pivots_pivots_capped_singleton_empty_if_params_exceed_vertex_count}:
  when the capped scan does \<^emph>\<open>not\<close> overflow and the source's own tree slice
  already holds at least @{term k} seen vertices, the singleton FindPivots call
  returns exactly the source.  This is the @{term "P = {s}"} half of the
  source-pivot witness, and it is precisely the regime of the decoupled path
  family: the cap covers the path, yet the source subtree is large.
\<close>

context unique_shortest_digraph
begin

lemma find_pivots_pivots_capped_singleton_source_if_large_tree:
  assumes no_overflow: "card (find_pivots_seen_capped k cap d {s} B) \<le> cap"
    and large: "k \<le> card (tree_of s \<inter> find_pivots_seen_capped k cap d {s} B)"
  shows "find_pivots_pivots_capped k cap d {s} B = {s}"
proof -
  let ?seen = "find_pivots_seen_capped k cap d {s} B"
  have no_overflow': "\<not> card ?seen > cap"
    using no_overflow by simp
  have qualifies: "{u \<in> {s}. k \<le> card (tree_of u \<inter> ?seen)} = {s}"
    using large by auto
  show ?thesis
    unfolding find_pivots_pivots_capped_def
    using no_overflow' qualifies by simp
qed

text \<open>
  The source's shortest-path tree is exactly its reachable set: the source is the
  head of every shortest walk, hence lies on every shortest path.  Combined with
  the FindPivots brick this turns the @{term "P = {s}"} obligation on the path
  family into a pure cardinality count of the capped scan.
\<close>

lemma tree_path_source_iff_reachable:
  "tree_path s v \<longleftrightarrow> reachable s v"
proof
  assume "tree_path s v"
  thus "reachable s v"
    by (rule tree_pathD)
next
  assume r: "reachable s v"
  have "shortest_walk s (shortest_path_to v) v"
    by (rule shortest_path_to_shortest[OF r])
  then have "walk_betw s (shortest_path_to v) v"
    unfolding shortest_walk_def simple_walk_betw_def by simp
  then have ne: "shortest_path_to v \<noteq> []"
    and hd: "hd (shortest_path_to v) = s"
    unfolding walk_betw_def by auto
  have mem: "s \<in> set (shortest_path_to v)"
    using ne hd by (metis hd_in_set)
  show "tree_path s v"
    by (rule tree_pathI[OF r mem])
qed

lemma tree_of_source_eq:
  "tree_of s = {v \<in> V. reachable s v}"
  unfolding tree_of_def by (simp add: tree_path_source_iff_reachable)

text \<open>
  \<^bold>\<open>Generic per-round bound on the capped FindPivots scan cost.\<close>  Each round of
  @{const fp_iter_capped_scan_cost} contributes @{term "card (outgoing_edges F)"}
  for the current frontier @{term F}, and every frontier's outgoing-edge set is a
  subset of the whole edge set, so each round costs at most @{const edge_count}.
  Hence the @{term n}-round scan costs at most @{term "n * edge_count"}, uniformly
  in the schedule arguments.  This is the only handle we need on the FindPivots
  cost: the cheap charged top-level run on the path family pays exactly one such
  scan per recursion level (all four partition costs being zero), so its whole
  cost is a sum of these scans plus a single base-case scan.
\<close>

lemma fp_iter_capped_scan_cost_le_rounds:
  "fp_iter_capped_scan_cost n cap d F W B \<le> n * edge_count"
proof (induction n arbitrary: d F W)
  case 0
  show ?case by simp
next
  case (Suc n)
  have round_le: "card (outgoing_edges F) \<le> edge_count"
    by (rule edge_count_outgoing_bound)
  have tail_le:
    "(if card (W \<union> fp_next d F B) > cap then 0
      else fp_iter_capped_scan_cost n cap (relax_frontier d F) (fp_next d F B)
             (W \<union> fp_next d F B) B) \<le> n * edge_count"
  proof (cases "card (W \<union> fp_next d F B) > cap")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using Suc.IH by simp
  qed
  have "fp_iter_capped_scan_cost (Suc n) cap d F W B
      = card (outgoing_edges F)
        + (if card (W \<union> fp_next d F B) > cap then 0
           else fp_iter_capped_scan_cost n cap (relax_frontier d F) (fp_next d F B)
                  (W \<union> fp_next d F B) B)"
    by (simp add: Let_def)
  also have "\<dots> \<le> edge_count + n * edge_count"
    using round_le tail_le by linarith
  also have "\<dots> = Suc n * edge_count" by simp
  finally show ?case .
qed

end

subsection \<open>The genuine shortest-path distance on the path family\<close>

text \<open>
  The unit-weight path \<open>P\<^sub>k\<close> has the identity distance \<open>dist 0 v = v\<close>: the
  canonical walk \<open>0 \<rightarrow> 1 \<rightarrow> \<dots> \<rightarrow> v\<close> is the unique simple walk to \<open>v\<close>
  (@{thm [source] path_k_simple_walk_unique}) and carries \<open>v\<close> unit edges.  This
  is the keystone distance fact underlying every later path-tree, bound-tree and
  FindPivots characterisation on the decoupled family.
\<close>

subsection \<open>A schedule that dominates the path size (non-vacuous regime)\<close>

text \<open>
  For the genuinely non-vacuous result we run the growing path \<open>P\<^sub>k\<close> at a schedule
  \<open>\<sigma> k\<close> chosen so that the FindPivots round count \<open>p = sssp_log_one_third_param (\<sigma> k)\<close>
  strictly exceeds the \<^term>\<open>Suc k\<close> path vertices.  Such a schedule exists because
  \<open>sssp_log_one_third_param\<close> diverges (@{thm [source] sssp_log_one_third_param_at_top}).
  In this regime the top pivots are empty and a charged top-level run exists
  unconditionally, while \<open>card (path_k_V k) = Suc k \<rightarrow> \<infinity>\<close>.\<close>

definition path_sched :: "nat \<Rightarrow> nat" where
  "path_sched k = (LEAST N. Suc k < sssp_log_one_third_param N)"

lemma path_sched_param_gt:
  "Suc k < sssp_log_one_third_param (path_sched k)"
proof -
  have "\<exists>N. Suc k < sssp_log_one_third_param N"
  proof -
    have "eventually (\<lambda>N. Suc (Suc k) \<le> sssp_log_one_third_param N) at_top"
      using sssp_log_one_third_param_at_top unfolding filterlim_at_top by blast
    then obtain N where N: "Suc (Suc k) \<le> sssp_log_one_third_param N"
      by (meson eventually_at_top_linorder order_refl)
    have "Suc k < sssp_log_one_third_param N" using N by linarith
    then show ?thesis by blast
  qed
  then show ?thesis
    unfolding path_sched_def by (rule LeastI_ex)
qed

context fixes k :: nat
begin

interpretation pk: finite_weighted_digraph
  "path_k_V k" "path_k_E k" "path_k_weight k" 0
  by (rule path_k_finite_weighted_digraph)

lemma path_k_walk_weight_upt:
  "a + j \<le> k \<Longrightarrow> pk.walk_weight [a..<Suc (a + j)] = real j"
proof (induction j arbitrary: a)
  case 0
  have "[a..<Suc (a + 0)] = [a]" by simp
  then show ?case by simp
next
  case (Suc j)
  have alt: "a < k" using Suc.prems by simp
  have w1: "path_k_weight k a (Suc a) = 1"
    using alt by (simp add: path_k_weight_def path_k_E_iff)
  have dec1: "[a..<Suc (a + Suc j)] = a # [Suc a..<Suc (a + Suc j)]"
    by (simp add: upt_conv_Cons)
  have dec2: "[Suc a..<Suc (a + Suc j)] = Suc a # [Suc (Suc a)..<Suc (a + Suc j)]"
    by (simp add: upt_conv_Cons)
  have ih: "pk.walk_weight [Suc a..<Suc (Suc a + j)] = real j"
    using Suc.IH[of "Suc a"] Suc.prems by simp
  have step: "pk.walk_weight (Suc a # [Suc (Suc a)..<Suc (a + Suc j)]) = real j"
    using dec2 ih by simp
  have "pk.walk_weight [a..<Suc (a + Suc j)]
      = pk.walk_weight (a # Suc a # [Suc (Suc a)..<Suc (a + Suc j)])"
    using dec1 dec2 by simp
  also have "\<dots> = path_k_weight k a (Suc a)
      + pk.walk_weight (Suc a # [Suc (Suc a)..<Suc (a + Suc j)])"
    by simp
  also have "\<dots> = 1 + real j"
    using w1 step by simp
  finally show ?case by simp
qed

lemma path_k_dist_eq:
  assumes "v \<le> k"
  shows "pk.dist 0 v = real v"
proof -
  have canon: "pk.simple_walk_betw 0 [0..<Suc v] v"
    using assms by (rule path_k_canonical_walk)
  have uniq: "{p. pk.simple_walk_betw 0 p v} = {[0..<Suc v]}"
  proof
    show "{p. pk.simple_walk_betw 0 p v} \<subseteq> {[0..<Suc v]}"
    proof
      fix p
      assume "p \<in> {p. pk.simple_walk_betw 0 p v}"
      then have "pk.simple_walk_betw 0 p v" by simp
      from path_k_simple_walk_unique[OF this assms]
      show "p \<in> {[0..<Suc v]}" by simp
    qed
    show "{[0..<Suc v]} \<subseteq> {p. pk.simple_walk_betw 0 p v}"
      using canon by simp
  qed
  have ww: "pk.walk_weight [0..<Suc v] = real v"
  proof -
    have hk: "0 + v \<le> k" using assms by simp
    show ?thesis
      using path_k_walk_weight_upt[OF hk] by (simp only: add_0_left)
  qed
  have "pk.simple_walk_weights 0 v = {real v}"
    unfolding pk.simple_walk_weights_def using uniq ww by simp
  then show ?thesis
    unfolding pk.dist_def by simp
qed

interpretation bpi: bounded_reduced_positive_instance
  "path_k_V k" "path_k_E k" "path_k_weight k" 0 1
  by (rule path_k_bounded_instance)

text \<open>
  The source's shortest-path tree is the whole path: every path vertex is
  reachable from \<open>0\<close>, and \<open>0\<close> heads every shortest walk.  Hence the
  source-tree slice in the FindPivots count is the entire vertex set.
\<close>

lemma path_k_tree_of_source:
  "bpi.tree_of 0 = path_k_V k"
proof -
  have "bpi.tree_of 0 = {v \<in> path_k_V k. pk.reachable 0 v}"
    by (rule bpi.tree_of_source_eq)
  also have "\<dots> = path_k_V k"
    using path_k_all_reachable by auto
  finally show ?thesis .
qed

text \<open>
  The capped FindPivots scan stays inside the graph, so its seen set never
  exceeds the @{term "Suc k"} path vertices.  This discharges the no-overflow
  half of the singleton source-pivot brick whenever the cap covers the path,
  i.e.\ eventually at the inflated schedule (see the cap-domination theorem
  below).
\<close>

lemma path_k_find_pivots_seen_card_le:
  "card (bpi.find_pivots_seen_capped K cap d {0} Infinity) \<le> Suc k"
proof -
  have s0: "{0} \<subseteq> path_k_V k"
    by (simp add: path_k_V_eq)
  have "bpi.find_pivots_seen_capped K cap d {0} Infinity \<subseteq> path_k_V k"
    unfolding bpi.find_pivots_seen_capped_def
    by (rule bpi.fp_iter_capped_seen_subset_V[OF s0 s0])
  then have "card (bpi.find_pivots_seen_capped K cap d {0} Infinity)
      \<le> card (path_k_V k)"
    by (rule card_mono[OF path_k_finite_V])
  then show ?thesis
    by (simp add: path_k_card_V)
qed

text \<open>
  \<^bold>\<open>Empty top pivots when the schedule dominates the path.\<close>  If the FindPivots
  round count \<open>K\<close> already strictly exceeds the \<^term>\<open>Suc k\<close> path vertices (and the
  cap covers the path, so the capped scan does not overflow), then no vertex roots a
  \<open>K\<close>-large source-tree slice --- the whole source tree has only \<^term>\<open>Suc k < K\<close>
  vertices --- so the capped FindPivots call from \<open>{0}\<close> returns the \<^emph>\<open>empty\<close> pivot
  set.  This is the genuinely \<^emph>\<open>non-vacuous\<close> regime: with empty pivots the top-level
  partition loop is immediately Done, so a charged top-level run exists
  unconditionally, with no recourse to the (walled) multi-step band walk.\<close>

lemma path_k_top_pivots_empty:
  assumes Kk: "Suc k < K" and cap: "Suc k \<le> cap"
  shows "bpi.find_pivots_pivots_capped K cap d {0} Infinity = {}"
proof -
  let ?seen = "bpi.find_pivots_seen_capped K cap d {0} Infinity"
  have s0: "{0} \<subseteq> path_k_V k" by (simp add: path_k_V_eq)
  have card_le: "card ?seen \<le> Suc k"
    by (rule path_k_find_pivots_seen_card_le)
  have le_cap: "card ?seen \<le> cap"
    using card_le cap by simp
  have notgt: "\<not> card ?seen > cap"
    using le_cap by simp
  have seen_sub: "?seen \<subseteq> path_k_V k"
    unfolding bpi.find_pivots_seen_capped_def
    by (rule bpi.fp_iter_capped_seen_subset_V[OF s0 s0])
  have inter_eq: "bpi.tree_of 0 \<inter> ?seen = ?seen"
    using seen_sub path_k_tree_of_source by auto
  have card_inter: "card (bpi.tree_of 0 \<inter> ?seen) \<le> Suc k"
    using inter_eq card_le by simp
  have nonqual: "\<not> K \<le> card (bpi.tree_of 0 \<inter> ?seen)"
    using card_inter Kk by linarith
  have qual_empty: "{u \<in> {0}. K \<le> card (bpi.tree_of u \<inter> ?seen)} = {}"
    using nonqual by auto
  show ?thesis
    unfolding bpi.find_pivots_pivots_capped_def
    using notgt qual_empty by simp
qed

text \<open>
  \<^bold>\<open>Non-vacuous run existence (empty-pivots regime).\<close>  Whenever the schedule
  parameter \<open>p = sssp_log_one_third_param N\<close> exceeds the \<^term>\<open>Suc k\<close> path
  vertices, the top pivots are empty (the cap \<open>p \<cdot> 2\<^bsup>p\<cdot>q\<^esup> \<ge> p\<close> covers the path),
  so a charged top-level cost exists by the immediate-Done route
  @{thm [source] bpi.charged_direct_insert_top_level_cost_exists_if_top_pivots_empty}.
  This discharges run-existence unconditionally on the path in the
  schedule-dominates-graph regime, the regime where the BMSSP top-level call
  terminates in a single sweep.\<close>

lemma path_k_charged_cost_exists_if_param_large:
  assumes Kk: "Suc k < sssp_log_one_third_param N"
  shows "\<exists>c. bpi.charged_direct_insert_top_level_cost 1 N c"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  have cap_ge: "Suc k \<le> ?cap"
    using Kk bmssp_level_cap_ge_level[of ?p ?q ?p] by linarith
  have empty: "bpi.find_pivots_pivots_capped ?p ?cap pk.finite_initial_label {0} Infinity = {}"
    by (rule path_k_top_pivots_empty[OF Kk cap_ge])
  show ?thesis
    by (rule bpi.charged_direct_insert_top_level_cost_exists_if_top_pivots_empty[OF empty])
qed

text \<open>
  \<^bold>\<open>Unconditional run existence at the dominating schedule.\<close>  Specialising the
  empty-pivots route at \<open>N = path_sched k\<close> discharges run-existence on \<open>P\<^sub>k\<close> with
  \<^emph>\<open>no\<close> side condition: at this schedule the FindPivots round count exceeds the
  path, so a charged top-level cost always exists.\<close>

lemma path_k_charged_cost_exists_at_path_sched:
  "\<exists>c. bpi.charged_direct_insert_top_level_cost 1 (path_sched k) c"
  by (rule path_k_charged_cost_exists_if_param_large[OF path_sched_param_gt])

text \<open>
  \<^bold>\<open>Unit out-degree and a linear FindPivots scan bound.\<close>  Each path vertex has at
  most one out-edge, so a singleton frontier stays a singleton along the capped
  FindPivots iteration; hence the scan cost is bounded by the round count times the
  frontier size --- here \<^emph>\<open>linearly\<close> in the frontier, with \<^emph>\<open>no\<close> cap factor.  This
  is the per-call ingredient for the genuine \<open>O(\<bar>V\<bar>)\<close> cost of the empty-pivots
  run (the general library bound carries a spurious \<open>cap\<close> factor).\<close>

lemma path_k_outdegree_le: "bpi.outdegree_le 1"
proof (unfold bpi.outdegree_le_def, intro ballI)
  fix u assume "u \<in> path_k_V k"
  have sub: "bpi.out_neighbors {u} \<subseteq> {Suc u}"
    unfolding bpi.out_neighbors_def using path_k_E_iff by auto
  have "card (bpi.out_neighbors {u}) \<le> card {Suc u}"
    by (rule card_mono[OF _ sub]) simp
  then show "card (bpi.out_neighbors {u}) \<le> 1" by simp
qed

lemma path_k_fp_iter_capped_scan_cost_le_card_frontier:
  assumes "F \<subseteq> path_k_V k"
  shows "bpi.fp_iter_capped_scan_cost n cap d F W B \<le> n * card F"
  using assms
proof (induction n arbitrary: d F W)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?F' = "bpi.fp_next d F B"
  let ?W' = "W \<union> ?F'"
  have round_le: "card (bpi.outgoing_edges F) \<le> card F"
    using bpi.card_outgoing_edges_le[OF Suc.prems bpi.bounded_edge_outdegree] by simp
  have F'_le: "card ?F' \<le> card F"
    using bpi.card_fp_next_le[OF Suc.prems path_k_outdegree_le] by simp
  have F'_subset: "?F' \<subseteq> path_k_V k"
    by (rule bpi.fp_next_subset_V)
  show ?case
  proof (cases "card ?W' > cap")
    case True
    have c: "card (bpi.outgoing_edges F) \<le> Suc n * card F"
    proof -
      have "card F \<le> Suc n * card F" by simp
      then show ?thesis using round_le by linarith
    qed
    show ?thesis using True c by (simp add: Let_def)
  next
    case False
    have tail: "bpi.fp_iter_capped_scan_cost n cap (bpi.relax_frontier d F) ?F' ?W' B
        \<le> n * card ?F'"
      by (rule Suc.IH[OF F'_subset])
    have step: "n * card ?F' \<le> n * card F"
      using F'_le by (rule mult_le_mono2)
    have c: "card (bpi.outgoing_edges F)
        + bpi.fp_iter_capped_scan_cost n cap (bpi.relax_frontier d F) ?F' ?W' B
        \<le> Suc n * card F"
    proof -
      have "card (bpi.outgoing_edges F)
          + bpi.fp_iter_capped_scan_cost n cap (bpi.relax_frontier d F) ?F' ?W' B
          \<le> card F + n * card F"
        using round_le tail step by linarith
      then show ?thesis by (simp add: algebra_simps)
    qed
    show ?thesis using False c by (simp add: Let_def)
  qed
qed

text \<open>
  Every prefix vertex \<open>v \<le> K \<le> k\<close> is a short-tight witness for the
  @{term K}-round FindPivots scan from the source: the canonical walk
  \<open>0 \<rightarrow> 1 \<rightarrow> \<dots> \<rightarrow> v\<close> is the (unique) shortest walk to \<open>v\<close>
  (@{thm [source] path_k_canonical_walk}, @{thm [source] path_k_dist_eq}), hence
  successively tight, starts at the complete source, stays below the
  \<^term>\<open>Infinity\<close> bound and uses exactly \<open>v \<le> K\<close> edges.
\<close>

lemma path_k_short_tight_witness_prefix:
  assumes vK: "v \<le> K" and Kk: "K \<le> k"
  shows "bpi.short_tight_witness K pk.finite_initial_label {0} Infinity v"
proof -
  have vk: "v \<le> k" using vK Kk by simp
  have ne: "[0..<Suc v] \<noteq> []" by simp
  have walk: "pk.shortest_walk 0 [0..<Suc v] v"
  proof -
    have sw: "pk.simple_walk_betw 0 [0..<Suc v] v"
      by (rule path_k_canonical_walk[OF vk])
    have ww: "pk.walk_weight [0..<Suc v] = real v"
      using path_k_walk_weight_upt[of 0 v] vk by simp
    have dd: "pk.dist 0 v = real v"
      by (rule path_k_dist_eq[OF vk])
    show ?thesis
      unfolding pk.shortest_walk_def using sw ww dd by simp
  qed
  have tight: "successively pk.tight_edge_step [0..<Suc v]"
    by (rule pk.shortest_walk_successively_tight[OF walk])
  have hd0: "hd [0..<Suc v] = 0"
    using hd_conv_nth[OF ne] by (simp add: nth_upt del: upt_Suc)
  have last_v: "last [0..<Suc v] = v"
    using last_conv_nth[OF ne] by (simp add: nth_upt del: upt_Suc)
  have dlab: "pk.finite_initial_label (hd [0..<Suc v]) = pk.dist 0 (hd [0..<Suc v])"
    using hd0 pk.finite_initial_label_source_complete by simp
  have len: "length (pk.path_edges [0..<Suc v]) \<le> K"
    using bpi.path_edges_length[of "[0..<Suc v]"] vK by simp
  show ?thesis
    unfolding bpi.short_tight_witness_def
  proof (intro exI conjI)
    show "[0..<Suc v] \<noteq> []" by (rule ne)
    show "hd [0..<Suc v] \<in> {0}" using hd0 by simp
    show "last [0..<Suc v] = v" by (rule last_v)
    show "pk.finite_initial_label (hd [0..<Suc v]) = pk.dist 0 (hd [0..<Suc v])"
      by (rule dlab)
    show "successively pk.tight_edge_step [0..<Suc v]" by (rule tight)
    show "\<forall>y\<in>set [0..<Suc v]. below_bound (pk.dist 0 y) Infinity" by simp
    show "length (pk.path_edges [0..<Suc v]) \<le> K" by (rule len)
  qed
qed

text \<open>
  The seen \<^emph>\<open>lower\<close> bound (deliverable (G2) for the \<open>P = {s}\<close> obligation):
  whenever the round count \<open>K\<close> is at most the path length and the cap covers the
  path, the @{term K}-round capped scan from \<open>{0}\<close> reaches at least @{term K}
  vertices.  The prefix \<open>{0..K}\<close> are short-tight witnesses, hence sit inside the
  completed (uncapped) seen set (@{thm [source] bpi.find_pivots_completes_short_vertices});
  the no-overflow regime collapses the capped scan to the uncapped one
  (@{thm [source] bpi.fp_iter_capped_eq_fp_iter_if_final_within_cap}).
\<close>

lemma path_k_seen_card_ge:
  assumes Kk: "K \<le> k" and cover: "Suc k \<le> cap"
  shows "K \<le> card (bpi.find_pivots_seen_capped K cap pk.finite_initial_label {0} Infinity)"
proof -
  let ?d = "pk.finite_initial_label"
  let ?seen_c = "bpi.find_pivots_seen_capped K cap ?d {0} Infinity"
  let ?seen_u = "bpi.find_pivots_seen K ?d {0} Infinity"
  have su: "{0} \<subseteq> path_k_V k" by (simp add: path_k_V_eq)
  have sound: "pk.sound_label pk.finite_initial_label"
    by (rule pk.finite_initial_label_sound[OF path_k_all_reachable])
  have reaches: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have subset_short: "{0..K} \<subseteq> bpi.find_pivots_short_vertices K ?d {0} Infinity"
  proof
    fix v assume "v \<in> {0..K}"
    then have vK: "v \<le> K" by simp
    have vk: "v \<le> k" using vK Kk by simp
    have wit: "bpi.short_tight_witness K ?d {0} Infinity v"
      by (rule path_k_short_tight_witness_prefix[OF vK Kk])
    have vV: "v \<in> path_k_V k" using vk by (simp add: path_k_V_eq)
    show "v \<in> bpi.find_pivots_short_vertices K ?d {0} Infinity"
      unfolding bpi.find_pivots_short_vertices_def using vV wit by simp
  qed
  have short_sub_seen: "bpi.find_pivots_short_vertices K ?d {0} Infinity \<subseteq> ?seen_u"
    using bpi.find_pivots_completes_short_vertices[OF sound reaches]
    by blast
  have subset_seen: "{0..K} \<subseteq> ?seen_u"
    using subset_short short_sub_seen by blast
  have seen_u_sub: "?seen_u \<subseteq> path_k_V k"
    unfolding bpi.find_pivots_seen_def
    by (rule bpi.fp_iter_seen_subset_V[OF su su])
  have fin_u: "finite ?seen_u"
    using seen_u_sub path_k_finite_V by (rule finite_subset)
  have card_u_ge: "K + 1 \<le> card ?seen_u"
  proof -
    have "card {0..K} \<le> card ?seen_u"
      by (rule card_mono[OF fin_u subset_seen])
    then show ?thesis by simp
  qed
  have card_c_le_cap: "card ?seen_c \<le> cap"
  proof -
    have "card ?seen_c \<le> Suc k" by (rule path_k_find_pivots_seen_card_le)
    then show ?thesis using cover by simp
  qed
  have eq_seen: "?seen_c = ?seen_u"
  proof -
    have le: "card (bpi.fp_seen (bpi.fp_iter_capped K cap ?d {0} {0} Infinity)) \<le> cap"
      using card_c_le_cap unfolding bpi.find_pivots_seen_capped_def .
    have "bpi.fp_iter_capped K cap ?d {0} {0} Infinity
        = bpi.fp_iter K ?d {0} {0} Infinity"
      by (rule bpi.fp_iter_capped_eq_fp_iter_if_final_within_cap[OF le])
    then show ?thesis
      unfolding bpi.find_pivots_seen_capped_def bpi.find_pivots_seen_def by simp
  qed
  show "K \<le> card ?seen_c"
    using card_u_ge eq_seen by simp
qed

text \<open>
  A bound-generic, label-generic version of the short-tight prefix witness: any
  source-complete finite label (\<open>d 0 = 0\<close>) makes every prefix vertex
  \<open>v \<le> K \<le> k\<close> a short-tight witness for the \<open>K\<close>-round capped scan, at any
  bound covering the path.  This frees the seen lower bound from the specific
  initial label, which is what the level-\<open>l\<close> child runs need (their FindPivots
  input label is the previous level's capped label, not \<open>finite_initial_label\<close>).
\<close>

lemma path_k_short_tight_witness_prefix_fin:
  assumes vK: "v \<le> K" and Kk: "K \<le> k" and d0: "d 0 = 0"
  shows "bpi.short_tight_witness K d {0} (Fin (real (Suc k))) v"
proof -
  have vk: "v \<le> k" using vK Kk by simp
  have ne: "[0..<Suc v] \<noteq> []" by simp
  have walk: "pk.shortest_walk 0 [0..<Suc v] v"
  proof -
    have sw: "pk.simple_walk_betw 0 [0..<Suc v] v"
      by (rule path_k_canonical_walk[OF vk])
    have ww: "pk.walk_weight [0..<Suc v] = real v"
      using path_k_walk_weight_upt[of 0 v] vk by simp
    have dd: "pk.dist 0 v = real v"
      by (rule path_k_dist_eq[OF vk])
    show ?thesis
      unfolding pk.shortest_walk_def using sw ww dd by simp
  qed
  have tight: "successively pk.tight_edge_step [0..<Suc v]"
    by (rule pk.shortest_walk_successively_tight[OF walk])
  have hd0: "hd [0..<Suc v] = 0"
    using hd_conv_nth[OF ne] by (simp add: nth_upt del: upt_Suc)
  have last_v: "last [0..<Suc v] = v"
    using last_conv_nth[OF ne] by (simp add: nth_upt del: upt_Suc)
  have dlab: "d (hd [0..<Suc v]) = pk.dist 0 (hd [0..<Suc v])"
    using hd0 d0 pk.dist_refl_zero[OF pk.source_in_V] by simp
  have len: "length (pk.path_edges [0..<Suc v]) \<le> K"
    using bpi.path_edges_length[of "[0..<Suc v]"] vK by simp
  show ?thesis
    unfolding bpi.short_tight_witness_def
  proof (intro exI conjI)
    show "[0..<Suc v] \<noteq> []" by (rule ne)
    show "hd [0..<Suc v] \<in> {0}" using hd0 by simp
    show "last [0..<Suc v] = v" by (rule last_v)
    show "d (hd [0..<Suc v]) = pk.dist 0 (hd [0..<Suc v])" by (rule dlab)
    show "successively pk.tight_edge_step [0..<Suc v]" by (rule tight)
    show "\<forall>y\<in>set [0..<Suc v]. below_bound (pk.dist 0 y) (Fin (real (Suc k)))"
    proof
      fix y assume "y \<in> set [0..<Suc v]"
      then have "y \<le> k" using vk by auto
      then show "below_bound (pk.dist 0 y) (Fin (real (Suc k)))"
        by (simp add: path_k_dist_eq)
    qed
    show "length (pk.path_edges [0..<Suc v]) \<le> K" by (rule len)
  qed
qed

text \<open>
  The bound-/label-generic seen lower bound: at a bound covering the path, the
  capped \<open>K\<close>-round scan from \<open>{0}\<close> reaches at least \<open>K\<close> vertices for any
  source-complete sound label, provided the cap covers the path.
\<close>

lemma path_k_seen_card_ge_fin:
  assumes Kk: "K \<le> k" and cover: "Suc k \<le> cap" and d0: "d 0 = 0"
    and sound: "pk.sound_label d"
  shows "K \<le> card (bpi.find_pivots_seen_capped K cap d {0} (Fin (real (Suc k))))"
proof -
  let ?B = "Fin (real (Suc k))"
  let ?seen_c = "bpi.find_pivots_seen_capped K cap d {0} ?B"
  let ?seen_u = "bpi.find_pivots_seen K d {0} ?B"
  have su: "{0} \<subseteq> path_k_V k" by (simp add: path_k_V_eq)
  have reaches: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have subset_short: "{0..K} \<subseteq> bpi.find_pivots_short_vertices K d {0} ?B"
  proof
    fix v assume "v \<in> {0..K}"
    then have vK: "v \<le> K" by simp
    have vk: "v \<le> k" using vK Kk by simp
    have wit: "bpi.short_tight_witness K d {0} ?B v"
      using path_k_short_tight_witness_prefix_fin[where K=K and v=v and d=d, OF vK Kk d0] .
    have vV: "v \<in> path_k_V k" using vk by (simp add: path_k_V_eq)
    show "v \<in> bpi.find_pivots_short_vertices K d {0} ?B"
      unfolding bpi.find_pivots_short_vertices_def using vV wit by simp
  qed
  have short_sub_seen: "bpi.find_pivots_short_vertices K d {0} ?B \<subseteq> ?seen_u"
    using bpi.find_pivots_completes_short_vertices[OF sound reaches] by blast
  have subset_seen: "{0..K} \<subseteq> ?seen_u" using subset_short short_sub_seen by blast
  have seen_u_sub: "?seen_u \<subseteq> path_k_V k"
    unfolding bpi.find_pivots_seen_def by (rule bpi.fp_iter_seen_subset_V[OF su su])
  have fin_u: "finite ?seen_u" using seen_u_sub path_k_finite_V by (rule finite_subset)
  have card_u_ge: "K + 1 \<le> card ?seen_u"
  proof -
    have "card {0..K} \<le> card ?seen_u" by (rule card_mono[OF fin_u subset_seen])
    then show ?thesis by simp
  qed
  have card_c_le_cap: "card ?seen_c \<le> cap"
  proof -
    have sub: "?seen_c \<subseteq> path_k_V k"
      unfolding bpi.find_pivots_seen_capped_def
      by (rule bpi.fp_iter_capped_seen_subset_V[OF su su])
    have "card ?seen_c \<le> card (path_k_V k)" by (rule card_mono[OF path_k_finite_V sub])
    then show ?thesis using cover by (simp add: path_k_card_V)
  qed
  have eq_seen: "?seen_c = ?seen_u"
  proof -
    have le: "card (bpi.fp_seen (bpi.fp_iter_capped K cap d {0} {0} ?B)) \<le> cap"
      using card_c_le_cap unfolding bpi.find_pivots_seen_capped_def .
    have "bpi.fp_iter_capped K cap d {0} {0} ?B = bpi.fp_iter K d {0} {0} ?B"
      by (rule bpi.fp_iter_capped_eq_fp_iter_if_final_within_cap[OF le])
    then show ?thesis
      unfolding bpi.find_pivots_seen_capped_def bpi.find_pivots_seen_def by simp
  qed
  show "K \<le> card ?seen_c" using card_u_ge eq_seen by simp
qed

lemma path_k_source_is_sole_pivot_fin:
  assumes Kk: "K \<le> k" and cover: "Suc k \<le> cap" and d0: "d 0 = 0"
    and sound: "pk.sound_label d"
  shows "bpi.find_pivots_pivots_capped K cap d {0} (Fin (real (Suc k))) = {0}"
proof (rule bpi.find_pivots_pivots_capped_singleton_source_if_large_tree)
  let ?B = "Fin (real (Suc k))"
  show "card (bpi.find_pivots_seen_capped K cap d {0} ?B) \<le> cap"
  proof -
    have su: "{0} \<subseteq> path_k_V k" by (simp add: path_k_V_eq)
    have "bpi.find_pivots_seen_capped K cap d {0} ?B \<subseteq> path_k_V k"
      unfolding bpi.find_pivots_seen_capped_def
      by (rule bpi.fp_iter_capped_seen_subset_V[OF su su])
    then have "card (bpi.find_pivots_seen_capped K cap d {0} ?B) \<le> Suc k"
      using card_mono[OF path_k_finite_V] by (simp add: path_k_card_V)
    then show ?thesis using cover by simp
  qed
  show "K \<le> card (bpi.tree_of 0
      \<inter> bpi.find_pivots_seen_capped K cap d {0} ?B)"
  proof -
    let ?seen_c = "bpi.find_pivots_seen_capped K cap d {0} ?B"
    have s0: "{0} \<subseteq> path_k_V k" by (simp add: path_k_V_eq)
    have seen_sub: "?seen_c \<subseteq> path_k_V k"
      unfolding bpi.find_pivots_seen_capped_def
      by (rule bpi.fp_iter_capped_seen_subset_V[OF s0 s0])
    have inter_eq: "bpi.tree_of 0 \<inter> ?seen_c = ?seen_c"
      using seen_sub path_k_tree_of_source by auto
    have "K \<le> card ?seen_c" by (rule path_k_seen_card_ge_fin[OF Kk cover d0 sound])
    then show ?thesis using inter_eq by simp
  qed
qed

text \<open>
  The source-is-sole-pivot gateway (deliverable (G3), conjunct \<open>P = {s}\<close>): under
  the same two hypotheses, the singleton FindPivots call on the path returns
  exactly the source.  This combines the seen lower bound above (the @{term K}
  qualifying vertices) with the no-overflow upper bound
  (@{thm [source] path_k_find_pivots_seen_card_le}) through the reusable brick
  @{thm [source] bpi.find_pivots_pivots_capped_singleton_source_if_large_tree}; the
  source tree is the whole path (@{thm [source] path_k_tree_of_source}), so the
  tree-slice intersection is the entire seen set.
\<close>

lemma path_k_source_is_sole_pivot:
  assumes Kk: "K \<le> k" and cover: "Suc k \<le> cap"
  shows "bpi.find_pivots_pivots_capped K cap pk.finite_initial_label {0} Infinity = {0}"
proof (rule bpi.find_pivots_pivots_capped_singleton_source_if_large_tree)
  show "card (bpi.find_pivots_seen_capped K cap pk.finite_initial_label {0} Infinity) \<le> cap"
  proof -
    have "card (bpi.find_pivots_seen_capped K cap pk.finite_initial_label {0} Infinity) \<le> Suc k"
      by (rule path_k_find_pivots_seen_card_le)
    then show ?thesis using cover by simp
  qed
  show "K \<le> card (bpi.tree_of 0
      \<inter> bpi.find_pivots_seen_capped K cap pk.finite_initial_label {0} Infinity)"
  proof -
    let ?seen_c = "bpi.find_pivots_seen_capped K cap pk.finite_initial_label {0} Infinity"
    have s0: "{0} \<subseteq> path_k_V k" by (simp add: path_k_V_eq)
    have seen_sub: "?seen_c \<subseteq> path_k_V k"
      unfolding bpi.find_pivots_seen_capped_def
      by (rule bpi.fp_iter_capped_seen_subset_V[OF s0 s0])
    have inter_eq: "bpi.tree_of 0 \<inter> ?seen_c = ?seen_c"
      using seen_sub path_k_tree_of_source by auto
    have "K \<le> card ?seen_c" by (rule path_k_seen_card_ge[OF Kk cover])
    then show ?thesis using inter_eq by simp
  qed
qed

text \<open>
  The remaining structural conjuncts of
  @{const strict_tie_breaking_digraph.charged_direct_insert_source_pivot_finishes}
  on the path family, discharged once and for all.  Together with the
  source-is-sole-pivot gateway above they reduce the predicate to its single
  charged child-run obligation (conjunct \<open>6\<close>): a full-cover level-\<open>p-1\<close> run of
  the path inside the bound \<^term>\<open>Fin (real (Suc k))\<close>.
\<close>

text \<open>Conjunct \<open>2\<close>: the source's FindPivots label never rises above \<open>0\<close>.\<close>
lemma path_k_fp_label_source_le_zero:
  "bpi.find_pivots_label_capped K cap pk.finite_initial_label {0} Infinity 0 \<le> 0"
proof -
  have "bpi.find_pivots_label_capped K cap pk.finite_initial_label {0} Infinity 0
      \<le> pk.finite_initial_label 0"
    by (rule bpi.find_pivots_label_capped_le)
  also have "pk.finite_initial_label 0 = pk.dist 0 0"
    by (rule pk.finite_initial_label_source_complete)
  also have "pk.dist 0 0 = 0"
    by (rule pk.dist_refl_zero[OF pk.source_in_V])
  finally show ?thesis .
qed

text \<open>Conjunct \<open>5\<close>: the zero-bounded source tree is empty.\<close>
lemma path_k_bound_tree_source_Fin0_empty:
  "pk.bound_tree {0} (Fin 0) = {}"
proof -
  have "\<And>v. v \<in> pk.bound_tree {0} (Fin 0) \<Longrightarrow> False"
  proof -
    fix v assume "v \<in> pk.bound_tree {0} (Fin 0)"
    then have rv: "pk.reachable 0 v" and bb: "below_bound (pk.dist 0 v) (Fin 0)"
      unfolding pk.bound_tree_def by auto
    have "0 \<le> pk.dist 0 v" by (rule pk.dist_nonneg[OF rv])
    moreover have "pk.dist 0 v < 0" using bb by simp
    ultimately show False by simp
  qed
  then show ?thesis by blast
qed

text \<open>Conjunct \<open>4\<close>: the FindPivots source precondition holds at any finite bound.\<close>
lemma path_k_fp_source_pre_full:
  "pk.bmssp_pre_full
     (bpi.find_pivots_label_capped K cap pk.finite_initial_label {0} Infinity)
     {0} (Fin B)"
proof -
  have allr: "\<And>v. v \<in> path_k_V k \<Longrightarrow> pk.reachable 0 v"
    by (rule path_k_all_reachable)
  have sc: "pk.finite_initial_label 0 = pk.dist 0 0"
    by (rule pk.finite_initial_label_source_complete)
  have pre0: "pk.bmssp_pre_full pk.finite_initial_label {0} Infinity"
  proof (rule pk.top_bmssp_pre_full)
    show "\<And>v. v \<in> path_k_V k \<Longrightarrow> pk.reachable 0 v" by (rule allr)
    show "pk.finite_initial_label 0 = pk.dist 0 0" by (rule sc)
  qed
  have sound: "pk.sound_label pk.finite_initial_label"
    by (rule pk.finite_initial_label_sound[OF allr])
  have reaches: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have pre_inf:
    "pk.bmssp_pre_full
       (bpi.find_pivots_label_capped K cap pk.finite_initial_label {0} Infinity)
       {0} Infinity"
    by (rule bpi.find_pivots_label_capped_preserves_source_pre[OF sound pre0 reaches])
  show ?thesis
    using pre_inf unfolding pk.bmssp_pre_full_def by auto
qed

text \<open>
  Conjunct \<open>7\<close>: with the bound \<^term>\<open>Fin (real (Suc k))\<close> chosen to cover the whole
  path, the source band is the entire path, so its outgoing boundary edges all
  relax to a value \<open>\<le> k < Suc k\<close> and the direct-edge batch is empty.
\<close>
lemma path_k_direct_batch_empty:
  "bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
     (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) Infinity = []"
proof -
  let ?U = "bpi.range_tree {0} 0 (Fin (real (Suc k)))"
  have setU: "set (bpi.edge_list_of (bpi.outgoing_edges ?U)) = bpi.outgoing_edges ?U"
    by (rule bpi.edge_list_of_properties(1)[OF bpi.finite_outgoing_edges])
  have no_edge: "\<And>e. e \<in> bpi.outgoing_edges ?U \<Longrightarrow>
      \<not> (real (Suc k) \<le> pk.dist 0 (fst e) + path_k_weight k (fst e) (snd e) \<and>
         below_bound (pk.dist 0 (fst e) + path_k_weight k (fst e) (snd e)) Infinity)"
  proof -
    fix e assume "e \<in> bpi.outgoing_edges ?U"
    then have edge: "e \<in> path_k_E k"
      unfolding bpi.outgoing_edges_def by auto
    obtain u v where e: "e = (u, v)" by (cases e)
    have euv: "(u, v) \<in> path_k_E k" using edge e by simp
    then have vSuc: "v = Suc u" and ult: "u < k"
      by (simp_all add: path_k_E_iff)
    have du: "pk.dist 0 u = real u"
      using ult by (intro path_k_dist_eq) simp
    have wuv: "path_k_weight k u v = 1"
      using euv by (simp add: path_k_weight_def)
    have "pk.dist 0 u + path_k_weight k u v = real u + 1"
      using du wuv by simp
    also have "\<dots> < real (Suc k)"
      using ult by simp
    finally show "\<not> (real (Suc k) \<le> pk.dist 0 (fst e) + path_k_weight k (fst e) (snd e) \<and>
         below_bound (pk.dist 0 (fst e) + path_k_weight k (fst e) (snd e)) Infinity)"
      using e by simp
  qed
  show ?thesis
    unfolding bpi.edge_relaxation_pairs_in_bound_def
    using setU no_edge by (auto simp: filter_empty_conv)
qed

text \<open>
  \<^bold>\<open>Milestone B1 (deliverable (G3)), the decoupled charged reduction.\<close>
  Putting conjuncts \<open>1\<close>--\<open>5\<close> and \<open>7\<close> together, the explicit-assumption
  top-level builder
  @{thm [source] bpi.charged_direct_insert_top_level_cost_exists_if_source_pivot_finishes}
  turns the existence of the single full-cover level-\<open>p-1\<close> child run (conjunct
  \<open>6\<close>) into the existence of a charged top-level cost.  This is the schedule-aware
  reduction of (G3) to the lone charged child-run obligation: once that run is
  built for the inflated schedule \<open>N\<close>, the charged top-level cost on \<open>P\<^sub>k\<close>
  exists unconditionally.
\<close>

lemma path_k_charged_cost_exists_if_child:
  assumes pk_le: "sssp_log_one_third_param N \<le> k"
    and cover: "Suc k \<le> bmssp_level_cap (sssp_log_one_third_param N)
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)"
    and child:
      "\<exists>U_child c_child.
        bpi.charged_direct_insert_costed_bmssp (Suc 0)
          (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
          (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
          (sssp_log_one_third_param N)
          (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
            (sssp_log_one_third_param N))
          (sssp_log_one_third_param N - 1)
          (bpi.find_pivots_label_capped (sssp_log_one_third_param N)
            (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
              (sssp_log_one_third_param N))
            pk.finite_initial_label {0} Infinity)
          {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k))) U_child c_child"
  shows "\<exists>c. bpi.charged_direct_insert_top_level_cost 1 N c"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  let ?d_fp = "bpi.find_pivots_label_capped ?p ?cap pk.finite_initial_label {0} Infinity"
  let ?P = "bpi.find_pivots_pivots_capped ?p ?cap pk.finite_initial_label {0} Infinity"
  have P0: "?P = {0}" by (rule path_k_source_is_sole_pivot[OF pk_le cover])
  have d_lt: "?d_fp 0 < real (Suc k)"
  proof -
    have "?d_fp 0 \<le> 0" by (rule path_k_fp_label_source_le_zero)
    also have "(0::real) < real (Suc k)" by simp
    finally show ?thesis .
  qed
  have bn: "(0::real) \<le> real (Suc k)" by simp
  have pre: "pk.bmssp_pre_full ?d_fp {0} (Fin (real (Suc k)))"
    by (rule path_k_fp_source_pre_full)
  have cap_pos: "0 < ?p * ?cap"
    using sssp_log_one_third_param_pos[of N] by (simp add: bmssp_level_cap_def)
  have card_lt: "card (pk.bound_tree ?P (Fin 0)) < ?p * ?cap"
  proof -
    have "pk.bound_tree ?P (Fin 0) = {}"
      using P0 path_k_bound_tree_source_Fin0_empty by simp
    then show ?thesis using cap_pos by simp
  qed
  have batch: "bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
      (bpi.range_tree ?P 0 (Fin (real (Suc k)))) (real (Suc k)) Infinity = []"
    using P0 path_k_direct_batch_empty by simp
  have main: "\<exists>c. bpi.charged_direct_insert_top_level_cost (Suc 0) N c"
    using child
  proof (elim exE)
    fix U_child c_child
    assume child':
      "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap
         (?p - 1) ?d_fp {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k)))
         U_child c_child"
    show ?thesis
    proof (rule bpi.charged_direct_insert_top_level_cost_exists_if_source_pivot_finishes)
      show "?P = {0}" by (rule P0)
      show "?d_fp 0 < real (Suc k)" by (rule d_lt)
      show "(0::real) \<le> real (Suc k)" by (rule bn)
      show "pk.bmssp_pre_full ?d_fp {0} (Fin (real (Suc k)))" by (rule pre)
      show "card (pk.bound_tree ?P (Fin 0)) < ?p * ?cap" by (rule card_lt)
      show "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap
          (?p - 1) ?d_fp {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k)))
          U_child c_child"
        by (rule child')
      show "bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
          (bpi.range_tree ?P 0 (Fin (real (Suc k)))) (real (Suc k)) Infinity = []"
        by (rule batch)
    qed
  qed
  then show ?thesis by simp
qed

text \<open>
  \<^bold>\<open>Cover lift (\<open>l \<rightarrow> Suc l\<close>).\<close>  If a full-cover charged run of the whole path
  exists at level \<open>l\<close> for the FindPivots label of a source-complete sound input
  label \<open>d\<close>, then one exists at level \<open>Suc l\<close> for \<open>d\<close>: the FindPivots call on
  the path returns just the source (cap covers the path), one pull separates the
  source from the band, the level-\<open>l\<close> cover discharges the band, and the residual
  loop terminates immediately.  Stacking this from the level-1 base reaches the
  level \<open>p-1\<close> required by conjunct 6.
\<close>

lemma path_k_cover_lift:
  fixes p q cap l :: nat and d :: "nat \<Rightarrow> real"
  assumes pk_le: "p \<le> k" and cover: "Suc k \<le> cap"
    and ppos: "0 < p"
    and sound: "pk.sound_label d" and d0: "d 0 = 0"
    and pre0: "pk.bmssp_pre_full d {0} Infinity"
    and child: "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
        (bmssp_level_cap p q) q p p cap l
        (bpi.find_pivots_label_capped p cap d {0} (Fin (real (Suc k))))
        {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k))) U c"
  shows "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap (Suc l) d {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U c"
proof -
  let ?B = "Fin (real (Suc k))"
  let ?d2 = "bpi.find_pivots_label_capped p cap d {0} ?B"
  let ?P = "bpi.find_pivots_pivots_capped p cap d {0} ?B"
  have reaches0: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have P0: "?P = {0}" by (rule path_k_source_is_sole_pivot_fin[OF pk_le cover d0 sound])
  have sound2: "pk.sound_label ?d2"
    unfolding bpi.find_pivots_label_capped_def
    by (rule bpi.fp_iter_capped_label_sound[OF sound reaches0])
  have le2: "?d2 0 \<le> d 0" by (rule bpi.find_pivots_label_capped_le)
  have d2_0: "?d2 0 = 0"
  proof -
    have "pk.dist 0 0 \<le> ?d2 0" using sound2 pk.source_in_V pk.reachable_refl[OF pk.source_in_V]
      unfolding pk.sound_label_def by blast
    moreover have "pk.dist 0 0 = 0" by (rule pk.dist_refl_zero[OF pk.source_in_V])
    ultimately show ?thesis using le2 d0 by simp
  qed
  have pre2: "pk.bmssp_pre_full ?d2 {0} ?B"
  proof -
    have preB: "pk.bmssp_pre_full d {0} ?B"
      using pre0 unfolding pk.bmssp_pre_full_def by auto
    show ?thesis
      by (rule bpi.find_pivots_label_capped_preserves_source_pre[OF sound preB reaches0])
  qed
  obtain U_c c_c where childrun:
    "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap l
       ?d2 {0} ?B (pk.dist 0) ?B U_c c_c"
    using child by blast
  have Mpos: "0 < bmssp_level_cap p q l" using ppos by (simp add: bmssp_level_cap_def)
  have pull: "pull_separates (bpi.label_partition_view ?d2 {0}) (bmssp_level_cap p q l)
      (real (Suc k)) {0} (real (Suc k)) (bpi.label_partition_view ?d2 {} :: nat partition_view)"
    unfolding pull_separates_def bpi.label_partition_view_def
    using Mpos d2_0 by simp
  have split: "{0} = bpi.split_below ?d2 {0} (real (Suc k))"
    using d2_0 by (auto simp: bpi.split_below_def)
  have small: "card (pk.bound_tree {0} (Fin 0)) < p * cap"
  proof -
    have "pk.bound_tree {0} (Fin 0) = {}" by (rule path_k_bound_tree_source_Fin0_empty)
    moreover have "0 < p * cap" using ppos cover by simp
    ultimately show ?thesis by simp
  qed
  have tail_empty:
    "keys_of (batch_min_update (bpi.label_partition_view ?d2 {} :: nat partition_view)
       (bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
          (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) ?B @
        bpi.edge_relaxation_pairs_between (pk.dist 0)
          (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) (real (Suc k)) @
        bpi.label_pairs_between ?d2 {0} (real (Suc k)) (real (Suc k)))) = {}"
  proof -
    have lower: "bpi.edge_relaxation_pairs_between (pk.dist 0)
        (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) (real (Suc k)) = []"
      unfolding bpi.edge_relaxation_pairs_between_def
      by (auto simp: filter_empty_conv split: prod.splits)
    have src: "bpi.label_pairs_between ?d2 {0} (real (Suc k)) (real (Suc k)) = []"
      unfolding bpi.label_pairs_between_def by (simp add: filter_empty_conv)
    have direct: "bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
        (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) ?B = []"
      unfolding bpi.edge_relaxation_pairs_in_bound_def by (auto simp: filter_empty_conv)
    show ?thesis using lower src direct unfolding batch_min_update_def by simp
  qed
  have loop:
    "\<exists>betas bs charged_Us child_outputs U c child_costs.
       bpi.charged_direct_insert_costed_partition_loop_state (Suc 0)
         (bmssp_level_cap p q) q p p cap l ?d2 {0} ?B (pk.dist 0)
         (bpi.label_partition_view ?d2 {0}) 0 betas bs ?B charged_Us child_outputs U c child_costs"
    by (rule bpi.charged_loop_single_step_then_done_exists_dist
        [where Bmax = "real (Suc k)" and beta = "real (Suc k)" and b = "real (Suc k)"
          and S_pull = "{0}" and D_pull = "bpi.label_partition_view ?d2 {} :: nat partition_view"
          and d_child = "pk.dist 0" and U_child = U_c and c_child = c_c])
      (use pull pre2 split reaches0 small childrun tail_empty in simp_all)
  then obtain betas bs charged_Us child_outputs U c child_costs where looprun:
    "bpi.charged_direct_insert_costed_partition_loop_state (Suc 0)
       (bmssp_level_cap p q) q p p cap l ?d2 {0} ?B (pk.dist 0)
       (bpi.label_partition_view ?d2 {0}) 0 betas bs ?B charged_Us child_outputs U c child_costs"
    by blast
  let ?U = "U \<union> {v \<in> pk.bound_tree {0} ?B. ?d2 v = pk.dist 0 v}"
  have run: "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap
      (Suc l) d {0} ?B (pk.dist 0) ?B ?U
      (bpi.fp_iter_capped_scan_cost p cap d {0} {0} ?B + 0 + c)"
    by (rule bpi.charged_direct_insert_costed_bmssp_step_with_insert_cost
        [where D = "bpi.label_partition_view ?d2 {0}" and c_insert = 0])
      (use looprun P0 in \<open>simp_all add: bpi.partition_initial_insert_cost_bound_def pk.complete_on_def\<close>)
  show ?thesis using run by blast
qed

text \<open>
  \<^bold>\<open>Level chain.\<close>  Stacking the cover lift from a level-1 base, a whole-path
  cover exists at every level \<open>l \<ge> 1\<close> for any source-complete sound input
  label.  Specialising at \<open>l = p - 1\<close> supplies conjunct 6 of
  @{const strict_tie_breaking_digraph.charged_direct_insert_source_pivot_finishes}
  unconditionally once the level-1 base is available.
\<close>

lemma path_k_cover_ge1:
  fixes p q cap :: nat
  assumes pk_le: "p \<le> k" and cover: "Suc k \<le> cap" and ppos: "0 < p"
    and base1: "\<And>d. pk.sound_label d \<Longrightarrow> d 0 = 0 \<Longrightarrow> pk.bmssp_pre_full d {0} Infinity
        \<Longrightarrow> \<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
            (bmssp_level_cap p q) q p p cap (Suc 0) d {0} (Fin (real (Suc k)))
            (pk.dist 0) (Fin (real (Suc k))) U c"
  shows "\<And>d. pk.sound_label d \<Longrightarrow> d 0 = 0 \<Longrightarrow> pk.bmssp_pre_full d {0} Infinity \<Longrightarrow>
      \<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p
        cap (Suc l) d {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k))) U c"
proof (induct l)
  case 0
  show ?case using base1[OF 0(1) 0(2) 0(3)] .
next
  case (Suc l)
  let ?d2 = "bpi.find_pivots_label_capped p cap d {0} (Fin (real (Suc k)))"
  have reaches0: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have sound2: "pk.sound_label ?d2"
    unfolding bpi.find_pivots_label_capped_def
    by (rule bpi.fp_iter_capped_label_sound[OF Suc(2) reaches0])
  have d2_0: "?d2 0 = 0"
  proof -
    have "pk.dist 0 0 \<le> ?d2 0" using sound2 pk.source_in_V pk.reachable_refl[OF pk.source_in_V]
      unfolding pk.sound_label_def by blast
    moreover have "pk.dist 0 0 = 0" by (rule pk.dist_refl_zero[OF pk.source_in_V])
    ultimately show ?thesis
      using bpi.find_pivots_label_capped_le[of p cap d "{0}" "Fin (real (Suc k))" 0] Suc(3) by simp
  qed
  have pre2: "pk.bmssp_pre_full ?d2 {0} Infinity"
  proof (rule pk.top_bmssp_pre_full)
    show "\<And>v. v \<in> path_k_V k \<Longrightarrow> pk.reachable 0 v" by (rule path_k_all_reachable)
    show "?d2 0 = pk.dist 0 0" using d2_0 pk.dist_refl_zero[OF pk.source_in_V] by simp
  qed
  have child: "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap (Suc l) ?d2 {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U c"
    by (rule Suc(1)[OF sound2 d2_0 pre2])
  show ?case
    by (rule path_k_cover_lift[OF pk_le cover ppos Suc(2) Suc(3) Suc(4) child])
qed

text \<open>
  \<^bold>\<open>The path band tree.\<close>  Every vertex \<open>a \<le> v \<le> k\<close> lies on the unique shortest
  walk from the source, so the source band starting at \<open>a\<close> below the finite
  bound \<^term>\<open>Fin r\<close> is exactly the prefix \<open>{a..k}\<close> truncated by \<open>r\<close>.
\<close>

lemma path_k_through_iff:
  assumes "v \<le> k"
  shows "pk.through {a} v \<longleftrightarrow> a \<le> v"
proof
  assume "pk.through {a} v"
  then obtain pp where sw: "pk.shortest_walk 0 pp v" and au: "a \<in> set pp"
    unfolding pk.through_def by auto
  have "pk.simple_walk_betw 0 pp v" using sw unfolding pk.shortest_walk_def by simp
  then have "pp = [0..<Suc v]" by (rule path_k_simple_walk_unique[OF _ assms])
  then show "a \<le> v" using au by auto
next
  assume "a \<le> v"
  then have aset: "a \<in> set [0..<Suc v]" by auto
  have ww: "pk.walk_weight [0..<Suc v] = real v"
    using path_k_walk_weight_upt[of 0 v] assms by simp
  have sw: "pk.shortest_walk 0 [0..<Suc v] v"
    unfolding pk.shortest_walk_def
    using path_k_canonical_walk[OF assms] ww path_k_dist_eq[OF assms] by simp
  show "pk.through {a} v" unfolding pk.through_def using sw aset by auto
qed

lemma path_k_bound_tree_band:
  "pk.bound_tree {a} (Fin r) = {v. a \<le> v \<and> v \<le> k \<and> real v < r}"
proof (intro set_eqI iffI)
  fix v assume "v \<in> pk.bound_tree {a} (Fin r)"
  then have vV: "v \<in> path_k_V k" and thr: "pk.through {a} v"
    and lt: "pk.dist 0 v < r"
    unfolding pk.bound_tree_def by auto
  have vk: "v \<le> k" using vV by (simp add: path_k_V_eq)
  show "v \<in> {v. a \<le> v \<and> v \<le> k \<and> real v < r}"
    using thr vk lt path_k_through_iff[OF vk] path_k_dist_eq[OF vk] by simp
next
  fix v assume "v \<in> {v. a \<le> v \<and> v \<le> k \<and> real v < r}"
  then have av: "a \<le> v" and vk: "v \<le> k" and lt: "real v < r" by auto
  show "v \<in> pk.bound_tree {a} (Fin r)"
    unfolding pk.bound_tree_def
    using av vk lt path_k_through_iff[OF vk] path_k_dist_eq[OF vk]
      path_k_all_reachable by (simp add: path_k_V_eq)
qed

text \<open>The base-case order on a path source band \<open>{a}\<close> below \<open>Suc k\<close> is just the
  increasing run \<open>[a, \<dots>, k]\<close>: distances equal indices, so the unique distinct
  distance-sorted listing of \<open>{a..k}\<close> is \<^term>\<open>[a..<Suc k]\<close>.\<close>

lemma path_k_base_order:
  shows "pk.base_case_order a (Fin (real (Suc k))) = [a..<Suc k]"
proof -
  have set_xs: "set (pk.base_case_order a (Fin (real (Suc k)))) = {a..k}"
  proof -
    have "set (pk.base_case_order a (Fin (real (Suc k))))
        = {v. a \<le> v \<and> v \<le> k \<and> real v < real (Suc k)}"
      by (simp add: pk.base_case_order_set path_k_bound_tree_band)
    also have "\<dots> = {a..k}" by auto
    finally show ?thesis .
  qed
  have dist_xs: "distinct (pk.base_case_order a (Fin (real (Suc k))))"
    by (rule pk.base_case_order_distinct)
  have sorted_xs: "sorted (pk.base_case_order a (Fin (real (Suc k))))"
  proof -
    have "sorted_wrt (\<le>) (pk.base_case_order a (Fin (real (Suc k))))"
    proof (rule sorted_wrt_mono_rel[OF _ pk.base_case_order_sorted])
      fix u v
      assume "u \<in> set (pk.base_case_order a (Fin (real (Suc k))))"
        and "v \<in> set (pk.base_case_order a (Fin (real (Suc k))))"
      then have "u \<le> k" and "v \<le> k" using set_xs by auto
      moreover assume "pk.dist 0 u \<le> pk.dist 0 v"
      ultimately show "u \<le> v" by (simp add: path_k_dist_eq)
    qed
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule sorted_distinct_set_unique[OF sorted_xs dist_xs, of "[a..<Suc k]"])
    show "set (pk.base_case_order a (Fin (real (Suc k)))) = set [a..<Suc k]"
      by (simp only: set_xs set_upt atLeastLessThanSuc_atLeastAtMost)
    show "sorted [a..<Suc k]" by (rule sorted_upt)
    show "distinct [a..<Suc k]" by (rule distinct_upt)
  qed
qed

text \<open>
  \<^bold>\<open>One base step.\<close>  A level-0 base case on a singleton path band \<open>{a}\<close>
  truncated just above \<open>a\<close> fully settles \<open>a\<close>: the bounded tree is \<open>{a}\<close>, of
  card \<open>1 \<le> p\<close>, so the base call keeps it whole.  Witnesses are given
  explicitly (the truncating label, returned bound, vertex set) to avoid any
  search in the large path simpset.\<close>

lemma path_k_base_step:
  fixes a p q cap :: nat and d :: "nat \<Rightarrow> real"
  assumes ak: "a \<le> k" and ppos: "0 < p"
  shows "\<exists>d' c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap 0 d {a} (Fin (real (Suc a)))
      d' (Fin (real (Suc a))) {a} c"
proof -
  have bt: "pk.bound_tree {a} (Fin (real (Suc a))) = {a}"
  proof -
    have "pk.bound_tree {a} (Fin (real (Suc a)))
        = {v. a \<le> v \<and> v \<le> k \<and> real v < real (Suc a)}"
      by (rule path_k_bound_tree_band)
    also have "\<dots> = {a}" using ak by (auto simp only: of_nat_less_iff Suc_le_eq atMost_iff)
    finally show ?thesis .
  qed
  have small: "card (pk.bound_tree {a} (Fin (real (Suc a)))) \<le> p"
    using bt ppos by simp
  have len: "length (pk.base_case_order a (Fin (real (Suc a)))) \<le> p"
  proof -
    have "set (pk.base_case_order a (Fin (real (Suc a)))) = {a}"
      using pk.base_case_order_set[of a "Fin (real (Suc a))"] bt by simp
    moreover have "distinct (pk.base_case_order a (Fin (real (Suc a))))"
      by (rule pk.base_case_order_distinct)
    ultimately have "length (pk.base_case_order a (Fin (real (Suc a)))) = 1"
      by (simp add: distinct_card[symmetric])
    then show ?thesis using ppos by simp
  qed
  have U: "pk.base_case_vertices p a (Fin (real (Suc a))) = {a}"
    using pk.base_case_success[OF len] bt by simp
  have B': "pk.base_case_bound p a (Fin (real (Suc a))) = Fin (real (Suc a))"
    using len by (simp add: pk.base_case_bound_def)
  let ?d' = "\<lambda>v. if v \<in> pk.base_case_vertices p a (Fin (real (Suc a)))
      then pk.dist 0 v else d v"
  have run: "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p
      cap 0 d {a} (Fin (real (Suc a))) ?d' (Fin (real (Suc a))) {a}
      (bpi.base_case_scan_cost (Suc 0) p a (Fin (real (Suc a))))"
    using bpi.Charged_Direct_Insert_Base[OF refl, where \<Delta>="Suc 0" and M_of="bmssp_level_cap p q"
        and t=q and h=p and k=p and cap=cap and d=d and x=a and B="Fin (real (Suc a))"] U B' by simp
  show ?thesis by (intro exI[of _ ?d'] exI) (rule run)
qed

text \<open>
  \<^bold>\<open>Top base step.\<close>  A level-0 base case on the whole source band \<open>{0}\<close> below
  \<^term>\<open>Fin (real (Suc k))\<close> settles exactly the prefix \<open>{0..<p}\<close> and advances the
  returned bound to \<^term>\<open>Fin (real p)\<close>: the path order is \<open>[0..<Suc k]\<close>, the
  capped scan stops at the \<open>p\<close>-th vertex \<open>p\<close>, and only strictly-smaller vertices
  survive.  This is the per-block brick that the multi-step loop chains.\<close>

text \<open>
  \<^bold>\<open>Singleton frontier pull.\<close>  A one-element bucket \<open>{a}\<close> with label view \<open>d\<close>
  is pulled whole (fits under the fanout \<open>0 < p\<close>), leaving the empty view; the
  separator threshold is the loop bound \<open>Bmax\<close>.  Each multi-step block iteration
  uses this pull.\<close>

lemma path_k_pull_singleton:
  fixes a p :: nat and Bmax :: real and d :: "nat \<Rightarrow> real"
  assumes ppos: "0 < p"
  shows "pull_separates (bpi.label_partition_view d {a}) p Bmax {a} Bmax
      (bpi.label_partition_view d {} :: nat partition_view)"
  unfolding pull_separates_def bpi.label_partition_view_def using ppos by simp

text \<open>
  \<^bold>\<open>Block range tree.\<close>  The slice of the source tree at heights \<open>[a, a+p)\<close> is the
  block \<open>{a..<a+p}\<close>; this is the charged child the loop discharges at each step.\<close>

lemma path_k_range_block:
  assumes apk: "a + p \<le> k"
  shows "bpi.range_tree {a} (real a) (Fin (real (a + p))) = {a..<a+p}"
proof -
  have "bpi.range_tree {a} (real a) (Fin (real (a + p)))
      = {v \<in> pk.bound_tree {a} (Fin (real (a + p))). real a \<le> pk.dist 0 v}"
    unfolding bpi.range_tree_def bpi.bound_tree_eq_tree_set by auto
  also have "pk.bound_tree {a} (Fin (real (a + p))) = {v. a \<le> v \<and> v \<le> k \<and> real v < real (a + p)}"
    by (rule path_k_bound_tree_band)
  also have "{v \<in> {v. a \<le> v \<and> v \<le> k \<and> real v < real (a + p)}. real a \<le> pk.dist 0 v} = {a..<a+p}"
    using apk by (auto simp: path_k_dist_eq)
  finally show ?thesis .
qed

text \<open>
  \<^bold>\<open>Source-pivot range slice.\<close>  Read off the source tree \<open>{0}\<close> the path range
  \<open>[a, b)\<close> is exactly the integer block \<open>{a..<b}\<close> whenever \<open>b \<le> Suc k\<close>.  Unlike
  @{thm [source] path_k_range_block} (which slices from the band start \<open>{a}\<close>), the
  pivot here is the \<^emph>\<open>global\<close> source \<open>{0}\<close> that the top-level partition loop carries,
  which is what the loop's relaxation batches @{term "bpi.range_tree {0} a B"} use.\<close>

lemma path_k_range_zero:
  assumes bk: "b \<le> Suc k"
  shows "bpi.range_tree {0} (real a) (Fin (real b)) = {a..<b}"
proof -
  have "bpi.range_tree {0} (real a) (Fin (real b))
      = {v \<in> pk.bound_tree {0} (Fin (real b)). real a \<le> pk.dist 0 v}"
    unfolding bpi.range_tree_def bpi.bound_tree_eq_tree_set by auto
  also have "pk.bound_tree {0} (Fin (real b)) = {v. 0 \<le> v \<and> v \<le> k \<and> real v < real b}"
    by (rule path_k_bound_tree_band)
  also have "{v \<in> {v. 0 \<le> v \<and> v \<le> k \<and> real v < real b}. real a \<le> pk.dist 0 v} = {a..<b}"
    using bk by (auto simp: path_k_dist_eq)
  finally show ?thesis .
qed

text \<open>
  \<^bold>\<open>The source-pivot pull on the path.\<close>  Because the source carries the genuine
  zero label, the loop's threshold pull @{term "bpi.split_below d {0} beta"} of the
  sole pivot set \<open>{0}\<close> is exactly \<open>{0}\<close> below a positive threshold and empty
  otherwise.  This pins down the only pivot the top-level loop can ever pull.\<close>

lemma path_k_split_below_zero:
  assumes d0: "d (0::nat) = 0"
  shows "bpi.split_below d {0} beta = (if 0 < beta then {0} else {})"
  using d0 unfolding bpi.split_below_def by auto

text \<open>
  \<^bold>\<open>Pivot settledness at the source band (the B2 cost brick).\<close>  At the loop's
  initial band \<open>a = 0\<close> the already-settled prefix @{term "pk.bound_tree {0} (Fin 0)"}
  is empty, so the source pull is trivially settled, and lands inside its own range
  slice \<open>{0..<b}\<close> whenever the child advanced the bound (\<open>0 < b \<le> Suc k\<close>).  This is
  the per-step ingredient of the no-stranding invariant of
  @{thm [source] bpi.charged_direct_insert_costed_partition_loop_state_cost_local_budget_if_settled},
  specialised to the unit-out-degree path where the loop runs at band \<open>0\<close>.\<close>

lemma path_k_pull_settled_at_zero:
  "bpi.split_below d {0} beta \<inter> pk.bound_tree {0} (Fin 0) = {}"
  using path_k_bound_tree_source_Fin0_empty by simp

lemma path_k_pull_in_first_slice:
  assumes bpos: "0 < b" and bk: "b \<le> Suc k"
  shows "bpi.split_below d {0} beta \<subseteq> bpi.range_tree {0} (real 0) (Fin (real b))"
proof -
  have sub0: "bpi.split_below d {0} beta \<subseteq> {0}"
    unfolding bpi.split_below_def by auto
  have "bpi.range_tree {0} (real 0) (Fin (real b)) = {0..<b}"
    by (rule path_k_range_zero[OF bk])
  then have "{0} \<subseteq> bpi.range_tree {0} (real 0) (Fin (real b))"
    using bpos by auto
  with sub0 show ?thesis by blast
qed

text \<open>
  \<^bold>\<open>The relaxation never re-creates the source.\<close>  Every relaxation target on the
  path is the head \<open>Suc u\<close> of a forward edge \<open>(u, Suc u)\<close>, hence strictly positive.
  So a loop step's batch keys avoid \<open>0\<close>: once the sole pivot \<open>0\<close> is pulled out of
  the partition it is never pushed back.  This is the frontier-monotonicity fact
  behind pivot settledness on the unit-out-degree path --- the loop can advance the
  frontier but can never return it to the source band.\<close>

lemma path_k_relax_in_bound_keys_pos:
  "0 \<notin> fst ` set (bpi.edge_relaxation_pairs_in_bound d U L B')"
proof -
  have setU: "set (bpi.edge_list_of (bpi.outgoing_edges U)) = bpi.outgoing_edges U"
    by (rule bpi.edge_list_of_properties(1)[OF bpi.finite_outgoing_edges])
  have tgt_pos: "\<And>u v. (u, v) \<in> bpi.outgoing_edges U \<Longrightarrow> 0 < v"
  proof -
    fix u v assume "(u, v) \<in> bpi.outgoing_edges U"
    then have "(u, v) \<in> path_k_E k"
      unfolding bpi.outgoing_edges_def by auto
    then have "v = Suc u" by (simp add: path_k_E_iff)
    then show "0 < v" by simp
  qed
  show ?thesis
  proof
    assume "0 \<in> fst ` set (bpi.edge_relaxation_pairs_in_bound d U L B')"
    then obtain val where
      "(0, val) \<in> set (bpi.edge_relaxation_pairs_in_bound d U L B')"
      by auto
    then obtain u v where uv: "(u, v) \<in> bpi.outgoing_edges U" and v0: "v = 0"
      unfolding bpi.edge_relaxation_pairs_in_bound_def
      using setU by auto
    from tgt_pos[OF uv] v0 show False by simp
  qed
qed

text \<open>The same frontier-positivity for the \<open>between\<close> relaxation batch: every
  pushed key is an edge target \<open>Suc u > 0\<close>.\<close>
lemma path_k_relax_between_keys_pos:
  "0 \<notin> fst ` set (bpi.edge_relaxation_pairs_between d U L H)"
proof -
  have setU: "set (bpi.edge_list_of (bpi.outgoing_edges U)) = bpi.outgoing_edges U"
    by (rule bpi.edge_list_of_properties(1)[OF bpi.finite_outgoing_edges])
  have tgt_pos: "\<And>u v. (u, v) \<in> bpi.outgoing_edges U \<Longrightarrow> 0 < v"
  proof -
    fix u v assume "(u, v) \<in> bpi.outgoing_edges U"
    then have "(u, v) \<in> path_k_E k"
      unfolding bpi.outgoing_edges_def by auto
    then have "v = Suc u" by (simp add: path_k_E_iff)
    then show "0 < v" by simp
  qed
  show ?thesis
  proof
    assume "0 \<in> fst ` set (bpi.edge_relaxation_pairs_between d U L H)"
    then obtain val where
      "(0, val) \<in> set (bpi.edge_relaxation_pairs_between d U L H)"
      by auto
    then obtain u v where uv: "(u, v) \<in> bpi.outgoing_edges U" and v0: "v = 0"
      unfolding bpi.edge_relaxation_pairs_between_def
      using setU by auto
    from tgt_pos[OF uv] v0 show False by simp
  qed
qed

text \<open>
  \<^bold>\<open>Block frontier.\<close>  Relaxing the block \<open>{a..<a+p}\<close> across its single boundary
  edge \<open>(a+p-1, a+p)\<close> pushes exactly the next frontier vertex \<open>a+p\<close>; the lower
  and source batches are empty.  Hence the partition advances \<open>{a} \<mapsto> {a+p}\<close>.\<close>

lemma path_k_block_next_keys:
  assumes apk: "a + p \<le> k" and ppos: "0 < p"
  shows "keys_of (batch_min_update (bpi.label_partition_view (pk.dist 0) {} :: nat partition_view)
      (bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
         (bpi.range_tree {a} (real a) (Fin (real (a+p)))) (real (a+p)) (Fin (real (Suc k))) @
       bpi.edge_relaxation_pairs_between (pk.dist 0)
         (bpi.range_tree {a} (real a) (Fin (real (a+p)))) (real (a+p)) (real (a+p)) @
       bpi.label_pairs_between (pk.dist 0) {a} (real (a+p)) (real (a+p)))) = {a+p}"
proof -
  let ?U = "bpi.range_tree {a} (real a) (Fin (real (a+p)))"
  have outset: "set (bpi.edge_list_of (bpi.outgoing_edges ?U)) = bpi.outgoing_edges ?U"
    by (rule bpi.edge_list_of_properties(1)[OF bpi.finite_outgoing_edges])
  have Ueq: "?U = {a..<a+p}" by (rule path_k_range_block[OF apk])
  have direct_fst:
    "fst ` set (bpi.edge_relaxation_pairs_in_bound (pk.dist 0) ?U (real (a+p)) (Fin (real (Suc k)))) = {a+p}"
  proof -
    have "set (bpi.edge_relaxation_pairs_in_bound (pk.dist 0) ?U (real (a+p)) (Fin (real (Suc k))))
        = (\<lambda>(u,v). (v, pk.dist 0 u + path_k_weight k u v)) `
            {e \<in> bpi.outgoing_edges ?U. real (a+p) \<le> pk.dist 0 (fst e) + path_k_weight k (fst e) (snd e)
               \<and> pk.dist 0 (fst e) + path_k_weight k (fst e) (snd e) < real (Suc k)}"
      unfolding bpi.edge_relaxation_pairs_in_bound_def using outset
      by (auto split: prod.splits)
    moreover have "{e \<in> bpi.outgoing_edges ?U. real (a+p) \<le> pk.dist 0 (fst e) + path_k_weight k (fst e) (snd e)
               \<and> pk.dist 0 (fst e) + path_k_weight k (fst e) (snd e) < real (Suc k)} = {(a+p-1, a+p)}"
      using apk ppos Ueq
      by (auto simp: bpi.outgoing_edges_def path_k_E_iff path_k_weight_def path_k_dist_eq of_nat_less_iff)
    ultimately show ?thesis using ppos by auto
  qed
  have lower: "bpi.edge_relaxation_pairs_between (pk.dist 0) ?U (real (a+p)) (real (a+p)) = []"
    unfolding bpi.edge_relaxation_pairs_between_def by (auto simp: filter_empty_conv)
  have src: "bpi.label_pairs_between (pk.dist 0) {a} (real (a+p)) (real (a+p)) = []"
    unfolding bpi.label_pairs_between_def by (simp add: filter_empty_conv)
  show ?thesis
    using direct_fst lower src by (simp add: batch_min_update_keys image_Un)
qed

lemma path_k_base_top:
  fixes p q cap :: nat and d :: "nat \<Rightarrow> real"
  assumes pk_le: "p \<le> k" and ppos: "0 < p"
  shows "bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap 0 d {0} (Fin (real (Suc k)))
      (\<lambda>v. if v \<in> pk.base_case_vertices p 0 (Fin (real (Suc k))) then pk.dist 0 v else d v)
      (Fin (real p)) {0..<p}
      (bpi.base_case_scan_cost (Suc 0) p 0 (Fin (real (Suc k))))"
proof -
  let ?xs = "pk.base_case_order 0 (Fin (real (Suc k)))"
  have order: "?xs = [0..<Suc k]" by (rule path_k_base_order)
  have len: "length ?xs = Suc k" using order by simp
  have not_le: "\<not> length ?xs \<le> p" using len pk_le by simp
  have nthp: "?xs ! p = p" using order pk_le by (simp add: nth_append)
  have distp: "pk.dist 0 (?xs ! p) = real p"
    using nthp pk_le by (simp add: path_k_dist_eq)
  have vert: "pk.base_case_vertices p 0 (Fin (real (Suc k))) = {0..<p}"
  proof -
    have take_eq: "take (Suc p) ?xs = [0..<Suc p]"
      using order pk_le by (simp add: take_upt del: upt_Suc)
    have setp: "set (take (Suc p) ?xs) = {0..p}"
      using take_eq by auto
    have dvals: "\<And>v. v \<le> p \<Longrightarrow> pk.dist 0 v = real v"
      using pk_le by (intro path_k_dist_eq) simp
    have "pk.base_case_vertices p 0 (Fin (real (Suc k)))
        = {v \<in> set (take (Suc p) ?xs). pk.dist 0 v < pk.dist 0 (?xs ! p)}"
      using not_le unfolding pk.base_case_vertices_def by (simp add: Let_def)
    also have "\<dots> = {v \<in> {0..p}. real v < real p}"
      using setp distp dvals by (auto simp: atLeastAtMost_iff)
    also have "\<dots> = {0..<p}"
      by (auto simp only: of_nat_less_iff atLeastLessThan_iff atLeastAtMost_iff)
    finally show ?thesis .
  qed
  have bnd: "pk.base_case_bound p 0 (Fin (real (Suc k))) = Fin (real p)"
    using not_le distp unfolding pk.base_case_bound_def by (simp add: Let_def)
  show ?thesis
    using bpi.Charged_Direct_Insert_Base[OF refl, where \<Delta>="Suc 0"
        and M_of="bmssp_level_cap p q" and t=q and h=p and k=p and cap=cap
        and d=d and x=0 and B="Fin (real (Suc k))"]
    by (simp only: vert bnd)
qed

text \<open>
  \<^bold>\<open>Generic block base step.\<close>  From any band start \<open>a\<close> with \<open>a + p \<le> k\<close>, the
  level-0 base call on \<open>{a}\<close> below the full bound settles exactly the block
  \<open>{a..<a+p}\<close> and advances the returned bound to \<^term>\<open>Fin (real (a+p))\<close>.
  Iterating this brick over \<open>a = 0, p, 2p, \<dots>\<close> is the multi-step frontier walk.\<close>

lemma path_k_base_block:
  fixes a p q cap :: nat and d :: "nat \<Rightarrow> real"
  assumes apk: "a + p \<le> k" and ppos: "0 < p"
  shows "bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap 0 d {a} (Fin (real (Suc k)))
      (\<lambda>v. if v \<in> pk.base_case_vertices p a (Fin (real (Suc k))) then pk.dist 0 v else d v)
      (Fin (real (a + p))) {a..<a+p}
      (bpi.base_case_scan_cost (Suc 0) p a (Fin (real (Suc k))))"
proof -
  let ?xs = "pk.base_case_order a (Fin (real (Suc k)))"
  have ak: "a \<le> k" using apk by simp
  have order: "?xs = [a..<Suc k]" by (rule path_k_base_order)
  have len: "length ?xs = Suc k - a" using order ak by simp
  have not_le: "\<not> length ?xs \<le> p" using len apk by simp
  have nthp: "?xs ! p = a + p" using order apk by (auto simp add: nth_append)
  have distp: "pk.dist 0 (?xs ! p) = real (a + p)"
    using nthp apk by (simp add: path_k_dist_eq)
  have vert: "pk.base_case_vertices p a (Fin (real (Suc k))) = {a..<a+p}"
  proof -
    have take_eq: "take (Suc p) ?xs = [a..<Suc (a + p)]"
      using order apk by (simp add: take_upt del: upt_Suc)
    have setp: "set (take (Suc p) ?xs) = {a..a+p}"
      using take_eq by auto
    have dvals: "\<And>v. v \<le> a + p \<Longrightarrow> pk.dist 0 v = real v"
      using apk by (intro path_k_dist_eq) simp
    have "pk.base_case_vertices p a (Fin (real (Suc k)))
        = {v \<in> set (take (Suc p) ?xs). pk.dist 0 v < pk.dist 0 (?xs ! p)}"
      using not_le unfolding pk.base_case_vertices_def by (simp add: Let_def)
    also have "\<dots> = {v \<in> {a..a+p}. real v < real (a + p)}"
      using setp distp dvals by (auto simp: atLeastAtMost_iff)
    also have "\<dots> = {a..<a+p}"
      by (auto simp only: of_nat_less_iff atLeastLessThan_iff atLeastAtMost_iff)
    finally show ?thesis .
  qed
  have bnd: "pk.base_case_bound p a (Fin (real (Suc k))) = Fin (real (a + p))"
    using not_le distp unfolding pk.base_case_bound_def by (simp add: Let_def)
  show ?thesis
    using bpi.Charged_Direct_Insert_Base[OF refl, where \<Delta>="Suc 0"
        and M_of="bmssp_level_cap p q" and t=q and h=p and k=p and cap=cap
        and d=d and x=a and B="Fin (real (Suc k))"]
    by (simp only: vert bnd)
qed

text \<open>\<^bold>\<open>Terminal block.\<close>  When the residual band \<open>{a..k}\<close> fits within \<open>p\<close>, the
  base call below the full bound covers it whole and keeps the bound, settling
  the loop.\<close>

lemma path_k_base_last:
  fixes a p q cap :: nat and d :: "nat \<Rightarrow> real"
  assumes ak: "a \<le> k" and ple: "Suc k - a \<le> p"
  shows "bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap 0 d {a} (Fin (real (Suc k)))
      (\<lambda>v. if v \<in> pk.base_case_vertices p a (Fin (real (Suc k))) then pk.dist 0 v else d v)
      (Fin (real (Suc k))) {a..k}
      (bpi.base_case_scan_cost (Suc 0) p a (Fin (real (Suc k))))"
proof -
  have bt: "pk.bound_tree {a} (Fin (real (Suc k))) = {a..k}"
    by (auto simp: path_k_bound_tree_band of_nat_less_iff atLeastAtMost_iff)
  have ord: "pk.base_case_order a (Fin (real (Suc k))) = [a..<Suc k]"
    by (rule path_k_base_order)
  have len: "length (pk.base_case_order a (Fin (real (Suc k)))) \<le> p"
    using ord ak ple by simp
  have U: "pk.base_case_vertices p a (Fin (real (Suc k))) = {a..k}"
    using pk.base_case_success[OF len] bt by simp
  have bnd: "pk.base_case_bound p a (Fin (real (Suc k))) = Fin (real (Suc k))"
    using len by (simp add: pk.base_case_bound_def)
  show ?thesis
    using bpi.Charged_Direct_Insert_Base[OF refl, where \<Delta>="Suc 0"
        and M_of="bmssp_level_cap p q" and t=q and h=p and k=p and cap=cap
        and d=d and x=a and B="Fin (real (Suc k))"]
    by (simp only: U bnd)
qed

text \<open>
  \<^bold>\<open>Level-0 whole-path cover (fanout regime).\<close>  When the FindPivots round count
  \<open>p\<close> already dominates the \<^term>\<open>Suc k\<close> path vertices, a single level-0 base call
  on \<open>{0}\<close> below \<^term>\<open>Fin (real (Suc k))\<close> settles the entire band \<open>{0..k}\<close>: the
  bounded tree has card \<open>Suc k \<le> p\<close>, so the capped scan keeps it whole and the
  bound is preserved.  This is the genuine level-0 child the cover lift needs.\<close>

lemma path_k_zero_cover:
  fixes p q cap :: nat and d :: "nat \<Rightarrow> real"
  assumes small: "Suc k \<le> p"
  shows "\<exists>d' U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap 0 d {0} (Fin (real (Suc k)))
      d' (Fin (real (Suc k))) U c"
proof -
  have card_le: "card (pk.bound_tree {0} (Fin (real (Suc k)))) \<le> p"
  proof -
    have "pk.bound_tree {0} (Fin (real (Suc k))) = {0..k}"
      by (auto simp: path_k_bound_tree_band of_nat_less_iff atLeastAtMost_iff)
    then have "card (pk.bound_tree {0} (Fin (real (Suc k)))) = Suc k" by simp
    then show ?thesis using small by simp
  qed
  show "\<exists>d' U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap 0 d {0} (Fin (real (Suc k)))
      d' (Fin (real (Suc k))) U c"
    using bpi.charged_bmssp_zero_full_cover[OF refl card_le,
        where \<Delta>="Suc 0" and M_of="bmssp_level_cap p q" and t=q and cap=cap and d=d]
    by blast
qed

text \<open>
  \<^bold>\<open>Level-1 base (fanout regime).\<close>  Lifting the level-0 whole cover by one pull
  gives the level-1 whole-path cover required as the base of @{thm [source]
  path_k_cover_ge1}, whenever \<open>p\<close> dominates the path.\<close>

lemma path_k_base1:
  fixes p q cap :: nat and d :: "nat \<Rightarrow> real"
  assumes pk_le: "p \<le> k" and cover: "Suc k \<le> cap" and ppos: "0 < p"
    and small: "Suc k \<le> p"
    and sound: "pk.sound_label d" and d0: "d 0 = 0"
    and pre0: "pk.bmssp_pre_full d {0} Infinity"
  shows "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap (Suc 0) d {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U c"
proof -
  let ?B = "Fin (real (Suc k))"
  let ?d2 = "bpi.find_pivots_label_capped p cap d {0} ?B"
  let ?P = "bpi.find_pivots_pivots_capped p cap d {0} ?B"
  have reaches0: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have P0: "?P = {0}" by (rule path_k_source_is_sole_pivot_fin[OF pk_le cover d0 sound])
  have sound2: "pk.sound_label ?d2"
    unfolding bpi.find_pivots_label_capped_def
    by (rule bpi.fp_iter_capped_label_sound[OF sound reaches0])
  have le2: "?d2 0 \<le> d 0" by (rule bpi.find_pivots_label_capped_le)
  have d2_0: "?d2 0 = 0"
  proof -
    have "pk.dist 0 0 \<le> ?d2 0" using sound2 pk.source_in_V pk.reachable_refl[OF pk.source_in_V]
      unfolding pk.sound_label_def by blast
    moreover have "pk.dist 0 0 = 0" by (rule pk.dist_refl_zero[OF pk.source_in_V])
    ultimately show ?thesis using le2 d0 by simp
  qed
  have pre2: "pk.bmssp_pre_full ?d2 {0} ?B"
  proof -
    have preB: "pk.bmssp_pre_full d {0} ?B"
      using pre0 unfolding pk.bmssp_pre_full_def by auto
    show ?thesis
      by (rule bpi.find_pivots_label_capped_preserves_source_pre[OF sound preB reaches0])
  qed
  obtain d_c U_c c_c where childrun:
    "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap 0
       ?d2 {0} ?B d_c ?B U_c c_c"
    using path_k_zero_cover[OF small] by blast
  have Mpos: "0 < bmssp_level_cap p q 0" using ppos by (simp add: bmssp_level_cap_def)
  have pull: "pull_separates (bpi.label_partition_view ?d2 {0}) (bmssp_level_cap p q 0)
      (real (Suc k)) {0} (real (Suc k)) (bpi.label_partition_view ?d2 {} :: nat partition_view)"
    unfolding pull_separates_def bpi.label_partition_view_def
    using Mpos d2_0 by simp
  have split: "{0} = bpi.split_below ?d2 {0} (real (Suc k))"
    using d2_0 by (auto simp: bpi.split_below_def)
  have small_tree: "card (pk.bound_tree {0} (Fin 0)) < p * cap"
  proof -
    have "pk.bound_tree {0} (Fin 0) = {}" by (rule path_k_bound_tree_source_Fin0_empty)
    moreover have "0 < p * cap" using ppos cover by simp
    ultimately show ?thesis by simp
  qed
  have tail_empty:
    "keys_of (batch_min_update (bpi.label_partition_view ?d2 {} :: nat partition_view)
       (bpi.edge_relaxation_pairs_in_bound d_c
          (bpi.range_tree {0} 0 ?B) (real (Suc k)) ?B @
        bpi.edge_relaxation_pairs_between d_c
          (bpi.range_tree {0} 0 ?B) (real (Suc k)) (real (Suc k)) @
        bpi.label_pairs_between ?d2 {0} (real (Suc k)) (real (Suc k)))) = {}"
  proof -
    have lower: "bpi.edge_relaxation_pairs_between d_c
        (bpi.range_tree {0} 0 ?B) (real (Suc k)) (real (Suc k)) = []"
      unfolding bpi.edge_relaxation_pairs_between_def
      by (auto simp: filter_empty_conv split: prod.splits)
    have src: "bpi.label_pairs_between ?d2 {0} (real (Suc k)) (real (Suc k)) = []"
      unfolding bpi.label_pairs_between_def by (simp add: filter_empty_conv)
    have direct: "bpi.edge_relaxation_pairs_in_bound d_c
        (bpi.range_tree {0} 0 ?B) (real (Suc k)) ?B = []"
      unfolding bpi.edge_relaxation_pairs_in_bound_def by (auto simp: filter_empty_conv)
    show ?thesis using lower src direct unfolding batch_min_update_def by simp
  qed
  have loop:
    "\<exists>betas bs charged_Us child_outputs U c child_costs.
       bpi.charged_direct_insert_costed_partition_loop_state (Suc 0)
         (bmssp_level_cap p q) q p p cap 0 ?d2 {0} ?B (pk.dist 0)
         (bpi.label_partition_view ?d2 {0}) 0 betas bs ?B charged_Us child_outputs U c child_costs"
    by (rule bpi.charged_loop_single_step_then_done_exists_dist
        [where Bmax = "real (Suc k)" and beta = "real (Suc k)" and b = "real (Suc k)"
          and S_pull = "{0}" and D_pull = "bpi.label_partition_view ?d2 {} :: nat partition_view"
          and d_child = "d_c" and U_child = U_c and c_child = c_c])
      (use pull pre2 split reaches0 small_tree childrun tail_empty in simp_all)
  then obtain betas bs charged_Us child_outputs U c child_costs where looprun:
    "bpi.charged_direct_insert_costed_partition_loop_state (Suc 0)
       (bmssp_level_cap p q) q p p cap 0 ?d2 {0} ?B (pk.dist 0)
       (bpi.label_partition_view ?d2 {0}) 0 betas bs ?B charged_Us child_outputs U c child_costs"
    by blast
  let ?U = "U \<union> {v \<in> pk.bound_tree {0} ?B. ?d2 v = pk.dist 0 v}"
  have run: "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap
      (Suc 0) d {0} ?B (pk.dist 0) ?B ?U
      (bpi.fp_iter_capped_scan_cost p cap d {0} {0} ?B + 0 + c)"
    by (rule bpi.charged_direct_insert_costed_bmssp_step_with_insert_cost
        [where D = "bpi.label_partition_view ?d2 {0}" and c_insert = 0])
      (use looprun P0 in \<open>simp_all add: bpi.partition_initial_insert_cost_bound_def pk.complete_on_def\<close>)
  show ?thesis using run by blast
qed

text \<open>
  \<^bold>\<open>Level-1 base in the genuine \<open>p \<le> k\<close> regime (empty-band / free-prefix
  construction).\<close>  Unlike @{thm [source] path_k_base1}, which needs the round
  count to dominate the path (\<open>Suc k \<le> p\<close>), this builds a level-1 whole-path
  cover for \<^emph>\<open>any\<close> \<open>p \<le> k\<close>.  The permissive charged loop is started at the band
  \<open>a = p\<close> (claiming the already-settled prefix \<open>{0..<p}\<close> via the true-distance
  output label), pulls the sole pivot \<open>{0}\<close>, runs a single level-0 base child
  that returns @{term "Fin (real p)"}, and finishes over the \<^emph>\<open>empty\<close> band
  \<open>{p..<p}\<close>: with \<open>a = b = p\<close> the range tree is empty, so the relaxation pushes
  nothing and the residual partition is empty, giving an immediate \<open>Done\<close> back
  at the input bound @{term "Fin (real (Suc k))"}.  This is the level-1 base the
  cover chain @{thm [source] path_k_cover_ge1} consumes.\<close>
lemma path_k_base1_general:
  fixes p q cap :: nat and d :: "nat \<Rightarrow> real"
  assumes pk_le: "p \<le> k" and cover: "Suc k \<le> cap" and ppos: "0 < p"
    and capgt: "1 < cap"
    and sound: "pk.sound_label d" and d0: "d 0 = 0"
    and pre0: "pk.bmssp_pre_full d {0} Infinity"
  shows "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap (Suc 0) d {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U c"
proof -
  let ?B = "Fin (real (Suc k))"
  let ?d2 = "bpi.find_pivots_label_capped p cap d {0} ?B"
  let ?P = "bpi.find_pivots_pivots_capped p cap d {0} ?B"
  let ?dc = "\<lambda>v. if v \<in> pk.base_case_vertices p 0 ?B then pk.dist 0 v else ?d2 v"
  have reaches0: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have P0: "?P = {0}" by (rule path_k_source_is_sole_pivot_fin[OF pk_le cover d0 sound])
  have sound2: "pk.sound_label ?d2"
    unfolding bpi.find_pivots_label_capped_def
    by (rule bpi.fp_iter_capped_label_sound[OF sound reaches0])
  have le2: "?d2 0 \<le> d 0" by (rule bpi.find_pivots_label_capped_le)
  have d2_0: "?d2 0 = 0"
  proof -
    have "pk.dist 0 0 \<le> ?d2 0" using sound2 pk.source_in_V pk.reachable_refl[OF pk.source_in_V]
      unfolding pk.sound_label_def by blast
    moreover have "pk.dist 0 0 = 0" by (rule pk.dist_refl_zero[OF pk.source_in_V])
    ultimately show ?thesis using le2 d0 by simp
  qed
  have pre2: "pk.bmssp_pre_full ?d2 {0} ?B"
  proof -
    have preB: "pk.bmssp_pre_full d {0} ?B"
      using pre0 unfolding pk.bmssp_pre_full_def by auto
    show ?thesis
      by (rule bpi.find_pivots_label_capped_preserves_source_pre[OF sound preB reaches0])
  qed
  have childrun:
    "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap 0
       ?d2 {0} ?B ?dc (Fin (real p)) {0..<p}
       (bpi.base_case_scan_cost (Suc 0) p 0 ?B)"
    by (rule path_k_base_top[OF pk_le ppos])
  have Mpos: "0 < bmssp_level_cap p q 0" using ppos by (simp add: bmssp_level_cap_def)
  have pull: "pull_separates (bpi.label_partition_view ?d2 {0}) (bmssp_level_cap p q 0)
      (real (Suc k)) {0} (real (Suc k)) (bpi.label_partition_view ?d2 {} :: nat partition_view)"
    unfolding pull_separates_def bpi.label_partition_view_def
    using Mpos d2_0 by simp
  have split: "{0} = bpi.split_below ?d2 {0} (real (Suc k))"
    using d2_0 by (auto simp: bpi.split_below_def)
  have rt_empty: "bpi.range_tree {0} (real p) (Fin (real p)) = {}"
    by (auto simp: bpi.range_tree_def)
  have small_tree: "card (pk.bound_tree {0} (Fin (real p))) < p * cap"
  proof -
    have "pk.bound_tree {0} (Fin (real p)) = {0..<p}"
      using pk_le by (auto simp: path_k_bound_tree_band of_nat_less_iff atLeast0LessThan)
    then have "card (pk.bound_tree {0} (Fin (real p))) = p" by simp
    moreover have "p < p * cap" using ppos capgt by simp
    ultimately show ?thesis by simp
  qed
  have tail_empty:
    "keys_of (batch_min_update (bpi.label_partition_view ?d2 {} :: nat partition_view)
       (bpi.edge_relaxation_pairs_in_bound ?dc
          (bpi.range_tree {0} (real p) (Fin (real p))) (real (Suc k)) ?B @
        bpi.edge_relaxation_pairs_between ?dc
          (bpi.range_tree {0} (real p) (Fin (real p))) (real p) (real (Suc k)) @
        bpi.label_pairs_between ?d2 {0} (real p) (real (Suc k)))) = {}"
  proof -
    have el: "bpi.edge_list_of (bpi.outgoing_edges {}) = []"
    proof -
      have "set (bpi.edge_list_of (bpi.outgoing_edges {})) = bpi.outgoing_edges {}"
        by (rule bpi.edge_list_of_properties(1)[OF bpi.finite_outgoing_edges])
      then show ?thesis by (simp add: bpi.outgoing_edges_def)
    qed
    have direct: "bpi.edge_relaxation_pairs_in_bound ?dc
        (bpi.range_tree {0} (real p) (Fin (real p))) (real (Suc k)) ?B = []"
      using rt_empty el by (simp add: bpi.edge_relaxation_pairs_in_bound_def)
    have lower: "bpi.edge_relaxation_pairs_between ?dc
        (bpi.range_tree {0} (real p) (Fin (real p))) (real p) (real (Suc k)) = []"
      using rt_empty el by (simp add: bpi.edge_relaxation_pairs_between_def)
    have src: "bpi.label_pairs_between ?d2 {0} (real p) (real (Suc k)) = []"
    proof -
      have fin: "finite (keys_of (bpi.label_partition_view ?d2 {0}))" by simp
      have "set (partition_key_order (bpi.label_partition_view ?d2 {0})) = {0}"
        using partition_key_order_properties(1)[OF fin] by simp
      then show ?thesis
        unfolding bpi.label_pairs_between_def using d2_0 ppos
        by (simp add: filter_empty_conv)
    qed
    show ?thesis using direct lower src unfolding batch_min_update_def by simp
  qed
  have loop:
    "\<exists>betas bs charged_Us child_outputs U c child_costs.
       bpi.charged_direct_insert_costed_partition_loop_state (Suc 0)
         (bmssp_level_cap p q) q p p cap 0 ?d2 {0} ?B (pk.dist 0)
         (bpi.label_partition_view ?d2 {0}) (real p) betas bs ?B charged_Us child_outputs U c child_costs"
    by (rule bpi.charged_loop_single_step_then_done_exists_dist
        [where Bmax = "real (Suc k)" and beta = "real (Suc k)" and b = "real p"
          and a = "real p" and S_pull = "{0}"
          and D_pull = "bpi.label_partition_view ?d2 {} :: nat partition_view"
          and d_child = ?dc and U_child = "{0..<p}"
          and c_child = "bpi.base_case_scan_cost (Suc 0) p 0 ?B"])
      (use pull pre2 split reaches0 small_tree childrun tail_empty pk_le in simp_all)
  then obtain betas bs charged_Us child_outputs U c child_costs where looprun:
    "bpi.charged_direct_insert_costed_partition_loop_state (Suc 0)
       (bmssp_level_cap p q) q p p cap 0 ?d2 {0} ?B (pk.dist 0)
       (bpi.label_partition_view ?d2 {0}) (real p) betas bs ?B charged_Us child_outputs U c child_costs"
    by blast
  let ?U = "U \<union> {v \<in> pk.bound_tree {0} ?B. ?d2 v = pk.dist 0 v}"
  have run: "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap
      (Suc 0) d {0} ?B (pk.dist 0) ?B ?U
      (bpi.fp_iter_capped_scan_cost p cap d {0} {0} ?B + 0 + c)"
    by (rule bpi.charged_direct_insert_costed_bmssp_step_with_insert_cost
        [where D = "bpi.label_partition_view ?d2 {0}" and c_insert = 0])
      (use looprun P0 in \<open>simp_all add: bpi.partition_initial_insert_cost_bound_def pk.complete_on_def\<close>)
  show ?thesis using run by blast
qed

text \<open>
  \<^bold>\<open>Milestone B1, discharged: a charged top-level cost exists on \<open>P\<^sub>k\<close> at the
  inflated schedule.\<close>  Stacking the empty-band level-1 base
  @{thm [source] path_k_base1_general} through the cover chain
  @{thm [source] path_k_cover_ge1} to level \<open>p - 1\<close> supplies the single charged
  child run (conjunct 6) that the source-pivot reduction
  @{thm [source] path_k_charged_cost_exists_if_child} turns into a charged
  top-level cost --- with \<^emph>\<open>no\<close> run-existence assumption, in the genuine
  \<open>2 \<le> p \<le> k\<close> regime where the cap covers the path.\<close>
theorem path_k_charged_cost_exists:
  assumes pk_le: "sssp_log_one_third_param N \<le> k"
    and cover: "Suc k \<le> bmssp_level_cap (sssp_log_one_third_param N)
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)"
    and p2: "2 \<le> sssp_log_one_third_param N"
  shows "\<exists>c. bpi.charged_direct_insert_top_level_cost 1 N c"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  let ?d_fp = "bpi.find_pivots_label_capped ?p ?cap pk.finite_initial_label {0} Infinity"
  have ppos: "0 < ?p" using p2 by simp
  have capge: "?p \<le> ?cap" by (rule bmssp_level_cap_ge_level)
  have capgt: "1 < ?cap" using p2 capge by simp
  have base1: "\<And>d. pk.sound_label d \<Longrightarrow> d 0 = 0 \<Longrightarrow> pk.bmssp_pre_full d {0} Infinity \<Longrightarrow>
      \<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap
        (Suc 0) d {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k))) U c"
    by (rule path_k_base1_general[OF pk_le cover ppos capgt])
  have allr: "\<And>v. v \<in> path_k_V k \<Longrightarrow> pk.reachable 0 v" by (rule path_k_all_reachable)
  have reaches0: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have fsound: "pk.sound_label pk.finite_initial_label"
    by (rule pk.finite_initial_label_sound[OF allr])
  have sc: "pk.finite_initial_label 0 = pk.dist 0 0"
    by (rule pk.finite_initial_label_source_complete)
  have pre0: "pk.bmssp_pre_full pk.finite_initial_label {0} Infinity"
    by (rule pk.top_bmssp_pre_full) (use allr sc in auto)
  have dfp_sound: "pk.sound_label ?d_fp"
    unfolding bpi.find_pivots_label_capped_def
    by (rule bpi.fp_iter_capped_label_sound[OF fsound reaches0])
  have dfp_pre: "pk.bmssp_pre_full ?d_fp {0} Infinity"
    by (rule bpi.find_pivots_label_capped_preserves_source_pre[OF fsound pre0 reaches0])
  have dfp_0: "?d_fp 0 = 0"
  proof -
    have "pk.dist 0 0 \<le> ?d_fp 0"
      using dfp_sound pk.source_in_V pk.reachable_refl[OF pk.source_in_V]
      unfolding pk.sound_label_def by blast
    moreover have "?d_fp 0 \<le> pk.finite_initial_label 0"
      by (rule bpi.find_pivots_label_capped_le)
    moreover have "pk.finite_initial_label 0 = 0"
      using sc pk.dist_refl_zero[OF pk.source_in_V] by simp
    moreover have "pk.dist 0 0 = 0" by (rule pk.dist_refl_zero[OF pk.source_in_V])
    ultimately show ?thesis by simp
  qed
  have chain: "\<And>d. pk.sound_label d \<Longrightarrow> d 0 = 0 \<Longrightarrow> pk.bmssp_pre_full d {0} Infinity \<Longrightarrow>
      \<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap
        (Suc (?p - 2)) d {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k))) U c"
    by (rule path_k_cover_ge1[OF pk_le cover ppos base1])
  have child: "\<exists>U_child c_child. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap (?p - 1) ?d_fp {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U_child c_child"
  proof -
    have pe: "Suc (?p - 2) = ?p - 1" using p2 by simp
    show ?thesis using chain[OF dfp_sound dfp_0 dfp_pre] pe by simp
  qed
  show ?thesis
    by (rule path_k_charged_cost_exists_if_child[OF pk_le cover child])
qed


text \<open>
  \<^bold>\<open>Cost-bounded level-1 base.\<close>  The cost-tracking twin of
  @{thm [source] path_k_base1_general}: the level-1 charged run built by the
  empty-band single-step-then-Done loop has cost exactly one FindPivots scan plus
  one base-case scan, hence at most @{term "p * bpi.edge_count + p"}.  All four
  partition costs and the Done tail are zero, so no edge-range or chain terms
  enter --- this is what keeps the cheap run polylogarithmic.
\<close>

lemma path_k_base1_costed:
  fixes p q cap :: nat and d :: "nat \<Rightarrow> real"
  assumes pk_le: "p \<le> k" and cover: "Suc k \<le> cap" and ppos: "0 < p"
    and capgt: "1 < cap"
    and sound: "pk.sound_label d" and d0: "d 0 = 0"
    and pre0: "pk.bmssp_pre_full d {0} Infinity"
  shows "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap (Suc 0) d {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U c
      \<and> c \<le> p * bpi.edge_count + p"
proof -
  let ?B = "Fin (real (Suc k))"
  let ?d2 = "bpi.find_pivots_label_capped p cap d {0} ?B"
  let ?P = "bpi.find_pivots_pivots_capped p cap d {0} ?B"
  let ?dc = "\<lambda>v. if v \<in> pk.base_case_vertices p 0 ?B then pk.dist 0 v else ?d2 v"
  have reaches0: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have P0: "?P = {0}" by (rule path_k_source_is_sole_pivot_fin[OF pk_le cover d0 sound])
  have sound2: "pk.sound_label ?d2"
    unfolding bpi.find_pivots_label_capped_def
    by (rule bpi.fp_iter_capped_label_sound[OF sound reaches0])
  have le2: "?d2 0 \<le> d 0" by (rule bpi.find_pivots_label_capped_le)
  have d2_0: "?d2 0 = 0"
  proof -
    have "pk.dist 0 0 \<le> ?d2 0" using sound2 pk.source_in_V pk.reachable_refl[OF pk.source_in_V]
      unfolding pk.sound_label_def by blast
    moreover have "pk.dist 0 0 = 0" by (rule pk.dist_refl_zero[OF pk.source_in_V])
    ultimately show ?thesis using le2 d0 by simp
  qed
  have pre2: "pk.bmssp_pre_full ?d2 {0} ?B"
  proof -
    have preB: "pk.bmssp_pre_full d {0} ?B"
      using pre0 unfolding pk.bmssp_pre_full_def by auto
    show ?thesis
      by (rule bpi.find_pivots_label_capped_preserves_source_pre[OF sound preB reaches0])
  qed
  have childrun:
    "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap 0
       ?d2 {0} ?B ?dc (Fin (real p)) {0..<p}
       (bpi.base_case_scan_cost (Suc 0) p 0 ?B)"
    by (rule path_k_base_top[OF pk_le ppos])
  have Mpos: "0 < bmssp_level_cap p q 0" using ppos by (simp add: bmssp_level_cap_def)
  have pull: "pull_separates (bpi.label_partition_view ?d2 {0}) (bmssp_level_cap p q 0)
      (real (Suc k)) {0} (real (Suc k)) (bpi.label_partition_view ?d2 {} :: nat partition_view)"
    unfolding pull_separates_def bpi.label_partition_view_def
    using Mpos d2_0 by simp
  have split: "{0} = bpi.split_below ?d2 {0} (real (Suc k))"
    using d2_0 by (auto simp: bpi.split_below_def)
  have rt_empty: "bpi.range_tree {0} (real p) (Fin (real p)) = {}"
    by (auto simp: bpi.range_tree_def)
  have small_tree: "card (pk.bound_tree {0} (Fin (real p))) < p * cap"
  proof -
    have "pk.bound_tree {0} (Fin (real p)) = {0..<p}"
      using pk_le by (auto simp: path_k_bound_tree_band of_nat_less_iff atLeast0LessThan)
    then have "card (pk.bound_tree {0} (Fin (real p))) = p" by simp
    moreover have "p < p * cap" using ppos capgt by simp
    ultimately show ?thesis by simp
  qed
  have tail_empty:
    "keys_of (batch_min_update (bpi.label_partition_view ?d2 {} :: nat partition_view)
       (bpi.edge_relaxation_pairs_in_bound ?dc
          (bpi.range_tree {0} (real p) (Fin (real p))) (real (Suc k)) ?B @
        bpi.edge_relaxation_pairs_between ?dc
          (bpi.range_tree {0} (real p) (Fin (real p))) (real p) (real (Suc k)) @
        bpi.label_pairs_between ?d2 {0} (real p) (real (Suc k)))) = {}"
  proof -
    have el: "bpi.edge_list_of (bpi.outgoing_edges {}) = []"
    proof -
      have "set (bpi.edge_list_of (bpi.outgoing_edges {})) = bpi.outgoing_edges {}"
        by (rule bpi.edge_list_of_properties(1)[OF bpi.finite_outgoing_edges])
      then show ?thesis by (simp add: bpi.outgoing_edges_def)
    qed
    have direct: "bpi.edge_relaxation_pairs_in_bound ?dc
        (bpi.range_tree {0} (real p) (Fin (real p))) (real (Suc k)) ?B = []"
      using rt_empty el by (simp add: bpi.edge_relaxation_pairs_in_bound_def)
    have lower: "bpi.edge_relaxation_pairs_between ?dc
        (bpi.range_tree {0} (real p) (Fin (real p))) (real p) (real (Suc k)) = []"
      using rt_empty el by (simp add: bpi.edge_relaxation_pairs_between_def)
    have src: "bpi.label_pairs_between ?d2 {0} (real p) (real (Suc k)) = []"
    proof -
      have fin: "finite (keys_of (bpi.label_partition_view ?d2 {0}))" by simp
      have "set (partition_key_order (bpi.label_partition_view ?d2 {0})) = {0}"
        using partition_key_order_properties(1)[OF fin] by simp
      then show ?thesis
        unfolding bpi.label_pairs_between_def using d2_0 ppos
        by (simp add: filter_empty_conv)
    qed
    show ?thesis using direct lower src unfolding batch_min_update_def by simp
  qed
  have beta_bd: "bound_le (Fin (real (Suc k))) ?B" by simp
  have a_le_b: "(real p :: real) \<le> real p" by simp
  have a_bd: "bound_le (Fin (real p)) ?B" using pk_le by simp
  have reaches_ball: "\<forall>x\<in>{0::nat}. pk.reachable 0 x" using reaches0 by simp
  have looprun:
    "bpi.charged_direct_insert_costed_partition_loop_state (Suc 0)
       (bmssp_level_cap p q) q p p cap 0 ?d2 {0} ?B (pk.dist 0)
       (bpi.label_partition_view ?d2 {0}) (real p) [real (Suc k)] [real p] ?B
       (bpi.range_tree {0} (real p) (Fin (real p)) # [bpi.range_tree {0} (real p) ?B])
       [{0..<p}]
       (pk.bound_tree {0} (Fin (real p)) \<union>
          \<Union>(set (bpi.range_tree {0} (real p) (Fin (real p)) # [bpi.range_tree {0} (real p) ?B])))
       (bpi.base_case_scan_cost (Suc 0) p 0 ?B) [bpi.base_case_scan_cost (Suc 0) p 0 ?B]"
    by (rule bpi.charged_loop_single_step_then_done_costed_dist
        [where Bmax = "real (Suc k)" and beta = "real (Suc k)" and b = "real p"
          and a = "real p" and S_pull = "{0}"
          and D_pull = "bpi.label_partition_view ?d2 {} :: nat partition_view"
          and d_child = ?dc and U_child = "{0..<p}"
          and c_child = "bpi.base_case_scan_cost (Suc 0) p 0 ?B"])
      (use pull beta_bd pre2 split reaches_ball a_le_b a_bd small_tree childrun
        tail_empty a_bd in simp_all)
  let ?U = "(pk.bound_tree {0} (Fin (real p)) \<union>
          \<Union>(set (bpi.range_tree {0} (real p) (Fin (real p)) # [bpi.range_tree {0} (real p) ?B])))
       \<union> {v \<in> pk.bound_tree {0} ?B. ?d2 v = pk.dist 0 v}"
  have run: "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap
      (Suc 0) d {0} ?B (pk.dist 0) ?B ?U
      (bpi.fp_iter_capped_scan_cost p cap d {0} {0} ?B + 0
        + bpi.base_case_scan_cost (Suc 0) p 0 ?B)"
    by (rule bpi.charged_direct_insert_costed_bmssp_step_with_insert_cost
        [where D = "bpi.label_partition_view ?d2 {0}" and c_insert = 0])
      (use looprun P0 in \<open>simp_all add: bpi.partition_initial_insert_cost_bound_def pk.complete_on_def\<close>)
  have cost_le: "bpi.fp_iter_capped_scan_cost p cap d {0} {0} ?B + 0
        + bpi.base_case_scan_cost (Suc 0) p 0 ?B \<le> p * bpi.edge_count + p"
  proof -
    have fp: "bpi.fp_iter_capped_scan_cost p cap d {0} {0} ?B \<le> p * bpi.edge_count"
      by (rule bpi.fp_iter_capped_scan_cost_le_rounds)
    have base: "bpi.base_case_scan_cost (Suc 0) p 0 ?B \<le> p"
      using bpi.base_case_scan_cost_le[OF bpi.bounded_edge_outdegree] by simp
    show ?thesis using fp base by simp
  qed
  show ?thesis using run cost_le by blast
qed

text \<open>
  \<^bold>\<open>Cost-bounded cover lift (\<open>l \<rightarrow> Suc l\<close>).\<close>  The cost-tracking twin of
  @{thm [source] path_k_cover_lift}: lifting a level-\<open>l\<close> whole-path cover of cost
  at most \<open>Cb\<close> to level \<open>Suc l\<close> adds exactly one FindPivots scan (cost
  \<open>\<le> p \<cdot> edge_count\<close>); all four partition costs and the Done tail are zero.  Stacking
  this from the level-1 base accumulates one scan per level, giving the
  polylogarithmic cheap-run cost.
\<close>

lemma path_k_cover_lift_costed:
  fixes p q cap l Cb :: nat and d :: "nat \<Rightarrow> real"
  assumes pk_le: "p \<le> k" and cover: "Suc k \<le> cap"
    and ppos: "0 < p"
    and sound: "pk.sound_label d" and d0: "d 0 = 0"
    and pre0: "pk.bmssp_pre_full d {0} Infinity"
    and child: "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
        (bmssp_level_cap p q) q p p cap l
        (bpi.find_pivots_label_capped p cap d {0} (Fin (real (Suc k))))
        {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k))) U c
        \<and> c \<le> Cb"
  shows "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap (Suc l) d {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U c
      \<and> c \<le> Cb + p * bpi.edge_count"
proof -
  let ?B = "Fin (real (Suc k))"
  let ?d2 = "bpi.find_pivots_label_capped p cap d {0} ?B"
  let ?P = "bpi.find_pivots_pivots_capped p cap d {0} ?B"
  have reaches0: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have P0: "?P = {0}" by (rule path_k_source_is_sole_pivot_fin[OF pk_le cover d0 sound])
  have sound2: "pk.sound_label ?d2"
    unfolding bpi.find_pivots_label_capped_def
    by (rule bpi.fp_iter_capped_label_sound[OF sound reaches0])
  have le2: "?d2 0 \<le> d 0" by (rule bpi.find_pivots_label_capped_le)
  have d2_0: "?d2 0 = 0"
  proof -
    have "pk.dist 0 0 \<le> ?d2 0" using sound2 pk.source_in_V pk.reachable_refl[OF pk.source_in_V]
      unfolding pk.sound_label_def by blast
    moreover have "pk.dist 0 0 = 0" by (rule pk.dist_refl_zero[OF pk.source_in_V])
    ultimately show ?thesis using le2 d0 by simp
  qed
  have pre2: "pk.bmssp_pre_full ?d2 {0} ?B"
  proof -
    have preB: "pk.bmssp_pre_full d {0} ?B"
      using pre0 unfolding pk.bmssp_pre_full_def by auto
    show ?thesis
      by (rule bpi.find_pivots_label_capped_preserves_source_pre[OF sound preB reaches0])
  qed
  obtain U_c c_c where childrun:
    "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap l
       ?d2 {0} ?B (pk.dist 0) ?B U_c c_c"
    and c_c_le: "c_c \<le> Cb"
    using child by blast
  have Mpos: "0 < bmssp_level_cap p q l" using ppos by (simp add: bmssp_level_cap_def)
  have pull: "pull_separates (bpi.label_partition_view ?d2 {0}) (bmssp_level_cap p q l)
      (real (Suc k)) {0} (real (Suc k)) (bpi.label_partition_view ?d2 {} :: nat partition_view)"
    unfolding pull_separates_def bpi.label_partition_view_def
    using Mpos d2_0 by simp
  have split: "{0} = bpi.split_below ?d2 {0} (real (Suc k))"
    using d2_0 by (auto simp: bpi.split_below_def)
  have small: "card (pk.bound_tree {0} (Fin 0)) < p * cap"
  proof -
    have "pk.bound_tree {0} (Fin 0) = {}" by (rule path_k_bound_tree_source_Fin0_empty)
    moreover have "0 < p * cap" using ppos cover by simp
    ultimately show ?thesis by simp
  qed
  have tail_empty:
    "keys_of (batch_min_update (bpi.label_partition_view ?d2 {} :: nat partition_view)
       (bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
          (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) ?B @
        bpi.edge_relaxation_pairs_between (pk.dist 0)
          (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) (real (Suc k)) @
        bpi.label_pairs_between ?d2 {0} (real (Suc k)) (real (Suc k)))) = {}"
  proof -
    have lower: "bpi.edge_relaxation_pairs_between (pk.dist 0)
        (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) (real (Suc k)) = []"
      unfolding bpi.edge_relaxation_pairs_between_def
      by (auto simp: filter_empty_conv split: prod.splits)
    have src: "bpi.label_pairs_between ?d2 {0} (real (Suc k)) (real (Suc k)) = []"
      unfolding bpi.label_pairs_between_def by (simp add: filter_empty_conv)
    have direct: "bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
        (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) ?B = []"
      unfolding bpi.edge_relaxation_pairs_in_bound_def by (auto simp: filter_empty_conv)
    show ?thesis using lower src direct unfolding batch_min_update_def by simp
  qed
  have beta_bd: "bound_le (Fin (real (Suc k))) ?B" by simp
  have a_le_b: "(0::real) \<le> real (Suc k)" by simp
  have a0_bd: "bound_le (Fin (0::real)) ?B" by simp
  have reaches_ball: "\<forall>x\<in>{0::nat}. pk.reachable 0 x" using reaches0 by simp
  have looprun:
    "bpi.charged_direct_insert_costed_partition_loop_state (Suc 0)
       (bmssp_level_cap p q) q p p cap l ?d2 {0} ?B (pk.dist 0)
       (bpi.label_partition_view ?d2 {0}) 0 [real (Suc k)] [real (Suc k)] ?B
       (bpi.range_tree {0} 0 (Fin (real (Suc k)))
          # [bpi.range_tree {0} (real (Suc k)) ?B])
       [U_c]
       (pk.bound_tree {0} (Fin 0) \<union>
          \<Union>(set (bpi.range_tree {0} 0 (Fin (real (Suc k)))
                   # [bpi.range_tree {0} (real (Suc k)) ?B])))
       c_c [c_c]"
    by (rule bpi.charged_loop_single_step_then_done_costed_dist
        [where Bmax = "real (Suc k)" and beta = "real (Suc k)" and b = "real (Suc k)"
          and a = "0::real" and S_pull = "{0}"
          and D_pull = "bpi.label_partition_view ?d2 {} :: nat partition_view"
          and d_child = "pk.dist 0" and U_child = U_c and c_child = c_c])
      (use pull beta_bd pre2 split reaches_ball a_le_b a0_bd small childrun
        tail_empty beta_bd in simp_all)
  let ?U = "(pk.bound_tree {0} (Fin 0) \<union>
          \<Union>(set (bpi.range_tree {0} 0 (Fin (real (Suc k)))
                   # [bpi.range_tree {0} (real (Suc k)) ?B])))
       \<union> {v \<in> pk.bound_tree {0} ?B. ?d2 v = pk.dist 0 v}"
  have run: "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p cap
      (Suc l) d {0} ?B (pk.dist 0) ?B ?U
      (bpi.fp_iter_capped_scan_cost p cap d {0} {0} ?B + 0 + c_c)"
    by (rule bpi.charged_direct_insert_costed_bmssp_step_with_insert_cost
        [where D = "bpi.label_partition_view ?d2 {0}" and c_insert = 0])
      (use looprun P0 in \<open>simp_all add: bpi.partition_initial_insert_cost_bound_def pk.complete_on_def\<close>)
  have cost_le: "bpi.fp_iter_capped_scan_cost p cap d {0} {0} ?B + 0 + c_c
      \<le> Cb + p * bpi.edge_count"
  proof -
    have fp: "bpi.fp_iter_capped_scan_cost p cap d {0} {0} ?B \<le> p * bpi.edge_count"
      by (rule bpi.fp_iter_capped_scan_cost_le_rounds)
    show ?thesis using fp c_c_le by simp
  qed
  show ?thesis using run cost_le by blast
qed

text \<open>
  \<^bold>\<open>Cost-bounded level chain.\<close>  Stacking the cost-bounded cover lift from the
  cost-bounded level-1 base, a whole-path cover of cost at most
  \<open>(Suc l) \<cdot> (p \<cdot> edge_count) + p\<close> exists at every level \<open>Suc l\<close>: each level adds one
  FindPivots scan.  Specialising at \<open>l = p - 1\<close> bounds the single charged child run
  feeding the top-level reduction by \<open>p \<cdot> (p \<cdot> edge_count) + p\<close>, which is
  polylogarithmic in the schedule.
\<close>

lemma path_k_cover_ge1_costed:
  fixes p q cap :: nat
  assumes pk_le: "p \<le> k" and cover: "Suc k \<le> cap" and ppos: "0 < p"
  shows "\<And>d. pk.sound_label d \<Longrightarrow> d 0 = 0 \<Longrightarrow> pk.bmssp_pre_full d {0} Infinity \<Longrightarrow>
      \<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p
        cap (Suc l) d {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k))) U c
        \<and> c \<le> Suc l * (p * bpi.edge_count) + p"
proof (induct l)
  case 0
  have capgt: "1 < cap" using cover ppos pk_le by linarith
  show ?case
    using path_k_base1_costed[OF pk_le cover ppos capgt "0"(1) "0"(2) "0"(3)]
    by simp
next
  case (Suc l)
  let ?d2 = "bpi.find_pivots_label_capped p cap d {0} (Fin (real (Suc k)))"
  have reaches0: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have sound2: "pk.sound_label ?d2"
    unfolding bpi.find_pivots_label_capped_def
    by (rule bpi.fp_iter_capped_label_sound[OF Suc(2) reaches0])
  have d2_0: "?d2 0 = 0"
  proof -
    have "pk.dist 0 0 \<le> ?d2 0" using sound2 pk.source_in_V pk.reachable_refl[OF pk.source_in_V]
      unfolding pk.sound_label_def by blast
    moreover have "pk.dist 0 0 = 0" by (rule pk.dist_refl_zero[OF pk.source_in_V])
    ultimately show ?thesis
      using bpi.find_pivots_label_capped_le[of p cap d "{0}" "Fin (real (Suc k))" 0] Suc(3) by simp
  qed
  have pre2: "pk.bmssp_pre_full ?d2 {0} Infinity"
  proof (rule pk.top_bmssp_pre_full)
    show "\<And>v. v \<in> path_k_V k \<Longrightarrow> pk.reachable 0 v" by (rule path_k_all_reachable)
    show "?d2 0 = pk.dist 0 0" using d2_0 pk.dist_refl_zero[OF pk.source_in_V] by simp
  qed
  have child: "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap p q) q p p cap (Suc l) ?d2 {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U c
      \<and> c \<le> Suc l * (p * bpi.edge_count) + p"
    by (rule Suc(1)[OF sound2 d2_0 pre2])
  obtain U c where run:
    "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap p q) q p p
      cap (Suc (Suc l)) d {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k))) U c"
    and cle: "c \<le> Suc l * (p * bpi.edge_count) + p + p * bpi.edge_count"
    using path_k_cover_lift_costed[OF pk_le cover ppos Suc(2) Suc(3) Suc(4) child]
    by blast
  have "c \<le> Suc (Suc l) * (p * bpi.edge_count) + p"
    using cle by (simp add: algebra_simps)
  then show ?case using run by blast
qed

text \<open>
  \<^bold>\<open>Cost-bounded top-level reduction.\<close>  The cost-tracking twin of
  @{thm [source] path_k_charged_cost_exists_if_child}: the source-pivot top-level
  run pulls the sole source pivot once, runs the bounded level-\<open>p-1\<close> child of cost
  at most \<open>Cb\<close>, and terminates (the direct batch is empty on the path).  Its cost
  is one more FindPivots scan on top of the child, hence at most
  \<open>Cb + p \<cdot> edge_count\<close>.
\<close>

lemma path_k_charged_cost_le_if_child:
  fixes Cb :: nat
  assumes pk_le: "sssp_log_one_third_param N \<le> k"
    and cover: "Suc k \<le> bmssp_level_cap (sssp_log_one_third_param N)
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)"
    and ppos: "0 < sssp_log_one_third_param N"
    and child:
      "\<exists>U_child c_child.
        bpi.charged_direct_insert_costed_bmssp (Suc 0)
          (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
          (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
          (sssp_log_one_third_param N)
          (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
            (sssp_log_one_third_param N))
          (sssp_log_one_third_param N - 1)
          (bpi.find_pivots_label_capped (sssp_log_one_third_param N)
            (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N)
              (sssp_log_one_third_param N))
            pk.finite_initial_label {0} Infinity)
          {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k))) U_child c_child
        \<and> c_child \<le> Cb"
  shows "\<exists>c. bpi.charged_direct_insert_top_level_cost 1 N c
      \<and> c \<le> Cb + sssp_log_one_third_param N * bpi.edge_count"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  let ?d_fp = "bpi.find_pivots_label_capped ?p ?cap pk.finite_initial_label {0} Infinity"
  let ?P = "bpi.find_pivots_pivots_capped ?p ?cap pk.finite_initial_label {0} Infinity"
  have P0: "?P = {0}" by (rule path_k_source_is_sole_pivot[OF pk_le cover])
  have d_lt: "?d_fp 0 < real (Suc k)"
  proof -
    have "?d_fp 0 \<le> 0" by (rule path_k_fp_label_source_le_zero)
    also have "(0::real) < real (Suc k)" by simp
    finally show ?thesis .
  qed
  have pre: "pk.bmssp_pre_full ?d_fp {0} (Fin (real (Suc k)))"
    by (rule path_k_fp_source_pre_full)
  have cap_pos: "0 < ?p * ?cap"
    using sssp_log_one_third_param_pos[of N] by (simp add: bmssp_level_cap_def)
  have card_lt: "card (pk.bound_tree {0} (Fin 0)) < ?p * ?cap"
  proof -
    have "pk.bound_tree {0} (Fin 0) = {}" by (rule path_k_bound_tree_source_Fin0_empty)
    then show ?thesis using cap_pos by simp
  qed
  have batch: "bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
      (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) Infinity = []"
    using P0 path_k_direct_batch_empty by simp
  obtain U_child c_child where childrun:
    "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap
       (?p - 1) ?d_fp {0} (Fin (real (Suc k))) (pk.dist 0) (Fin (real (Suc k)))
       U_child c_child"
    and c_child_le: "c_child \<le> Cb"
    using child by blast
  have Mpos: "0 < bmssp_level_cap ?p ?q (?p - 1)"
    using ppos by (simp add: bmssp_level_cap_def)
  have pull: "pull_separates (bpi.label_partition_view ?d_fp {0})
      (bmssp_level_cap ?p ?q (?p - 1)) (real (Suc k)) {0} (real (Suc k))
      (bpi.label_partition_view ?d_fp {} :: nat partition_view)"
    unfolding pull_separates_def bpi.label_partition_view_def
    using Mpos d_lt by simp
  have split: "{0} = bpi.split_below ?d_fp {0} (real (Suc k))"
    using d_lt by (auto simp: bpi.split_below_def)
  have reaches0: "\<forall>x\<in>{0::nat}. pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have beta_bd: "bound_le (Fin (real (Suc k))) Infinity" by simp
  have a_le_b: "(0::real) \<le> real (Suc k)" by simp
  have a0_bd: "bound_le (Fin (0::real)) Infinity" by simp
  have tail_empty:
    "keys_of (batch_min_update (bpi.label_partition_view ?d_fp {} :: nat partition_view)
       (bpi.edge_relaxation_pairs_in_bound (pk.dist 0)
          (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) Infinity @
        bpi.edge_relaxation_pairs_between (pk.dist 0)
          (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) (real (Suc k)) @
        bpi.label_pairs_between ?d_fp {0} (real (Suc k)) (real (Suc k)))) = {}"
  proof -
    have lower: "bpi.edge_relaxation_pairs_between (pk.dist 0)
        (bpi.range_tree {0} 0 (Fin (real (Suc k)))) (real (Suc k)) (real (Suc k)) = []"
      unfolding bpi.edge_relaxation_pairs_between_def
      by (auto simp: filter_empty_conv split: prod.splits)
    have src: "bpi.label_pairs_between ?d_fp {0} (real (Suc k)) (real (Suc k)) = []"
      unfolding bpi.label_pairs_between_def by (simp add: filter_empty_conv)
    show ?thesis using lower src batch unfolding batch_min_update_def by simp
  qed
  have looprun:
    "bpi.charged_direct_insert_costed_partition_loop_state (Suc 0)
       (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap (?p - 1) ?d_fp {0} Infinity (pk.dist 0)
       (bpi.label_partition_view ?d_fp {0}) 0 [real (Suc k)] [real (Suc k)] Infinity
       (bpi.range_tree {0} 0 (Fin (real (Suc k)))
          # [bpi.range_tree {0} (real (Suc k)) Infinity])
       [U_child]
       (pk.bound_tree {0} (Fin 0) \<union>
          \<Union>(set (bpi.range_tree {0} 0 (Fin (real (Suc k)))
                   # [bpi.range_tree {0} (real (Suc k)) Infinity])))
       c_child [c_child]"
    by (rule bpi.charged_loop_single_step_then_done_costed_dist
        [where Bmax = "real (Suc k)" and beta = "real (Suc k)" and b = "real (Suc k)"
          and a = "0::real" and S_pull = "{0}"
          and D_pull = "bpi.label_partition_view ?d_fp {} :: nat partition_view"
          and d_child = "pk.dist 0" and U_child = U_child and c_child = c_child])
      (use pull beta_bd pre split reaches0 a_le_b a0_bd card_lt childrun
        tail_empty beta_bd in simp_all)
  let ?U = "(pk.bound_tree {0} (Fin 0) \<union>
          \<Union>(set (bpi.range_tree {0} 0 (Fin (real (Suc k)))
                   # [bpi.range_tree {0} (real (Suc k)) Infinity])))
       \<union> {v \<in> pk.bound_tree {0} Infinity. ?d_fp v = pk.dist 0 v}"
  let ?c = "bpi.fp_iter_capped_scan_cost ?p ?cap pk.finite_initial_label {0} {0} Infinity
       + 0 + c_child"
  have run: "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap
      (Suc (?p - 1)) pk.finite_initial_label {0} Infinity (pk.dist 0) Infinity ?U ?c"
    by (rule bpi.charged_direct_insert_costed_bmssp_step_with_insert_cost
        [where D = "bpi.label_partition_view ?d_fp {0}" and c_insert = 0])
      (use looprun P0 in \<open>simp_all add: bpi.partition_initial_insert_cost_bound_def pk.complete_on_def\<close>)
  have p_eq: "Suc (?p - 1) = ?p" using ppos by simp
  have run': "bpi.charged_direct_insert_costed_bmssp (Suc 0) (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap
      ?p pk.finite_initial_label {0} Infinity (pk.dist 0) Infinity ?U ?c"
    using run p_eq by simp
  have toprun: "bpi.charged_direct_insert_top_level_run (Suc 0) N (pk.dist 0) ?U ?c"
    unfolding bpi.charged_direct_insert_top_level_run_def
    using run' by (simp add: Let_def)
  have topcost: "bpi.charged_direct_insert_top_level_cost (Suc 0) N ?c"
    unfolding bpi.charged_direct_insert_top_level_cost_def using toprun by blast
  have cost_le: "?c \<le> Cb + ?p * bpi.edge_count"
  proof -
    have fp: "bpi.fp_iter_capped_scan_cost ?p ?cap pk.finite_initial_label {0} {0} Infinity
        \<le> ?p * bpi.edge_count"
      by (rule bpi.fp_iter_capped_scan_cost_le_rounds)
    show ?thesis using fp c_child_le by simp
  qed
  have main: "\<exists>c. bpi.charged_direct_insert_top_level_cost (Suc 0) N c
      \<and> c \<le> Cb + ?p * bpi.edge_count"
    using topcost cost_le by blast
  then show ?thesis by simp
qed

text \<open>
  \<^bold>\<open>The cheap charged top-level cost is polylogarithmic.\<close>  Assembling the
  cost-bounded level chain (to level \<open>p-1\<close>) and the cost-bounded top-level
  reduction: in the genuine \<open>2 \<le> p \<le> k\<close> pivot regime where the cap covers the
  path, a charged top-level cost exists that is bounded by
  \<open>p \<cdot> (p \<cdot> edge_count) + p\<close> --- a single \<^emph>\<open>square-of-the-pivot-rounds\<close> times edge
  factor.  No band-containment or amortized engine is needed: the cheap run pays
  one FindPivots scan per recursion level plus one base scan.
\<close>

theorem path_k_charged_cost_le:
  assumes pk_le: "sssp_log_one_third_param N \<le> k"
    and cover: "Suc k \<le> bmssp_level_cap (sssp_log_one_third_param N)
      (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)"
    and p2: "2 \<le> sssp_log_one_third_param N"
  shows "\<exists>c. bpi.charged_direct_insert_top_level_cost 1 N c
      \<and> c \<le> sssp_log_one_third_param N * (sssp_log_one_third_param N * bpi.edge_count)
            + sssp_log_one_third_param N"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  let ?cap = "bmssp_level_cap ?p ?q ?p"
  let ?d_fp = "bpi.find_pivots_label_capped ?p ?cap pk.finite_initial_label {0} Infinity"
  have ppos: "0 < ?p" using p2 by simp
  have allr: "\<And>v. v \<in> path_k_V k \<Longrightarrow> pk.reachable 0 v" by (rule path_k_all_reachable)
  have reaches0: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have fsound: "pk.sound_label pk.finite_initial_label"
    by (rule pk.finite_initial_label_sound[OF allr])
  have sc: "pk.finite_initial_label 0 = pk.dist 0 0"
    by (rule pk.finite_initial_label_source_complete)
  have pre0: "pk.bmssp_pre_full pk.finite_initial_label {0} Infinity"
    by (rule pk.top_bmssp_pre_full) (use allr sc in auto)
  have dfp_sound: "pk.sound_label ?d_fp"
    unfolding bpi.find_pivots_label_capped_def
    by (rule bpi.fp_iter_capped_label_sound[OF fsound reaches0])
  have dfp_pre: "pk.bmssp_pre_full ?d_fp {0} Infinity"
    by (rule bpi.find_pivots_label_capped_preserves_source_pre[OF fsound pre0 reaches0])
  have dfp_0: "?d_fp 0 = 0"
  proof -
    have "pk.dist 0 0 \<le> ?d_fp 0"
      using dfp_sound pk.source_in_V pk.reachable_refl[OF pk.source_in_V]
      unfolding pk.sound_label_def by blast
    moreover have "?d_fp 0 \<le> pk.finite_initial_label 0"
      by (rule bpi.find_pivots_label_capped_le)
    moreover have "pk.finite_initial_label 0 = 0"
      using sc pk.dist_refl_zero[OF pk.source_in_V] by simp
    moreover have "pk.dist 0 0 = 0" by (rule pk.dist_refl_zero[OF pk.source_in_V])
    ultimately show ?thesis by simp
  qed
  have chain: "\<exists>U c. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap (Suc (?p - 2)) ?d_fp {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U c
      \<and> c \<le> Suc (?p - 2) * (?p * bpi.edge_count) + ?p"
    by (rule path_k_cover_ge1_costed[OF pk_le cover ppos dfp_sound dfp_0 dfp_pre])
  have pe: "Suc (?p - 2) = ?p - 1" using p2 by simp
  have child: "\<exists>U_child c_child. bpi.charged_direct_insert_costed_bmssp (Suc 0)
      (bmssp_level_cap ?p ?q) ?q ?p ?p ?cap (?p - 1) ?d_fp {0} (Fin (real (Suc k)))
      (pk.dist 0) (Fin (real (Suc k))) U_child c_child
      \<and> c_child \<le> (?p - 1) * (?p * bpi.edge_count) + ?p"
    using chain pe by simp
  obtain c where tc: "bpi.charged_direct_insert_top_level_cost 1 N c"
    and cle: "c \<le> ((?p - 1) * (?p * bpi.edge_count) + ?p) + ?p * bpi.edge_count"
    using path_k_charged_cost_le_if_child[OF pk_le cover ppos child] by blast
  have arith: "((?p - 1) * (?p * bpi.edge_count) + ?p) + ?p * bpi.edge_count
      = ?p * (?p * bpi.edge_count) + ?p"
  proof -
    obtain m where pm: "?p = Suc m" using gr0_implies_Suc[OF ppos] by blast
    show ?thesis by (simp add: pm)
  qed
  have "c \<le> ?p * (?p * bpi.edge_count) + ?p" using cle arith by simp
  with tc show ?thesis by blast
qed

text \<open>
  \<^bold>\<open>Charged-cost structural facts.\<close>  The next
  facts record permissive-relation structure on the path: a returned bound that
  covers the path forces the whole vertex set into the bounded tree, a level-0
  base settles at most \<open>kk \<le> k\<close> vertices, and (the harder fact) a source-pivot
  loop whose data structure already excludes the source but is still nonempty
  can never finish.  They are reusable ingredients for bounding charged costs.
\<close>

text \<open>A covering returned bound forces the whole path into the bounded tree.\<close>
lemma path_k_cover_imp_V_subset:
  assumes cov: "bound_le (Fin (real (Suc k))) B'"
  shows "path_k_V k \<subseteq> pk.bound_tree {0} B'"
proof
  fix v assume "v \<in> path_k_V k"
  then have vk: "v \<le> k" by (simp add: path_k_V_eq)
  have below: "below_bound (pk.dist 0 v) B'"
  proof (cases B')
    case (Fin r)
    have "real (Suc k) \<le> r" using cov Fin by simp
    then have "real v < r" using vk by simp
    then show ?thesis using Fin path_k_dist_eq[OF vk] by simp
  next
    case Infinity
    then show ?thesis by simp
  qed
  have thr: "pk.through {0} v" using path_k_through_iff[OF vk] by simp
  show "v \<in> pk.bound_tree {0} B'"
    unfolding pk.bound_tree_def
    using vk thr below path_k_all_reachable by (simp add: path_k_V_eq)
qed

text \<open>\<^bold>\<open>Base of the no-coverage induction.\<close>  A level-0 charged base run from the
  source settles at most \<open>kk \<le> k\<close> vertices, so its returned bound cannot cover
  the \<^term>\<open>Suc k\<close> path vertices.\<close>
lemma path_k_charged_base_noncover:
  fixes kk :: nat
  assumes kk_le: "kk \<le> k"
    and run: "bpi.charged_direct_insert_costed_bmssp \<Delta> M_of t h kk cap 0 d {0} B d' B' U c"
    and sound: "pk.sound_label d"
    and pre: "pk.bmssp_pre_full d {0} B"
  shows "\<not> bound_le (Fin (real (Suc k))) B'"
proof
  assume cov: "bound_le (Fin (real (Suc k))) B'"
  have reaches: "\<And>x. x \<in> {0::nat} \<Longrightarrow> pk.reachable 0 x"
    using pk.reachable_refl[OF pk.source_in_V] by simp
  have post: "pk.bmssp_post_full d {0} B d' B' U"
    by (rule bpi.charged_direct_insert_costed_bmssp_correct[OF run sound pre reaches])
  have U_eq: "U = pk.bound_tree {0} B'"
    using post unfolding pk.bmssp_post_full_def by blast
  have sub: "path_k_V k \<subseteq> U"
    using path_k_cover_imp_V_subset[OF cov] U_eq by simp
  have finU: "finite U"
  proof -
    have "U \<subseteq> path_k_V k"
      using U_eq unfolding pk.bound_tree_def by auto
    then show ?thesis using path_k_finite_V by (rule finite_subset)
  qed
  have ge: "Suc k \<le> card U"
    using card_mono[OF finU sub] by (simp add: path_k_card_V)
  have U_base: "U = pk.base_case_vertices kk 0 B"
    using run by (cases rule: bpi.charged_direct_insert_costed_bmssp_zeroE) auto
  have "card U \<le> kk"
    using U_base pk.card_base_case_vertices_le by metis
  with ge kk_le show False by simp
qed

text \<open>\<^bold>\<open>Frontier persistence (the undone band-monotonicity invariant, on the
  charged cost relation).\<close>  On the source-pivot path a partition loop whose
  current data structure already excludes the source \<open>0\<close> but is still nonempty
  can never finish: the only pullable pivot is \<open>0\<close> (every \<open>split_below d {0}\<close>
  lies in \<open>{0}\<close>), so each remaining step is a null pull, and the relaxation only
  ever pushes strictly positive frontier vertices
  (@{thm [source] path_k_relax_in_bound_keys_pos},
  @{thm [source] path_k_relax_between_keys_pos}).  Hence the nonempty,
  source-free frontier is preserved forever and neither \<open>Done\<close> (empty keys) nor
  \<open>Stop\<close> (cap threshold, excluded by \<open>Suc k < kk \<cdot> cap\<close>) can fire.\<close>
lemma path_k_loop_frontier_persist:
  "bpi.charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h kk cap l d P B d'
      D a betas bs B' charged_Us child_outputs U c child_costs \<Longrightarrow>
     P = {0} \<Longrightarrow> Suc k < kk * cap \<Longrightarrow> (0::nat) \<notin> keys_of D \<Longrightarrow> keys_of D \<noteq> {}
     \<Longrightarrow> False"
  and "bpi.charged_direct_insert_costed_bmssp \<Delta> M_of t h kk cap l d S B d' B' U c
     \<Longrightarrow> True"
proof (induction rule:
    bpi.charged_direct_insert_costed_partition_loop_state_charged_direct_insert_costed_bmssp.inducts)
  case (Charged_Direct_Insert_State_Done D a B d' P \<Delta> M_of t h kk cap l d)
  then show ?case by simp
next
  case (Charged_Direct_Insert_State_Stop a B d' P kk cap \<Delta> M_of t h l d D)
  have thr: "kk * cap \<le> card (pk.bound_tree P (Fin a))"
    using Charged_Direct_Insert_State_Stop by blast
  have card_le: "card (pk.bound_tree P (Fin a)) \<le> Suc k"
  proof -
    have "pk.bound_tree P (Fin a) \<subseteq> path_k_V k"
      unfolding pk.bound_tree_def by auto
    then show ?thesis
      using card_mono[OF path_k_finite_V] by (simp add: path_k_card_V)
  qed
  show ?case
    using thr card_le Charged_Direct_Insert_State_Stop.prems(2) by linarith
next
  case (Charged_Direct_Insert_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' kk cap \<Delta> t h d_child U_child c_child charged_child
      direct_edge_batch lower_edge_batch source_batch batch D_next c_pull
      c_direct c_lower c_sources betas bs charged_tail child_outputs_tail
      U_tail c_tail child_costs_tail c)
  have P0: "P = {0}" using Charged_Direct_Insert_State_Step.prems(1) .
  have regime: "Suc k < kk * cap" using Charged_Direct_Insert_State_Step.prems(2) .
  have notin: "(0::nat) \<notin> keys_of D" using Charged_Direct_Insert_State_Step.prems(3) .
  have ne: "keys_of D \<noteq> {}" using Charged_Direct_Insert_State_Step.prems(4) .
  have split: "S_pull = bpi.split_below d P beta"
    using Charged_Direct_Insert_State_Step by metis
  have spull_sub: "S_pull \<subseteq> {0}"
    using split P0 unfolding bpi.split_below_def by auto
  have pull: "pull_separates D (M_of l) Bmax S_pull beta D_pull"
    using Charged_Direct_Insert_State_Step by metis
  have spull_keys: "S_pull \<subseteq> keys_of D"
    using pull unfolding pull_separates_def by simp
  have spull_empty: "S_pull = {}"
    using spull_sub spull_keys notin by blast
  have dpull_keys: "keys_of D_pull = keys_of D"
    using pull spull_empty unfolding pull_separates_def by simp
  have batch_eq: "batch = direct_edge_batch @ lower_edge_batch @ source_batch"
    using Charged_Direct_Insert_State_Step by metis
  have dir_eq: "direct_edge_batch
      = bpi.edge_relaxation_pairs_in_bound d_child charged_child beta B"
    using Charged_Direct_Insert_State_Step by metis
  have low_eq: "lower_edge_batch
      = bpi.edge_relaxation_pairs_between d_child charged_child b beta"
    using Charged_Direct_Insert_State_Step by metis
  have src_eq: "source_batch = bpi.label_pairs_between d S_pull b beta"
    using Charged_Direct_Insert_State_Step by metis
  have src_empty: "source_batch = []"
  proof -
    have fin: "finite (keys_of (bpi.label_partition_view d {}))" by simp
    have "set (partition_key_order (bpi.label_partition_view d {})) = {}"
      using partition_key_order_properties(1)[OF fin] by simp
    then have "partition_key_order (bpi.label_partition_view d {}) = []"
      by simp
    then show ?thesis
      using src_eq spull_empty by (simp add: bpi.label_pairs_between_def)
  qed
  have batch_pos: "(0::nat) \<notin> fst ` set batch"
  proof -
    have "fst ` set batch
        = fst ` set direct_edge_batch \<union> fst ` set lower_edge_batch"
      using batch_eq src_empty by (simp add: image_Un)
    then show ?thesis
      using dir_eq low_eq
        path_k_relax_in_bound_keys_pos path_k_relax_between_keys_pos by auto
  qed
  have Dnext: "D_next = batch_min_update D_pull batch"
    using Charged_Direct_Insert_State_Step by metis
  have keys_next: "keys_of D_next = keys_of D \<union> fst ` set batch"
    using Dnext dpull_keys by (simp add: batch_min_update_keys)
  have notin_next: "(0::nat) \<notin> keys_of D_next"
    using keys_next notin batch_pos by simp
  have ne_next: "keys_of D_next \<noteq> {}"
    using keys_next ne by simp
  show ?case
    using Charged_Direct_Insert_State_Step notin_next ne_next by metis
next
  case (Charged_Direct_Insert_Base S x \<Delta> M_of t h kk cap d B)
  then show ?case by simp
next
  case (Charged_Direct_Insert_Step D kk cap d S B c_insert t \<Delta> M_of h l d' a
      betas bs B' charged_Us child_outputs U_loop c_loop child_costs_loop U c)
  then show ?case by simp
qed

end

subsection \<open>The bucket cap dominates the path size at the inflated schedule\<close>

abbreviation cap_at :: "nat \<Rightarrow> nat" where
  "cap_at N \<equiv> bmssp_level_cap (sssp_log_one_third_param N)
     (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)"

lemma param_one_third_ge_factor:
  "sssp_log_factor_one_third N \<le> real (sssp_log_one_third_param N)"
proof -
  have "(0::real) \<le> sssp_log_factor_one_third N"
    by (rule less_imp_le[OF sssp_log_factor_one_third_pos])
  then show ?thesis
    by (simp add: sssp_log_one_third_param_def)
qed

lemma param_two_thirds_ge_factor:
  "sssp_log_factor N \<le> real (sssp_log_two_thirds_param N)"
proof -
  have "(0::real) \<le> sssp_log_factor N"
    by (rule less_imp_le[OF sssp_log_factor_pos])
  then show ?thesis
    by (simp add: sssp_log_two_thirds_param_def)
qed

lemma ln_le_param_product:
  "ln (real N + 2)
     \<le> real (sssp_log_one_third_param N) * real (sssp_log_two_thirds_param N)"
proof -
  have lnnn: "0 \<le> ln (real N + 2)"
    by simp
  have prod_eq:
    "sssp_log_factor_one_third N * sssp_log_factor N = ln (real N + 2)"
  proof -
    have "sssp_log_factor_one_third N * sssp_log_factor N
        = (ln (real N + 2)) powr (1 / 3) * (ln (real N + 2)) powr (2 / 3)"
      by (simp add: sssp_log_factor_one_third_def sssp_log_factor_def)
    also have "\<dots> = (ln (real N + 2)) powr (1 / 3 + 2 / 3)"
      by (rule powr_add[symmetric])
    also have "\<dots> = ln (real N + 2)"
      using lnnn by simp
    finally show ?thesis .
  qed
  have f23_nn: "0 \<le> sssp_log_factor N"
    by (rule less_imp_le[OF sssp_log_factor_pos])
  have p_nn: "0 \<le> real (sssp_log_one_third_param N)"
    by simp
  have "sssp_log_factor_one_third N * sssp_log_factor N
      \<le> real (sssp_log_one_third_param N) * real (sssp_log_two_thirds_param N)"
    by (rule mult_mono[OF param_one_third_ge_factor param_two_thirds_ge_factor
        p_nn f23_nn])
  then show ?thesis
    using prod_eq by simp
qed

lemma powr_ln2_le_cap:
  "(real N + 2) powr ln 2 \<le> real (cap_at N)"
proof -
  let ?p = "sssp_log_one_third_param N"
  let ?q = "sssp_log_two_thirds_param N"
  have cap_eq: "cap_at N = ?p * 2 ^ (?p * ?q)"
    by (rule bmssp_level_cap_eq)
  have rp1: "(1::real) \<le> real ?p"
  proof -
    have "(1::nat) \<le> ?p"
      using sssp_log_one_third_param_pos[of N] by linarith
    thus ?thesis by simp
  qed
  have ln_le: "ln (real N + 2) \<le> real (?p * ?q)"
    using ln_le_param_product[of N] by simp
  have "(real N + 2) powr ln 2 = 2 powr ln (real N + 2)"
    by (simp add: powr_def mult.commute)
  also have "\<dots> \<le> 2 powr real (?p * ?q)"
    by (rule powr_mono[OF ln_le]) simp
  also have "\<dots> = (2::real) ^ (?p * ?q)"
    by (rule powr_realpow[OF zero_less_numeral])
  also have "\<dots> = 1 * (2::real) ^ (?p * ?q)"
    by simp
  also have "\<dots> \<le> real ?p * (2::real) ^ (?p * ?q)"
    by (rule mult_right_mono[OF rp1]) simp
  also have "\<dots> = real (cap_at N)"
    by (simp add: cap_eq)
  finally show ?thesis .
qed

text \<open>
  The decisive arithmetic fact (milestone \textbf{B0}, deliverable (G2)): at the
  inflated schedule \<open>n \<cdot> n\<close> the top-level bucket cap eventually covers all
  @{term "Suc n"} path vertices.
\<close>

theorem eventually_card_path_le_cap_inflated:
  "eventually (\<lambda>n. card (path_k_V n) \<le> cap_at (n * n)) at_top"
proof -
  have growth:
    "eventually (\<lambda>n::nat. real (Suc n) \<le> (real n) powr (2 * ln 2)) at_top"
    by (rule real_Suc_le_powr_eventually[OF one_less_two_ln_two])
  have ev_n: "eventually (\<lambda>n::nat. (1::nat) \<le> n) at_top"
    by (rule eventually_ge_at_top)
  from growth ev_n show ?thesis
  proof eventually_elim
    case (elim n)
    have npos: "0 < real n"
      using elim(2) by simp
    have sq: "real (n * n) = (real n) powr 2"
    proof -
      have "(real n) powr 2 = (real n) ^ 2"
        by (simp add: powr_numeral)
      then show ?thesis
        by (simp add: power2_eq_square)
    qed
    have "real (Suc n) \<le> (real n) powr (2 * ln 2)"
      by (rule elim(1))
    also have "(real n) powr (2 * ln 2) = ((real n) powr 2) powr ln 2"
      by (rule powr_powr[symmetric])
    also have "\<dots> = real (n * n) powr ln 2"
      by (simp only: sq)
    also have "real (n * n) powr ln 2 \<le> (real (n * n) + 2) powr ln 2"
    proof (rule powr_mono2)
      show "0 \<le> ln (2::real)"
        using ln_gt_zero[of 2] by simp
      show "0 \<le> real (n * n)"
        by simp
      show "real (n * n) \<le> real (n * n) + 2"
        by simp
    qed
    also have "\<dots> \<le> real (cap_at (n * n))"
      using powr_ln2_le_cap[of "n * n"] by simp
    finally have "real (Suc n) \<le> real (cap_at (n * n))" .
    then have "Suc n \<le> cap_at (n * n)"
      by (simp only: of_nat_le_iff)
    then show ?case
      by (simp add: path_k_card_V)
  qed
qed

subsection \<open>The inflated schedule index stays below the graph size\<close>

text \<open>
  Growth upper bound (used so that the prefix \<open>{0..p}\<close> of short-tight witnesses
  fits inside the path): at the inflated schedule \<open>k \<cdot> k\<close> the FindPivots round
  parameter \<open>p = sssp_log_one_third_param (k \<cdot> k)\<close> is eventually at most the path
  length \<open>k\<close>, because \<open>p \<sim> (ln (k\<^sup>2 + 2))\<^bsup>1/3\<^esup>\<close> grows far slower than \<open>k\<close>.
\<close>

lemma path_param_le_self:
  "eventually (\<lambda>k::nat. sssp_log_one_third_param (k * k) \<le> k) at_top"
proof -
  have ev2: "eventually (\<lambda>k::nat. 2 \<le> k) at_top"
    by (rule eventually_ge_at_top)
  show ?thesis
  proof (rule eventually_mono[OF ev2])
    fix k :: nat
    assume k2: "2 \<le> k"
    have kpos: "0 < k"
      using k2 by simp
    have rk_pos: "0 \<le> real k"
      by simp
    have nat_cube: "k * k + 1 \<le> k * k * k"
    proof -
      have kk1: "1 \<le> k * k"
        using kpos by simp
      have "k * k + 1 \<le> k * k + k * k"
        using kk1 by simp
      also have "k * k + k * k = 2 * (k * k)"
        by simp
      also have "2 * (k * k) \<le> k * (k * k)"
        using k2 by (rule mult_le_mono1)
      also have "k * (k * k) = k * k * k"
        by (simp add: mult.assoc)
      finally show ?thesis .
    qed
    have real_cube: "real (k * k) + 1 \<le> (real k) ^ 3"
    proof -
      have "real (k * k) + 1 = real (k * k + 1)"
        by simp
      also have "\<dots> \<le> real (k * k * k)"
        using nat_cube by (simp only: of_nat_le_iff)
      also have "real (k * k * k) = (real k) ^ 3"
        by (simp add: power3_eq_cube)
      finally show ?thesis .
    qed
    have ln_le: "ln (real (k * k) + 2) \<le> (real k) ^ 3"
    proof -
      have pos: "0 < real (k * k) + 2"
        by (rule add_nonneg_pos) simp_all
      have "ln (real (k * k) + 2) \<le> (real (k * k) + 2) - 1"
        by (rule ln_le_minus_one[OF pos])
      also have "(real (k * k) + 2) - 1 = real (k * k) + 1"
        by simp
      also have "real (k * k) + 1 \<le> (real k) ^ 3"
        by (rule real_cube)
      finally show ?thesis .
    qed
    have ln_nonneg: "0 \<le> ln (real (k * k) + 2)"
    proof -
      have "(0::real) \<le> real (k * k)"
        by simp
      then have "(1::real) < real (k * k) + 2"
        by linarith
      then have "0 < ln (real (k * k) + 2)"
        by (rule ln_gt_zero)
      then show ?thesis by simp
    qed
    have factor_le: "sssp_log_factor_one_third (k * k) \<le> real k"
    proof -
      have "sssp_log_factor_one_third (k * k)
          = ln (real (k * k) + 2) powr (1 / 3)"
        by (simp add: sssp_log_factor_one_third_def)
      also have "\<dots> = root 3 (ln (real (k * k) + 2))"
        using root_powr_inverse[of 3 "ln (real (k * k) + 2)"] ln_nonneg
        by simp
      also have "\<dots> \<le> root 3 ((real k) ^ 3)"
        using real_root_le_mono[of 3 "ln (real (k * k) + 2)" "(real k) ^ 3"]
          ln_le by simp
      also have "root 3 ((real k) ^ 3) = real k"
        using real_root_power_cancel[of 3 "real k"] rk_pos by simp
      finally show ?thesis .
    qed
    have "sssp_log_one_third_param (k * k)
        = nat \<lceil>sssp_log_factor_one_third (k * k)\<rceil>"
      by (simp add: sssp_log_one_third_param_def)
    also have "\<dots> \<le> nat \<lceil>real k\<rceil>"
      using factor_le by (intro nat_mono ceiling_mono)
    also have "nat \<lceil>real k\<rceil> = k"
      by simp
    finally show "sssp_log_one_third_param (k * k) \<le> k" .
  qed
qed

subsection \<open>The inflated schedule is genuine and keeps the polylog in \<open>\<Theta>(ln n)\<close>\<close>

lemma nat_le_mult_self: "(n::nat) \<le> n * n"
  by (cases n) auto

theorem inflated_schedule_at_top:
  "filterlim (\<lambda>n::nat. n * n) at_top at_top"
  unfolding filterlim_at_top
proof
  fix Z :: nat
  have "eventually (\<lambda>n::nat. Z \<le> n) at_top"
    by (rule eventually_ge_at_top)
  then show "eventually (\<lambda>n::nat. Z \<le> n * n) at_top"
  proof eventually_elim
    case (elim n)
    show ?case
      using elim nat_le_mult_self[of n] by linarith
  qed
qed

theorem ln_inflated_schedule:
  assumes "1 \<le> n"
  shows "ln (real (n * n)) = 2 * ln (real n)"
proof -
  have "0 < real n"
    using assms by simp
  then show ?thesis
    by (simp add: ln_mult)
qed

text \<open>Deliverable (G1): the graph size itself is unbounded.\<close>

theorem path_card_V_at_top:
  "filterlim (\<lambda>n. card (path_k_V n)) at_top at_top"
proof -
  have "filterlim (\<lambda>n::nat. Suc n) at_top at_top"
    by (simp add: filterlim_Suc)
  then show ?thesis
    by (simp add: path_k_card_V)
qed

text \<open>
  \<^bold>\<open>The inflated-schedule pivot regime (B1 staging).\<close>  Three facts hold together
  for all but finitely many \<open>n\<close>: the FindPivots round count
  \<open>p = sssp_log_one_third_param (n \<cdot> n)\<close> has grown past \<open>1\<close> (so the level chain
  \<open>p - 1 \<ge> 1\<close> is non-degenerate), it stays below the path length \<open>n\<close>, and the
  inflated bucket cap covers the \<open>Suc n\<close> path vertices.  These are exactly the
  hypotheses \<open>p \<le> k\<close>, \<open>Suc k \<le> cap\<close>, \<open>0 < p\<close> of the path cover bricks at
  \<open>k = n\<close>, packaged as a single eventual statement to feed the (G3) reduction.
\<close>

theorem eventually_inflated_pivot_regime:
  "eventually (\<lambda>n. 2 \<le> sssp_log_one_third_param (n * n)
       \<and> sssp_log_one_third_param (n * n) \<le> n
       \<and> Suc n \<le> cap_at (n * n)) at_top"
proof -
  have p2: "eventually (\<lambda>n::nat. 2 \<le> sssp_log_one_third_param (n * n)) at_top"
  proof -
    have "filterlim (\<lambda>n::nat. sssp_log_one_third_param (n * n)) at_top at_top"
      by (rule filterlim_compose[OF sssp_log_one_third_param_at_top inflated_schedule_at_top])
    then show ?thesis
      unfolding filterlim_at_top by blast
  qed
  have ple: "eventually (\<lambda>k::nat. sssp_log_one_third_param (k * k) \<le> k) at_top"
    by (rule path_param_le_self)
  have cap: "eventually (\<lambda>n. Suc n \<le> cap_at (n * n)) at_top"
    using eventually_card_path_le_cap_inflated by (simp add: path_k_card_V)
  from p2 ple cap show ?thesis
    by eventually_elim simp
qed

subsection \<open>The decoupled charged running time of the path family\<close>

definition path_nonvac_time :: "nat \<Rightarrow> nat" where
  "path_nonvac_time n =
     strict_tie_breaking_digraph.charged_direct_insert_top_level_time
       (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n)"

text \<open>
  The decoupled charged reduction (milestone \textbf{B1}, deliverable (G3)):
  whenever the source pivot finishes on \<open>P\<^sub>n\<close> at the inflated schedule \<open>n \<cdot> n\<close>,
  a charged top-level run --- hence a charged top-level cost --- exists.  This is
  the schedule-decoupled analogue of
  @{thm [source] eventually_path_family_charged_direct_insert_top_level_cost_if_source_pivot_finishes}.
\<close>

theorem eventually_path_nonvac_charged_cost_exists_if_source_pivot_finishes:
  assumes source_pivot_finishes:
    "eventually
      (\<lambda>n. strict_tie_breaking_digraph.charged_direct_insert_source_pivot_finishes
        (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n)) at_top"
  shows "eventually
    (\<lambda>n. \<exists>c. strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
      (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c) at_top"
  using source_pivot_finishes
proof eventually_elim
  case (elim n)
  interpret bpi: bounded_reduced_positive_instance
    "path_k_V n" "path_k_E n" "path_k_weight n" 0 1
    by (rule path_k_bounded_instance)
  have "bpi.charged_direct_insert_source_pivot_finishes 1 (n * n)"
    using elim .
  then show ?case
    by (rule bpi.charged_direct_insert_top_level_cost_exists_if_source_pivot_finishes_pred)
qed

text \<open>
  \<^bold>\<open>Milestone B1, fully discharged.\<close>  Dropping the \<open>source_pivot_finishes\<close>
  hypothesis: at the inflated schedule the genuine \<open>2 \<le> p \<le> n\<close> pivot regime
  holds eventually (@{thm [source] eventually_inflated_pivot_regime}), so the
  unconditional charged-cost existence
  @{thm [source] path_k_charged_cost_exists} applies for all but finitely many
  \<open>n\<close>.  A charged top-level run on the decoupled family therefore exists
  eventually, with \<^emph>\<open>no\<close> assumption.\<close>
theorem eventually_path_nonvac_charged_cost_exists:
  "eventually
    (\<lambda>n. \<exists>c. strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
      (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c) at_top"
  using eventually_inflated_pivot_regime
proof eventually_elim
  case (elim n)
  show ?case
  proof (rule path_k_charged_cost_exists)
    show "sssp_log_one_third_param (n * n) \<le> n" using elim by simp
    show "Suc n \<le> bmssp_level_cap (sssp_log_one_third_param (n * n))
        (sssp_log_two_thirds_param (n * n)) (sssp_log_one_third_param (n * n))"
      using elim by simp
    show "2 \<le> sssp_log_one_third_param (n * n)" using elim by simp
  qed
qed

text \<open>
  \<^bold>\<open>Status of the unconditional discharge of \<open>source_pivot_finishes\<close> (G3).\<close>
  The reduction above turns (G3) into the obligation
  \<^item> \<open>eventually (\<lambda>n. charged_direct_insert_source_pivot_finishes (P\<^sub>n) 0 1 (n \<cdot> n)) at_top\<close>.
  Its first conjunct \<open>P = {s}\<close> is supplied by the reusable brick
  @{thm [source] unique_shortest_digraph.find_pivots_pivots_capped_singleton_source_if_large_tree},
  whose two premises specialise to the path as follows.  The genuine distance
  @{thm [source] path_k_dist_eq} and the source-tree identity
  @{thm [source] path_k_tree_of_source} collapse the source-tree slice to the
  capped scan, and the no-overflow premise is
  @{thm [source] path_k_find_pivots_seen_card_le} together with the cap
  domination below.  What remains for \<open>P = {s}\<close> is the seen \<^emph>\<open>lower\<close> bound
  \<open>p \<le> card (find_pivots_seen_capped \<dots>)\<close>, i.e.\ that the @{term p}-round
  bounded scan from \<open>{0}\<close> reaches at least @{term p} path vertices; with
  @{thm [source] path_k_dist_eq} every prefix edge is tight, so the prefix
  \<open>{0..p}\<close> are short-tight witnesses inside the scan.  The remaining conjuncts of
  \<open>source_pivot_finishes\<close> (the band child run and the empty direct-edge batch)
  are then a multi-step loop-coverage construction that pulls the path band by
  band, each child closed by the empty-pivots route on a sub-band that fits
  below @{term p}, and is the substance of milestone \textbf{B1}.
\<close>

subsection \<open>The decoupled charged headline (conditional skeleton for \textbf{B3})\<close>

text \<open>
  Mirroring the diagonal conditional
  @{thm [source] bmssp_path_family_charged_direct_insert_runtime_bigo_size_if_cost_bounded},
  but on the \<^emph>\<open>decoupled\<close> family \<open>P\<^sub>n\<close> run at schedule \<open>n \<cdot> n\<close>: if charged
  top-level runs eventually exist and every charged cost is bounded by the
  refined graph-time budget at the inflated schedule, the least charged cost has
  the genuine size-parametric target \<open>O(n \<cdot> (ln n)\<^bsup>2/3\<^esup>)\<close>.  Unlike the
  diagonal version, the two hypotheses here are \<^emph>\<open>not\<close> obstructed: the cap covers
  the path (see @{thm [source] eventually_card_path_le_cap_inflated}), so the
  goal of milestones \textbf{B1}/\textbf{B2} is to discharge them unconditionally.
\<close>

theorem path_nonvac_runtime_bigo_if_runs_and_cost_bound:
  assumes charged_runs_exist:
    "eventually
      (\<lambda>n. \<exists>c. strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
        (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c) at_top"
    and charged_cost_bound:
    "eventually
      (\<lambda>n. \<forall>c.
        strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
          (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c \<longrightarrow>
        c \<le> bmssp_refined_graph_time_bound
          (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. n) (Suc n)) at_top"
  shows "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real n * (ln (real n + 2)) powr (2 / 3))"
proof -
  have "(\<lambda>n. real (path_nonvac_time n))
      \<in> O(\<lambda>n. sssp_time_target (\<lambda>n. n) n)"
  proof (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_square_arg_slack
      [where D = 1 and Cn = 2 and Cm = 1
        and v = "\<lambda>n. Suc n" and m' = "\<lambda>n. n" and m = "\<lambda>n. n"])
    show "0 < (2 :: real)" by simp
    show "0 < (1 :: real)" by simp
    show "eventually (\<lambda>n. real (Suc n) \<le> 2 * real n) at_top"
      by (rule eventually_at_top_linorderI[of 1]) simp
    show "eventually (\<lambda>n. real n \<le> 1 * real n) at_top"
      by simp
    show "eventually
        (\<lambda>n. path_nonvac_time n \<le>
          bmssp_refined_graph_time_bound
            (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. n) (Suc n)) at_top"
      using charged_runs_exist charged_cost_bound
    proof eventually_elim
      case (elim n)
      then obtain c where cost:
        "strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
           (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c"
        by blast
      interpret bpi: bounded_reduced_positive_instance
        "path_k_V n" "path_k_E n" "path_k_weight n" 0 1
        by (rule path_k_bounded_instance)
      have cost': "bpi.charged_direct_insert_top_level_cost 1 (n * n) c"
        using cost .
      have time_le_c: "bpi.charged_direct_insert_top_level_time 1 (n * n) \<le> c"
        unfolding bpi.charged_direct_insert_top_level_time_def
        by (rule Least_le) (rule cost')
      have c_le:
        "c \<le> bmssp_refined_graph_time_bound
          (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. n) (Suc n)"
        using elim(2) cost by blast
      have tb:
        "bpi.charged_direct_insert_top_level_time 1 (n * n) = path_nonvac_time n"
        by (simp add: path_nonvac_time_def)
      show ?case
        using time_le_c c_le tb by linarith
    qed
  qed
  then show ?thesis
    unfolding sssp_time_target_def sssp_log_factor_def by simp
qed

text \<open>
  The same conditional headline phrased in deliverable (G5)'s exact form, in the
  \<^emph>\<open>genuine vertex count\<close> @{term "card (path_k_V n)"}.  This is the precise
  statement that milestones \textbf{B1}/\textbf{B2} must make unconditional.
\<close>

theorem path_nonvac_runtime_bigo_card_V_if_runs_and_cost_bound:
  assumes charged_runs_exist:
    "eventually
      (\<lambda>n. \<exists>c. strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
        (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c) at_top"
    and charged_cost_bound:
    "eventually
      (\<lambda>n. \<forall>c.
        strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
          (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c \<longrightarrow>
        c \<le> bmssp_refined_graph_time_bound
          (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. n) (Suc n)) at_top"
  shows "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real (card (path_k_V n)) *
           (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
proof -
  have base: "(\<lambda>n. real (path_nonvac_time n))
      \<in> O(\<lambda>n. real n * (ln (real n + 2)) powr (2 / 3))"
    by (rule path_nonvac_runtime_bigo_if_runs_and_cost_bound
        [OF charged_runs_exist charged_cost_bound])
  have dom: "(\<lambda>n::nat. real n * (ln (real n + 2)) powr (2 / 3))
      \<in> O(\<lambda>n. real (card (path_k_V n)) *
            (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
  proof (rule landau_o.big_mono)
    show "eventually
        (\<lambda>n::nat. norm (real n * (ln (real n + 2)) powr (2 / 3)) \<le>
          norm (real (card (path_k_V n)) *
            (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))) at_top"
    proof (intro always_eventually allI)
      fix n :: nat
      have card_eq: "card (path_k_V n) = Suc n"
        by (rule path_k_card_V)
      have f2: "(ln (real n + 2)) powr (2 / 3)
          \<le> (ln (real (Suc n) + 2)) powr (2 / 3)"
      proof (rule powr_mono2)
        show "0 \<le> (2 / 3 :: real)" by simp
        show "0 \<le> ln (real n + 2)" by simp
        show "ln (real n + 2) \<le> ln (real (Suc n) + 2)" by simp
      qed
      have prod_le: "real n * (ln (real n + 2)) powr (2 / 3)
          \<le> real (Suc n) * (ln (real (Suc n) + 2)) powr (2 / 3)"
      proof (rule mult_mono)
        show "real n \<le> real (Suc n)" by simp
        show "(ln (real n + 2)) powr (2 / 3)
            \<le> (ln (real (Suc n) + 2)) powr (2 / 3)" by (rule f2)
        show "0 \<le> real (Suc n)" by simp
        show "0 \<le> (ln (real n + 2)) powr (2 / 3)" by simp
      qed
      have f_nonneg: "0 \<le> real n * (ln (real n + 2)) powr (2 / 3)"
        by simp
      have g_nonneg: "0 \<le> real (Suc n) * (ln (real (Suc n) + 2)) powr (2 / 3)"
        by simp
      show "norm (real n * (ln (real n + 2)) powr (2 / 3)) \<le>
          norm (real (card (path_k_V n)) *
            (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
        using prod_le f_nonneg g_nonneg by (simp add: card_eq)
    qed
  qed
  show ?thesis
    using base dom by (rule landau_o.big_trans)
qed

text \<open>
  \<^bold>\<open>Factoring the cost hypothesis through the library cost bound (B2 scaffolding).\<close>
  The verbatim @{const bmssp_refined_graph_time_bound} hypothesis of the headline
  above is exactly what the proven library theorem
  @{thm [source] strict_tie_breaking_digraph.charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree}
  delivers from the canonical closed-bound predicate
  @{const strict_tie_breaking_digraph.charged_direct_insert_closed_refined_bound_log_params_fixed_degree}
  on the decoupled family (the path is fully reachable and unit out-degree, so the
  two side conditions are automatic).  Discharging \<open>charged_cost_bound\<close> therefore
  reduces to the canonical closed-bound predicate at the inflated schedule, which
  is the single remaining obligation of milestone \textbf{B2}.
\<close>

lemma eventually_path_nonvac_cost_bound_if_closed_bound:
  assumes closed_bound:
    "eventually
      (\<lambda>n. strict_tie_breaking_digraph.charged_direct_insert_closed_refined_bound_log_params_fixed_degree
        (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n)) at_top"
  shows "eventually
    (\<lambda>n. \<forall>c.
      strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
        (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c \<longrightarrow>
      c \<le> bmssp_refined_graph_time_bound
        (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. n) (Suc n)) at_top"
  using closed_bound
proof eventually_elim
  case (elim n)
  interpret bpi: bounded_reduced_positive_instance
    "path_k_V n" "path_k_E n" "path_k_weight n" 0 1
    by (rule path_k_bounded_instance)
  show ?case
  proof (intro allI impI)
    fix c
    assume cost: "bpi.charged_direct_insert_top_level_cost 1 (n * n) c"
    have "c \<le> bmssp_refined_graph_time_bound
        (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. bpi.edge_count) bpi.vertex_count"
      by (rule bpi.charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree
        [OF bpi.all_vertices_reachable bpi.bounded_edge_outdegree elim cost])
    then show "c \<le> bmssp_refined_graph_time_bound
        (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. n) (Suc n)"
      by (simp add: bpi.edge_count_def bpi.vertex_count_def path_k_card_E path_k_card_V)
  qed
qed

text \<open>
  The headline phrased against the canonical obligations: top-level runs exist and
  the closed refined bound holds, both eventually.  This trims \textbf{B3} to the
  two library-shaped premises that \textbf{B1}/\textbf{B2} must make unconditional.
\<close>

theorem path_nonvac_runtime_bigo_card_V_if_runs_and_closed_bound:
  assumes charged_runs_exist:
    "eventually
      (\<lambda>n. \<exists>c. strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
        (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c) at_top"
    and closed_bound:
    "eventually
      (\<lambda>n. strict_tie_breaking_digraph.charged_direct_insert_closed_refined_bound_log_params_fixed_degree
        (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n)) at_top"
  shows "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real (card (path_k_V n)) *
           (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
  by (rule path_nonvac_runtime_bigo_card_V_if_runs_and_cost_bound
      [OF charged_runs_exist eventually_path_nonvac_cost_bound_if_closed_bound[OF closed_bound]])

text \<open>
  \<^bold>\<open>Milestone B1 applied to the headline.\<close>  The run-existence premise of the
  headline is now genuinely \<^emph>\<open>discharged\<close> (not merely bypassed by the vacuous
  least-cost constant): @{thm [source] eventually_path_nonvac_charged_cost_exists}
  proves a charged top-level run exists for all but finitely many \<open>n\<close>, so the
  headline reduces to the single canonical cost obligation \<open>closed_bound\<close>
  (\textbf{B2}).  This makes the runtime claim genuinely non-vacuous: the
  bounded quantity is the cost of a run that provably exists.\<close>
theorem path_nonvac_runtime_bigo_card_V_if_closed_bound_runs_discharged:
  assumes closed_bound:
    "eventually
      (\<lambda>n. strict_tie_breaking_digraph.charged_direct_insert_closed_refined_bound_log_params_fixed_degree
        (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n)) at_top"
  shows "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real (card (path_k_V n)) *
           (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
  by (rule path_nonvac_runtime_bigo_card_V_if_runs_and_closed_bound
      [OF eventually_path_nonvac_charged_cost_exists closed_bound])


subsection \<open>Dropping the run-existence premise (B1, unconditional in runs)\<close>

lemma Least_le_or_const:
  fixes P :: "nat \<Rightarrow> bool" and B :: nat
  assumes "\<And>c. P c \<Longrightarrow> c \<le> B"
  shows "(LEAST c. P c) \<le> B + (LEAST c::nat. \<not> True)"
proof (cases "\<exists>c. P c")
  case True
  then obtain c where "P c" by blast
  then have "(LEAST c. P c) \<le> c" by (rule Least_le)
  also have "c \<le> B" using assms[OF \<open>P c\<close>] .
  finally show ?thesis by simp
next
  case False
  then have "(\<lambda>c. P c) = (\<lambda>c. \<not> True)" by auto
  then show ?thesis by simp
qed

lemma path_refined_bound_bigo:
  "(\<lambda>n. real (bmssp_refined_graph_time_bound
            (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. n) (Suc n)))
     \<in> O(\<lambda>n. sssp_time_target (\<lambda>n. n) n)"
  by (rule bmssp_refined_cost_bound_bigo_sssp_time_target_log_params_bounded_degree_square_arg_slack
      [where D = 1 and Cn = 2 and Cm = 1
        and v = "\<lambda>n. Suc n" and m' = "\<lambda>n. n" and m = "\<lambda>n. n"])
     (simp_all add: eventually_at_top_linorderI[of 1])

lemma sssp_time_target_self_ge:
  "eventually (\<lambda>n::nat. real K \<le> sssp_time_target (\<lambda>n. n) n) at_top"
proof (rule eventually_at_top_linorderI[of "max 1 K"])
  fix n :: nat assume n: "max 1 K \<le> n"
  have n1: "1 \<le> n" and nK: "K \<le> n" using n by auto
  have lnge: "1 \<le> ln (real n + 2)"
  proof -
    have "exp (1::real) \<le> 3" by (rule exp_le)
    also have "(3::real) \<le> real n + 2" using n1 by simp
    finally have "exp (1::real) \<le> real n + 2" .
    then show ?thesis by (simp add: ln_ge_iff)
  qed
  have "real K \<le> real n" using nK by simp
  also have "real n = real n * 1" by simp
  also have "\<dots> \<le> real n * (ln (real n + 2)) powr (2/3)"
  proof (rule mult_left_mono)
    have "(1::real) = 1 powr (2/3)" by simp
    also have "\<dots> \<le> (ln (real n + 2)) powr (2/3)"
      using lnge by (intro powr_mono2) auto
    finally show "(1::real) \<le> (ln (real n + 2)) powr (2/3)" .
  qed simp
  also have "\<dots> = sssp_time_target (\<lambda>n. n) n"
    unfolding sssp_time_target_def sssp_log_factor_def by simp
  finally show "real K \<le> sssp_time_target (\<lambda>n. n) n" .
qed

lemma const_bigo_target:
  "(\<lambda>n::nat. real K) \<in> O(\<lambda>n. sssp_time_target (\<lambda>n. n) n)"
proof (rule landau_o.big_mono, rule eventually_mono[OF sssp_time_target_self_ge[of K]])
  fix n :: nat assume "real K \<le> sssp_time_target (\<lambda>n. n) n"
  then show "norm (real K) \<le> norm (sssp_time_target (\<lambda>n. n) n)" by simp
qed

text \<open>\<^bold>\<open>Milestone B1, unconditional in run-existence.\<close>  The charged running time
  of the decoupled path family is size-parametric \<open>O\<close> of the SSSP time target as
  soon as every charged top-level cost is bounded by the refined graph-time
  budget --- with \<^emph>\<open>no\<close> assumption that a charged run exists.  When a run exists
  the least cost is bounded by the budget; when none exists the least-cost is a
  fixed constant, which the divergent target dominates.\<close>

theorem path_nonvac_runtime_bigo_if_cost_bound:
  assumes charged_cost_bound:
    "eventually
      (\<lambda>n. \<forall>c.
        strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
          (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c \<longrightarrow>
        c \<le> bmssp_refined_graph_time_bound
          (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. n) (Suc n)) at_top"
  shows "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real n * (ln (real n + 2)) powr (2 / 3))"
proof -
  have key: "(\<lambda>n. real (path_nonvac_time n))
      \<in> O(\<lambda>n. sssp_time_target (\<lambda>n. n) n)"
  proof -
    have le: "eventually (\<lambda>n. real (path_nonvac_time n) \<le>
        real (bmssp_refined_graph_time_bound
          (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. n) (Suc n))
        + real (LEAST c::nat. \<not> True)) at_top"
      using charged_cost_bound
    proof eventually_elim
      case (elim n)
      interpret bpi: bounded_reduced_positive_instance
        "path_k_V n" "path_k_E n" "path_k_weight n" 0 1
        by (rule path_k_bounded_instance)
      have time_eq: "path_nonvac_time n
          = (LEAST c. bpi.charged_direct_insert_top_level_cost 1 (n * n) c)"
        by (simp add: path_nonvac_time_def bpi.charged_direct_insert_top_level_time_def)
      have bound: "\<And>c. bpi.charged_direct_insert_top_level_cost 1 (n * n) c \<Longrightarrow>
          c \<le> bmssp_refined_graph_time_bound
            (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. n) (Suc n)"
        using elim by blast
      have "(LEAST c. bpi.charged_direct_insert_top_level_cost 1 (n * n) c)
          \<le> bmssp_refined_graph_time_bound
            (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. n) (Suc n)
          + (LEAST c::nat. \<not> True)"
        by (rule Least_le_or_const[OF bound])
      then show ?case using time_eq by simp
    qed
    have sum_bigo: "(\<lambda>n. real (bmssp_refined_graph_time_bound
          (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. n) (Suc n))
        + real (LEAST c::nat. \<not> True))
        \<in> O(\<lambda>n. sssp_time_target (\<lambda>n. n) n)"
      using path_refined_bound_bigo const_bigo_target by (rule sum_in_bigo)
    have mono: "(\<lambda>n. real (path_nonvac_time n))
        \<in> O(\<lambda>n. real (bmssp_refined_graph_time_bound
              (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
              (\<lambda>_. sssp_log_two_thirds_param (n * n))
              (\<lambda>_. sssp_log_one_third_param (n * n))
              (\<lambda>_. sssp_log_one_third_param (n * n))
              (\<lambda>_. sssp_log_two_thirds_param (n * n))
              (\<lambda>_. n) (Suc n))
            + real (LEAST c::nat. \<not> True))"
    proof (rule landau_o.big_mono)
      show "eventually (\<lambda>n. norm (real (path_nonvac_time n)) \<le>
          norm (real (bmssp_refined_graph_time_bound
            (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_one_third_param (n * n))
            (\<lambda>_. sssp_log_two_thirds_param (n * n))
            (\<lambda>_. n) (Suc n))
          + real (LEAST c::nat. \<not> True))) at_top"
        using le by (auto elim!: eventually_mono)
    qed
    show ?thesis using mono sum_bigo by (rule landau_o.big_trans)
  qed
  then show ?thesis
    unfolding sssp_time_target_def sssp_log_factor_def by simp
qed

text \<open>The same statement in the genuine vertex count, and reduced to the canonical
  closed refined bound: both now \<^emph>\<open>without\<close> the run-existence premise.\<close>

theorem path_nonvac_runtime_bigo_card_V_if_cost_bound:
  assumes charged_cost_bound:
    "eventually
      (\<lambda>n. \<forall>c.
        strict_tie_breaking_digraph.charged_direct_insert_top_level_cost
          (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n) c \<longrightarrow>
        c \<le> bmssp_refined_graph_time_bound
          (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_one_third_param (n * n))
          (\<lambda>_. sssp_log_two_thirds_param (n * n))
          (\<lambda>_. n) (Suc n)) at_top"
  shows "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real (card (path_k_V n)) *
           (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
proof -
  have base: "(\<lambda>n. real (path_nonvac_time n))
      \<in> O(\<lambda>n. real n * (ln (real n + 2)) powr (2 / 3))"
    by (rule path_nonvac_runtime_bigo_if_cost_bound[OF charged_cost_bound])
  have dom: "(\<lambda>n::nat. real n * (ln (real n + 2)) powr (2 / 3))
      \<in> O(\<lambda>n. real (card (path_k_V n)) *
            (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
  proof (rule landau_o.big_mono)
    show "eventually
        (\<lambda>n::nat. norm (real n * (ln (real n + 2)) powr (2 / 3)) \<le>
          norm (real (card (path_k_V n)) *
            (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))) at_top"
    proof (intro always_eventually allI)
      fix n :: nat
      have card_eq: "card (path_k_V n) = Suc n"
        by (rule path_k_card_V)
      have f2: "(ln (real n + 2)) powr (2 / 3)
          \<le> (ln (real (Suc n) + 2)) powr (2 / 3)"
      proof (rule powr_mono2)
        show "0 \<le> (2 / 3 :: real)" by simp
        show "0 \<le> ln (real n + 2)" by simp
        show "ln (real n + 2) \<le> ln (real (Suc n) + 2)" by simp
      qed
      have prod_le: "real n * (ln (real n + 2)) powr (2 / 3)
          \<le> real (Suc n) * (ln (real (Suc n) + 2)) powr (2 / 3)"
      proof (rule mult_mono)
        show "real n \<le> real (Suc n)" by simp
        show "(ln (real n + 2)) powr (2 / 3)
            \<le> (ln (real (Suc n) + 2)) powr (2 / 3)" by (rule f2)
        show "0 \<le> real (Suc n)" by simp
        show "0 \<le> (ln (real n + 2)) powr (2 / 3)" by simp
      qed
      have f_nonneg: "0 \<le> real n * (ln (real n + 2)) powr (2 / 3)"
        by simp
      have g_nonneg: "0 \<le> real (Suc n) * (ln (real (Suc n) + 2)) powr (2 / 3)"
        by simp
      show "norm (real n * (ln (real n + 2)) powr (2 / 3)) \<le>
          norm (real (card (path_k_V n)) *
            (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
        using prod_le f_nonneg g_nonneg by (simp add: card_eq)
    qed
  qed
  show ?thesis
    using base dom by (rule landau_o.big_trans)
qed

theorem path_nonvac_runtime_bigo_card_V_if_closed_bound:
  assumes closed_bound:
    "eventually
      (\<lambda>n. strict_tie_breaking_digraph.charged_direct_insert_closed_refined_bound_log_params_fixed_degree
        (path_k_V n) (path_k_E n) (path_k_weight n) 0 1 (n * n)) at_top"
  shows "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real (card (path_k_V n)) *
           (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
  by (rule path_nonvac_runtime_bigo_card_V_if_cost_bound
      [OF eventually_path_nonvac_cost_bound_if_closed_bound[OF closed_bound]])

subsection \<open>Charged-cost upper bound via the uncharged refinement (B2, uncharged route)\<close>

text \<open>
  \<^bold>\<open>The decoupled charged running time is bounded by the refined graph-time budget
  as soon as a single \<^emph>\<open>uncharged\<close> top-level run exists.\<close>  The charged closed-bound
  predicate bounds \<^emph>\<open>every\<close> charged run, which on the path is genuinely too strong:
  the permissive charged loop admits runs at non-zero source bands whose slice
  accounting breaks band-containment.  The headline only needs the \<^emph>\<open>least\<close> charged
  cost, so it suffices to exhibit one bounded run.  Every uncharged run refines to a
  charged run of equal cost (@{thm [source] unique_shortest_digraph.direct_insert_costed_bmssp_refines_charged_direct_insert}),
  and the uncharged top-level cost is bounded unconditionally by the proven library
  bound @{thm [source] strict_tie_breaking_digraph.finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_amortized}
  (no band-containment side condition).  Hence the least charged cost --- i.e.\ the
  decoupled running time --- is bounded by the refined budget whenever an uncharged
  run exists, reducing \textbf{B2} to the genuinely \<^emph>\<open>constructible\<close> obligation of
  uncharged top-level run existence on the path.
\<close>

context fixes k :: nat
begin
interpretation pk: finite_weighted_digraph
  "path_k_V k" "path_k_E k" "path_k_weight k" 0
  by (rule path_k_finite_weighted_digraph)
interpretation bpi: bounded_reduced_positive_instance
  "path_k_V k" "path_k_E k" "path_k_weight k" 0 1
  by (rule path_k_bounded_instance)

lemma path_k_uncharged_top_run_imp_charged_cost:
  assumes run:
    "bpi.direct_insert_costed_bmssp (1::nat)
       (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
       (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
       (sssp_log_one_third_param N) (cap_at N) (sssp_log_one_third_param N)
       pk.finite_initial_label {0} Infinity d' Infinity U c"
  shows "bpi.charged_direct_insert_top_level_cost 1 N c"
proof -
  have charged:
    "bpi.charged_direct_insert_costed_bmssp (1::nat)
       (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
       (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
       (sssp_log_one_third_param N) (cap_at N) (sssp_log_one_third_param N)
       pk.finite_initial_label {0} Infinity d' Infinity U c"
    by (rule bpi.direct_insert_costed_bmssp_refines_charged_direct_insert[OF run])
  have "bpi.charged_direct_insert_top_level_run 1 N d' U c"
    unfolding bpi.charged_direct_insert_top_level_run_def
    using charged by (simp add: Let_def)
  then show ?thesis
    unfolding bpi.charged_direct_insert_top_level_cost_def by blast
qed

lemma path_k_charged_cost_imp_nonvac_time_le:
  assumes cost: "bpi.charged_direct_insert_top_level_cost 1 (k * k) c"
  shows "path_nonvac_time k \<le> c"
proof -
  have "bpi.charged_direct_insert_top_level_time 1 (k * k) \<le> c"
    by (rule bpi.charged_direct_insert_top_level_time_le[OF cost])
  then show ?thesis by (simp add: path_nonvac_time_def)
qed

lemma path_k_uncharged_run_cost_bound:
  fixes N :: nat
  assumes p2: "2 \<le> sssp_log_one_third_param N"
    and run:
      "bpi.direct_insert_costed_bmssp (1::nat)
         (bmssp_level_cap (sssp_log_one_third_param N) (sssp_log_two_thirds_param N))
         (sssp_log_two_thirds_param N) (sssp_log_one_third_param N)
         (sssp_log_one_third_param N) (cap_at N) (sssp_log_one_third_param N)
         pk.finite_initial_label {0} Infinity d' Infinity U c"
  shows "c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc 1 * sssp_log_one_third_param N) (\<lambda>_. sssp_log_two_thirds_param N)
      (\<lambda>_. sssp_log_one_third_param N) (\<lambda>_. sssp_log_one_third_param N)
      (\<lambda>_. sssp_log_two_thirds_param N) (\<lambda>_. k) (Suc k)"
proof -
  let ?p = "sssp_log_one_third_param N" and ?q = "sssp_log_two_thirds_param N"
  have ppos: "0 < ?p" using p2 by simp
  have qp2: "?q \<le> ?p * ?p" by (rule sssp_log_two_thirds_param_le_one_third_square)
  have pp2: "?p * ?p \<le> Suc 1 * ?p * ?p" by simp
  have df: "(1::nat) \<le> Suc 1 * ?p" using ppos by presburger
  have rp: "0 < ?q" by simp
  have insf: "?q \<le> Suc 1 * ?p * ?p" using qp2 pp2 by linarith
  have seensf: "?p * 1 + Suc 1 * ?p \<le> 2 * (Suc 1 * ?p)" by presburger
  have srcf: "Suc ?p \<le> 2 * (Suc 1 * ?p)" using ppos by presburger
  note base = bpi.finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_amortized
      [where A = "Suc 1 * ?p" and R = ?q and A_insert = "Suc 1 * ?p"
        and \<Delta> = "1::nat" and t = ?q and h = ?p and k = ?p and l = ?p,
        OF bpi.all_vertices_reachable bpi.bounded_edge_outdegree df rp insf insf seensf srcf ppos run]
  show ?thesis
    using base
    by (simp add: bpi.edge_count_def bpi.vertex_count_def path_k_card_E path_k_card_V)
qed

lemma path_k_uncharged_run_imp_nonvac_time_le_bound:
  assumes p2: "2 \<le> sssp_log_one_third_param (k * k)"
    and run:
      "bpi.direct_insert_costed_bmssp (1::nat)
         (bmssp_level_cap (sssp_log_one_third_param (k * k)) (sssp_log_two_thirds_param (k * k)))
         (sssp_log_two_thirds_param (k * k)) (sssp_log_one_third_param (k * k))
         (sssp_log_one_third_param (k * k)) (cap_at (k * k)) (sssp_log_one_third_param (k * k))
         pk.finite_initial_label {0} Infinity d' Infinity U c"
  shows "path_nonvac_time k \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc 1 * sssp_log_one_third_param (k * k)) (\<lambda>_. sssp_log_two_thirds_param (k * k))
      (\<lambda>_. sssp_log_one_third_param (k * k)) (\<lambda>_. sssp_log_one_third_param (k * k))
      (\<lambda>_. sssp_log_two_thirds_param (k * k)) (\<lambda>_. k) (Suc k)"
proof -
  have cost: "bpi.charged_direct_insert_top_level_cost 1 (k * k) c"
    by (rule path_k_uncharged_top_run_imp_charged_cost[OF run])
  have tle: "path_nonvac_time k \<le> c"
    by (rule path_k_charged_cost_imp_nonvac_time_le[OF cost])
  have cle: "c \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc 1 * sssp_log_one_third_param (k * k)) (\<lambda>_. sssp_log_two_thirds_param (k * k))
      (\<lambda>_. sssp_log_one_third_param (k * k)) (\<lambda>_. sssp_log_one_third_param (k * k))
      (\<lambda>_. sssp_log_two_thirds_param (k * k)) (\<lambda>_. k) (Suc k)"
    by (rule path_k_uncharged_run_cost_bound[OF p2 run])
  show ?thesis using tle cle by linarith
qed

text \<open>
  \<^bold>\<open>The cheap charged running time is below the refined graph-time budget.\<close>  The
  genuinely \<^emph>\<open>constructible\<close> analogue of
  @{thm [source] path_k_uncharged_run_imp_nonvac_time_le_bound}: rather than
  assuming an (in the genuine regime non-existent) uncharged top-level run, we use
  the cheap charged top-level cost @{thm [source] path_k_charged_cost_le}, whose
  value \<open>p \<cdot> (p \<cdot> edge_count) + p\<close> is dominated termwise by the refined budget
  --- the edge factor absorbs \<open>p\<^sup>2 \<cdot> edge_count\<close> and the vertex factor absorbs the
  additive \<open>p\<close>.  Hence the least charged cost, i.e.\ the decoupled running time,
  is below the refined budget, with \<^emph>\<open>no\<close> run-existence or cost-bound assumption.
\<close>

lemma path_k_charged_cheap_imp_nonvac_time_le_bound:
  assumes pk_le: "sssp_log_one_third_param (k * k) \<le> k"
    and cover: "Suc k \<le> bmssp_level_cap (sssp_log_one_third_param (k * k))
      (sssp_log_two_thirds_param (k * k)) (sssp_log_one_third_param (k * k))"
    and p2: "2 \<le> sssp_log_one_third_param (k * k)"
  shows "path_nonvac_time k \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc 1 * sssp_log_one_third_param (k * k)) (\<lambda>_. sssp_log_two_thirds_param (k * k))
      (\<lambda>_. sssp_log_one_third_param (k * k)) (\<lambda>_. sssp_log_one_third_param (k * k))
      (\<lambda>_. sssp_log_two_thirds_param (k * k)) (\<lambda>_. k) (Suc k)"
proof -
  let ?p = "sssp_log_one_third_param (k * k)"
  let ?q = "sssp_log_two_thirds_param (k * k)"
  obtain c where cost: "bpi.charged_direct_insert_top_level_cost 1 (k * k) c"
    and cle: "c \<le> ?p * (?p * bpi.edge_count) + ?p"
    using path_k_charged_cost_le[OF pk_le cover p2] by blast
  have tle: "path_nonvac_time k \<le> c"
    by (rule path_k_charged_cost_imp_nonvac_time_le[OF cost])
  have edge: "bpi.edge_count = k"
    by (simp add: bpi.edge_count_def path_k_card_E)
  have c_le2: "c \<le> ?p * (?p * k) + ?p" using cle edge by simp
  have edge_term: "?p * (?p * k) \<le> (?q + ?q + ?p * ?p) * k"
  proof -
    have "?p * (?p * k) = (?p * ?p) * k" by (simp add: mult.assoc)
    also have "\<dots> \<le> (?q + ?q + ?p * ?p) * k" by (rule mult_le_mono1) simp
    finally show ?thesis .
  qed
  have ge1: "(1::nat) \<le> (2 * ?p + 1) * (Suc k)"
    using mult_le_mono[of 1 "2 * ?p + 1" 1 "Suc k"] by simp
  have vert_term: "?p \<le> 2 * (Suc 1 * ?p) * (2 * ?p + 1) * (Suc k)"
  proof -
    have a: "?p \<le> 2 * (Suc 1 * ?p)" by simp
    have b: "2 * (Suc 1 * ?p) \<le> 2 * (Suc 1 * ?p) * (2 * ?p + 1) * (Suc k)"
    proof -
      have "2 * (Suc 1 * ?p) * 1
          \<le> 2 * (Suc 1 * ?p) * ((2 * ?p + 1) * (Suc k))"
        by (rule mult_le_mono2[OF ge1])
      thus ?thesis by (simp add: mult.assoc)
    qed
    from a b show ?thesis by linarith
  qed
  have budget_ge: "?p * (?p * k) + ?p \<le> bmssp_refined_graph_time_bound
      (\<lambda>_. Suc 1 * ?p) (\<lambda>_. ?q) (\<lambda>_. ?p) (\<lambda>_. ?p) (\<lambda>_. ?q) (\<lambda>_. k) (Suc k)"
  proof -
    have "?p * (?p * k) + ?p
        \<le> 2 * (Suc 1 * ?p) * (2 * ?p + 1) * (Suc k) + (?q + ?q + ?p * ?p) * k"
      using edge_term vert_term by linarith
    also have "\<dots> = bmssp_refined_graph_time_bound
        (\<lambda>_. Suc 1 * ?p) (\<lambda>_. ?q) (\<lambda>_. ?p) (\<lambda>_. ?p) (\<lambda>_. ?q) (\<lambda>_. k) (Suc k)"
      by (simp add: bmssp_refined_graph_time_bound_def)
    finally show ?thesis .
  qed
  show ?thesis using tle c_le2 budget_ge by linarith
qed

end

theorem path_nonvac_runtime_bigo_card_V_if_time_le_bound:
  assumes tle:
    "eventually (\<lambda>n. path_nonvac_time n \<le> bmssp_refined_graph_time_bound
        (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n)) (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n)) (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n)) (\<lambda>_. n) (Suc n)) at_top"
  shows "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real (card (path_k_V n)) *
           (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
proof -
  let ?B = "\<lambda>n. bmssp_refined_graph_time_bound
        (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n)) (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n)) (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n)) (\<lambda>_. n) (Suc n)"
  have dom_b: "(\<lambda>n. real (path_nonvac_time n)) \<in> O(\<lambda>n. real (?B n))"
  proof (rule landau_o.big_mono)
    show "eventually (\<lambda>n. norm (real (path_nonvac_time n)) \<le> norm (real (?B n))) at_top"
      using tle by eventually_elim simp
  qed
  have b_target: "(\<lambda>n. real (?B n)) \<in> O(\<lambda>n. sssp_time_target (\<lambda>n. n) n)"
    by (rule path_refined_bound_bigo)
  have base: "(\<lambda>n. real (path_nonvac_time n)) \<in> O(\<lambda>n. sssp_time_target (\<lambda>n. n) n)"
    using dom_b b_target by (rule landau_o.big_trans)
  have base': "(\<lambda>n. real (path_nonvac_time n))
      \<in> O(\<lambda>n. real n * (ln (real n + 2)) powr (2 / 3))"
    using base unfolding sssp_time_target_def sssp_log_factor_def by simp
  have dom: "(\<lambda>n::nat. real n * (ln (real n + 2)) powr (2 / 3))
      \<in> O(\<lambda>n. real (card (path_k_V n)) *
            (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
  proof (rule landau_o.big_mono)
    show "eventually
        (\<lambda>n::nat. norm (real n * (ln (real n + 2)) powr (2 / 3)) \<le>
          norm (real (card (path_k_V n)) *
            (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))) at_top"
    proof (intro always_eventually allI)
      fix n :: nat
      have card_eq: "card (path_k_V n) = Suc n" by (rule path_k_card_V)
      have f2: "(ln (real n + 2)) powr (2 / 3) \<le> (ln (real (Suc n) + 2)) powr (2 / 3)"
        by (rule powr_mono2) simp_all
      have prod_le: "real n * (ln (real n + 2)) powr (2 / 3)
          \<le> real (Suc n) * (ln (real (Suc n) + 2)) powr (2 / 3)"
        by (rule mult_mono[OF _ f2]) simp_all
      show "norm (real n * (ln (real n + 2)) powr (2 / 3)) \<le>
          norm (real (card (path_k_V n)) *
            (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
        using prod_le by (simp add: card_eq)
    qed
  qed
  show ?thesis using base' dom by (rule landau_o.big_trans)
qed

subsection \<open>The unconditional non-vacuous size-parametric running-time bound\<close>

text \<open>
  \<^bold>\<open>Milestones B1/B2/B3, fully discharged.\<close>  The decoupled charged running time
  of the path family is \<^emph>\<open>unconditionally\<close> in the genuine size-parametric class
  \<open>O(card V\<^sub>n \<cdot> (ln (card V\<^sub>n))\<^bsup>2/3\<^esup>)\<close>, with \<^emph>\<open>no\<close> run-existence,
  cost-bound, or closed-bound hypothesis.  Combining
  @{thm [source] eventually_inflated_pivot_regime} (the genuine \<open>2 \<le> p \<le> n\<close>
  pivot regime where the cap covers the path holds eventually) with
  @{thm [source] path_k_charged_cheap_imp_nonvac_time_le_bound} (the cheap charged
  top-level cost lies below the refined graph-time budget) discharges the time
  hypothesis of @{thm [source] path_nonvac_runtime_bigo_card_V_if_time_le_bound}.

  This is the unconditional form of the conditional headline
  @{thm [source] path_nonvac_runtime_bigo_card_V_if_runs_and_closed_bound}: both of
  its premises (eventual charged-run existence and the canonical closed refined
  bound) are now dropped.  The running time bounded here is genuinely
  non-vacuous: it is the \<^emph>\<open>least\<close> charged cost of the decoupled family, a cost of
  a charged top-level run that provably exists and is provably small.
\<close>

theorem path_nonvac_runtime_bigo_card_V_unconditional:
  "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real (card (path_k_V n)) *
           (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
proof (rule path_nonvac_runtime_bigo_card_V_if_time_le_bound)
  show "eventually
      (\<lambda>n. path_nonvac_time n \<le> bmssp_refined_graph_time_bound
        (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. n) (Suc n)) at_top"
    using eventually_inflated_pivot_regime
  proof eventually_elim
    case (elim n)
    show ?case
      by (rule path_k_charged_cheap_imp_nonvac_time_le_bound) (use elim in auto)
  qed
qed

text \<open>
  The same unconditional bound restated against the two library-shaped premises of
  the conditional headline, witnessing that both have been discharged: the charged
  runtime is in the size-parametric class with neither the run-existence premise
  nor the closed refined bound assumed.
\<close>

theorem path_nonvac_runtime_bigo_card_V_runs_and_closed_bound_discharged:
  "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real (card (path_k_V n)) *
           (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
  by (rule path_nonvac_runtime_bigo_card_V_unconditional)


definition path_uncharged_top_run :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "path_uncharged_top_run n d' U c \<longleftrightarrow>
     unique_shortest_digraph.direct_insert_costed_bmssp (path_k_V n) (path_k_E n) (path_k_weight n) 0
       (1::nat) (bmssp_level_cap (sssp_log_one_third_param (n * n)) (sssp_log_two_thirds_param (n * n)))
       (sssp_log_two_thirds_param (n * n)) (sssp_log_one_third_param (n * n))
       (sssp_log_one_third_param (n * n)) (cap_at (n * n)) (sssp_log_one_third_param (n * n))
       (finite_weighted_digraph.finite_initial_label (path_k_V n) (path_k_E n) (path_k_weight n) 0)
       {0} Infinity d' Infinity U c"

lemma eventually_path_nonvac_time_le_bound_if_uncharged_runs:
  assumes ex: "eventually (\<lambda>n. \<exists>d' U c. path_uncharged_top_run n d' U c) at_top"
  shows "eventually (\<lambda>n. path_nonvac_time n \<le> bmssp_refined_graph_time_bound
        (\<lambda>_. Suc 1 * sssp_log_one_third_param (n * n)) (\<lambda>_. sssp_log_two_thirds_param (n * n))
        (\<lambda>_. sssp_log_one_third_param (n * n)) (\<lambda>_. sssp_log_one_third_param (n * n))
        (\<lambda>_. sssp_log_two_thirds_param (n * n)) (\<lambda>_. n) (Suc n)) at_top"
  using ex eventually_inflated_pivot_regime
proof eventually_elim
  case (elim n)
  interpret pk: finite_weighted_digraph
    "path_k_V n" "path_k_E n" "path_k_weight n" 0
    by (rule path_k_finite_weighted_digraph)
  interpret bpi: bounded_reduced_positive_instance
    "path_k_V n" "path_k_E n" "path_k_weight n" 0 1
    by (rule path_k_bounded_instance)
  from elim obtain d' U c where
    run: "bpi.direct_insert_costed_bmssp (1::nat)
       (bmssp_level_cap (sssp_log_one_third_param (n * n)) (sssp_log_two_thirds_param (n * n)))
       (sssp_log_two_thirds_param (n * n)) (sssp_log_one_third_param (n * n))
       (sssp_log_one_third_param (n * n)) (cap_at (n * n)) (sssp_log_one_third_param (n * n))
       pk.finite_initial_label {0} Infinity d' Infinity U c"
    unfolding path_uncharged_top_run_def by blast
  have p2: "2 \<le> sssp_log_one_third_param (n * n)" using elim by simp
  show ?case
    by (rule path_k_uncharged_run_imp_nonvac_time_le_bound[OF p2 run])
qed

theorem path_nonvac_runtime_bigo_card_V_if_uncharged_runs:
  assumes ex: "eventually (\<lambda>n. \<exists>d' U c. path_uncharged_top_run n d' U c) at_top"
  shows "(\<lambda>n. real (path_nonvac_time n))
     \<in> O(\<lambda>n. real (card (path_k_V n)) *
           (ln (real (card (path_k_V n)) + 2)) powr (2 / 3))"
  by (rule path_nonvac_runtime_bigo_card_V_if_time_le_bound
      [OF eventually_path_nonvac_time_le_bound_if_uncharged_runs[OF ex]])




subsection \<open>Charged closed-bound engine (B2): the charged level recurrence solver\<close>

text \<open>
  The charged top-level closed-bound predicate
  @{const strict_tie_breaking_digraph.charged_direct_insert_closed_refined_bound_log_params_fixed_degree}
  bounds \<^emph>\<open>every\<close> charged top-level run.  The uncharged analogue is already solved
  by @{thm [source] strict_tie_breaking_digraph.direct_insert_costed_bmssp_level_bound_from_local_budgets_with_invariants_and_edge_budget};
  here we build the charged analogue, threading the charged per-step closer
  @{thm [source] strict_tie_breaking_digraph.charged_direct_insert_costed_nonbase_step_closes_level_bound_from_child_bound_with_invariants_and_edge_budget}
  through the recursion.  The two semantic obligations the charged closer carries
  --- the loop edge budget and the source-progress (no-stranding) invariant --- are
  discharged generically here (edge budget) and on the path below (source progress).
\<close>

context strict_tie_breaking_digraph
begin

text \<open>Charged analogue of
  @{thm [source] direct_insert_costed_partition_loop_state_trivial_edge_budget}: the
  separated direct/lower edge-range sums of a charged loop step are dominated by the
  outgoing-edge count of the produced loop output, with combined factor \<open>t + h\<close>.\<close>

lemma charged_direct_insert_costed_partition_loop_state_trivial_edge_budget:
  assumes run:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  shows "t * sum_list
      (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
    h * sum_list (map card (range_tree_child_edge_range_list P a betas bs))
    \<le> (t + h) * card (outgoing_edges U)"
proof -
  have mono: "nondecreasing_from a bs"
    by (rule charged_direct_insert_costed_partition_loop_state_mono[OF run])
  have trace: "concrete_partition_loop_trace P B a bs d' B' charged_Us U"
    by (rule charged_direct_insert_costed_partition_loop_state_trace
      [OF run sound pre P_reaches])
  have children:
    "list_all2 (\<lambda>U X. U = X \<and> complete_on d' U) charged_Us
      (range_tree_chain_list P a bs B')"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have U_def: "U = bound_tree P (Fin a) \<union> \<Union>(set charged_Us)"
    using trace unfolding concrete_partition_loop_trace_def by blast
  have Union_eq:
    "\<Union>(set charged_Us) = \<Union>(set (range_tree_chain_list P a bs B'))"
    using children by (induction rule: list_all2_induct) auto
  have U_eq_chain:
    "U = bound_tree P (Fin a) \<union> range_tree_chain P a bs B'"
    using U_def Union_eq Union_range_tree_chain_list[of P a bs B'] by simp
  have chain_subset: "range_tree_chain P a bs B' \<subseteq> U"
    using U_eq_chain by blast
  have outgoing_subset:
    "outgoing_edges (range_tree_chain P a bs B') \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF chain_subset])
  have card_out_le:
    "card (outgoing_edges (range_tree_chain P a bs B')) \<le>
      card (outgoing_edges U)"
    by (rule card_mono) (simp_all add: outgoing_subset)
  have sum_le_chain:
    "h * sum_list (map card (range_tree_child_edge_range_list P a betas bs)) +
     t * sum_list
       (map card (range_tree_child_direct_edge_range_list P B a betas bs))
     \<le> (h + t) * card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule weighted_sum_child_lower_direct_edge_ranges_le_outgoing_edges_chain
      [OF mono])
  have chain_to_U:
    "(h + t) * card (outgoing_edges (range_tree_chain P a bs B')) \<le>
      (h + t) * card (outgoing_edges U)"
    using card_out_le by simp
  show ?thesis
    using sum_le_chain chain_to_U by (simp add: algebra_simps)
qed

text \<open>\<^bold>\<open>Per-child amortized output \<open>\<rightarrow>\<close> slice converter (B2 engine).\<close>  The charged
  amortized loop closer
  @{thm [source] charged_direct_insert_costed_partition_loop_state_closes_amortized_bound_from_child_costs}
  consumes per-child amortized bounds stated against the \<^emph>\<open>disjoint range-tree
  slices\<close>.  A recursion-level induction instead produces per-child bounds against
  the child \<^emph>\<open>outputs\<close>.  Whenever each output sits inside its slice (the
  band-containment maintained by the descending recursion), the amortized budget's
  monotonicity @{thm [source] bmssp_amortized_cost_bound_mono} lifts the
  output bounds to the slice bounds the closer needs.\<close>

lemma list_all2_bmssp_amortized_cost_bound_lift_subset:
  assumes outb:
    "list_all2 (\<lambda>c_child UB.
        c_child \<le> bmssp_amortized_cost_bound A R h t q L (snd UB) (fst UB))
      child_costs output_pairs"
    and contain:
    "list_all2 (\<lambda>OB SB.
        fst OB \<subseteq> fst SB \<and> snd OB = snd SB \<and> finite (fst SB))
      output_pairs slice_pairs"
  shows "list_all2 (\<lambda>c_child UB.
      c_child \<le> bmssp_amortized_cost_bound A R h t q L (snd UB) (fst UB))
    child_costs slice_pairs"
proof (rule list_all2_all_nthI)
  show "length child_costs = length slice_pairs"
    using outb contain by (simp add: list_all2_lengthD)
next
  fix i assume i: "i < length child_costs"
  have i2: "i < length output_pairs"
    using outb i by (simp add: list_all2_lengthD)
  have c_le:
    "child_costs ! i \<le>
      bmssp_amortized_cost_bound A R h t q L
        (snd (output_pairs ! i)) (fst (output_pairs ! i))"
    using list_all2_nthD[OF outb i] by simp
  have cont:
    "fst (output_pairs ! i) \<subseteq> fst (slice_pairs ! i) \<and>
      snd (output_pairs ! i) = snd (slice_pairs ! i) \<and>
      finite (fst (slice_pairs ! i))"
    using list_all2_nthD[OF contain i2] by simp
  have "bmssp_amortized_cost_bound A R h t q L
        (snd (output_pairs ! i)) (fst (output_pairs ! i))
      \<le> bmssp_amortized_cost_bound A R h t q L
        (snd (slice_pairs ! i)) (fst (slice_pairs ! i))"
    using cont bmssp_amortized_cost_bound_mono[of "fst (output_pairs ! i)"
        "fst (slice_pairs ! i)" A R h t q L "snd (slice_pairs ! i)"]
    by auto
  with c_le show
    "child_costs ! i \<le>
      bmssp_amortized_cost_bound A R h t q L
        (snd (slice_pairs ! i)) (fst (slice_pairs ! i))"
    by linarith
qed

text \<open>\<^bold>\<open>Band containment (B2 engine): a settled child output sits inside its slice.\<close>
  The descending recursion maintains, at a loop step with lower band \<open>a\<close>, two
  modular invariants of the working label \<open>d\<close> over the pivot set \<open>S\<close>: a
  \<^emph>\<open>label floor\<close> \<open>a \<le> d x\<close> and \<^emph>\<open>prefix exactness\<close> below \<open>a\<close>.  Under those a
  pulled child's whole produced tree @{term "bound_tree S B"} lies at or above the
  band, hence inside the band-range slice @{term "range_tree S a B"} --- using only
  @{thm [source] tree_path_dist_le} and the floor/exactness reductions of the note
  preceding @{thm [source] split_below_inter_bound_tree_empty_if_label_ge_exact}.\<close>

lemma bound_tree_subset_range_tree_if_floor_exact:
  assumes floor: "\<And>x. x \<in> S \<Longrightarrow> a \<le> d x"
    and exact: "\<And>u. u \<in> S \<Longrightarrow> dist s u < a \<Longrightarrow> d u = dist s u"
  shows "bound_tree S B \<subseteq> range_tree S a B"
proof
  fix v assume "v \<in> bound_tree S B"
  then have vtree: "v \<in> tree_set S" and vbelow: "below_bound (dist s v) B"
    unfolding bound_tree_eq_tree_set by auto
  from vtree obtain u where uS: "u \<in> S" and tp: "tree_path u v"
    unfolding tree_set_def by blast
  have du_le: "dist s u \<le> dist s v" by (rule tree_path_dist_le[OF tp])
  have a_le_u: "a \<le> dist s u"
  proof (rule ccontr)
    assume "\<not> a \<le> dist s u"
    then have lt: "dist s u < a" by simp
    then have "d u = dist s u" using exact[OF uS] by simp
    with lt have "d u < a" by simp
    with floor[OF uS] show False by simp
  qed
  from a_le_u du_le have "a \<le> dist s v" by simp
  with vtree vbelow show "v \<in> range_tree S a B"
    unfolding range_tree_def by simp
qed

lemma bound_tree_split_below_subset_range_tree_if_floor_exact:
  assumes floor: "\<And>x. x \<in> P \<Longrightarrow> a \<le> d x"
    and exact: "\<And>u. u \<in> P \<Longrightarrow> dist s u < a \<Longrightarrow> d u = dist s u"
  shows "bound_tree (split_below d P beta) B \<subseteq> range_tree P a B"
proof (rule subset_trans[OF _ range_tree_split_below_subset])
  show "bound_tree (split_below d P beta) B
      \<subseteq> range_tree (split_below d P beta) a B"
  proof (rule bound_tree_subset_range_tree_if_floor_exact)
    fix x assume x: "x \<in> split_below d P beta"
    have "x \<in> P" by (rule rev_subsetD[OF x split_below_subset])
    then show "a \<le> d x" by (rule floor)
  next
    fix u assume u: "u \<in> split_below d P beta" and ult: "dist s u < a"
    have "u \<in> P" by (rule rev_subsetD[OF u split_below_subset])
    then show "d u = dist s u" using ult by (rule exact)
  qed
qed

text \<open>\<^bold>\<open>Charged per-child amortized slice-bound propagator (B2 engine).\<close>  The
  charged amortized loop closer
  @{thm [source] charged_direct_insert_costed_partition_loop_state_closes_amortized_bound_from_child_costs}
  consumes per-child amortized bounds stated against the disjoint range-tree
  slices @{term "range_tree_child_bound_pair_list P a betas bs"}.  A recursion-level
  induction supplies per-child bounds against the child \<^emph>\<open>outputs\<close>; whenever each
  output sits inside its slice --- a @{const list_all2} band-containment that the
  descending recursion threads as data (and which is trivial on the source band
  \<open>a = 0\<close>, where the slice is the full bounded tree) --- the amortized budget's
  monotonicity lifts the output bounds to the slice bounds.  Unlike the unusable
  library closers, the per-child budget here is stated against \<^emph>\<open>outputs\<close>, so it is
  dischargeable by an ordinary inductive hypothesis.\<close>

lemma charged_child_amortized_slice_bounds_from_output_and_containment:
  "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U c child_costs \<Longrightarrow>
    P \<subseteq> V \<Longrightarrow>
    k * card P \<le> cap \<Longrightarrow>
    tree_antichain P \<Longrightarrow>
    (\<And>c_child U_child S_child B_child d_child B_child'.
        \<lbrakk>charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child) \<Longrightarrow>
    list_all2 (\<lambda>U_out SB. U_out \<subseteq> fst SB) child_outputs
      (range_tree_child_bound_pair_list P a betas bs) \<Longrightarrow>
    list_all2 (\<lambda>c_child SB.
        case SB of (U_child, B_child) \<Rightarrow>
          c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
      child_costs (range_tree_child_bound_pair_list P a betas bs)"
  and charged_direct_insert_costed_bmssp_child_amortized_slice_bounds_trivial:
  "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c \<Longrightarrow> True"
proof (induction rule:
    charged_direct_insert_costed_partition_loop_state_charged_direct_insert_costed_bmssp.inducts)
  case (Charged_Direct_Insert_State_Done D a B d' P \<Delta> M_of t h k cap l d)
  then show ?case by simp
next
  case (Charged_Direct_Insert_State_Stop a B d' P k cap \<Delta> M_of t h l d D)
  then show ?case by simp
next
  case (Charged_Direct_Insert_State_Step D M_of l Bmax S_pull beta D_pull B d
      P a b B' d' k cap \<Delta> t h d_child U_child c_child charged_child
      direct_edge_batch lower_edge_batch source_batch batch D_next c_pull
      c_direct c_lower c_sources betas bs charged_tail child_outputs_tail
      U_tail c_tail child_costs_tail c)
  have contain_unf:
    "list_all2 (\<lambda>U_out SB. U_out \<subseteq> fst SB)
        (U_child # child_outputs_tail)
        ((range_tree P a (Fin b), Fin beta) #
          range_tree_child_bound_pair_list P b betas bs)"
    using Charged_Direct_Insert_State_Step.prems by simp
  have contain_head: "U_child \<subseteq> range_tree P a (Fin b)"
    using contain_unf by simp
  have contain_tail:
    "list_all2 (\<lambda>U_out SB. U_out \<subseteq> fst SB) child_outputs_tail
      (range_tree_child_bound_pair_list P b betas bs)"
    using contain_unf by simp
  have tail:
    "list_all2 (\<lambda>c_child SB.
        case SB of (U_child, B_child) \<Rightarrow>
          c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
      child_costs_tail (range_tree_child_bound_pair_list P b betas bs)"
    using Charged_Direct_Insert_State_Step.IH
      Charged_Direct_Insert_State_Step.prems contain_tail by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Charged_Direct_Insert_State_Step unfolding pull_separates_def by blast
  have below_pull: "\<And>x. x \<in> S_pull \<Longrightarrow> below_bound (d x) (Fin beta)"
  proof -
    fix x assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta"
      using Charged_Direct_Insert_State_Step by blast
    then show "below_bound (d x) (Fin beta)"
      using xS unfolding split_below_def by auto
  qed
  have pull_k_cap: "k * card S_pull \<le> cap"
  proof -
    have "S_pull = split_below d P beta"
      using Charged_Direct_Insert_State_Step by blast
    then show ?thesis
      using split_below_scaled_card_le
        [OF Charged_Direct_Insert_State_Step.prems(1)
          Charged_Direct_Insert_State_Step.prems(2), of d beta] by simp
  qed
  have pull_anti: "tree_antichain S_pull"
  proof -
    have "S_pull = split_below d P beta"
      using Charged_Direct_Insert_State_Step by blast
    then show ?thesis
      using split_below_tree_antichain
        [OF Charged_Direct_Insert_State_Step.prems(3), of d beta] by simp
  qed
  have child_run:
    "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull
      (Fin beta) d_child (Fin b) U_child c_child"
    using Charged_Direct_Insert_State_Step by blast
  have pre_pull: "bmssp_pre_full d S_pull (Fin beta)"
    using Charged_Direct_Insert_State_Step by blast
  have reaches_pull: "\<And>x. x \<in> S_pull \<Longrightarrow> reachable s x"
    using Charged_Direct_Insert_State_Step by blast
  have head_out:
    "c_child \<le> bmssp_amortized_cost_bound A R h t q L (Fin beta) U_child"
    by (rule Charged_Direct_Insert_State_Step.prems(4)
      [OF child_run pre_pull reaches_pull card_pull below_pull
        pull_k_cap pull_anti])
  have head:
    "c_child \<le>
      bmssp_amortized_cost_bound A R h t q L (Fin beta) (range_tree P a (Fin b))"
    using head_out
      bmssp_amortized_cost_bound_mono[OF contain_head finite_range_tree,
        of A R h t q L "Fin beta"]
    by simp
  show ?case
    using head tail by simp
next
  case (Charged_Direct_Insert_Base S x \<Delta> M_of t h k cap d B)
  then show ?case by simp
next
  case (Charged_Direct_Insert_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' charged_Us child_outputs U_loop c_loop child_costs_loop U c)
  then show ?case by simp
qed

text \<open>\<^bold>\<open>Charged amortized level recurrence (B2 engine).\<close>  The charged analogue of
  @{thm [source] direct_insert_costed_bmssp_amortized_bound_from_local_budgets_with_invariants}:
  a strong-induction on the recursion level closes the charged run cost against the
  amortized graph budget @{const bmssp_amortized_cost_bound} of the produced output
  @{term U}.  The per-loop scan/insert budget, the source-progress (settledness)
  oracle, and the band-containment of child outputs are taken as the modular
  threaded side-conditions @{term step_budget}, @{term source_progress} and
  @{term child_containment}; each is discharged on the decoupled path below, where
  the source band \<open>a = 0\<close> makes them transparent.\<close>

lemma charged_direct_insert_costed_bmssp_amortized_bound_from_budgets_progress_containment:
  assumes base_budget: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and source_factor: "Suc h \<le> A"
    and k_pos: "0 < k"
    and M_cap: "\<And>i. i \<le> l \<Longrightarrow> M_of i \<le> cap"
    and step_budget:
      "\<And>l d S B D c_insert d' a betas bs B' charged_Us child_outputs U_loop
          c_loop child_costs U.
        D = label_partition_view
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k cap d S B) \<Longrightarrow>
        charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
          (find_pivots_label_capped k cap d S B)
          (find_pivots_pivots_capped k cap d S B) B d' D a betas bs B'
          charged_Us child_outputs U_loop c_loop child_costs \<Longrightarrow>
        complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k cap d S B v = dist s v} \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d S B \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> reachable s x) \<Longrightarrow>
        (\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B) \<Longrightarrow>
        k * card S \<le> cap \<Longrightarrow>
        tree_antichain S \<Longrightarrow>
        fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
    and source_progress:
      "\<And>l' d P B d' D a betas bs B' charged_Us child_outputs U c child_costs
          child_sources.
        charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l' d P B
          d' D a betas bs B' charged_Us child_outputs U c child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        list_all2
          (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
            charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l' d S_child B_child
              d_child B_child' U_child c_child \<and>
            bmssp_pre_full d S_child B_child \<and>
            (\<forall>x\<in>S_child. reachable s x) \<and>
            card S_child \<le> M_of l' \<and>
            (\<forall>x\<in>S_child. below_bound (d x) B_child))
          child_sources (range_tree_child_list P a bs) \<Longrightarrow>
        sum_list (map card child_sources) \<le> card (range_tree_chain P a bs B')"
    and child_containment:
      "\<And>l' d P B d' D a betas bs B' charged_Us child_outputs U c child_costs.
        charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l' d P B
          d' D a betas bs B' charged_Us child_outputs U c child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        list_all2 (\<lambda>U_out SB. U_out \<subseteq> fst SB) child_outputs
          (range_tree_child_bound_pair_list P a betas bs)"
    and run:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_k_cap: "k * card S \<le> cap"
    and S_anti: "tree_antichain S"
  shows "c \<le> bmssp_amortized_cost_bound A R h t l (2 * l + 1) B U"
  using run sound pre S_reaches below S_k_cap S_anti M_cap
proof (induction l arbitrary: d S B d' B' U c rule: less_induct)
  case (less l)
  show ?case
  proof (cases l)
    case 0
    have run0:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
      using less.prems(1) 0 by simp
    show ?thesis
      using run0
    proof cases
      case (Charged_Direct_Insert_Base x)
      have scan:
        "base_case_scan_cost \<Delta> k x B \<le>
          R * card (outgoing_edges (base_case_vertices k x B))"
        using R_pos unfolding base_case_scan_cost_def by simp
      show ?thesis
        using Charged_Direct_Insert_Base 0 scan
        by (simp add: bmssp_amortized_cost_bound_def; linarith)
    qed
  next
    case (Suc l0)
    have run_suc:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l0) d S B d' B' U c"
      using less.prems(1) Suc by simp
    show ?thesis
    proof (cases rule: charged_direct_insert_costed_bmssp_SucE[OF run_suc])
      case (1 c_insert a betas bs charged_Us child_outputs U_loop c_loop
          child_costs_loop)
      let ?d_fp = "find_pivots_label_capped k cap d S B"
      let ?P = "find_pivots_pivots_capped k cap d S B"
      let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
      have sound_fp: "sound_label ?d_fp"
        unfolding find_pivots_label_capped_def
        by (rule fp_iter_capped_label_sound[OF less.prems(2) less.prems(4)])
      have pivot_pre: "bmssp_pre_full ?d_fp ?P B"
        using find_pivots_capped_establishes_pivot_pre_concrete
          [OF less.prems(2) less.prems(3) less.prems(4)] .
      have S_subset: "S \<subseteq> V"
        using less.prems(3) unfolding bmssp_pre_full_def by blast
      have P_subset_S: "?P \<subseteq> S"
        unfolding find_pivots_pivots_capped_def by (auto split: if_splits)
      have P_subset_V: "?P \<subseteq> V"
        using P_subset_S S_subset by blast
      have P_reaches: "\<And>x. x \<in> ?P \<Longrightarrow> reachable s x"
        using P_subset_S less.prems(4) by blast
      have P_k_cap: "k * card ?P \<le> cap"
        by (rule find_pivots_pivots_capped_scaled_card_le
          [OF S_subset less.prems(6)])
      have P_anti: "tree_antichain ?P"
        by (rule find_pivots_pivots_capped_tree_antichain[OF less.prems(7)])
      have child_bound:
        "\<And>c_child U_child S_child B_child d_child B_child'.
          \<lbrakk>charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child B_child
              d_child B_child' U_child c_child;
            bmssp_pre_full ?d_fp S_child B_child;
            \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
            card S_child \<le> M_of l0;
            \<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child;
            k * card S_child \<le> cap;
            tree_antichain S_child\<rbrakk>
          \<Longrightarrow> c_child \<le>
            bmssp_amortized_cost_bound A R h t l0 (2 * l0 + 1) B_child U_child"
      proof -
        fix c_child U_child S_child B_child d_child B_child'
        assume child:
            "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child
              B_child d_child B_child' U_child c_child"
          and child_pre: "bmssp_pre_full ?d_fp S_child B_child"
          and child_reaches: "\<And>x. x \<in> S_child \<Longrightarrow> reachable s x"
          and child_below:
            "\<And>x. x \<in> S_child \<Longrightarrow> below_bound (?d_fp x) B_child"
          and child_k_cap: "k * card S_child \<le> cap"
          and child_anti: "tree_antichain S_child"
        have M_cap_child: "\<And>i. i \<le> l0 \<Longrightarrow> M_of i \<le> cap"
          using less.prems(8) Suc by simp
        show "c_child \<le>
            bmssp_amortized_cost_bound A R h t l0 (2 * l0 + 1) B_child U_child"
          by (rule less.IH[of l0 ?d_fp S_child B_child d_child B_child'
                U_child c_child, OF _ child sound_fp child_pre child_reaches
                child_below child_k_cap child_anti M_cap_child])
            (simp add: Suc)
      qed
      have contain:
        "list_all2 (\<lambda>U_out SB. U_out \<subseteq> fst SB) child_outputs
          (range_tree_child_bound_pair_list ?P a betas bs)"
        by (rule child_containment[OF 1(4) sound_fp pivot_pre P_reaches])
      have child_cost_bounds:
        "list_all2 (\<lambda>c_child SB.
            case SB of (U_child, B_child) \<Rightarrow>
              c_child \<le> bmssp_amortized_cost_bound A R h t l0 (2 * l0 + 1)
                B_child U_child)
          child_costs_loop (range_tree_child_bound_pair_list ?P a betas bs)"
        by (rule charged_child_amortized_slice_bounds_from_output_and_containment
          [OF 1(4) P_subset_V P_k_cap P_anti child_bound contain])
      have src_prog:
        "\<And>child_sources.
          list_all2
            (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
              charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l0 ?d_fp S_child
                B_child d_child B_child' U_child c_child \<and>
              bmssp_pre_full ?d_fp S_child B_child \<and>
              (\<forall>x\<in>S_child. reachable s x) \<and>
              card S_child \<le> M_of l0 \<and>
              (\<forall>x\<in>S_child. below_bound (?d_fp x) B_child))
            child_sources (range_tree_child_list ?P a bs) \<Longrightarrow>
          sum_list (map card child_sources) \<le> card (range_tree_chain ?P a bs B')"
        using source_progress[OF 1(4) sound_fp pivot_pre P_reaches] .
      have scan_insert:
        "fp_iter_capped_scan_cost k cap d S S B + c_insert \<le> A * card U"
        by (rule step_budget[OF refl 1(3) 1(4) 1(5) 1(1)
            less.prems(2) less.prems(3) less.prems(4) less.prems(5)
            less.prems(6) less.prems(7)])
      have trace:
        "concrete_partition_loop_trace ?P B a bs d' B' charged_Us U_loop"
        by (rule charged_direct_insert_costed_partition_loop_state_trace
          [OF 1(4) sound_fp pivot_pre P_reaches])
      have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
        by (rule concrete_partition_loop_trace_post[OF trace])
      have finite_U_loop: "finite U_loop"
        using loop_post unfolding bmssp_post_full_def by simp
      have finite_U: "finite U"
        using 1(1) finite_U_loop by simp
      have step:
        "c \<le> bmssp_amortized_cost_bound A R h t
          (Suc l0) (Suc (Suc (2 * l0 + 1))) B U"
        by (rule charged_direct_insert_costed_nonbase_step_closes_amortized_bound_from_child_costs
          [OF 1(4) sound_fp pivot_pre P_reaches child_cost_bounds source_factor
            src_prog 1(1) finite_U scan_insert 1(2)])
      show ?thesis
        using step Suc by simp
    qed
  qed
qed

text \<open>\<^bold>\<open>Charged top-level refined-graph-time bound (B2), conditional on the two
  threaded settledness invariants.\<close>  The charged analogue of
  @{thm [source] finite_initial_label_direct_insert_costed_top_level_correct_and_closed_bmssp_refined_graph_time_bound_level_cap_amortized}:
  every charged top-level run is bounded by the refined graph-time budget, with the
  per-loop scan/insert budget discharged by the bucketed step-cost lemma and the two
  recursion-threaded oracles --- source progress and child-output band-containment ---
  left as the only side-conditions.  On the decoupled path family below both reduce to
  the source-band settledness already isolated for the family, so this delivers the
  canonical closed refined bound unconditionally there.\<close>

theorem finite_initial_label_charged_top_level_refined_bound_amortized:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le \<Delta>"
    and degree_factor: "\<Delta> \<le> A"
    and R_pos: "0 < R"
    and insert_factor: "t \<le> A * k"
    and insert_scaled_factor: "t \<le> A_insert * k"
    and seen_scaled_factor: "k * \<Delta> + A_insert \<le> 2 * A"
    and source_factor: "Suc h \<le> 2 * A"
    and k_pos: "0 < k"
    and source_progress:
      "\<And>l' d P B d' D a betas bs B' charged_Us child_outputs U c child_costs
          child_sources.
        charged_direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l' d P B
          d' D a betas bs B' charged_Us child_outputs U c child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        list_all2
          (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
            charged_direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
              (bmssp_level_cap k t l) l' d S_child B_child
              d_child B_child' U_child c_child \<and>
            bmssp_pre_full d S_child B_child \<and>
            (\<forall>x\<in>S_child. reachable s x) \<and>
            card S_child \<le> bmssp_level_cap k t l' \<and>
            (\<forall>x\<in>S_child. below_bound (d x) B_child))
          child_sources (range_tree_child_list P a bs) \<Longrightarrow>
        sum_list (map card child_sources) \<le> card (range_tree_chain P a bs B')"
    and child_containment:
      "\<And>l' d P B d' D a betas bs B' charged_Us child_outputs U c child_costs.
        charged_direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l' d P B
          d' D a betas bs B' charged_Us child_outputs U c child_costs \<Longrightarrow>
        sound_label d \<Longrightarrow>
        bmssp_pre_full d P B \<Longrightarrow>
        (\<And>x. x \<in> P \<Longrightarrow> reachable s x) \<Longrightarrow>
        list_all2 (\<lambda>U_out SB. U_out \<subseteq> fst SB) child_outputs
          (range_tree_child_bound_pair_list P a betas bs)"
    and run:
      "charged_direct_insert_costed_bmssp \<Delta> (bmssp_level_cap k t) t h k
        (bmssp_level_cap k t l) l
        finite_initial_label {s} Infinity d' Infinity U c"
  shows "c \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
    (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
proof -
  have pre: "bmssp_pre_full finite_initial_label {s} Infinity"
    using all_reachable finite_initial_label_source_complete
    by (rule top_bmssp_pre_full)
  have sound: "sound_label finite_initial_label"
    using finite_initial_label_sound[OF all_reachable] .
  have S_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using all_reachable source_in_V by blast
  have below: "\<And>x. x \<in> {s} \<Longrightarrow>
      below_bound (finite_initial_label x) Infinity"
    by simp
  have top_cap: "k * card {s} \<le> bmssp_level_cap k t l"
  proof -
    have one_le: "1 \<le> bmssp_level_width t l"
      unfolding bmssp_level_width_def by simp
    have "k * 1 \<le> k * bmssp_level_width t l"
      by (rule mult_left_mono[OF one_le]) simp
    then show ?thesis
      unfolding bmssp_level_cap_def by simp
  qed
  have top_anti: "tree_antichain {s}"
    by simp
  have amortized:
    "c \<le> bmssp_amortized_cost_bound (2 * A) R h t l (2 * l + 1) Infinity U"
  proof (rule charged_direct_insert_costed_bmssp_amortized_bound_from_budgets_progress_containment
      [where A = "2 * A" and R = R,
        OF _ R_pos source_factor k_pos _ _ source_progress child_containment
          run sound pre S_reaches below top_cap top_anti])
    show "\<Delta> \<le> 2 * A"
      using degree_factor by simp
  next
    fix i
    assume "i \<le> l"
    then show "bmssp_level_cap k t i \<le> bmssp_level_cap k t l"
      by (rule bmssp_level_cap_mono)
  next
    fix l' d S B D c_insert d' a betas bs B' charged_Us child_outputs
      U_loop c_loop child_costs U
    assume D_def:
        "D = label_partition_view
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
      and insert:
        "partition_initial_insert_cost_bound c_insert t
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B)"
      and loop:
        "charged_direct_insert_costed_partition_loop_state \<Delta> (bmssp_level_cap k t) t h k
          (bmssp_level_cap k t l) l'
          (find_pivots_label_capped k (bmssp_level_cap k t l) d S B)
          (find_pivots_pivots_capped k (bmssp_level_cap k t l) d S B) B d' D
          a betas bs B' charged_Us child_outputs U_loop c_loop child_costs"
      and complete:
        "complete_on d'
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v}"
      and U_def:
        "U = U_loop \<union>
          {v \<in> bound_tree S B'.
            find_pivots_label_capped k (bmssp_level_cap k t l) d S B v =
              dist s v}"
      and sound_s: "sound_label d"
      and pre_s: "bmssp_pre_full d S B"
      and reaches_s: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
      and below_s: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
      and S_k_cap: "k * card S \<le> bmssp_level_cap k t l"
      and anti: "tree_antichain S"
    have seen_success:
      "B' = B \<Longrightarrow>
        card (find_pivots_seen_capped k (bmssp_level_cap k t l) d S B)
        \<le> card U"
      by (rule charged_direct_insert_costed_step_seen_success
        [OF loop U_def sound_s pre_s reaches_s below_s])
    show "fp_iter_capped_scan_cost k (bmssp_level_cap k t l) d S S B +
        c_insert \<le> 2 * A * card U"
      by (rule charged_direct_insert_costed_capped_step_scan_insert_budget_from_scaled_seen_or_threshold
        [OF degree degree_factor insert_factor insert_scaled_factor
          seen_scaled_factor insert loop U_def sound_s pre_s reaches_s
          S_k_cap anti k_pos seen_success])
  qed
  have post_full:
    "bmssp_post_full finite_initial_label {s} Infinity d' Infinity U"
    by (rule charged_direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
  have post: "bmssp_post finite_initial_label {s} Infinity d' Infinity U"
    using bmssp_post_full_imp_post[OF post_full] .
  have U_V: "U = V"
    using post bound_tree_source_infinity[OF all_reachable]
    unfolding bmssp_post_def by auto
  have graph_bound:
    "bmssp_amortized_cost_bound (2 * A) R h t l (2 * l + 1) Infinity U
      \<le> bmssp_refined_graph_time_bound (\<lambda>_. A) (\<lambda>_. R) (\<lambda>_. h)
        (\<lambda>_. l) (\<lambda>_. t) (\<lambda>_. edge_count) vertex_count"
  proof -
    have U_card: "card U = vertex_count"
      unfolding U_V vertex_count_def by simp
    have out_le: "card (outgoing_edges U) \<le> edge_count"
      by (rule edge_count_outgoing_bound)
    have range_le: "card (outgoing_edges_range U 0 Infinity) \<le> edge_count"
      by (rule card_outgoing_edges_range_le_edge_count)
    have out_term:
      "(R + l * h) * card (outgoing_edges U) \<le> (R + l * h) * edge_count"
      using out_le by simp
    have range_term:
      "t * card (outgoing_edges_range U 0 Infinity) \<le> t * edge_count"
      using range_le by simp
    show ?thesis
      unfolding bmssp_amortized_cost_bound_def bmssp_refined_graph_time_bound_def
      using U_card out_term range_term by (simp add: algebra_simps; linarith)
  qed
  show ?thesis
    using amortized graph_bound by linarith
qed

end

end
