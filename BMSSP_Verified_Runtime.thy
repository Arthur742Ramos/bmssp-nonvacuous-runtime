theory BMSSP_Verified_Runtime
  imports BMSSP_Top_Level_Bounds
begin

section \<open>Runtime Bound for a Verified-Correct BMSSP Run\<close>

text \<open>
  The top-level theory \<open>BMSSP_Top_Level_Bounds\<close> proves two facts
  that, taken separately, leave a gap a reader is right to worry about.

  \<^item> \<open>exact_concrete_top_level_run_correct_and_refined_bound_log_params_fixed_degree\<close>
    shows that \emph{one} costed run is simultaneously correct and cost-bounded:
    for a single \<open>exact_concrete_top_level_run\<close> producing output label
    \<open>d'\<close>, completed set \<open>U\<close> and cost \<open>c\<close>, we have
    \<open>U = V\<close>, \<open>sssp_correct d'\<close>, and a closed-form bound on
    \<open>c\<close>.  This is a per-run statement in closed form.

  \<^item> \<open>bmssp_runtime_bigo_target\<close> lifts the closed-form bound to the
    asymptotic headline \<open>O(m * (ln n) powr (2/3))\<close>,
    but it is stated about \<open>T_bmssp D\<close> alone --- the
    \emph{least cost} over valid runs.  As a number, \<open>T_bmssp D N\<close>
    carries no evidence that the run achieving it computes shortest paths.

  The asymptotic headline therefore speaks about a least-cost integer, while the
  correctness theorem speaks about an individual run; nothing yet says the run
  whose cost realises the asymptotic bound is the same run that is proved
  correct.  This theory closes that gap.  Its central observation is that
  \<open>T_bmssp D N\<close>, being a least cost, is realised by an \emph{actual}
  run (by \<open>exact_concrete_top_level_time_witness\<close>), and that this
  realising run is governed by the per-run correctness theorem.  Consequently
  the asymptotic running-time bound is a statement about runs that are
  themselves verified to return exact single-source shortest-path distances.
\<close>

context strict_tie_breaking_digraph
begin

text \<open>
  First, the least-cost value @{term "T_bmssp D N"} is realised by a concrete
  top-level run, and that run satisfies full single-source shortest-path
  correctness.  The hypothesis is exactly the one already used throughout the
  top-level development: at least one valid run exists for the given size.
\<close>

theorem T_bmssp_realised_by_verified_run:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
    and run_exists: "exact_concrete_top_level_cost D N c"
  shows "\<exists>d' U.
      exact_concrete_top_level_run D N d' U (T_bmssp D N) \<and>
      U = V \<and> sssp_correct d'"
proof -
  have cost_T:
    "exact_concrete_top_level_cost D N (exact_concrete_top_level_time D N)"
    by (rule exact_concrete_top_level_time_witness[OF run_exists])
  then obtain d' U where run:
    "exact_concrete_top_level_run D N d' U (exact_concrete_top_level_time D N)"
    unfolding exact_concrete_top_level_cost_def by blast
  have correct:
    "U = V \<and> sssp_correct d' \<and>
      exact_concrete_top_level_time D N \<le> bmssp_refined_graph_time_bound
        (\<lambda>_. Suc D * sssp_log_one_third_param N)
        (\<lambda>_. sssp_log_two_thirds_param N)
        (\<lambda>_. sssp_log_one_third_param N)
        (\<lambda>_. sssp_log_one_third_param N)
        (\<lambda>_. sssp_log_two_thirds_param N)
        (\<lambda>_. edge_count) vertex_count"
    by (rule exact_concrete_top_level_run_correct_and_refined_bound_log_params_fixed_degree
      [OF all_reachable degree run])
  show ?thesis
    using run correct unfolding T_bmssp_def by blast
qed

text \<open>
  The realising run exists for all but finitely many sizes: the same
  eventual-existence fact that powers the asymptotic proof
  (@{thm [source] eventually_exact_concrete_top_level_cost_from_empty_top_pivots})
  guarantees a valid run, hence a verified realising run, eventually in
  @{term N}.
\<close>

theorem eventually_T_bmssp_realised_by_verified_run:
  assumes all_reachable: "\<And>v. v \<in> V \<Longrightarrow> reachable s v"
    and degree: "edge_outdegree_le D"
  shows "eventually
    (\<lambda>N. \<exists>d' U.
        exact_concrete_top_level_run D N d' U (T_bmssp D N) \<and>
        U = V \<and> sssp_correct d') at_top"
proof -
  have runs:
    "eventually (\<lambda>N. \<exists>c. exact_concrete_top_level_cost D N c) at_top"
    by (rule eventually_exact_concrete_top_level_cost_from_empty_top_pivots)
  show ?thesis
  proof (rule eventually_mono[OF runs])
    fix N
    assume "\<exists>c. exact_concrete_top_level_cost D N c"
    then obtain c where c: "exact_concrete_top_level_cost D N c" by blast
    show "\<exists>d' U.
        exact_concrete_top_level_run D N d' U (T_bmssp D N) \<and>
        U = V \<and> sssp_correct d'"
      by (rule T_bmssp_realised_by_verified_run[OF all_reachable degree c])
  qed
qed

end

text \<open>
  The public headline of this theory lives in the same asymptotic locale as
  \<open>bmssp_runtime_headline_instance.bmssp_runtime_bigo_target\<close>.
  It states the deterministic BMSSP running-time bound together with the
  witness that the running time belongs to runs returning exact shortest-path
  distances: for all but finitely many sizes the checked running time
  \<open>T_bmssp N\<close> is the cost of a concrete run whose output is
  \<open>sssp_correct\<close> and whose completed set is the whole vertex set.
\<close>

context bmssp_runtime_headline_instance
begin

theorem verified_bmssp_runtime_bigo_target:
  shows "(\<lambda>n. real (T_bmssp n)) \<in>
      O(\<lambda>n. real (m n) * (ln (real n + 2)) powr (2 / 3)) \<and>
    eventually
      (\<lambda>N. \<exists>d' U.
          bounded.exact_concrete_top_level_run D N d' U (T_bmssp N) \<and>
          U = V \<and> bounded.sssp_correct d') at_top"
proof
  show "(\<lambda>n. real (T_bmssp n)) \<in>
      O(\<lambda>n. real (m n) * (ln (real n + 2)) powr (2 / 3))"
    by (rule bmssp_runtime_bigo_target)
next
  have "eventually
      (\<lambda>N. \<exists>d' U.
          bounded.exact_concrete_top_level_run D N d' U
            (bounded.T_bmssp D N) \<and>
          U = V \<and> bounded.sssp_correct d') at_top"
    by (rule bounded.eventually_T_bmssp_realised_by_verified_run
      [OF bounded.all_vertices_reachable bounded.bounded_edge_outdegree])
  then show "eventually
      (\<lambda>N. \<exists>d' U.
          bounded.exact_concrete_top_level_run D N d' U (T_bmssp N) \<and>
          U = V \<and> bounded.sssp_correct d') at_top"
    unfolding T_bmssp_def .
qed

text \<open>
  Read together, the two conjuncts of
  @{thm [source] verified_bmssp_runtime_bigo_target} say that the
  @{term "O(\<lambda>n. real (m n) * (ln (real n + 2)) powr (2/3))"} running-time
  bound is not a statement about an abstract least cost in isolation: the cost
  it bounds is, for all but finitely many sizes, achieved by an explicit BMSSP
  run that provably computes the exact single-source shortest-path distance
  function on every reachable vertex.  This is the sense in which the entry
  delivers a single algorithm that is at once correct and within the
  deterministic sorting-barrier running time.
\<close>

end

end
