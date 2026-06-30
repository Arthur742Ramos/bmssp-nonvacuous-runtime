theory BMSSP_Cost_Totality
  imports BMSSP_Path_Family
begin

section \<open>On the Totality of the Exact-Concrete Cost Relation\<close>

text \<open>
  This theory records a precise, machine-checked structural fact about the
  exact-concrete cost relation @{const unique_shortest_digraph.exact_concrete_bmssp}
  and its companion loop relation
  @{const unique_shortest_digraph.exact_concrete_partition_loop_state}.

  The intended goal was to discharge the run-existence hypothesis
  \<open>runs_exist\<close> of @{thm [source] bmssp_path_family_runtime_bigo_size}
  unconditionally, by constructing a terminating partition-loop witness for the
  path family.  The construction reduces, via
  @{thm [source]
    unique_shortest_digraph.exact_concrete_bmssp_Suc_exists_from_finite_initial_loop_cases},
  to building a partition-loop state whose loop iterates over the successive
  half-open distance ranges of the pivot tree.

  The lemmas below show why that loop cannot iterate more than once under a sound
  label.  The single inductive rule
  @{const unique_shortest_digraph.exact_concrete_partition_loop_state}
  uses for a genuine step (Exact-Concrete-State-Step) carries the hypothesis
  that the recursive child output equals the incremental range tree
  @{term "range_tree P a (Fin b)"}.  But child correctness, available whenever
  the carried label is sound, pins that same child output to the cumulative
  bounded tree @{term "bound_tree P (Fin b)"}.  Since
  @{term "range_tree P a (Fin b)"} is by definition the set difference
  @{term "bound_tree P (Fin b) - bound_tree P (Fin a)"}, the two can agree only
  when the lower prefix @{term "bound_tree P (Fin a)"} is empty.  For a
  reachable singleton source rooted at @{term s} this prefix is empty exactly
  when the lower bound is zero, because the source itself has distance zero and
  therefore lies in every prefix with a strictly positive bound.

  The consequence is that a sound exact-concrete partition loop admits a genuine
  step only at lower bound zero; any second genuine step, which would necessarily
  occur at a strictly positive lower bound, is impossible.  A complete top-level
  run, whose returned bound is @{term Infinity}, requires the loop to terminate
  in the Done case with an emptied partition; with non-empty pivots that demands
  the single permitted step to leave no residual frontier, i.e. its one child
  must already solve the entire bounded tree.  These observations isolate the
  obstruction to the unconditional totality result precisely in the shape of the
  State-Step rule.

  \<^bold>\<open>Consequence for the path family.\<close>  On the unit-weight directed path
  \<open>P\<^sub>k\<close> the top-level schedule parameter \<open>p = sssp_log_one_third_param k\<close>
  grows only like \<open>\<lceil>(ln k)\<^bsup>1/3\<^esup>\<rceil>\<close>, so \<open>p < k + 1 =\<close> the vertex count for
  every \<open>k \<ge> 1\<close>; the empty-pivot existence route (which would need
  \<open>vertex_count < p\<close>) therefore never applies, the top pivot set is non-empty,
  and the loop is forced into a genuine step.  By the rigidity above that step
  sits at lower bound \<open>0\<close>, and its single child --- bottoming out at the
  truncating base case \<open>base_case_vertices\<close>, which keeps at most the \<open>k\<close>
  closest vertices --- settles only an initial prefix of the path, stranding
  the remaining vertices in a tail loop that has no applicable rule.  Hence
  \<^emph>\<open>no complete top-level run exists on \<open>P\<^sub>k\<close> for \<open>k \<ge> 2\<close>\<close>.

  In particular the hypothesis \<open>runs_exist\<close> of \<open>bmssp_path_family_runtime_bigo_size\<close>
  is \<^emph>\<open>unsatisfiable\<close> for the path family at every \<open>k \<ge> 2\<close>.  That theorem
  remains a valid conditional statement, but as a claim about an actual BMSSP
  run on \<open>P\<^sub>k\<close> it is vacuous: the algorithm-level size-parametric running-time
  bound is not witnessed by any run of the present exact-concrete relation.  The
  \<^emph>\<open>unconditional\<close> floor \<open>path_size_cost_bigo_size\<close>, which bounds the closed
  cost \<^emph>\<open>expression\<close> with the graph cardinalities substituted, is unaffected and
  remains genuinely true.  Closing the gap would require relaxing the
  State-Step rule to mirror the (more permissive) operational loop
  \<open>operational_partition_loop\<close>, which leaves the child output free rather than
  equating it with the incremental range tree; that changes the cost relation on
  which the entire runtime development depends, and is a design decision recorded
  here rather than undertaken.
\<close>

context unique_shortest_digraph
begin

text \<open>
  Step rigidity.  In a sound exact-concrete loop step the recursive child output
  is the cumulative bounded tree, so equating it with the incremental range tree
  forces the lower prefix tree to be empty.
\<close>

lemma exact_concrete_step_forces_empty_prefix:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d P (Fin Bmax)"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and pull_split: "S_pull = split_below d P beta"
    and beta_bound: "bound_le (Fin beta) (Fin Bmax)"
    and child_pre: "bmssp_pre_full d S_pull (Fin beta)"
    and a_le_b: "a \<le> b"
    and child:
      "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child c_child"
    and U_child_eq: "U_child = range_tree P a (Fin b)"
  shows "bound_tree P (Fin a) = {}"
proof -
  have S_pull_reaches: "\<And>x. x \<in> S_pull \<Longrightarrow> reachable s x"
    using pull_split P_reaches unfolding split_below_def by blast
  have child_post:
    "bmssp_post_full d S_pull (Fin beta) d_child (Fin b) U_child"
    by (rule exact_concrete_bmssp_correct[OF child sound child_pre S_pull_reaches])
  have pre_beta: "bmssp_pre_full d P (Fin beta)"
    using bmssp_pre_full_bound_mono[OF pre beta_bound] .
  have cover_beta: "complete_tree_cover d P (Fin beta)"
    using bmssp_pre_full_complete_tree_cover[OF pre_beta] .
  have child_post_split:
    "bmssp_post_full d (split_below d P beta) (Fin beta) d_child (Fin b) U_child"
    using child_post pull_split by simp
  have U_child_tree: "U_child = bound_tree P (Fin b)"
    using pull_recursive_post_lifts_bound_tree[OF cover_beta child_post_split] .
  have eq: "range_tree P a (Fin b) = bound_tree P (Fin b)"
    using U_child_eq U_child_tree by simp
  have sub: "bound_tree P (Fin a) \<subseteq> bound_tree P (Fin b)"
    using a_le_b by (intro bound_tree_bound_mono) simp
  show ?thesis
    using eq sub unfolding range_tree_eq_bound_diff by blast
qed

end

text \<open>
  Two locale-free interface facts about @{const pull_separates}.  The first is
  cap monotonicity: weakening the pull capacity preserves a pull.  The second is
  the existence of a singleton pull at any capacity \<open>M \<ge> 1\<close>, given a key whose
  value strictly dominates every other key's value.  The residual queue in the
  existential is annotated @{typ "'k partition_view"} so that the record
  extension slot is fixed to @{typ unit}; without the annotation the concrete
  record witness fails to unify with the fresh extension type variable that the
  bare existential introduces.
\<close>

lemma pull_separates_mono_cap:
  assumes "pull_separates D M B S x D'" and "M \<le> M'"
  shows "pull_separates D M' B S x D'"
  using assms unfolding pull_separates_def by (meson le_trans)

lemma pull_separates_singleton_exists_abstract:
  assumes fin: "finite (keys_of D)"
    and u: "u \<in> keys_of D"
    and umin: "\<And>v. v \<in> keys_of D \<Longrightarrow> v \<noteq> u \<Longrightarrow> value_of D u < value_of D v"
    and M1: "1 \<le> M"
    and upper: "value_of D u < B"
  shows "\<exists>beta (D'::'k partition_view).
           pull_separates (D::'k partition_view) M B {u} beta D'"
proof -
  have le_rem: "\<And>v. v \<in> keys_of D - {u} \<Longrightarrow> value_of D u \<le> value_of D v"
    using umin by (auto intro: less_imp_le)
  show ?thesis
  proof (cases "keys_of D - {u} = {}")
    case True
    have "pull_separates D M B {u} B
            \<lparr> keys_of = keys_of D - {u}, value_of = value_of D \<rparr>"
      unfolding pull_separates_def using u M1 True le_rem by simp
    thus ?thesis by blast
  next
    case False
    let ?A = "value_of D ` (keys_of D - {u})"
    have finA: "finite ?A" using fin by simp
    have neA: "?A \<noteq> {}" using False by simp
    have lo: "\<And>v. v \<in> keys_of D - {u} \<Longrightarrow> Min ?A \<le> value_of D v"
      using finA by (auto intro: Min_le)
    have hi: "value_of D u < Min ?A"
      using finA neA umin by (auto simp: Min_gr_iff)
    have "pull_separates D M B {u} (Min ?A)
            \<lparr> keys_of = keys_of D - {u}, value_of = value_of D \<rparr>"
      unfolding pull_separates_def using u M1 le_rem lo hi False by simp
    thus ?thesis by blast
  qed
qed

context strict_tie_breaking_digraph
begin

text \<open>
  Source persistence.  The source lies in every prefix tree with a strictly
  positive bound, because its true distance is zero.
\<close>

lemma source_in_positive_prefix:
  assumes a_pos: "0 < a"
  shows "s \<in> bound_tree {s} (Fin a)"
proof -
  have reach: "reachable s s"
    by (rule reachable_refl[OF source_in_V])
  have dist0: "dist s s = 0"
    by (rule dist_refl_zero[OF source_in_V])
  have below: "below_bound (dist s s) (Fin a)"
    using dist0 a_pos by simp
  show ?thesis
    by (rule source_in_own_bound_tree[OF _ reach below]) simp
qed

text \<open>
  The obstruction, combining step rigidity with source persistence.  For the
  singleton source a genuine exact-concrete loop step is impossible at any
  strictly positive lower bound.  Equivalently every genuine step must occur at
  lower bound zero, so a sound loop performs at most one genuine step.
\<close>

lemma no_genuine_exact_concrete_step_at_positive_lower_bound:
  assumes sound: "sound_label d"
    and pre: "bmssp_pre_full d {s} (Fin Bmax)"
    and pull_split: "S_pull = split_below d {s} beta"
    and beta_bound: "bound_le (Fin beta) (Fin Bmax)"
    and child_pre: "bmssp_pre_full d S_pull (Fin beta)"
    and a_pos: "0 < a"
    and a_le_b: "a \<le> b"
    and child:
      "exact_concrete_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child c_child"
    and U_child_eq: "U_child = range_tree {s} a (Fin b)"
  shows "False"
proof -
  have P_reaches: "\<And>x. x \<in> {s} \<Longrightarrow> reachable s x"
    using reachable_refl[OF source_in_V] by simp
  have empty: "bound_tree {s} (Fin a) = {}"
    by (rule exact_concrete_step_forces_empty_prefix
      [OF sound pre P_reaches pull_split beta_bound child_pre a_le_b child
        U_child_eq])
  have "s \<in> bound_tree {s} (Fin a)"
    by (rule source_in_positive_prefix[OF a_pos])
  then show False
    using empty by simp
qed

text \<open>
  \<^bold>\<open>The relaxed (charged) model: isolating the remaining obligation.\<close>
  The rigidity analysis above explains why the \<^emph>\<open>exact-concrete\<close> relation
  admits no genuine step at a positive lower bound, and hence why its
  size-parametric running-time bound is vacuous on the path family.  The
  permissive @{const charged_direct_insert_costed_bmssp} relation removes that
  rigidity --- its State-Step rule (rule \<open>Charged_Direct_Insert_Step\<close>) leaves
  the child output @{term U_child} free and only records the incremental range
  tree @{term "range_tree P a (Fin b)"} as the cost-accounting slice
  @{term charged_child}.  Runs therefore exist; the open question is whether the
  charged per-level \<^emph>\<open>cost\<close> bound goes through.

  That bound is gated on a single arithmetic obligation, the charged
  \<open>source_progress\<close>: for each loop child the pulled source set must be dominated
  in cardinality by its range-tree slice,
  @{term "card (split_below d P beta) \<le> card (range_tree P a (Fin b))"}.
  Summed along the loop via
  @{thm [source] sum_card_dominated_by_range_tree_child_list_le_chain} this is
  exactly what bounds the cumulative pull cost by the chain cardinality, i.e.
  linearly in the vertex count.

  The direct-insert development discharges this for free only because its rigid
  rule equates the child output with the slice; by the same rigidity that route
  is vacuous (the lemmas above).  In the charged model the child output is the
  cumulative @{term "bound_tree P (Fin b)"} (no lower bound), so the slice bound
  is genuine new information.  The lemmas below reduce it to a single named
  side-condition --- \<^emph>\<open>pivot settledness\<close>: the pulled sources avoid the
  already-settled prefix @{term "bound_tree P (Fin a)"} below the step's lower
  bound @{term a}.  Geometrically: a pivot pulled at the band starting at
  @{term a} has true distance at least @{term a}.

  This side-condition is \<^emph>\<open>not\<close> derivable from the local State-Step hypotheses
  (\<open>complete_on d'\<close> constrains the output label @{term d'}, not the input label
  @{term d} that selects the pulled sources; a settled pivot below @{term a}
  carrying a small input label could be pulled).  Establishing it requires a
  frontier/monotonicity invariant threaded top-down through the charged
  inductive relation --- the same band-monotonicity that underlies the
  correctness proof, but re-expressed on the separate cost relation.  That is
  the design step the introduction to this theory records as not undertaken.
  The reduction below makes the obligation precise, single, and reusable: once
  pivot settledness is available as a loop invariant, the charged top-level
  bound becomes unconditional by mirroring the direct-insert chain.
\<close>

lemma split_below_card_le_range_tree_if_settled:
  assumes within: "split_below d P beta \<subseteq> bound_tree P (Fin b)"
    and settled: "split_below d P beta \<inter> bound_tree P (Fin a) = {}"
  shows "card (split_below d P beta) \<le> card (range_tree P a (Fin b))"
proof -
  have "split_below d P beta \<subseteq> bound_tree P (Fin b) - bound_tree P (Fin a)"
    using within settled by blast
  also have "\<dots> = range_tree P a (Fin b)"
    by (simp add: range_tree_eq_bound_diff)
  finally show ?thesis
    by (rule card_mono[OF finite_range_tree])
qed

text \<open>
  The within-bound inclusion is the standard source-subset fact: pivots whose
  input label is correct and below the returned bound @{term b} lie in the
  child's bounded tree, hence (by monotonicity of @{const bound_tree} in the
  source set) in @{term "bound_tree P (Fin b)"}.
\<close>

lemma split_below_within_bound_tree_if_complete_label_below:
  assumes complete: "complete_on d (split_below d P beta)"
    and reaches: "\<And>x. x \<in> split_below d P beta \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> split_below d P beta \<Longrightarrow> d x < b"
  shows "split_below d P beta \<subseteq> bound_tree P (Fin b)"
proof -
  have "split_below d P beta \<subseteq> bound_tree (split_below d P beta) (Fin b)"
  proof (rule sources_subset_bound_tree_if_label_below[OF complete reaches])
    fix x assume "x \<in> split_below d P beta"
    then show "below_bound (d x) (Fin b)" using below by simp
  qed
  also have "\<dots> \<subseteq> bound_tree P (Fin b)"
    by (rule bound_tree_mono[OF split_below_subset])
  finally show ?thesis .
qed

text \<open>
  The tight reduction.  The charged per-child source-card domination follows
  from the standard pivot-completeness and label bound (both available in the
  direct-insert template) together with the single genuinely-new pivot
  settledness side-condition.  This is the charged counterpart of the direct
  \<open>source_card_le\<close> step and feeds the existing chain summation.
\<close>

lemma split_below_card_le_range_tree_if_complete_and_settled:
  assumes complete: "complete_on d (split_below d P beta)"
    and reaches: "\<And>x. x \<in> split_below d P beta \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> split_below d P beta \<Longrightarrow> d x < b"
    and settled: "split_below d P beta \<inter> bound_tree P (Fin a) = {}"
  shows "card (split_below d P beta) \<le> card (range_tree P a (Fin b))"
  by (rule split_below_card_le_range_tree_if_settled
        [OF split_below_within_bound_tree_if_complete_label_below
            [OF complete reaches below] settled])

text \<open>
  \<^bold>\<open>Reducing the settledness side-condition to threaded invariants.\<close>
  The lemmas above take pivot settledness
  @{term "split_below d P beta \<inter> bound_tree P (Fin a) = {}"} as a hypothesis.
  The authors' note (above) flags that settledness is \<^emph>\<open>not\<close> derivable from the
  local State-Step hypotheses alone: it needs a frontier/monotonicity invariant
  threaded top-down through the recursion.  The next three lemmas isolate
  \<^emph>\<open>exactly\<close> that obligation by reducing settledness to two recognizable,
  modular invariants of the input label @{term d} at a loop step:
  \<^item> \<^bold>\<open>label-floor\<close> @{term "\<forall>x\<in>P. a \<le> d x"} --- the current pivot labels lie at
    or above the step's lower band @{term a} (the structural fact that earlier
    bands have already consumed the sources below @{term a}), and
  \<^item> \<^bold>\<open>prefix-exactness\<close> @{term "\<forall>v\<in>tree_set P. dist s v < a \<longrightarrow> d v = dist s v"}
    --- @{term d} is exact on the settled tree-set prefix below @{term a} (the
    band-monotonicity invariant the descending recursion maintains).
  Under those two, a pulled pivot with @{term "dist s x < a"} would have
  exact label @{term "d x = dist s x"} and hence @{term "d x < a"},
  contradicting the label floor; so the pull is
  settled.  This turns the opaque settledness side-condition into the single
  precise invariant a top-down threading must establish, and feeds the existing
  card / chain machinery unchanged.
\<close>

lemma split_below_inter_bound_tree_empty_if_label_ge_exact:
  assumes ge: "\<And>x. x \<in> P \<Longrightarrow> a \<le> d x"
    and exact: "\<And>v. v \<in> tree_set P \<Longrightarrow> dist s v < a \<Longrightarrow> d v = dist s v"
  shows "split_below d P beta \<inter> bound_tree P (Fin a) = {}"
  using ge exact by (force simp: split_below_def bound_tree_eq_tree_set)

lemma split_below_card_le_range_tree_if_complete_label_ge_exact:
  assumes complete: "complete_on d (split_below d P beta)"
    and reaches: "\<And>x. x \<in> split_below d P beta \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> split_below d P beta \<Longrightarrow> d x < b"
    and ge: "\<And>x. x \<in> P \<Longrightarrow> a \<le> d x"
    and exact: "\<And>v. v \<in> tree_set P \<Longrightarrow> dist s v < a \<Longrightarrow> d v = dist s v"
  shows "card (split_below d P beta) \<le> card (range_tree P a (Fin b))"
  by (rule split_below_card_le_range_tree_if_complete_and_settled
        [OF complete reaches below
          split_below_inter_bound_tree_empty_if_label_ge_exact[OF ge exact]])

lemma split_below_subset_range_tree_if_complete_label_ge_exact:
  assumes complete: "complete_on d (split_below d P beta)"
    and reaches: "\<And>x. x \<in> split_below d P beta \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> split_below d P beta \<Longrightarrow> d x < b"
    and ge: "\<And>x. x \<in> P \<Longrightarrow> a \<le> d x"
    and exact: "\<And>v. v \<in> tree_set P \<Longrightarrow> dist s v < a \<Longrightarrow> d v = dist s v"
  shows "split_below d P beta \<subseteq> range_tree P a (Fin b)"
proof -
  have within: "split_below d P beta \<subseteq> bound_tree P (Fin b)"
    by (rule split_below_within_bound_tree_if_complete_label_below[OF complete reaches below])
  have settled: "split_below d P beta \<inter> bound_tree P (Fin a) = {}"
    by (rule split_below_inter_bound_tree_empty_if_label_ge_exact[OF ge exact])
  have "split_below d P beta \<subseteq> bound_tree P (Fin b) - bound_tree P (Fin a)"
    using within settled by blast
  also have "\<dots> = range_tree P a (Fin b)"
    by (simp add: range_tree_eq_bound_diff)
  finally show ?thesis .
qed

text \<open>
  \<^bold>\<open>Strong base case of the charged totality induction.\<close>
  At level @{term "0::nat"} the charged relation can fire only through the
  \<open>Charged_Direct_Insert_Base\<close> rule, which is restricted to singleton source
  sets.  For such a singleton we exhibit the complete base-case witness: a
  charged run exists, the returned bound does not exceed the input bound, the
  output set is exactly the bounded tree of the returned bound, and the returned
  label is complete on that output.  This is the leaf in which the level
  induction for charged-run existence (obligation \<^emph>\<open>O1\<close> of the path-family
  bridge) bottoms out.  The completeness certificate is read straight off
  \<open>base_case_result_correct\<close>; note we reduce that fact with
  \<open>base_case_result_def\<close> and \<open>prod.case\<close> \<^emph>\<open>only\<close> -- a full simplification would
  orient the \<open>U = bound_tree S B'\<close> conjunct into a rewrite rule and corrupt the
  label witness, which itself mentions @{term base_case_vertices}.
\<close>

lemma charged_bmssp_zero_total:
  assumes "S = {x}"
  shows "\<exists>d' B' U c.
    charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c \<and>
    bound_le B' B \<and>
    U = bound_tree S B' \<and>
    complete_on d' U"
proof -
  let ?d' = "\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v"
  let ?B' = "base_case_bound k x B"
  let ?U = "base_case_vertices k x B"
  have run: "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B ?d' ?B' ?U
      (base_case_scan_cost \<Delta> k x B)"
    by (rule Charged_Direct_Insert_Base[OF assms])
  have corr: "?U = bound_tree S ?B' \<and> complete_on ?d' ?U"
    using base_case_result_correct[OF assms, where k=k and B=B and d=d]
    unfolding base_case_result_def prod.case .
  have le: "bound_le ?B' B" by (rule base_case_bound_le)
  show ?thesis using run le corr by blast
qed

text \<open>
  \<^bold>\<open>Full coverage at the leaf.\<close>  When the bounded tree of the input bound has
  at most @{term k} vertices the truncating base case keeps \<^emph>\<open>all\<close> of them, so
  the level-@{term "0::nat"} charged run returns the input bound itself
  (@{term "B' = B"}) and its output set is the entire bounded tree
  @{term "bound_tree S B"}.  This is the sharpened leaf used by the coverage
  half of the level induction: a small enough source band is completely solved
  in one base call without losing the residual frontier.
\<close>

lemma charged_bmssp_zero_full_cover:
  assumes S: "S = {x}"
    and small: "card (bound_tree S B) \<le> k"
  shows "\<exists>d' U c.
    charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B U c \<and>
    U = bound_tree S B \<and> complete_on d' U"
proof -
  have order_len: "length (base_case_order x B) = card (bound_tree {x} B)"
  proof -
    have "distinct (base_case_order x B)"
      by (rule base_case_order_distinct)
    moreover have "set (base_case_order x B) = bound_tree {x} B"
      by (rule base_case_order_set)
    ultimately show ?thesis
      by (metis distinct_card)
  qed
  have len: "length (base_case_order x B) \<le> k"
    using small order_len S by simp
  have U: "base_case_vertices k x B = bound_tree {x} B"
    by (rule base_case_success[OF len])
  have B': "base_case_bound k x B = B"
    using len unfolding base_case_bound_def by (simp add: Let_def)
  let ?d' = "\<lambda>v. if v \<in> base_case_vertices k x B then dist s v else d v"
  have run:
    "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B
      ?d' (base_case_bound k x B) (base_case_vertices k x B)
      (base_case_scan_cost \<Delta> k x B)"
    by (rule Charged_Direct_Insert_Base[OF S])
  have complete: "complete_on ?d' (base_case_vertices k x B)"
    unfolding complete_on_def by simp
  have run2:
    "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B
      ?d' B (bound_tree S B) (base_case_scan_cost \<Delta> k x B)"
    using run by (simp add: B' U S)
  have complete2: "complete_on ?d' (bound_tree S B)"
    using complete by (simp add: U S)
  show ?thesis
    using run2 complete2 by blast
qed

text \<open>
  \<^bold>\<open>The output-label collapse \<open>d' = dist s\<close>.\<close>  Fixing the run's output label to
  the true distance @{term "dist s"} trivialises every completeness obligation
  in the charged relation: @{thm complete_on_dist} gives
  @{term "complete_on (dist s) U"} for all @{term U}, and the next fact gives
  @{term "complete_preserved d (dist s) U"} for all @{term d}, @{term U}.  Since
  @{const charged_direct_insert_top_level_cost} existentially quantifies the
  output label, choosing @{term "dist s"} is legitimate (the empty-pivot witness
  already does so), and it removes the band-monotonicity exactness invariant from
  the run-existence problem entirely, leaving a purely structural induction.
\<close>

lemma complete_preserved_dist: "complete_preserved d (dist s) U"
  unfolding complete_preserved_def using complete_on_dist by blast

text \<open>
  The @{term "d' = dist s"} specialisation of the band-loop driver
  @{thm [source] charged_direct_insert_partition_loop_state_cases_exists_with_complete}:
  with the output label pinned to @{term "dist s"} every \<open>complete_on\<close> and
  \<open>complete_preserved\<close> side-condition is discharged automatically, so a loop state
  exists as soon as the current band admits a Done, Stop, or Step case (the Step
  case still carrying a child run and a recursive tail loop state).
\<close>

lemma charged_loop_state_exists_dist:
  fixes a Bmax :: real
  assumes cases:
    "(keys_of D = {} \<and> bound_le (Fin a) B) \<or>
     (bound_le (Fin a) B \<and> k * cap \<le> card (bound_tree P (Fin a))) \<or>
     (\<exists>S_pull beta D_pull B'.
       pull_separates D (M_of l) Bmax S_pull beta D_pull \<and>
       bound_le (Fin beta) B \<and>
       bmssp_pre_full d S_pull (Fin beta) \<and>
       S_pull = split_below d P beta \<and>
       (\<forall>x\<in>S_pull. reachable s x) \<and>
       card (bound_tree P (Fin a)) < k * cap \<and>
       (\<exists>d_child b U_child c_child betas bs charged_tail
           child_outputs_tail U_tail c_tail child_costs_tail.
         a \<le> b \<and>
         bound_le (Fin a) B' \<and>
         charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d
           S_pull (Fin beta) d_child (Fin b) U_child c_child \<and>
         charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
           d P B (dist s)
           (batch_min_update D_pull
             (edge_relaxation_pairs_in_bound d_child
                (range_tree P a (Fin b)) beta B @
              edge_relaxation_pairs_between d_child
                (range_tree P a (Fin b)) b beta @
              label_pairs_between d S_pull b beta))
           b betas bs B' charged_tail child_outputs_tail U_tail c_tail
           child_costs_tail))"
  shows "\<exists>betas bs B' charged_Us child_outputs U c child_costs.
    charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
      d P B (dist s) D a betas bs B' charged_Us child_outputs U c child_costs"
proof -
  have "\<exists>betas bs B' charged_Us child_outputs U c child_costs.
      charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l
        d P B (dist s) D a betas bs B' charged_Us child_outputs U c child_costs \<and>
      complete_on (dist s) ((\<lambda>_::bound. {}) B')"
    by (rule charged_direct_insert_partition_loop_state_cases_exists_with_complete
        [where W = "\<lambda>_::bound. {}" and d' = "dist s" and Bmax = Bmax])
      (use cases in \<open>blast intro: complete_on_dist complete_preserved_dist\<close>)
  thus ?thesis by blast
qed

text \<open>
  \<^bold>\<open>One genuine step, then Done, under @{term "d' = dist s"}.\<close>  Specialising the
  combined step/Done loop witness
  @{thm [source] charged_direct_insert_partition_loop_state_step_done_exists}
  to the true-distance output label discharges all three completeness
  side-conditions automatically (via @{thm complete_on_dist} and
  @{thm complete_preserved_dist}) and fixes the four partition-operation costs to
  zero.  What is left is purely structural: a pull of the current band, a
  recursive child run, the resulting residual partition view being empty, and the
  band/threshold bookkeeping.  The loop returned terminates at the input bound
  @{term B} -- its output bound is @{term B} itself -- so it is exactly the loop
  shape consumed by the top-level existence reduction when @{term "B = Infinity"}.
\<close>

lemma charged_loop_single_step_then_done_exists_dist:
  fixes a b beta Bmax :: real and B :: bound and D D_pull :: "'a partition_view"
  assumes pull: "pull_separates D (M_of l) Bmax S_pull beta D_pull"
    and beta_bound: "bound_le (Fin beta) B"
    and pre: "bmssp_pre_full d S_pull (Fin beta)"
    and split: "S_pull = split_below d P beta"
    and reaches: "\<forall>x\<in>S_pull. reachable s x"
    and a_le_b: "a \<le> b"
    and a_bound: "bound_le (Fin a) B"
    and small: "card (bound_tree P (Fin a)) < k * cap"
    and child:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child c_child"
    and tail_empty:
      "keys_of (batch_min_update D_pull
        (edge_relaxation_pairs_in_bound d_child (range_tree P a (Fin b)) beta B @
         edge_relaxation_pairs_between d_child (range_tree P a (Fin b)) b beta @
         label_pairs_between d S_pull b beta)) = {}"
    and b_bound: "bound_le (Fin b) B"
  shows "\<exists>betas bs charged_Us child_outputs U c child_costs.
    charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B
      (dist s) D a betas bs B charged_Us child_outputs U c child_costs"
proof -
  let ?cc = "range_tree P a (Fin b)"
  let ?direct = "edge_relaxation_pairs_in_bound d_child ?cc beta B"
  let ?lower = "edge_relaxation_pairs_between d_child ?cc b beta"
  let ?sources = "label_pairs_between d S_pull b beta"
  let ?batch = "?direct @ ?lower @ ?sources"
  let ?D_next = "batch_min_update D_pull ?batch"
  have tail:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B
      (dist s) ?D_next b [] [] B [range_tree P b B] []
      (bound_tree P (Fin b) \<union> \<Union>(set [range_tree P b B])) 0 []"
    by (rule Charged_Direct_Insert_State_Done)
       (use tail_empty b_bound in \<open>auto intro: complete_on_dist\<close>)
  have run:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B
      (dist s) D a [beta] [b] B (?cc # [range_tree P b B]) [U_child]
      (bound_tree P (Fin a) \<union> \<Union>(set (?cc # [range_tree P b B])))
      (0 + 0 + 0 + 0 + c_child + 0) [c_child]"
    by (rule Charged_Direct_Insert_State_Step
        [where Bmax = Bmax and S_pull = S_pull and D_pull = D_pull
          and charged_child = ?cc and direct_edge_batch = ?direct
          and lower_edge_batch = ?lower and source_batch = ?sources
          and batch = ?batch and D_next = ?D_next
          and c_pull = 0 and c_direct = 0 and c_lower = 0 and c_sources = 0
          and c_tail = 0])
       (use pull beta_bound pre split reaches a_le_b a_bound small child tail in
         \<open>auto intro: complete_on_dist complete_preserved_dist
           simp: partition_pull_cost_bound_def partition_batch_cost_bound_def\<close>)
  then show ?thesis by blast
qed

text \<open>
  \<^bold>\<open>Cost-exposing form of the single-step-then-Done loop.\<close>  Identical to
  @{thm [source] charged_loop_single_step_then_done_exists_dist} but returning the
  concrete loop state with its cost read off as the lone child cost
  @{term c_child} (all four partition costs and the empty Done tail are zero).
  This is the brick the cheap charged top-level run on the path family threads
  level by level, so that the whole run cost telescopes to a sum of the FindPivots
  scans plus the single base-case scan, with no edge-range or chain terms.
\<close>

lemma charged_loop_single_step_then_done_costed_dist:
  fixes a b beta Bmax :: real and B :: bound and D D_pull :: "'a partition_view"
  assumes pull: "pull_separates D (M_of l) Bmax S_pull beta D_pull"
    and beta_bound: "bound_le (Fin beta) B"
    and pre: "bmssp_pre_full d S_pull (Fin beta)"
    and split: "S_pull = split_below d P beta"
    and reaches: "\<forall>x\<in>S_pull. reachable s x"
    and a_le_b: "a \<le> b"
    and a_bound: "bound_le (Fin a) B"
    and small: "card (bound_tree P (Fin a)) < k * cap"
    and child:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child c_child"
    and tail_empty:
      "keys_of (batch_min_update D_pull
        (edge_relaxation_pairs_in_bound d_child (range_tree P a (Fin b)) beta B @
         edge_relaxation_pairs_between d_child (range_tree P a (Fin b)) b beta @
         label_pairs_between d S_pull b beta)) = {}"
    and b_bound: "bound_le (Fin b) B"
  shows "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B
      (dist s) D a [beta] [b] B
      (range_tree P a (Fin b) # [range_tree P b B]) [U_child]
      (bound_tree P (Fin a) \<union> \<Union>(set (range_tree P a (Fin b) # [range_tree P b B])))
      c_child [c_child]"
proof -
  let ?cc = "range_tree P a (Fin b)"
  let ?direct = "edge_relaxation_pairs_in_bound d_child ?cc beta B"
  let ?lower = "edge_relaxation_pairs_between d_child ?cc b beta"
  let ?sources = "label_pairs_between d S_pull b beta"
  let ?batch = "?direct @ ?lower @ ?sources"
  let ?D_next = "batch_min_update D_pull ?batch"
  have tail:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B
      (dist s) ?D_next b [] [] B [range_tree P b B] []
      (bound_tree P (Fin b) \<union> \<Union>(set [range_tree P b B])) 0 []"
    by (rule Charged_Direct_Insert_State_Done)
       (use tail_empty b_bound in \<open>auto intro: complete_on_dist\<close>)
  show ?thesis
    by (rule Charged_Direct_Insert_State_Step
        [where Bmax = Bmax and S_pull = S_pull and D_pull = D_pull
          and charged_child = ?cc and direct_edge_batch = ?direct
          and lower_edge_batch = ?lower and source_batch = ?sources
          and batch = ?batch and D_next = ?D_next
          and c_pull = 0 and c_direct = 0 and c_lower = 0 and c_sources = 0
          and c_tail = 0])
       (use pull beta_bound pre split reaches a_le_b a_bound small child tail in
         \<open>auto intro: complete_on_dist complete_preserved_dist
           simp: partition_pull_cost_bound_def partition_batch_cost_bound_def\<close>)
qed

text \<open>
  \<^bold>\<open>One genuine step, then an arbitrary tail, under @{term "d' = dist s"}.\<close>  This
  is the multi-step companion of @{thm [source] charged_loop_single_step_then_done_exists_dist}:
  rather than forcing the residual partition to be empty (Done) it consumes a
  ready-made loop state for the band \<open>[b, B')\<close> and stacks one more
  @{term Charged_Direct_Insert_State_Step} on top, pulling the band \<open>[a, b)\<close>
  with a recursive child run.  All three completeness obligations and the four
  partition costs collapse via @{thm complete_on_dist} / @{thm complete_preserved_dist}.
  Iterating this brick is how the path band is covered step by step: each step
  fans out one level-@{term l} child of at most @{term "k * cap"} vertices, so a
  whole-path cover follows by chaining the cons over the frontier.
\<close>

lemma charged_loop_step_cons_exists_dist:
  fixes a b beta Bmax :: real and B B' :: bound and D D_pull :: "'a partition_view"
  assumes pull: "pull_separates D (M_of l) Bmax S_pull beta D_pull"
    and beta_bound: "bound_le (Fin beta) B"
    and pre: "bmssp_pre_full d S_pull (Fin beta)"
    and split: "S_pull = split_below d P beta"
    and reaches: "\<forall>x\<in>S_pull. reachable s x"
    and a_le_b: "a \<le> b"
    and a_bound: "bound_le (Fin a) B'"
    and small: "card (bound_tree P (Fin a)) < k * cap"
    and child:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_pull (Fin beta)
        d_child (Fin b) U_child c_child"
    and D_next:
      "D_next = batch_min_update D_pull
        (edge_relaxation_pairs_in_bound d_child (range_tree P a (Fin b)) beta B @
         edge_relaxation_pairs_between d_child (range_tree P a (Fin b)) b beta @
         label_pairs_between d S_pull b beta)"
    and tail:
      "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B
        (dist s) D_next b betas bs B' charged_tail child_outputs_tail U_tail c_tail
        child_costs_tail"
  shows "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B
      (dist s) D a (beta # betas) (b # bs) B'
      (range_tree P a (Fin b) # charged_tail) (U_child # child_outputs_tail)
      (bound_tree P (Fin a) \<union> \<Union>(set (range_tree P a (Fin b) # charged_tail)))
      (0 + 0 + 0 + 0 + c_child + c_tail) (c_child # child_costs_tail)"
  by (rule Charged_Direct_Insert_State_Step
      [where Bmax = Bmax and S_pull = S_pull and D_pull = D_pull
        and charged_child = "range_tree P a (Fin b)"
        and direct_edge_batch = "edge_relaxation_pairs_in_bound d_child (range_tree P a (Fin b)) beta B"
        and lower_edge_batch = "edge_relaxation_pairs_between d_child (range_tree P a (Fin b)) b beta"
        and source_batch = "label_pairs_between d S_pull b beta"
        and D_next = D_next and c_pull = 0 and c_direct = 0 and c_lower = 0
        and c_sources = 0])
    (use pull beta_bound pre split reaches a_le_b a_bound small child D_next tail in
      \<open>auto intro: complete_on_dist complete_preserved_dist
        simp: partition_pull_cost_bound_def partition_batch_cost_bound_def\<close>)

text \<open>
  \<^bold>\<open>Charged per-call progress: the success-or-threshold dichotomy.\<close>
  The next five facts are the charged-cost analogue of the direct-insert
  source-card chain.  For every charged run the number of sources is bounded
  by the cardinality of the run's \<^emph>\<open>own\<close> output @{term U}: either the bound was
  not advanced (success, @{term "B' = B"}), so the sources sit inside their own
  bounded tree, or the FindPivots cap is saturated (threshold,
  @{term "k * cap \<le> card U"}).  This is the stranding-free progress step.  It
  transfers the direct-insert dichotomy to the permissive charged relation
  \<^emph>\<open>without\<close> the rigid @{term "U_child = range_tree P a (Fin b)"} step rule, and
  is therefore non-vacuous on the path family.  Note, however, that the bound
  is against the run's \<^emph>\<open>cumulative\<close> own output, not the disjoint range slice;
  summing it over the loop children does not on its own telescope to the linear
  chain (see the loop-level companion below).
\<close>

text \<open>PIECE A: charged source-card chain (amortized, stranding-free via the
  success-or-threshold dichotomy).\<close>

theorem charged_direct_insert_costed_bmssp_source_card_le_if_sound_label_below_output:
  assumes run:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B'"
  shows "card S \<le> card U"
proof -
  have post: "bmssp_post_full d S B d' B' U"
    by (rule charged_direct_insert_costed_bmssp_correct[OF run sound pre S_reaches])
  have U_eq: "U = bound_tree S B'"
    using post unfolding bmssp_post_full_def by blast
  have S_subset_U: "S \<subseteq> U"
  proof
    fix x
    assume xS: "x \<in> S"
    have S_subset: "S \<subseteq> V"
      using pre unfolding bmssp_pre_full_def by blast
    have xV: "x \<in> V"
      using S_subset xS by blast
    have reach_x: "reachable s x"
      by (rule S_reaches[OF xS])
    have dist_le: "dist s x \<le> d x"
      using sound xV reach_x unfolding sound_label_def by blast
    have below_dist: "below_bound (dist s x) B'"
      using below_bound_le_trans[OF dist_le below[OF xS]] .
    show "x \<in> U"
      unfolding U_eq
      by (rule source_in_own_bound_tree[OF xS reach_x below_dist])
  qed
  have finite_U: "finite U"
    unfolding U_eq bound_tree_def using finite_V by auto
  show ?thesis
    by (rule card_mono[OF finite_U S_subset_U])
qed

theorem charged_direct_insert_costed_bmssp_Suc_success_or_threshold:
  assumes run:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
  shows "B' = B \<or> k * cap \<le> card U"
  using run
proof cases
  case (Charged_Direct_Insert_Step D c_insert a betas bs charged_Us
      child_outputs U_loop c_loop child_costs_loop)
  let ?d_fp = "find_pivots_label_capped k cap d S B"
  let ?P = "find_pivots_pivots_capped k cap d S B"
  let ?W = "{v \<in> bound_tree S B'. ?d_fp v = dist s v}"
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
      [OF Charged_Direct_Insert_Step(3) sound_fp pivot_pre P_reaches])
  have loop_trace:
    "concrete_partition_loop_trace ?P B a bs d' B' charged_Us U_loop"
    by (rule charged_direct_insert_costed_partition_loop_state_trace
      [OF Charged_Direct_Insert_Step(3) sound_fp pivot_pre P_reaches])
  have loop_post: "bmssp_post_full ?d_fp ?P B d' B' U_loop"
    by (rule concrete_partition_loop_trace_post[OF loop_trace])
  have finite_U_loop: "finite U_loop"
    using loop_post unfolding bmssp_post_full_def by simp
  show ?thesis
    using loop_class
  proof
    assume "B' = B"
    then show ?thesis
      by blast
  next
    assume threshold_loop: "k * cap \<le> card U_loop"
    have U_eq: "U = U_loop \<union> ?W"
      using Charged_Direct_Insert_Step(5) by simp
    have finite_U: "finite U"
      unfolding U_eq using finite_U_loop by simp
    have U_loop_subset: "U_loop \<subseteq> U"
      unfolding U_eq by blast
    have "card U_loop \<le> card U"
      by (rule card_mono[OF finite_U U_loop_subset])
    then show ?thesis
      using threshold_loop by linarith
  qed
qed

theorem charged_direct_insert_costed_bmssp_zero_source_card_le_from_label_below:
  assumes run:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
  using run
proof cases
  case (Charged_Direct_Insert_Base x)
  have S_eq: "S = {x}"
    using Charged_Direct_Insert_Base by simp
  have xS: "x \<in> S"
    using S_eq by simp
  have xV: "x \<in> V"
    using pre xS unfolding bmssp_pre_full_def by blast
  have reach_x: "reachable s x"
    by (rule S_reaches[OF xS])
  have dist_le: "dist s x \<le> d x"
    using sound xV reach_x unfolding sound_label_def by blast
  have below_dist: "below_bound (dist s x) B"
    using below_bound_le_trans[OF dist_le below[OF xS]] .
  have x_bound: "x \<in> bound_tree {x} B"
    by (rule source_in_own_bound_tree[OF _ reach_x below_dist]) simp
  have xU: "x \<in> U"
    using source_in_base_case_vertices[OF x_bound k_pos]
    using Charged_Direct_Insert_Base by simp
  have singleton_subset: "{x} \<subseteq> U"
    using xU by blast
  have finite_U: "finite U"
    using Charged_Direct_Insert_Base by simp
  have "card {x} \<le> card U"
    by (rule card_mono[OF finite_U singleton_subset])
  then show ?thesis
    using S_eq by simp
qed

theorem charged_direct_insert_costed_bmssp_Suc_source_card_le_from_label_below:
  assumes run:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l) d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_cap: "card S \<le> cap"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
proof -
  have call_class: "B' = B \<or> k * cap \<le> card U"
    by (rule charged_direct_insert_costed_bmssp_Suc_success_or_threshold
      [OF run sound pre S_reaches])
  then show ?thesis
  proof
    assume B'_eq: "B' = B"
    show ?thesis
    proof (rule charged_direct_insert_costed_bmssp_source_card_le_if_sound_label_below_output
        [OF run sound pre S_reaches])
      fix x
      assume "x \<in> S"
      then show "below_bound (d x) B'"
        using below B'_eq by simp
    qed
  next
    assume threshold: "k * cap \<le> card U"
    have "cap \<le> k * cap"
      using k_pos by (cases k) simp_all
    then show ?thesis
      using S_cap threshold by linarith
  qed
qed

theorem charged_direct_insert_costed_bmssp_source_card_le_from_label_below_all_levels:
  assumes run:
      "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S B d' B' U c"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d S B"
    and S_reaches: "\<And>x. x \<in> S \<Longrightarrow> reachable s x"
    and below: "\<And>x. x \<in> S \<Longrightarrow> below_bound (d x) B"
    and S_cap: "card S \<le> cap"
    and k_pos: "0 < k"
  shows "card S \<le> card U"
proof (cases l)
  case 0
  have run0:
    "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap 0 d S B d' B' U c"
    using run 0 by simp
  show ?thesis
    by (rule charged_direct_insert_costed_bmssp_zero_source_card_le_from_label_below
      [OF run0 sound pre S_reaches below k_pos])
next
  case (Suc l')
  have run_suc:
    "charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap (Suc l') d S B d' B' U c"
    using run Suc by simp
  show ?thesis
    by (rule charged_direct_insert_costed_bmssp_Suc_source_card_le_from_label_below
      [OF run_suc sound pre S_reaches below S_cap k_pos])
qed


text \<open>Loop-level companion: the charged partition-loop cost is bounded by the
  linear range-tree chain cardinality as soon as the pulled child sources land
  in their range slices (the transparent no-stranding/settledness invariant).\<close>

lemma list_all2_card_mono_if_finite_right:
  assumes "list_all2 (\<subseteq>) Xs Ys"
    and "\<And>Y. Y \<in> set Ys \<Longrightarrow> finite Y"
  shows "list_all2 (\<lambda>X Y. card X \<le> card Y) Xs Ys"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons X Xs Y Ys)
  have fY: "finite Y" using Cons.prems by simp
  have tail_fin: "\<And>Yy. Yy \<in> set Ys \<Longrightarrow> finite Yy" using Cons.prems by simp
  have "card X \<le> card Y" using card_mono[OF fY Cons.hyps(1)] .
  moreover have "list_all2 (\<lambda>X Y. card X \<le> card Y) Xs Ys"
    using Cons.IH[OF tail_fin] .
  ultimately show ?case by simp
qed

lemma finite_range_tree_child_list_elem:
  "Y \<in> set (range_tree_child_list S a bs) \<Longrightarrow> finite Y"
  by (induction bs arbitrary: a) auto

lemma list_all2_subset_imp_card_le_range_tree_child_list:
  assumes "list_all2 (\<subseteq>) Xs (range_tree_child_list S a bs)"
  shows "list_all2 (\<lambda>X R. card X \<le> card R) Xs (range_tree_child_list S a bs)"
  by (rule list_all2_card_mono_if_finite_right[OF assms])
     (rule finite_range_tree_child_list_elem)

theorem charged_direct_insert_costed_partition_loop_state_source_sum_le_chain_if_settled:
  assumes loop:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  shows "\<exists>child_sources.
    length child_sources = length bs \<and>
    list_all2
      (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
        charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs) \<and>
    c \<le> sum_list child_costs + sum_list (map card child_sources) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      h * sum_list (map card child_sources) \<and>
    (list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs) \<longrightarrow>
       sum_list (map card child_sources) \<le> card (range_tree_chain P a bs B'))"
proof -
  have mono: "nondecreasing_from a bs"
    using charged_direct_insert_costed_partition_loop_state_mono[OF loop] .
  obtain child_sources where
    L: "length child_sources = length bs" and
    A2: "list_all2
      (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
        charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs)" and
    C: "c \<le> sum_list child_costs + sum_list (map card child_sources) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      h * sum_list (map card child_sources)"
    using charged_direct_insert_costed_partition_loop_state_cost_bound_by_child_sources_and_edge_ranges[OF loop sound pre reaches]
    by blast
  have settle_imp:
    "list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs) \<longrightarrow>
       sum_list (map card child_sources) \<le> card (range_tree_chain P a bs B')"
  proof
    assume sub: "list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs)"
    have dom: "list_all2 (\<lambda>X R. card X \<le> card R) child_sources (range_tree_child_list P a bs)"
      using list_all2_subset_imp_card_le_range_tree_child_list[OF sub] .
    show "sum_list (map card child_sources) \<le> card (range_tree_chain P a bs B')"
      by (rule sum_card_dominated_by_range_tree_child_list_le_chain[OF mono dom])
  qed
  show ?thesis
    using L A2 C settle_imp by blast
qed


text \<open>Explicit linear per-loop cost.  Substituting the settled source bound into
  the cost decomposition turns the only non-telescoping source term
  \<open>(1 + h) * sum_list (map card child_sources)\<close> into a linear function of the
  produced range-tree chain.  Under the transparent settledness invariant the
  charged partition-loop cost is therefore bounded by the recursive child costs
  plus \<open>(1 + h) * card (range_tree_chain P a bs B')\<close> plus the edge-range terms
  (which telescope linearly through the shared @{term range_tree_child_list}
  machinery, exactly as in the direct-insert level bound).  This is the cost half
  of the charged per-level closer; the only remaining obligation to discharge the
  charged top-level bound is the settledness hypothesis itself, i.e.\ the global
  amortized no-stranding invariant.\<close>

theorem charged_direct_insert_costed_partition_loop_state_cost_le_linear_if_settled:
  assumes loop:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  shows "\<exists>child_sources.
    length child_sources = length bs \<and>
    list_all2
      (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
        charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs) \<and>
    (list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs) \<longrightarrow>
       c \<le> sum_list child_costs
           + (1 + h) * card (range_tree_chain P a bs B')
           + t * sum_list
               (map card (range_tree_child_direct_edge_range_list P B a betas bs))
           + h * sum_list
               (map card (range_tree_child_edge_range_list P a betas bs)))"
proof -
  obtain child_sources where
    L: "length child_sources = length bs" and
    A2: "list_all2
      (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
        charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs)" and
    C: "c \<le> sum_list child_costs + sum_list (map card child_sources) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      h * sum_list (map card child_sources)" and
    settle_imp:
      "list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs) \<longrightarrow>
         sum_list (map card child_sources) \<le> card (range_tree_chain P a bs B')"
    using charged_direct_insert_costed_partition_loop_state_source_sum_le_chain_if_settled
      [OF loop sound pre reaches]
    by blast
  have linear_imp:
    "list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs) \<longrightarrow>
       c \<le> sum_list child_costs
           + (1 + h) * card (range_tree_chain P a bs B')
           + t * sum_list
               (map card (range_tree_child_direct_edge_range_list P B a betas bs))
           + h * sum_list
               (map card (range_tree_child_edge_range_list P a betas bs))"
  proof
    assume sub: "list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs)"
    let ?SC = "sum_list (map card child_sources)"
    let ?K = "card (range_tree_chain P a bs B')"
    have SCK: "?SC \<le> ?K" using settle_imp sub by blast
    have "c \<le> sum_list child_costs + ?SC + h * ?SC +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))"
      using C by simp
    also have "sum_list child_costs + ?SC + h * ?SC = sum_list child_costs + (1 + h) * ?SC"
      by simp
    finally have step1:
      "c \<le> sum_list child_costs + (1 + h) * ?SC
          + t * sum_list
              (map card (range_tree_child_direct_edge_range_list P B a betas bs))
          + h * sum_list
              (map card (range_tree_child_edge_range_list P a betas bs))"
      by simp
    have "(1 + h) * ?SC \<le> (1 + h) * ?K"
      by (rule mult_le_mono2[OF SCK])
    then show "c \<le> sum_list child_costs
           + (1 + h) * ?K
           + t * sum_list
               (map card (range_tree_child_direct_edge_range_list P B a betas bs))
           + h * sum_list
               (map card (range_tree_child_edge_range_list P a betas bs))"
      using step1 by linarith
  qed
  show ?thesis using L A2 linear_imp by blast
qed


text \<open>Fully-linear per-loop local budget under settledness.  The two edge-range
  sums telescope to @{term edge_count} through the shared
  @{term range_tree_child_edge_range_list} /
  @{term range_tree_child_direct_edge_range_list} disjointness lemmas (the same
  ones the direct-insert level bound uses), so under the settledness invariant the
  charged partition-loop cost reduces to the canonical local budget
  \<open>sum_list child_costs + (1 + h) * card (range_tree_chain P a bs B') +
  (t + h) * edge_count\<close>: recursive child costs, a linear function of the produced
  range-tree chain, and a linear function of the edge count.  This is precisely
  the per-level local-budget shape consumed by the direct-insert linchpin
  induction; the charged top-level bound now reduces to threading the single
  settledness hypothesis through that induction.\<close>

theorem charged_direct_insert_costed_partition_loop_state_cost_local_budget_if_settled:
  assumes loop:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
  shows "\<exists>child_sources.
    length child_sources = length bs \<and>
    list_all2
      (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
        charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs) \<and>
    (list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs) \<longrightarrow>
       c \<le> sum_list child_costs
           + (1 + h) * card (range_tree_chain P a bs B')
           + (t + h) * edge_count)"
proof -
  have mono: "nondecreasing_from a bs"
    using charged_direct_insert_costed_partition_loop_state_mono[OF loop] .
  obtain child_sources where
    L: "length child_sources = length bs" and
    A2: "list_all2
      (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
        charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
          d_child B_child' U_child c_child \<and>
        bmssp_pre_full d S_child B_child \<and>
        (\<forall>x\<in>S_child. reachable s x) \<and>
        card S_child \<le> M_of l \<and>
        (\<forall>x\<in>S_child. below_bound (d x) B_child))
      child_sources (range_tree_child_list P a bs)" and
    lin_imp:
      "list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs) \<longrightarrow>
         c \<le> sum_list child_costs
             + (1 + h) * card (range_tree_chain P a bs B')
             + t * sum_list
                 (map card (range_tree_child_direct_edge_range_list P B a betas bs))
             + h * sum_list
                 (map card (range_tree_child_edge_range_list P a betas bs))"
    using charged_direct_insert_costed_partition_loop_state_cost_le_linear_if_settled
      [OF loop sound pre reaches]
    by blast
  have edge_direct:
    "sum_list (map card (range_tree_child_direct_edge_range_list P B a betas bs))
      \<le> edge_count"
    by (rule sum_card_range_tree_child_direct_edge_range_list_le_edge_count[OF mono])
  have edge_lower:
    "sum_list (map card (range_tree_child_edge_range_list P a betas bs))
      \<le> edge_count"
    by (rule sum_card_range_tree_child_edge_range_list_le_edge_count[OF mono])
  have budget_imp:
    "list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs) \<longrightarrow>
       c \<le> sum_list child_costs
           + (1 + h) * card (range_tree_chain P a bs B')
           + (t + h) * edge_count"
  proof
    assume sub: "list_all2 (\<subseteq>) child_sources (range_tree_child_list P a bs)"
    let ?K = "card (range_tree_chain P a bs B')"
    have c_le:
      "c \<le> sum_list child_costs + (1 + h) * ?K
          + t * sum_list
              (map card (range_tree_child_direct_edge_range_list P B a betas bs))
          + h * sum_list
              (map card (range_tree_child_edge_range_list P a betas bs))"
      using lin_imp sub by blast
    have t_bound: "t * sum_list
            (map card (range_tree_child_direct_edge_range_list P B a betas bs))
          \<le> t * edge_count"
      by (rule mult_le_mono2[OF edge_direct])
    have h_bound: "h * sum_list
            (map card (range_tree_child_edge_range_list P a betas bs))
          \<le> h * edge_count"
      by (rule mult_le_mono2[OF edge_lower])
    have dist: "(t + h) * edge_count = t * edge_count + h * edge_count"
      by (simp add: algebra_simps)
    show "c \<le> sum_list child_costs + (1 + h) * ?K + (t + h) * edge_count"
      using c_le t_bound h_bound unfolding dist by linarith
  qed
  show ?thesis using L A2 budget_imp by blast
qed

text \<open>\<^bold>\<open>Increment monotonicity bridge.\<close>  A child run's cost is bounded by its
  \<^emph>\<open>own\<close> range-tree increment @{term "range_tree (split_below d P beta) a B"};
  because the pulled source @{term "split_below d P beta"} sits inside the parent
  pivot tree, that increment is contained in the parent slice
  @{term "range_tree P a B"}, and @{const level_range_cost_bound} is monotone in
  the set argument.  Hence the intrinsic child bound transfers to the slice bound
  the loop closer consumes --- using only the easy containment direction, with no
  cut-equality obligation.\<close>

lemma tree_set_mono: "X \<subseteq> Y \<Longrightarrow> tree_set X \<subseteq> tree_set Y"
  unfolding tree_set_def by blast

lemma range_tree_mono_tree_set:
  "tree_set S \<subseteq> tree_set P \<Longrightarrow> range_tree S a B \<subseteq> range_tree P a B"
  unfolding range_tree_def by blast

lemma range_tree_split_below_subset:
  "range_tree (split_below d P beta) a B \<subseteq> range_tree P a B"
  by (rule range_tree_mono_tree_set, rule tree_set_mono, rule split_below_subset)

lemma level_range_cost_bound_mono:
  assumes sub: "X \<subseteq> Y" and finY: "finite Y"
  shows "level_range_cost_bound A R L X \<le> level_range_cost_bound A R L Y"
proof -
  have "card X \<le> card Y" by (rule card_mono[OF finY sub])
  moreover have "card (outgoing_edges X) \<le> card (outgoing_edges Y)"
    by (rule card_mono[OF finite_outgoing_edges outgoing_edges_mono[OF sub]])
  ultimately show ?thesis
    unfolding level_range_cost_bound_def by (intro add_mono mult_le_mono2)
qed

lemma level_range_cost_bound_range_tree_split_below_le:
  assumes finP: "finite (range_tree P a B)"
  shows "level_range_cost_bound A R L (range_tree (split_below d P beta) a B)
       \<le> level_range_cost_bound A R L (range_tree P a B)"
  by (rule level_range_cost_bound_mono[OF range_tree_split_below_subset finP])

text \<open>\<^bold>\<open>Increment-faithful charged loop closer.\<close>  The same per-loop accounting as
  @{thm [source] charged_direct_insert_costed_partition_loop_state_closes_level_bound_from_child_bound_with_invariants_and_edge_ranges},
  but the produced bound is kept against the range-tree \<^emph>\<open>chain\<close>
  @{term "range_tree_chain P a bs B'"} --- the freshly-settled increment of the
  loop --- rather than being loosened to the loop output @{term U}.  Keeping the
  chain is what lets the bound telescope across the recursion: a child's loop
  charges only its own increment, and sibling increments are disjoint.  The
  source term @{term "(Suc h) * card (range_tree_chain P a bs B')"} is absorbed
  into the vertex coefficient through @{term "Suc h \<le> A"}.\<close>

theorem charged_direct_insert_costed_partition_loop_state_closes_increment_bound_from_child_bound_with_invariants:
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
  shows "c \<le>
    A * Suc L * card (range_tree_chain P a bs B') +
    R * card (outgoing_edges (range_tree_chain P a bs B')) +
    t * sum_list
      (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
    h * sum_list
      (map card (range_tree_child_edge_range_list P a betas bs))"
proof -
  have P_subset: "P \<subseteq> V"
    using pre unfolding bmssp_pre_full_def by blast
  have child_cost_bounds:
    "list_all2 (\<lambda>c_child charged_child.
      c_child \<le> level_range_cost_bound A R L charged_child)
      child_costs (range_tree_child_list P a bs)"
    by (rule charged_direct_insert_costed_partition_loop_state_child_cost_bounds_with_invariants
      [OF run P_subset P_k_cap P_anti child_bound])
  obtain child_sources where sources:
      "list_all2
        (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
          charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
        child_sources (range_tree_child_list P a bs)"
    and cost:
      "c \<le> sum_list child_costs + sum_list (map card child_sources) +
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs)) +
        h * sum_list (map card child_sources)"
    using charged_direct_insert_costed_partition_loop_state_cost_bound_by_child_sources_and_edge_ranges
      [OF run sound pre P_reaches] by blast
  have source_sum:
    "sum_list (map card child_sources) \<le> card (range_tree_chain P a bs B')"
    by (rule source_progress[OF sources])
  have mono: "nondecreasing_from a bs"
    by (rule charged_direct_insert_costed_partition_loop_state_mono[OF run])
  have child_sum:
    "sum_list child_costs \<le>
      A * L * card (range_tree_chain P a bs B') +
      R * card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule child_costs_le_level_range_child_list_bound[OF mono child_cost_bounds])
  let ?K = "card (range_tree_chain P a bs B')"
  let ?OE = "card (outgoing_edges (range_tree_chain P a bs B'))"
  let ?D = "sum_list (map card (range_tree_child_direct_edge_range_list P B a betas bs))"
  let ?E = "sum_list (map card (range_tree_child_edge_range_list P a betas bs))"
  let ?SC = "sum_list (map card child_sources)"
  have src_abs: "?SC + h * ?SC \<le> A * ?K"
  proof -
    have "?SC + h * ?SC = Suc h * ?SC" by simp
    also have "\<dots> \<le> Suc h * ?K" using source_sum by (rule mult_le_mono2)
    also have "\<dots> \<le> A * ?K" using source_factor by (rule mult_le_mono1)
    finally show ?thesis .
  qed
  have "c \<le> (A * L * ?K + R * ?OE) + ?SC + t * ?D + h * ?E + h * ?SC"
    using cost child_sum by linarith
  also have "\<dots> = A * L * ?K + R * ?OE + t * ?D + h * ?E + (?SC + h * ?SC)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> A * L * ?K + R * ?OE + t * ?D + h * ?E + A * ?K"
    using src_abs by linarith
  also have "\<dots> = A * Suc L * ?K + R * ?OE + t * ?D + h * ?E"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Charged amortized accounting (B2).\<close>  The charged counterpart of
  the direct-insert amortized chain (@{thm [source] direct_insert_costed_partition_loop_state_closes_amortized_bound_from_child_costs}).
  The pulled child sources are absorbed into the produced range-tree chain via
  the per-loop \<open>source_progress\<close> settledness oracle, and the edge-range sums
  telescope through the shared disjointness lemmas exactly as in the
  direct-insert development.  These reduce the charged top-level refined bound to
  the single settledness side-condition.\<close>

text \<open>\<^bold>\<open>Increment-monotonicity bridge for the amortized budget.\<close>  The amortized
  cost budget is monotone in its vertex-set argument (all three of @{const card},
  @{const outgoing_edges}, and @{const outgoing_edges_range} are), so a child run's
  intrinsic amortized bound against its own range-tree increment
  @{term "range_tree (split_below d P beta) a B'"} transfers to the parent slice
  @{term "range_tree P a B'"} that the loop closer consumes --- using only the easy
  containment direction @{thm [source] range_tree_split_below_subset}.\<close>

lemma bmssp_amortized_cost_bound_mono:
  assumes sub: "X \<subseteq> Y" and finY: "finite Y"
  shows "bmssp_amortized_cost_bound A R h t q L B X
       \<le> bmssp_amortized_cost_bound A R h t q L B Y"
proof -
  have cX: "card X \<le> card Y" by (rule card_mono[OF finY sub])
  have cOE: "card (outgoing_edges X) \<le> card (outgoing_edges Y)"
    by (rule card_mono[OF finite_outgoing_edges outgoing_edges_mono[OF sub]])
  have cOER: "card (outgoing_edges_range X 0 B) \<le> card (outgoing_edges_range Y 0 B)"
    by (rule card_mono[OF finite_outgoing_edges_range outgoing_edges_range_mono_sources[OF sub]])
  show ?thesis
    unfolding bmssp_amortized_cost_bound_def
    using cX cOE cOER by (intro add_mono mult_le_mono2)
qed

lemma bmssp_amortized_cost_bound_range_tree_split_below_le:
  assumes finP: "finite (range_tree P a B')"
  shows "bmssp_amortized_cost_bound A R h t q L B
            (range_tree (split_below d P beta) a B')
       \<le> bmssp_amortized_cost_bound A R h t q L B (range_tree P a B')"
  by (rule bmssp_amortized_cost_bound_mono[OF range_tree_split_below_subset finP])

theorem charged_cost_from_child_source_and_amortized_bounds:
  assumes run:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
        c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
        child_costs (range_tree_child_bound_pair_list P a betas bs)"
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
  shows "c \<le>
    A * L * card (range_tree_chain P a bs B') +
    (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
    t * sum_list
      (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
    t * sum_list
      (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
    h * sum_list
      (map card (range_tree_child_edge_range_list P a betas bs)) +
    (Suc h) * card (range_tree_chain P a bs B')"
proof -
  obtain child_sources where sources:
      "list_all2
        (\<lambda>S_child charged_child. \<exists>c_child U_child B_child d_child B_child'.
          charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child \<and>
          bmssp_pre_full d S_child B_child \<and>
          (\<forall>x\<in>S_child. reachable s x) \<and>
          card S_child \<le> M_of l \<and>
          (\<forall>x\<in>S_child. below_bound (d x) B_child))
        child_sources (range_tree_child_list P a bs)"
    and cost:
      "c \<le> sum_list child_costs + sum_list (map card child_sources) +
        t * sum_list
          (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs)) +
        h * sum_list (map card child_sources)"
    using charged_direct_insert_costed_partition_loop_state_cost_bound_by_child_sources_and_edge_ranges
      [OF run sound pre P_reaches] by blast
  have mono: "nondecreasing_from a bs"
    by (rule charged_direct_insert_costed_partition_loop_state_mono[OF run])
  have source_sum:
    "sum_list (map card child_sources) \<le> card (range_tree_chain P a bs B')"
    by (rule source_progress[OF sources])
  have child_sum_raw:
    "sum_list child_costs \<le>
      A * L * sum_list (map card (range_tree_child_list P a bs)) +
      (R + q * h) *
        sum_list (map (\<lambda>U. card (outgoing_edges U))
          (range_tree_child_list P a bs)) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs))"
    by (rule sum_bmssp_amortized_child_bounds_le[OF child_cost_bounds])
  have child_card_sum:
    "sum_list (map card (range_tree_child_list P a bs)) \<le>
      card (range_tree_chain P a bs B')"
    by (rule card_range_tree_child_list_le_chain[OF mono])
  have child_out_sum:
    "sum_list (map (\<lambda>U. card (outgoing_edges U))
        (range_tree_child_list P a bs)) \<le>
      card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule card_outgoing_edges_range_tree_child_list_le_chain[OF mono])
  have child_sum:
    "sum_list child_costs \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs))"
  proof -
    have vterm:
      "A * L * sum_list (map card (range_tree_child_list P a bs)) \<le>
       A * L * card (range_tree_chain P a bs B')"
      using child_card_sum by simp
    have eterm:
      "(R + q * h) *
        sum_list (map (\<lambda>U. card (outgoing_edges U))
          (range_tree_child_list P a bs)) \<le>
       (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B'))"
      using child_out_sum by simp
    show ?thesis
      using child_sum_raw vterm eterm by linarith
  qed
  have "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      sum_list (map card child_sources) +
      h * sum_list (map card child_sources)"
    using cost child_sum by linarith
  also have "\<dots> \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      (Suc h) * card (range_tree_chain P a bs B')"
  proof -
    have h_part:
      "h * sum_list (map card child_sources) \<le>
        h * card (range_tree_chain P a bs B')"
      using source_sum by simp
    have "sum_list (map card child_sources) +
        h * sum_list (map card child_sources) \<le>
      card (range_tree_chain P a bs B') +
        h * card (range_tree_chain P a bs B')"
      using source_sum h_part by linarith
    then have "sum_list (map card child_sources) +
        h * sum_list (map card child_sources) \<le>
      Suc h * card (range_tree_chain P a bs B')"
      by (simp add: algebra_simps)
    then show ?thesis by linarith
  qed
  finally show ?thesis .
qed

theorem charged_direct_insert_costed_partition_loop_state_closes_amortized_bound_from_child_costs:
  assumes run:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U c child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
        c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
        child_costs (range_tree_child_bound_pair_list P a betas bs)"
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
  shows "c \<le> bmssp_amortized_cost_bound A R h t (Suc q) (Suc L) B U"
proof -
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
  have finite_U: "finite U"
    using U_eq_chain by simp
  have chain_subset: "range_tree_chain P a bs B' \<subseteq> U"
    using U_eq_chain by blast
  have card_chain_le: "card (range_tree_chain P a bs B') \<le> card U"
    by (rule card_mono[OF finite_U chain_subset])
  have outgoing_subset:
    "outgoing_edges (range_tree_chain P a bs B') \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF chain_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le:
    "card (outgoing_edges (range_tree_chain P a bs B')) \<le>
      card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have range_subset:
    "outgoing_edges_range (range_tree_chain P a bs B') 0 B \<subseteq>
      outgoing_edges_range U 0 B"
    by (rule outgoing_edges_range_mono_sources[OF chain_subset])
  have card_range_le:
    "card (outgoing_edges_range (range_tree_chain P a bs B') 0 B) \<le>
      card (outgoing_edges_range U 0 B)"
    by (rule card_mono[OF finite_outgoing_edges_range range_subset])
  have mono: "nondecreasing_from a bs"
    by (rule charged_direct_insert_costed_partition_loop_state_mono[OF run])
  have beta_bounds: "bounds_le B betas"
    by (rule charged_direct_insert_costed_partition_loop_state_beta_bounds[OF run])
  have cost:
    "c \<le>
      A * L * card (range_tree_chain P a bs B') +
      (R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs)) +
      (Suc h) * card (range_tree_chain P a bs B')"
    by (rule charged_cost_from_child_source_and_amortized_bounds
      [OF run sound pre P_reaches child_cost_bounds source_progress])
  have lower_sum:
    "sum_list (map card (range_tree_child_edge_range_list P a betas bs))
      \<le> card (outgoing_edges (range_tree_chain P a bs B'))"
    by (rule sum_card_range_tree_child_edge_range_list_le_outgoing_edges_chain
      [OF mono])
  have direct_sum:
    "sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
     sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs))
     \<le> card (outgoing_edges_range (range_tree_chain P a bs B') 0 B)"
    by (rule sum_card_range_tree_child_zero_direct_edge_ranges_le_outgoing_edges_range_chain
      [OF mono beta_bounds])
  have vertex_part:
    "A * L * card (range_tree_chain P a bs B') +
      Suc h * card (range_tree_chain P a bs B') \<le>
     A * Suc L * card U"
  proof -
    have source_term:
      "Suc h * card (range_tree_chain P a bs B') \<le>
       A * card U"
    proof -
      have "Suc h * card (range_tree_chain P a bs B') \<le>
          A * card (range_tree_chain P a bs B')"
        by (rule mult_right_mono[OF source_factor]) simp
      also have "\<dots> \<le> A * card U"
        using card_chain_le by simp
      finally show ?thesis .
    qed
    have child_term:
      "A * L * card (range_tree_chain P a bs B') \<le>
       A * L * card U"
      using card_chain_le by simp
    have "A * L * card U + A * card U = A * Suc L * card U"
      by (simp add: algebra_simps)
    then show ?thesis
      using child_term source_term by linarith
  qed
  have edge_part:
    "(R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
      h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))
     \<le> (R + Suc q * h) * card (outgoing_edges U)"
  proof -
    have lower_term:
      "h * sum_list
        (map card (range_tree_child_edge_range_list P a betas bs))
       \<le> h * card (outgoing_edges (range_tree_chain P a bs B'))"
      using lower_sum by simp
    have chain_term:
      "(R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
        h * card (outgoing_edges (range_tree_chain P a bs B')) =
       (R + Suc q * h) *
        card (outgoing_edges (range_tree_chain P a bs B'))"
      by (simp add: algebra_simps)
    have to_chain:
      "(R + q * h) * card (outgoing_edges (range_tree_chain P a bs B')) +
        h * sum_list
          (map card (range_tree_child_edge_range_list P a betas bs))
       \<le> (R + Suc q * h) *
        card (outgoing_edges (range_tree_chain P a bs B'))"
      using lower_term chain_term by linarith
    have to_U:
      "(R + Suc q * h) *
        card (outgoing_edges (range_tree_chain P a bs B')) \<le>
       (R + Suc q * h) * card (outgoing_edges U)"
      using card_out_le by simp
    show ?thesis
      using to_chain to_U by linarith
  qed
  have direct_part:
    "t * sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      t * sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs))
     \<le> t * card (outgoing_edges_range U 0 B)"
  proof -
    have "t * (sum_list
        (map card (range_tree_child_zero_edge_range_list P a betas bs)) +
      sum_list
        (map card (range_tree_child_direct_edge_range_list P B a betas bs)))
      \<le> t * card (outgoing_edges_range (range_tree_chain P a bs B') 0 B)"
      using direct_sum by simp
    also have "\<dots> \<le> t * card (outgoing_edges_range U 0 B)"
      using card_range_le by simp
    finally show ?thesis
      by (simp add: algebra_simps)
  qed
  have "c \<le>
      A * Suc L * card U +
      (R + Suc q * h) * card (outgoing_edges U) +
      t * card (outgoing_edges_range U 0 B)"
    using cost vertex_part edge_part direct_part by linarith
  then show ?thesis
    unfolding bmssp_amortized_cost_bound_def .
qed

theorem charged_direct_insert_costed_nonbase_step_closes_amortized_bound_from_child_costs:
  assumes loop:
    "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U_loop c_loop child_costs"
    and sound: "sound_label d"
    and pre: "bmssp_pre_full d P B"
    and P_reaches: "\<And>x. x \<in> P \<Longrightarrow> reachable s x"
    and child_cost_bounds:
      "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
        c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
        child_costs (range_tree_child_bound_pair_list P a betas bs)"
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
    and U_def: "U = U_loop \<union> W"
    and finite_U: "finite U"
    and scan_insert: "c_scan_insert \<le> A * card U"
    and c_def: "c = c_scan_insert + c_loop"
  shows "c \<le>
    bmssp_amortized_cost_bound A R h t (Suc q) (Suc (Suc L)) B U"
proof -
  have loop_bound:
    "c_loop \<le>
      bmssp_amortized_cost_bound A R h t (Suc q) (Suc L) B U_loop"
    by (rule charged_direct_insert_costed_partition_loop_state_closes_amortized_bound_from_child_costs
      [OF loop sound pre P_reaches child_cost_bounds source_factor source_progress])
  have U_loop_subset: "U_loop \<subseteq> U"
    using U_def by blast
  have card_loop_le: "card U_loop \<le> card U"
    by (rule card_mono[OF finite_U U_loop_subset])
  have outgoing_subset: "outgoing_edges U_loop \<subseteq> outgoing_edges U"
    by (rule outgoing_edges_mono[OF U_loop_subset])
  have finite_out_U: "finite (outgoing_edges U)"
    by simp
  have card_out_le: "card (outgoing_edges U_loop) \<le> card (outgoing_edges U)"
    by (rule card_mono[OF finite_out_U outgoing_subset])
  have range_subset:
    "outgoing_edges_range U_loop 0 B \<subseteq> outgoing_edges_range U 0 B"
    by (rule outgoing_edges_range_mono_sources[OF U_loop_subset])
  have card_range_le:
    "card (outgoing_edges_range U_loop 0 B) \<le>
      card (outgoing_edges_range U 0 B)"
    by (rule card_mono[OF finite_outgoing_edges_range range_subset])
  have loop_to_U:
    "c_loop \<le>
      A * Suc L * card U +
      (R + Suc q * h) * card (outgoing_edges U) +
      t * card (outgoing_edges_range U 0 B)"
  proof -
    have vterm:
      "A * Suc L * card U_loop \<le> A * Suc L * card U"
      using card_loop_le by simp
    have eterm:
      "(R + Suc q * h) * card (outgoing_edges U_loop) \<le>
       (R + Suc q * h) * card (outgoing_edges U)"
      using card_out_le by simp
    have rterm:
      "t * card (outgoing_edges_range U_loop 0 B) \<le>
       t * card (outgoing_edges_range U 0 B)"
      using card_range_le by simp
    show ?thesis
      using loop_bound vterm eterm rterm
      unfolding bmssp_amortized_cost_bound_def by linarith
  qed
  have "c \<le>
      A * card U +
      (A * Suc L * card U +
       (R + Suc q * h) * card (outgoing_edges U) +
       t * card (outgoing_edges_range U 0 B))"
    using scan_insert loop_to_U c_def by linarith
  also have "\<dots> =
      A * Suc (Suc L) * card U +
      (R + Suc q * h) * card (outgoing_edges U) +
      t * card (outgoing_edges_range U 0 B)"
    by (simp add: algebra_simps)
  finally show ?thesis
    unfolding bmssp_amortized_cost_bound_def .
qed

text \<open>\<^bold>\<open>Charged amortized child-cost propagator.\<close>  The amortized
  counterpart of @{thm [source] charged_direct_insert_costed_partition_loop_state_child_cost_bounds_with_invariants}:
  it threads an amortized per-child budget (stated against the disjoint range-tree
  slice @{term charged_child}) across the partition loop, producing the list the
  amortized loop closer consumes.  In a recursion-level induction the per-child
  budget is discharged by the inductive hypothesis against the child increment and
  the increment->slice bridge
  @{thm [source] bmssp_amortized_cost_bound_range_tree_split_below_le}.\<close>

theorem charged_direct_insert_costed_partition_loop_state_child_amortized_cost_bounds_with_invariants:
  "charged_direct_insert_costed_partition_loop_state \<Delta> M_of t h k cap l d P B d' D a
      betas bs B' charged_Us child_outputs U c child_costs \<Longrightarrow>
    P \<subseteq> V \<Longrightarrow>
    k * card P \<le> cap \<Longrightarrow>
    tree_antichain P \<Longrightarrow>
    (\<And>c_child charged_child U_child S_child B_child d_child B_child'.
        \<lbrakk>charged_direct_insert_costed_bmssp \<Delta> M_of t h k cap l d S_child B_child
            d_child B_child' U_child c_child;
          bmssp_pre_full d S_child B_child;
          \<And>x. x \<in> S_child \<Longrightarrow> reachable s x;
          card S_child \<le> M_of l;
          \<And>x. x \<in> S_child \<Longrightarrow> below_bound (d x) B_child;
          k * card S_child \<le> cap;
          tree_antichain S_child\<rbrakk>
        \<Longrightarrow> c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child charged_child) \<Longrightarrow>
    list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
      c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
    child_costs (range_tree_child_bound_pair_list P a betas bs)"
and charged_direct_insert_costed_bmssp_child_amortized_cost_bounds_with_invariants_trivial:
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
  have tail:
    "list_all2 (\<lambda>c_child UB. case UB of (U_child, B_child) \<Rightarrow>
      c_child \<le> bmssp_amortized_cost_bound A R h t q L B_child U_child)
      child_costs_tail (range_tree_child_bound_pair_list P b betas bs)"
    using Charged_Direct_Insert_State_Step.IH Charged_Direct_Insert_State_Step.prems
    by blast
  have card_pull: "card S_pull \<le> M_of l"
    using Charged_Direct_Insert_State_Step unfolding pull_separates_def by blast
  have below_pull: "\<And>x. x \<in> S_pull \<Longrightarrow> below_bound (d x) (Fin beta)"
  proof -
    fix x assume xS: "x \<in> S_pull"
    have "S_pull = split_below d P beta" using Charged_Direct_Insert_State_Step by blast
    then show "below_bound (d x) (Fin beta)" using xS unfolding split_below_def by auto
  qed
  have pull_k_cap: "k * card S_pull \<le> cap"
  proof -
    have "S_pull = split_below d P beta" using Charged_Direct_Insert_State_Step by blast
    then show ?thesis
      using split_below_scaled_card_le
        [OF Charged_Direct_Insert_State_Step.prems(1)
          Charged_Direct_Insert_State_Step.prems(2), of d beta] by simp
  qed
  have pull_anti: "tree_antichain S_pull"
  proof -
    have "S_pull = split_below d P beta" using Charged_Direct_Insert_State_Step by blast
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
  have charged_child_eq: "charged_child = range_tree P a (Fin b)"
    using Charged_Direct_Insert_State_Step by blast
  have head:
    "c_child \<le> bmssp_amortized_cost_bound A R h t q L (Fin beta) charged_child"
    by (rule Charged_Direct_Insert_State_Step.prems(4)
      [OF child_run pre_pull reaches_pull card_pull below_pull
        pull_k_cap pull_anti])
  show ?case
    using head tail Charged_Direct_Insert_State_Step charged_child_eq by simp
next
  case (Charged_Direct_Insert_Base S x \<Delta> M_of t h k cap d B)
  then show ?case by simp
next
  case (Charged_Direct_Insert_Step D k cap d S B c_insert t \<Delta> M_of h l
      d' a betas bs B' charged_Us child_outputs U_loop c_loop child_costs_loop U c)
  then show ?case by simp
qed

end

end
