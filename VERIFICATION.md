# BMSSP Verification Trace

This file records the current submission-facing verification state for the
BMSSP entry.

## Public Claim Split

The checked development exposes seven public surfaces:

1. Executable correctness for `bmssp_distances`, stated in
   `BMSSP_Executable_Headline`.
2. Cost-model asymptotic bounds for the costed BMSSP recurrence, stated in
   `BMSSP_Top_Level_Bounds`.
3. A verified-correct-run runtime bound joining (1)-style correctness with the
   (2) asymptotic bound on a single object, stated in
   `BMSSP_Verified_Runtime` (`verified_bmssp_runtime_bigo_target`).
4. A size-parametric path-family surface over the unbounded family `P_k`,
   stated in `BMSSP_Path_Family`. Three distinct claims must be separated here:
   - `path_size_cost_bigo_size` (UNCONDITIONAL, genuinely true): the closed BMSSP
     cost *expression* on `P_k`, with the graph cardinalities substituted, is
     `O(k * log^{2/3} k)` with the real graph size `k` as the asymptotic
     variable. This is arithmetic about the cost formula.
   - `bmssp_path_family_runtime_bigo_size` (CONDITIONAL and, for this family,
     VACUOUS): the same bound for the *running time of an actual run*, under a
     hypothesis `runs_exist`. **`runs_exist` is unsatisfiable for `P_k` at every
     `k >= 2`** — see surface (6) — so this theorem, while logically valid, is
     witnessed by no run and must NOT be presented as evidence that the
     algorithm meets the bound. `path_k_bounded_instance` (runtime-locale
     inhabitation for every `k`) and `path_family_not_forced_degenerate` remain
     true and are about locale membership / the empty-pivot regime, not run
     existence.
   - `bmssp_path_family_charged_direct_insert_runtime_bigo_size_if_cost_bounded`
     (CONDITIONAL and checked): the strong-version bridge for
     `charged_direct_insert_top_level_time`. It assumes eventual
     `charged_direct_insert_top_level_cost` existence and the still-pending
     charged runtime upper-bound chain. The runtime branch reports the endpoint
     theorem as
     `charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree`,
     still conditional on
     `charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N`.
     It must not be presented as a final non-vacuous path-family theorem until
     those assumptions are discharged by the charged totality/existence and
     charged runtime-bound sessions.
5. Bucketed partition operation-cost realization facts, stated in
   `BMSSP_Bucketed_Partition_Internal` and re-exported through
   `BMSSP_Bucketed_Partition`.
6. A machine-checked obstruction record, stated in `BMSSP_Cost_Totality`
   (`exact_concrete_step_forces_empty_prefix`,
   `no_genuine_exact_concrete_step_at_positive_lower_bound`): under a sound
   label a genuine exact-concrete loop step is forced to lower bound zero, so
   the loop takes at most one genuine step. Because a complete top-level run
   must terminate in the `Done` case with output bound `Infinity`, and one
   step's truncating base case settles only a `k`-bounded prefix of the path,
   no complete run exists on `P_k` for `k >= 2`. This is why the `runs_exist`
   hypothesis of surface (4) cannot be discharged for the path family.
7. An **unconditional, non-vacuous** size-parametric runtime headline for the
   *charged* loop on the path family at a *decoupled, inflated* schedule, stated in
   `BMSSP_NonVacuous_Family` (`path_nonvac_runtime_bigo_card_V_unconditional`):
   `(\<lambda>n. real (path_nonvac_time n)) \<in> O(\<lambda>n. card V_n * (ln (card V_n))^{2/3})`
   with **no hypotheses**. Run-existence is proved unconditionally
   (`eventually_path_nonvac_charged_cost_exists`); the bounded quantity is the least
   charged cost of a genuine run; and the family is genuinely unbounded
   (`path_card_V_at_top`). This discharges the charged bridge of surface (4) on a
   different object (charged relation, schedule `n*n`) from the vacuous coupled-schedule
   exact-concrete bound of surface (6).

There is no theorem claiming a generated-code machine-step bound for the SML
export; the one-vertex-per-pull executable is a reference implementation and is
deliberately not claimed to meet the asymptotic bound.  **Scope note (disclosed,
not hidden):** the *exact-concrete* algorithm-level size-parametric bound at the
*coupled* schedule (surface 4, `bmssp_path_family_runtime_bigo_size`) is vacuous on
its own family — its `runs_exist` hypothesis is provably unsatisfiable for `P_k`,
`k >= 2` (surface 6) — and that specific theorem is retained only as an honest
record. A genuine **non-vacuous** algorithm-level size-parametric bound is
nevertheless available and is the discharged headline: surface 7
(`path_nonvac_runtime_bigo_card_V_unconditional`) runs the *charged* relation at a
*decoupled, inflated* schedule, where a complete run provably exists, and is fully
unconditional. The two are different objects (exact-concrete/coupled vs
charged/decoupled inflated) and do not conflict; the unconditional cost-formula floor
`path_size_cost_bigo_size` also remains genuinely true.

## Assumption Ledger

The executable headline is conditional exactly on
`nat_graph_well_formed G` and `src \<in> nat_graph_vertices G`.
`nat_graph_well_formed G` expands to a duplicate-free directed edge list and
`nat_graph_total_weight G < bmssp_infinity`; it does not include uniqueness of
shortest paths.

The asymptotic headline is a locale theorem for the costed recurrence.  The
assumption-free statement is assumption-free only after entering the runtime
locale, whose interpretation carries the reduced positive instance,
reachability, and bounded-outdegree hypotheses.

## Canonical Correctness Headline

The executable headline theorem is:

```isabelle
theorem bmssp_correct_strong:
  assumes well_formed: "nat_graph_well_formed G"
    and src_in: "src \<in> nat_graph_vertices G"
  shows
    "distinct (map fst (bmssp_distances G src)) \<and>
     set (map fst (bmssp_distances G src)) =
       {v \<in> nat_graph_vertices G. nat_graph_reachable G src v} \<and>
     (\<forall>(v, d) \<in> set (bmssp_distances G src).
        real d = nat_graph_dist G src v)"
```

The underlying executable refinement theorem is kept under the descriptive
name `bmssp_correct_executable`.

## Required Headline Names

- `bmssp_correct_strong`
- `bmssp_correct_executable`
- `bmssp_runtime_bigo_target`
- `verified_bmssp_runtime_bigo_target`
- `T_bmssp_realised_by_verified_run`
- `eventually_T_bmssp_realised_by_verified_run`
- `bp_realises_partition_insert_cost_bound`
- `bp_realises_partition_batch_cost_bound`
- `bp_realises_partition_pull_cost_bound`
- `bp_insert_cost_bound`
- `bp_batch_prepend_cost_bound`
- `bp_pull_cost_bound`
- `example_bmssp_correct`
- `path_runtime_bigo_target`
- `path_verified_runtime_bigo_target`
- `star_verified_runtime_bigo_target`
- `path_size_cost_bigo_size`
- `bmssp_path_family_runtime_bigo_size`
- `bmssp_path_family_charged_direct_insert_runtime_bigo_size_if_cost_bounded`
- `path_k_bounded_instance`
- `path_family_not_forced_degenerate`
- `exact_concrete_step_forces_empty_prefix`
- `no_genuine_exact_concrete_step_at_positive_lower_bound`

## Runtime Locale Non-Vacuity

`bmssp_runtime_bigo_target` and the joined
`verified_bmssp_runtime_bigo_target` are theorems of the runtime locale
`bounded_reduced_positive_instance`.  Two structurally different theories
interpret that locale on explicit graphs, discharging all of its assumptions
(unique shortest walks, positive weights, full reachability, bounded
outdegree):

- `BMSSP_Runtime_Instance` on the unit-weight directed path `0 -> 1 -> 2 -> 3`
  (outdegree one), re-exporting `path_runtime_bigo_target` and
  `path_verified_runtime_bigo_target`;
- `BMSSP_Runtime_Instance_Branching` on the out-star `1 <- 0 -> 2`
  (outdegree two, two incomparable shortest paths), re-exporting
  `star_runtime_bigo_target` and `star_verified_runtime_bigo_target`.

The `*_verified_runtime_bigo_target` facts are closed, assumption-free
instances in which the logarithmic running-time bound is coupled with the
guarantee that the bounded running time is, eventually, the cost of a run
returning exact shortest-path distances.  Because the two graphs share no
structural feature beyond the locale assumptions, together they certify that
the runtime headline is non-vacuous across genuinely different graph shapes.

## Build Commands

With a stock **Isabelle2025-2** (the `isabelle` executable on the `PATH`), run
from this entry's directory (`projects/bmssp-isabelle`):

```bash
isabelle build -D . BMSSP_Correctness
```

For the full presentation PDF:

```bash
isabelle build -P bmssp-pdf-out -D . BMSSP_Correctness
```

On the original Windows development host the same build is driven through the
bundled Cygwin Bash, e.g.:

```bash
/cygdrive/q/src/isabelle-borel-determinacy/toolchain/Isabelle2025-2/bin/isabelle build \
  -D . BMSSP_Correctness
```

## Proof Hygiene

The submission-facing theories are the top-level `*.thy` files reachable from
the public session root `BMSSP_Executable_Headline`.  They contain no
intentional proof holes or unchecked primitive shortcuts such as `sorry`,
`oops`, `axiomatization`, `smt_oracle`, or orphaned `sledgehammer` commands.

The remaining top-level theories are active session material.  A dependency
check from `BMSSP_Executable_Headline`, `BMSSP_Runtime_Instance`, and
`BMSSP_Runtime_Instance_Branching` reaches all of them, so there is no inactive
top-level proof theory left in the entry.

## Strong BMSSP Path-Family Integration Checklist

The checked charged theorem in `BMSSP_Path_Family` is deliberately conditional.
Once the parallel proof sessions land, update `HEADLINE.md`, `README.md`, and
`document/root.tex` only if the following facts are available and used to
instantiate its assumptions:

1. Eventual charged totality/existence on the path family, i.e. a theorem that
   proves the eventual statement
   `(\<lambda>k. \<exists>c. charged_direct_insert_top_level_cost 1 k c)` at `at_top`
   after interpreting `P_k`.
2. The remaining runtime closed-bound theorem
   `charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N`,
   so the reported exported theorem
   `charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree`
   can show each realised `charged_direct_insert_top_level_cost` is bounded by
   the refined graph-time expression.
3. Only after (1) and (2), promote
   `bmssp_path_family_charged_direct_insert_runtime_bigo_size_if_cost_bounded`
   from a conditional bridge to the JAR-facing non-vacuous path-family theorem.
