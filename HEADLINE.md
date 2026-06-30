# BMSSP Headline Theorems

This document indexes the public statements a reviewer should use when
checking the BMSSP entry.  The headline covers five checked surfaces:
executable correctness, cost-model runtime, a verified-correct-run runtime
bound that joins the two, the path-family cost-expression floor with
conditional runtime bridges, and the bucketed operation-cost interface.

> **TL;DR.** `bmssp_correct_strong` proves that the executable
> `bmssp_distances` returns the exact reachable shortest-distance map.
> The costed BMSSP recurrence is proved within the abstract
> operation-cost model, and the bucketed partition is proved to realize the
> primitive costs used by that model.  `verified_bmssp_runtime_bigo_target`
> then joins cost and correctness on one object: the `O(m * log^{2/3} n)`
> running time bounded by the headline is, eventually, the cost of a concrete
> run proved to compute exact shortest-path distances.  There is no theorem
> claiming that the one-vertex-per-pull executable reference implementation
> itself runs in the asymptotic bound.

We verify functional correctness of the executable `bmssp_distances`.
Separately, we formalize a costed BMSSP recurrence and prove the
`O(m * log^{2/3}(n))` bound under the abstract operation-cost interface,
then show that the bucketed partition operations realize the required
primitive costs.

---

## 1. Scope

The entry deliberately keeps three claims separate.  The semantic BMSSP
development proves the bounded recursive correctness obligations over finite
weighted digraphs.  The runtime development proves a cost-model theorem for
the abstract BMSSP recurrence and partition-operation interface.  The
executable development proves functional correctness of `bmssp_distances` for
finite natural weighted graphs subject to `nat_graph_well_formed G` and
`src \<in> nat_graph_vertices G`.  Here `nat_graph_well_formed G` is the
representation-side condition that edges are not duplicated and that the
total natural edge weight is below the executable sentinel `bmssp_infinity`.

The executable headline is not derived from a generated-code machine-step
bound, and the runtime headline is not stated as a theorem about SML execution
time.  The two layers share BMSSP and partition primitives, but they remain
separate checked artifacts.

The proof chain is:

```text
finite graph semantics
  -> BMSSP pre/post
  -> FindPivots + recursive BMSSP correctness
  -> abstract partition interface
  -> exact costed BMSSP recurrence
  -> logarithmic parameter schedule
  -> bucketed partition realizes operation costs
  -> executable natural graph correctness
```

---

## 2. Claim 1: Executable Correctness

### `bmssp_correct_strong`

**File:** [`BMSSP_Executable_Headline.thy`](BMSSP_Executable_Headline.thy)

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

**Meaning.** For every well-formed finite natural graph and source vertex,
the executable association list has distinct keys, those keys are exactly the
reachable vertices, and every stored natural distance is the semantic
shortest-path distance after coercion to `real`.  This theorem has no
unique-shortest-path or tie-breaking hypothesis beyond the displayed
well-formedness and source-membership assumptions.

The proof of `bmssp_correct_strong` is assembled from these facts:

| Fact | Role |
|---|---|
| `bmssp_distances_distinct_keys` | output keys are distinct |
| `bmssp_distances_output_reachable` | every output key is reachable |
| `bmssp_distances_keys_subset_carrier` | every output key is a graph vertex |
| `BMSSP_Executable_Refinement.bmssp_correct_executable(1)` | every output distance is exact |
| `BMSSP_Executable_Refinement.bmssp_correct_executable(2)` | every reachable vertex appears |

---

## 3. Claim 2: Cost-Model Runtime

### `bmssp_runtime_bigo_target`

**File:** [`BMSSP_Top_Level_Bounds.thy`](BMSSP_Top_Level_Bounds.thy)

This is the main asymptotic theorem for the costed BMSSP recurrence under the
abstract operation-cost interface and logarithmic parameter schedule.  Its
closed assumption-free presentation is inside the runtime locale; interpreting
that locale supplies the reduced positive instance, reachability, and bounded
outdegree hypotheses.

The runtime theorem is about `T_bmssp` and related costed recurrence
quantities.  It is not a theorem about the machine steps taken by exported
SML code for `bmssp_distances`.

---

## 3a. Claim 2b: Runtime Bound for a Verified-Correct Run

### `verified_bmssp_runtime_bigo_target`

**File:** [`BMSSP_Verified_Runtime.thy`](BMSSP_Verified_Runtime.thy)

Claim 2 bounds `T_bmssp D N`, the *least* cost over valid runs; as an integer
it carries no evidence that the run achieving it computes shortest paths.  This
theorem closes that gap.  In the asymptotic runtime locale it proves the
conjunction

```isabelle
(\<lambda>n. real (T_bmssp n)) \<in> O(\<lambda>n. real (m n) * (ln (real n + 2)) powr (2/3))
\<and>
eventually (\<lambda>N. \<exists>d' U.
    exact_concrete_top_level_run D N d' U (T_bmssp N) \<and>
    U = V \<and> sssp_correct d') at_top
```

The first conjunct is the headline `O(m * log^{2/3} n)` bound.  The second
states that, for all but finitely many sizes, the bounded running time
`T_bmssp N` is realised by an actual concrete BMSSP run whose output label is
`sssp_correct` (exact single-source shortest-path distances) and whose
completed set is the whole vertex set `V`.  The bridge rests on the per-run
theorem `exact_concrete_top_level_run_correct_and_refined_bound_log_params_fixed_degree`
together with `exact_concrete_top_level_time_witness`, which exhibits the
least cost as a genuine run.

The supporting in-locale facts are `T_bmssp_realised_by_verified_run` and
`eventually_T_bmssp_realised_by_verified_run`.  The bound is certified
non-vacuous on two structurally different concrete graphs:
`path_verified_runtime_bigo_target` (the directed path `0 -> 1 -> 2 -> 3`, in
[`BMSSP_Runtime_Instance.thy`](BMSSP_Runtime_Instance.thy)) and
`star_verified_runtime_bigo_target` (the out-star `1 <- 0 -> 2` with
outdegree two, in
[`BMSSP_Runtime_Instance_Branching.thy`](BMSSP_Runtime_Instance_Branching.thy)).

---

## 3b. Claim 2c: Size-Parametric Runtime Bound (graph size as the variable)

### `path_size_cost_bigo_size`, `bmssp_path_family_runtime_bigo_size`, and the charged bridge

**File:** [`BMSSP_Path_Family.thy`](BMSSP_Path_Family.thy)

Claims 2 and 2b state the `O(m * log^{2/3} n)` bound for a graph *fixed* by the
runtime locale; the asymptotic variable there drives the internal logarithmic
schedule, and the edge factor is a constant of the fixed graph.  This claim
removes that limitation by introducing an unbounded family of graphs — the
unit-weight directed paths `P_k` on vertices `0..k` with edges `i -> i+1`, so
`card (E_k) = k` and `card (V_k) = k+1` both grow with `k`.

- `path_size_cost_bigo_size` (UNCONDITIONAL, genuinely true): the closed BMSSP
  cost *expression* on `P_k`, with the graph cardinalities substituted, is in
  `O(k * (ln k)^{2/3})` where `k` is the genuine graph size. This is arithmetic
  about the cost formula and carries no run-existence assumption.
- `bmssp_path_family_runtime_bigo_size` (CONDITIONAL — and VACUOUS for this
  family): the same bound for the *running time of an actual run*
  `path_T_bmssp k`, under a hypothesis `runs_exist`. **That hypothesis is
  provably unsatisfiable for `P_k` at every `k >= 2`** (see the obstruction
  below), so this theorem — though logically valid — is witnessed by no run and
  must NOT be read as "the algorithm meets the bound on the path family."
- `path_k_bounded_instance`: `P_k` inhabits the runtime locale
  `bounded_reduced_positive_instance` for *every* `k`, proved by a genuine
  inductive unique-shortest-walk argument (not code evaluation). This is about
  *locale membership*, and remains true; it does not imply a run exists.
- `path_family_not_forced_degenerate`: the empty-pivot no-op regime is escaped
  at schedule `N := k` — which, combined with the obstruction below, is exactly
  *why* no complete run exists (the loop is forced into a genuine step it cannot
  complete).
- `bmssp_path_family_charged_direct_insert_runtime_bigo_size_if_cost_bounded`
  (CONDITIONAL bridge — now **discharged**; see §3c): the parallel statement for
  `charged_direct_insert_top_level_time`.  It replaces the exact-concrete
  `runs_exist` premise with eventual existence of
  `charged_direct_insert_top_level_cost`, but it also honestly assumes the
  missing charged cost upper bound for every realised charged run.  The runtime
  branch reports the intended bound theorem as
  `charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree`,
  still conditional on
  `charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N`. This
  is the integration point for the strong BMSSP branches; it is not a
  non-vacuous final path-family theorem until charged totality/existence and
  the closed-bound runtime fact discharge those premises.

### The obstruction (`BMSSP_Cost_Totality.thy`)

`exact_concrete_step_forces_empty_prefix` and
`no_genuine_exact_concrete_step_at_positive_lower_bound` machine-check that,
under a sound label, a genuine exact-concrete loop step is forced to lower bound
zero (the step rule equates the child output with the *incremental* range tree,
while child correctness pins it to the *cumulative* bounded tree). So the loop
takes at most one genuine step. A complete top-level run must terminate in the
`Done` case with output bound `Infinity`; one step's truncating base case
settles only a `k`-bounded prefix of the path, stranding the rest. Hence **no
complete top-level run exists on `P_k` for `k >= 2`**, and `runs_exist` cannot
be discharged for the path family. This is a defect of the exact-concrete
relation's over-rigid step rule (the operational loop, which leaves the child
output free, does not suffer it); closing it changes the cost relation the whole
runtime development depends on.

Bottom line for this claim. Two facts coexist and must not be conflated:
**(i)** the *exact-concrete* algorithm-level bound at the *coupled* schedule `N := k`
(`bmssp_path_family_runtime_bigo_size`) is **vacuous** on `P_k` — its `runs_exist`
premise is provably unsatisfiable (the obstruction above), and it is retained only as
an honest record; **(ii)** the *charged* relation at a *decoupled, inflated* schedule
**does** admit a genuine complete run and yields a fully **unconditional, non-vacuous**
size-parametric headline — see §3c, which discharges the charged bridge of the bullet
above. These are different objects (exact-concrete/coupled vs charged/decoupled); the
obstruction is specific to the exact-concrete relation at the coupled schedule and does
not touch §3c.

---

## 3c. Claim 2d: Unconditional non-vacuous size-parametric runtime headline (discharged)

**File:** [`BMSSP_NonVacuous_Family.thy`](BMSSP_NonVacuous_Family.thy)

This is the discharged, genuinely non-vacuous size-parametric headline. It runs the
*charged* direct-insert loop on the path family `P_n` at a **decoupled, inflated**
schedule index `n * n` — rather than the coupled `N := k` of §3b, where the bucket cap
is sub-linear in `k` so no run completes. At the inflated schedule the cap covers the
whole path, so a genuine complete charged run exists.

```isabelle
theorem path_nonvac_runtime_bigo_card_V_unconditional:
  "(λn. real (path_nonvac_time n))
     ∈ O(λn. real (card (path_k_V n))
            * (ln (real (card (path_k_V n)) + 2)) powr (2/3))"
```

with `path_nonvac_time n = charged_direct_insert_top_level_time (P_n) 0 1 (n * n)`.
The bound has **no hypotheses**, and it is non-vacuous in this precise sense:

| Vacuity risk | Closed by (in `BMSSP_NonVacuous_Family.thy`) |
|---|---|
| Finite/bounded family | `path_card_V_at_top` — `card (path_k_V n) ⟶ ∞` |
| No run exists (bound empty) | `eventually_path_nonvac_charged_cost_exists` — a charged top-level run exists eventually, **unconditionally** |
| Regime secretly `False` | `eventually_inflated_pivot_regime` — `eventually (2 ≤ p(n²) ≤ n ∧ Suc n ≤ cap(n²))` |
| Bounded quantity a junk default | `path_nonvac_time` is the *least* charged cost; existence makes it a real run's cost |

The two premises of the §3b bridge are discharged as follows.
- **Run-existence (B1):** recovered via the inflated/dominating-schedule regime; the
  single-pivot loop-walk obstruction (`split_below d {0} β ⊆ {0}`) is routed around
  because the cap now covers the path. Result: `eventually_path_nonvac_charged_cost_exists`
  (no assumptions).
- **Cost (B2):** because the headline bounds the *least*-cost run, it is discharged by
  bounding one specific **cheap** charged run
  (`path_k_charged_cheap_imp_nonvac_time_le_bound`). The universal `closed_bound` over
  *all* runs is in fact false on this family and is deliberately **not** used.

---

## 4. Claim 3: Bucketed Operation-Cost Interface

### Bucketed realization facts

**File:** [`BMSSP_Bucketed_Partition_Internal.thy`](BMSSP_Bucketed_Partition_Internal.thy)

These corollaries package the concrete bucketed bounds for Insert,
BatchPrepend, and Pull into the abstract predicates used by the recurrence
theorem:

- `bp_realises_partition_insert_cost_bound`
- `bp_realises_partition_batch_cost_bound`
- `bp_realises_partition_pull_cost_bound`

The supporting primitive bounds are:

- `bp_insert_cost_bound`
- `bp_batch_prepend_cost_bound`
- `bp_pull_cost_bound`

---

## 5. Executable Surface

The executable entry point is a finite natural-weight instantiation using the
bucketed work-list.  Its functional correctness is proved independently
against the shortest-path semantics.  The asymptotic result applies to the
costed BMSSP model and bucketed operation interface; the two layers share the
same partition primitives but are distinct artifacts.

The executable smoke test is `example_bmssp_correct` in
[`BMSSP_Code_Export.thy`](BMSSP_Code_Export.thy).  It checks by evaluation
that `bmssp_distances example_graph 0` computes
`[(0, 0), (1, 3), (2, 5), (3, 8), (4, 6)]`.

---

## 6. Executable Correctness Sites

The public headline theorem is `bmssp_correct_strong`; the executable
refinement layer also exports the lower-level two-clause theorem used in its
proof:

| File | Role |
|---|---|
| `BMSSP_Executable_Headline.thy` | reader-facing exact shortest-distance map theorem |
| `BMSSP_Executable_Refinement.thy` | exported `bmssp_correct_executable` refinement theorem |

---

## 7. Build and Audit

The whole session is built by:

```bash
isabelle build -D . BMSSP_Correctness
```

The proof-hygiene sweep is recorded in [`VERIFICATION.md`](VERIFICATION.md).
It checks that the BMSSP theories contain no unchecked proof placeholders and
no extra primitive declarations beyond the imported HOL basis.
