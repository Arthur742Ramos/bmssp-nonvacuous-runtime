# BMSSP Isabelle/HOL Formalization

This project formalizes the bounded multi-source shortest path (BMSSP)
algorithm behind the deterministic directed single-source shortest path
breakthrough of Duan, Mao, Mao, Shu, and Yin.

The paper is:

Ran Duan, Jiayi Mao, Xiao Mao, Xinkai Shu, and Longhui Yin,
*Breaking the Sorting Barrier for Directed Single-Source Shortest Paths*,
STOC 2025.

BMSSP is a recursive subproblem for shortest paths.  Instead of solving
single-source shortest paths in one global priority queue, it works with a
set of sources, an upper bound on the distances of interest, and a controlled
amount of work per recursive level.  The algorithm is designed so that its
partition data structure only needs to distinguish buckets of candidate
labels at the granularity required by the recursion.

The public result is split into five claims:

1. `bmssp_correct_strong` verifies functional correctness of the executable
   `bmssp_distances`: the output keys are distinct, the key set is exactly the
   reachable vertex set, and each returned distance is the semantic shortest
   distance.
2. `bmssp_runtime_bigo_target` formalizes a costed BMSSP recurrence and
   proves the `O(m * log^{2/3}(n))` bound under
   the abstract operation-cost interface.
3. `verified_bmssp_runtime_bigo_target` joins the cost bound and correctness on
   a single object: the running time bounded by claim 2 is, for all but
   finitely many sizes, the cost of a concrete BMSSP run that is proved
   `sssp_correct` on the whole vertex set. It is certified non-vacuous on two
   structurally different concrete graphs (`path_verified_runtime_bigo_target`,
   `star_verified_runtime_bigo_target`).
4. For the unbounded family of unit-weight directed paths `P_k` (edges `k`,
   vertices `k+1`), `path_size_cost_bigo_size` proves *unconditionally* that the
   closed BMSSP cost *expression* is `O(k * log^{2/3}(k))` in the true graph size
   `k`. The companion `bmssp_path_family_runtime_bigo_size` states the same bound
   for an actual exact-concrete run, but only *conditionally* on a `runs_exist`
   hypothesis — which `BMSSP_Cost_Totality` shows is **unsatisfiable for `P_k` at
   `k >= 2`**. The strong-version integration point is the checked theorem
   `bmssp_path_family_charged_direct_insert_runtime_bigo_size_if_cost_bounded`,
   which uses `charged_direct_insert_top_level_time` and assumes eventual
   charged run existence plus the still-pending charged runtime upper-bound
   chain. The reported runtime endpoint is
   `charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree`,
   still conditional on
   `charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N`.
   Until those assumptions are discharged, the non-vacuous path-family content
   remains the unconditional cost-expression floor. `path_k_bounded_instance`
   (locale inhabitation for every `k`, by a genuine inductive proof) and
   `path_family_not_forced_degenerate` remain true.
5. `bp_realises_partition_insert_cost_bound`,
   `bp_realises_partition_batch_cost_bound`, and
   `bp_realises_partition_pull_cost_bound` show that the bucketed partition
   operations realize the primitive costs required by that interface.

## Scope

The entry keeps the semantic BMSSP proof, the cost-model runtime proof, and
the executable correctness proof separate.  The public executable theorem
applies to finite natural weighted digraphs subject to
`nat_graph_well_formed G` and `src \<in> nat_graph_vertices G`; it does not
assume unique shortest paths.  The predicate `nat_graph_well_formed G` means
that the directed edge list has no duplicate edges and that
`nat_graph_total_weight G < bmssp_infinity`, the finite-infinity guard used by
the executable natural-number representation.  The public runtime theorem is
a theorem about the costed BMSSP recurrence under the abstract
partition-operation interface, not a machine-step theorem for generated SML.

The executable entry point is a finite natural-weight instantiation using the
bucketed work-list.  Its functional correctness is proved independently
against the shortest-path semantics.  The asymptotic result applies to the
costed BMSSP model and bucketed operation interface; the two layers share the
same partition primitives but are distinct artifacts.

The proof chain can be read as: finite graph semantics to BMSSP pre/post, then
FindPivots and recursive BMSSP correctness, then the abstract partition
interface, exact costed BMSSP recurrence, logarithmic parameter schedule,
bucketed partition primitive-cost realization, and finally executable natural
graph correctness.

## What Is Formalized

The development has four layers.

The first layer is an abstract correctness model.  It defines finite directed
graphs with non-negative real weights, shortest-path distances as minima over
simple walks, the BMSSP precondition, and the BMSSP postcondition.  This layer
does not commit to a concrete priority queue or partition data structure.

The second layer is the recursive BMSSP algorithm and its proof of
correctness.  The proof follows the paper's decomposition: base cases,
FindPivots, partition-loop pulls, recursive calls on bounded ranges, and final
assembly of completed vertices.

The third layer is a cost interface.  The recursive runtime proof only needs
abstract facts about Insert, BatchPrepend, and Pull.  The interface keeps the
algorithmic proof independent from the concrete data structure used later.

The fourth layer is the paper-faithful bucketed partition data structure.
It proves Insert at the paper-tight `O(log(N/M))` scale, BatchPrepend with
the matching amortised batch bound, and Pull at amortised `O(M)`.  These are
the primitive-cost facts used by the abstract recurrence theorem.

The entry also includes a concrete code-export theory.  Isabelle evaluates a
small graph during the build and proves that the computed distances match the
hand-computed expected result.

## Reviewer Pointers

For the shortest route through the final statements, start with
[`HEADLINE.md`](HEADLINE.md).  For the proof-chain and reproducibility trace,
use [`VERIFICATION.md`](VERIFICATION.md).

The BMSSP theories are checked by Isabelle/HOL under the imported HOL basis.
The final keyword sweep for unchecked proof placeholders and extra primitive
declarations is recorded in `VERIFICATION.md`.

## Important Theorems

The main theorem names most users will want are:

- `bmssp_correct_strong`

  The strongest executable correctness headline.  It states that
  `bmssp_distances` has distinct keys, exactly the reachable-vertex key set,
  and exact shortest-path distances for every returned pair.

- `bp_insert_cost_bound`

  The bucketed Insert operation satisfies the paper-tight logarithmic
  amortised bound in the ratio `N/M`.

- `bp_batch_prepend_cost_bound`

  The bucketed BatchPrepend operation satisfies the amortised batch bound used
  by the recursive partition loop.

- `bp_pull_cost_bound`

  The bucketed Pull operation satisfies the amortised linear-in-block-size
  bound `O(M)`.

- `bp_realises_partition_insert_cost_bound`

  The concrete bucketed Insert operation discharges the abstract Insert cost
  predicate.

- `bp_realises_partition_batch_cost_bound`

  The concrete bucketed BatchPrepend operation discharges the abstract
  BatchPrepend cost predicate.

- `bp_realises_partition_pull_cost_bound`

  The concrete bucketed Pull operation discharges the abstract Pull cost
  predicate.

- `bmssp_runtime_bigo_target`

  The cost-model runtime target for the abstract costed recurrence under the
  logarithmic parameter schedule.  This is not an end-to-end machine-step
  statement for the generated executable.

- `bmssp_path_family_charged_direct_insert_runtime_bigo_size_if_cost_bounded`

  The checked conditional bridge for the strong path-family runtime statement.
  It is ready to instantiate once charged direct-insert existence/totality and
  the runtime chain ending in
  `charged_direct_insert_top_level_cost_refined_bound_log_params_fixed_degree`
  are proved, including the remaining closed-bound premise
  `charged_direct_insert_closed_refined_bound_log_params_fixed_degree D N`; it
  is not itself a discharged non-vacuous path-family headline.

- `example_bmssp_correct`

  The executable smoke test.  The proof is by code evaluation and checks that
  `bmssp_distances example_graph 0` computes
  `[(0, 0), (1, 3), (2, 5), (3, 8), (4, 6)]`.

## Building

The entry builds with a stock **Isabelle2025-2** in which the `isabelle`
executable is on the `PATH`.  All commands are run from this entry's
directory (`projects/bmssp-isabelle`, the directory holding `ROOT`).

For a fast incremental proof check while editing:

```bash
isabelle build -o document=false -D . BMSSP_Correctness
```

For the normal AFP-facing session build (proofs and the document PDF):

```bash
isabelle build -D . BMSSP_Correctness
```

For a clean PDF readiness check that also collects the presentation output:

```bash
isabelle build -c -D . -P bmssp-pdf-out BMSSP_Correctness
```

The session exports SML code for the executable example.  To materialize it
on disk after a successful build, run:

```bash
isabelle build -e -o document=false -D . BMSSP_Correctness
```

The generated file is:

```text
projects/bmssp-isabelle/generated/BMSSP.ML
```

### Windows monorepo workspace

On the original Windows development host the bundled Isabelle is reached
through Cygwin Bash; the portable commands above are equivalent to, e.g.:

```powershell
& 'Q:\src\isabelle-borel-determinacy\toolchain\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc '/cygdrive/q/src/isabelle-borel-determinacy/toolchain/Isabelle2025-2/bin/isabelle build -D /cygdrive/q/src/isabelle-afp-monorepo/projects/bmssp-isabelle BMSSP_Correctness'
```

The executable smoke test prints the checked distance map:

```text
[(0, 0), (1, 3), (2, 5), (3, 8), (4, 6)]
```

## Session Structure

The Isabelle session is `BMSSP_Correctness`.  Its parent is `HOL`, and it
imports `HOL-Library`.  The session builds the abstract graph
model, the recursive correctness proof, the abstract and concrete cost layers, the
bucketed partition refinement, the headline runtime theorem, and the
executable export theory.

The session contains `BMSSP_Partition_Data_Structure.thy`, a baseline
sorted-list model of the abstract partition interface used by the exact
recurrence and abstraction proofs.  It is not the paper-faithful bucketed
implementation.  The bucketed structure in `BMSSP_Bucketed_Partition.thy` is
the data structure connected to the ratio-log operation-cost story.

## Theory Guide

### `BMSSP_Correctness.thy`

This is the entry point for the mathematical problem.  It defines the
`bound` datatype, finite weighted directed graphs, walks, simple walks,
reachability, shortest-path distances, and the BMSSP pre/postcondition.  The
locale `finite_weighted_digraph` is the abstract graph context used by the
rest of the development.

### `BMSSP_Shortest_Path_Lemmas.thy`

This file develops reusable shortest-path facts over the abstract graph
model.  It isolates the graph-theoretic lemmas needed later by FindPivots,
partition-loop assembly, and the executable refinement layer.

### `BMSSP_Initialization.thy`

This file proves that the top-level SSSP call can be initialized as a BMSSP
problem.  It connects the source vertex, the initial labels, and the
unbounded top-level distance threshold.

### `BMSSP_Unique_Shortest_Tree.thy`

This theory adds the unique-shortest-path setting used by the algorithmic
correctness layer.  It packages the assumptions under which shortest paths
form the tree-like structure exploited by the recursive proof.

### `BMSSP_Find_Pivots_Core.thy`

This is the lower-level library for the FindPivots subroutine.  It defines
the core reachability and label sets from which the capped pivot selection
theory is built.

### `BMSSP_Find_Pivots.thy`

This file formalizes the FindPivots step.  FindPivots is the subroutine that
selects a bounded set of pivots and advances labels enough to keep the
recursion balanced.  It is one of the main places where the parameter
schedule interacts with graph reachability.

### `BMSSP_Algorithm_Correctness.thy`

This theory states the abstract BMSSP step and proves the main abstract
correctness theorem.  It explains how a recursive call, a pivot set, a
partition-loop trace, and final assembly together imply the BMSSP
postcondition.

### `BMSSP_Partition_Interface.thy`

This is the abstraction boundary for the partition data structure.  It
defines partition views, Insert, BatchPrepend, Pull contracts, and the
abstract cost predicates used by the runtime proof.  The headline proof
depends on this interface, not on a particular implementation.

### `BMSSP_Partition_Data_Structure.thy`

This is the baseline sorted-list model of the abstract interface.  It remains
in the active session because later exact-cost and recurrence proofs use its
abstraction relation and operation facts.  It is not the executable data
structure for the paper-faithful bucketed cost result, because sorted-list
Insert gives a `log N` search scale rather than the required `log(N/M)` bucket
ratio.

### `BMSSP_Pull_Minimum.thy`

This theory proves facts about minimum extraction and Pull-style separation.
It supports both the abstract partition interface and the later operational
pull bridge.

### `BMSSP_Partition_Pull_Bridge.thy`

This file connects Pull specifications to the partition-loop proof shape.
It packages the conditions under which a pulled set separates the next
recursive range from the remaining candidates.

### `BMSSP_Concrete_Step.thy`

This theory replaces an abstract one-step postcondition by a concrete trace
of partition-loop ranges.  It is the bridge from the paper's recursive
description to an Isabelle induction over explicit child ranges.

### `BMSSP_Concrete_Top_Level.thy`

This file proves the top-level correctness consequences of the concrete
one-step formulation.  It keeps the correctness theorem independent from the
later cost accounting.

### `BMSSP_Base_Case.thy`

This theory handles the base case of the recursive algorithm.  It uses a
bounded extraction order to show that the base case completes the vertices it
is supposed to complete.

### `BMSSP_Recursive.thy`

This file packages the recursive BMSSP correctness theorem.  It connects the
base case and the recursive step into the final abstract recursive run.

### `BMSSP_Operational_Pull.thy`

This theory gives a more operational account of Pull for the partition loop.
It is used to align the abstract Pull contract with the concrete trace used
by the costed recursion.

### `BMSSP_Complexity.thy`

This is the base complexity library.  It defines the logarithmic parameter
schedule and elementary bounds that are reused by the costed range and
top-level theories.

### `BMSSP_Range_Costed.thy`

This theory introduces costed range recursion.  It tracks the work spent on
recursive ranges before the exact partition costs are plugged in.

### `BMSSP_Exact_Range_Costed.thy`

This file refines the range-cost accounting.  It makes the child-cost and
range-cost decomposition precise enough for the final recurrence.

### `BMSSP_Direct_Insert_Costed.thy`

This theory separates the partition loop's direct inserts from the batches
that are prepended into the next block.  That distinction is essential for
using the abstract Insert and BatchPrepend cost predicates correctly.

### `BMSSP_Exact_Concrete_Cost.thy`

This file combines the concrete recursive correctness story with the exact
cost accounting.  It is one of the final bridges between the algorithmic
proof and the asymptotic top-level theorem.

### `BMSSP_Strict_Tie_Breaking.thy`

This theory develops the strict tie-breaking assumptions used by the unique
shortest-path proof layer.  It prepares the graph for a clean recursive
correctness argument.

### `BMSSP_Top_Level_Bounds.thy`

This is the headline runtime theory.  It instantiates the logarithmic
schedule and proves `bmssp_runtime_bigo_target`, the
asymptotic target for the abstract costed recurrence.

### `BMSSP_Bucketed_Partition.thy`

This is the paper-faithful bucketed partition refinement.  It defines the
bucketed state, invariants, Insert, BatchPrepend, Pull, costed operations,
potential function, and the three primary paper-tight bounds:
`bp_insert_cost_bound`, `bp_batch_prepend_cost_bound`, and
`bp_pull_cost_bound`.

### `BMSSP_Code_Export.thy`

This theory gives the executable demonstration.  It instantiates a concrete
graph type with natural-number vertices and weights, defines
`bmssp_distances`, proves `example_bmssp_correct` by evaluation, prints the
example result with `value`, and exports SML code.

### `BMSSP_Executable_Base_Case.thy`

This file bridges the abstract base-case reasoning to the executable
natural-graph setting.

### `BMSSP_Executable_Refinement.thy`

This theory is the public import point for the executable refinement layer.
The long proof is kept in `BMSSP_Executable_Refinement_Internal.thy`; this
wrapper re-exports `bmssp_correct_executable` and the distinct-key fact used by
the stronger public theorem.

### `BMSSP_Executable_Headline.thy`

This is the reader-facing executable correctness wrapper.  Its theorem
`bmssp_correct_strong` exposes distinct keys, the exact reachable-vertex key
set, and exact distances.

### `BMSSP_Runtime_Instance.thy`

This theory certifies that the runtime headline is not vacuous.  It interprets
the `bounded_reduced_positive_instance` locale on a concrete unit-weight
directed path `0 -> 1 -> 2 -> 3` (discharging unique shortest walks via the
verified simple-walk enumerator, positive weights, full reachability, and
bounded outdegree) and re-exports the resulting closed, assumption-free
running-time bound as `path_runtime_bigo_target`.

## Executable Example

The example graph in `BMSSP_Code_Export.thy` has vertices `0` through `4`.
The source is `0`, and the graph includes direct and indirect paths that
exercise the bucketed work-list operations.

The expected distances are:

```text
d(0) = 0
d(1) = 3
d(2) = 5
d(3) = 8
d(4) = 6
```

The theorem

```isabelle
lemma example_bmssp_correct:
  "bmssp_distances example_graph 0 = example_expected_dist"
  by eval
```

is deliberately proved by executable evaluation.  During the Isabelle build,
Poly/ML evaluates the generated code equations for the concrete example and
checks that the result is the hand-computed distance map.

## Notes for Maintainers

Do not use the baseline sorted-list `partition_state` as evidence for the
paper-tight bucketed runtime claim.  The sorted-list model is active proof
infrastructure for exact recurrence and abstraction facts, but it does not
realize the paper's `log(N/M)` Insert scale.

The bucketed refinement is the authoritative concrete data structure for the
cost-interface result.  In particular, preserve these theorem statements:

```text
bp_insert_cost_bound
bp_batch_prepend_cost_bound
bp_pull_cost_bound
bp_realises_partition_insert_cost_bound
bp_realises_partition_batch_cost_bound
bp_realises_partition_pull_cost_bound
bmssp_runtime_bigo_target
example_bmssp_correct
bmssp_correct_strong
```

When editing documentation antiquotations or proof text, run the full session
build.  Isabelle checks theory text antiquotations during the build, so a
broken theorem reference is a real build failure.

When editing generated-code-facing definitions, also run the export command
with `-e` and confirm that `generated/BMSSP.ML` is still regenerated.
