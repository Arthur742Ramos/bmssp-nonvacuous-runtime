# Reviewer's guide

This document is for a reviewer who wants to check this development quickly and
adversarially. It says **what is proved, exactly where, what is and isn't assumed, how
to verify it in one command, and what is deliberately *not* claimed.**

---

## 1. What to check in five minutes

```bash
# 1. There are no proof holes anywhere in the session:
grep -rnwE 'sorry|oops|axiomatization|consts' *.thy        # expect: no matches

# 2. The build is not run in a permissive mode:
grep -nE 'quick_and_dirty|skip_proofs' ROOT *.thy          # expect: no matches

# 3. The kernel checks everything, from clean, proofs + document:
isabelle build -c -D .                                      # expect: Finished BMSSP_Correctness, exit 0
```

The session imports only `HOL` and `HOL-Library` (see [`ROOT`](ROOT)); there is no
external AFP dependency and nothing is added to the trusted base. Because `ROOT` sets
no `quick_and_dirty`/`skip_proofs`, a successful build is a genuine kernel check — a
stray `sorry` would make the build fail, not pass.

Continuous integration runs the same check on every push
([`.github/workflows/build.yml`](.github/workflows/build.yml), proofs only, no LaTeX).

---

## 2. The headline theorem (and why it is non-vacuous)

**File:** [`BMSSP_NonVacuous_Family.thy`](BMSSP_NonVacuous_Family.thy)

```isabelle
theorem path_nonvac_runtime_bigo_card_V_unconditional:
  "(λn. real (path_nonvac_time n))
     ∈ O(λn. real (card (path_k_V n))
            * (ln (real (card (path_k_V n)) + 2)) powr (2/3))"
```

`path_nonvac_time n` is the **charged direct-insert top-level running time** of the
unit-weight directed path `P_n` (vertices `0..n`, edges `i -> i+1`) run at schedule
index `n * n`. The statement has **no `assumes`**.

A size-parametric `O(...)` bound is only meaningful if the bounded object exists and
the family is infinite. Each escape hatch is closed by a named, checked fact:

| Could the bound be vacuous because… | Ruled out by | Statement |
|---|---|---|
| …the family is finite? | `path_card_V_at_top` | `filterlim (λn. card (path_k_V n)) at_top at_top` |
| …no run exists, so the cost is undefined/empty? | `eventually_path_nonvac_charged_cost_exists` | `eventually (λn. ∃c. charged_…_top_level_cost (P_n) 0 1 (n*n) c) at_top` — **no assumptions** |
| …the "regime" predicate is secretly `False`? | `eventually_inflated_pivot_regime` | `eventually (λn. 2 ≤ p(n²) ∧ p(n²) ≤ n ∧ Suc n ≤ cap(n²)) at_top` |
| …`path_nonvac_time` is a junk default when no run exists? | it is the **least** charged cost, and existence (row 2) makes that least a real run's cost | — |

So the bounded quantity is the cost of a *genuine* charged run, on a family whose
vertex count tends to infinity, with the bound stated in the real graph size.

To audit the proof yourself, read the final `proof` of
`path_nonvac_runtime_bigo_card_V_unconditional` and its two feeders:
`eventually_inflated_pivot_regime` and `path_k_charged_cheap_imp_nonvac_time_le_bound`.

---

## 3. The one subtlety a reviewer should not miss

The companion document [`HEADLINE.md`](HEADLINE.md) (§3b) records that an **earlier**
size-parametric statement is *vacuous*:

> `bmssp_path_family_runtime_bigo_size` — the **exact-concrete** relation at the
> **coupled** schedule `N := k` — is conditional on `runs_exist`, and `runs_exist` is
> **provably unsatisfiable** on `P_k` for `k ≥ 2` (the obstruction in
> `BMSSP_Cost_Totality.thy`).

This is **still true and is not contradicted** by §2 above. The headline of §2 is a
**different object**:

| | §3b vacuous bound | §2 unconditional headline |
|---|---|---|
| Cost relation | exact-concrete | **charged** |
| Schedule | coupled, `N := k` | **decoupled, inflated `n·n`** |
| Bucket cap vs path | cap is sub-linear ⇒ no run completes | cap covers the path ⇒ **run exists** |
| Status | conditional, vacuous (honest record) | **unconditional, non-vacuous** |

The obstruction is specific to the over-rigid exact-concrete step rule at the coupled
schedule. The charged relation at the inflated schedule leaves the child output free and
admits a genuine complete run — which is what makes §2 non-vacuous. Both facts are kept
in the repository on purpose, clearly separated.

---

## 4. The rest of the entry (also proved here)

This repository is the **complete** `BMSSP_Correctness` session (36 theories, ~1,800
checked facts), not just the new theorem. The other reader-facing claims:

| Claim | Theorem | File |
|---|---|---|
| Executable correctness (exact shortest-distance map) | `bmssp_correct_strong` | [`BMSSP_Executable_Headline.thy`](BMSSP_Executable_Headline.thy) |
| Cost-model runtime `O(m·log^{2/3} n)` (costed recurrence) | `bmssp_runtime_bigo_target` | [`BMSSP_Top_Level_Bounds.thy`](BMSSP_Top_Level_Bounds.thy) |
| Verified-correct-run runtime (cost + correctness on one run) | `verified_bmssp_runtime_bigo_target` | [`BMSSP_Verified_Runtime.thy`](BMSSP_Verified_Runtime.thy) |
| Certified non-vacuous instances (directed path, out-star) | `path_verified_runtime_bigo_target`, `star_verified_runtime_bigo_target` | [`BMSSP_Runtime_Instance.thy`](BMSSP_Runtime_Instance.thy), [`BMSSP_Runtime_Instance_Branching.thy`](BMSSP_Runtime_Instance_Branching.thy) |
| Bucketed operation-cost realization (Insert/BatchPrepend/Pull) | `bp_realises_partition_*_cost_bound` | [`BMSSP_Bucketed_Partition_Internal.thy`](BMSSP_Bucketed_Partition_Internal.thy) |
| Machine-checked obstruction record | `exact_concrete_step_forces_empty_prefix` | [`BMSSP_Cost_Totality.thy`](BMSSP_Cost_Totality.thy) |
| **NEW: unconditional non-vacuous size-parametric headline** | `path_nonvac_runtime_bigo_card_V_unconditional` | [`BMSSP_NonVacuous_Family.thy`](BMSSP_NonVacuous_Family.thy) |

[`HEADLINE.md`](HEADLINE.md) states each of these precisely; [`VERIFICATION.md`](VERIFICATION.md)
is the proof-hygiene/assumption ledger.

---

## 5. Scope and limitations (what is *not* claimed)

- The runtime results are about the **charged operation-cost model** of the BMSSP
  recurrence. They are **not** machine-step bounds for the exported SML, and not claims
  about wall-clock time on hardware. The executable surface (`bmssp_correct_strong`) is
  a separate, functional-correctness artifact.
- The §2 headline bounds the **least** charged cost of the family — the honest,
  witnessed quantity. It is not a `∀`-runs bound; indeed the universal `closed_bound`
  is false on this family and is not used.
- The executable headline assumes only `nat_graph_well_formed G` and
  `src ∈ nat_graph_vertices G` (see the Assumption Ledger in `VERIFICATION.md`).

---

## 6. Reproducing the document

The PDF in [`BMSSP_Correctness.pdf`](BMSSP_Correctness.pdf) is produced by the same
build. To regenerate it (requires a LaTeX installation):

```bash
isabelle build -D .
```

To check proofs only (no LaTeX required), use `isabelle build -o document=false -D .`
— this is what CI runs.
