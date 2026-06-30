# BMSSP in Isabelle/HOL — an unconditional, non‑vacuous size‑parametric runtime bound

A machine‑checked Isabelle/HOL development of **BMSSP** (the *Bounded Multi‑Source
Shortest Path* recurrence behind recent sub‑sorting‑barrier SSSP work), culminating
in a **fully unconditional, non‑vacuous, size‑parametric running‑time theorem** for an
unbounded graph family.

> Every theorem here is checked by the Isabelle kernel. There is **no `sorry`, no
> `oops`, no `axiomatization`**, and the session does **not** enable `quick_and_dirty`
> or `skip_proofs` — so a green build is a real proof.

---

## The headline result

```isabelle
theorem path_nonvac_runtime_bigo_card_V_unconditional:
  "(λn. real (path_nonvac_time n))
     ∈ O(λn. real (card (path_k_V n))
            * (ln (real (card (path_k_V n)) + 2)) powr (2/3))"
```

*(`BMSSP_NonVacuous_Family.thy`)*

**In words.** Let `P_n` be the unit‑weight directed path on vertices `0 → 1 → … → n`
(so `card V = n + 1` and `card E = n`, both growing without bound). Running the costed
**charged BMSSP** loop on `P_n` at a suitably *inflated* schedule, the running time is

```
    O( |V| · (ln |V|)^(2/3) )
```

measured in the **genuine graph size** `|V|`. The bound has **no hypotheses**.

This is the size‑parametric statement that was previously only available
*conditionally* (it assumed both run‑existence and a closed cost bound). Both premises
are now discharged.

---

## Why it is non‑vacuous

A size‑parametric `O(...)` statement is worthless if the object it bounds never exists
or the family is finite. All four escape hatches are closed **in the proof**:

| Risk | Ruled out by |
|---|---|
| Finite / bounded family | `path_card_V_at_top`: `card (path_k_V n) ⟶ ∞` |
| No run exists (bound is empty) | `eventually_path_nonvac_charged_cost_exists`: a charged top‑level run exists **eventually, unconditionally** |
| The "regime" is secretly `False` | `eventually_inflated_pivot_regime`: `eventually (2 ≤ p(n²) ≤ n ∧ Suc n ≤ cap(n²))` — the bucket cap really covers the path |
| Bounded quantity is a junk default | `path_nonvac_time n` is the **least** charged cost; since a run provably exists, that least is realised by an actual run |

So the bounded quantity is the cost of a *genuine* charged run, on a family whose size
tends to infinity.

---

## Honest scope

This development is careful about what is and isn't claimed:

- The bound is on the **least charged cost** of the decoupled family — the honest,
  witnessed quantity (existence is proved, so the least is a real run's cost).
- It is a theorem about the **charged operation‑cost model** of the BMSSP recurrence,
  **not** a machine‑step bound for exported SML, and not a claim about a specific
  hardware execution.
- The path family is genuinely sparse, so a key part of the work was proving that a
  complete charged run *exists at all* (the naïve single‑pivot loop cannot walk the
  path; see the proof architecture below).

See [`HEADLINE.md`](HEADLINE.md) for the full statement of every public claim in the
broader BMSSP entry, and [`VERIFICATION.md`](VERIFICATION.md) for the proof‑hygiene
sweep.

---

## Verification

- **Hole‑free.** No `sorry` / `oops` / `axiomatization` / `consts` in any theory.
- **No shortcuts.** `ROOT` sets only `[document = pdf, timeout = 600]` — no
  `quick_and_dirty`, no `skip_proofs`.
- **Builds from clean**, proofs **and** the PDF document, in one command.

### Reproduce it

Requires **Isabelle2025‑2** (with the bundled `HOL-Library`).

```bash
# from the repository root
isabelle build -D .
```

A successful run ends with `Finished BMSSP_Correctness` and exit code `0`. To force a
full clean rebuild (no cached heaps):

```bash
isabelle build -c -D .
```

The pre‑built document is included as
[`BMSSP_Correctness.pdf`](BMSSP_Correctness.pdf), and the exported reference code lives
under [`generated/`](generated).

---

## Proof architecture

The unconditional headline is assembled in three milestones inside
[`BMSSP_NonVacuous_Family.thy`](BMSSP_NonVacuous_Family.thy):

- **B1 — existence (unconditional).** The thin path defeats the naïve loop‑walk
  (`split_below d {0} β ⊆ {0}` — only the source is ever pulled). Run‑existence is
  recovered via the *inflated / dominating schedule* regime (`p > Suc k`), where the
  bucket cap covers the whole path and a genuine terminating charged run exists.
  Result: `eventually_path_nonvac_charged_cost_exists` — **no assumptions**.

- **B2 — cost (the cheap‑run route).** The headline bounds the *least*‑cost run, so it
  does **not** need the (in fact false) universal `closed_bound`. Instead the proof
  exhibits one specific **cheap** charged run and bounds its cost by the refined
  graph‑time budget — i.e. polylog in the graph size
  (`path_k_charged_cheap_imp_nonvac_time_le_bound`).

- **B3 — assembly.** B1 + B2 discharge both premises of the conditional headline,
  collapsing it to `path_nonvac_runtime_bigo_card_V_unconditional`.

---

## Repository layout

| Path | What it is |
|---|---|
| [`BMSSP_NonVacuous_Family.thy`](BMSSP_NonVacuous_Family.thy) | **The new result** — B1/B2/B3 and the unconditional headline |
| [`BMSSP_Path_Family.thy`](BMSSP_Path_Family.thy) | The path family `P_k`, its locale membership, and the conditional bridges |
| [`BMSSP_Cost_Totality.thy`](BMSSP_Cost_Totality.thy) | Charged totality / amortised cost infrastructure |
| [`BMSSP_Complexity.thy`](BMSSP_Complexity.thy) | The logarithmic schedule, level caps, and `O(...)` machinery |
| [`BMSSP_Top_Level_Bounds.thy`](BMSSP_Top_Level_Bounds.thy) | Top‑level cost relations and `source_pivot_finishes` |
| [`BMSSP_Executable_Headline.thy`](BMSSP_Executable_Headline.thy) | Executable correctness of `bmssp_distances` |
| [`HEADLINE.md`](HEADLINE.md) | All public claims of the entry, precisely stated |
| [`VERIFICATION.md`](VERIFICATION.md) | Proof‑hygiene audit |
| [`BMSSP_ENTRY_README.md`](BMSSP_ENTRY_README.md) | Original entry overview |
| [`ROOT`](ROOT) | The `BMSSP_Correctness` Isabelle session |
| `document/` | LaTeX sources for the generated PDF |

(36 theory files in total; the session imports only `HOL` + `HOL-Library`.)

---

## License

See [`LICENSE`](LICENSE). The BMSSP development is released for reuse under the terms
stated there.

---

## Credits

Formalised in Isabelle/HOL by **Arthur742Ramos**, with autonomous proof engineering
driven by the GitHub Copilot CLI (Claude Opus 4.8, maximum reasoning effort). The
final non‑vacuous headline — breaking the thin‑path obstruction via the inflated
schedule and the cheap‑run cost bound — was developed and machine‑checked end‑to‑end.

Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>
