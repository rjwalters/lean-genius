# Knowledge Base: taxicab-number-oq-01

## Problem Summary

`Ta(2) = 1729` (Hardy–Ramanujan number): 1729 is the **smallest** positive
integer expressible as a sum of two positive cubes in two distinct ways:

    1729 = 1³ + 12³ = 9³ + 10³.

Fully finite and **decidable** — no infinitary content. The task is to formalize
the value + minimality and discharge by a bounded finite search.

---

## Insights

### Session 2026-06-16 (s01, researcher-1) — OBSERVE/ORIENT (build-gated)

**Mode**: fresh problem (EMPTY). **Backend state**: dual blackout — Aristotle MCP
`prove` → `Resource not found` (404, probed this session); Docker pool saturated
(13–14 concurrent `lean-build` peers on the 7.65 GiB VM, over the 2-container
safety threshold — building a 15th would OOM peers' work). No Lean compiled.
Deliverable is a grounded formalization design + a Python certificate, with a
build-pending scaffold for the next Docker-up session.

**Key tractability fact (the only real design point).** For any `n ≤ 1729`, a
representation `n = a³ + b³` with `1 ≤ a ≤ b` satisfies `b³ ≤ n ≤ 1729 < 2197 = 13³`,
so `a, b ≤ 12`. Therefore the search may be restricted to the `12 × 12` grid
`Finset.Icc 1 12 ×ˢ Finset.Icc 1 12` for *every* `n ≤ 1729` simultaneously — this
keeps the decidable instance small (~144 filtered pairs per `n`, ~250k total over
the minimality range) instead of an `n`-dependent unbounded search.

**Formalization (scaffold in `proofs/Proofs/TaxicabNumberOQ01.lean`, UNregistered):**

```lean
def reps (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 12 ×ˢ Finset.Icc 1 12).filter
    (fun p => p.1 ≤ p.2 ∧ p.1 ^ 3 + p.2 ^ 3 = n)

theorem card_reps_1729 : (reps 1729).card = 2 := by decide
theorem minimal_below_1729 : ∀ m < 1729, (reps m).card < 2 := by decide
```

`∀ m < 1729, …` is decidable via `Nat.decidableBallLT`; the Finset card is
decidable via `DecidableEq`. `taxicab_two_eq_1729` assembles these into the
least-witness statement `2 ≤ card(reps 1729) ∧ ∀ m < 1729, ¬ 2 ≤ card(reps m)`.

**Independent numeric certificate** (`verify_taxicab.py`, ran clean this session):
- `reps(1729) = [(1,12), (9,10)]` (exactly two unordered pairs).
- No `m < 1729` has `≥ 2` representations (minimality holds).
- **Cap-soundness**: a generous cap (20) finds no representation that the cap-12
  grid misses, for every `m ≤ 1729` — so bounding summands at 12 is lossless here.

### Risk / open verification question (next session)

The only unknown is whether kernel `decide` reduces the ~250k bounded-`Nat` cube
checks within build limits. If it times out / OOMs in the kernel:
- swap `minimal_below_1729` to `native_decide` — instant, but introduces
  `Lean.ofReduceBool`, which downgrades the entry from `verified` to `axiomatized`
  (badge `axiom`). Prefer keeping `decide` if it compiles.
- or shrink the per-`n` work (e.g. precompute the sorted cube list, or prove
  minimality by a coarser case split) to keep it axiom-free.

---

## Mathlib / Gallery Gap

Absent from Mathlib and the gallery. Distinct from `ramanujan-sum-fallacy`. No
existing `Taxicab*` Lean file. Mathlib has no `taxicab`/`Ta(k)` development.

---

## Dead Ends

(none yet)

---

## Next Steps

1. **Build the scaffold** when a Docker slot opens (≤ 2 peers):
   `./proofs/scripts/docker-build.sh Proofs.TaxicabNumberOQ01`. Confirm `decide`
   compiles; if not, apply the `native_decide` fallback (and set status
   `axiomatized`).
2. **Register** in `Proofs.lean` and add gallery data
   `src/data/proofs/taxicab-number-oq-01/meta.json` only after a green build.
3. Set status `verified` (0 sorries, 0 axioms) iff `decide` carried it; otherwise
   `axiomatized` with the `native_decide`/`ofReduceBool` assumption documented.
4. Optional follow-up: `Ta(2)` as the least element of `{n | 2 ≤ card(reps n)}`
   phrased with `Nat.find`, or a `Ta(1) = 2` warm-up (`2 = 1³ + 1³`, least sum of
   two positive cubes) — only if it adds theory, not a renaming.
