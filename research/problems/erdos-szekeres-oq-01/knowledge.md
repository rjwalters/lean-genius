# Knowledge Base: erdos-szekeres-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Target**: discharge `erdos_szekeres_existence_axiom` in `proofs/Proofs/ErdosSzekeres.lean`
(line 200), converting it from an `axiom` to a proved `theorem`. This reduces the parent
`erdos-szekeres` gallery entry from 2 axioms to 1 (the remaining axiom,
`erdos_szekeres_tight_axiom` at line 235, is out of scope here).

The parent encodes sequences as `Sequence α n := Fin n → α` and subsequences as the
structures `IncreasingSubseq f k` / `DecreasingSubseq f k`, each carrying
`positions : Fin k → Fin n` that is `StrictMono` with `StrictMono (f ∘ positions)`
(resp. `StrictAnti`).

**Two approaches are on the table** (see `problem.md`): the in-progress bottom-up
Approach B (#22772) and the newly-surveyed Archive-import Approach A.

---

## Insights

### S3 ORIENT (2026-06-13, researcher-1) — Mathlib already proves the core (Approach A)

- **`Theorems100.erdos_szekeres`** in the Mathlib **Archive**
  (`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`) is a *fully proved*
  Erdős–Szekeres theorem (no axioms), using the same pigeonhole-on-pairs argument the
  parent's docstring describes — i.e. it already contains the exact content Approach B is
  hand-rebuilding. Signature:
  ```lean
  theorem erdos_szekeres {α β} [Fintype α] [LinearOrder α] [LinearOrder β]
      {r s : ℕ} {f : α → β} (hn : r * s < Fintype.card α) (hf : Injective f) :
      (∃ t : Finset α, r < t.card ∧ StrictMonoOn f ↑t) ∨
      (∃ t : Finset α, s < t.card ∧ StrictAntiOn f ↑t)
  ```
- **The Archive is importable here**: `proofs/Proofs/BallotProblem.lean` already imports
  `Archive.Wiedijk100Theorems.BallotProblem`. The lakefile requires `mathlib`, and the
  Archive ships with it, so `import Archive.Wiedijk100Theorems.AscendingDescendingSequences`
  is expected to resolve (confirm at build time).
- **Bound reconciliation is exact** under the index shift `r ↦ r-1`, `s ↦ s-1`:
  Archive's `(r-1)*(s-1) < Fintype.card (Fin n) = n` ⟺ parent's `n ≥ (r-1)*(s-1)+1`.
  Archive's conclusion `(r-1) < t.card` ⟺ `r ≤ t.card`.
- **Structure conversion bearer**: `Finset.orderEmbOfCardLe (t : Finset α) (h : k ≤ t.card)
  : Fin k ↪o α` gives a strictly-monotone `Fin k → α` with image ⊆ `t`
  (Mathlib `Data/Finset/Sort.lean`, mathlib3 `order_emb_of_card_le`). Composing the
  `StrictMonoOn f ↑t` witness with this embedding yields the parent's
  `StrictMono (f ∘ positions)` via `StrictMonoOn.comp_strictMono`.

### Recommended ACT plan for Approach A

1. `import Archive.Wiedijk100Theorems.AscendingDescendingSequences`.
2. In the discharging theorem (same signature as `erdos_szekeres_existence_axiom`):
   apply `Theorems100.erdos_szekeres (α := Fin n) (β := α) (r := r-1) (s := s-1) f`
   with the bound rewritten via `Fintype.card_fin` + `omega`.
3. Case-split the disjunction; in each case take `t` and build
   `positions := Finset.orderEmbOfCardLe t (by omega : r ≤ t.card)`, then assemble the
   `IncreasingSubseq` / `DecreasingSubseq` structure (`strictMono_values` from
   `StrictMonoOn.comp_strictMono`).
4. Replace the `axiom` with this theorem.

### Strategic note vs Approach B

Approach B (#22772, ACT-1 done) is hand-building `maxIncLen`/`maxDecLen` +
`HasIncreasingEndingAt` infrastructure (lines 99–174 of the parent) and still owes the
position→pair injectivity lemma (`maxIncLen_lt_of_lt`) plus the final pigeonhole. If
Approach A's import resolves, it discharges the axiom with ~30–50 LOC of plumbing instead,
making the in-progress bottom-up scaffold unnecessary for the *axiom-discharge* goal.
Worth prototyping Approach A before committing to Approach B's ACT-2.

---

## Dead Ends

- (none recorded yet). Approach B is *viable but likely dominated* by Approach A for the
  axiom-discharge goal — not a dead end, just more code than necessary if A typechecks.

---

## Build status

ACT (either approach) is **build-gated** and not attempted during the 2026-06-13 Docker
blackout. Prototype Approach A and Docker-verify once build infra is restored.
