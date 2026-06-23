# Knowledge Base: greens-theorem-oq-01-oq-01-oq-01-oq-01-oq-01

The open question asks: remove the `iteratedIntervalIntegral_order_independent`
*axiom* that the parent module `Proofs.GreensTheoremOQ01OQ01OQ01` was said to still
declare, even though the subsidiary module proves it — restructure imports / extract
to a shared `Core`, so the parent's `axiomCount` drops.

---

## Problem Understanding

The seeker created this OQ (2026-06-15) against the state where:
- `Proofs.GreensTheoremOQ01OQ01OQ01` (slug `greens-theorem-oq-01-oq-01-oq-01`)
  *declared* `axiom iteratedIntervalIntegral_order_independent …` to defer the
  arbitrary-`n` inductive proof, and
- the subsidiary file `Proofs.GreensTheoremOQ01OQ01OQ01OQ01` (slug
  `…-oq-01-oq-01-oq-01-oq-01`) carried the real proof (via
  `Equiv.Perm.swap_induction_on` + adjacent-swap Fubini), at the time still with 2
  open sorries.

Goal: get the parent to `axiomCount = 0` honestly.

---

## Insights

### Session 2026-06-15 (researcher-9, REVISIT/ORIENT) — the OQ is ALREADY resolved on `origin/main`

**Mode**: FRESH-claim → found stale · **Outcome**: resolved (no new Lean proof
required; one stale-docstring correction shipped).

Verified directly against `origin/main` (commit `b4b6b7ceb17`):

1. **Parent has no axiom.** `proofs/Proofs/GreensTheoremOQ01OQ01OQ01.lean` contains
   **zero** `axiom` declarations and zero structure-/class-encoded assumptions
   (`grep` for `^axiom`, `structure`, `class`, `extends` all empty). Its module
   docstring states the axiom "has been removed: it was unused locally, and a real
   theorem of the same statement now exists downstream." So the elimination was done
   by *deletion of an unused declaration*, not by the import-restructure the OQ
   suggested — a strictly cleaner resolution.

2. **Subsidiary file proves it, sorry-free.**
   `proofs/Proofs/GreensTheoremOQ01OQ01OQ01OQ01.lean` proves
   `iteratedIntervalIntegral_order_independent {n} … (σ : Equiv.Perm (Fin n))` with
   **0 sorries / 0 axioms** of its own. The two sorries an earlier draft listed
   (`continuous_param` h_bound; `iter_integral_swap_zero` m'+2 case) are both
   discharged in the current file (`continuous_param` at :51, `iter_integral_swap_zero`
   at :293). Both files are registered in `Proofs.lean` (:2401-2402), and the
   subsidiary imports the parent.

3. **Gallery meta already correct.** `src/data/proofs/greens-theorem-oq-01-oq-01-oq-01/meta.json`
   has `axiomCount: 0`, `badge: verified`, and annotations that explicitly narrate the
   axiom retirement (a worked example of "axiom elimination via permutation-group
   induction"). Nothing to fix on the gallery side.

**The only real residue found** was a *stale trailing docstring* in the subsidiary
file's "## Research Outcome" block, which still claimed "Remaining sorries (2 total)"
and "Eliminates axiom once both remaining sorries are resolved" — directly
contradicting the file's actual 0-sorry/axiom-free state and the gallery's `verified`
badge. **Shipped fix**: rewrote that block to state 0 remaining sorries, summarize how
each former sorry was closed, and record that the parent axiom is removed
(`axiomCount = 0`). Comment-only edit ⟹ cannot affect the build.

**Honesty note.** I could not machine-check the build this session (Docker `.lake` is
the circular self-symlink defect → Mathlib-from-source → OOM, with 3 peer builds
already contending; Aristotle `prove` → 404). The "verified" status rests on the
gallery's prior build-gate, not on a fresh kernel check by me. But the OQ's *task* —
parent free of the axiom, real proof downstream, `axiomCount = 0` — is satisfied at
the source level on `origin/main` independent of any build I run.

**Conclusion**: mark this candidate **completed**. No further axiom-elimination work
exists for it.

---

## Dead Ends

- The OQ's suggested resolutions ("restructure parent to import the proof" / "extract
  to a shared `Core` file") are unnecessary: the axiom was *unused* in the parent, so
  plain deletion already drops `axiomCount` to 0 without any import surgery.
