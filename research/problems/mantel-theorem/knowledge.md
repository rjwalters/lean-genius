# Knowledge Base: mantel-theorem

Insights accumulated during research on this problem.

---

## Problem Understanding

Mantel's theorem (1907): a triangle-free (`K₃`-free, i.e. `CliqueFree 3`) simple graph
on `n` vertices has at most `⌊n²/4⌋` edges, attained by the balanced complete bipartite
graph. It is the `r = 2` base case of Turán's theorem.

---

## Insights

### M1 (researcher-6, 2026-06-15) — SOLVED via Mathlib Turán specialization (BUILD GREEN)

- **Mathlib already provides the general Turán edge bound.** The Turán development lives in
  `Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean` (the old
  `Mathlib.Combinatorics.SimpleGraph.Turan` is now a `deprecated_module` redirect since
  2025-08-21). The load-bearing lemma is

      SimpleGraph.CliqueFree.card_edgeFinset_le (cf : G.CliqueFree (r + 1)) :
        let n := Fintype.card V;
        #G.edgeFinset ≤ (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2

  Specializing at `r = 2` and simplifying the RHS to `⌊n²/4⌋` IS Mantel's theorem. No new
  graph theory required — the only real work is the closing arithmetic identity.

- **The arithmetic identity `turan_two_simp`:**
  `(n² − (n%2)²)·(2−1)/(2·2) + (n%2).choose 2 = n²/4`.
  Two facts close it: (1) the binomial term vanishes since `n%2 < 2 ≤ 2`
  (`Nat.choose_eq_zero_of_lt`); (2) `n² = 4·((n/2)² + (n/2)·(n%2)) + (n%2)²` (proved by
  `conv_lhs => rw [← Nat.div_add_mod n 2]; ring`), and `(n%2)² < 4`, so `omega` finishes
  `(n² − (n%2)²)/4 = n²/4` by abstracting `n²`, `(n%2)²`, `(n/2)²`, `(n/2)·(n%2)` as atoms.

- **Sharpness is free.** `turanGraph n 2` is triangle-free (`turanGraph_cliqueFree (0<2)`)
  and has exactly `⌊n²/4⌋` edges (`card_edgeFinset_turanGraph` + `turan_two_simp`). Packaged
  as `mantel_bound_is_tight`.

- **Gotchas:**
  - `r` is implicit in `CliqueFree.card_edgeFinset_le`; pass `(r := 2)` and supply
    `h : G.CliqueFree 3` directly — `3` and `2+1` are defeq for Nat literals.
  - The conclusion is wrapped in `let n := Fintype.card V; …`. A `calc` first step against
    the explicit (let-free) RHS mis-parses / fails to match; `exact le_trans hb
    (le_of_eq (turan_two_simp _))` reduces the `let` by `whnf` and works.

### M2 (researcher-11 wrote, researcher-3 verified, 2026-06-15) — equality characterization (BUILD GREEN)

- **BUILD GREEN (researcher-3, 2026-06-15).** `docker-build.sh Proofs.MantelTheoremUniqueness`
  succeeded (7744 jobs, exit 0) on an uncontended slot (host ~18GB free; ~120s cold Mathlib
  clone + warm Azure cache download, then 17s to compile the target). The proof compiled exactly
  as written — no edits needed. Registered both `Proofs.MantelTheorem` and
  `Proofs.MantelTheoremUniqueness` in `Proofs.lean` (neither was registered despite M1 being
  merged), credited `mantel_equality_iff` in the gallery `originalContributions`, and removed
  the equality-characterization open question. The `theoremCount: 5` in the `leanFile` block
  stays accurate — it counts the base file only; `mantel_equality_iff` lives in the separate
  companion file.

- **Pool desync caught.** The candidate pool still listed `mantel-theorem` as
  `available`/EMPTY even though M1 was merged + audited (#24750/#24771/#24780). Fixed the live
  pool status to `completed`; this had caused at least one redundant re-claim. Future agents:
  the gallery entry is verified — work the follow-ups, not the base problem.

- **The characterization is the `r=2` uniqueness half of Turán.** Equality
  `#G.edgeFinset = ⌊n²/4⌋ ↔ G ≅ turanGraph n 2` reduces to `G.IsTuranMaximal 2` because:
  `IsTuranMaximal r := IsExtremal (CliqueFree · (r+1))`, i.e. `p G ∧ ∀ ⦃G'⦄ [DecidableRel],
  p G' → #G'.edgeFinset ≤ #G.edgeFinset`. Attaining the proven maximum `⌊n²/4⌋` *is* being
  extremal — no new graph theory, the upper bound `mantel_card_edgeFinset_le` does all the
  work in the `∀ G'` step.

- **Reverse direction is one rewrite.** `Iso.card_edgeFinset_eq` (a `G ≃g H` preserves
  `#edgeFinset`) + `card_edgeFinset_turanGraph_two` gives `#G.edge = ⌊n²/4⌋` from the iso.

- **Avoids the M1 `let` pitfall.** M2 calls the already-specialized `mantel_card_edgeFinset_le`
  (clean RHS `(Fintype.card V)²/4`), not the `let n := …`-wrapped `CliqueFree.card_edgeFinset_le`,
  so the `calc` matches directly.

- **Infra gotcha.** Docker builds here cold-clone Mathlib + download the ~7700-file cache each
  run (~750s) before compiling, so single-file builds exceed the 20m wrapper timeout under
  contention (was at 6–7 concurrent `lean-build` containers). Memory cap (2.5GB) keeps the
  host safe but the target never reached compilation. M2 shipped build-pending in companion
  file `MantelTheoremUniqueness.lean`; verify when a warm/uncontended slot exists.

---

## Dead Ends

- A from-scratch AM–GM / degree-sum proof (the textbook route) was deemed unnecessary once
  the Mathlib Turán specialization was confirmed to compile; not attempted.

---

## Open Follow-ups

- **Equality characterization (M2)** — DONE: `mantel_equality_iff` built GREEN and
  merged via #24869, registered in `MantelTheoremUniqueness.lean`, folded into the
  gallery entry. No longer open.
- **Stability (M3)** — Erdős–Simonovits: a triangle-free graph with near-`⌊n²/4⌋` edges is
  structurally close to the balanced complete bipartite graph.
- **Erdős–Stone–Simonovits** — express the extremal number of any forbidden `H` via `χ(H)`.
