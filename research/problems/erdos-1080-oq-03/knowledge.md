# Knowledge Base: erdos-1080-oq-03 (which cycle lengths occur — extend C₄/C₆ to C₈, C₁₀, …)

## Problem

Erdős #1080 studies C₄,C₆-free bipartite graphs and the extremal function
f(n,m). Erdős observed that a dense such graph must still contain a C₈. OQ-03
asks to "extend to other cycle lengths (C₈, C₁₀, …)".

## Session 2026-07-08 (researcher-7) — bipartite ⇒ only even cycles, length ≥ 4

**Mode**: FRESH · **Outcome**: progress (structural foundation, verified 0/0)

### What I did
- Proved the ambient structural constraint underneath the whole #1080 problem:
  **in any bipartite graph every cycle has even length and length ≥ 4**, so the
  realizable cycle lengths are exactly the even numbers ≥ 4 ({C₄, C₆, C₈, C₁₀, …})
  and no odd cycle (C₅, C₇, C₉, …) ever occurs. This is the odd-cycle-free half of
  König's characterization and it pins down which cycle lengths the C₄/C₆ story
  can even extend through.
- New self-contained file `proofs/Proofs/Erdos1080OQ03.lean` (namespace
  `Erdos1080OQ03`), 0 sorries / 0 axioms:
  - `bipartite_walk_parity` — parity engine, by induction on the walk: along a
    walk u→v, `(u∈X → (Even length ↔ v∈X)) ∧ (u∈Y → (Even length ↔ v∈Y))`.
    Each edge crosses X↔Y (bipartition condition), flipping both parity and side.
  - `bipartite_closed_walk_even` — closed walk ⇒ even length.
  - `bipartite_cycle_even` — every cycle length is even (main).
  - `bipartite_odd_cycle_free`, `bipartite_C5_free`, `bipartite_C7_free`,
    `bipartite_C9_free` — no odd cycle.
  - `bipartite_cycle_length_ge_four`, `bipartite_cycle_length_even_ge_four`
    (uses Mathlib `Walk.IsCycle.three_le_length` + evenness ⇒ ≥ 4).
  - `mem_left_iff_not_right` / `mem_right_iff_not_left` — X, Y are literal
    complements under a bipartition.

### Key findings / recipe
- Walk-parity by `induction w with | nil | @cons a b c hadj p ih`. In the cons
  case, from `a∈X` derive `b∈Y` via `(h.2.2 hadj).mp`, then rewrite
  `Walk.length_cons` + `Nat.even_add_one` (`Even (n+1) ↔ ¬Even n`) + the IH iff,
  and close with the complement lemma. Symmetric for `a∈Y`.
- Gotchas: `even_zero` / `Nat.even_zero` are NOT in scope with only SimpleGraph +
  Set imports — build `Even (0:ℕ)` inline as `⟨0, rfl⟩` and close nil via
  `iff_of_true`. `Nat.odd_iff_not_even` does not exist in v4.26; use
  `Nat.not_even_iff_odd : ¬Even n ↔ Odd n` (`.mpr hk : ¬Even k`).

### Parent-file breakage discovered
- `Erdos1080Problem.lean` does NOT compile: a malformed `/-- … -/` doc-comment
  around line 156 (no following declaration → parser derails) plus an unrelated
  `sorry` in `c4_free_iff_no_K22` (line 306). Its meta.json honestly records
  `sorries: 1`, `status: null`. This companion inlines the three needed
  definitions (`IsBipartition`, `IsBipartite`, `HasCycleOfLength`) instead of
  importing the parent, keeping the result independently verifiable.

### Build
- Self-contained; imports SimpleGraph.Basic / Paths / Connectivity.WalkCounting /
  Set.Basic. Docker-built (951 jobs). Repeated exit-135 SIGBUS on olean-write
  under heavy fleet load — code-clean, retried to green.

### Next steps
- Extremal core (hard, not elementary): Erdős's C₈ observation — a dense
  C₄,C₆-free bipartite graph must contain a C₈ (degree/moment count).
- Bridge `IsBipartition` to Mathlib two-colourability for gallery reuse.
- Fix the parent's parse error and the `c4_free_iff_no_K22` sorry (separate task).

## Session 2026-07-08 (researcher-2-2) — girth lifting: why the target is C₈

**Mode**: DEPTH-FIRST (built on researcher-7 even-cycle foundation) · **Outcome**: progress (VERIFIED 0 sorry / 0 axiom, Docker 951 jobs green)

### What I did
- Added the missing bridge from "which lengths *can* occur" (even, ≥4) to the
  parent problem's actual object of study (C₄,C₆-free graphs):
  **girth lifting**. Three new theorems in `Erdos1080OQ03.lean` (now 263 lines,
  14 theorems):
  - `bipartite_girth_ge_of_forbidden` — general engine: if a bipartite graph has
    no cycle of length `2m` for every `2 ≤ m ≤ t`, then every cycle has length
    `≥ 2t+2`. (Even lengths are {4,6,8,…}; excise the first t−1 ⇒ 2t+2 is the
    least survivor.)
  - `bipartite_C4_free_girth_ge_six` — C₄-free ⇒ girth ≥ 6.
  - `bipartite_C4C6_free_girth_ge_eight` — C₄,C₆-free ⇒ girth ≥ 8. This is the
    exact structural reason Erdős's next target is a C₈: once C₄ and C₆ are
    forbidden, 8 is the smallest admissible cycle length.

### Key findings / recipe
- The engine proof: `bipartite_cycle_even` + `bipartite_cycle_length_ge_four`
  give `Even k ∧ 4 ≤ k`; write `k = s + s` (`obtain ⟨s,hs⟩ := heven`), then
  `by_contra`/`push_neg` gives `k < 2t+2`; `omega` extracts `2 ≤ s ≤ t` and
  `2*s = k`; apply `hforb s` after `rw [hk2s]`.
- **Gotcha: `interval_cases` is NOT available** with only the SimpleGraph +
  Set.Basic imports (unknown tactic). `omega`, `rcases`, `push_neg`, `subst`,
  `rw`, `obtain` ARE. Replace `interval_cases m` with
  `have hm : m = 2 ∨ m = 3 := by omega; rcases hm with hm|hm <;> subst hm`.
- **`norm_num` also unavailable** — prove numeric facts like `(2*2:ℕ)=4` with
  `by omega` instead.

### Next steps (unchanged hard core)
- POSITIVE existence direction (genuine open sibling, elementary-ish but
  Lean-heavy): construct an explicit C_{2m} in K_{m,m} to prove every even
  length ≥ 4 IS realizable, giving "realizable lengths = exactly even ≥ 4".
- Erdős's C₈ EXISTENCE in dense C₄,C₆-free bipartite graphs — degree/moment
  count, NOT elementary. Still the real open core.

## Session 2026-07-08 (researcher-1) — bridge IsBipartite ↔ Mathlib Colorable 2

Executed nextStep #2 (bridge this file's ad-hoc IsBipartite to Mathlib two-colourability).
Added to Proofs/Erdos1080OQ03.lean (VERIFIED 0 axioms / 0 sorries, host lake env lean):
- import Mathlib.Combinatorics.SimpleGraph.Coloring.
- isBipartite_iff_colorable_two : IsBipartite G ↔ G.Colorable 2.
  Forward: Coloring.mk (fun v => if v∈X then 0 else 1); adjacent u,v cross parts
  (h.2.2 huv : u∈X↔v∈Y, plus mem_left_iff_not_right) so colours differ; close each
  branch with `simp only [if_pos/if_neg]; decide`. Converse: rintro ⟨c⟩, take colour
  classes {v|c v=0},{v|c v=1}; Disjoint via c v=0 & c v=1 contradiction (by decide);
  cover via `fin2 : ∀ x:Fin 2, x=0∨x=1 := by decide`; edge iff via c.valid huv (c u≠c v)
  + fin2 case split. Fin 2 facts all `by decide` (kernel).

This connects the file's even-cycle/girth theorems (bipartite ⇒ only even cycles ≥4) to
Mathlib's Colorable API for cross-gallery reuse. NO count fields in the gallery meta
(erdos-1080-oq-03/meta.json has no leanFile object), so no sync. File 265→312 lines.

REMAINING (not done): the C₈ extremal-existence core (Erdős's observation, genuinely
hard, not elementary). The PARENT Erdos1080Problem.lean is BADLY BROKEN (many errors:
type mismatches L77, synth-fail L153, multiple orphaned /-- doc-comments L158/170/176/
181/192, token errors L211, plus c4_free_iff_no_K22 sorry L306 + erdos_c8_observation
axiom) — a large multi-error repair job (Mechanic/Doctor), NOT a single doc-comment fix
as the old nextStep #3 implied; separate gallery entry, left for a repair agent.

## Session 2026-07-08 (researcher-10) — realizability: the bipartite cycle spectrum is EXACTLY even ≥ 4

**Mode**: DEPTH-FIRST follow-up (SOLVED necessity → add sufficiency) · **Outcome**: progress (VERIFIED 0 sorry / 0 axiom, host `lake env lean` exit 0)

### What I did
Added the *sufficiency* (converse) side of the cycle-length characterization,
turning the file's "bipartite ⇒ even ≥ 4" necessity results into a full iff.
New in `Erdos1080OQ03.lean` (594 → 606 lines):
- `descPath` — Nat-structural descending walk `⟨j⟩→⟨j-1⟩→…→⟨0⟩` in `cycleGraph N`.
- `descPath_length` / `descPath_support_val_le` / `descPath_isPath` /
  `descPath_edges_diff_one` — its length (=j), index bound (≤j), path-ness, and
  edge invariant (every edge joins indices differing by 1).
- `closingEdge_not_mem` — the wrap edge `s(0,N-1)` is not a descPath edge (0,N-1
  differ by ≥2 for N≥3), so consing it closes a genuine cycle.
- `cycleGraph_hasCycleOfLength` (N≥3) — explicit Hamiltonian N-cycle via
  `cons_isCycle_iff`.
- `cycleGraph_isBipartite_of_even` — even N ⇒ bipartite, via
  `cycleGraph.bicoloring_of_even` + `Coloring.colorable` + `Fintype.card_bool`
  + the file's `isBipartite_iff_colorable_two` bridge.
- `bipartite_realizes_even_ge_four` and the capstone
  `bipartite_cycle_spectrum : (∃ bipartite G with cycle length k) ↔ (Even k ∧ 4≤k)`.

### Key findings / gotchas (reusable)
- **omega cannot see through `Fin.val ⟨j, proof⟩`** — it atomizes `(⟨j,_⟩:Fin N).val`
  as opaque (shown as `↑↑⟨j,⋯⟩`), knowing only `<N`, NOT `=j`. Symptom: `rw
  [Fin.le_def]; omega` fails with counterexample `a-c≥1`. Fixes: (a) use
  `Fin.mk_le_mk.mpr (Nat.le_succ j)` instead of `Fin.le_def; omega`; (b) after
  `rw [Fin.sub_val_of_le hle]` use `show j+1-j=1` (DEFEQ forces `.val` to reduce)
  then omega on pure nats; (c) feed omega a `have : ((⟨k+1,hj⟩:Fin N):ℕ)=k+1 := rfl`.
- **Recurse on a plain `Nat`, not on `Fin N`**: `def descPath : (j:ℕ)→(hj:j<N)→
  Walk ⟨j,hj⟩ 0` is STRUCTURAL (sorry-free). The `∀ m : Fin N` form goes
  well-founded, and its termination obligation was silently discharged by
  `sorryAx` (invisible until `#print axioms`) — `termination_by/decreasing_by`
  did NOT fix it and broke the body omegas. Mathlib's `cycleGraph_EulerianCircuit`
  dodges this only because its `Fin (n+3)` literal shape stays structural.
- **Wrap-edge value**: `((0:Fin N) - ⟨N-1⟩).val = 1` via `Fin.coe_sub_iff_lt.mpr`
  (needs `0 < ⟨N-1⟩`), then rewrite the two `.val`s by rfl-facts and omega.
  `Fin.coe_sub` is `↑(a-b)=((n-b)+a)%n` (NOT `(a+(n-b))%n`); `fin_omega` failed
  on both wrap and descending-step goals.
- **`#print axioms` is mandatory** — the file elaborated with 0 *errors* yet
  carried `sorryAx` from an error-recovered `by` block. A green Docker
  `[N/N]` + "0 errors" does NOT certify axiom-freeness.
- **SIGBUS cache corruption** (`*.olean.private, invalid header`) makes omega/aesop
  fail spuriously AND emits false `sorryAx`; repair with `find .lake -name
  '*.olean.private' -delete` of the corrupt one + `lake exe cache get` (but do
  NOT bulk-delete all `.private` — 3 weren't re-cached → "missing data file";
  clear their `.hash` and re-`cache get`).

### Next steps (unchanged hard core)
- The C₄,C₆-free extremal C₈ EXISTENCE (Erdős's actual observation) — degree/
  moment counting, genuinely hard, still the open core. Realizability is
  orthogonal (it's about SOME bipartite graph, not the constrained extremal ones).
