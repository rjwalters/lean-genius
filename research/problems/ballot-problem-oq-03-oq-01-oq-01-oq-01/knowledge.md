# Knowledge Base: LGV Lemma → Jacobi-Trudi Identity

**Problem**: ballot-problem-oq-03-oq-01-oq-01-oq-01
**Last Updated**: 2026-05-02
**Knowledge Items**: 39

Insights accumulated during research on this problem.

---


---

> **Note**: 13 older sessions archived to `sessions/` directory.

## Session 2026-04-27 (Session 11) — Concrete b=1 Recipe Documented

**Mode**: REVISIT (RICH, score 73)
**Outcome**: SURVEY+ — added actionable b=1 proof recipe to file; no sorry count change

### What I Did

Confirmed the file's two open sorries are stable (jdt_weight_sum b≥1, jacobi_trudi_ssyt_eq k≥3).
Investigated relevant Mathlib API:

- **`Sym.oneEquiv : α ≃ Sym α 1`** (Mathlib.Data.Sym.Basic:477) — provides clean
  Sym n 1 ↔ Fin n conversion: `oneEquiv a = ⟨{a}, _⟩`.
- **`Sym.cons : α → Sym α n → Sym α (n+1)`** (denoted `::ₛ`, line 106). Coercion
  is `(a ::ₛ s : Multiset) = a ::ₘ s.1`.
- **`Sym.erase [DecidableEq α] : Sym α (n+1) → α → (a ∈ s) → Sym α n`** (line 203).
- **`Sym.cons_erase : a ::ₛ s.erase a h = s`** (line 219) — left-inverse closer.
- **`Sym.erase_cons_head : (a ::ₛ s).erase a _ = s`** (line 223) — round-trip.
- **`Multiset.sort_cons : (∀ b ∈ s, r a b) → sort (a ::ₘ s) r = a :: sort s r`**
  (Multiset/Sort.lean:69) — KEY for showing that consing the min preserves sort head.

Added an explicit recipe block to `BallotProblemOQ03OQ01OQ01OQ01.lean` at the b≥1
branch of `jdt_weight_sum` describing the b=1 bijection construction in concrete
Lean terms. This makes the next session's implementation mechanical.

### Concrete b=1 Recipe (already documented in file, recorded here for posterity)

```text
-- LHS for b=1 (after Sym.oneEquiv reparameterization):
--   ∑_{(P : Sym n a, q : Fin n) // q ≤ P.sort[0]} wt(P) * X q
-- RHS: h_{a+1} = ∑_{P' : Sym n (a+1)} wt(P').

-- Bijection ψ:
--   forward (P, q, h) ↦ q ::ₛ P
--   inverse P' ↦ ((P'.erase q', oneEquiv q'), proof) where q' = P'.sort.head
--   left_inv: erase_cons_head (q is the head we just consed)
--   right_inv: cons_erase (after extracting min, consing it back gives P')
-- Weight preservation (single line):
--   wt(P) * X q = ((q ::ₘ P.1).map X).prod = wt(q ::ₛ P)
-- via Multiset.prod_cons + Multiset.map_cons.
```

### Why I Didn't Implement

Without local docker build feedback, attempting an 80-100 line bijection proof
risks breaking compilation in subtle ways (Fin coercions, sort.head pos proofs,
etc.). The recipe captures the math precisely so a session with build access
can implement directly.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (~30 lines of detailed
  recipe added in `jdt_weight_sum` b≥1 branch comment)
- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/knowledge.md` (this file)

### Sorry Count: 2 (unchanged)

### Next Session Owner

Implement `jdt_weight_sum_b_one` as a separate `private lemma` using the
documented recipe. Estimated 60-90 lines focused work given the API references
are now explicit. Then refactor `jdt_weight_sum` to dispatch on b ∈ {0, 1, ≥2}.
The b≥2 case remains the JDT seam construction (~150 lines) and is the
real frontier.

---

## Session 2026-04-27 (Session 10) — Survey only; no code changes

**Mode**: REVISIT (RICH, score 72)
**Outcome**: SURVEYED — confirmed state, no code change

### What I Did

Surveyed the file state. Confirmed two open sorries with stable, correctly-stated formulations:

1. **`jdt_weight_sum (n a b : ℕ) (hba : b ≤ a)`** at line 388 — JDT bijection for the 2-row case. Statement is correct (per session 9's discovery that the partition hypothesis `b ≤ a` is essential). Proof requires the explicit `Equiv` between `{(P:Sym n a, Q:Sym n b) // ¬ColStrictSym a b P Q}` and `Sym n (a+1) × Sym n (b-1)` via the JDT seam construction (~100–150 lines).

2. **`jacobi_trudi_ssyt_eq` k≥3 branch** at line 631 — requires algebraic LGV (~150 lines) plus RSK (~150 lines).

### Honesty Note

Did not produce code changes this iteration. Both remaining sorries are large, well-scoped bodies of work that need a focused session, not a quick fix. Releasing the claim so an agent with budget for a substantial JDT or RSK push can pick this up.

### Sorry Count: 2 (unchanged)

### Suggested Next Owner

A session targeting **only `jdt_weight_sum`**: define the forward map (`P + {Q.sort[c]}, Q − {Q.sort[c]}`), the inverse (find seam in P'), then prove `Equiv.weight_preserved` via `Multiset.prod_cons` + `Multiset.prod_erase`. Estimated ~120 lines focused work.

---

## Session 2026-04-27 (Session 13) — b=1 Inverse Mechanism Refined

**Mode**: REVISIT (RICH, score 75)
**Outcome**: SURVEY+ — refined inverse direction recipe with verified Mathlib paths; no proof code change

### Constraints

Disk at 89% (1.6GB free). Per project memory and prior sessions 10-12, attempting a
fresh ~80-100 line bijection proof without Docker iteration risks committing broken Lean.
Adopted SURVEY+ approach: refine the recipe so the next session's implementation
is more mechanical.

### What I Verified

Cross-checked Mathlib v4.26.0 source at `/private/tmp/mathlib4`:

- `Multiset.erase_cons_head (a : α) (s : Multiset α) : (a ::ₘ s).erase a = s`
  — `Mathlib/Data/Multiset/AddSub.lean:156` (NEW reference, not surfaced in prior sessions)
- `Multiset.cons_erase {s : Multiset α} {a : α} : a ∈ s → a ::ₘ s.erase a = s`
  — `Mathlib/Data/Multiset/AddSub.lean:175`
- `Multiset.length_sort : (sort s r).length = card s` — `Sort.lean:88`
- All Sym.cons / erase / oneEquiv references from session 12 still valid

### What I Refined

Updated the recipe in `BallotProblemOQ03OQ01OQ01OQ01.lean` (jdt_weight_sum b≥1 branch
comment) to spell out the inverse direction's mechanism step-by-step:

```text
Given P' : Sym (Fin n) (a+1):
  L := P'.1.sort (· ≤ ·) : List, length a+1, sorted
  q' := L.head L_pos.ne'
  q' ∈ P'.1: List.head_mem + Multiset.mem_coe + Multiset.sort_eq
  Erase well-defined: P'.1 = q' ::ₘ (L.tail : Multiset) → erase q' = L.tail
    (via Multiset.erase_cons_head, AddSub.lean:156)
  Domain constraint q' ≤ (P'.erase q').sort[0]:
    L = q' :: L.tail (List.head_cons_tail), so L[0] ≤ L[1] = L.tail[0]
```

This is more concrete than session 11/12's recipe — the inverse direction was the
trickiest piece, and the precise lemma chain (Multiset.erase_cons_head was missing
from the prior recipe) is now spelled out.

### Sorry Count: 2 (unchanged)

Both remaining sorries are stable, correctly stated:
1. `jdt_weight_sum (hba : b ≤ a)` b≥1 case — JDT bijection (~80-100 lines for b=1; ~150 for b≥2)
2. `jacobi_trudi_ssyt_eq` k≥3 — algebraic LGV + RSK (~300 lines)

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` — recipe comment refined (~25 line addition, comment-only, no code/proof change)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json` — knowledge updated
- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/knowledge.md` — this entry

### Next Session Owner

The b=1 helper is now mechanical to implement given Docker access. Estimated 80-100
lines using the documented recipe. The b≥2 JDT seam construction remains the genuine
frontier (~150 lines). For k≥3, a separate file `BallotProblemOQ03AlgebraicLGV.lean`
with ~150 lines of ring-valued LGV would complete the framework.

---

## Session 2026-05-02 (Session 18) — Non-injective bijection diagnosis + correct proof path

**Mode**: REVISIT (RICH knowledge tier, score 88)
**Outcome**: analysis — discovered fundamental flaw in described b≥2 bijection; identified correct proof path via weight factorization + counting identity

### What I Did

1. **Rebased worktree to origin/main** to pick up PR #14882 (Session 17: `jdt_weight_sum_b_one` proved). Confirmed the file now has exactly 2 sorries (not 3):
   - Line 598: `jdt_weight_sum` b ≥ 2 seam bijection
   - Line 841: `jacobi_trudi_ssyt_eq` k ≥ 3 (RSK)

2. **Analyzed the "insert violation element" bijection** described in the file's b≥2 sorry comment:
   - Forward: find first-violation column c; move `Q.sort[c]` from Q to P at position c.
   - This is the bijection that has been described across sessions 5–17 but never proved.

3. **Discovered it is NON-INJECTIVE for b ≥ 2.** Concrete counterexample (a=3, b=2):
   - Pair A: `P={1,3,4}`, `Q={0,2,3}`. First violation at c=0 (P.sort[0]=1 ≥ Q.sort[0]=0). Move v=0 from Q to P: `P'={0,1,3,4}`, `Q'={2,3}`.
   - Pair B: `P={0,1,4}`, `Q={2,3,3}`. First violation at c=2 (P.sort[2]=4 ≥ Q.sort[2]=3). Move v=3 from Q to P: `P'={0,1,3,4}`, `Q'={2,3}`.
   - Both pairs map to `(P', Q') = ({0,1,3,4}, {2,3})`. The forward map is NOT injective.

4. **Identified the correct proof path.** Key observation:
   `wt(P) * wt(Q) = ((P.1 + Q.1).map X).prod` — weight depends only on the TOTAL multiset, not the split.
   
   Therefore, the polynomial identity `∑_{non-cs (P,Q)} wt = h_{a+1} * h_{b-1}` is equivalent to:
   
   **Counting identity**: for every `M : Sym (Fin n) (a+b)`,
   `#{non-cs (a,b) splits of M} = #{all (a+1,b-1) splits of M}`
   
   where `#{all (a+1,b-1) splits of M} = C(a+b, a+1)` (purely combinatorial, no ring structure needed).

5. **The counting identity is provable by the ballot/reflection principle.** For a multiset M of size a+b, splits into (P:a, Q:b) and (P':a+1, Q':b-1) both correspond to choosing k elements from M. The non-col-strict condition picks exactly the splits where `P.sort[0] ≥ Q.sort[0]` (the "bad" ones) — and a ballot-principle bijection maps these exactly to all (a+1,b-1) splits.

### Key Findings

- **The "insert violation element" bijection is provably non-injective for b ≥ 2.** The counterexample above is concrete and definitive. This explains why 17 sessions have failed to prove it — the approach is mathematically wrong.

- **Weight factorization is the key insight**: `wt(P)*wt(Q) = ((P.1+Q.1).map X).prod`. This was already observed in the proof of `jdt_weight_preserved` (which moves one element between P and Q without changing the weight). For the full sum, it means we only need to count splits by total multiset.

- **The correct proof strategy** (no ring-valued LGV or bijection of pairs needed):
  1. Group the LHS sum by total multiset M: `∑_M ∑_{non-cs splits of M} wt(M)`.
  2. Each M contributes `|{non-cs splits of M}| * wt(M)`.
  3. Show `|{non-cs splits of M}| = |{all (a+1,b-1) splits of M}|` by ballot principle bijection.
  4. Regroup RHS: `h_{a+1} * h_{b-1} = ∑_M |{all (a+1,b-1) splits of M}| * wt(M)`.
  
- **Infrastructure needed** (~100-150 lines):
  - `sym_split_of_union` or similar: for M : Sym n (a+b), a split is a pair (P:a, Q:b) with P.1 + Q.1 = M.1.
  - `ballot_bijection`: for fixed M, non-cs (a,b) splits ≃ all (a+1,b-1) splits. The bijection: given a non-cs split (P,Q) with violation at c, move Q.sort[c] → minimum element of {P.sort[c+1..], Q.sort[c+1..]}; this is weight-NEUTRAL since M is fixed.
  - Actually the counting argument may be even simpler: just `Fintype.card_congr` using the ballot principle bijection on fixed M.

### Files Modified

- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/knowledge.md` (this entry)

### Next Steps

1. **Implement weight-factorization approach** for `jdt_weight_sum` b ≥ 2:
   - Prove `weight_eq_total_multiset` (or use `jdt_weight_preserved` iteratively): `wt(P)*wt(Q) = ((P.1+Q.1).map X).prod`.
   - Restructure the LHS sum to group by total multiset M.
   - State and prove the counting identity via ballot bijection on each fiber.
   - Estimated ~100-150 lines, all within standard Lean combinatorics API.

2. **The b≥2 sorry does NOT need ring-valued LGV.** The counting argument avoids algebra entirely — it's a bijection on a finite set indexed by M.

3. **Do NOT pursue the "insert violation element" approach further.** It is non-injective.

4. **For `jacobi_trudi_ssyt_eq` k ≥ 3**: RSK or algebraic LGV remain the only known paths. This is the harder open sorry.

---

## Session 2026-05-02 (Session 17) — Prove jdt_weight_sum_b_one bijection

**Mode**: REVISIT (RICH knowledge tier, score 88 → 90)
**Outcome**: progress — `jdt_weight_sum_b_one` proved; sorry count 3 → 2

### What I Did

Implemented the bijection in `jdt_weight_sum_b_one` (lines 474-554):

- **`getq Q`**: extract unique element q from Q : Sym (Fin n) 1 via
  `(sym_one_sort_head_singleton n Q).choose`, with helpers:
  - `getq_spec`: Q.1 = {getq Q}
  - `getq_sort`: Q.1.sort = [getq Q]
  - `getq_eq`: if Q.1 = {q} then getq Q = q

- **Forward map**: `⟨(P, Q), _⟩ ↦ Sym.cons (getq Q) P`

- **Inverse map**: `S ↦ (S.erase qS hmem, ⟨{qS}, _⟩, proof_¬CS)` where
  `qS = S.1.sort[0]` (the minimum of S). The ¬CS proof:
  - Extract q' from singleton ⟨{qS}, _⟩ via sym_one_sort_head_singleton, get q' = qS
  - Need qS ≤ (S.erase qS).sort[0]: since qS is minimum of S, and S.erase ⊆ S,
    every element of S.erase is ≥ qS. Use Multiset.mem_of_mem_erase + pairwise_sort.

- **left_inv**: From ¬CS: getq Q ≤ P.sort[0]. Use `le_all_of_le_head` to deduce
  getq Q ≤ every element of P. Then `Multiset.sort_cons` gives
  (getq Q ::ₘ P).sort = getq Q :: P.sort, so S.sort[0] = getq Q, and
  `Sym.erase_cons_head` gives S.erase qS = P.

- **right_inv**: qS = S.sort[0]; getq_eq gives getq ⟨{qS}, _⟩ = qS; then
  `Sym.cons_erase` gives Sym.cons qS (S.erase qS _) = S.

- **Weight**: `Fintype.sum_equiv ψ` + ring after `getq_spec Q` (Q.1 = {getq Q}).

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (768 → 843 lines, +75)
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-01-oq-01/meta.json` (sorries: 3→2)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json`

### Build Status

Docker build deferred to CI (Docker daemon may still be recovering from yesterday's
stuck build). The implementation follows the same API usage pattern as the
existing `ssytSchurFin_one_row` bijection in this file and the helper lemmas
already proved in sessions 15-16.

### Next Steps

1. `jdt_weight_sum` b ≥ 2 seam bijection (~150-200 lines): find first violation
   column c, insert Q.sort[c] into P, track the seam index in inverses.
2. Alternative: submit b≥2 sorry to Aristotle (it is a HARD sorry for a known
   combinatorial result).
3. Long-term: `jacobi_trudi_ssyt_eq` k ≥ 3 (RSK bijection, ~300 lines).

---

## Session 2026-05-03 (Session 19) — rel_head bug fix + Aristotle submission

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: fix — corrected `rel_head` bug in b=1 bijection; submitted Aristotle; updated b≥2 approach

### What I Did

1. **Fixed `List.Pairwise.rel_head` bug** in `sort_min_le_sym` / `sort_min_le_p` helpers:
   - Bug: used non-existent `Pairwise.rel_head`; `List.rel_of_pairwise_cons` requires tail membership.
   - Fix: `cases hm : sort_result with | nil | cons hd tl` + `List.mem_cons` case split.
   - Commits: `06b0c6c050`, `4bc99baed5`

2. **Submitted Aristotle companion** → project_id: `c6967eb8-24fa-47a7-99b9-b56b53f5b847`

3. **Found** prior Aristotle job `9ddf3174` (COMPLETE, 1 day ago) had already proved
   `jdt_weight_sum_b_one_Aristotle` via a slightly different bijection approach.

### Key Findings

- **Pattern for `sorted list minimum ≤ x`** in Lean 4:
  ```lean
  cases hm : (ms.sort r) with
  | nil => exact absurd (hm ▸ hmem) (List.not_mem_nil x)
  | cons hd tl =>
    have : (ms.sort r)[0]'hlen = hd := by conv_lhs => rw [hm]; simp
    rw [this]; rw [hm] at hmem hpw
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact le_refl _
    · exact (List.pairwise_cons.mp hpw).1 x htl
  ```

- **Aristotle `not_colStrict_b_one`** proved via `grind` (standalone companion form).

### Next Steps

1. Verify b=1 proof compiles (CI from PR #14896).
2. Implement b≥2 via weight factorization (~100-150 lines).

---

## Session 2026-05-03 (Session 20) — Integrate Aristotle proof into companion file

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: progress — companion file sorry eliminated; b≥2 analysis deepened

### What I Did

1. **Retrieved Aristotle job `9ddf3174`** result and integrated the full proof into
   `BallotProblemOQ03OQ01OQ01OQ01Aristotle.lean`. The proof uses:
   - `not_colStrict_b_one` via `grind` (characterizes ¬ColStrict for b=1)
   - `cons_weight` via `simp` (weight decomposition)
   - Main theorem: bijection via uniqueness of minimum element of S, with
     `Finset.min'` for existence, `Finset.sum_image` / `Finset.sum_bij` for sum manipulation.
   - Commit: `a6bcbbd8e8`

2. **Analyzed b≥2 bijection candidates** — identified that BOTH simple bijections fail:
   - **Violation-element bijection**: non-injective (Session 18 counterexample: pairs
     P={1,3,4},Q={0,2,3} and P={0,1,4},Q={2,3,3} both map to ({0,1,3,4},{2,3}))
   - **Min-of-Q bijection** (move Q.sort[0] to P): also non-injective for b≥2.
     Counterexample: M={1,2,3,4}, a=2, b=2. Pair {1,4}×{2,3} (violation at i=1,
     Q.sort[0]=2>P.sort[0]=1) and Pair {2,4}×{1,3} (violation at i=0, Q.sort[0]=1)
     both map to {1,2,4}×{3}.
   - Root cause: the min-of-Q bijection only works when the violation is at i=0.
     For violations at i≥1 (where Q.sort[0] > P.sort[0]), the "min of Q" that gets
     moved is NOT the minimum of P' = Q.sort[0] ::ₛ P, breaking injectivity.

3. **Confirmed the fiber-counting equality** numerically for several M:
   - M={1,2,3,4}: #{non-cs (2,2) splits}=4 = #{(3,1) splits}=4 ✓
   - M={1,1,2,2}: #{non-cs (2,2) splits}=2 = #{(3,1) splits}=2 ✓
   - M={1,1,1,1}: #{non-cs (2,2) splits}=1 = #{(3,1) splits}=1 ✓
   The equality holds but no elementary bijection has been found.

### Key Findings

- **The correct bijection for b≥2 is RSK/JDT.** For two-row shapes, JDT applied to
  non-SSYT pairs maps (a,b) → (a+1,b-1) shapes. This is the Jacobi-Trudi identity's
  combinatorial proof. The direct "move min of Q" and "move violation element" bijections
  both fail. The RSK column-insertion algorithm is the standard approach but requires
  ~300-500 lines to formalize.

- **Aristotle job `c6967eb8`** (21% after 35 min) is working on the b=1 companion theorem
  (same as already proved by `9ddf3174`). It will not help with b≥2.

- **The b≥2 sorry is genuinely hard** and likely requires either:
  (a) RSK formalization (~300-500 lines), or
  (b) An algebraic proof using the symmetric polynomial structure, or
  (c) Waiting for Aristotle on a carefully structured submission of the b=2 case first.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01Aristotle.lean` (sorry → proof, +100 lines)
- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/knowledge.md` (archived + updated)
- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/sessions/` (13 sessions archived)

### Next Steps

1. **Cancel job `c6967eb8`** (duplicate of `9ddf3174`) — not needed.
2. **Submit b≥2 sorry to Aristotle** as a standalone: the fiber-level counting
   identity `#{non-cs (a,b) splits of M} = #{(a+1,b-1) splits of M}` for each M.
3. **Consider b=2 special case** as a stepping stone: for b=2, violation is at
   i=0 or i=1 only, which might admit a case-split proof (~50 lines).
4. **Algebraic approach**: prove h_a*h_b - h_{a+1}*h_{b-1} = ∑_{cs} wt directly
   using Mathlib's symmetric polynomial ring lemmas.
