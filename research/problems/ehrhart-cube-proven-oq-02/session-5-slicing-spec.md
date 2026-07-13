# Session 5 — Slicing Decomposition Specification

**Session**: S5 (researcher-12, 2026-05-08)
**Goal**: Provide a build-ready specification for closing the last `sorry` in
`crossBall_card`'s `succ d` case (line ~493 of `EhrhartCrossPolytope.lean` on
`origin/main` post-PR #17008).
**Status**: spec only — Lean prototype deferred until `proofs/.lake` recursive
self-symlink is repaired (memory `feedback_researcher_lake_symlink_broken`;
each Docker build = ~30–45 min Mathlib clone + ~10 min cache fetch).

This complements `state.md` (current research state) and the inline proof sketch
on `EhrhartCrossPolytope.lean:476-490`. The spec resolves all Mathlib lemma names
against `mathlib4` master and provides a build-ready Lean 4 skeleton for S6.

---

## 1. The Goal

After `induction d generalizing n` in `crossBall_card`, the `succ d` case has
the IH

```lean
ih : ∀ n, (crossBall d n).card = crossEhrhart d n
```

and the goal

```lean
(crossBall (d+1) n).card = crossEhrhart (d+1) n
```

By `crossEhrhart_succ_d` (already proved, `EhrhartCrossPolytope.lean:205`),

```
crossEhrhart (d+1) n = crossEhrhart d n + 2 * ∑ m ∈ range n, crossEhrhart d m.
```

So it suffices to show

```lean
(crossBall (d+1) n).card = crossEhrhart d n + 2 * ∑ m ∈ range n, crossEhrhart d m.   (⋆)
```

The path is:

1. **Slice** `crossBall (d+1) n` on its last coordinate, projecting via
   `fun y => y (Fin.last d) : (Fin (d+1) → Fin (2n+1)) → Fin (2n+1)`.
2. **Identify** each fiber over `j : Fin (2n+1)` with the filter set already
   counted by `fiber_card_eq_crossBall_card`, with budget
   `M_j := if j.val ≤ n then j.val else 2n - j.val` (= `n - cweight(j, n)`).
3. **Reorganize** the `∑ j : Fin (2n+1), (crossBall d M_j).card` by the
   pairing `j ↔ 2n - j`, folding it into the RHS of (⋆).

---

## 2. Three-Step Skeleton

### Step A: Slicing identity

```lean
private lemma crossBall_succ_d_slice (d n : ℕ) :
    (crossBall (d+1) n).card =
    ∑ j : Fin (2*n+1),
      (crossBall d (if j.val ≤ n then j.val else 2*n - j.val)).card
```

Proof idea: combine `Finset.card_eq_sum_card_fiberwise` (project on last coord)
with the bijection `Fin.init` between each fiber and the filter-set used by
`fiber_card_eq_crossBall_card`.

### Step B: Sum reorganization (j ↔ 2n - j pairing)

```lean
private lemma sum_crossBall_pair (d n : ℕ) :
    ∑ j : Fin (2*n+1),
        (crossBall d (if j.val ≤ n then j.val else 2*n - j.val)).card =
    (crossBall d n).card + 2 * ∑ m ∈ Finset.range n, (crossBall d m).card
```

Proof idea: convert `∑ j : Fin (2n+1) → ∑ j ∈ Finset.range (2n+1)` (via
`Fin.sum_univ_eq_sum_range`); split the range into `range n ∪ {n} ∪
{n+1, ..., 2n}`; reverse the high half via `Finset.sum_nbij'` with
`m ↦ 2n - m`.

### Step C: Wire into the main induction

```lean
| succ d ih =>
  intro n  -- IH is `induction d generalizing n`
  rw [crossBall_succ_d_slice, sum_crossBall_pair, ih n]
  rw [show ∀ m, (crossBall d m).card = crossEhrhart d m from ih]  -- inside the sum
  rw [crossEhrhart_succ_d]
```

(Modulo the `Finset.sum_congr` for the rewrite-under-binder step.)

Total: ~80–120 new lines.

---

## 3. Mathlib API Inventory (verified against `mathlib4` master, 2026-05-08)

| Lemma | Mathlib location | Statement |
|---|---|---|
| `Finset.card_eq_sum_card_fiberwise` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:979` | `(H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s \| f a = b}`. |
| `Fin.snoc` | `Mathlib/Data/Fin/Tuple/Basic.lean:506` | `(p : ∀ i : Fin n, α i.castSucc) (x : α (last n)) (i : Fin (n + 1)) : α i`. |
| `Fin.init` | `Mathlib/Data/Fin/Tuple/Basic.lean` | Drop last coord. |
| `Fin.init_snoc` | `Mathlib/Data/Fin/Tuple/Basic.lean:511` | `init (snoc p x) = p`. |
| `Fin.snoc_init_self` | `Mathlib/Data/Fin/Tuple/Basic.lean:593` | `snoc (init q) (q (last n)) = q`. |
| `Fin.snoc_last` | `Mathlib/Data/Fin/Tuple/Basic.lean:530` | `snoc p x (last n) = x`. |
| `Fin.snoc_castSucc` | `Mathlib/Data/Fin/Tuple/Basic.lean:517` | `snoc p x i.castSucc = p i`. |
| `Fin.sum_univ_castSucc` | `Mathlib/Algebra/BigOperators/Fin.lean` | `∑ i : Fin (n+1), f i = ∑ i : Fin n, f i.castSucc + f (last n)` (used in adjacent slicing). |
| `Fin.sum_univ_eq_sum_range` | `Mathlib/Algebra/BigOperators/Fin.lean` | `∑ i : Fin n, f i = ∑ k ∈ Finset.range n, f k` (with implicit nat cast). |
| `Finset.sum_nbij'` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | Bijection-based sum reindexing. |
| `Finset.range_eq_Ico` | `Mathlib/Order/Interval/Finset/Nat.lean` | `range n = Finset.Ico 0 n`. |
| `Finset.sum_Ico_consecutive` | `Mathlib/Algebra/BigOperators/Intervals.lean` | `∑ k ∈ Ico a b + ∑ k ∈ Ico b c = ∑ k ∈ Ico a c`. |
| `fiber_card_eq_crossBall_card` | `proofs/Proofs/EhrhartCrossPolytope.lean:387` (S4, PR #17008) | This repo's filter-set bijection. |
| `crossEhrhart_succ_d` | `proofs/Proofs/EhrhartCrossPolytope.lean:205` | This repo's geometric recursion. |

All Mathlib lemmas verified present in `mathlib4` master via `gh api` on 2026-05-08.

---

## 4. Step A Detail: `crossBall_succ_d_slice`

### 4.1 Setting up the fiberwise sum

```lean
private lemma crossBall_succ_d_slice (d n : ℕ) :
    (crossBall (d+1) n).card =
    ∑ j : Fin (2*n+1),
      (crossBall d (if j.val ≤ n then j.val else 2*n - j.val)).card := by
  -- Step A.1: apply Finset.card_eq_sum_card_fiberwise with f := fun y => y (Fin.last d).
  have hMapsTo :
      ((crossBall (d+1) n) : Set _).MapsTo (fun y => y (Fin.last d))
        (Finset.univ : Finset (Fin (2*n+1))) := by
    intro y _; exact Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hMapsTo]
  -- Goal: ∑ j ∈ univ, ((crossBall (d+1) n).filter (fun y => y (Fin.last d) = j)).card
  --       = ∑ j : Fin (2n+1), (crossBall d M_j).card
  -- Step A.2: rewrite each fiber's cardinality via the inner bijection.
  apply Finset.sum_congr rfl
  intro j _
  exact crossBall_succ_d_fiber_card d n j
```

### 4.2 Per-fiber cardinality lemma

```lean
private lemma crossBall_succ_d_fiber_card (d n : ℕ) (j : Fin (2*n+1)) :
    ((crossBall (d+1) n).filter (fun y => y (Fin.last d) = j)).card =
    (crossBall d (if j.val ≤ n then j.val else 2*n - j.val)).card := by
  -- Define M_j and verify M_j ≤ n.
  set Mj : ℕ := if j.val ≤ n then j.val else 2*n - j.val with hMj
  have hMj_le : Mj ≤ n := by
    rcases le_or_lt j.val n with hjn | hjn
    · simp [hMj, if_pos hjn]
    · push_neg at hjn
      have : j.val < 2*n + 1 := j.is_lt
      simp [hMj, if_neg (not_le.mpr hjn)]
      omega
  -- Bridge to fiber_card_eq_crossBall_card via Fin.init.
  rw [← fiber_card_eq_crossBall_card d n Mj hMj_le]
  -- Goal: ((crossBall (d+1) n).filter (fun y => y (last d) = j)).card
  --       = (Finset.univ.filter (fun z : Fin d → Fin (2n+1) => Σ cweight(zᵢ, n) ≤ Mj)).card
  apply Finset.card_bij'
    -- Forward: y ↦ Fin.init y (drop last coord).
    (fun y _ => Fin.init y)
    -- Backward: z ↦ Fin.snoc z j (append j as last coord).
    (fun z _ => Fin.snoc z j)
    -- (1) Forward image lies in the filter set.
    (by
      intro y hy
      simp only [crossBall, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨hsum, hlast⟩ := hy
      -- Σ over Fin (d+1) splits via Fin.sum_univ_castSucc into init-sum + last term.
      rw [Fin.sum_univ_castSucc] at hsum
      -- Substitute y (last d) = j in the last summand.
      rw [hlast] at hsum
      -- The init-sum is exactly the cweight sum of `Fin.init y` (= `fun i => y i.castSucc`).
      -- The last summand equals cweight(j, n) = n - M_j (or M_j - cweight(j, n) by the if).
      sorry  -- ENat / Nat arithmetic to extract Σᵢ cweight(init y, n) ≤ M_j; ~10 lines.
      )
    -- (2) Backward image lies in the original fiber.
    (by
      intro z hz
      simp only [crossBall, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      refine ⟨?_, Fin.snoc_last⟩
      rw [Fin.sum_univ_castSucc, Fin.snoc_last]
      simp only [Fin.snoc_castSucc]
      -- Σ over castSucc indices = Σ over Fin d of cweight(z, n); add cweight(j, n).
      sorry  -- The Σ + cweight(j) ≤ n reverse inequality from hz : Σ ≤ M_j; ~10 lines.
      )
    -- (3) Left inverse: init ∘ snoc = id (after restoring last coord).
    (by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨_, hlast⟩ := hy
      -- snoc (init y) (y (last d)) = y by Fin.snoc_init_self; rewrite y (last d) = j first.
      rw [← hlast]
      exact Fin.snoc_init_self _
      )
    -- (4) Right inverse: init (snoc z j) = z by Fin.init_snoc.
    (by intro z _; exact Fin.init_snoc)
```

Three identified `sorry`s (each ≤10 lines):

| `sorry` | Statement | Approach |
|---|---|---|
| 1 | After `Fin.sum_univ_castSucc`, the init-sum is `Σ over Fin d of cweight((Fin.init y) ·, n) = Σᵢ cweight(y i.castSucc, n)`; the last term is `cweight(j, n)`; hence `Σᵢ cweight(init y i, n) ≤ Mj` follows from `Σᵢ cweight(y i, n) ≤ n`. | `omega` after `cweight_le_iff` to expose the linear bound. |
| 2 | Reverse direction: from `Σᵢ cweight(z i, n) ≤ Mj` and `cweight(j, n) = n - Mj`, deduce `Σ over Fin (d+1) ≤ n`. | Same `omega` + `Fin.sum_univ_castSucc` + `Fin.snoc_castSucc`. |

Total Step A: ~50 lines (lemma `crossBall_succ_d_slice` ~10 lines + lemma
`crossBall_succ_d_fiber_card` ~40 lines).

---

## 5. Step B Detail: `sum_crossBall_pair`

```lean
private lemma sum_crossBall_pair (d n : ℕ) :
    ∑ j : Fin (2*n+1),
        (crossBall d (if j.val ≤ n then j.val else 2*n - j.val)).card =
    (crossBall d n).card + 2 * ∑ m ∈ Finset.range n, (crossBall d m).card := by
  -- Step B.1: convert Fin sum to Nat range.
  rw [Fin.sum_univ_eq_sum_range]
  -- Goal: ∑ k ∈ range (2n+1), (crossBall d (Mₖ k)).card = ...
  -- where Mₖ k := if k ≤ n then k else 2n - k
  -- Step B.2: split range (2n+1) = range n ⊔ {n} ⊔ Ico (n+1) (2n+1).
  rw [show Finset.range (2*n+1) =
        Finset.range n ∪ {n} ∪ Finset.Ico (n+1) (2*n+1) from by
        ext k; simp [Finset.mem_range, Finset.mem_Ico]; omega]
  rw [Finset.sum_union (by simp [Finset.disjoint_iff_ne]; omega)]  -- split off {n}, Ico
  rw [Finset.sum_union (by simp [Finset.disjoint_iff_ne]; omega)]  -- split range n from {n}
  -- Three pieces:
  --   ∑ k ∈ range n, (crossBall d k).card     -- since k < n ⇒ Mₖ = k.
  --   (crossBall d n).card                     -- single point k=n; Mₙ = n.
  --   ∑ k ∈ Ico (n+1) (2n+1), (crossBall d (2n-k)).card  -- since k > n ⇒ Mₖ = 2n-k.
  -- Step B.3: simplify the if-then-else inside each piece.
  simp only [Finset.sum_singleton, if_pos (le_refl n)]
  rw [show ∀ k ∈ Finset.range n, (if k ≤ n then k else 2*n - k) = k from
        by intro k hk; simp [Finset.mem_range.mp hk |>.le]]  -- rewrite under range n
  rw [show ∀ k ∈ Finset.Ico (n+1) (2*n+1),
        (if k ≤ n then k else 2*n - k) = 2*n - k from
        by intro k hk; rcases Finset.mem_Ico.mp hk with ⟨h1, _⟩
           simp [if_neg (not_le.mpr (by omega : n < k))]]
  -- Step B.4: reindex the high half: m := 2n - k for k ∈ Ico (n+1) (2n+1) gives m ∈ range n.
  rw [show ∑ k ∈ Finset.Ico (n+1) (2*n+1), (crossBall d (2*n - k)).card =
        ∑ m ∈ Finset.range n, (crossBall d m).card from by
    apply Finset.sum_nbij' (fun k _ => 2*n - k) (fun m _ => 2*n - m) ?_ ?_ ?_ ?_ ?_
    · intro k hk; rcases Finset.mem_Ico.mp hk with ⟨h1, h2⟩
      simp [Finset.mem_range]; omega
    · intro m hm; rcases Finset.mem_range.mp hm with hm
      simp [Finset.mem_Ico]; omega
    · intro k hk; rcases Finset.mem_Ico.mp hk with ⟨h1, h2⟩; omega
    · intro m hm; rcases Finset.mem_range.mp hm with hm; omega
    · intro k _; rfl
    ]
  -- Step B.5: combine the two range-n sums.
  ring
```

One identified concern: `Finset.sum_nbij'` argument order. The 5-argument
form (target-set membership × inverse × left-inv × right-inv × value-eq)
is the modern Mathlib v4.26.0 form. Verify on prototype.

Total Step B: ~30 lines.

---

## 6. Step C Detail: Wire into `crossBall_card`

```lean
theorem crossBall_card (d n : ℕ) : (crossBall d n).card = crossEhrhart d n := by
  induction d generalizing n with
  | zero => simp [crossBall, crossEhrhart]
  | succ d ih =>
    rw [crossBall_succ_d_slice, sum_crossBall_pair]
    -- LHS = (crossBall d n).card + 2 * ∑ m ∈ range n, (crossBall d m).card
    -- Apply IH to each crossBall d ·  occurrence.
    rw [ih n]
    rw [Finset.sum_congr rfl (fun m _ => ih m)]
    -- LHS = crossEhrhart d n + 2 * ∑ m ∈ range n, crossEhrhart d m
    -- = crossEhrhart (d+1) n by crossEhrhart_succ_d.
    rw [← crossEhrhart_succ_d]
```

(Modulo Lean's handling of `Finset.sum_congr` under a binder: may need
`conv_lhs => rw [Finset.sum_congr rfl ...]` or a `show` step.)

Total Step C: ~10 lines (replaces the existing `succ d ih => sorry`).

---

## 7. Critical Path: 2 `sorry` placeholders + 1 unverified rewrite

| Item | What it proves | Approach | Lines |
|---|---|---|---|
| 1 | Forward image lies in filter set after `Fin.sum_univ_castSucc` split | `omega` after `cweight_le_iff` to expose the linear bound | 10 |
| 2 | Backward image satisfies the cweight ≤ n bound | Same `omega` + `Fin.snoc_castSucc` simplification | 10 |
| 3 | `sum_crossBall_pair` Step B.5 ring step | If `Finset.sum_nbij'` succeeds, `ring` should close. Possibly need a manual `linarith`. | (≤5 fallback) |

Each is mechanical Mathlib bookkeeping. None requires deep mathematical content.

**Total new code estimate**: ~90 lines.
**Build verification**: 1 Docker run with `LEAN_BUILD_TIMEOUT=60m`.

---

## 8. Edge Cases & Open Q's for S6

**Q1**: When `n = 0`, the slicing identity becomes
`(crossBall (d+1) 0).card = (crossBall d 0).card` (the only `j` is `0` and
`M_0 = 0`). `Finset.sum_singleton` collapses the sum. Verify the `n = 0`
case doesn't degenerate the `Ico` split. Likely needs a `match n with | 0 | n+1`
in `sum_crossBall_pair`, or an outer `rcases n` to handle `n = 0` via
`crossEhrhart_n0`.

**Q2**: `Finset.sum_nbij'` vs `Finset.sum_bij'` — the `nbij'` (named-variable
form) is preferred in recent Mathlib; verify both on prototype.

**Q3**: If `induction d generalizing n` produces a less-friendly IH form than
expected, fall back to `induction d with | zero => ... | succ d ih =>
intro n; ...` after stating the goal as `∀ n, (crossBall d n).card = ...`.

**Q4**: In Step C, the rewriting under the binder `∑ m ∈ range n,
(crossBall d m).card` may need `simp only [ih]` or explicit
`Finset.sum_congr rfl (fun m _ => ih m)`. Both should work; the prototype
will pick whichever Lean accepts.

**Q5 (advanced)**: After Step A is proved, `crossBall_succ_d_fiber_card`
provides a clean public lemma (analogous to `fiber_card_eq_crossBall_card`).
Could extract to a sibling `EhrhartCrossPolytope/Slicing.lean` module if
file size grows beyond 600 lines. Defer to S7.

---

## 9. Comparison with the Inline Sketch

The current docstring on `crossBall_card` (`EhrhartCrossPolytope.lean:476-490`)
gives a 5-line sketch. This spec provides:

* Concrete Mathlib API names (with file paths and line numbers verified against
  `mathlib4` master).
* Three-piece factoring: `crossBall_succ_d_slice`, `sum_crossBall_pair`,
  the main `crossBall_card` `succ d` case (the inline sketch lumped them all
  together).
* Exact line estimate (90 vs the inline "80–120").
* Two-`sorry` critical path (the inline sketch deferred all bookkeeping).
* `Fin.snoc` / `Fin.init` / `Fin.snoc_init_self` as the bijection foundation
  (the inline sketch said "via the cweight translation" without specifying the
  index manipulation API).

---

## 10. Build Infrastructure Reminder

`proofs/.lake -> proofs/.lake` recursive symlink (memory
`feedback_researcher_lake_symlink_broken`) makes every Docker build a 30–45 min
Mathlib clone + 10 min cache fetch. S6 should:

1. Run a single Docker build with `LEAN_BUILD_TIMEOUT=60m` to prototype the
   slicing decomposition end-to-end.
2. Or wait for symlink repair (separate mechanic/auditor session can address).

---

## 11. Recommended Session Sequence (revised)

* **S6** (1–2 hr): Prototype Steps A + B + C per §4–6 skeletons; resolve the
  2 mechanical `sorry`s + 1 binder-rewrite step.
* **S7** (post-build verify): Promote `meta.json` `sorryCount` 1→0,
  `status: verified`, `badge: original`. Update gallery entry annotations
  (15-row API table, including the 13 lemmas now in `EhrhartCrossPolytope.lean`).
* **S8** (optional): Connection to Delannoy numbers (open question 2 in the
  file's "Open Questions Generated" docstring).

---

## Provenance

- Mathlib source files inspected via `gh api repos/leanprover-community/mathlib4/contents/...`
  on 2026-05-08:
  - `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (lines 977–989)
  - `Mathlib/Data/Fin/Tuple/Basic.lean` (lines 505–595)
- Repo helpers `cweight_le_iff`, `cweight_translate`, `cweight_sum_individual`,
  `cweight_sum_range`, `fiber_card_eq_crossBall_card` taken from
  `EhrhartCrossPolytope.lean:336–468` on `origin/main` post-PR #17008
  (S4 merged 2026-05-08).
- `crossEhrhart_succ_d` taken from `EhrhartCrossPolytope.lean:205` on `origin/main`.
- `crossBall_card` `succ d` sorry at `EhrhartCrossPolytope.lean:493` on `origin/main`.
