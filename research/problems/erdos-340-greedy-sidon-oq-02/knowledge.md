# Knowledge Base: erdos-340-greedy-sidon-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal (OQ-02).** Remove the lone axiom of the parent gallery entry
`erdos-340-greedy-sidon`:

```lean
axiom sidon_upper_bound (A : Finset ℕ) (hA : IsSidon A) (N : ℕ)
    (hAN : ∀ a ∈ A, a ≤ N) :
    A.card ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 1
```

This is the sharp **Erdős–Turán** upper bound for a Sidon set in `{1,…,N}`. The
parent proves only the *weak* difference-counting bound
`sidon_upper_bound_weak : |A| ≤ √(2N)+1`, then postulates the sharp form.

`IsSidon A` (parent def) means: `∀ a b c d ∈ A, a ≤ b → c ≤ d → a+b=c+d → a=c ∧ b=d`
(distinct-sums form; equivalently distinct positive differences).

---

## Current Lean state (`proofs/Proofs/Erdos340GreedySidonOQ02.lean`, 186 lines)

The file implements the sliding-window / Cauchy–Schwarz argument
(Erdős–Turán, Lindström form). Fully proved **unconditionally**:

- `isSidon_image_add`, `card_image_add` — translation invariance (shift `A ↦ A+ℓ`
  so every element lands in `[ℓ, N+ℓ]`).
- `windowCount B ℓ x := (B.filter (fun b => x < b ∧ b ≤ x+ℓ)).card`.
- **`window_sum_identity`** (counting fact A):
  `∑_{x<M} windowCount B ℓ x = ℓ·|B|` when `B ⊆ [ℓ,M]`. PROVED.
- **`sidon_window_key`** (the Cauchy–Schwarz assembly): for a Sidon `A ⊆ {0,…,N}`
  and any `ℓ ≥ 1`, `ℓ·|A|² ≤ (N+ℓ)·(ℓ-1+|A|)`. PROVED, *conditional on* the one
  remaining lemma below. Uses `Finset.sq_sum_le_card_mul_sum_sq` (Cauchy–Schwarz).

**The single remaining `sorry` (line 123):**

```lean
theorem window_pair_bound (B : Finset ℕ) (ℓ M : ℕ) (hℓ : 1 ≤ ℓ)
    (hBsid : IsSidon B) (hB : ∀ b ∈ B, ℓ ≤ b ∧ b ≤ M) :
    ∑ x ∈ range M, windowCount B ℓ x * (windowCount B ℓ x - 1) ≤ ℓ * (ℓ - 1) := by
  sorry
```

This is counting fact **(B)**: the total number of ordered pairs sharing a window,
weighted, is `≤ ℓ(ℓ-1)`. It is *known finite combinatorics, not the open
problem*. Closing it makes the OQ-02 file 0-sorry; combined with optimising
`ℓ ≈ √N` (a further, separate step) it discharges the parent axiom.

---

## COMPLETE PROOF of `window_pair_bound` (formalization roadmap)

Notation: `W x := B.filter (fun b => x < b ∧ b ≤ x+ℓ)`, so `windowCount B ℓ x = (W x).card`.

**Step 1 — pairs inside a window.** `n·(n-1) = |s.offDiag|` for `n = s.card`:
`windowCount * (windowCount - 1) = (W x).offDiag.card` via `Finset.offDiag_card`
(`s.offDiag.card = s.card * (s.card - 1)`).

**Step 2 — push the filter through `offDiag`.** Since `W x = B.filter Q` with
`Q b = (x<b ∧ b≤x+ℓ)`:
`(W x).offDiag = B.offDiag.filter (fun p => Q p.1 ∧ Q p.2)`
— proved by `ext ⟨a,b⟩; simp [Finset.mem_offDiag, Finset.mem_filter]; tauto`.

**Step 3 — Fubini (swap the two sums).**
```
∑_{x∈range M} (W x).offDiag.card
  = ∑_{x} ∑_{p∈B.offDiag} (if Q x p.1 ∧ Q x p.2 then 1 else 0)   -- Finset.card_filter
  = ∑_{p∈B.offDiag} ∑_{x∈range M} (if … then 1 else 0)          -- Finset.sum_comm
  = ∑_{p∈B.offDiag} cov p
```
where `cov (a,b) := ((range M).filter (fun x => (x<a∧a≤x+ℓ)∧(x<b∧b≤x+ℓ))).card`.

**Step 4 — windows covering a fixed pair.** For `(a,b) ∈ B.offDiag` (so `a≠b`,
`a,b ∈ [ℓ,M]`): the covering `x` satisfy `x < min a b` and `max a b - ℓ ≤ x`; all
such `x` automatically lie in `range M` (`x < min ≤ M`, `x ≥ max-ℓ ≥ 0`). Hence
the filtered set equals `Finset.Ico (max a b - ℓ) (min a b)` (prove by `ext x;
simp; omega` using `hB`), and by `Nat.card_Ico`:
`cov (a,b) = min a b - (max a b - ℓ) = ℓ - |a-b|`  (ℕ-truncated; `= 0` when `|a-b| ≥ ℓ`).

So `∑_{x} windowCount·(windowCount-1) = ∑_{(a,b)∈B.offDiag} (ℓ - |a-b|)`.

**Step 5 — regroup by difference using the Sidon property.** Reuse parent infra
(`Proofs.Erdos340GreedySidon`):
- `orderedPairsLt B := B.offDiag.filter (fun p => p.1 < p.2)`,
- `pairDiff p := p.2 - p.1`,
- `sidon_pairDiff_injective : Set.InjOn pairDiff (orderedPairsLt B)` — **already proved**
  (built on `IsSidon.diff_injective`).

Split `B.offDiag` by orientation; the swap `(a,b)↦(b,a)` is a difference-preserving
bijection `orderedPairsLt ↔ orderedPairsGt`, giving
`∑_{(a,b)∈B.offDiag}(ℓ-|a-b|) = 2·∑_{p∈orderedPairsLt B}(ℓ - pairDiff p)`
(`Finset.sum_bij` on the swap; `B.offDiag = orderedPairsLt ⊎ orderedPairsGt`).

By injectivity (`Finset.sum_image` / `card_image_of_injOn`):
`∑_{p∈orderedPairsLt B}(ℓ - pairDiff p) = ∑_{d ∈ (orderedPairsLt B).image pairDiff}(ℓ - d)`.
The image is a set of *distinct positive* naturals; terms with `d ≥ ℓ` vanish, and
`image ∩ Ico 1 ℓ ⊆ Ico 1 ℓ`, so by `Finset.sum_le_sum_of_subset_of_nonneg`:
`≤ ∑_{d ∈ Finset.Ico 1 ℓ}(ℓ - d) = ∑_{k=1}^{ℓ-1} k = ℓ(ℓ-1)/2`
(reindex `d ↦ ℓ-d`; Gauss sum `Finset.sum_range_id_mul_two` / `Gauss_sum`).

Therefore the total `= 2·(ℓ(ℓ-1)/2) = ℓ(ℓ-1)`. ∎

The only orientation-handling piece without a ready-made lemma is the
factor-2 swap in Step 5; an alternative packaging is the single injection
`φ(a,b) = (|a-b|, decide (a<b)) : B.offDiag ↪ Ico 1 ℓ × Bool`, whose injectivity
follows from `IsSidon.diff_injective` (difference ⇒ unordered pair) plus the
orientation bit, bounding the sum by `∑_{Ico 1 ℓ × Bool}(ℓ-d) = ℓ(ℓ-1)` directly.

---

## Insights

- **The crux (distinct differences) is already formalized in the parent**
  (`IsSidon.diff_injective`, `sidon_pairDiff_injective`). OQ-02 does **not** need
  to reprove it — only to plug it into a double-counting/Gauss-sum assembly.
- `window_pair_bound` is `HARD` (known result), **not** `OPEN`. It is the correct
  target for Aristotle `prove_file` once the backend is reachable.
- Closing it gives a 0-sorry OQ-02 file but does **not** by itself remove the
  parent axiom: the `ℓ ≈ √N` optimisation that turns `sidon_window_key` into the
  `√N + √√N + 1` bound is a separate (elementary but fiddly) ℕ-arithmetic step.

## Dead Ends

- Bounded/`interval_cases` enumeration cannot reach this — it is a genuine
  infinite family. The window/Cauchy–Schwarz route in the file is the right one.

---

## Session 2026-06-18 (Session 2) — researcher-12

**Mode**: REVISIT (claimed from pool) · **Outcome**: progress (ORIENT→ACT roadmap; verification blocked by infra)

### What I did
- Confirmed the OQ-02 file's structure: only `window_pair_bound` (line 123) is open;
  `sidon_window_key` and `window_sum_identity` are fully proved.
- Located the reusable parent infrastructure that supplies the Sidon crux
  (`IsSidon.diff_injective` L109, `sidon_pairDiff_injective` L165, `orderedPairsLt`,
  `pairDiff`) — established it removes the hardest sub-goal.
- Worked out and recorded the **complete** Step 1–5 proof above (offDiag pairs →
  filter pushthrough → Fubini → `cov = ℓ-|a-b|` via `Ico`/`Nat.card_Ico` →
  Sidon-injective regrouping → Gauss sum `ℓ(ℓ-1)`), with exact Mathlib API.

### Why no verified Lean this session
- Aristotle backend returned `"Resource not found"` on `prove_file` (down).
- Docker build host saturated: 9 `lean-build-*` containers, load avg ≈ 20, and the
  parent `Erdos340GreedySidon.olean` is **not** cached, so a build would compile the
  full parent+deps — irresponsible to add on a load-20 host. Did not build.

### Next steps
1. Submit the file to Aristotle `prove_file` when the MCP backend recovers — this
   single HARD sorry is exactly its sweet spot.
2. Or hand-formalize Steps 1–5 above (≈120–180 lines) in a warm-cache, low-load
   window; build with `./proofs/scripts/docker-build.sh Proofs.Erdos340GreedySidonOQ02`.
3. After 0-sorry: add the `ℓ ≈ √N` optimisation to derive the sharp bound and
   discharge `axiom sidon_upper_bound` in the parent; flip parent meta
   `axiomatized/axiom → verified` (axiomCount 1 → 0).

---

## RESOLUTION (iter 3, 2026-06-18) — file complete; axiom NOT removable this way

`window_pair_bound` was closed and the companion landed on `main` (#25945, commit
`cdc8c8ceefc`): `Erdos340GreedySidonOQ02.lean` is now **0-sorry / 0-axiom**, proving
`sidon_window_key : ℓ·|A|² ≤ (N+ℓ)(ℓ-1+|A|)` for all `ℓ ≥ 1`.

### The step-3 plan above (discharge `sidon_upper_bound` via `ℓ ≈ √N`) is INVALID
Numerically optimising the proved key inequality over all integer `ℓ ≥ 1` (checked
N ≤ 3·10⁵) gives a best `|A|`-bound of ≈ **1.13·√N** asymptotically — correct order
`O(√N)` but a strictly larger lower-order term than the parent axiom's
`⌊√N⌋ + ⌊√⌊√N⌋⌋ + 1 ≈ √N + N^{1/4}`. Concretely:

| N      | key-inequality best `|A|` UB | axiom floor bound | optimal ℓ |
|--------|------------------------------|-------------------|-----------|
| 15     | 6                            | 5                 | 4         |
| 100    | 13                           | 14                | 21        |
| 1 000  | 38                           | 37                | 99        |
| 10⁴    | 115                          | 110               | 390       |
| 10⁶    | 1135                         | 1032              | 3978      |

The optimal `ℓ` is ≈ `4√N`, *not* `√N`, and even there the bound overshoots the floor
constant (gap grows to 105 by N ≈ 1.9·10⁵). The `∑ wc(wc-1) ≤ ℓ(ℓ-1)` bound in
`window_pair_bound` is itself **sharp** for Sidon sets (each difference `d < ℓ` occurs
≤ once ⇒ `2∑_{d<ℓ}(ℓ-d) = ℓ(ℓ-1)`), so the looseness is intrinsic to this Cauchy–Schwarz
route, not a slack to be tightened. Reaching `√N + N^{1/4}` needs the sharper Lindström
weighting — a different counting argument — so **`sidon_upper_bound` cannot be discharged
by optimising `sidon_window_key` over ℓ.** Treat parent axiom removal as a separate,
harder research line (or leave the entry honestly `axiomatized`).

Also note: the existing axiom-free `sidon_upper_bound_weak` (`|A| ≤ ⌊√(2N)⌋+1`,
difference-counting) already *beats* the key-inequality bound across the small/mid-N
range, so no derived explicit cardinality theorem from `sidon_window_key` was worth adding.

---

## Session 2026-06-19 (researcher-10): the optimisation IS worth formalizing — `sidon_card_le_sqrt`

The prior note above ("no derived explicit cardinality theorem from `sidon_window_key`
was worth adding") under-valued the **asymptotic** picture. The elementary
`sidon_upper_bound_weak` (`⌊√(2N)⌋+1`) beats the key-inequality bound only for small/mid
`N`; for large `N` the optimised key bound `√N + N^{1/4} + O(1)` is dramatically tighter
(optimal leading constant `1` vs `√2 ≈ 1.414`). That optimal leading term is worth a
verified theorem in its own right, so this session formalized it.

**New file `Erdos340SidonErdosTuran.lean`** (imports `Erdos340GreedySidonOQ02`):

```lean
theorem sidon_card_le_sqrt (A : Finset ℕ) (hA : IsSidon A) (N : ℕ)
    (hAN : ∀ a ∈ A, a ≤ N) :
    A.card ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 2
```

Fully **verified, 0-axiom** (`#print axioms` = `propext, Classical.choice, Quot.sound`).

* **Window length.** Optimum of `ℓ·k² ≤ (N+ℓ)(ℓ-1+k)` is `ℓ* = √((k-1)N) ≈ N^{3/4}`
  when `k ≈ √N` (NOT `≈√N`). The clean integer choice `ℓ = ⌊√N⌋·⌊√⌊√N⌋⌋ + 1` works.
* **Why `+2` not `+1`.** Confirmed by exhaustive search (`N < 3·10⁵`): with
  `s=⌊√N⌋, t=⌊√s⌋`, the value `k = s+t+3` is ALWAYS refuted by some `ℓ` (so `k ≤ s+t+2`
  is provable), but `k = s+t+2` survives for ~12% of `N` (e.g. `N=15`: key permits `6`,
  true max is `5`). The Cauchy–Schwarz step is intrinsically lossy by `+1`. **The parent
  axiom `sidon_upper_bound` (the `+1` form) therefore stays — it is not a slack of this
  route.** (Corroborates the prior session's conclusion.)
* **Arithmetic core (`window_opt_arith`, over ℤ).** By-contradiction with `k=s+t+3+d`,
  `N` at worst case `s²+2s`: the gap factors as
  `Q = (s·t+1)d² + C₁·d + (s+t+2)·R`, `R = -s²+st²+3st-2s+t+3 ≥ 1`. `R ≥ 1` is the
  concavity certificate `2t·R = (t²+2t-s)·e₀ + (s-t²)·e₁ + 2t(s-t²)(t²+2t-s)` with
  endpoints `e₀ = 3t³-2t²+t+3 ≥ 1`, `e₁ = (t-1)²(t+2)+1 ≥ 1`. `C₁ ≥ 0` via
  `s·(t²+2t-s) ≥ 0`. Each step is a low-degree `nlinarith`. Bracketings: `Nat.sqrt_le'`,
  `Nat.lt_succ_sqrt'`.
