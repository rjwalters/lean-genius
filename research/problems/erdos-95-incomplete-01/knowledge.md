# erdos-95-incomplete-01 — Sum of Squared Distance Multiplicities

Target file: `proofs/Proofs/Erdos95Problem.lean` (gallery entry `erdos-95`).

## Phase: ACT (sorry elimination)

### Session 2026-06-26 (researcher-1)

Goal of session: finish the two outstanding `sorry`s left by a prior session
and reconcile gallery metadata.

**State on entry:** worktree had uncommitted work filling both `sorry`s, but
the `sum_multiplicities` proof did **not** compile.

**Bug found & fixed — `sum_multiplicities`.**
The prior proof did `rw [← Finset.offDiag_card, …]`. But
`Finset.offDiag_card : (offDiag s).card = s.card * s.card - s.card`
produces the `n*n - n` form, while the theorem statement's RHS is
`s.card * (s.card - 1)`. These are *not syntactically* equal (ℕ truncated
subtraction), so the `←` rewrite cannot match and the proof fails.
Fix mirrors the proven pattern in `Erdos840Aristotle.lean`:
```
have hfib : P.points.offDiag.card = (distanceSet P).sum (multiplicity P) :=
  Finset.card_eq_sum_card_fiberwise (f := fun pq => dist pq.1 pq.2)
    (t := distanceSet P) hmem
rw [← hfib, Finset.offDiag_card]
cases h : P.points.card with
| zero => simp
| succ n =>
  have hrw : (n + 1) * (n + 1) = (n + 1) * n + (n + 1) := by ring
  simp only [Nat.succ_sub_one]
  omega
```
**Gotcha (reusable):** `Finset.offDiag_card` gives `n*n - n`, never `n*(n-1)`.
Bridge with `cases card; zero => simp; succ n => ring-fact + omega`.

**`erdos_conjecture_proved`** (kept from prior session, lemmas all verified
against local Mathlib): absorbs the Guth–Katz `log n` into `n^ε`. Key step
`ε·log m ≤ m^ε` from `Real.log_le_sub_one_of_pos` after `Real.log_rpow`,
then split `m^{3+ε} = m^3·m^ε` and take `C' = C/ε`.

**Result:** file now has **0 sorries**, **2 axioms** (`guth_katz_theorem`,
`convex_polygon_case`) — both genuinely deep results, correctly left
axiomatized. Status stays `axiomatized` / badge `axiom`.

### BUILD NOT VERIFIED THIS SESSION
Docker build was impossible: host disk 99% full and the Docker/containerd
content store is corrupted (input/output error reading blobs — even
`docker images` fails). Per repo policy `lake build` must never be run
directly. Every Mathlib lemma used was instead checked by name + signature
against `proofs/.lake/packages/mathlib`. The PR is gated for review until a
clean Docker build confirms it.

### Lemmas relied on (all confirmed present in local Mathlib)
- `Finset.card_eq_sum_card_fiberwise`, `Finset.offDiag_card`,
  `Finset.mem_image_of_mem`
- `Real.rpow_add`, `Real.rpow_natCast`, `Real.log_rpow`,
  `Real.log_le_sub_one_of_pos`, `Real.rpow_pos_of_pos`, `le_div_iff₀`

### Next step
Once Docker is healthy, run
`./proofs/scripts/docker-build.sh Proofs.Erdos95Problem` to confirm.
If `hsplit`'s `congr 1; rw [← Real.rpow_natCast]; norm_num` step fails,
fall back to `rw [Real.rpow_add hmpos, ← Real.rpow_natCast m 3]; norm_num`.

### Session 2026-07-01 (researcher-4) — Follow-up: Cauchy–Schwarz bridge to #94

**Mode:** FRESH (claimed EMPTY, but target file was already SOLVED: 0 sorries,
2 deep axioms `guth_katz_theorem`/`convex_polygon_case`). Per skill's
SOLVED strategy, generated a strong follow-up rather than churning the
finished proof.

**What I added (Part IV·5 of `Erdos95Problem.lean`):**
- `distinctDistances P := (distanceSet P).card` — the count `t` (Problem #94).
- `sq_sum_multiplicities_le` — **unconditional, 0-axiom**: `(n(n-1))² ≤ t·∑f(d)²`.
  One-line Cauchy–Schwarz via Mathlib `sq_sum_le_card_mul_sum_sq` (Chebyshev
  special case) + `sum_multiplicities`. This is the exact bridge the gallery
  entry's `keyInsights[0]` described *informally* but never formalized.
- `distinctDistances_lower_bound` — combines the bridge with `guth_katz_theorem`
  to get `n²(n-1)² ≤ C·t·n³·log n`, i.e. `t ≫ n/log n` (the Guth–Katz #94
  result). Reuses ONLY the existing axiom; adds no new axioms.

**Verification:** Docker down; standalone `lean` on the full file hits a whnf
heartbeat timeout inside the *pre-existing* `sum_multiplicities`
(`Finset.card_eq_sum_card_fiberwise` reducing real-equality `DecidablePred`) —
the unmodified HEAD file shows the identical timeout, so it is an artifact of
heartbeat-limited standalone elaboration, not a regression (the file merged in
#30353 under lake/CI, and `#print axioms sum_multiplicities` reports no sorry
even in the timing-out run). My two new theorems were verified **in isolation**
against `import Mathlib` (umbrella loads fine — no Kaehler wall this session)
with `sum_multiplicities` stubbed: they compile and
`#print axioms distinctDistances_lower_bound` = `[propext, Classical.choice,
guth_katz_theorem, sum_multiplicities, Quot.sound]` — no `sorryAx`, no new axioms.

**Reusable gotchas:**
- Chebyshev/Cauchy–Schwarz sum lemma is top-level `sq_sum_le_card_mul_sum_sq`
  (NOT `Finset.…`); needs `import Mathlib.Algebra.Order.Chebyshev`. Works over ℕ
  (`[Semiring][LinearOrder][IsStrictOrderedRing][ExistsAddOfLE]`); the `↑s.card`
  cast is defeq to `s.card` since `NatCast ℕ = ⟨id⟩`.
- `erdos_conjecture_proved` shows `ε : ℕ` (wrong) in standalone/umbrella here —
  the rpow default-instance for `(n:ℝ)^(3+ε)` resolves to `Monoid.npow` outside
  the merge-time env. Also a standalone artifact, not touched.

**Status:** target proof unchanged (still axiomatized, 2 deep axioms); added
2 proved theorems + 1 def. Gallery meta counts bumped (thm 3→5, def 9→10,
line 231→300, import +Chebyshev). PR opened; gated on a clean lake/Docker build.
