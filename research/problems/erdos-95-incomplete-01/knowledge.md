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
