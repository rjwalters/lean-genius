# Knowledge Base: erdos-1012-oq-01-oq-02

COMPLETE. Structural arithmetic of the Woodall edge threshold
`edgeThreshold n k = C(n-k-1,2) + C(k+2,2) + 1` (child of erdos-1012-oq-01).

## n-direction (prior sessions)
- `edgeThreshold_eq` explicit polynomial form.
- `edgeThreshold_succ_left`: recurrence, adding a vertex raises threshold by n-k-1 (n≥k+1).
- `edgeThreshold_lt_succ` / `edgeThreshold_mono`: strict/weak monotonicity in n.
- `edgeThreshold_le_choose_two` / `..._add_surplus_eq_choose_two` / `..._lt_choose_two`:
  non-degeneracy vs C(n,2) (exact surplus k(k+2)+(n-(2k+3))(k+1), degenerate only at (0,3)).

## k-direction (researcher-1, 2026-07-08)
The complementary variation in k (n fixed). Both binomials move oppositely as k grows, so
the discrete k-derivative is the **signed** quantity `2k+4-n`:

- `edgeThreshold_succ_right (n k) (h : k+2 ≤ n) : edgeThreshold n (k+1) + n = edgeThreshold n k + (2k+4)`
  — subtraction-free ℕ identity for the k-recurrence (derivative 2k+4-n). Proof: unfold,
  rewrite n-k-1 = (n-k-2)+1, n-(k+1)-1 = n-k-2, k+1+2 = (k+2)+1, apply `choose_two_succ`
  to both, then `omega`.
- `edgeThreshold_succ_right_le (h : 2k+4 ≤ n) : edgeThreshold n (k+1) ≤ edgeThreshold n k`
  — decreasing branch.
- `edgeThreshold_le_succ_right (k+2 ≤ n ≤ 2k+4) : edgeThreshold n k ≤ edgeThreshold n (k+1)`
  — increasing branch.

Together: the threshold is **U-shaped (convex) in k** for fixed n, minimized near
`k = (n-4)/2`. Both branches follow from the recurrence by `omega` (ET terms as atoms,
sign of 2k+4-n from the range hypothesis).

VERIFIED 0 axioms (propext/Quot.sound only) / 0 sorries, no native_decide. First-try build.

## threshold_diff connection + Θ(n²) growth (researcher-2, 2026-07-08, PR #36084)
Closed the documented remaining next step. 6 new theorems, VERIFIED 0 axioms / 0 sorries,
no native_decide (Docker green, 7744 jobs).

Boundary-difference bridge (parent `threshold_diff` = `C(k+2,2)-C(k+1,2)`, evaluated):
- `choose_two_diff_succ (k) : C(k+2,2) - C(k+1,2) = k+1` — the parent's abstract RHS,
  computed. Gotcha: `choose_two_succ (k+1)` yields `(k+1+1).choose 2`, which omega
  atomizes separately from `(k+2).choose 2`; `rw [show k+1+1 = k+2 by omega] at h` first.
- `edgeThreshold_boundary_step (k) : edgeThreshold (2k+3) k = edgeThreshold (2k+2) k + (k+1)`
  — the n-recurrence's derivative `n-k-1` evaluated at n=2k+2 (via `edgeThreshold_succ_left`).
- `threshold_diff_eq (k) : edgeThreshold (2k+3) k - edgeThreshold (2k+2) k = k+1` — closes
  the loop: the abstract binomial difference and the recurrence both give k+1.

Θ(n²) growth (quadratic sandwich):
- `two_mul_edgeThreshold (h : k+2 ≤ n) : 2·edgeThreshold n k = (n-k-1)(n-k-2)+(k+2)(k+1)+2`
  — subtraction-free doubled closed form (reuses `two_mul_choose_two`).
- `edgeThreshold_quadratic_lower (h : k+2 ≤ n) : (n-k-1)(n-k-2) ≤ 2·edgeThreshold n k`.
- `edgeThreshold_quadratic_sandwich (h : 2k+3 ≤ n) : (n-k-1)(n-k-2) ≤ 2·edgeThreshold n k
  ≤ n(n-1)` — two-sided quadratic bound (upper reuses `edgeThreshold_le_choose_two`),
  so the threshold grows like ½n², the same rate as C(n,2).

The next step is now COMPLETE; no obvious further elementary arithmetic remains for this
child (the n- and k-recurrences, non-degeneracy, boundary connection, and growth rate are
all recorded). Deeper work belongs to the parent (Woodall's f(k) axioms).
