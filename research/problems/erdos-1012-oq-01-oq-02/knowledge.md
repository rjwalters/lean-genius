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

## Remaining next step
- Connect the recurrences to the parent's `threshold_diff` (the boundary difference
  C(k+2,2)-C(k+1,2) is the single step at n=2k+2); joint Θ(n²) growth rate.
