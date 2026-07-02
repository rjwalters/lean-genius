# Knowledge Base: ramsey-r4k-oq-05

## Question

Generalize the parent's `ramsey_recursion` to the full Erdős–Szekeres upper
bound `R(r,s) ≤ C(r+s-2, r-1)` by induction on `r + s`, using Pascal's identity.

## Status — RESOLVED (VERIFIED, 0-axiom), researcher-2, 2026-07-02

**Answer: YES.** `proofs/Proofs/RamseyR4kOQ05.lean` (126 lines, 4 theorems,
0 axioms, 0 sorries) proves, over the parent's `RamseyProp`/`ramseyUpperBound`
API (`import Proofs.RamseyR4k`):

- `ramseyProp_erdos_szekeres (r s) (1≤r) (1≤s) : RamseyProp (C(r+s-2, r-1)) r s`
- `ramseyProp_ramseyUpperBound` — same, phrased via `ramseyUpperBound r s`
- `ramseyProp_r4k (k) (1≤k) : RamseyProp (C(k+2,3)) 4 k` — recovers the parent's
  R(4,k) ≤ C(k+2,3) as an actual Ramsey guarantee (consistency check).

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]` only.

## Proof recipe

Strong induction on `r + s` via a bound variable `N` (`ramseyProp_erdos_szekeres_aux`).

- **Base r = 1:** `C(s-1, 0) = 1` (simp), `ramseyProp_one_left 1 s le_rfl`.
- **Base s = 1:** `C(r-1, r-1) = 1` (`Nat.choose_self` after `r+1-2 = r-1` by omega),
  `ramseyProp_one_right 1 r le_rfl`.
- **Step r,s ≥ 2:** IH on `(r-1,s)` → `C(r+s-3, r-2)` vertices, IH on `(r,s-1)` →
  `C(r+s-3, r-1)` vertices. Normalize all indices to `r+s-3` (omega), combine with
  `ramsey_recursion`, then Pascal `Nat.choose_succ_succ'` rewrites the sum
  `C(r+s-3,r-2)+C(r+s-3,r-1)` as `C(r+s-2,r-1)` — closing by rfl once the
  `(·)+1` successor forms line up (`r+s-2 = (r+s-3)+1`, `r-1 = (r-2)+1`).

The only friction is Nat subtraction bookkeeping; omega handles every index identity.

## Build notes (infra)

- Parent olean must be built to import it: `ulimit -s 65520` before
  `lake env lean -o .../RamseyR4k.olean Proofs/RamseyR4k.lean`. Without the raised
  stack, olean serialization stack-overflows (exit 139, looks like a segfault).
- Verify child + axioms the same way (`-o` build under raised stack, then a tiny
  in-`proofs/` checker file with `#print axioms`).

## Follow-ups (not pursued — depth guard)

This slug is at OQ depth 1 (`ramsey-r4k-oq-05`), so follow-ups are allowed, but the
natural next steps are substantial: the Erdős probabilistic lower bound
`R(k,k) ≥ 2^{k/2}` over the same API, or the recent `(4-ε)^k` upper bound.
