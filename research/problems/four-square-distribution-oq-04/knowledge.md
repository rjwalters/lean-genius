# Knowledge Base: four-square-distribution-oq-04

Generalizing the four-square type-decomposition to r_{2k}(n) via the
hyperoctahedral (signed-permutation) group B_{2k} = S_{2k} ⋉ (Z/2)^{2k}.

---

## Problem Understanding

The gallery proof `four-square-distribution` (the 2k = 4 case) writes
r_4(n) = Σ over "ordering types" of an orbit size 2^{#nonzero}·4!/∏m_i!. The seeker
stub (problem.md) asks: does this orbit–stabilizer bookkeeping generalize to
r_{2k}(n) under B_{2k} = S_{2k} ⋉ (Z/2)^{2k}, |B_{2k}| = (2k)!·2^{2k} (e.g.
|B_8| = 8!·2^8 = 10,321,920)? The arithmetic value of the total (Jacobi) is taken
as input; the open contribution is the purely group-theoretic orbit count.

---

## Insights

### Session 2026-06-15 (ORIENT) — the generalization holds; formula + bearers pinned

**Mode**: FRESH · **Outcome**: ORIENT (answer + exact durable verification; Lean
ACT is Docker-gated and scoped below).

**Answer: YES, verbatim, for every 2k.** Model a representation as a tuple
`x = (x_1,…,x_{2k}) ∈ Z^{2k}` with `Σ x_i² = n`. B_{2k} acts by permuting
coordinates and flipping signs. The orbits are exactly the **shape classes** (the
multiset of absolute values `{|x_i|}`), and for a shape `s` with `z` zero parts
and distinct-absolute-value multiplicities `{m_i}` (0 included, so `Σ m_i = 2k`):

        orbit(s)  =  2^(2k − z) · (2k)! / ∏_i (m_i!)
                  =  2^(#nonzero parts) · multinomial(2k; multiplicities),     (★)

        r_{2k}(n) =  Σ_{shapes s of n}  orbit(s).                              (DECOMP)

By orbit–stabilizer the stabilizer of a shape-`s` representation has order

        |stab(s)|  =  |B_{2k}| / orbit(s)  =  2^z · z! · ∏_{nonzero} (m_j!).    (STAB)

**Reading of (STAB) — the key subtlety for a Lean ACT.** The stabilizer is *not*
the full Young-subgroup `∏ m_i!`: of the `2^{2k}` sign flips, only the `2^z` flips
on the **zero** coordinates fix the tuple (flipping a 0 does nothing); flipping any
nonzero coordinate changes `x_i ↦ −x_i ≠ x_i`. So the sign group contributes `2^z`,
the permutations contribute `z!` (permuting the zeros) times `∏_{nonzero} m_j!`
(permuting equal nonzero values). The `2^z` zero-sign degeneracy is exactly why the
orbit carries `2^{#nonzero}` and not `2^{2k}`. Mishandling zeros is the one place a
naive `card B / Young-subgroup` computation goes wrong.

**Durable artifact** `verify_hyperoctahedral_2k.py` (stdlib, exact integers, all
checks PASS): for `2k ∈ {2,4,6,8}` and `n` up to `{300,200,120,80}` it checks
(a) the orbit formula (★) against an INDEPENDENT brute count of signed orderings;
(b) `orbit(s)·|stab(s)| = |B_{2k}|` (orbit–stabilizer) for every shape;
(c) `Σ_shapes orbit = r_{2k}(n)` where `r_{2k}` is computed independently by
convolving the single-coordinate signed-square distribution; plus anchors
`r_2 = 4(d_1−d_3)` and `r_4 = 8σ*` against the convolutional totals. Worked example
`n=30, 2k=4`: shapes `(0,1,2,5)→orbit 192, stab 2` and `(1,2,3,4)→orbit 384,
stab 1`, summing to `r_4(30)=576`.

**Mathlib bearers for the ACT (confirmed by code search at HEAD).**
- `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
  (`Mathlib/GroupTheory/GroupAction/Quotient.lean`) — the orbit-size = |G|/|stab|
  engine; gives (★) once the action and stabilizer order are in place.
- `MulAction.orbitEquivQuotientStabilizer` (`Mathlib/GroupTheory/Index.lean`).
- `Nat.sum_four_squares` (existence). The signed-permutation group itself has **no
  Mathlib name** (`hyperoctahedral` = 0 hits): B_{2k} must be assembled as
  `Equiv.Perm (Fin (2k))` acting on `Fin (2k) → ℤ` together with sign flips
  `(ZMod 2)^{2k}` (or directly as the relevant `MulAction`).

---

## Next steps

1. **ACT (Lean, Docker-gated).** For a FIXED small `m = 2k ∈ {4,6,8}` (avoids the
   parametric semidirect-product construction): define the `MulAction` of
   `Equiv.Perm (Fin m) × (Fin m → Multiplicative (ZMod 2))` on `{f : Fin m → ℤ //
   Σ f² = n}`, compute `|stab|` for a shape via the zero/ nonzero split above, and
   invoke `card_orbit_mul_card_stabilizer_eq_card_group` to land (★). Reuse the
   parent's `RepType` shape machinery for the sorted-representative side.
2. **Honest obstruction.** As in the 2k=4 parent, (DECOMP) `r_{2k} = Σ orbit`
   needs the orbit partition of the full representation set, i.e. "every signed
   ordering lies in exactly one shape orbit" — a `MulAction` partition argument,
   not the orbit-size formula. That partition (not (★)) is the real Lean work; the
   parent discharged it only case-by-case for small `n`.
3. Optionally record the matching arithmetic inputs (r_6, r_8 Jacobi/modular
   formulas) so the decomposition can be stated with an explicit total.

## Dead Ends / Non-starters

- A fully *parametric in k* Lean proof is overkill for a first ACT: building
  `B_{2k}` as a generic semidirect product and computing its order/action is
  heavier than fixing `m ∈ {4,6,8}` and proving each by `decide`-friendly finite
  group actions.
- Treating the stabilizer as the full Young subgroup `∏ m_i!` (forgetting the
  `2^z` zero-sign factor) gives the wrong orbit size — the verifier rejects it.
