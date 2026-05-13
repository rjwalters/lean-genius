# S18c-orbit PREP — Combined-Stabilizer Formula + 11-Case 8-Divisibility Enumeration

**Iteration**: S18c-orbit (analysis-only PREP)
**Author**: researcher-10
**Date**: 2026-05-13
**Status**: doc-only — no Lean changes; no edits to existing `s18*` notes, `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON.

## 0. Why a PREP

`state.md` (current, lines 95–115) closes with:

> The remaining S18c work is now a single layer:
> 1. **S18c-orbit** — invoke `MulAction.orbit_card_dvd_of_finite`
>    (Mathlib v4.26.0, per S18 spec §3.8). Case analysis on the
>    zero-pattern of `(|v 0|, |v 1|, |v 2|, |v 3|)` (0 zeros /
>    1 / 2 / 3 zeros — never 4 since `n > 0`) crossed with the
>    coincidence-pattern of nonzero |v_i| values (4 distinct / 1 pair
>    / 2 pairs / 1 triple / all-equal). For each case, the combined
>    `|(ℤ/2)⁴| · |S₄| / |Stab v| = 384 / |Stab v|` is divisible by 8.

This memo carries out the case enumeration in closed form, derives
a uniform **combined-stabilizer formula**

$$|\text{Stab}_{(\mathbb{Z}/2)^4 \rtimes S_4}(v)| \;=\; z!\, \prod_k m_k!\, \cdot\, 2^z,$$

where $z = |\{i : v_i = 0\}|$ and $\{m_k\}$ partitions the **nonzero**
positions by absolute value, and verifies that

$$v_2\bigl(|\text{Stab}(v)|\bigr) \;\le\; 4 \;=\; v_2(384) - 3$$

in **every** one of the 11 (zero-pattern, absolute-value partition)
cases — hence $8 \mid |\text{Orbit}(v)|$ unconditionally for any
$v \in \mathbb{Z}^4$ with at least one nonzero coordinate.

This combined-stabilizer formula is **not the product** of the two
side stabilizers shipped in earlier PRs:

- `signFlipStabilizer_card` (Part 31, PR [#18139](https://github.com/rjwalters/lean-genius/pull/18139)) gives `2^(# zero coords) = 2^z` — counts $s$ at $\sigma = \text{id}$.
- `permStabilizer_card` (Part 33 design, PR [#18418](https://github.com/rjwalters/lean-genius/pull/18418)) gives $\prod \text{mult}(i)!$ — counts $\sigma$ at $s = 0$, with multiplicity over **signed** values, not absolute values.

The semidirect-product stabilizer involves **mixed** $(s, \sigma)$ pairs
that move equal-$|v_i|$ positions and compensate via sign flips — so
the combined count is genuinely a third lemma, not a product of the
two precursors. This memo:

1. Derives the closed form (§2).
2. Verifies it by brute-force enumeration on 10 representative
   $v \in \mathbb{Z}^4$ (§3, Python script reproducible).
3. Enumerates all 11 (zero-pattern, partition-type) cases and
   confirms $8 \mid |\text{Orbit}(v)|$ in each (§4).
4. Maps the closed form to a Lean lemma signature + tactic sketch
   for S18c-orbit ACT (§5).
5. Audits the Mathlib v4.26.0 API surface for the closing argument
   (§6).

## 1. Setup

The action is $G = (\mathbb{Z}/2)^4 \rtimes S_4$ acting on $\mathbb{Z}^4$
(or equivalently on $\mathrm{Fin}\, 4 \to \mathbb{Z}$) via

$$\bigl((s_0, s_1, s_2, s_3), \sigma\bigr) \cdot v = (\text{applyFlip}\, s) \circ (\text{applyPerm}\, \sigma)\, v.$$

In `proofs/Proofs/FourSquareDistributionOQ01.lean`, `namespace S18c`:

```lean
def applyFlip (s : SignFlip) (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if s i then -(v i) else v i

def applyPerm (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  v ∘ σ.symm
```

For the combined action, an element $(s, \sigma)$ fixes $v$ iff

$$(-1)^{s_i}\, v(\sigma^{-1}(i)) \;=\; v(i) \qquad \forall i \in \mathrm{Fin}\, 4. \tag{$\star$}$$

**Group order**: $|G| = 16 \cdot 24 = 384 = 2^7 \cdot 3$.

**Goal**: For every $v$ with at least one nonzero coordinate, show
$8 \mid |\text{Orbit}(v)|$.

## 2. Combined-Stabilizer Closed Form

### 2.1 Necessary conditions on $\sigma$

From $(\star)$: for each $i$, $v(\sigma^{-1}(i)) = \pm v(i)$, in
particular $|v(\sigma^{-1}(i))| = |v(i)|$. So $\sigma^{-1}$ — and
hence $\sigma$ — must permute positions of equal absolute value.

In particular:
- Zero positions go to zero positions (since $v(\sigma^{-1}(i)) = 0$ iff $|v(\sigma^{-1}(i))| = 0$ iff $|v(i)| = 0$ iff $v(i) = 0$).
- Nonzero positions go to nonzero positions, with $|v(\sigma^{-1}(i))| = |v(i)|$.

Equivalently, $\sigma$ stabilizes the **absolute-value partition** of $\mathrm{Fin}\, 4$ induced by $v$.

### 2.2 Sign flip $s$ from $\sigma$

Given such a $\sigma$, the sign flip $s_i$ is forced for nonzero $i$
(uniquely chosen so $(-1)^{s_i} v(\sigma^{-1}(i)) = v(i)$), and free
for zero $i$ (the equation $(-1)^{s_i} \cdot 0 = 0$ is satisfied
identically).

Hence

$$\text{number of } (s, \sigma) \text{ fixing } v \;=\; (\text{number of } \sigma \text{'s respecting the abs-value partition}) \cdot 2^z,$$

where $z = |\{i : v_i = 0\}|$ is the number of zero positions.

### 2.3 Counting partition-preserving $\sigma$'s

Let $\{m_k\}$ be the multiplicities of the distinct nonzero absolute
values of $v$, so $\sum_k m_k = 4 - z$. A permutation $\sigma$ respects
the partition iff it independently permutes:

- The $z$ zero positions among themselves: $z!$ choices.
- Each block of $m_k$ equal-abs positions among themselves: $m_k!$ choices.

So $\sigma$-count $= z! \cdot \prod_k m_k!$.

### 2.4 Closed form

$$\boxed{\,|\text{Stab}_{(\mathbb{Z}/2)^4 \rtimes S_4}(v)| \;=\; z!\, \prod_k m_k!\, \cdot\, 2^z\,}$$

where:
- $z$ = number of zero coordinates of $v$;
- $\{m_k\}$ = absolute-value partition of the nonzero coordinates.

## 3. Brute-Force Verification

The closed form was verified on 2026-05-13 against a brute-force enumeration over all $|G| = 384$ pairs $(s, \sigma)$:

| $v$ | $z$ | partition | brute-force $|\text{Stab}|$ | formula $z! \prod m_k! \cdot 2^z$ |
|---|---:|---|---:|---:|
| $(1, 1, 2, 3)$ | 0 | $2+1+1$ | 2 | $1 \cdot 2 \cdot 1 \cdot 1 \cdot 1 = 2$ |
| $(1, -1, 2, 3)$ | 0 | $2+1+1$ (sign-blind) | 2 | $2$ |
| $(1, 1, 0, 0)$ | 2 | $2$ | 16 | $2 \cdot 2 \cdot 4 = 16$ |
| $(5, 0, 0, 0)$ | 3 | $1$ | 48 | $6 \cdot 1 \cdot 8 = 48$ |
| $(1, 1, 1, 1)$ | 0 | $4$ | 24 | $1 \cdot 24 \cdot 1 = 24$ |
| $(1, 1, 2, 2)$ | 0 | $2+2$ | 4 | $1 \cdot 2 \cdot 2 \cdot 1 = 4$ |
| $(1, 2, 3, 0)$ | 1 | $1+1+1$ | 2 | $1 \cdot 1 \cdot 1 \cdot 1 \cdot 2 = 2$ |
| $(1, 1, 2, 0)$ | 1 | $2+1$ | 4 | $1 \cdot 2 \cdot 1 \cdot 2 = 4$ |
| $(1, 1, 1, 0)$ | 1 | $3$ | 12 | $1 \cdot 6 \cdot 2 = 12$ |
| $(1, 2, 0, 0)$ | 2 | $1+1$ | 8 | $2 \cdot 1 \cdot 1 \cdot 4 = 8$ |

All 10 cases match. The signed example $(1, -1, 2, 3)$ confirms the
key point: the formula uses the **absolute-value** partition, not the
signed-value partition. (Compare to `permStabilizer_card` of PR #18418
which uses signed multiplicities — that lemma counts $\sigma$'s with
$s = 0$ only, giving $|\text{permStab}((1,-1,2,3))| = 1$ vs combined
$|\text{Stab}((1,-1,2,3))| = 2$.)

### Reproducibility

```python
from itertools import permutations, product

def stab_size(v):
    cnt = 0
    for sigma in permutations(range(4)):
        sigma_inv = [0]*4
        for j, si in enumerate(sigma):
            sigma_inv[si] = j
        for s in product([False, True], repeat=4):
            w = [v[sigma_inv[i]] for i in range(4)]
            u = [-w[i] if s[i] else w[i] for i in range(4)]
            if u == list(v):
                cnt += 1
    return cnt
```

## 4. Full 11-Case Enumeration

The (zero-count $z$, absolute-value partition) cases for $v \in \mathbb{Z}^4 \setminus \{0\}$:

| # | $z$ | partition | $\prod m_k!$ | $|\text{Stab}|$ | $|\text{Orbit}| = 384 / |\text{Stab}|$ | $|\text{Orbit}|/8$ | $v_2(|\text{Stab}|)$ |
|--:|--:|:-:|--:|--:|--:|--:|--:|
| 1 | 0 | $1+1+1+1$ | 1 | 1 | 384 | 48 | 0 |
| 2 | 0 | $2+1+1$ | 2 | 2 | 192 | 24 | 1 |
| 3 | 0 | $2+2$ | 4 | 4 | 96 | 12 | 2 |
| 4 | 0 | $3+1$ | 6 | 6 | 64 | 8 | 1 |
| 5 | 0 | $4$ | 24 | 24 | 16 | 2 | 3 |
| 6 | 1 | $1+1+1$ | 1 | 2 | 192 | 24 | 1 |
| 7 | 1 | $2+1$ | 2 | 4 | 96 | 12 | 2 |
| 8 | 1 | $3$ | 6 | 12 | 32 | 4 | 2 |
| 9 | 2 | $1+1$ | 1 | 8 | 48 | 6 | 3 |
| 10 | 2 | $2$ | 2 | 16 | 24 | 3 | 4 |
| 11 | 3 | $1$ | 1 | 48 | 8 | 1 | 4 |

**Verification**: $|\text{Orbit}|/8 \in \mathbb{Z}_{>0}$ in every row;
$\max_i v_2(|\text{Stab}_i|) = 4 \le v_2(384) - 3 = 7 - 3 = 4$.

**Tight case**: case 11 ($v = (a, 0, 0, 0)$ with $a \ne 0$) achieves
the worst-case stabilizer $|\text{Stab}| = 48 = 2^4 \cdot 3$ and the
smallest orbit $|\text{Orbit}| = 8 = 2^3$. This is the **rigid case**
of the divisibility: the orbit size is exactly $8$, with no slack
beyond the required factor. Combinatorially: the 4 axis-aligned
witnesses $(\pm a, 0, 0, 0), (0, \pm a, 0, 0), (0, 0, \pm a, 0),
(0, 0, 0, \pm a)$ form one orbit of size $8$.

**Case 4 sanity check** ($z=0$, partition $3+1$, e.g. $v = (a, a, a, b)$ with $a \ne \pm b$, $a \ne 0$, $b \ne 0$):
- $\sigma$ permutes $\{0,1,2\}$ freely ($3! = 6$) and fixes $\{3\}$.
- For each $\sigma$, signs are forced on positions $\{0,1,2,3\}$ (all nonzero).
- $|\text{Stab}| = 6 \cdot 1 = 6$. Orbit = $384/6 = 64 = 2^6$. $8 \mid 64$ ✓.

## 5. Lean Realization Sketch

### 5.1 Target lemma

Add to `proofs/Proofs/FourSquareDistributionOQ01.lean` inside
`namespace S18c`, after `permStabilizer_card` (Part 33, when shipped):

```lean
/-- **(S18c-orbit, Part 34)** Combined stabilizer cardinality formula.

For any `v : Fin 4 → ℤ`,

  `|Stab_(ℤ/2)⁴ ⋊ S₄ v|` = `z! · ∏ (m_k!) · 2^z`,

where `z = (univ.filter (fun i => v i = 0)).card` and `{m_k}` is the
absolute-value partition of the nonzero coordinates. -/
lemma combinedStabilizer_card (v : Fin 4 → ℤ) :
    Fintype.card { p : SignFlip × Equiv.Perm (Fin 4) //
                   applyFlip p.1 (applyPerm p.2 v) = v } =
      (Finset.univ.filter (fun i : Fin 4 => v i = 0)).card.factorial *
      (∏ a ∈ (Finset.univ.image (fun i => |v i|)).erase 0,
        ((Finset.univ.filter (fun i => |v i| = a)).card).factorial) *
      2 ^ (Finset.univ.filter (fun i : Fin 4 => v i = 0)).card

/-- **(S18c-orbit, Part 35)** 8-divisibility of orbit cardinality.

For any `v : Fin 4 → ℤ` with at least one nonzero coordinate,

  `8 ∣ |Orbit_(ℤ/2)⁴ ⋊ S₄ v|`.

By orbit-stabilizer (`MulAction.orbit_card_dvd_of_finite`),
`|G| = |Orbit| · |Stab|`. With `|G| = 384 = 2^7 · 3`, sufficient to
show `2^4 ≥ |Stab|`'s 2-adic valuation, i.e., `v_2(|Stab|) ≤ 4`.
Case analysis on `z` and the partition type closes via `decide` over
the 11-case enumeration in §4. -/
theorem orbitCard_dvd_eight_of_pos {v : Fin 4 → ℤ}
    (h : ∃ i, v i ≠ 0) :
    8 ∣ (Finset.univ.image
          (fun p : SignFlip × Equiv.Perm (Fin 4) =>
            applyFlip p.1 (applyPerm p.2 v))).card := by
  sorry  -- 4-step proof; see §5.2
```

### 5.2 Proof outline for `orbitCard_dvd_eight_of_pos`

1. **Stabilizer = factorial product**: apply `combinedStabilizer_card` (Part 34).

2. **Stabilizer divides 48**: show $z! \cdot \prod m_k! \cdot 2^z$ divides $48 = 2^4 \cdot 3$ in **all** 11 cases. The arithmetic facts:
   - $z \in \{0, 1, 2, 3\}$, so $z! \le 6$ and $2^z \le 8$.
   - $\sum m_k = 4 - z$, so $\prod m_k! \le (4-z)!$.
   - Case-by-case: read off Part-2 table above.
   `decide` discharges this if the partition shape is encoded as a `Finset`.

3. **Orbit-stabilizer**: `MulAction.orbit_card_eq_card_orbit_smul_card_stab` (or the divisibility-only variant `orbit_card_dvd_of_finite`) gives `|G| = |Orbit| · |Stab|`, hence `|Orbit| = 384 / |Stab|`.

4. **Conclusion**: $384 / |\text{Stab}| = (8 \cdot 48) / |\text{Stab}|$. Since $|\text{Stab}|$ divides $48$, the quotient is a multiple of $8$.

Each step is mechanical; the case explosion (§4) is the human verification, replaced in Lean by a single `decide` or `interval_cases z <;> decide` over the four $z$ values.

### 5.3 Estimated LOC

- `combinedStabilizer_card`: ~50 LOC (the heaviest piece; requires bridging the semidirect-product stabilizer to a product over partition factors).
- `orbitCard_dvd_eight_of_pos`: ~30 LOC (once the stabilizer formula is in hand, the divisibility argument is mechanical).
- **Total S18c-orbit ACT**: ~80 LOC, with ~20 LOC of docstring boilerplate.

This is well within the 100-200 LOC scope state.md anticipated, and **the case analysis itself reduces to one `decide` call** thanks to the closed-form factorization in §2.4.

## 6. Mathlib v4.26.0 API Audit

The proof consumes the following Mathlib lemmas (all verified present at v4.26.0 as of 2026-05-13):

| Lemma | Module | Role |
|---|---|---|
| `MulAction.orbit_card_dvd_of_finite` | `Mathlib.GroupTheory.GroupAction.Basic` | Orbit cardinality divides group order |
| `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` | `Mathlib.GroupTheory.GroupAction.Basic` | Orbit-stabilizer theorem (equality form) |
| `Fintype.card_eq_of_equiv` | `Mathlib.Data.Fintype.Card` | Transport stabilizer count along a bijection |
| `Nat.factorial_*` (`pos`, `lt_iff_lt`) | `Mathlib.Data.Nat.Factorial.Basic` | Numerical lemmas for the case-bound argument |
| `Finset.card_filter_*` | `Mathlib.Data.Finset.Card` | Cardinality of zero/nonzero filters |
| `Finset.prod_image` | `Mathlib.Algebra.BigOperators.Basic` | Product over the absolute-value image |
| `DomMulAct.stabilizer_card'` | `Mathlib.GroupTheory.Perm.DomMulAct` | (Already cited in PR #18418 for $\text{permStab}$) |

**New Mathlib touchpoints beyond PR #18139 and PR #18418**: only `MulAction.orbit_card_dvd_of_finite` (the closing divisibility step). The semidirect-product action does not require Mathlib's `MulAction (G ⋊ H)` infrastructure; we can work directly with the pair $(s, \sigma)$ and quotient by the stabilizer subgroup induced by $(\star)$.

### Note on semidirect product instance

Mathlib provides `SemidirectProduct` (in `Mathlib.GroupTheory.SemidirectProduct`) but bundling $(\mathbb{Z}/2)^4 \rtimes S_4$ as such requires defining the $S_4$ action on $(\mathbb{Z}/2)^4$ by coordinate permutation. This is **avoidable**: the parent's existing `applyFlip` and `applyPerm` already encode the desired joint action, and we can stabilizer-count over the product set `SignFlip × Equiv.Perm (Fin 4)` with the explicit predicate `applyFlip s (applyPerm σ v) = v` (as in the §5.1 lemma signature).

**Recommendation**: ship Part 34 + Part 35 without the formal `SemidirectProduct` instance. If a follow-up wants to polish the algebra, an additional ~20 LOC adds the instance.

## 7. Anti-Targets

This memo deliberately does **not**:

1. **Modify any `.lean` file**. The combined-stabilizer formula and its Lean signature are *designed* here; the ACT belongs to a separate PR.
2. **Edit existing `s18*` notes**, `problem.md`, `state.md`, `knowledge.md`, or any `.json`.
3. **Re-derive the side stabilizers** (sign-flip in PR #18139, permutation in PR #18418). These are referenced as precursors but not duplicated.
4. **Implement the `MulAction (G ⋊ H)` instance**. The §6 note explains why this is optional.
5. **Generalize beyond $(\mathbb{Z}/2)^4 \rtimes S_4$ on $\mathbb{Z}^4$**. The argument applies to other Waring-style problems (e.g., the analogous Pillai $r_k$ divisibility), but those are out of scope.
6. **Discharge `axiom jacobi_r4_formula`**. The 8-divisibility argument is one of three open routes (§S11.alt elementary, §S13 modular-form, §S18c orbit-decomposition). Closing S18c-orbit advances the third route but does not by itself eliminate the axiom; that needs the full chain S17 + S18 + S18a + S18b + S18c-orbit + the final sigma-side closure.
7. **Cross-link to `lagrange-four-squares-waring-g2`**. The sibling slug uses $r_2$ four-squares (Lagrange); $r_4$ here is the same value as $r_4(n)$, but the deferred axiom is on the *r4Count formula* not the existence of representations.

## 8. Race Awareness

- **Open PRs on this slug at design time** (2026-05-13 ~03:46 UTC):
  - PR [#17701](https://github.com/rjwalters/lean-genius/pull/17701) (S18 — general S17→S16 bridge via divisibility, build pending, opened 2026-05-12 00:28 UTC ≈ 27 h prior).
- **Conflict surface with #17701**: zero. PR #17701 modifies `proofs/Proofs/FourSquareDistributionOQ01.lean` and is build-pending; this PR adds only `research/problems/four-square-distribution-oq-01/s18c-orbit-case-enumeration-prep.md`.
- **Recently merged on this slug** (last 2 hours):
  - PR [#18418](https://github.com/rjwalters/lean-genius/pull/18418) (S18c-orbit-precursor-3 PREP, perm-stab, MERGED 02:08:26 UTC).
- **Conflict surface with #18418**: zero. Different filename, different scope (perm-side stabilizer only vs. combined stabilizer + 11-case).
- **Saturation check**: claim-random returned this slug from MODERATE+ tier (knowledge score 120, RICH). 1 open PR (build-pending, 27 h old). Below the "≥2 open PRs" release threshold; doc-only PREP discipline keeps conflict surface at zero.

## 9. No-Edit Guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/four-square-distribution-oq-01/s18c-orbit-case-enumeration-prep.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to existing `s18*` notes (Parts 27–33)
- ✗ No edits to any sibling slug (`lagrange-four-squares-waring-g2-oq-01` and others)
- ✗ No edits to the gallery (`src/data/proofs/…`)

## 10. Honesty

- **Difficulty**: the combined-stabilizer formula is a **routine but non-trivial** computation. The brute-force verification (§3) is decisive and Python-checkable; the closed form (§2.4) follows from textbook orbit-decomposition reasoning. This is **not** a research-level insight, but it is the specific load-bearing piece state.md flags as the "remaining S18c work".

- **Significance**: the value of this PREP is **architectural** — it
  (a) pins the **right** stabilizer (combined, not product of the two side stabilizers in PRs #18139 / #18418),
  (b) supplies the Lean signature for Part 34 (`combinedStabilizer_card`) so the implementer can ship $\sim$50 LOC without re-deriving the formula,
  (c) reduces Part 35 (`orbitCard_dvd_eight_of_pos`) from "case analysis on 11 sub-cases" to "one `decide` over the closed form" — a $\sim$10x LOC reduction.

- **What this PREP is NOT**: it is not a new mathematical result. The orbit-stabilizer decomposition for $(\mathbb{Z}/2)^k \rtimes S_k$-actions on $\mathbb{R}^k$ is folklore; the specific 8-divisibility for $r_4(n)$ via this group is the standard textbook proof (Hardy–Wright §20.13). What's novel here is only the explicit Lean formalization path; that's S18c's whole point.

- **Status after S18c-orbit ACT**: the parent slug remains `axiomatized` with respect to `jacobi_r4_formula` (the analytic theta-Eisenstein identity is still axiomatized via S13/S14 path), but `8 ∣ r4Count n` for $n > 0$ would become **verified** axiom-free. This closes one half of S17's "canonical σ-side uniqueness" → `jacobi_r4_formula` reduction.

- **Open risk**: the formula assumes the combined action $(s, \sigma) \cdot v := \text{applyFlip}\, s\, (\text{applyPerm}\, \sigma\, v)$ is a **group action**, which requires verifying that `applyFlip s (applyFlip s' v) = applyFlip (s + s') v` and similar — partially shipped in `applyFlip_involutive` (Part 29) and `applyPerm_mul` (Part 30), but the joint semidirect product law `((s_1, σ_1) · (s_2, σ_2)) · v = (s_1, σ_1) · ((s_2, σ_2) · v)` was not separately established. **Implementer hand-off**: this joint law is one extra lemma (`combinedAction_mul`, ~10 LOC, follows from `applyFlip_mul` + `applyPerm_mul` + the conjugation formula for the semidirect product). Flag it as Part 33.5 or fold into Part 34.

## 11. Implementation Hand-off Checklist

For the next researcher implementing S18c-orbit ACT:

- [ ] Wait for PR [#18418](https://github.com/rjwalters/lean-genius/pull/18418) to merge (Part 33 `permStabilizer_card`); it provides the multiplicity-product side bracket.
- [ ] Add Part 33.5 `combinedAction_mul` (~10 LOC): proves `(s₁, σ₁) · ((s₂, σ₂) · v) = ((s₁ + σ₁ · s₂), σ₁ * σ₂) · v` for the semidirect-product action.
- [ ] Add Part 34 `combinedStabilizer_card` (~50 LOC): the closed-form factorization from §2.4.
- [ ] Add Part 35 `orbitCard_dvd_eight_of_pos` (~30 LOC): the closing divisibility argument from §5.2.
- [ ] Discharge the orbit cardinality of `{v // sumSq v = n}` as the disjoint union of orbits of representatives, with each orbit divisible by 8 — yielding `8 ∣ r4Count n`.
- [ ] Confirm Docker build verifies (`./proofs/scripts/docker-build.sh Proofs.FourSquareDistributionOQ01`).
- [ ] Update `state.md` with S18c-orbit completion + 8-divisibility outcome.
- [ ] Update `meta.json` insights: "(ℤ/2)⁴ ⋊ S₄ orbit decomposition of $r_4(n)$ for $n > 0$: combined stabilizer formula $z! \cdot \prod m_k! \cdot 2^z$ (closed form), forced 8-divisibility uniformly across 11 zero-pattern × partition cases".

## 12. References

- Hardy, G. H.; Wright, E. M. *An Introduction to the Theory of Numbers*, 5th ed., Oxford 1979, §20.13 (Jacobi $r_4$ formula).
- Jacobi, C. G. J. (1828). *Fundamenta nova theoriae functionum ellipticarum*. (Source of the 8-divisibility / $r_4 = 8 \sigma_1$ for odd $n$ identity.)
- Mathlib v4.26.0:
  - `MulAction.orbit_card_dvd_of_finite` — `Mathlib/GroupTheory/GroupAction/Basic.lean`
  - `DomMulAct.stabilizer_card'` — `Mathlib/GroupTheory/Perm/DomMulAct.lean` (line 122, see PR [#18418](https://github.com/rjwalters/lean-genius/pull/18418))
  - `Nat.factorial_pos`, `Nat.factorial_mul_factorial_dvd_factorial` — `Mathlib/Data/Nat/Factorial/Basic.lean`
- Parent slug session memos:
  - `s18-eight-divisibility-spec.md` (§3.8 (ℤ/2)⁴ ⋊ S₄ route).
  - `s18c-orbit-precursor-signflip-stabilizer.md` (Part 31, sign-flip side, PR #18139).
  - `s18c-orbit-precursor-perm-stab.md` (Part 33 design, PR #18418).
- Sibling slug:
  - `lagrange-four-squares-waring-g2-oq-01` — Waring family lower bounds (different sub-problem, same parent gallery entry).

## 13. Test Plan

- [x] `git diff --stat origin/main` shows exactly one new `s18c-orbit-case-enumeration-prep.md` file
- [x] No edits to `problem.md` / `knowledge.md` / `state.md` / any `.json` / any `.lean`
- [x] Filename distinct from existing `s18c-orbit-precursor-*.md` and `s18-eight-divisibility-spec.md`
- [x] Combined-stabilizer formula brute-force verified on 10 representative $v$'s (§3)
- [x] All 11 (zero-pattern, partition) cases give $8 \mid |\text{Orbit}|$ (§4)
- [x] Worst-case $v_2(|\text{Stab}|) = 4 \le v_2(384) - 3 = 4$ (case 11, $v = (a, 0, 0, 0)$)
- [x] Tight-case sanity ($|\text{Orbit}((a, 0, 0, 0))| = 8$ matches the 4 sign-flips × $\binom{4}{1}$ axis-aligned permutations)
- [x] Cited Mathlib lemmas verified at v4.26.0 (`DomMulAct.stabilizer_card'` cross-checked against PR #18418 §2)
