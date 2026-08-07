# Scout: length-agnostic mixed-anchor parity (goal #1 / #9d bottleneck)

## CORRECTION (v2 — supersedes the involution route below)

The involution `x ↦ −x−t` does NOT act on the displacement-t solution set
without a reflection symmetry of the labeled adjacency (it maps the pair
(x, x+t) to the negated-reversed pair, which is a different edge unless
`Adj (u a) (u b) = Adj (u (−a)) (u (−b))`). The corrected — and stronger —
route comes from the 0/1 wave equation:

`[B, S + S⁻¹] = 0` for a 0/1 block B says
`B(x−1,y) + B(x+1,y) = B(x,y−1) + B(x,y+1)`; over ℝ the solutions are
`c(y−x) + h(y+x)`, and 0/1-valuedness forces, on EACH parity class of
(y−x, y+x) (two classes when ℓ is even), that B is EITHER pure circulant
(function of y−x) OR pure Hankel (function of y+x) — a 3-value collision
argument (c and h each ≤2-valued, non-constant both ⟹ ≥3 distinct sums).
This is exactly the even-sector circulant/reverse classification
(`EvenCycleSelfIntertwiner`).

Parity consequences for the anchored count A(t) = #{x : B(x, x+t) = 1}:
- **Hankel classes contribute evenly** to every A(t): solutions of
  `2x ≡ h − t` come 0-or-2 at even ℓ.
- **Circulant classes** contribute `(ℓ/2)·[t ∈ supp]` per class:
  even when ℓ ≡ 0 (mod 4); the support indicator when ℓ ≡ 2 (mod 4).
- Odd ℓ: whole block circulant (known), contribution `ℓ·[t ∈ supp]`, odd
  iff t in support.

So: **p-divisible blocks of length ≡ 0 (mod 4) vanish from the parity
terminal entirely; blocks of length ≡ 2 (mod 4) contribute exactly their
circulant-class support parity; odd blocks as before.** The length-agnostic
three-point terminal then requires only the refined count hypothesis: the
number of p-divisible components with ℓ odd or ℓ ≡ 2 (mod 4) — weighted by
their circulant-class support — is odd. `hodd` is replaced by this weaker,
automatically-satisfiable-or-checkable condition, and length-≡0(4)
components are unconditionally harmless.

Formalization order (corrected):
1. 0/1 wave-equation class dichotomy (or specialize EvenCycleSelfIntertwiner).
2. Hankel-class evenness: `2x ≡ c` has an even solution count at even ℓ.
3. ℓ mod 4 split of the circulant contribution.
4. Refined terminal with the weighted count hypothesis.

--- (original note, involution route DEPRECATED) ---

Problem: `odd_mixedProjectedAnchor_iff_threePoint` needs `hodd` (every
p-divisible defect component has odd length) because the diagonal-block
translation invariance (`mixedLabeledAdjMatrix_diag_translationInvariant`)
uses `graph_equalOddCycle_diagBlock_adj_shift_iff`, which is genuinely false
at even cycle length (the ±k Fourier pairs of S + S⁻¹ are degenerate and the
commutant admits reflection/Hankel components).

## Findings

1. **Zero-row support is the wrong primitive at even length.** For odd ℓ,
   translation invariance makes the 0-row support representative of every
   row; for even ℓ the block entry χ(x, y) can depend on x + y (reflection
   part), so `graphCycleBlockZeroSupport` loses information. The
   length-agnostic definition should be the full anchored count
   `A_c(t) := #{x : ZMod ℓ | G.Adj (u c x) (u c (x + t))}` and the projected
   anchor `Σ_{c p-div} Σ_{t ≡ s (p)} A_c(t)` — this is what the Fourier trace
   actually produces (the ℓ-fold overcount at odd length is `ℓ · [t ∈ supp]`,
   absorbed by the existing 1/ℓ normalizations).

2. **Free parity law at even length** (new, elementary): for even ℓ and any
   t, the involution `x ↦ −x − t` acts on the solution set of `A_c(t)`
   (adjacency symmetry). Its fixed points are the solutions of `2x = −t`:
   none when t is odd, exactly two when t is even. Hence
   - `t` odd ⟹ `A_c(t)` is EVEN;
   - `t` even ⟹ `A_c(t) ≡ #{centered candidates that are adjacent} (mod 2)`,
     i.e. parity is carried entirely by the ≤2 "antipodally centered" edges
     at displacement t.
   (At odd ℓ the same involution has exactly one fixed point for every t,
   recovering `A_c(t) ≡ [centered edge] (mod 2)` — the known route to the
   three-point terminal, now uniform in ℓ.)

3. **Consequence for the mod-p projection** (p odd prime, p ∣ ℓ, ℓ even):
   within a residue class s mod p, displacements alternate parity as t runs
   through s, s+p, s+2p, … (p odd), so every class contains both parities of
   t equally often (ℓ/p even ⟹ exactly ℓ/(2p) odd and ℓ/(2p) even each).
   The class parity therefore reduces to
   `P_c(s) ≡ Σ_{t ≡ s, t even} [centered-edge parity of t] (mod 2)` — a sum
   over the "half-cycle" `t = 2r` of centered-edge indicators, i.e. the
   parity of anchored edges of the SQUARED cycle structure. Suggested Lean
   object: `centeredEdge G (u c) r := G.Adj (u c (−r)) (u c r)` (displacement
   2r centered at 0 up to the 2x = −t translate), with
   `P_c(s) ≡ #{r : 2r ≡ s, centeredEdge r} (mod 2)`.

4. **What this buys**: the dichotomy engine only needs parity CONSTANCY
   or a ≤k-point exceptional set for `s ↦ P(s)`. With (3), the even-length
   contribution is the mod-p projection of a single Boolean function on the
   ℓ/2-cycle (centered edges), and `2r ≡ s` is a bijection r ↔ s (2
   invertible mod p): so `P_c(s) ≡ #{r ∈ class(s/2) : centeredEdge r}` —
   structurally IDENTICAL to the odd-length projected-anchor object, at the
   substituted frequency s/2. The three-point argument should then run
   verbatim with the exceptional set transformed by the ·2⁻¹ map (still ≤3
   points). Conjecture: `odd_mixedProjectedAnchor_iff_threePoint` holds
   without `hodd`, with the same three exceptional points, after replacing
   zero-row supports by centered/anchored counts throughout.

## Suggested formalization order
1. Define `anchoredCount` (full-row) + lemma `anchoredCount_eq_card_support`
   at odd length (compat with existing zero-row development).
2. The involution parity lemma (2) — pure ZMod combinatorics, no graph
   theory beyond `G.symm`.
3. The `s ↦ s·2⁻¹` transport of the projection (3).
4. Re-derive the three-point terminal length-agnostically; retire `hodd`
   from `le_pDivisibleAnchorMass_of_countOdd` and downstream.

Files touched would be new (`Erdos85MixedAnchorParityGeneral.lean`) +
eventual rewires in `Erdos85LargePrimeParityTerminal`; existing files stay.
