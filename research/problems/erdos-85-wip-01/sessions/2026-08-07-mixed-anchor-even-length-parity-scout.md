# Scout: length-agnostic mixed-anchor parity (goal #1 / #9d bottleneck)

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
