# Knowledge: Burnside's pᵃqᵇ Theorem (abel-ruffini-galois-extensions-oq-07)

## Status (2026-05-08, Iteration 9)

Phase-2 axiomatization with axiom narrowed and three of four `(a, b) = (2, 1)`
sub-cases discharged axiom-free (S7, S7.5, S9) modulo a single isolated
sorry deferred to S10:
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`, 876 lines, 20 theorems
(16 substantive), 1 axiom (umbrella for `2 ≤ a ∨ 2 ≤ b`), 1 sorry
(`sylow_two_unique_when_n3_four`, S10 deferred).

## Key Results

| Theorem | Statement | Axiom-free? |
|---|---|---|
| `pGroup_isSolvable` | `IsPGroup p G → IsSolvable G` | Yes (Mathlib chain) |
| `burnside_pq_a_zero` | `Nat.card G = p^0 · q^b → IsSolvable G` | Yes |
| `burnside_pq_b_zero` | `Nat.card G = p^a · q^0 → IsSolvable G` | Yes |
| `burnside_pq_same_prime` | `Nat.card G = p^a · p^b → IsSolvable G` | Yes |
| `squarefreeOrder_isSolvable` (S4) | `Squarefree (Nat.card G) → IsSolvable G` | Yes (IsZGroup chain) |
| `burnside_pq_pq_case` (S4) | `p ≠ q ∧ Nat.card G = p · q → IsSolvable G` | Yes |
| `burnside_pq_nontrivial` (axiom, narrowed S4) | `p ≠ q ∧ a, b ≥ 1 ∧ (2 ≤ a ∨ 2 ≤ b) ∧ Nat.card G = p^a · q^b → IsSolvable G` | **No (narrowed axiom)** |
| `burnside_pq` | `Nat.card G = p^a · q^b → IsSolvable G` | Uses axiom only for `2 ≤ a ∨ 2 ≤ b` |
| `alternatingGroupFin5_card` (S3) | `Nat.card A₅ = 2^2 · 3 · 5` | Yes |
| `alternatingGroupFin5_not_solvable` (S3) | `¬ IsSolvable A₅` | Yes |
| `burnside_pq_sharp` (S3) | conjunction of above two | Yes |

## Mathlib API anchors

### Core (S2)
- `IsPGroup.iff_card.mpr ⟨n, hcard⟩` : derive `IsPGroup p G` from `Nat.card G = p^n`.
- `IsPGroup.isNilpotent : IsPGroup p G → IsNilpotent G` (in `Mathlib.GroupTheory.Nilpotent`).
- `IsNilpotent G → IsSolvable G` : Mathlib instance, derived via `infer_instance`.
- `Nat.eq_zero_or_pos a : a = 0 ∨ 0 < a` for trivial-case dispatch.
- `eq_or_ne p q : p = q ∨ p ≠ q` for prime-equality split.

### Squarefree route (S4)
- `IsZGroup.of_squarefree : Squarefree (Nat.card G) → IsZGroup G` (in `Mathlib.GroupTheory.SpecificGroups.ZGroup`).
- `instance [Finite G] [IsZGroup G] : IsSolvable G` (same file).
- `Nat.coprime_primes hp hq : Coprime p q ↔ p ≠ q` (in `Mathlib.Data.Nat.Prime.Basic`).
- `Prime.squarefree : Prime x → Squarefree x` (in `Mathlib.Algebra.Squarefree.Basic`).
  Apply via `hp.out.prime.squarefree` (where `hp : Fact p.Prime`).
- `Nat.squarefree_mul (hmn : m.Coprime n) : Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n`
  (in `Mathlib.Data.Nat.Squarefree`).

## Why three trivial cases plus pq case collapse

All four trivial cases (`a = 0`, `b = 0`, `p = q`, `|G| = 1`) reduce to G being a
p-group for some prime p:

- `a = 0` → `|G| = q^b` → `IsPGroup q G`.
- `b = 0` → `|G| = p^a` → `IsPGroup p G`.
- `p = q` → `|G| = p^(a+b)` → `IsPGroup p G`.
- `|G| = 1` → degenerate; absorbed by either of the above (since `p^0 = q^0 = 1`).

Mathlib's `IsPGroup → IsNilpotent → IsSolvable` chain then closes them axiom-free.

The squarefree case (`a = b = 1`, `p ≠ q`) reduces to the squarefree route:

- `Nat.card G = p · q` with `p ≠ q` → `Squarefree (p · q)` → `IsZGroup G` → `IsSolvable G`.

This eliminates the `a = b = 1` sub-case of the original `burnside_pq_nontrivial` axiom.
The genuinely-open Lean content is now exactly: `|G|` divisible by `p²` or `q²`
for distinct primes (`2 ≤ a ∨ 2 ≤ b`).

## Two proof routes for `burnside_pq_nontrivial` (residual case, `2 ≤ a ∨ 2 ≤ b`)

### Route A: Burnside 1904 (character theory)
- Pick minimal counterexample G; show G is non-abelian simple with no normal Sylow.
- Pick `g ∈ Z(P)` of prime order (P a Sylow p-subgroup).
- Conjugacy class size `|cl(g)| = |G : C_G(g)|` is divisible only by powers of q.
- Apply column orthogonality of irreducible characters: `Σ χ(1)·χ(g) = 0`.
- Algebraic-integer arithmetic in the cyclotomic ring `ℤ[ζ_n]` derives a contradiction.

**Mathlib gap**: The algebraic-integer hypothesis `(|G|/χ(1))χ(g) ∈ ℤ̄_K` is not
formalized at the needed generality. Estimated 100-200 additional lines on top
of `Mathlib.RepresentationTheory.Character.char_orthonormal`.

### Route B: Goldschmidt-Matsuyama 1970s (character-free)
- Use the focal subgroup theorem: `P ∩ G' = focal subgroup of P in G`.
- Apply transfer homomorphism on Sylow p-subgroup.
- Show `P ∩ G' < P`, contradicting `G = G'` for non-abelian simple G.

**Mathlib status**: `Mathlib.GroupTheory.Focal` provides the focal subgroup
definition, `transferFocal`, `commutator_inf_eq_focalSubgroup`, etc. Significant
scaffolding exists for this route. Estimated 200-400 lines on top of this.

**Recommendation**: Route B (character-free), since Mathlib's `Focal` infrastructure
is closer to ready than the algebraic-integer infrastructure for Route A.

### Sub-case strategy (intermediate Sylow analysis)

Before tackling the full Goldschmidt-Matsuyama proof, the residual axiom can be
narrowed further by proving specific sub-cases via Sylow analysis:

- `|G| = p² · q` (a=2, b=1): ~50-100 lines. Sylow's third theorem gives
  `n_p | q` and `n_q | p²`; case analysis on (n_p, n_q) yields a normal Sylow.
- `|G| = p · q²` (a=1, b=2): symmetric to above.
- `|G| = p² · q²` (a=b=2): more delicate; Sylow + counting elements.

Each of these subsumes a specific instance of the axiom. After all three are
proved, the axiom narrows to `3 ≤ a ∨ 3 ≤ b`.

## Sharpness check

`|A₅| = 60 = 2² · 3 · 5` has THREE distinct primes — exactly one more than
Burnside permits. Combined with the parent gallery entry's
`¬ IsSolvable (Equiv.Perm (Fin 5))`, this gives the exact prime-multiplicity
threshold for solvability: groups of order divisible by ≤ 2 primes are always
solvable; groups divisible by ≥ 3 primes can fail (and A₅ is the smallest).

Note: A₅ also defeats the squarefree route — `|A₅| = 60 = 2² · 3 · 5` has `2²`,
so `squarefreeOrder_isSolvable` does not apply. The squarefree route is strictly
weaker than the full Burnside theorem: it covers any number of distinct primes
each to first power, but cannot handle `p²` for any prime.

## Path forward

1. **(S5, PR #16972, merged)** `burnside_pq_with_normal_pSylow` and `_qSylow`
   reduction lemmas: `|G| = p^a · q^b` + normal Sylow ⇒ solvable.
2. **(S7, PR #17114, merged)** `burnside_p_squared_q_p_gt_q`: `|G| = p²·q`
   with `q < p` is solvable axiom-free (Sylow's third theorem forces `n_p = 1`).
3. **(S7.5, PR #17155, merged)** `burnside_p_squared_q_p_lt_q`: `|G| = p²·q`
   with `p < q` and `(p, q) ≠ (2, 3)` is solvable axiom-free.
4. **(S8, PR #17180, merged)** `session-8-twelve-spec.md` — detailed
   spec for the `|G| = 12` exceptional case (5 helper lemmas + main
   theorem skeleton; ~180 estimated lines for full implementation).
5. **(S9, this session)** Implements the bulk of S8 spec axiom-free,
   with one isolated sorry deferred to S10:
   * `sylow_count_dvd_four_modEq_one_three` (private helper, axiom-free):
     `n ≥ 1 ∧ n ∣ 4 ∧ n ≡ 1 [MOD 3] → n ∈ {1, 4}`. Decidable on Nat.
   * `sylow_two_unique_when_n3_four` (private, sorry'd for S10):
     `|G| = 12 ∧ n_3 = 4 → Subsingleton (Sylow 2 G)`. Element counting.
   * `burnside_p_squared_q_twelve` (axiom-free modulo above): handles
     both `n_3 = 1` (direct) and `n_3 = 4` (via S10 lemma) branches.
6. **(S10)** Close `sylow_two_unique_when_n3_four`'s sorry via
   element counting (~80-120 lines): pairwise trivial intersection
   of Sylow 3's, partition `{g | g^3 = 1} = {e} ⊔ ⊔ᵢ (Q_i \ {e})`,
   cardinality 9, residue 3 = `|P| − 1`, set equality forces
   uniqueness. Mathlib API: `Set.ncard_biUnion` /
   `Finset.card_disjUnion`, `Subgroup.ext`, `Sylow.ext`.
7. **(post-S10)** Update `burnside_pq` dispatch to peel off
   `(a, b) = (2, 1)` axiom-free for ALL `(p, q)` (combine S7, S7.5, S9).
8. **(S11)** Symmetric `(1, 2)` shape: `burnside_p_q_squared_*` mirroring
   S7/S7.5/S9.
9. **(S12)** Update `burnside_pq` dispatch to peel off `(1, 2)` too.
   Narrow `burnside_pq_nontrivial` axiom hypothesis to `2 ≤ a ∧ 2 ≤ b`.
10. **(S13)** `|G| = p²·q²` Sylow analysis (~150 lines).
11. **(S14+)** Goldschmidt-Matsuyama on top of `Mathlib.GroupTheory.Focal`
    (~200-400 lines). Closes ALL remaining cases.
12. **(Final)** Replace `axiom burnside_pq_nontrivial` with theorem; sync
    meta.json; submit Mathlib upstream PR (~1000 lines total).

## Insight (S8): Why `|G| = 12` requires element counting, not Sylow alone

For `|G| = p²·q` with `p ≠ q`, Sylow's third theorem gives `n_p ∈ {divisors of q}`
and `n_q ∈ {divisors of p²}`, each `≡ 1` modulo the corresponding prime. The
constraint `n_q ≡ 1 [MOD q]` for `n_q ∈ {1, p, p²}` rules out `n_q = p` whenever
`p < q` (since `q ∣ p − 1` is impossible) and rules out `n_q = p²` whenever
`q ∤ p² − 1 = (p − 1)(p + 1)`. The latter fails only when `q ∣ p + 1` AND
`q ∤ p − 1`, which forces `q = p + 1`. The only consecutive primes are
`(2, 3)` — hence the exceptional case `|G| = 12`.

In this exceptional case `n_3 = 4` is genuinely possible (realized by `A₄`).
Sylow's third theorem alone cannot rule it out; one must count elements:
distinct Sylow 3-subgroups intersect trivially (prime order), so 4 such
subgroups contain `1 + 4·2 = 9` elements (with `g^3 = 1`). The remaining
`12 − 9 = 3` elements together with the identity form a unique 4-element
set that necessarily coincides with any Sylow 2-subgroup, forcing `n_2 = 1`.

**Generalization caveat**: This element-counting trick is specific to `|G| = 12`.
For `|G| = 18 = 2·3²` (the symmetric `(1, 2)` exceptional case with
`(p, q) = (2, 3)`), an analogous count gives `9 + 9 = 18`, leaving `0`
slots — meaning the Sylow 2 and Sylow 3 unions exactly partition `G`. The
proof structure is similar but the bound is tighter (must rule out triple
overlaps explicitly).

## Insight (S9): Skeleton-first implementation strategy

S9 implements the case-split skeleton of `burnside_p_squared_q_twelve`
fully, while isolating the one element-counting sub-lemma
(`sylow_two_unique_when_n3_four`) as a single sorry. This decoupling has
three advantages:

1. **Risk amortization.** The `n_3 = 1` branch is fully discharged
   axiom-free using only the merged S5 reduction lemmas. If the
   `n_3 = 4` branch turns out to require unexpected Mathlib calls in
   S10, the existing `n_3 = 1` discharge is unaffected.
2. **Build-pending acceptability.** The S9 PR adheres to the S7.5
   pattern verbatim — same `Sylow.card_eq_multiplicity` chain, same
   `Subgroup.card_mul_index` cancellation, same `factorization_*`
   computation. Risk-equivalent to S7.5; either both build or both
   need the same fix.
3. **Sharp focus for S10.** S10 has exactly one statement to prove,
   with a clear input (`Nat.card G = 12`, `n_3 = 4`) and a clear
   output (`Subsingleton (Sylow 2 G)`). All surrounding context
   (factorization, index computation, Sylow normality, discharge via
   reduction lemmas) is already wired up in `burnside_p_squared_q_twelve`.

The tradeoff: `sorries 0 → 1` in this PR. This is a temporary
regression that S10 reverses. The badge stays `axiom` (since the
umbrella axiom is unchanged). The substantive progress is the wiring
up of all the dispatch + factorization + index machinery for the
exceptional case, leaving only the genuinely-hard set-cardinality
core.

## Mathlib API for S10 element counting (to verify when build available)

The element-counting argument needs:

| Lemma | Likely Mathlib location | Purpose |
|---|---|---|
| `Subgroup.disjoint_iff_inf_eq_bot` | `Mathlib.Algebra.Group.Subgroup.Basic` | Distinct prime-order Sylows have trivial intersection. |
| `Subgroup.card_eq_one_iff_eq_bot` | `Mathlib.Algebra.Group.Subgroup.Lattice` | `|H| = 1 ↔ H = ⊥`. |
| `Sylow.ext` | `Mathlib.GroupTheory.Sylow` | Sylow equality from underlying-subgroup equality. |
| `Set.ncard_biUnion` / `Finset.card_disjUnion` | `Mathlib.Data.Set.Card` | Disjoint-union cardinality. |
| `Subgroup.card_inf_le_card` | `Mathlib.Algebra.Group.Subgroup.Lattice` | `|P ⊓ Q| ∣ |P|`. |
| `Equiv.Perm.orderOf_dvd_card` (analogous) | `Mathlib.GroupTheory.OrderOfElement` | `g ∈ H → orderOf g ∣ |H|`. |

Risk: `Set.ncard` vs `Finset.card` choice may matter — `Sylow p G` is
a `Finset` for finite `G` via `Sylow.fintype`, but the underlying
`Subgroup G` is naturally a `Set G`. May need careful coercion.
