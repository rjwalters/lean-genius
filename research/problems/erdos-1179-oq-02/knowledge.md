# Knowledge: erdos-1179-oq-02

## Question (defined from the parent 0-knowledge stub)

Erdős #1179 (PROVED, main asymptotic): for `0<ε<1`, `g_ε(N)` = least `k` such that
a uniformly random `k`-subset `A` of an abelian group `G`, `|G|=N`, has w.h.p. an
ε-uniform subset-sum representation function
`F_A(g)=#{S⊆A : Σ_{x∈S} x = g}`, i.e. `|F_A(g) − 2^k/N| ≤ ε·2^k/N` for all `g`.

**oq-02 (OPEN):** can the Erdős–Hall `(1+o(1))` *multiplicative* factor be sharpened
to a bounded *additive* error?  `g_ε(N) ≤ log₂N + O_ε(1)`.

## Bound hierarchy

| Result | Bound on g_ε(N) |
|--------|-----------------|
| Trivial lower bound | `≥ log₂N` (need `2^k ≥ N`) |
| Erdős–Rényi (1965) | `≤ (2+o(1))log₂N + O_ε(1)` |
| Erdős–Hall (1976) | `≤ (1 + O_ε(log log log N / log log N))·log₂N` |
| **oq-02 (open)** | **`≤ log₂N + O_ε(1)`** ? |

## Status

ORIENT/DEFINE only (2026-06-14). The OQ is asymptotic/analytic — finite computation
cannot decide it. `verify_uniform_subset_sums.py` (build-free, stdlib) confirms the
parent identity `Σ_g F_A(g)=2^|A|`, the lower bound (no ε-uniform `k<log₂N`), and
tabulates the exact empirical additive gap on `ℤ/N` (stays ~1–3.5 for the
probabilistic proxy, `N=2..12`). Honest caveat: tiny `N`, single group — consistent
with but not evidence for a bounded gap. Both backends (Docker + Aristotle) down.

See `src/data/research/problems/erdos-1179-oq-02.json` for the full record.

## Session 2026-06-15 (researcher-2) S3 ACT — deterministic upper-bound companion (additive constant 0 on 𝔽₂^m)

Complements #24551's lower bound `g_ε(N) ≥ log₂N` with the sharpest UPPER side.
**Key:** if a subset `A` gives every group element a UNIQUE subset-sum
representation (`reprCount A g = 1 ∀g` — e.g. a basis of `(ZMod 2)^m`, `N=2^m`),
then `A` is **exactly 0-uniform** and `|A| = ⌈log₂N⌉` exactly. So
`g_0(N) = log₂N` on the elementary-abelian-2-group family, *deterministically*
(not w.h.p.). The OQ's additive constant is therefore 0 on this family and
cannot be forced positive in general. (Does NOT resolve oq-02: general/random G,
w.h.p.)

**Built (build-pending, UNREGISTERED — blackout):** `proofs/Proofs/Erdos1179OQ02Upper.lean`
- `card_eq_two_pow_of_unique_repr`: reprCount≡1 ⟹ N = 2^|A| (via `total_reprCount`).
- `epsUniform_zero_of_unique_repr`: reprCount≡1 ⟹ `IsEpsUniform A 0` (μ = 2^|A|/N = 1).
- `unique_repr_card_eq_clog`: reprCount≡1 ⟹ `A.card = Nat.clog 2 N` (optimal).
Bearer name-checked @ 2df2f01: `Nat.clog_pow (b x:ℕ)(hb:1<b): clog b (b^x)=x`
(Data/Nat/Log.lean:453). 0 axioms / 0 sorry by construction; needs Docker to verify.

**Cert:** `verify_unique_repr_upper.py` — PASS, basis of 𝔽₂^m m=1..8: reprCount≡1,
Σ=2^|A|, 0-uniform, |A|=clog₂N.

**Next:** post-blackout register+build `Erdos1179OQ02Upper.lean`; optionally
instantiate at `G=(ZMod 2)^m` with the standard basis to exhibit a concrete
`∀g, reprCount A g = 1` witness (needs the powerset-sum↔indicator bijection over 𝔽₂).
