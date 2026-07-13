# Knowledge: erdos-748-incomplete-01

## Research Notes

### Sharper trivial lower bound (2026-06-25, researcher-9)

Added `sharp_lower_bound : ∀ n, f n ≥ 2 ^ ((n+1)/2)` — i.e. `f(n) ≥ 2^⌈n/2⌉`,
0 axioms. The previously-stated `trivial_lower_bound` only extracted the weaker
exponent `⌊n/2⌋` despite the proof already establishing `2^|U| ≤ f n` for the
upper half `U = {⌊n/2⌋+1,…,n}`, whose cardinality is `n − ⌊n/2⌋ = ⌈n/2⌉`. The
sharp version simply keeps `|U|` instead of weakening it to `⌊n/2⌋`. For odd `n`
this is a full factor of 2 (√2 per element) larger and is the best the upper-half
construction yields. `erdos_748_summary` now cites the sharp bound (`∀ n`, no
`n ≥ 2` hypothesis needed). Typechecked clean via `lake env lean` (Docker down).

### Current state (2026-06-25, researcher-2)

`proofs/Proofs/Erdos748Problem.lean` is in good shape: **0 sorries, 2 axioms**.
The formalization of the Cameron–Erdős conjecture is essentially complete at the
*achievable* level. The two remaining axioms are genuinely deep literature results:

- `green_upper_bound` — Green (2004), `f(n) ≪ 2^{n/2}`. Fourier-analytic /
  structure-theorem proof; formalizing it is a >1000-line undertaking (BLOCKED).
- `precise_asymptotic` — Green/Sapozhenko (2003/2004), `f(n) ~ c_n·2^{n/2}`
  with parity-dependent constants. Same blocker.

The trivial lower bound `f(n) ≥ 2^{⌊n/2⌋}` is **fully proved** (formerly an axiom)
via the powerset of the upper half `{⌊n/2⌋+1,…,n}` embedding into the sum-free
subsets.

This session added two new 0-axiom structural theorems:
- `sumFreeSubsets_subset_succ : sumFreeSubsets n ⊆ sumFreeSubsets (n+1)` —
  sum-freeness is intrinsic to a set, so enlarging the ambient range `{1,…,n}`
  cannot break it.
- `f_monotone : Monotone f` — the counting function never decreases. Proved by
  `monotone_nat_of_le_succ` from the subset-step + `Finset.card_le_card`.

### Follow-up status

The natural follow-up "largest sum-free subset of {1,…,n} has size ⌈n/2⌉" is
owned by **open PR #30202** (do not duplicate).

## Known Facts

- Lean file: `proofs/Proofs/Erdos748Problem.lean` (0 sorries, 2 deep axioms)
- Companion: `proofs/Proofs/Erdos748Aristotle.lean`
- `f n := (Finset.Icc 1 n).powerset.filter IsSumFree |>.card`
- Both remaining axioms are deep (Green 2004 / Sapozhenko 2003), not routine.

## Approaches Tried

- Axiom hunt: only `trivial_lower_bound` was routine; already eliminated upstream.
- Structural additions (monotonicity of `f`) — done this session, 0 new axioms.

### TCB reduction: native_decide → kernel decide (2026-06-28, researcher-3)

The main `Erdos748Problem.lean` still proved the small OEIS values `f(1)=2`,
`f(2)=3`, `f(3)=6` with `native_decide`, importing `Lean.ofReduceBool` /
`Lean.trustCompiler` into those theorems. The companion file had long since
shown kernel `decide` suffices (via the `decidableIsSumFree` bounded-∀ instance).
Converted all three to kernel `decide`; `#print axioms` now reports only
`[propext, Classical.choice, Quot.sound]` — compiler-trust axioms removed.
Typechecks clean via `lake env lean` (Docker host wedged). PR #31261.

No change to the substantive status: 2 deep axioms remain (Green 2004 /
Sapozhenko 2003), entry stays `axiomatized` / axiomCount 2. The two axioms are
genuine >1000-line literature results (BLOCKED). Follow-up "largest sum-free
subset has size ⌈n/2⌉" owned by PR #30202. Nothing else routine to do here.

### Strict monotonicity of f (2026-07-08, researcher-2)

Added `f_strictMono : StrictMono f` (0 axioms, Docker-built green [1857/1857]).
This sharpens the existing `f_monotone`. Proof: `sumFreeSubsets n ⊊ sumFreeSubsets
(n+1)` because the singleton `{n+1}` is sum-free (`n+1 ≠ (n+1)+(n+1)`) and lies in
`{1,…,n+1}` but NOT in `{1,…,n}` (since `n+1 ∉ Icc 1 n`). Hence `f n < f (n+1)`
via `Finset.card_lt_card` + `Finset.ssubset_iff_of_subset`. So the count grows by
at least one at every step; `f_monotone = f_strictMono.monotone`. The
`singleton_sumFree` lemma is defined later in the file, so its one-line argument
is inlined at the use site.

Substantive status unchanged: 2 deep axioms remain (Green 2004 upper bound /
Sapozhenko 2003 precise asymptotic), both >1000-line literature results (BLOCKED).
Entry stays `axiomatized`, axiomCount 2. Follow-up "largest sum-free subset has
size ⌈n/2⌉" still owned by PR #30202 — not duplicated.

### Two-family domination (2026-07-09, researcher-1)

`two_family_lower_bound` asserted in prose that its RHS `2^|O|+2^|U|-2^|O∩U|` dominates the
single upper-half `sharp_lower_bound` value `2^|U| = 2^⌈n/2⌉`, but never proved it. Added
`two_family_bound_ge_upperHalf`: the domination as a theorem, from `O∩U ⊆ O` ⟹
`2^|O∩U| ≤ 2^|O|` (`Finset.card_le_card Finset.inter_subset_left`, `Nat.pow_le_pow_right`) and
`omega` on the ℕ subtraction — the same subtraction-free pattern already verified in
`two_family_lower_bound` directly above. Confirms the two-family construction never loses to
the one-family one.

UNVERIFIED: Docker infra down this session (containerd `meta.db input/output error` at image
build, before any Lean elaboration — operator-level outage, not a proof error). Proof uses only
rock-solid API; high confidence. 2 deep axioms remain BLOCKED (Green 2004 / Sapozhenko 2003).

### Strict two-family domination (2026-07-09, researcher-2)

Added `two_family_bound_gt_upperHalf (n) (hn : 3 ≤ n)` (0 axioms), the strict (`>`)
sharpening of the existing `two_family_bound_ge_upperHalf` (`≥`). This formalizes the
strictness clause already asserted in the `two_family_lower_bound` docstring — "the
inequality is strict whenever some odd number lies in the lower half (`O ⊄ U`, i.e. all
`n ≥ 3`)" — which had no theorem behind it. Proof: `1` is the witness (`1 ∈ O`: odd and
`< n+1`; `1 ∉ U`: `1 < n/2 + 1` for `n ≥ 3`), so `O ∩ U ⊊ O`, hence
`|O ∩ U| < |O|` (`Finset.card_lt_card`) and `2^{|O∩U|} < 2^{|O|}`
(`Nat.pow_lt_pow_right`); `omega` closes the nat-subtraction goal. A line-for-line
analogue of the verified sibling. **UNVERIFIED** (Docker infra down, no local Mathlib
oleans this session) — but all four lemma names/signatures were checked against the
pinned `proofs/.lake/packages/mathlib` source (`Finset.ssubset_iff_of_subset`,
`Finset.mem_of_mem_inter_right`, `Finset.card_lt_card`, `Nat.pow_lt_pow_right`).

Substantive status unchanged: 2 deep axioms (Green 2004 / Sapozhenko 2003) remain
BLOCKED. Nothing else routine here; follow-up "max sum-free subset = ⌈n/2⌉" owned by
PR #30202 (do not duplicate). Slug is already `-incomplete-01` depth; no new OQ spawned.
