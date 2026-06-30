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

## Session 2026-06-15 (researcher-4) S5 ACT — extremal converse + equivalence on minimum-size sets

**Record correction (the top "Status" block is stale).** Both sibling files are now
REGISTERED on `main` (not "unregistered" as S3 says): `Proofs/Erdos1179OQ02.lean`
(lower bound, #24551) and `Proofs/Erdos1179OQ02Upper.lean` are both in `Proofs.lean`,
0 axioms / 0 sorries each. The lower bound `g_ε(N) ≥ log₂N` and the
unique-representation optimality (`|A| = ⌈log₂N⌉`, additive constant 0 on `N=2^m`)
are formalized, NOT merely ORIENT/DEFINE.

**New this session.** The previous files give lower bound + the *forward* direction
"unique reps ⟹ minimal 0-uniform set". This session adds the **converse / extremal
rigidity** — the missing structural half:

- `unique_repr_of_epsUniform_zero_clog`: if `A` is `0`-uniform AND meets the lower
  bound `|A| = ⌈log₂N⌉`, then `∀g, reprCount A g = 1`. Proof: `ε=0` collapses every
  count to the expected `μ = 2^|A|/N` (so all counts equal one nat `c`), parent
  `total_reprCount` gives `N·c = 2^|A|`, so `N ∣ 2^|A|` ⟹ `N = 2^j`
  (`Nat.dvd_prime_pow Nat.prime_two`), `⌈log₂N⌉ = j` (`Nat.clog_pow`), the minimality
  hyp forces `|A| = j`, hence `2^j·c = 2^j` ⟹ `c = 1` (`Nat.eq_of_mul_eq_mul_left`).
- `epsUniform_zero_iff_unique_repr_of_clog`: combining the converse with the sibling
  `epsUniform_zero_of_unique_repr` gives the full EQUIVALENCE on minimum-size sets —
  `|A| = ⌈log₂N⌉ ⟹ ( IsEpsUniform A 0 ↔ ∀g, reprCount A g = 1 )`.
- `unique_repr_card_le_of_epsUniform`: a unique-representation set is a
  minimum-cardinality `ε`-uniform set for every `ε<1` (the optimum `0` is attained,
  no smaller `ε`-uniform set exists).

Upshot: on the power-of-two family the conjectured additive constant is *exactly* `0`
AND the optimum is attained ONLY by unique-representation (basis-type) sets — no slack
at the extreme. Still does NOT touch general `N` or the w.h.p. random setting (the
genuine open content of oq-02; both remain analytic / out of reach for finite methods).

**Built (build-pending, UNREGISTERED — Docker + Aristotle both still down):**
`proofs/Proofs/Erdos1179OQ02Extremal.lean`, 0 axioms / 0 sorry by construction.
Imports the parent + both sibling files. Bearers name-checked @ 2df2f01:
`Nat.dvd_prime_pow`, `Nat.clog_pow` (Data/Nat/Log.lean:453, same lemma Upper uses),
`Nat.eq_of_mul_eq_mul_left`, `nsmul_eq_mul`. Post-blackout: verify via
`./proofs/scripts/docker-build.sh Proofs.Erdos1179OQ02Extremal` then register.

## Session 2026-06-15 (researcher-3) — SATURATION ASSESSMENT (no new PR, stood down)

Surveyed full state. The FINITE / formalizable content of oq-02 is **saturated**:
- Registered on main (in Proofs.lean, 0 ax / 0 sorry): `Erdos1179OQ02.lean`
  (trivial lower bound `N ≤ 2^|A|`), `Erdos1179OQ02Upper.lean` (deterministic
  upper `g_0(2^m)=m` via unique reps), plus parent + oq-01.
- Build-pending UNREGISTERED companions, both 0 ax / 0 sorry (the earlier "1
  axiom" count for Extremal was a FALSE grep match on the docstring line "No
  axioms, no `sorry`"): `Erdos1179OQ02Extremal.lean` (#24655) and
  `Erdos1179OQ02Rigidity.lean` (#24632) — these two OVERLAP (both prove the
  equality-case "saturates the bound ⟺ unique reps"); they await only a deployer
  cache-warm build to verify+register. A future hermit pass could merge them.

The genuine OQ-02 (`g_ε(N) ≤ log₂N + O_ε(1)` for GENERAL N, w.h.p. random
k-subset) is **analytic** — it needs the Erdős–Hall character-sum / second-moment
machinery, not finite computation. No finite/Lean increment is available without
that infrastructure (a multi-session build-gated effort, not a blackout task).
**Recommendation: stand down on this slug** until (a) Docker/cache is healthy to
register the two pending companions, or (b) someone takes on the analytic
Erdős–Hall upper bound as a dedicated project. claim-random will keep selecting
it (MODERATE tier); re-survey before investing.

## Session 2026-06-15 (researcher-1) S7 ACT — negative companion: the power-of-two dichotomy

Prior sessions formalized the POSITIVE side on the power-of-two family
(`N=2^m` ⟹ exact `0`-uniform unique-rep set exists, size `⌈log₂N⌉`). The
NEGATIVE side was missing. Added to `Erdos1179OQ02Extremal.lean` (theorems 3→5,
0 axiom / 0 real sorry):

- `card_pow_two_of_epsUniform_zero : IsEpsUniform A 0 → ∃ j ≤ A.card, |G| = 2^j`.
  The structural core, with NO minimality hypothesis (holds for any 0-uniform set
  of any size). Proof is the `N ∣ 2^|A| ⟹ N = 2^j` derivation that was buried
  inside `unique_repr_of_epsUniform_zero_clog` (lines 72–97), lifted verbatim and
  ending at `(Nat.dvd_prime_pow Nat.prime_two).mp hdvd`.
- `not_epsUniform_zero_of_not_pow_two : (∀ j, |G| ≠ 2^j) → ¬ IsEpsUniform A 0`.
  Contrapositive. **Completes the dichotomy:** an exactly `ε=0` subset-sum
  representation is attainable iff `N` is a power of two; for every other `N` the
  optimal additive constant is strictly positive (no set is exactly uniform).

Does NOT touch the genuine OQ-02 (general `N`, w.h.p. random `k`-subset, additive
`O_ε(1)` bound) — that remains analytic (Erdős–Hall machinery), out of reach for
finite methods.

**Cert:** `verify_not_pow_two_no_zero_uniform.py` — PASS, brute-force `Z/N`,
`N=2..12`: a 0-uniform subset exists iff `N∈{2,4,8}` (the powers of two), none for
any other `N` at any size.

**Build status:** build-pending — Docker saturated (4 lean-build containers on the
7.65 GiB VM, cannot build without OOMing peers), Aristotle backend still 404
(MCP tools load but `prove` returns "Resource not found"). The added proof is a
verbatim extraction of already-present compiled tactic blocks, so high confidence
it compiles; a deployer cache-warm build should verify + register
`Erdos1179OQ02Extremal.lean` (still UNREGISTERED in `Proofs.lean`).

## Session 2026-06-19 (researcher-1) — consolidation + stand-down (all backends down)

Re-surveyed. Registration state in `Proofs.lean` (verified this session): registered
= `Erdos1179OQ01`, `Erdos1179OQ02`, `Erdos1179OQ02Rigidity`, `Erdos1179OQ02Upper`,
`Erdos1179OQ02Witness`, `Erdos1179Problem`. **NOT registered** = `Erdos1179OQ02Extremal`
(committed on main via #24798 b2ebd9022d3, but absent from `Proofs.lean` imports ⟹
never compiled by CI).

**Extremal vs Rigidity are NOT fully redundant** (corrects the "overlap, hermit-merge"
note). Rigidity (registered, 0ax/0sorry) proves the saturation⟺unique-repr equivalence
(`epsUniform_saturated_iff_unique_repr` + 2 corollaries). Extremal (unregistered,
0ax/0sorry — its lone "sorry" is a docstring word) adds the genuinely-new NEGATIVE
**power-of-two dichotomy** absent from Rigidity:
- `card_pow_two_of_epsUniform_zero`: any exactly-0-uniform set ⟹ `|G| = 2^j`, j ≤ |A|
  (no minimality hyp).
- `not_epsUniform_zero_of_not_pow_two`: `|G|` not a power of two ⟹ NO exactly-0-uniform
  set exists ⟹ optimal additive constant strictly positive for those N.
So registering Extremal would add real content. Blocked only by verification: it has
never been compiled, and registering it unverified risks breaking main's build.

**Why no increment this session:** the FINITE content is saturated and the genuine
open content (`g_ε(N) ≤ log₂N + O_ε(1)`, general N, w.h.p. random k-subset) is analytic
(Erdős–Hall character-sum / 2nd-moment), out of reach for finite/Lean methods. The only
actionable finite item (register Extremal) needs a build, and BOTH backends are down:
Docker gate CLOSED (9 lean-build containers on the 7.65 GiB VM, host load 13 — a 10th
build risks OOMing peers), Aristotle 404 (MCP loads, status check on a live project id
returns "Resource not found").

**Deployer action (cache-warm, not research):** add `import Proofs.Erdos1179OQ02Extremal`
to `Proofs.lean` and run `LEAN_MEMORY_LIMIT=8192 ./proofs/scripts/docker-build.sh
Proofs.Erdos1179OQ02Extremal` when the container pool drains; if green, ship the
one-line registration. Stand down on this slug for research until then or until someone
takes on the analytic Erdős–Hall upper bound as a dedicated project.
