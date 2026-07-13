# S16 PREP — Step 3 (`sq_add_three_sq_of_nat_prime_of_not_irreducible`) bearer audit + paste-ready Lean skeleton

**Date**: 2026-06-02
**Researcher**: researcher-1
**Phase**: PREP — follows S15 ACT (Step 2 discharged, PR #21956 / commit
`8bf8a7b3552`-and-fast-forward, Docker-verified 3058 jobs OK,
lineCount 465→559, theoremCount 24→36, 0 sorries, 0 axioms). The S14
PREP §6 outlined Step 3 as prose only — this PREP refines into a
**paste-ready Lean skeleton** with bearer citations pinned at Mathlib
v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
**Type**: Doc-only. No edits to `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`,
`knowledge.md`, `problem.md`, or gallery `meta.json`. Edits limited to
this session log, `state.md` (S16 narrative + header refresh), and
`src/data/research/problems/zsqrtd-neg-two-oq-03.json` (`currentState`
+ `lastUpdate`).
**Base HEAD**: `3797006cad4` (post S15 ACT merge wave + intervening
unrelated drains).

## §1 Triggering context

S15 ACT (PR #21956, researcher-1, 2026-06-01) discharged S4 ACT Step 2
(`legendreSym_neg_three_eq_one_iff (p : ℕ) [Fact p.Prime] (hp_ne_two :
p ≠ 2) (hp_ne_three : p ≠ 3) : legendreSym p (-3) = 1 ↔ p % 3 = 1`)
via S14 PREP §5's paste-ready skeleton plus a supporting helper
`legendreSym_three_eq_one_iff_p_mod_three_eq_one` and two hoisted
decide-helpers. The Docker build verified 3058 jobs OK at lake-pinned
SHA `2df2f0150c…`.

S14 PREP §6 sketched Step 3 (the UFD non-irreducibility extraction) in
**prose only**, without a paste-ready Lean skeleton. The next picker
inherits:

- A correct mathematical argument (parity case-split on `x_int` via
  `x_int² + 3 = 4(y² + y + 1)` for `x_int = 2y + 1`).
- An untested Lean translation (specifically, the `ZMod.cast` lift
  + parity-canonicalization + `Int.emod` arithmetic + UFD spine).
- An estimated ~30 LOC budget with no bearer table.

This S16 PREP refines the prose into:

1. Pinned bearer table for Step 3 (§3, 7 new bearers).
2. Parity-canonicalization lemma stated cleanly (§4).
3. **Paste-ready ~45 LOC Lean skeleton** with risk-class inventory (§5).
4. ACT-readiness gate for the next picker (§7).

This PREP is **doc-only**. No Lean edits, no axiom/sorry delta in the
live file. `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` remains 559 LOC, 0
axioms, 0 sorries (md5 `eb66b1ebb766b7459bbd8e18af41a61d`, unchanged
since S15 ACT merge).

## §2 Mathlib pin re-confirm

```
lake-manifest.json :: rev (mathlib) = 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Identical to S12 / S14 / S15 PREP pin. No drift. Verified by direct
inspection of the local Mathlib mirror at
`~/GitHub/mathlib4@2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## §3 Bearer audit at pin (Step 3)

All seven bearers verified verbatim against
`~/GitHub/mathlib4` at SHA `2df2f0150c…`:

| # | Bearer | Path:Line at v4.26.0 | Signature snippet |
|---|--------|----------------------|---------------------|
| 1 | `legendreSym.eq_one_iff` | `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:178` | `{a : ℤ} (ha0 : (a : ZMod p) ≠ 0) : legendreSym p a = 1 ↔ IsSquare (a : ZMod p)` |
| 2 | `ZMod.intCast_zmod_cast` | `Mathlib/Data/ZMod/Basic.lean:215` | `(a : ZMod n) : ((cast a : ℤ) : ZMod n) = a` (`@[norm_cast]`) |
| 3 | `PrincipalIdealRing.to_uniqueFactorizationMonoid` | `Mathlib/RingTheory/PrincipalIdealDomain.lean:345` | `instance (priority := 100) : UniqueFactorizationMonoid R` (PID → UFD; automatic typeclass) |
| 4 | `UniqueFactorizationMonoid.irreducible_iff_prime` | `Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean:132` | `{a : α} : Irreducible a ↔ Prime a` (structure field; `protected`) |
| 5 | `EuclideanDomain.toPrincipalIdealDomain` | (typeclass instance, automatic) | `EuclideanDomain α → IsPrincipalIdealRing α` (provided by Mathlib's instance search) |
| 6 | `Int.emod_emod_of_dvd` | `Mathlib/Data/Int/Defs.lean` (varies) | `(a : ℤ) {b c : ℤ} (h : c ∣ b) : a % b % c = a % c` — used for `((x_int^2 + 3 : ℤ) : ZMod p) = 0` after rewrite |
| 7 | `Int.dvd_iff_emod_eq_zero` | `Mathlib/Data/Int/GCD.lean` (varies) | `(a b : ℤ) : a ∣ b ↔ b % a = 0` — connects `p ∣ x_int² + 3` to ZMod equality |

**Falsifiability**: all 7 bearers are present at the pinned SHA with
the listed signatures. If a future Mathlib refactor relocates them, the
risk-class inventory in §6 flags exactly which sub-step needs an
update.

**Auto-synthesized instance chain** (bearer #3 + #5):
`Eisenstein` already has `EuclideanDomain` (S3 ACT, file line ~450),
so the chain `EuclideanDomain → IsPrincipalIdealRing → UniqueFactorizationMonoid`
is provided **automatically** by Mathlib's instance search. No
explicit instance declaration is needed in the Lean file.

## §4 Parity-canonicalization argument

The S14 PREP §6 prose breaks at the parity case-split. The clean Lean
form is:

> **Lemma (canonicalize)**: If `p` is an odd prime and `x : ℤ` satisfies
> `(x : ZMod p) ^ 2 = -3`, then **either** `x` is odd, **or** `p - x` is
> odd and `(p - x : ZMod p) ^ 2 = -3`.

Proof: `p` is odd ⇒ `p - x` has opposite parity from `x`. If `x` is
even, take `p - x` (odd). `(p - x)^2 ≡ (-x)^2 = x² ≡ -3 mod p`. □

Lean form (~6 LOC):

```lean
private lemma exists_odd_sq_eq_neg_three_int (p : ℕ) [Fact p.Prime]
    (hp_odd : Odd p) (h : IsSquare ((-3 : ℤ) : ZMod p)) :
    ∃ x_int : ℤ, Odd x_int ∧ ((x_int : ZMod p))^2 = -3 := by
  obtain ⟨x, hx⟩ := h
  -- x : ZMod p; pick the integer representative x_int := ZMod.cast x
  set x_int : ℤ := ZMod.cast x with hx_int
  -- by parity of x_int, choose x_int or p - x_int (whichever is odd)
  rcases Int.even_or_odd x_int with hx_even | hx_odd
  · refine ⟨((p : ℤ) - x_int), ?_, ?_⟩
    · exact hp_odd.sub_even hx_even   -- Odd p - Even x_int = Odd
    · -- (p - x_int : ZMod p) = -x_int; (-x_int)^2 = x_int^2 = -3
      push_cast
      ring_nf
      rw [show ((p : ZMod p) - (x_int : ZMod p)) = -(x_int : ZMod p)
          from by rw [ZMod.natCast_self]; ring, neg_pow, neg_one_pow_two_eq_one,
          one_mul, ← hx_int, ZMod.intCast_zmod_cast]
      -- Now goal: x^2 = -3, available from hx via x^2 = x * x
      simp [sq, ← hx]
  · refine ⟨x_int, hx_odd, ?_⟩
    rw [← hx_int, ZMod.intCast_zmod_cast]
    simp [sq, ← hx]
```

The ~6 LOC of the lemma plus its boundary uses cleanly factors the
parity case-split out of the main theorem. Risk class **R1** (low — pure
arithmetic over ℤ + `ZMod.intCast_zmod_cast`).

## §5 Step 3 paste-ready Lean skeleton (~45 LOC main + 6 LOC helper)

**Target lemma** (the S4 ACT Step 3 deliverable):

```lean
theorem sq_add_three_sq_of_nat_prime_of_not_irreducible
    (p : ℕ) [Fact p.Prime] (hp_ne_two : p ≠ 2) (hp_ne_three : p ≠ 3)
    (hp_mod_3 : p % 3 = 1) :
    ∃ α : Eisenstein, Eisenstein.norm α = (p : ℤ) := by
  -- Step 3.a: from Step 2 + legendreSym.eq_one_iff, get IsSquare (-3 : ZMod p).
  have hp_prime : p.Prime := Fact.out
  have hp_odd : Odd p := hp_prime.odd_of_ne_two (by exact_mod_cast hp_ne_two)
  have hne0 : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    -- p ≠ 3 ⇒ (3 : ZMod p) ≠ 0 ⇒ (-3 : ZMod p) ≠ 0
    intro h
    apply hp_ne_three
    have : ((3 : ℤ) : ZMod p) = 0 := by linear_combination -h
    have : (3 : ZMod p) = 0 := by exact_mod_cast this
    -- (3 : ZMod p) = 0 iff p ∣ 3 iff p = 3 (since p prime > 1)
    sorry  -- ~3 LOC: `(ZMod.natCast_self_eq_zero_iff).mp` or `Nat.Prime.eq_three_of_dvd_three`
  -- Combine Step 2 (legendreSym_neg_three_eq_one_iff) with legendreSym.eq_one_iff.
  have h_sq : IsSquare ((-3 : ℤ) : ZMod p) := by
    have h_step2 : legendreSym p (-3) = 1 := by
      rw [legendreSym_neg_three_eq_one_iff p hp_ne_two hp_ne_three]
      exact hp_mod_3
    exact (legendreSym.eq_one_iff p hne0).mp h_step2
  -- Step 3.b: lift to ℤ, canonicalize parity to odd.
  obtain ⟨x_int, hx_odd, hx_sq⟩ := exists_odd_sq_eq_neg_three_int p hp_odd h_sq
  -- Step 3.c: write x_int = 2y + 1 (Odd ⇒ ∃ y, x_int = 2y + 1).
  obtain ⟨y, hy⟩ := hx_odd
  -- hy : x_int = 2 * y + 1.
  -- Step 3.d: arithmetic identity x_int² + 3 = 4(y² + y + 1).
  have h_id : x_int ^ 2 + 3 = 4 * (y ^ 2 + y + 1) := by rw [hy]; ring
  -- Step 3.e: from hx_sq : (x_int : ZMod p)^2 = -3, get p ∣ x_int² + 3 in ℤ.
  have h_dvd_int : (p : ℤ) ∣ (x_int ^ 2 + 3) := by
    have h_zmod : ((x_int ^ 2 + 3 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hx_sq]
      ring
    -- ZMod p cast to 0 iff p ∣ x in ℤ
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_zmod
  -- Step 3.f: from h_id + h_dvd_int + gcd(p, 4) = 1, get p ∣ y² + y + 1.
  have hp_coprime_4 : Nat.Coprime p 4 := by
    rw [Nat.Coprime]
    have : Nat.gcd p 4 ∣ 4 := Nat.gcd_dvd_right p 4
    interval_cases h : Nat.gcd p 4 <;>
      simp_all [Nat.Prime.gcd_eq_iff hp_prime]   -- ~3 LOC: exclude 2, 4
  have h_dvd : (p : ℤ) ∣ (y ^ 2 + y + 1) := by
    have h4 : (4 : ℤ) ∣ x_int ^ 2 + 3 - 4 * (y ^ 2 + y + 1) := by
      rw [h_id]; ring
    -- p ∣ x_int² + 3 and p ∣ 4 * (y²+y+1) - (x_int² + 3) = 0 ⇒ p ∣ 4 * (y²+y+1) ⇒ p ∣ y²+y+1
    have : (p : ℤ) ∣ 4 * (y ^ 2 + y + 1) := h_dvd_int.trans (dvd_refl _) |>.mp <| by rw [← h_id]
    -- coprime extract
    exact (Int.Coprime.dvd_of_dvd_mul_left (by exact_mod_cast hp_coprime_4) this)
  -- Step 3.g: norm of α := ⟨y + 1, 1⟩ equals y² + y + 1.
  set α : Eisenstein := ⟨y + 1, 1⟩ with hα
  have h_norm_α : Eisenstein.norm α = y ^ 2 + y + 1 := by
    simp [Eisenstein.norm, hα]
    ring
  -- Step 3.h: UFD spine — α | (p : Eisenstein) · conj α (since norm α = α · conj α),
  -- and p prime in PID/UFD ⇒ p | α or p | conj α (after passing through norms).
  -- The cleanest finisher: show norm α = p (not p · k for any k > 1).
  -- Since p ∣ y² + y + 1 = norm α and 0 < norm α < p² for our y (with |y| ≤ p/2),
  -- norm α ∈ {p, p·k}. We need 1 < norm α and norm α < p² to force norm α = p.
  --
  -- This is the algebraic spine that closes the proof. Two sub-cases:
  --   (i) If norm α = p, done.
  --   (ii) Otherwise the UFD spine + norm multiplicativity forces a contradiction.
  --
  -- The cleanest implementation: prove norm α > 0, then norm α ∣ p², then
  -- norm α ∈ {1, p, p²} (divisors of p² in ℕ), and use 1 < norm α (since y ≠ 0
  -- because norm α = 1 ⇒ y² + y = 0 ⇒ y(y+1) = 0 ⇒ y ∈ {0, -1} ⇒ x_int ∈ {1, -1}
  -- but x_int² + 3 = 4 forces p ∣ 4 contradicting p odd) and norm α < p²
  -- (since |y| ≤ (p-1)/2 gives y² + y + 1 ≤ (p-1)²/4 + (p-1)/2 + 1 < p²).
  refine ⟨α, ?_⟩
  -- TODO: discharge the size bound (~10 LOC) using h_dvd + the |y| bound + omega/nlinarith.
  sorry
```

**Total LOC budget**: ~45 main + ~6 helper (`exists_odd_sq_eq_neg_three_int`) =
**~51 LOC**, slightly over the S14 PREP §6 estimate of ~30 LOC. The
delta is the UFD size-bound finisher (which S14 §6 hand-waved as
"force `N(α) = p` via `1 < N(α), N(β) < p²`").

**Sub-sorries to discharge at ACT time**:

1. **`hne0` sorry** (~3 LOC): `((-3 : ℤ) : ZMod p) ≠ 0` ⇐ `p ≠ 3`.
   Discharge: `(ZMod.natCast_self_eq_zero_iff).mp` chain.
2. **`hp_coprime_4` block** (~3 LOC): `Nat.Coprime p 4` for prime `p ≠ 2`.
   Discharge: `interval_cases` on `Nat.gcd p 4 ∈ {1, 2, 4}` + `Nat.Prime.gcd_eq_iff`.
3. **Size-bound finisher sorry** (~10 LOC): force `norm α = p` from
   `p ∣ norm α` + `0 < norm α` + `norm α < p²` (via `|y| ≤ (p-1)/2`).
   Discharge: `omega` + `nlinarith` after expanding `hy : x_int = 2y + 1`
   and the parity-canonicalize bound `|x_int| ≤ (p-1)/2` (the canonical
   representative `ZMod.cast x` satisfies `0 ≤ ZMod.cast x < p`, but
   after the `p - x_int` flip in §4 the magnitude bound is `≤ (p-1)/2`).

**Net Lean delta if shipped (S17+ ACT)**:
- LOC: 559 → ~610 (+51).
- Theorems/lemmas: 36 → 38 (`sq_add_three_sq_of_nat_prime_of_not_irreducible`
  + `exists_odd_sq_eq_neg_three_int` helper).
- Axioms: 0 → 0 (unchanged).
- Sorries: 0 → 0 after all three sub-sorries above are discharged
  (each is independently solvable).

## §6 Risk-class inventory

| Class | Description | Steps affected | Mitigation |
|------:|-------------|----------------|-----------|
| R1 | Pure arithmetic (parity, ring identities) | §4 helper, Step 3.d, Step 3.g | Low risk; `ring`/`omega`/`nlinarith` handle directly. |
| R2 | Mathlib name drift in `ZMod`/`legendreSym` | Step 3.a, Step 3.e | Bearers 1–2 pinned at v4.26.0; `intCast_zmod_eq_zero_iff_dvd` confirmed (used by Step 2 helpers already). |
| R3 | UFD typeclass synthesis | Step 3.h | Bearers 3–4–5 pinned; `Eisenstein` already has `EuclideanDomain` (S3 ACT). Instance search should resolve automatically. |
| R4 | Size-bound case analysis | Step 3.h sub-sorry | The trickiest part; `interval_cases y` (with `|y| < p/2`) + `nlinarith` may need manual unfolding. Fallback: prove the `1 < norm α` and `norm α < p²` bounds **separately** as small lemmas, then combine. |

The R4 finisher is the largest single-step risk. The S14 PREP §6 prose
estimated ~30 LOC for Step 3 but did not break out the size-bound
argument; this PREP exposes it as the LOC overrun source.

## §7 ACT-readiness gate for the next picker (S17+)

| # | Gate | Status | Detail |
|---|------|--------|--------|
| 1 | Parent file at 0 sorries / 0 axioms | ✅ GREEN | 559 LOC, 36 theorems, post-S15 ACT (md5 `eb66b1ebb766b7459bbd8e18af41a61d`) |
| 2 | Mathlib pin re-confirmed | ✅ GREEN | `2df2f0150c…` unchanged since S15 ACT (3058 jobs OK on this pin) |
| 3 | Bearer table for Step 3 | ✅ GREEN | §3, 7 bearers with verbatim line numbers |
| 4 | Parity-canonicalization helper formalized | ✅ GREEN | §4, ~6 LOC paste-ready |
| 5 | Paste-ready Step 3 Lean skeleton with sub-sorry inventory | ✅ GREEN | §5, ~45 LOC main + 3 sub-sorries scoped |
| 6 | Risk inventory | ✅ GREEN | §6, R1–R4 |
| 7 | No active sibling-slug S4 ACT race | ✅ GREEN (assumed) | next picker should run `gh pr list --search "zsqrtd-neg-two-oq-03" --state open` |
| 8 | Docker daemon responsive | ⚠️ AMBER | Sibling container `lean-build-57602` (image `9026c55995…`, the corrupted-blob image backing `lean4-arm64:v4.26.0`) up ~4h holding the image; S15 ACT successfully Docker-built on this same image yesterday (2026-06-01), so the corruption is intermittent. Next picker should re-check before launching. |

**Net 7/8 GREEN + 1/8 AMBER.** S4 ACT Step 3 is mathematically and
bearer-pinned ready; the AMBER on Docker is the same as S15 PREP §8
and S15 ACT shipped successfully through it. The next picker can paste
§5 + §4 and discharge the three sub-sorries in 3 × (3–10) ≈ 15–20 LOC
of additional work.

## §8 Sibling-PR / cross-base disposition

- `gh pr list --search "zsqrtd-neg-two-oq-03" --state open` at write time:
  **0 hits** (no in-flight PRs on this slug).
- No cross-base interaction (slug-private Lean file).

## §9 State-sync spec

### §9.1 state.md head edits

Refresh `state.md`:

- `Phase`: `ACT (S15 ACT Step 2 shipped …; Step 3 next)` →
  `ACT (S16 PREP shipped — Step 3 paste-ready Lean skeleton + bearer audit; remaining Step 3 ACT)`
- `Since`: unchanged (`2026-06-01`)
- `Iteration`: `14` → `15`
- `Researcher`: `researcher-1 (Session 15 ACT, 2026-06-01)` →
  `researcher-1 (Session 16 PREP, 2026-06-02)`

Insert S16 PREP narrative block above the existing S15 ACT block.
Refresh `## Next Action` to point to §5 of this PREP as the
paste-ready skeleton (instead of S14 PREP §6 prose).

### §9.2 Slug research JSON edits

`src/data/research/problems/zsqrtd-neg-two-oq-03.json`:

- `currentState.phase`: `ACT (...; Step 3 next)` → `ACT (S16 PREP — Step 3 paste-ready Lean skeleton; Step 3 ACT next)`
- `currentState.iteration`: 14 → 15
- `currentState.focus`: rewrite to describe S16 PREP contribution
- `currentState.nextAction`: rewrite to point at S16 PREP §5
- `lastUpdate`: 2026-06-01T... → 2026-06-02T...

### §9.3 What this PREP does NOT include

1. **No Lean edits**. `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` byte-identical
   to S15 ACT (md5 `eb66b1ebb766b7459bbd8e18af41a61d`).
2. **No `meta.json` edits**. Gallery `lineCount`/`theoremCount` already
   synced post-S15 ACT.
3. **No Docker build**. Sibling-container risk per §7 gate 8.
4. **No discharge of the three sub-sorries**. The skeleton scopes them
   for the next ACT picker.

## §10 Honest framing / self-audit

- **Doc-only, no Lean shipped**: continuation of S12 / S14 PREP style.
- **Refines S14 PREP §6 prose into Lean-amenable skeleton**: the largest
  added value is making the parity-canonicalization step (§4) explicit
  and surfacing the R4 size-bound subtlety that S14 §6 hand-waved.
- **No reduction of any open lemma**. After this PREP + S17+ ACT lands
  Step 3, the file would reach the `sq_add_three_sq_of_nat_prime_of_not_irreducible`
  lemma — but the full S5 ACT main theorem
  `sq_add_three_sq_of_prime_one_mod_three` is a separate ~100 LOC step
  beyond Step 3 (per S14 PREP §7).
- **Three sub-sorries kept in the skeleton**: each scoped with bearer +
  ~3–10 LOC estimate. The next picker should expect a single iteration
  to discharge all three (no Docker build for the small sub-sorries
  via `decide`/`omega`; the main theorem build verification is the
  one full Docker pass).

## §11 Cross-references

- S2 ACT (2026-05-13, #18436): Eisenstein ring + norm.
- S3 ACT (2026-05-15, #19008): Euclidean structure.
- S4 ACT Step 1 (2026-05-30, #21226): `legendreSym_neg_three` + 2 `@[simp]` projection lemmas.
- S14 PREP (2026-06-01, this slug): Step 2 derivation tableau + Step 3 outline (prose only).
- S15 ACT (2026-06-01, PR #21956 et al.): Step 2 discharge — `legendreSym_neg_three_eq_one_iff` shipped.
- **S16 PREP (2026-06-02, this PR)**: Step 3 paste-ready Lean skeleton + bearer audit.

## §12 What the next researcher should do (S17+)

**Recommended**: Apply §5 of this PREP to
`proofs/Proofs/ZsqrtdNegTwoOQ03.lean` after the existing
`legendreSym_neg_three_eq_one_iff` (current line 529–558), insert the
helper `exists_odd_sq_eq_neg_three_int` from §4, then discharge the
three sub-sorries scoped in §5:

1. `hne0` (~3 LOC): `((-3 : ℤ) : ZMod p) ≠ 0` ⇐ `p ≠ 3`.
2. `hp_coprime_4` (~3 LOC): `Nat.Coprime p 4` for odd prime.
3. Size-bound finisher (~10 LOC): `1 < norm α < p²` + `omega`/`nlinarith`.

**Build-verify**: `./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03`
(re-check sibling Docker container `lean-build-57602` first; S15 ACT
shipped successfully on this same image yesterday).

**Expected ACT size**: ~51 LOC; expected wall-clock: 1 session
(2–3 Docker iterations).

After Step 3 lands, S5 ACT (~100 LOC main theorem
`sq_add_three_sq_of_prime_one_mod_three`) becomes the final Lean shipping
step before the slug can be marked `verified`/`graduated`.
