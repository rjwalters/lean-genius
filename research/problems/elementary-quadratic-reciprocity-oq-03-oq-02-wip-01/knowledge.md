# Knowledge: Kronecker Symbol WIP Completion

## Result (2026-07-07)

**Target 1 — full second-argument multiplicativity — is proven and machine-verified**
in `proofs/Proofs/ElementaryQuadraticReciprocityOQ03OQ02.lean` (0 sorries, 0 axioms,
builds under Mathlib v4.26).

New declarations:
- `kronecker_eq_sign_jacobi (a n : ℤ) (hn : n ≠ 0)` — normal form:
  `kronecker a n = (if n < 0 then kroneckerNeg1 a else 1) * jacobiSym a n.natAbs`.
- `kroneckerNeg1_sq` (private) — `kroneckerNeg1 a * kroneckerNeg1 a = 1`.
- `kronecker_mul_right (a m n : ℤ) (hmn : m * n ≠ 0)` — `(a/mn) = (a/m)(a/n)`.
- `kronecker_mul_right_odd` retained as the `ℕ`-typed odd-modulus corollary.

## Key insights

- **`jacobiSym.mul_right'` needs only nonzero moduli, not oddness.** The prior
  session assumed the general even/negative case required supplementary laws
  `(2/n)`, `(-1/n)`. That is true for the *classical* Kronecker symbol, but this
  file's `kronecker` definition routes the whole modulus through `jacobiSym |n|`,
  so multiplicativity is immediate from `jacobiSym.mul_right' a (b₁≠0) (b₂≠0)`.
- **Normal-form trick.** The three special-modulus branches (`n = 0, ±1`) obstruct
  a direct `split_ifs` when the three `kronecker` calls have *different* moduli
  (`m*n`, `m`, `n`). Collapsing each to `sign(n)·J(a||n|)` first makes the
  remaining case analysis purely about signs.
- **Sign multiplicativity** across a nonzero product: the only nontrivial case is
  `m<0, n<0` (then `m*n>0`), where the two sign characters must cancel — handled
  by `kroneckerNeg1_sq` (a value in `{±1}` squares to 1).
- **Scope caveat (honesty).** At even moduli the file's symbol equals Jacobi's
  value at 2, NOT the classical mod-8 character `kronecker2` (which is defined in
  the file but never wired into `kronecker`). So `kronecker_mul_right` is
  multiplicativity of the symbol *as defined* — it coincides with the classical
  Kronecker symbol at all odd moduli and at `n = ±1`. Status kept `wip`.
- **Build gotcha:** local Docker builds of this file SIGSEGV/exit-135 on the
  `#print axioms` commands (stack overflow); the origin/main version always
  *replays* its cached olean so the crash only appears once the file is edited.
  Commented the `#print axioms` block out; the file otherwise builds in ~2s.

## Update (2026-07-08) — self-reciprocity of the prime 2

New theorem `kronecker2_eq_kronecker_two (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1)`:
`kronecker2 (n : ℤ) = kronecker 2 n`, i.e. `(n/2) = (2/n)` for odd positive `n`.
This bridges the two a-priori distinct "2-characters" that coexist in the file:
- `kronecker2` — a function of the *numerator*, the even real Dirichlet character
  mod 8 (Section 6: `kronecker2_mul` / `_periodic` / `_neg` / `_values`), and
- `kronecker 2 ·` — a function of the *denominator* (Section 8: `kronecker_two_odd`).
They agree on the odd integers (both `+1` on `±1 mod 8`, `−1` on `±3 mod 8`), so
the proof is `kronecker_two_odd` + `unfold kronecker2` + a residue comparison by
`omega`. Build-verified (3058 jobs, 0 sorries, 0 axioms). `theoremCount` 25→26.

*Build note:* the file still exhibits the documented exit-135 SIGSEGV on the
first fresh build after an edit (elaborates fully — `3058/3058` — then crashes on
finalization). A plain retry builds green (environmental / shared-volume, not a
proof error). Do NOT edit the proof in response to a line-less 135.
*(Reproduced again 2026-07-08: fresh build `✖ 135` at `3058/3058`, plain retry
`✔ Built`. Same behaviour, same fix.)*

## Update (2026-07-08 #2) — denominator-side periodicity of the supplementary characters

Two new theorems establish that the two *denominator-side* quadratic characters
are periodic Dirichlet characters (theoremCount 26→28, lineCount 477→510,
0 sorries / 0 axioms):
- `kronecker_neg_one_periodic (n hn hno)` — for odd positive `n`,
  `(-1/(n+4)) = (-1/n)`: the sign character `(-1/·)` is periodic mod 4.
- `kronecker_two_periodic (n hn hno)` — for odd positive `n`,
  `(2/(n+8)) = (2/n)`: the character `(2/·)` is periodic mod 8.

Both are one-liners off the Section-8 supplementary laws: rewrite the numeral
addition `(n:ℤ)+k = ((n+k:ℕ):ℤ)` (`push_cast; ring`), apply `kronecker_neg_one_odd`
/`kronecker_two_odd` on both sides, then close with `(n+k)%k = n%k` by `omega`.

**Why this matters (honest framing).** These are the *denominator-side* complement
of `kronecker2_periodic` (which is the *numerator* character `(·/2)`). Combined
with `kronecker_mul_right` (multiplicativity in the denominator), they exhibit the
supplementary characters `(-1/·)` and `(2/·)` as Dirichlet characters mod 4 and mod
8 — the periodicity + multiplicativity data the Gauss-sum route to generalized
reciprocity (refinement 2) rests on. This is incremental structural progress, not
the reciprocity core itself, which still needs the Gauss sum (open).

## Open work

1. Refine `kronecker` to use `kronecker2` at the 2-adic part (→ classical symbol
   at even moduli), then re-prove `kronecker_mul_right` for the refined def.
   (`kronecker2_eq_kronecker_two` is a step toward this: it shows the refined and
   current defs would agree at odd moduli, so only the even branch changes.)
2. Target 2: generalized quadratic reciprocity for arbitrary fundamental
   discriminants — supplementary laws (done: `kronecker_neg_one_odd`,
   `kronecker_two_odd`) + Gauss sums (open).
# Knowledge: elementary-quadratic-reciprocity-oq-03-oq-02-wip-01 (Kronecker Symbol WIP)

Target file: proofs/Proofs/ElementaryQuadraticReciprocityOQ03OQ02.lean (gallery
elementary-quadratic-reciprocity-oq-03-oq-02). File is otherwise COMPLETE (0 real
sorries — the 9 grep hits are all "`sorry`-free" comments; 0 axioms; no
native_decide). Full two-argument multiplicativity + supplementary-law/χ-character
dictionary (χ₄, χ₈, χ₈') already present from prior sessions.

## Session 2026-07-08 (researcher-1) — {−1,0,1}-valued (real quadratic character)

The full `kronecker` symbol lacked the basic "real character" property (only
`kronecker2` had `kronecker2_values`). Added it (3 thm, VERIFIED 0/0):
- `kronecker_trichotomy (a n) : kronecker a n = 0 ∨ = 1 ∨ = -1`. Proof: n=0 →
  `kronecker0` (if-split, tauto); n≠0 → `kronecker_eq_sign_jacobi` normal form,
  sign ∈{-1,1} (split_ifs on kroneckerNeg1), `jacobiSym.trichotomy a n.natAbs`
  gives J∈{0,1,-1}, product cases via ring.
- `kronecker_abs_le_one : |kronecker a n| ≤ 1` — rcases trichotomy <;> norm_num.
- `kronecker_sq_mem : kronecker a n ^ 2 = 0 ∨ = 1` (order-two character) — same.

This is exactly the "real Dirichlet character" object the Gauss-sum route consumes.
File 677 L, 44 thm, 0 axioms, 0 sorries. VERIFIED (TWO line-less exit-135 SIGBUS at
olean-write [3058/3058] no elab errors → `--repair-cache` then rebuild green 2.7s;
plain retry alone did NOT fix, repair-cache did). Pre-existing linter warning
line 304 `done` does nothing — not mine, untouched.

## Still open (NOT session-sized)
- Wire `kronecker2` into the definition so it becomes the classical symbol at even
  moduli, re-prove `kronecker_mul_right` for the refined def.
- Target 2: generalized reciprocity for fundamental discriminants (Gauss sums).
Key API: jacobiSym.trichotomy / eq_one_or_neg_one / eq_zero_iff_not_coprime[NeZero].

## Session 2026-07-08 (researcher-3) — (-2/·) supplementary character completed

The three nontrivial supplementary characters mod 8 had asymmetric coverage:
`(-1/·)` and `(2/·)` each had an explicit residue-table `if`-form
(`kronecker_neg_one_odd`, `kronecker_two_odd`) AND a periodicity lemma
(`kronecker_neg_one_periodic` mod 4, `kronecker_two_periodic` mod 8), but the
combined character `(-2/·)` had only the abstract bridges (`= χ₈'`, `= (-1/·)·(2/·)`).
Filled the gap (2 thm, VERIFIED 0/0, leanFile 676→709 L / 44→46 thm):

- `kronecker_neg_two_odd (n hn hno)`: `(-2/n) = if n%8=1∨n%8=3 then 1 else -1`.
  One-liner mirroring `kronecker_two_odd`: `kronecker_eq_jacobi` +
  `jacobiSym.at_neg_two` (`J(-2|n)=χ₈' n`) + `ZMod.χ₈'_nat_eq_if_mod_eight` +
  `if_neg` on the even branch. Note the `+1` classes are `{1,3} mod 8` (where χ₈'
  is +1), DISTINCT from the `{1,7}` classes of `(2/·)` — the two mod-8 characters
  split the odd residues differently.
- `kronecker_neg_two_periodic (n hn hno)`: `(-2/(n+8)) = (-2/n)`. Mirrors
  `kronecker_two_periodic`; period is 8 (NOT 4) because the character carries the
  mod-8 part χ₈, so unlike `(-1/·)` it is not periodic mod 4.

Every one of the three supplementary characters now has: value-table + periodicity
+ canonical-χ bridge — the complete Dirichlet-character data the Gauss-sum route
(Target 2) consumes. Still open (unchanged, NOT session-sized): (1) wire `kronecker2`
into the def for the classical symbol at even moduli; (2) generalized reciprocity
via Gauss sums.

*Build:* green first try (3058 jobs, 2.7s) — no SIGBUS this cycle. Pre-existing
line-304 `done`-does-nothing linter warning is not mine (untouched).

## Update (2026-07-09, researcher-4 — PR #36433)

Added **Section 10: numerator-negation supplementary law** to
`ElementaryQuadraticReciprocityOQ03OQ02.lean` (5 theorems, 0 sorries/axioms, build exit 0).
This fills the numerator-side sign gap: `(-a/n) = (-1/n)·(a/n) = χ₄(n)·(a/n)`, the
numerator analog of the denominator law `kronecker_neg_one_odd`.
- `kronecker_neg_numerator` (general modulus), `kronecker_neg_numerator_eq_χ₄`
  (canonical `ZMod.χ₄`), `kronecker_neg_numerator_if` (residue table),
  `kronecker_neg_numerator_one_mod_four` / `_three_mod_four` (parity corollaries).
- All reduce to `kronecker_mul_left` + `kronecker_neg_one_odd`/`_eq_χ₄` + omega/ring.
- Reusable ingredient for the still-open generalized-reciprocity (Gauss-sum) core (Target 2).
Still open: Target 2 Gauss-sum reciprocity core; refinement (1) wiring `kronecker2` into
the even-modulus branch.

## Update (2026-07-09, researcher-6 — PR pending)

Added **Section 11: remaining character-axiom normalizations** to
`ElementaryQuadraticReciprocityOQ03OQ02.lean` (2 theorems, 0 sorries/axioms).
Both stated WIP Targets (`kronecker_mul_left`/`kronecker_mul_right`) are ALREADY DONE
(lines 296/341); this fills the two omitted Dirichlet-character axioms for `(·/n)`:
- `kronecker_zero_left (n) (hn0 hn1 hnm1) : kronecker 0 n = 0` — the `χ(0)=0` companion
  to the existing `χ(1)=1` `kronecker_one_left`. Via `kronecker_eq_sign_jacobi 0 n hn0`
  + `jacobiSym.zero_left (hb : 1 < n.natAbs)` (`omega` gets `1<natAbs` from n∉{0,±1}) + `mul_zero`.
- `kronecker_sq_eq_one_of_coprime (a n hn hno h) : kronecker a n ^ 2 = 1` — sharpens the
  unconditional `kronecker_sq_mem` (∈{0,1}) to `=1` on units; rcases
  `kronecker_eq_one_or_neg_one_of_coprime` + norm_num.

**Build status: elaboration-clean, UNVERIFIED (olean-write SIGBUS-135).** ~9 docker runs
all reached `[3058/3058]` and elaborated my file cleanly (0.3–4.1s, never a `.lean` error),
then exit 135 at the olean write — the documented environmental crash for this larger file
(809 L). `docker-repair-cache.sh` (full 7727-file refresh) did NOT clear it this cycle.
Prior sessions (R3/R4) on this same file eventually built green when the env cooperated;
the 2 added lemmas depend only on already-proven in-file results + Mathlib `jacobiSym.zero_left`.

Still open (unchanged, NOT session-sized): Target 2 Gauss-sum generalized reciprocity core;
refinement (1) wiring `kronecker2` into the even-modulus branch.

## Session 2026-07-22 (researcher-1) — Section 15: refinement target 1 DONE (classical Kronecker symbol)

Wired `kronecker2` into the 2-adic part — the long-flagged "NOT session-sized" refinement
turned out session-sized once the right decomposition was found. 7 theorems + 1 def,
host-verified (`lake env lean` exit 0; `#print axioms` = [propext, Classical.choice,
Quot.sound] on all 7; no sorry/native_decide; file 1254→1446 L):

- `kroneckerClassical a n := if n = 0 then kronecker0 a else sign * kronecker2 a ^ v₂(|n|) * J(a | |n|/2^v₂)`.
  KEY SIMPLIFICATION: no special ±1 branches needed (at n=±1 the valuation is 0 and odd
  part is 1, so the formula collapses to the sign character) — normal form is definitional.
- `kroneckerClassical_eq_kronecker_of_odd` / `_eq_jacobi`: agreement at odd moduli — ALL
  Sections 4–14 odd-modulus results transfer verbatim.
- `kroneckerClassical_two` / `_two_pow`: (a/2) = kronecker2 a, (a/2^k) = kronecker2^k —
  the defining classical values the original def lacked.
- `kroneckerClassical_eq_sign_mul_kronecker`: bridge — classical = sign · (a/2)^v · kronecker(odd part).
- `kroneckerClassical_mul_right` (THE stated WIP target), `_mul_left` (all moduli incl 0),
  `_pow_right`: full bi-multiplicativity for the refined def. χ₈ multiplicativity imported
  via `kronecker2_mul`, NOT re-derived.

API notes: `ord_compl[p]` NOTATION DOES NOT EXIST in this Mathlib — use camelCase lemmas
about the raw expression `n / p ^ n.factorization p`: `Nat.ordCompl_mul`, `Nat.ordCompl_pos`,
`Nat.not_dvd_ordCompl`, plus `Nat.factorization_mul`+`Finsupp.add_apply` (valuation additive),
`Nat.Prime.factorization_pow`+`Finsupp.single_eq_same`. All with existing imports.
Gotchas: `Nat.pos_pow_of_pos` gone (use `pow_pos`); `Nat.dvd_iff_mod_eq_zero` now takes no
explicit args. Host `lake env lean` sidesteps the documented Docker olean-write SIGBUS-135.

### Still open
- Target 2 ONLY: generalized reciprocity for fundamental discriminants (Gauss sums) — deep,
  NOT session-sized. Everything else on this file is done.

## Session 2026-07-24 (researcher-1) — classical product form

**Route (by mechanism): parity bookkeeping over the qstar form (no new number theory).**

- `legendreSym_neg_one_eq_pow q hq2 : legendreSym q (-1) = (-1)^((q-1)/2)` — Euler
  criterion (`legendreSym.eq_pow`) + `q/2 = (q-1)/2` for odd q + file-private
  `int_pm_one_cast_inj` for ±1 descent. Deliberately avoids Mathlib `χ₄`/`at_neg_one`
  (those live in the QR file) to keep the independence claim airtight.
- `quadratic_reciprocity_product` — case split on parity of `(q-1)/2`: even ⇒ qstar
  says (p|q) = (q|p) and RHS = 1 via `Nat.even_mul`; odd ⇒ `legendreSym.mul` splits
  (−1·q), the supplement supplies `(-1)^((p-1)/2)`, `pow_mul` + 2-case parity closes RHS.
- Gotcha: `legendreSym.eq_one_or_neg_one` takes the prime as an explicit arg — bare
  application elaborates the hypothesis as the prime (type mismatch at ℕ).
