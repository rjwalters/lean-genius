# Knowledge Base: zsqrtd-neg-two-oq-02

## Source
Seeker-selected gallery-extracted open question extending **zsqrtd-neg-two**.

**Question**: formalize the full Legendre–Gauss three-square theorem
`n = a²+b²+c² (a,b,c ∈ ℤ)  ⟺  n ≠ 4ᵃ(8b+7)` on top of the gallery's
ℤ[√−2] (norm form `x²+2y²`) development.

## Progress Summary

**Phase OBSERVE (S1, researcher-3, 2026-06-15).** Numerical grounding of the
ORIENT verdict reached qualitatively in the two prior open PRs (#24256, #24257:
"ℤ[√−2] reaches only the `x²+2y²` subset, cannot prove the full theorem"). This
session quantifies that reach, exhibits concrete gap witnesses, and pins the
elementary (formalizable) forward direction. All numbers reproducible via
`verify_three_square_observe.py` (pure Python, no Docker).

## Numerical findings (range 0..20000)

| Check | Result |
|---|---|
| three-square ⟺ `¬ 4ᵃ(8b+7)` (the target iff) | **0 mismatches** over 0..20000 |
| sums of three squares in 1..20000 | 16669 |
| …of those, representable as `x²+2y²` (ℤ[√−2] norm) | **6016 (36.1%)** |
| `x²+2y²` numbers that are NOT sums of three squares | **0** (subset confirmed) |
| smallest 3-square numbers NOT of form `x²+2y²` | 5, 10, 13, 14, 20, 21, 26, 29, 30, 35, … |

**Reading.** The ℤ[√−2] norm form is a *strict ~36% subset* of the three-square
numbers — it misses numbers as small as **5** (`= 2²+1²+0²`, but `5 ≠ x²+2y²`).
So the parent infrastructure structurally **cannot** deliver the converse: the
`x²+2y²` representation theory only certifies a proper subset, never the full
"`¬4ᵃ(8b+7) ⟹ three squares`" direction. This confirms #24256/#24257
quantitatively.

## What ℤ[√−2] *does* give (the trivial inclusion)

`x²+2y² = x² + y² + y²` ⟹ every norm-form value is a sum of three squares.
This inclusion is one-line formalizable but is the *weak* direction; it covers
only the 36% subset above, not the theorem.

## The genuinely formalizable piece: the forward obstruction

The forward direction `n = 4ᵃ(8b+7) ⟹ ¬ three squares` is fully elementary and
Lean-ready (no ANT machinery, no ℤ[√−2]):

1. **Mod-8 residues.** Squares mod 8 lie in `{0,1,4}`. The three-fold sumset
   `{0,1,4}+{0,1,4}+{0,1,4} (mod 8)` omits **7**. Hence `n ≡ 7 (mod 8)` is
   never a sum of three squares. (Finite `decide`/`Finset` check.)
2. **4-descent.** If `4 ∣ n` and `n = a²+b²+c²`, then `a,b,c` are all even
   (squares mod 4 ∈ {0,1}; three of them summing to `0 mod 4` forces all `≡0`),
   so `n/4 = (a/2)²+(b/2)²+(c/2)²`. Iterating strips the `4ᵃ` factor and reduces
   to the `8b+7` base case from step 1.

This is the substantive *provable* deliverable on this slug; the converse is the
deep direction (ternary quadratic forms / Dirichlet on primes in AP) and is the
true open work, not reachable through the `x²+2y²` norm form.

## Recommended next steps

1. **ACT (Docker-gated):** formalize the forward obstruction (steps 1–2 above)
   in Lean — `squares mod 8 ⊆ {0,1,4}` + the 4-descent — as a standalone,
   ℤ[√−2]-independent lemma. This is the piece the parent infrastructure does
   *not* help with but which IS formalizable. (Blocked this session: Docker
   blackout, `docker ps` hangs.)
2. The converse stays open; routing it via ternary forms or Dirichlet is a
   >1000-LOC foundational build, out of near-term reach and **not** served by
   ℤ[√−2]. Document the negative ORIENT verdict (now quantified) in the gallery
   so future pickers don't re-attempt the `x²+2y²` route.

## Mathlib notes

- Squares-mod-`m` residue facts: `ZMod` + `decide`.
- The four-square theorem is in Mathlib; the three-square theorem is **not**
  (the converse is the missing deep result).

---

## Session 2026-06-15 (researcher-3) — forward obstruction is ALREADY PROVEN; do not duplicate

**Mode**: REVISIT (MODERATE). **Outcome**: progress (cross-reference / anti-duplication ORIENT).

The prior "Recommended next steps" propose an ACT to formalize the forward obstruction
(`n = 4ᵃ(8b+7) ⟹ ¬ three squares`, via squares-mod-8 ⊆ {0,1,4} + 4-descent) as a standalone lemma.
**That lemma already exists, fully proved, in the gallery** — re-formalizing it would duplicate
proven infrastructure (the same dead-end the waring-g2 slug flags re: Davenport–Cassels).

- **`proofs/Proofs/ThreeSquares.lean:185`** — `excluded_form_not_sum_three_sq {n : ℕ} (h : IsExcludedForm n) : ¬∃ a b c : ℤ, a^2+b^2+c^2 = n`, with `IsExcludedForm n := ∃ a b : ℕ, n = 4^a*(8*b+7)` (line 69). **0 axioms, 0 sorries, registered.** Its proof is exactly steps 1–2 from this knowledge file (squares mod 8 ∈ {0,1,4} omits 7; strong-induction 4-descent). The file even has the `decide`-style witnesses `excluded_form_not_sum_three_sq ⟨0,0,rfl⟩` for 7, 15, 28, 31 (lines 1717–1729).
- Therefore the only genuinely OPEN piece on this slug is the **converse** (`¬4ᵃ(8b+7) ⟹ three squares`), which this slug already established (quantitatively, 36% subset) is **not** reachable via the ℤ[√−2] norm form. The converse is itself axiomatized-but-not-proved in `ThreeSquares.lean` (`not_excluded_form_is_sum_three_sq`, the Minkowski+Dirichlet route, Docker-gated) — see the `lagrange-four-squares-waring-g2-oq-03` slug, which owns that work.

**Net**: this slug needs **no new Lean** — its formalizable deliverable is subsumed by `ThreeSquares.lean`, and its deep direction is owned by the waring-g2 slug. Recommend marking the ℤ[√−2] route closed (negative verdict) and not re-attempting the forward obstruction. (No code; dual blackout re-confirmed live: docker timeout, Aristotle 404.)

## Session 2026-06-22 (researcher-1) — bridge the obstruction to the parent norm form

**Mode**: REVISIT (RICH, verdict was "no new Lean"). **Outcome**: progress (small but real:
the file's docstring is framed entirely around the ℤ[√−2] norm form `x²+2y²`, yet contained
ZERO lemmas about it — added the missing bridge).

### What I Did
- `normForm_isSumThreeSq (x y : ℤ) : ∃ a b c, a²+b²+c² = x²+2y²` — the trivial inclusion
  `x²+2y² = x²+y²+y²` (`⟨x, y, y, by ring⟩`).
- `normForm_ne_four_pow_mul (x y a b) : x²+2y² ≠ 4^a(8b+7)` — applying the existing
  contrapositive `sumThreeSq_ne_four_pow_mul` to the inclusion. The ℤ[√−2] representable
  numbers provably respect the Legendre obstruction (a proper subset of three-square numbers).

This makes the file actually engage the norm form it is *about*, and partially addresses the
file's open question "connect it to the parent ℤ[√−2] representation theorems".

### Verification — DOCKER WAS DOWN, used host single-file bypass
- `docker-build.sh` crashed mid-build with `error waiting for container: unexpected EOF`
  (exit 125), then Docker Desktop went fully down ("Docker is not installed"); restart
  (`osascript quit` + `open -a Docker`) did NOT bring the daemon back within ~9 min (disk
  was healthy at 17%, so NOT disk pressure this time — daemon just stuck).
- **BYPASS (works, matches researcher-7 memory note)**: host has `lean v4.26.0`
  (`/opt/homebrew/bin/lean`) + prebuilt Mathlib oleans in main-repo
  `proofs/.lake/packages/*/.lake/build/lib/lean`. Set
  `LEAN_PATH=$(printf '%s:' proofs/.lake/packages/*/.lake/build/lib/lean; echo proofs/.lake/build/lib/lean)`
  and run `lean <worktree-file>` directly (~seconds, no Docker). EXIT=0, no errors.
- `#print axioms` (append fully-qualified `#print axioms ZsqrtNegTwoOQ02.normForm_*` to a
  temp copy, elaborate): both new theorems depend only on `[propext, Classical.choice,
  Quot.sound]` (normForm_isSumThreeSq just `[propext]`) — NO `ofReduceBool`/`sorryAx`.
  Stays 0-axiom verified.

### Files Modified
- `proofs/Proofs/ZsqrtdNegTwoOQ02.lean` (139→162 lines, +2 thm, Step 4 section)
- `src/data/proofs/zsqrtd-neg-two-oq-02/meta.json` (counts, contributions, section, open Q)

### Next Steps (unchanged deep work)
- Sufficiency direction (Dirichlet + ternary forms) remains the genuine open work, owned by
  the `lagrange-four-squares-waring-g2-oq-03` slug; NOT reachable via ℤ[√−2].
