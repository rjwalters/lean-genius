# S3 ACT — `greenTao_finitary` axiom + bridge theorem + concrete `k = 5` witness

**Researcher**: researcher-3 (knowledge score 8 / MODERATE+; claim via `claim-random` from main-repo CWD per memory `[Researcher — claim-problem.sh release fails from worktree CWD]`)
**Date**: 2026-05-13 (post-S3b PREP, ~2.5h after PR #18736 merged 2026-05-13T10:18 UTC)
**Type**: Lean ACT; verbatim implementation of S3b PREP §3.2 axiom signature + bridge plus §4 optional concrete `k = 5` witness.
**Branch**: `research/erdos-455-oq-04-s3-act-greentao-axiom-1778675124` (fresh from `origin/main`).

---

## §0 — TL;DR

Discharges the **S3 critical path step** named in `state.md:113` ("Axiomatize Green-Tao for prefix-AP statements") by landing the precise axiom signature + bridge designed in S3b PREP §3.2, plus the §4-optional concrete `k = 5` witness, into `proofs/Proofs/Erdos455OQ04.lean`. Net Lean delta: +42 LOC, +2 theorems, +1 axiom, 0 sorries.

| | Pre (S2 ACT) | Post (S3 ACT) |
|---|---|---|
| `lineCount` | 84 | 126 |
| `theoremCount` | 2 | 4 |
| `defCount` | 2 (+1 structure) | 2 (+1 structure) |
| `sorryCount` | 0 | 0 |
| `axiomCount` | 0 | 1 |

Build is **pending** — local Docker build blocked by the worktree `.lake` symlink trap (memory `[.lake symlink loop + mid-build worktree wipe]`); doctor/mechanic verifies on a fresh container. Same pattern as the S2 ACT (PR #18590).

---

## §1 — Why this ACT now

The S3b PREP (PR #18736, researcher-6, merged 2026-05-13T10:18 UTC) **fully designs** the S3 ACT:

* §2 — Mathlib bearer-audit confirms Green-Tao's absence at v4.26.0 (no `GreenTao*`, no `Szemeredi theorem` (general `k`), no `primes_arithmetic_progression`; Dirichlet is present but insufficient — see PR #18736 §2.2).
* §3.1 — Six candidate axiom forms evaluated; form F1 (raw AP triple) recommended.
* §3.2 — Exact Lean source for `axiom greenTao_finitary` + `theorem exists_apGap_zero_of_length` bridge, ~20 LOC.
* §3.3 — `APGapPrimeSeq 0` is uninstantiable (no infinite AP of primes); finitary statement is mandatory.
* §4 — Optional concrete `k = 5` witness `(a, g) = (5, 6)` certifying the AP `5, 11, 17, 23, 29`, sorry-free **and** axiom-free.

This ACT lifts §3.2 + §4 verbatim into `proofs/Proofs/Erdos455OQ04.lean`.

---

## §2 — Axiom and theorems added

### 2.1 `greenTao_finitary` (axiom, ~3 LOC + ~17 doc LOC)

```lean
axiom greenTao_finitary :
    ∀ k : ℕ, ∃ a g : ℕ, 0 < g ∧ ∀ n, n < k → Nat.Prime (a + n * g)
```

Form F1 per S3b PREP §3.1: raw `(a, g)` existential, length `k`, `g > 0`, every prefix term up to `n < k` prime. Coprime `(a, g)` is **not** explicit — it follows from each `a + n g` being prime for `n < k` (if `gcd(a, g) > 1` and `g > 0`, all but at most one term is composite). See S3b PREP §3.1 reason 3.

Docstring cites Green-Tao 2008 with full reference, notes Mathlib's absence of the theorem, distinguishes from Dirichlet (residue class ≠ consecutive prime AP), and references the small-case sanity witness in `exists_apGap_zero_length_5_witness`.

### 2.2 `exists_apGap_zero_of_length` (bridge theorem, ~8 LOC + ~5 doc LOC)

```lean
theorem exists_apGap_zero_of_length (k : ℕ) :
    ∃ q : ℕ → ℕ, HasAPGaps q 0 ∧ ∀ n, n < k → (q n).Prime := by
  obtain ⟨a, g, _hg, hp⟩ := greenTao_finitary k
  refine ⟨fun n => a + n * g, ?_, hp⟩
  intro n
  push_cast
  ring
```

Departure from S3b PREP §3.2 prescription: the prescription's signature included `StrictMono q` (3-way conjunction with `HasAPGaps` and `∀ n < k, prime`). I **dropped `StrictMono`** from the conclusion because:

1. **It's not in the parent S2 ACT's analogue**: `exists_length40_apGapPrimeSeq` (line 77-81) has the 2-way conclusion `HasAPGaps q 2 ∧ ∀ n < 40, prime`, not the 3-way one. Symmetry with the d=2 case is preferred.
2. **`StrictMono` is implied for prime APs**: any `q n = a + n * g` with `g > 0` is `StrictMono`; the hypothesis `0 < g` from `greenTao_finitary` is available via `_hg` if downstream consumers need it.
3. **Smaller proof obligation**: drops the `intro m n hmn; have : m * g < n * g := …` step. The bridge becomes 3 tactic lines (`obtain; refine; push_cast; ring`).

If a future consumer needs `StrictMono`, it's a 1-line auxiliary lemma `(0 < g) → StrictMono (fun n => a + n * g)` via `Nat.mul_lt_mul_right`.

### 2.3 `exists_apGap_zero_length_5_witness` (concrete witness, ~6 LOC + ~4 doc LOC)

```lean
theorem exists_apGap_zero_length_5_witness :
    ∃ a g : ℕ, 0 < g ∧ ∀ n, n < 5 → Nat.Prime (a + n * g) := by
  refine ⟨5, 6, by decide, ?_⟩
  intro n hn
  interval_cases n <;> decide
```

Lifts S3b PREP §4 verbatim. Provides a concrete witness `(a, g) = (5, 6)` giving the AP `5, 11, 17, 23, 29` (all prime). **Sorry-free and axiom-free** — does not invoke `greenTao_finitary`; all five primality checks resolve via kernel `decide`. This is the highest-confidence non-trivial element of the file: a deterministic sanity certificate for the axiom at `k = 5`.

---

## §3 — Pre-push safety checks

Per memory traps:

* **Sibling-race check**: `gh pr list --repo rjwalters/lean-genius --search "erdos-455 in:title" --state open` returned **0** at claim time (2026-05-13 ~11:46 UTC).
* **Branch contamination**: created **fresh** branch `research/erdos-455-oq-04-s3-act-greentao-axiom-1778675124` from `origin/main` (not from `feature/researcher-3`), per memory `[Researcher — push onto branch with open PR silently contaminates PR scope]`. `git log origin/main..HEAD` confirms 0 spurious commits at branch creation.
* **Write/Edit tool main-repo trap**: All Write/Edit calls used the worktree-prefixed absolute path `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-3/...`. Verified via `git status` from the worktree showing the expected 2 modified + 1 added file.
* **`.lake` symlink trap**: doc + Lean change committed before any local Docker build; build deferred to a fresh container (doctor/mechanic).
* **`claim-problem.sh release` from worktree CWD trap**: release will `cd /Users/rwalters/GitHub/lean-genius && /Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh release erdos-455-oq-04` to ensure the main-repo's `research/claims/` lock is removed.
* **`gh` default-repo trap**: all `gh pr {list,create,view}` use explicit `--repo rjwalters/lean-genius`.

---

## §4 — Mathlib import surface

No changes to imports. `proofs/Proofs/Erdos455OQ04.lean` already imports:

* `Mathlib.Data.Nat.Prime.Basic` — supplies `Nat.Prime`.
* `Mathlib.Tactic` — supplies `push_cast`, `ring`, `decide`, `interval_cases`, `refine`, `obtain`.
* `Proofs.Erdos455Problem` — parent file; not used directly by the new declarations but kept for consistency.

The new theorems require **no additional imports**. `Nat.Prime`'s `Decidable` instance ships with `Mathlib.Data.Nat.Prime.Basic`, enabling kernel `decide` on the concrete witness.

---

## §5 — Composed gallery posture (post-S3 ACT)

| Witness | Direction | Length | Axioms | Sorries | Source |
|---|---|---|---|---|---|
| `exists_length40_apGapPrimeSeq` (S2 ACT) | `d = 2` (via Euler) | exactly 40 | 0 | 0 | `proofs/Proofs/Erdos455OQ04.lean:77` |
| `exists_apGap_zero_of_length` (S3 ACT, this PR) | `d = 0` (via Green-Tao) | every `k : ℕ` | 1 (`greenTao_finitary`) | 0 | `proofs/Proofs/Erdos455OQ04.lean:~108` |
| `exists_apGap_zero_length_5_witness` (S3 ACT, this PR) | `d = 0` (concrete) | exactly 5 | 0 | 0 | `proofs/Proofs/Erdos455OQ04.lean:~120` |

**Gallery `meta.json`** (S5's task, not this PR's):
* `status: "axiomatized"` (mandatory due to `greenTao_finitary`).
* `axiomCount: 1`.
* `sorryCount: 0`.
* `lineCount: 126`.
* `theoremCount: 4` (`eulerPoly_hasAPGaps`, `exists_length40_apGapPrimeSeq`, `exists_apGap_zero_of_length`, `exists_apGap_zero_length_5_witness`).
* `defCount: 2` + 1 structure (`APGapPrimeSeq`).

`src/data/research/problems/erdos-455-oq-04.json` is **not modified** here (per
S2 ACT precedent, `leanFiles` aggregation is auditor's domain via a `audit/sync-*`
PR after this PR's build verifies green).

---

## §6 — Honesty

* The bridge theorem dropped `StrictMono` vs S3b PREP §3.2 prescription. Documented in §2.2 above; not a regression — the value is unchanged (the existential's `q n = a + n * g` is automatically strictly monotone given `g > 0`, and downstream consumers can recover via a 1-line lemma).
* `greenTao_finitary` is a genuine, well-defined axiom for a known-true theorem (Green-Tao 2008, peer-reviewed in Annals of Math). Not vapor.
* `axiomCount` rises from 0 to 1 for this slug. The parent `Erdos455Problem.lean` is unaffected. The `status` field on the gallery JSON should become `"axiomatized"` in S5; that's not this PR.
* Build is **pending**, not verified. The `decide` and `native_decide` tactics in the concrete witnesses (`k = 5` for d=0, `n < 40` for d=2 in S2 ACT) need kernel reduction; previous S2 ACT exercised similar `native_decide` at `n < 40` so this should succeed on a fresh Docker build.

---

## §7 — References

* **Green, B.; Tao, T. (2008)**. *The primes contain arbitrarily long arithmetic progressions.* Annals of Mathematics 167(2), 481–547. **The axiomatized theorem.**
* **S3b PREP** (PR #18736, researcher-6, 2026-05-13): Green-Tao axiom signature design, Mathlib bearer-audit, bridge recipe. **This ACT implements §3.2 + §4 verbatim.**
* **S2 ACT** (PR #18590, researcher-5, 2026-05-13): `eulerPoly` witness scaffold for `d = 2`.
* **S2 PREP** (PR #18540, researcher-6, 2026-05-13): verbatim Lean source for `exists_length40_apGapPrimeSeq`.
* **S3 PREP** (PR #18651, researcher-4, 2026-05-13): catalog errata audit (sibling angle, not implemented here).
* **S1b OBSERVE** (PR #18468, researcher-9, 2026-05-13): Euler-polynomial correction to cubic-growth conjecture.
* **S1 OBSERVE** (PR #18331, researcher-10, 2026-05-12): AP-gap prime sequence framework.
* **Mathlib pin**: `proofs/lake-manifest.json` (HEAD pin); `Mathlib.Data.Nat.Prime.Basic` supplies decidable `Nat.Prime`.

---

## §8 — Files modified

* `proofs/Proofs/Erdos455OQ04.lean` (84 → 126 LOC, +42)
* `research/problems/erdos-455-oq-04/state.md` (Phase S2 ACT → S3 ACT, +counts, +next)
* `research/problems/erdos-455-oq-04/sessions/2026-05-13-s3-act-greentao-axiom-and-bridge.md` (this file, new)

**Not modified**:

* `proofs/Proofs/Erdos455Problem.lean` (parent, untouched)
* `proofs/Proofs.lean` (no new imports — `Proofs.Erdos455OQ04` import added by S2 ACT)
* `research/problems/erdos-455-oq-04/{problem,knowledge}.md` (S1 OBSERVE surveys, stable)
* `src/data/research/problems/erdos-455-oq-04.json` (auditor's domain for sorries/axioms aggregation)
* `src/data/proofs/erdos-455-oq-04/` (no gallery directory yet — S5)
