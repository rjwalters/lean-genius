# S21 ACT — discharge Step 3 (`sylow_p_is_pcycle`): fold orphan, fix 2 bugs, Docker-verified GREEN (researcher-11, 2026-06-18)

## Mode
REVISIT — already held the claim on `abel-ruffini-galois-extensions-oq-06-galois-direction`
(RICH). Docker is up this session.

## Prior state (S18–S20)
- Registered file `Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean` carried
  **4 sorries**: Step 1 (`sylow_p_unique`), Step 3 (`sylow_p_is_pcycle`), Step 4
  (`normalizer_iso_AGL1Z`), main (`primitive_solvable_subgroup_embeds_AGL1Z`).
- A turnkey orphan `…GaloisDirectionStep3.lean` carried a complete, 0-sorry proof of
  `sylow_p_is_pcycle` with a verbatim-identical signature (S15 authored, S17 fixed 3 bugs,
  S18 strengthened with the `σ ∈ H` conjunct). It had **never been confirmed GREEN** —
  S17 left 4 `?`-confidence calls awaiting a first build; S19's verify failed only because
  Docker was down; S20 attempted a fold but the build result was never recorded.

## What S21 did
1. **Built the Step3 orphan in isolation** (`docker-build.sh Proofs.…Step3`), zero risk to
   the registered file. It surfaced **2 real elaboration bugs** (exactly the `?`-flagged
   calls):
   - `Proofs/…Step3.lean:80` — `Nat.pow_le_pow_right hp.pos.le hi2`: the resolved overload
     wants `0 < p` (`p > 0`), not `0 ≤ p`. Fix: `Nat.pow_le_pow_right hp.pos hi2`.
   - `Proofs/…Step3.lean:110` — `MulAction.orbit_eq_univ (0 : ZMod p)`: in Mathlib v4.26.0
     (pin `2df2f015`) `orbit_eq_univ` takes the acting group `M` as an **explicit** argument
     (it is preceded by `variable (M)` in `GroupAction/Basic.lean`). Fix:
     `MulAction.orbit_eq_univ H (0 : ZMod p)`.
2. **Folded the corrected proof into the registered file**:
   - Replaced the three targeted `Mathlib.GroupTheory.*` imports with `import Mathlib`
     (the proof needs factorization/Legendre, orbit–stabilizer, `ZMod`/index cardinality,
     and cyclic-group bearers not in the targeted set; full Mathlib also covers the Step-4
     `ConjAct.normal_of_characteristic_of_normal` instance).
   - Added the helper `padicValNat_factorial_self : (p!).factorization p = 1` (Legendre at
     the prime itself), with `omit [Fact p.Prime] in` to silence the unused-section-variable
     linter (the helper takes `hp : p.Prime` explicitly).
   - Replaced the `sylow_p_is_pcycle` `sorry` with the corrected body; rewrote its docstring
     to record the discharge and the Step A/B/C route.
3. **Deleted the now-redundant orphan** `…GaloisDirectionStep3.lean` (the proof now lives in
   the registered file; git history preserves the orphan at #25449).
4. **Rebuilt the registered module** `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`.

## Result
- **Build: GREEN — `Build completed successfully (7745 jobs)`** (folded build), re-confirmed
  on the final committed state (omit + docstring + orphan deletion).
- **Sorry frontier: 4 → 3.** Remaining: Step 1 `sylow_p_unique` (line ~117), Step 4
  `normalizer_iso_AGL1Z` (~262), main (~422). **Steps 2, 3, 5 are now proved.**
- 0 axioms (the folded proof is `sorry`-free and uses no `native_decide`/`axiom`).

## Next steps
- **Step 1 `sylow_p_unique`** is the next (and hardest) target, ~70–110 LOC. The Step1 orphan
  (`…GaloisDirectionStep1.lean`) already proves Lemma A (a nontrivial finite solvable group
  has a nontrivial abelian characteristic subgroup = last nontrivial derived-series term) and
  scopes the full route. Remaining obligations there: Lemma B (`normal ⇒ transitive` via the
  block API), Lemma C (`transitive ⇒ p ∣ |A|` via orbit–stabilizer — directly mirrors this
  session's Step A), and the Sylow-transport assembly (`ConjAct.normal_of_characteristic_of_normal`
  + `Sylow.ofCard` + Legendre + `Sylow.unique_of_normal`).
- **Step 4 `normalizer_iso_AGL1Z`** (~80–150 LOC, numerically certified by S11), then the
  main assembly (pure glue once Steps 1/4 land — the main-assembly orphan drafts it).

## Note
- Stale PR #25110 ("Step-3 orphan — … not yet green") is superseded by this fold; it can be
  closed.
- Docker builds work from this worktree despite the `proofs/.lake` self-symlink (the
  `lean-mathlib-cache` volume mount shadows it); ~14 min/build under heavy IO contention from
  concurrent agents.
