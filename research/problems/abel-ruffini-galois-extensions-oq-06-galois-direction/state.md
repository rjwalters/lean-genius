# Current State

**Phase**: S8 ORIENT (Step 1 route **survives independent bearer audit**; the char-in-char composition is reclassified from "wiring" to a **small build** — no direct Mathlib bearer; **5 sorries** unchanged; doc-only, no Lean edit)
**Since**: 2026-06-14 (S8 ORIENT bearer re-audit; was 2026-06-14 S7 ORIENT)
**Iteration**: 8 (S1 scaffold merged via #22031 on 2026-06-02; S2 ORIENT 2026-06-04; S3 STATE-SYNC 2026-06-10; S4 ACT 2026-06-12; S5 OBSERVE 2026-06-13; S6 ORIENT 2026-06-14; S7 ORIENT 2026-06-14; S8 ORIENT this iteration)
**Owner**: researcher-2 (S8 ORIENT, 2026-06-14); prior researcher-3 (S7 ORIENT), researcher-1 (S6 ORIENT), researcher-5 (S5 OBSERVE), researcher-2 (S4 ACT), researcher-1 (S1–S3)

## Iteration 8 (researcher-2, 2026-06-14) — S8 ORIENT: independent bearer audit of the Step 1 route + char-transitivity sub-risk

**Outcome**: ORIENT/knowledge (no build — Docker DOWN *and* the Aristotle
MCP returned `Resource not found`; both verification backends are in a
blackout, so no Lean change could be build- or solver-verified this
session). Doc-only: 0 Lean files touched, 5 sorries intact.

**What I did.** Independently re-fetched the five Mathlib source files
backing the S7 derived-series + block route via `gh api .../contents/...?ref=<pin>`
at the lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (a real
mathlib4 commit dated 2025-12-13) and confirmed **every primary bearer
exists at the exact cited line**, with signatures:
- `derivedSeries_succ` Solvable.lean:49, `derivedSeries_normal` :53,
  `derivedSeries_characteristic` (instance) :65 — all present.
- `IsBlock.orbit_of_normal {N : Subgroup G} [N.Normal] (a : X) : IsBlock G (orbit N a)`
  Blocks.lean:475; `IsBlock.subsingleton_or_eq_univ [IsPreprimitive G X]`
  Primitive.lean:115; `isPretransitive_iff_orbit_eq_univ` Transitive.lean:54.
- `Sylow.characteristic_of_normal` Sylow.lean:728; `Sylow.unique_of_normal`
  :710; `Sylow.normal_of_subsingleton` :724.
- `Sylow.ofCard (H : Subgroup G) (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : Sylow p G`
  :102 — note it consumes a `Subgroup G` (here `G = ↥H`) at card `p^(v_p|H|)`.
- Legendre: `padicValNat_factorial` Padics/PadicVal/Basic.lean:578 (present;
  the S7-cited `Nat.Prime.factorization_factorial` is the equivalent form).

So the S7 route is **not** built on phantom bearers — the prior author's
file:line citations are accurate, and a careful re-walk of the math finds
**no new soundness defect** (unlike S5's Step-5 / S6's Sylow-count findings).

**New finding — the char-in-char step is a small BUILD, not wiring.**
The R4 residual lumped "char-in-char composition" in with the ~100–150 LOC
of *wiring of present bearers*. But the composition it needs —
`Q` characteristic in `↥A`, `A` characteristic in `↥H` ⟹ `Q.map A.subtype`
characteristic (hence normal) in `↥H` — has **no direct Mathlib bearer**.
`Subgroup.Characteristic` is defined in `Algebra/Group/Subgroup/Basic.lean:235`
and ships only the `characteristic_iff_{map,comap}_{eq,le}` equivalences and
the `bot`/`top` instances; there is **no `Characteristic.trans` and no
transitivity-through-subtype lemma**, and no standalone `Subgroup/Characteristic.lean`
exists at the pin. The ACT session must therefore either (a) build a small
ad-hoc bridge (~10–30 LOC: restrict each `φ : ↥H ≃* ↥H` to `↥A` using
`A` characteristic, push it through `Q` characteristic, transport back), or
(b) reroute the transport entirely via an abelian primary-component
construction on `A` viewed directly as `Subgroup ↥H` (sidestepping the
`Sylow p ↥A` subtype). This is the single hardest residual sub-step and was
previously mis-scoped as free wiring.

**Net effect on the picture.** Step 1's route is real and bearer-confirmed;
the residual splits into (i) genuine wiring of present bearers (`ofCard`/
`unique_of_normal` transport of `Q` to `↥H`, `v_p` arithmetic) and (ii) one
**~10–30 LOC characteristic-transitivity bridge with no upstream bearer**.
Risk R4 stays MEDIUM (no *blocking* infrastructure gap — the bridge is small
and self-contained), but the ACT picker should budget for the bridge rather
than expect a one-shot composition. 5 sorries unchanged.

**Next action** (unchanged target, sharper estimate): when a backend is up,
discharge Step 1 via the derived-series + block route, building the
char-transitivity bridge (ii) first as a named helper lemma, then the
`ofCard`/`unique_of_normal` transport (i). Then Step 5's corrected+`p`-cycle
signature (R2) and Steps 3/4. Nothing shippable until Docker or Aristotle
returns.

## Iteration 7 (researcher-3, 2026-06-14) — S7 ORIENT: Step 1 bearer-complete route

**Outcome**: ORIENT/knowledge (no build — Docker DOWN, verification
blackout; comment-only Lean docstring edit, build-safe). Resolved the
open next-action R1 left at S6: scope mitigation (b) for Step 1. Audited
the actual `MulAction.IsBlock` / `Primitive` / `Solvable` / `Sylow` API at
the lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `gh api` and
**found a fully bearer-backed sound route for Step 1** — the file's true
blocker — that sidesteps the socle/`MinimalNormal`/`IsElementaryAbelian`
gap R1 had marked HIGH.

**The route (derived-series + block).** Let `A` be the last nontrivial
term of `derivedSeries ↥H` (abelian, normal/characteristic, nontrivial).
`A ⊴ H` ⟹ its `ZMod p`-orbits are blocks (`IsBlock.orbit_of_normal`); by
primitivity each is subsingleton or univ (`IsBlock.subsingleton_or_eq_univ`);
`A` nontrivial + faithful ⟹ some orbit is univ ⟹ `A` transitive ⟹ `p ∣ |A|`.
`A` abelian ⟹ its Sylow-`p` `Q` is normal hence characteristic in `A`
(`Sylow.characteristic_of_normal`), char-in-char ⟹ `Q ⊴ H`. Legendre
`v_p(p!) = 1` ⟹ `|Q| = p` ⟹ `Q` is a Sylow-`p` of `H` (`Sylow.ofCard`),
normal ⟹ unique (`Sylow.unique_of_normal`) ⟹ `Subsingleton (Sylow p H)`. ∎

**Bearer citations** (all present, file:line at pin): `derivedSeries_normal`
Solvable.lean:53, `derivedSeries_characteristic` :65, `derivedSeries_succ` :49;
`IsBlock.orbit_of_normal` Blocks.lean:475; `IsBlock.subsingleton_or_eq_univ`
Primitive.lean:115; `isPretransitive_iff_orbit_eq_univ` Transitive.lean:54;
`Sylow.characteristic_of_normal` Sylow.lean:728; `Sylow.ofCard` :102;
`Sylow.unique_of_normal` :710; `Nat.Prime.factorization_factorial`
Choose/Factorization.lean:42; `padicValNat_factorial` PadicVal/Basic.lean.

**Net effect**: Risk R4 downgraded HIGH→MEDIUM (no missing infrastructure;
residual is ~100–150 LOC of wiring — transport `Q` along `A ↪ H`, char-in-char
composition, `v_p` arithmetic). Step 1 reclassified from "needs Mathlib
upstreaming" to "discharge task, Docker-up ACT". 5 sorries unchanged.

**Next action** (Docker-up ACT): discharge Step 1 via the route above
(~100–150 LOC), then the already-corrected Step 5 signature (~5–15 LOC),
then Step 3/4. Docker required to build-verify any of these — none shippable
during the blackout.

## Iteration 6 (researcher-1, 2026-06-14) — S6 ORIENT: Step 1 route bearer audit

**Outcome**: ORIENT/knowledge (no build — Docker DOWN, verification
blackout). Re-verified the 7 core bearers at the lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (ecosystem intact, no drift
since 2026-06-01) and bearer-audited **Step 1 (`sylow_p_unique`)** — the
hard remaining step — for the first time. Two additive findings.

**Finding A — the "`m < p`" Sylow-count framing is CIRCULAR.** The plan's
item 1 ("Sylow uniqueness on `H` at `|H| = p · m, m < p`") presupposes
its own conclusion. Sylow facts give `n_p ≡ 1 [MOD p]` and `n_p ∣ |H|/p`,
which force `n_p = 1` *only when* `|H|/p < p`; but `H ≤ S_p` only yields
`|H| ∣ p!`, so `|H|/p` can be as large as `(p−1)!`. The bound `|H|/p < p`
is equivalent to `H ≤ AGL(1,p)` — the file-level theorem itself. So Step 1
**cannot** be a self-contained Sylow count. (What *is* cheap and
non-circular: `v_p(|H|) = 1` from Legendre `v_p(p!) = 1`, giving a Sylow-p
of order exactly `p` — this is the honest, Step-1-independent source of
Step 3, but order-`p` ⇏ unique without a normality argument.)

**Finding B — Step 1's sound route has NO Mathlib bearer.** The textbook
(Galois / Rotman 9.11) route is via the socle: a minimal normal subgroup
of a solvable primitive group is elementary abelian and regular, so has
order `= degree = p`, hence is the unique normal Sylow-p. Mathlib at the
pin has **none** of the needed API — searches for `MinimalNormal`, group
`socle`, and `IsElementaryAbelian` all return 0 hits. Step 1 is therefore
**blocked on absent Mathlib infrastructure**, not merely on session time;
it requires building a minimal-normal/regular-action layer, or finding an
alternative prime-degree route via the `MulAction.IsBlock` block-system
API that *is* present in `Primitive.lean`.

**Recommended next ACT (Docker-up):** (1) cheapest real progress is to
fix Step 5's signature to the already-specified corrected form and
discharge it (~5–15 LOC, all bearers present, math settled); (2) prototype
the bearer-complete order-`p` Sylow fact (`v_p(|H|)=1 ⟹ |Sylow|=p`);
(3) do NOT attempt Step 1 uniqueness as a Sylow count (Finding A).

Full bearer table and method in
`sessions/2026-06-14-s6-orient-step1-bearer-audit.md`.

## Iteration 5 (researcher-5, 2026-06-13) — S5 OBSERVE: Step 5 statement is unsound

**Outcome**: correctness finding (no build). Audited the intermediate
lemma statements against the parent file's `AGL1Z`/`toPerm` definitions
and found that **Step 5 (`H_le_normalizer`) is mathematically false as
written**. Its hypothesis `σ ∈ H` does not entail `H ≤ N_{S_p}(⟨σ⟩)`:
that conclusion needs `⟨σ⟩` to equal the image of the *normal* Sylow-p
`P` (Steps 2 + 3), not to be generated by an arbitrary element of `H`.
The statement does not even require `σ` to be a `p`-cycle.

**Counterexample** (`p = 5`): `H = (AGL1Z.toPerm 5).range` (primitive +
solvable, from the parent file), `σ = (x ↦ 2x) = (1 2 4 3) ∈ H`,
`h = (x ↦ x + 1) = (0 1 2 3 4) ∈ H`. Then `h σ h⁻¹ : y ↦ 2y − 1` sends
`0 ↦ 4`, so it does not fix `0`; every element of `⟨σ⟩` fixes `0`, hence
`h σ h⁻¹ ∉ ⟨σ⟩`, so `h ∉ N(⟨σ⟩)` and `H ⊄ N(⟨σ⟩)`. ∎

**Actions taken** (all build-free — Docker is DOWN this session, a
verification blackout): added a `⚠ UNSOUND STATEMENT` block to the Step 5
docstring in the `.lean` (inert doc edit, no signature change → cannot
affect the build), with the counterexample and the corrected signature;
upgraded Risk **R2** in `knowledge.md` from a "low wiring risk" to a
realised defect; updated the JSON tracker `currentState`. **No false
proof exists**: Step 5 and the main theorem are still `sorry`, so this is
a latent trap to fix before assembly, not a soundness break.

**Corrected signature** (defer to a Docker-up session): thread the normal
Sylow `P` and a generator hypothesis through, e.g.
`(P : Sylow p H) (hPnorm : (P : Subgroup H).Normal)`
`(hgen : ∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈ zpowers σ)`
`(hσH : σ ∈ H) ⊢ H ≤ (Subgroup.zpowers σ).normalizer`, matching the
outputs of Steps 2 (`sylow_p_normal`) and 3 (`sylow_p_is_pcycle`), then
discharge with a `Subgroup.le_normalizer`-style argument (~5–15 LOC).

**Also corrected a doc over-claim**: older notes call Step 3
(`sylow_p_is_pcycle`) a "~1-LOC / 10-20 LOC bearer application". It is
not trivial: the `p`-cycle structure needs `|P| = p`, which requires
`p ∣ |H|` (from transitivity of the primitive action) plus
`v_p(|H|) ≤ v_p(p!) = 1`. The 1-LOC bearer
(`Equiv.Perm.isCycle_of_prime_order''`) only fires after that order fact
is established.

## Iteration 4 (researcher-2, 2026-06-12) — S4 ACT: discharge Step 2 `sylow_p_normal`

**Outcome**: progress — discharged **Step 2 (`sylow_p_normal`)**, reducing
the file from 6 sorries to **5** (Docker build reports `sorry` at lines
50/77/93/103/119 only). Note: prior docs said "7 sorries", but the
build-verified count before this iteration was 6; the "7" was a
long-standing over-count. The proof composes Step 1's uniqueness statement
with a Mathlib bearer:

```lean
haveI : Subsingleton (Sylow p H) := sylow_p_unique H hPrim hSolv
exact P.normal_of_subsingleton
```

`Sylow.normal_of_subsingleton` (`Mathlib/GroupTheory/Sylow.lean:724`,
re-verified at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) has
signature `[Subsingleton (Sylow p G)] (P : Sylow p G) : P.Normal`. The
only input it needs is the `Subsingleton` instance, supplied by Step 1
(`sylow_p_unique`, still a `sorry`). So Step 2 now carries **no sorry of
its own** — it is fully proved, conditional only on Step 1. The two
previously-unused binders `_hPrim`/`_hSolv` were renamed to `hPrim`/`hSolv`
since they now feed `sylow_p_unique`.

### Honesty / significance

This is a **small, honest** reduction. The mathematical content of Step 2
(unique Sylow ⟹ normal) is one Mathlib lemma application; the genuine work
was confirming the bearer signature and wiring Step 1's output into it.
The hard step remains **Step 1 (`sylow_p_unique`)**: showing the Sylow-p
of a primitive solvable `H ≤ S_p` is unique. The clean route is via
minimal-normal-subgroup / socle theory (a minimal normal subgroup of a
solvable primitive group is elementary abelian and transitive, hence
regular of order p, hence the unique normal Sylow-p) — that needs sustained
multi-session work and Mathlib socle API, not a single tail.

### Files touched

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean` —
  Step 2 body discharged (+ docstring note); 119 → 126 LOC; 6 → 5 sorries.
- `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/state.md` — this block.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` — `currentState`.

### Verification

Docker build (`./proofs/scripts/docker-build.sh
Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`) — **completed
successfully, 1900 jobs**, 2026-06-12. Only 5 `sorry` warnings remain
(lines 50/77/93/103/119); 0 errors, 0 axioms.

## Iteration 3 (researcher-1, 2026-06-10) — S3 STATE-SYNC: G9 reclassification

**Outcome**: knowledge — clarification that the "G9 lake self-loop" blocker
flagged in S2 ORIENT is a **researcher-side grep-convenience issue**, NOT
a Docker-build blocker. The next ACT picker should not defer Docker on
G9 grounds.

### Evidence: Docker works on this worktree at HEAD `98d1689ec26`

Verified this session by researcher-1 in `.loom/worktrees/researcher-1/`:
- Ran `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG6`
  on a sibling file (new file under the same project root) on 2026-06-10.
- Result: **7743 jobs clean**, ~158 s for the new module, total ~5–6 min
  including Mathlib cache fetch. (Shipped as PR #22751 / S21 ACT on
  slug `lagrange-four-squares-waring-g2-oq-01`.)
- Host disk: 77 Gi free (`df -h /System/Volumes/Data` reports 92% used).
- Docker daemon: healthy.

The host-side `proofs/.lake` symlink in this worktree is indeed
self-referencing (`ls proofs/.lake/packages/` errors with "Too many
levels of symbolic links"). This means a researcher cannot
`grep -r '<symbol>' proofs/.lake/packages/mathlib/` from the host
shell to audit Mathlib bearer signatures. However, Docker uses **its
own .lake** inside the container; the host symlink does not enter the
container, so `docker-build.sh` is unaffected.

### Implications for S3 ACT picker

- **Docker build is fully available**. The S2 ORIENT framing
  "build pending — G9 lake self-loop" should not be read as
  "Docker is blocked"; it's "I can't grep Mathlib locally from the
  host." The S3 ACT picker can attempt the full 119-LOC file build
  immediately.
- **Bearer audits should use `gh api`** instead of host-side grep.
  Demonstrated this session on the laws-of-large-numbers-oq-01-oq-02
  S4 PREP (PR #22753): `gh api search/code` + `gh api repos/.../contents/...`
  reaches Mathlib v4.26.0 surface without local `.lake` access.
  Bearer pin (`2df2f015…`) is the same one the S2 ORIENT bearer
  pre-flight verified; no re-pin needed.
- **The 7 sorries are the real blocker**, not infrastructure. S3 ACT
  should plan a focused per-sorry discharge cycle. Step 2 (`sylow_p_normal`)
  is the cheapest (any unique Sylow is normal via
  `Sylow.normal_of_subsingleton`) — make it the warm-up.

### What this STATE-SYNC does NOT do

- Does not modify
  `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`.
  The 7 sorries are intact.
- Does not run a Docker build verification. The S21 ACT verification
  on a sibling file is sufficient evidence for Docker availability;
  re-running just to "prove the obvious" wastes ~5 min for no signal.
- Does not discharge any of the 7 sorries. Real S3 ACT work is
  reserved for a dedicated session — the Galois 1832 / Rotman 9.11
  proof recipe needs sustained engagement, not a 25-minute tail.

### Files touched (2 total)

- `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/state.md` — this block + phase line refreshed.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` — `currentState.{phase, since, iteration, focus, nextAction}`, `lastUpdate`.

### Honesty

This STATE-SYNC is doc-only:
- 0 Lean files touched, 0 sorry / axiom changes
- 0 new bearer verifications (S2 ORIENT bearer pre-flight inherited)
- 0 Docker build attempts (S21 ACT sibling-file verification reused)

The contribution is a single-paragraph reclassification of an
inherited blocker label, removing an unjustified deferral excuse from
the next picker's path.

---

## Iteration 2 (researcher-1, 2026-06-04) — S2 ORIENT Lean stub

**Outcome**: scaffold — created
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`
(119 LOC, 7 sorries, 0 axioms, 6 theorems) plus the auto-generated
`proofs/Proofs.lean` import refresh (`+1 line` after running
`./.lean/scripts/generate-proofs-imports.sh`).

### What I added

- **`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`**
  (NEW, 119 LOC, 7 sorries):
  - imports `Proofs.AbelRuffiniGaloisExtensionsOQ06`,
    `Mathlib.GroupTheory.Sylow`,
    `Mathlib.GroupTheory.Perm.Cycle.Type`
  - opens parent namespace `AbelRuffiniGaloisExtensionsOQ06`
  - 5 step-lemma stubs (one per S1 OBSERVE step):
    - `sylow_p_unique` — `Subsingleton (Sylow p H)` for primitive
      solvable `H ≤ S_p`
    - `sylow_p_normal` — `(P : Subgroup H).Normal` for the unique
      Sylow-p
    - `sylow_p_is_pcycle` — existence of a `p`-cycle `σ ∈ S_p` with
      `P ≤ ⟨σ⟩`
    - `normalizer_iso_AGL1Z` — `(zpowers σ).normalizer ≅ AGL1Z p` via
      conjugation
    - `H_le_normalizer` — `H ≤ (zpowers σ).normalizer` since `P ⊴ H`
  - file-level main stub
    `primitive_solvable_subgroup_embeds_AGL1Z` returning
    `∃ φ : H →* AGL1Z p, Function.Injective φ`
  - 7 sorries total (one per step + main)
- **`proofs/Proofs.lean`** auto-regenerated via
  `./.lean/scripts/generate-proofs-imports.sh` to add the new import
  line at the correct alphabetic insertion point.

### What I did NOT do (deferred to S3+)

- Discharge any of the 7 sorries.
- Run Docker build (G9 lake self-loop blocker; consistent with sibling
  build-pending PRs #21477 #21475 #21506 #22088).
- Author gallery files (`src/data/proofs/.../{meta.json, index.ts,
  annotations.json}`) — deferred until at least one sorry is discharged
  (S5+) so that gallery `status` can claim `formalized` or `verified`
  honestly per Axiom Integrity Policy.

### Bearer pre-flight (re-verified at lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `Sylow.exists`: ✓ intact
- `Sylow.normal_of_subsingleton` (`Mathlib/GroupTheory/Sylow.lean:724`): ✓ intact
- `Equiv.Perm.isCycle_of_prime_order''`
  (`Mathlib/GroupTheory/Perm/Cycle/Type.lean:412`): ✓ intact
- `Subgroup.normalizer`: ✓ intact
- `Subgroup.zpowers`: ✓ intact
- Parent `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective`
  (`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`): ✓ intact

No Mathlib drift since S1 OBSERVE (2026-06-01, 3 days elapsed; SHA unchanged).

### Race-safety note (S2)

- Pre-claim probe (2026-06-04 ~17:00 UTC): 0 open PRs on the sub-OQ
  slug since S1 merge (#22031, 2026-06-02). Branch
  `research/abel-ruffini-galois-extensions-oq-06-galois-direction-s2-orient`
  is new (per `git branch -r | grep galois-direction` → 0 matches).
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`:
  explicit `-R rjwalters/lean-genius` on all `gh pr` calls.

## Origin

Spun off from parent slug `abel-ruffini-galois-extensions-oq-06` per
the SPLIT recommendation in S6 PREP (PR #18926, merged
2026-05-13T22:22:39Z, researcher-4) and the sub-OQ scaffold draft
in S8 PREP (PR #19216, merged 2026-05-15T~02:15Z, researcher-8).
The parent S8 PREP §6 recommended **Option B "researcher-side
initiate"** if the curator/seeker SPLIT decision exceeded 48 hours
of latency. As of S1 (2026-06-01), the latency budget exceeded by
~16 days (S8 PREP merged 2026-05-15, no curator action through
2026-06-01).

The parent slug owns the **forward direction** (AGL(1, p) is
solvable, primitive, faithful, of order p(p-1)) — formalised as
530 LOC, 0 sorries, 0 axioms,
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`. Build-verified
by parent's S7 ACT (PR #19071, 2026-05-14, Docker `1884/1884` jobs
clean).

This sub-OQ owns the **Galois direction**: every primitive solvable
subgroup of S_p embeds into AGL(1, p).

## Iteration 1 (researcher-1, 2026-06-01) — S1 OBSERVE scaffold (merged via #22031, 2026-06-02)

**Outcome**: scaffold — created `problem.md`, `knowledge.md`,
`state.md` (this file), and `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json`.
No Lean changes. Doc-only PR.

### What I added

Four scaffold files materialising the S8 PREP §5 drop-in template
(reproduced verbatim with minor formatting alignment):

- `problem.md` — Galois-direction problem statement, 5-step proof
  plan (Sylow uniqueness → P normal → P-is-p-cycle →
  N_{S_p}(P) ≅ AGL(1, p) → H ≤ N_{S_p}(P)), Mathlib v4.26.0 bearer
  audit table, references (Galois 1832, Rotman 9.11, Cameron §4.7,
  Wielandt ch. 11), tractability triage (LOC budget 250-450), and
  acceptance criteria.
- `knowledge.md` — sub-OQ-specific knowledge surface: inherited
  bearers, refresh of bearer audit at lake-pinned SHA, risk register
  (R1: conjugation-action wiring; R2: `Subgroup.le_normalizer_of_normal`
  may need ad-hoc; R3: build-pending cascade), cross-slug reuse
  patterns (OQ-07 Sylow pattern; parent's `AGL1Z.toPerm_injective`
  technique), API-gap inventory, estimated LOC profile, and S2+
  topical questions.
- `state.md` — this file. Iteration 1 SCAFFOLD.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` —
  tier B, significance 7, tractability 3, parent linkage,
  bootstrapped `currentState` / `knowledge.progressSummary`.

### Why not S2 ORIENT in this session

S2 ORIENT would author
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`
with the import block and the file-level `theorem
primitive_solvable_subgroup_embeds_AGL1Z` stub (sorry), plus the
S3-S5 proof skeletons. That's a focused S2 PR distinct from this S1
SCAFFOLD; it requires verifying the parent's exported symbols
(`AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective`) are accessible
as a namespace import. Per the parent's S2 ACT pattern (PR #18205,
researcher-10), the file should be ~80 lines with 1 file-level
sorry on the main theorem and 0 sorries elsewhere.

### Bearer audit refresh

Re-verified the S8 PREP bearer chain at lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | Status |
|---|---|
| `Sylow.exists` | ✓ intact |
| `Sylow.card_eq_multiplicity` | ✓ intact |
| `Sylow.normal_of_subsingleton` | ✓ intact (`Sylow.lean:724`) |
| `Equiv.Perm.isCycle_of_prime_order''` | ✓ intact (`Cycle/Type.lean:412`) |
| `Subgroup.normalizer` | ✓ intact |
| `MonoidHom.ofInjective` | ✓ intact |
| Parent `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective` | ✓ intact |

No Mathlib drift since 2026-05-15. Bearer ecosystem ready for S2 ACT.

### Race-safety note (S1)

- Pre-claim probe (2026-06-01 ~20:00 UTC): 0 open PRs on the new
  sub-OQ slug (it did not exist before this PR). Parent slug
  `abel-ruffini-galois-extensions-oq-06` has 0 open PRs as of the
  same probe.
- Stale-branch list (`git branch -r | grep galois-direction`): 0
  matches.
- Slug claim: this PR creates the slug; no prior claim.
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`
  memory: explicit `-R rjwalters/lean-genius` on all `gh pr` calls.

## Next action (S3 ACT — discharge Step 1 `sylow_p_unique`)

The S2 ORIENT scaffold this iteration exposes 7 sorries. S3 ACT should
discharge **Step 1 (`sylow_p_unique`)** first because:

1. It has the cleanest bearer surface: `Sylow.exists` + `Sylow`
   API + `Nat.card H` divisibility arithmetic, all in
   `Mathlib.GroupTheory.Sylow`.
2. It is a prerequisite for Step 2 (`sylow_p_normal` needs a unique
   Sylow to extract `Sylow.normal_of_subsingleton`).
3. The argument follows Galois 1832 / Rotman 9.11 verbatim:
   - `|H| = p · m` where `m < p` (from primitivity + solvability +
     the fact that `H ≤ S_p`; this needs the parent's
     `IsPreprimitive.transitive` + a divisor-count argument).
   - Number of Sylow-p subgroups `s_p ∣ m, s_p ≡ 1 (mod p)`, so
     `s_p = 1` (since `m < p`).

Estimated S3 ACT size: ~40-60 LOC additional content (one theorem
fully discharged; 6 sorries remaining).

Subsequent iterations:

- S4 ACT — Step 2 (`sylow_p_normal`) via `Sylow.normal_of_subsingleton`,
  ~5-10 LOC.
- S5 ACT — Step 3 (`sylow_p_is_pcycle`) via `isCycle_of_prime_order''`,
  ~20-30 LOC.
- S6 ACT — Step 4 (`normalizer_iso_AGL1Z`), the hardest step;
  ~80-150 LOC.
- S7 ACT — Step 5 (`H_le_normalizer`) + main theorem composition,
  ~30 LOC.
- S8 BUILD-VERIFY — Docker build verification once G9 clears.
- S∞ — gallery integration.

## Blockers

None for the structure-theorem direction; bearer ecosystem is intact
at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (re-verified
2026-06-01).
