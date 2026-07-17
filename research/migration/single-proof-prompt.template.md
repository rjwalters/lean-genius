# MIGRATION — SINGLE-PROOF FIX (Lean/Mathlib <OLD> → <NEW>)

You fix ONE Lean proof file: bring it from RESIDUAL (fails on <NEW>) to GREEN (compiles), verify in
Docker, flip its one ledger row, push a per-proof branch. You are one of N parallel single-proof
agents; you touch ONLY your assigned file. Do NOT merge, do NOT open a PR (the orchestrator collects).

## FRAMING
The file was GREEN on the OLD toolchain — the theorem is TRUE and a proof existed; the bump only changed
how it's SPELLED. So it's EXPENSIVE (many API-drift sites), never "impossible." Grind it. Exceptions:
(1) unsound-original files whose old green exploited a since-tightened tactic (a false theorem an old
`ring`/`simp`/`decide` accepted) — FIX the statement+proof to the genuinely-true form (add the missing
hypothesis / fix the edge case; NEVER weaken to vacuous, NEVER sorry/axiomatize); note it as a
SOUNDNESS-REPAIR in your report. (2) native_decide/noncomputable cases where the cheap compute-proof is
gone and a real argument is too deep for one session — if you can't finish, report FAILED with a
diagnosis (don't sorry). (3) if the file OOMs (EXIT=137) even after you simplify, report FAILED:OOM.

## YOUR ASSIGNMENT (substituted per dispatch)
- FILE:      {{FILE}}            (edit ONLY Proofs/{{FILE}}.lean)
- WORKTREE:  {{WORKTREE}}
- CACHE_VOL: {{CACHE_VOL}}
- CPUSET:    {{CPUSET}}
- BRANCH:    mig/{{FILE}}

## SETUP
cd {{WORKTREE}} && git fetch origin {{FEATURE_BRANCH}} -q && \
  git checkout -q -B mig/{{FILE}} origin/{{FEATURE_BRANCH}}

## VERIFY RECIPE (NEVER run bare `lake build` on the host — OOM risk)
docker run --rm --memory 6g --cpuset-cpus {{CPUSET}} \
  -v "{{WORKTREE}}:/workspace" \
  -v {{PKGS_VOL}}:/workspace/proofs/.lake/packages \
  -v {{CACHE_VOL}}:/workspace/proofs/.lake/build \
  -w /workspace/proofs {{IMAGE}} \
  bash -c 'lake env lean Proofs/{{FILE}}.lean 2>&1 | tail -50; echo EXIT=${PIPESTATUS[0]}'
EXIT=0 ⇒ GREEN. Iterate until green. Only ONE container at a time (you own {{CPUSET}}).
IMPORTANT: grep the FULL output for "error", don't just `tail` — parallel elaboration output isn't
position-sorted and early errors get consumed by a maxErrors cap, hiding later ones.

## SEAM CHEATSHEET (fill fresh each migration — drift is version-specific; keep the CLASSES below)
Behavior classes that RECUR across bumps (start here even before you know the new renames):
- **Big-operator greedy binding**: `∑ x ∈ s, f x - g` / `∫ .. , f - g` parse the trailing `- …`/`≤`/`=`
  INTO the binder → parenthesize the sum/integral.
- **`subst h` (h : a = b) eliminates the OTHER side than you expect** and cascades name-elimination through
  later `rcases … | rfl` splits → prefer named equalities + `.trans`, or `rw`, over `subst`/`rintro rfl`.
- **`set x := e with hx` is opaque** to omega/simp/mod_cast → `rw [hx]`/`dsimp only` first; and non-generalized
  index-dependent hyps now sort BEFORE the generalized var in `induction … generalizing` IHs.
- **Beta-unreduced lambda goals** (`(· * k) a`, `(fun i => …) ⟨0,_⟩`) break `omega`/`rw` atom-matching →
  `dsimp only at h` before the tactic; and `fin_cases`/anonymous-constructor terms may be non-canonical.
- **Instance/typeclass tightening**: `haveI`→`letI` for defeq-through-unfold; implicit type args left as
  stuck metavariables need explicit `(𝕜 := …)`/`(V := …)` pinning; `def X := <TypeSynonym>` no longer
  unfolds for instance search → make it `abbrev`; scoped notations (`ℝ≥0∞`, Finset `+`, `𝓝`) need
  `open scoped …`; structure fields that became one-field classes (Std.Symm/Std.Irrefl) need `constructor`/`⟨⟩`.
- **`native_decide`/`decide` on now-noncomputable paths** (orderOf on Subgroup, Fintype of an infinite-ambient
  subtype) → bridge to a computable predicate, or `norm_num` for concrete facts.
- **Scoped-name auto-binding is a SILENT-WRONG-STATEMENT trap**: a scoped constant (`ω`, `Real.pi` when
  protected) used without its `open` silently auto-binds as a fresh ∀-implicit instead of erroring — audit.
- Forward-referenced local lemmas/axioms must be REORDERED above first use (hard error now).
- **CASCADE**: a lone "object file …olean does not exist" means a GREEN parent isn't in cache — build the
  parent first inside the container (`lake build Proofs.<Parent>`, NOT `lake env lean`) to unmask real drift.

## FINISH (per proof)
1. When EXIT=0: flip your row in proofs/batch2/verify-results.tsv from
   `{{FILE}}\tRESIDUAL\t<class>` to `{{FILE}}\tGREEN\t` (tab-separated, GREEN's 3rd col empty).
   (col1 is the BARE module name — match it exactly.)
2. `git add proofs/Proofs/{{FILE}}.lean proofs/batch2/verify-results.tsv` (nothing else) →
   commit `migrate: {{FILE}} RESIDUAL->GREEN` → `git push -u origin mig/{{FILE}}`.
3. Report EXACTLY: `GREEN {{FILE}} | branch mig/{{FILE}} | <one-line fix> | seams: <new seams> |
   repair: <soundness-repair note if any>`. If you could not finish: `FAILED {{FILE}} | <reason/diagnosis>
   | <error count + top blocker>` and push nothing.

## native_decide RULE (axiom integrity)
Prefer a REAL proof. If the original used `decide` and the new toolchain no longer reduces it, try a real
argument first; only fall back to `native_decide` if necessary. If you introduce `native_decide` where the
original did NOT have it, you MUST report `native_decide-introduced: <lemmas>` — it adds the
`Lean.ofReduceBool` axiom and flags the gallery meta for re-audit. Preserve pre-existing sorries/axioms
(formalized/axiomatized entries) — just make the file COMPILE.

## HARD RULES
- Never `lake build` on the host; only the container recipe. Edit ONLY Proofs/{{FILE}}.lean. Flip ONLY
  your ledger row. Never touch STATUS.md. Never sorry/axiomatize/weaken. Push only if GREEN.
