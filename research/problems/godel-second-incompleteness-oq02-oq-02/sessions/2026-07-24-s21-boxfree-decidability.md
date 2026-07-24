# S21 — Decidability of the box-free fragment of GL (researcher-2, 2026-07-24)

## Outcome: BUILT (new file, 0 sorries, 0 axioms beyond propext/Quot.sound)

New file `proofs/Proofs/GodelSecondIncompletenessOQ02Decidable.lean` (~200 LOC,
Mathlib-free, matching chain style). Implements S20's recorded "next tractable
S21 option (c)": decidability of box-free GL via S19's `boxfree_characterization`
+ finite valuation search.

## Results

- `eval_congr` — `eval` depends only on `atoms φ` (no box-freeness needed:
  boxes evaluate to `true` outright under the boolean semantics).
- `allSubsets` / `filterTrue` / `valOf` — hand-rolled (core-only) enumeration of
  the `2^k` valuations on the atom list, with coverage
  (`filterTrue_mem_allSubsets`) and agreement (`valOf_filterTrue`) lemmas.
- `tautCheck : GLFormula → Bool` — the finite truth-table check.
- **`tautCheck_correct`**: box-free `φ` → (`GL_proves φ ↔ tautCheck φ = true`).
- **`decidableGLProvesBoxFree`**: `Decidable (GL_proves φ)` for box-free `φ` —
  provability in the box-free fragment of GL is decidable, by kernel
  computation (`decide`; NO `native_decide`, so no `Lean.ofReduceBool`).
- Demos: `GL_proves_peirce` (Peirce's law by pure computation) and
  `GL_not_proves_assertion` (`GL ⊬ (p → q) → p` — computational
  non-derivability, complementing S19's hand-built `GL_proves_no_atom`).

`#print axioms tautCheck_correct` = `[propext, Quot.sound]`.

## Verification

- Host: `lake env lean` exit 0 on pinned v4.31 toolchain.
- Docker: `./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02Decidable`.

## Tracker-sync deferral (deliberate)

S20 PR #43350 (open at session time) rewrites `state.md`/`knowledge.md`/the
research JSON for this problem. To keep this PR conflict-free it adds ONLY the
Lean file and this session note. Next session (or a follow-up) should fold S21
into `state.md`/`knowledge.md` after #43350 merges.

## Next candidates (S22+)

- Full GL decidability via finite model property (Segerberg filtration over the
  S20 `Kripke.lean` semantics) — multi-session.
- Arithmetic Htaut/Hk/Hlob still wait on the Σ₁ Provable rebuild (S6 PREP #18497).

## Gotchas for future sessions

- `List.mem_map_of_mem` arity drifts across toolchains — use
  `List.mem_map.mpr ⟨_, h, rfl⟩`.
- `BoxFree` is a Prop-valued match (not decidable as-is); discharge concrete
  instances with `by simp [BoxFree]`.
- The demo `decide`s reduce 16 valuations in the kernel instantly; keep demo
  formulas small (atoms list has multiplicity, so `allSubsets` is `2^(#occurrences)`).
