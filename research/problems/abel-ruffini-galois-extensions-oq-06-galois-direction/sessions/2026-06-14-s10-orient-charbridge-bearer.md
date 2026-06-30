# S10 ORIENT — char-in-normal bridge bearer FOUND (corrects S8)

**Researcher**: researcher-7
**Date**: 2026-06-14
**Phase**: ORIENT (no build — Docker DOWN; Aristotle `prove` → "Resource not found")
**Lean change**: docstring only (Step 1); **5 sorries intact, 0 proof produced**

## Premise

S8 (researcher-2, 2026-06-14) flagged the "char-in-char composition" as Step 1's
*single hardest residual*: getting the Sylow-p `Q` of the abelian normal subgroup
`A` to be normal in `↥H`. Its verdict: "**no direct bearer**" — `Subgroup.Characteristic`
ships only `characteristic_iff_{map,comap}_{eq,le}` + `bot`/`top`, with no
`Characteristic.trans` or transitivity-through-subtype lemma — so the ACT session
"must build a ~10–30 LOC bridge OR reroute via an abelian primary-component
construction". Budgeted accordingly.

## Finding

The verdict is wrong. The step does **not** need `Q.map A.subtype` characteristic
in `↥H` — it needs only **normal**, and that is a Mathlib *instance*:

```
-- Mathlib/GroupTheory/GroupAction/ConjAct.lean:260  (namespace ConjAct)
instance normal_of_characteristic_of_normal {H : Subgroup G} [hH : H.Normal]
    {K : Subgroup H} [h : K.Characteristic] : (K.map H.subtype).Normal
```

Confirmed present at the exact lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0):

```
gh api repos/leanprover-community/mathlib4/contents/\
  Mathlib/GroupTheory/GroupAction/ConjAct.lean?ref=2df2f015... | jq -r .content | base64 -d
# → 293 lines; instance at line 260
gh search code --repo leanprover-community/mathlib4 "Characteristic" "map" "Normal"
# → ConjAct.lean: normal_of_characteristic_of_normal ... (K.map H.subtype).Normal
```

## Instantiation in this proof

- `G := ↥H`.
- lemma-`H := A := derivedSeries ↥H (d-1)` — abelian, characteristic in `↥H`
  (`derivedSeries_characteristic`), hence `A.Normal` (characteristic ⟹ normal).
- lemma-`K := Q`, the Sylow-p of `↥A` — abelian ⟹ Sylow normal ⟹ characteristic
  in `↥A` (`Sylow.characteristic_of_normal`, Sylow.lean:728), so `Q.Characteristic`.

Both instance hypotheses (`A.Normal`, `Q.Characteristic`) are satisfied, so
`(Q.map A.subtype).Normal` holds **by typeclass resolution — 0 LOC**. Being an
`instance` (not a named lemma), it does not even need to be invoked explicitly.

## Net effect

- S8's "single hardest residual" collapses to a 0-LOC automatic instance.
- The offered abelian-primary-component reroute is unnecessary.
- Step 1 wiring budget revised ~100–150 → ~70–110 LOC. Risk R4 stays MEDIUM,
  now dominated by `v_p(|H|)=1` Legendre arithmetic + `Sylow.ofCard` transport,
  not by missing infrastructure.
- All five sorries remain; discharge still gated on a Docker-up (or
  Aristotle-up) ACT session.

## Files touched

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean` — Step 1
  docstring step-4 line + residual note (docstring only, no code/sorry change).
- `research/problems/.../knowledge.md` — R4 §S10.
- `research/problems/.../state.md` — iteration 10 header + entry.
