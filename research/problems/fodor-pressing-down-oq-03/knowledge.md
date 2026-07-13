# Knowledge — Reflection Principles and □_κ over `Club/Basic`

> S1 OBSERVE feasibility map for `fodor-pressing-down-oq-03`.
> Sources: Jech, *Set Theory* (3rd ed.) §8, §23; Kunen, *Set Theory*
> (2011) II.6, III.6; Cummings, "Iterated Forcing and Elementary
> Embeddings" and the *Handbook of Set Theory* square chapter; Todorcevic,
> *Walks on Ordinals*. All Lean references are to the tree at
> `proofs/Proofs/` (module `Proofs.Club.Basic`, 230 LOC, 0 sorries,
> 0 axioms per the parent `meta.json`).

---

## 1. The two halves of the question

The OQ bundles two objects of **opposite logical character**. Keeping them
apart is the single most important observation for anyone continuing this
slug.

| Object | ZFC status | Uses club structure? | Formalizable now? |
|--------|------------|----------------------|-------------------|
| **Club reflection** (a club `C` reflects: `C ∩ α` is club in `α` at each acc. point `α`) | **Theorem of ZFC** | yes (positive) | **Yes** — small, on current infra |
| **Trace of a club** (`Lim(C) = {α : α ∈ Acc(C)}` is club) | Theorem of ZFC | yes | Yes — small |
| **Full stationary reflection** `Refl(κ)` | **Independent** (large-cardinal strength; fails at ω₁, needs ≥ weakly compact at ω₂) | yes | No — not a ZFC theorem, cannot be "verified" |
| **□_κ square sequence** | consistent with ZFC (Jensen: holds in `L`); *negation* also consistent | **non-club / coherent** | No — needs a new coherent-club module |
| **□_κ ⟹ ∃ non-reflecting stationary `S ⊆ κ⁺`** | Theorem of ZFC (given a □-sequence) | non-club | No — depends on the □ module |

**Design consequence.** A Lean deliverable for this OQ must ship the
*positive ZFC fragment* (rows 1–2) as verified content, and record the
independent / obstruction fragment (rows 3–5) as *stated hypotheses or
future modules* — never as verified ZFC theorems. Claiming a positive
reflection theorem "0-axiom verified" would be **mathematically false**.

---

## 2. Precise definitions in the `Club/Basic` framework

The module works "below an ordinal `o`" (`o = κ.ord` in applications).
Reflection lifts verbatim.

```lean
-- Reflection of S at α  (α < o), phrased with the existing predicate.
-- "S reflects at α"  ⟺  S is stationary *below α*.
def Reflects (S : Set Ordinal) (α : Ordinal) : Prop :=
  Ordinal.IsStationaryBelow S α

-- The trace / set of reflection points of S below o.
def Trace (S : Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {α | α < o ∧ Reflects S α}

-- Non-degeneracy guard: reflection is only meaningful at points of
-- uncountable cofinality (see §3.3). Encoded as a side predicate, not
-- baked into `Reflects`, to keep the base lemmas cofinality-free.
def UncofPoint (α : Ordinal) : Prop := Ordinal.omega0 < α.cof.ord
```

Note `Reflects S α := IsStationaryBelow S α` is faithful: `IsStationaryBelow`
already quantifies over clubs *below α*, all of which are `⊆ Iio α`, so
"`S` meets every club below `α`" is exactly "`S ∩ α` is stationary in `α`".
No `S ∩ Iio α` bookkeeping is needed at the definition site.

**□_κ (target definition, needs a new module — see §5):**

```lean
-- κ⁺ = (Order.succ κ) at the cardinal level; here o := (Order.succ κ).ord.
structure IsSquareSequence (C : Ordinal → Set Ordinal) (κ : Cardinal.{0}) : Prop where
  club    : ∀ α, α < (Order.succ κ).ord → IsSuccLimit α → IsClubBelow (C α) α
  otp_le  : ∀ α, α < (Order.succ κ).ord → (C α).OrderTypeLE κ.ord   -- otp(C α) ≤ κ  (API TBD)
  cohere  : ∀ α β, β.IsAcc (C α) → C β = C α ∩ Set.Iio β            -- the coherence law
```

`otp_le` is the load-bearing gap: it needs an **order-type / enumeration**
API for a `Set Ordinal` that Mathlib does not currently expose in the
`IsClubBelow` idiom (see §5.2).

---

## 3. Truth-value map (do not overclaim)

### 3.1 Club reflection — ZFC theorem, TARGET #1

**Claim.** If `IsClubBelow C o`, `α ≤ o`, and `α.IsAcc C` (`α` is an
accumulation point of `C`), then `IsClubBelow (C ∩ Set.Iio α) α`.

*Proof sketch (all three fields).*
- `subset_Iio`: `C ∩ Iio α ⊆ Iio α` — immediate.
- `closed` (below `α`): `C` is `IsClosedBelow … o`; closedness is *local*
  (`isClosedBelow_iff` quantifies "for all acc. points `< α`"), so the
  same witness works below `α`. Restricting the ambient bound from `o`
  down to `α ≤ o` only *shrinks* the set of accumulation points to check.
- `unbounded` (below `α`): this **is** the hypothesis `α.IsAcc C`. Unfold
  `isAcc_iff`: for every `p < α` there is `δ ∈ C` with `p < δ < α`; that
  `δ ∈ C ∩ Iio α`, giving `IsUnboundedBelow (C ∩ Iio α) α`.

Reuses `IsClubBelow.mem_of_isAcc` (Basic:73), `isClosedBelow_iff`,
`isAcc_iff`. **This is the honest formal meaning of "clubs reflect."**

### 3.2 Trace of a club is club — ZFC theorem, TARGET #2

**Claim.** For `IsClubBelow C o` (with `o` a limit), the limit-point set
`Lim(C) o = {α | α < o ∧ α.IsAcc C}` satisfies `IsClubBelow (Lim(C) o) o`.

Closed: a limit of accumulation points of `C` is an accumulation point.
Unbounded: between any `p < o` and `o`, iterate the club's unboundedness ω
times and take the sup — a standard "ω-th accumulation point exists" argument
(the same *zipper* pattern already used in `diagInter_isUnboundedBelow`).
Corollary: a club reflects at *club-many* points (`Trace` of a club contains
a club), the strongest positive statement provable here.

### 3.3 Why full reflection is NOT available — the ω₁ obstruction (ZFC)

Reflection at `α` is only non-degenerate when `cf(α) > ω`: for `cf(α) = ω`,
a cofinal ω-sequence's closure is a club in `α` that a "diagonal" stationary
set can dodge, so stationarity-in-`α` carries no reflection content.

**Formalizable ZFC fact (a genuine negative result, TARGET #3-lite):**
> For every limit `α < ω₁`, `cf(α) = ω`; hence `ω₁` has **no** reflection
> point of uncountable cofinality below it: `Trace S ω₁ ∩ {α | UncofPoint α} = ∅`
> for *every* `S ⊆ ω₁`.

Reason: every `α < ω₁` is a countable ordinal, so `cf(α) ≤ |α| ≤ ℵ₀`. This
is exactly why non-trivial reflection first lives at `ω₂`, and why □ is
formulated at successor cardinals `κ⁺ ≥ ω₂`. This statement **is** ZFC-true
and formalizable (needs `Cardinal.cof` lemmas + `Ordinal.cof_lt_card`-style
bounds); it is the *right* honest content to pair with the base case, in
place of any (false-in-ZFC) positive reflection theorem.

### 3.4 □_κ and non-reflection — ZFC-from-□, but □ itself is the frontier

Given a `□_κ`-sequence, `S = {α < κ⁺ : cf(α) = ω}` restricted along the
coherent clubs is stationary and non-reflecting: at any `β` with `cf(β) > ω`,
`C_β` is a club in `β` missing `S ∩ β` in a way the coherence law
propagates. This is a real ZFC theorem *relative to the hypothesis*
`IsSquareSequence C κ`. It is formalizable as a theorem taking
`IsSquareSequence` as a **hypothesis** (0 axioms, honest), but the
`IsSquareSequence` *structure* + its `otp_le` field are the missing infra.

---

## 4. Reusable inventory from `Club/Basic.lean`

Directly reusable for TARGETS #1–#3-lite (no change to `Basic`):

| Lemma (Basic.lean) | Role in reflection layer |
|--------------------|--------------------------|
| `IsClubBelow` (49) / fields | the reflected object |
| `IsClubBelow.mem_of_isAcc` (73) | club contains its acc. points → closedness transport |
| `isClubBelow_Iio_of_isSuccLimit` (95) | canonical club witness below a limit |
| `IsUnboundedBelow` (44) + `.nonempty` (108) | the unbounded field of the reflected club |
| `IsStationaryBelow` (55) | **is** `Reflects` |
| `IsStationaryBelow.nonempty` (196) | reflection ⇒ nonempty trace slice |
| `IsStationaryBelow.of_subset` (205) | pass reflection to subsets |
| `IsStationaryBelow.mono` (226) / `IsUnboundedBelow.mono` (220) | monotonicity of the trace |

Mathlib substrate: `Ordinal.IsAcc`, `Ordinal.IsClosedBelow`, `isAcc_iff`,
`isClosedBelow_iff` (Topology); `Ordinal.cof`, cofinality bounds
(Cofinality) for §3.3.

**Nothing in `Basic` needs editing** for the ZFC-true fragment — the
reflection layer is a *pure downstream extension file*.

---

## 5. Mathlib / gallery gaps (what blocks the □ half)

### 5.1 No stationary-reflection API anywhere
Neither Mathlib nor the gallery defines `Reflects` / `Trace`. This is the
easy gap — filled by TARGETS #1–#3 (this OQ).

### 5.2 No order-type / enumeration API for `Set Ordinal` clubs — **the real blocker**
`□_κ`'s `otp(C_α) ≤ κ` needs the order type of a set of ordinals. Mathlib has
`Ordinal.type`/`Ordinal.typein` for well-orders and `Ordinal.enumOrd` for
*classes*, but the `IsClubBelow`-idiom sets are `Set Ordinal`, not bundled
well-orders. A bridge (`Set Ordinal → Ordinal` order type, plus
`otp (C ∩ Iio β) = typein …` coherence lemmas) must be built before `□` can
even be *stated* cleanly. ~1 new module.

### 5.3 Coherence bookkeeping
The `cohere` law `C_β = C_α ∩ Iio β` at limit points of `C_α` is a
recursion-friendly statement, but *constructing* a □-sequence (Jensen's
`L`-construction) is far beyond current gallery scope. The tractable
direction is **hypothesis-taking**: prove "□ ⟹ non-reflecting stationary
set" with `IsSquareSequence` as an input, deferring existence.

### 5.4 κ⁺ ergonomics
Working at `(Order.succ κ).ord` (successor *cardinal* as an ordinal) needs
`Cardinal.ord_succ`-style rewriting; manageable but adds friction.

---

## 6. Graded plan

### S2 (tractable, ZFC-true, ~40–70 LOC, ONE downstream file)
Create `proofs/Proofs/Reflection/Basic.lean` (`import Proofs.Club.Basic`),
namespace `Ordinal`:

1. `def Reflects`, `def Trace` (§2).
2. `theorem clubReflects` — TARGET #1 (§3.1). *Load-bearing; ~20 LOC.*
3. `theorem isClubBelow_trace` — TARGET #2 (§3.2), club reflects at
   club-many points. *~25 LOC, reuses the zipper idea.*
4. `theorem Reflects.mono`, `Reflects.of_superset` — cheap monotonicity.
5. `theorem no_uncof_reflection_omega1` — TARGET #3-lite (§3.3), the honest
   ω₁ non-reflection fact. *~15 LOC, cofinality bound.*

All 0-axiom, 0-sorry, ZFC-true. Gallery entry
`fodor-pressing-down-oq-03` becomes a *verified* "reflection base layer"
proof. **This is the recommended first ACT once a build route exists.**

### S3 (frontier, multi-file)
6. `Reflection/OrderType.lean` — the `Set Ordinal` order-type bridge (§5.2).
7. `structure IsSquareSequence` + `theorem square_gives_nonreflecting`
   (hypothesis-taking form, §3.4). Existence of □ is **out of scope**
   (Jensen `L`-construction).

### Honest answer to the OQ
> **Yes, partially.** The club/stationary substrate extends *immediately*
> to the **positive base case** of reflection (clubs reflect; trace of a
> club is club) and to the **ZFC non-reflection fact at ω₁** — all
> 0-axiom formalizable on `Club/Basic` as-is (S2). It does **not** extend
> to **full stationary reflection** (independent of ZFC — not a theorem to
> verify) nor, without a new order-type/coherence module, to a clean
> statement of **□_κ** itself; the "□ ⇒ non-reflecting stationary set"
> implication is reachable only in *hypothesis-taking* form (S3).

---

## 7. Build/verification status this cycle

**Not built.** The working environment has **no Mathlib `.olean` cache**
anywhere under `proofs/.lake` (checked: `Mathlib.olean`, `Ordinal/Topology.olean`
absent) and disk sits at 99% (~11 GiB free). Compiling Mathlib from source
is infeasible here (hours + tens of GiB). Per project precedent (e.g. the
feasibility-map deliverable pattern), this S1 OBSERVE ships as documentation
+ a paste-ready S2 design; the S2 Lean file should be authored and verified
in a cycle with a warm Mathlib cache (`docker-build.sh` or
`lake env lean` off a populated `.lake`). No unverified Lean is committed.
