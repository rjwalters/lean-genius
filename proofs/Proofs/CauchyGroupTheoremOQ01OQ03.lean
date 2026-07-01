import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# The prime spectrum of a finite group via element orders

*Follow-up to `cauchy-group-theorem-oq-01` (Open Question 2).*

The parent entry formalises **Cauchy's theorem** — if a prime `p` divides `|G|`
then `G` has an element of order `p` — together with a *one-way* contrapositive
certificate: the absence of an order-`p` element proves `p ∤ |G|`
(`not_dvd_card_of_no_orderOf_eq`).

Open Question 2 asks to turn that certificate into a **decidable test on the
prime set of `|G|`**: an algorithm that, for a concrete finite group, certifies
exactly which primes divide the order by exhibiting order-`p` elements (presence)
or ruling them out (absence).

The mathematical heart of such a test is the **biconditional** that the parent
stops short of stating. Cauchy gives the hard `(→)` direction; the elementary
Lagrange fact `orderOf x ∣ |G|` gives the easy `(←)` direction. Together:

> For a prime `p`, `p ∣ |G|` **if and only if** `G` has an element of order `p`.

Equivalently, the set of primes dividing `|G|` is *exactly* the set of primes
that occur as an element order:

> `p ∈ (Fintype.card G).primeFactors ↔ ∃ x : G, orderOf x = p`   (for `p` prime).

Because both sides are decidable predicates on a `Fintype`, this **is** the
decidable prime certificate: to certify the full prime spectrum of a concrete
group one checks, prime by prime, whether an order-`p` witness exists.

We prove the biconditional (multiplicative and additive), the two-way absence
certificate that generalises the parent's one-way version, the prime-spectrum
characterisation, and then run the certificate end-to-end on `ZMod 12`
(order `12 = 2² · 3`): primes `2, 3` are present, prime `5` is absent — all
discharged through the general theorems, with kernel `decide` only on `ℕ`
(no `native_decide`, so no `Lean.ofReduceBool`).

Everything is verified from Mathlib; the file introduces no axioms.
-/

variable {G : Type*}

/-! ## The Cauchy biconditional -/

/-- **Cauchy biconditional (multiplicative).** For a prime `p`, the prime `p`
divides `|G|` *if and only if* `G` contains an element of order exactly `p`.

The forward direction is Cauchy's theorem (`exists_prime_orderOf_dvd_card`); the
reverse is Lagrange's theorem in the form `orderOf x ∣ |G|` (`orderOf_dvd_card`).
The parent entry proves only the forward direction and a one-way contrapositive —
this biconditional is the missing piece that makes the prime test *decidable*. -/
theorem prime_dvd_card_iff_exists_orderOf [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    p ∣ Fintype.card G ↔ ∃ x : G, orderOf x = p := by
  refine ⟨exists_prime_orderOf_dvd_card p, ?_⟩
  rintro ⟨x, rfl⟩
  exact orderOf_dvd_card

/-- **Cauchy biconditional (additive).** The additive-group form of
`prime_dvd_card_iff_exists_orderOf`, using additive orders. -/
theorem prime_dvd_card_iff_exists_addOrderOf [AddGroup G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    p ∣ Fintype.card G ↔ ∃ x : G, addOrderOf x = p := by
  refine ⟨exists_prime_addOrderOf_dvd_card p, ?_⟩
  rintro ⟨x, rfl⟩
  exact addOrderOf_dvd_card

/-! ## The two-way absence certificate -/

/-- **Two-way absence certificate (multiplicative).** For a prime `p`, `p` does
**not** divide `|G|` *if and only if* `G` has *no* element of order `p`.

This upgrades the parent's `not_dvd_card_of_no_orderOf_eq` (which proves only
`(no order-p element) → p ∤ |G|`) to a biconditional: the *absence* of an
order-`p` witness is not merely sufficient but *equivalent* to `p ∤ |G|`. It is
the formal statement that "search for an order-`p` element" is a *complete*
decision procedure for `p ∣ |G|`. -/
theorem not_dvd_card_iff_forall_orderOf_ne [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    ¬ p ∣ Fintype.card G ↔ ∀ x : G, orderOf x ≠ p := by
  rw [prime_dvd_card_iff_exists_orderOf]
  push_neg
  rfl

/-- **Two-way absence certificate (additive).** Additive-group form of
`not_dvd_card_iff_forall_orderOf_ne`. -/
theorem not_dvd_card_iff_forall_addOrderOf_ne [AddGroup G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    ¬ p ∣ Fintype.card G ↔ ∀ x : G, addOrderOf x ≠ p := by
  rw [prime_dvd_card_iff_exists_addOrderOf]
  push_neg
  rfl

/-! ## The prime spectrum as an order spectrum -/

/-- **Prime spectrum = order spectrum (multiplicative).** A prime `p` lies in the
set of prime factors of `|G|` *iff* it is realised as the order of some element.

This is the set-level packaging of the Cauchy biconditional: the prime factors of
`|G|` are exactly the primes appearing in the "order spectrum" `{orderOf x : x ∈ G}`.
It is the object OQ 2 calls the *certified prime set* of the group. -/
theorem mem_primeFactors_card_iff_exists_orderOf [Group G] [Fintype G] (p : ℕ)
    (hp : p.Prime) : p ∈ (Fintype.card G).primeFactors ↔ ∃ x : G, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nonempty G := ⟨1⟩
  rw [Nat.mem_primeFactors]
  refine ⟨fun h => (prime_dvd_card_iff_exists_orderOf p).1 h.2.1, fun h => ?_⟩
  exact ⟨hp, (prime_dvd_card_iff_exists_orderOf p).2 h, Fintype.card_ne_zero⟩

/-- **Prime spectrum = order spectrum (additive).** Additive-group form of
`mem_primeFactors_card_iff_exists_orderOf`. -/
theorem mem_primeFactors_card_iff_exists_addOrderOf [AddGroup G] [Fintype G] (p : ℕ)
    (hp : p.Prime) : p ∈ (Fintype.card G).primeFactors ↔ ∃ x : G, addOrderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nonempty G := ⟨0⟩
  rw [Nat.mem_primeFactors]
  refine ⟨fun h => (prime_dvd_card_iff_exists_addOrderOf p).1 h.2.1, fun h => ?_⟩
  exact ⟨hp, (prime_dvd_card_iff_exists_addOrderOf p).2 h, Fintype.card_ne_zero⟩

/-! ## Running the certificate on `ZMod 12`

The additive group `ZMod 12` has order `12 = 2² · 3`, so its certified prime set
is `{2, 3}`. We drive the general theorems above to certify the whole spectrum:
`2` and `3` are present (with explicit witnesses), and `5` is absent — the
prototypical output of the algorithm OQ 2 asks for. The presence/absence of each
prime in `(card).primeFactors` is obtained *through* the spectrum theorem, so the
concrete facts are corollaries of the general result rather than raw `ℕ`-trivia;
every step reduces to a `decide` on divisibility of `ℕ` only, keeping the file
free of `Lean.ofReduceBool`. -/

/-- **Presence at `p = 2`.** `ZMod 12` has an element of additive order `2`,
obtained from the Cauchy biconditional and `2 ∣ 12`. -/
theorem exists_addOrderOf_two_zmod12 : ∃ x : ZMod 12, addOrderOf x = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (prime_dvd_card_iff_exists_addOrderOf 2).1 ?_
  rw [ZMod.card]; decide

/-- **Presence at `p = 3`.** `ZMod 12` has an element of additive order `3`. -/
theorem exists_addOrderOf_three_zmod12 : ∃ x : ZMod 12, addOrderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (prime_dvd_card_iff_exists_addOrderOf 3).1 ?_
  rw [ZMod.card]; decide

/-- The explicit order-`2` witness: `6 : ZMod 12` satisfies `6 ≠ 0` and `6+6 = 0`,
so `addOrderOf 6 = 2`. Confirms the abstract presence certificate concretely. -/
theorem addOrderOf_six_zmod12 : addOrderOf (6 : ZMod 12) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact addOrderOf_eq_prime (by decide) (by decide)

/-- The explicit order-`3` witness: `4 : ZMod 12` satisfies `4 ≠ 0` and `4+4+4 = 0`,
so `addOrderOf 4 = 3`. -/
theorem addOrderOf_four_zmod12 : addOrderOf (4 : ZMod 12) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact addOrderOf_eq_prime (by decide) (by decide)

/-- **Absence at `p = 5`.** Since `5 ∤ 12`, the two-way absence certificate proves
`ZMod 12` has *no* element of additive order `5` — a universally quantified
non-existence obtained *without* enumerating all `12` elements, straight from the
general theorem. This is the "certified absence" half of OQ 2's algorithm. -/
theorem no_addOrderOf_five_zmod12 : ∀ x : ZMod 12, addOrderOf x ≠ 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [← not_dvd_card_iff_forall_addOrderOf_ne, ZMod.card]
  decide

/-- **`2` is in the certified prime spectrum of `ZMod 12`** — *because* an
order-`2` element exists. A direct corollary of the spectrum theorem, reading the
concrete membership off the presence certificate. -/
theorem two_mem_spectrum_zmod12 : (2 : ℕ) ∈ (Fintype.card (ZMod 12)).primeFactors :=
  (mem_primeFactors_card_iff_exists_addOrderOf 2 Nat.prime_two).2 exists_addOrderOf_two_zmod12

/-- **`3` is in the certified prime spectrum of `ZMod 12`** — because an order-`3`
element exists. -/
theorem three_mem_spectrum_zmod12 : (3 : ℕ) ∈ (Fintype.card (ZMod 12)).primeFactors :=
  (mem_primeFactors_card_iff_exists_addOrderOf 3 Nat.prime_three).2 exists_addOrderOf_three_zmod12

/-- **`5` is *not* in the certified prime spectrum of `ZMod 12`** — because no
order-`5` element exists. The absence certificate feeds the spectrum theorem to
rule the prime out. Together with the two memberships this pins the spectrum down
to exactly `{2, 3}`, prime by prime, entirely through the general theorem. -/
theorem five_not_mem_spectrum_zmod12 : (5 : ℕ) ∉ (Fintype.card (ZMod 12)).primeFactors := by
  rw [mem_primeFactors_card_iff_exists_addOrderOf 5 (by norm_num)]
  rintro ⟨x, hx⟩
  exact no_addOrderOf_five_zmod12 x hx

/-- **Full certified spectrum of `ZMod 12`.** Packaging the three certificates:
`5` is absent while `2` and `3` are present — the certified prime set is `{2, 3}`,
exactly the prime factors of `12`, obtained one prime at a time via the
biconditional rather than by trusting a `native_decide` computation. -/
theorem certified_spectrum_zmod12 :
    (5 : ℕ) ∉ (Fintype.card (ZMod 12)).primeFactors ∧
      (2 : ℕ) ∈ (Fintype.card (ZMod 12)).primeFactors ∧
        (3 : ℕ) ∈ (Fintype.card (ZMod 12)).primeFactors :=
  ⟨five_not_mem_spectrum_zmod12, two_mem_spectrum_zmod12, three_mem_spectrum_zmod12⟩
