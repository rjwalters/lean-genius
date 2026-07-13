# Divergent Thinking: Idea Generation

**Purpose**: Generate many possible approaches without judgment.

**Mindset**: Quantity over quality. No idea is too wild. Judgment comes later.

---

## The Process

### Step 1: Prepare Your Mind

Before generating ideas, ensure you have:
- [ ] Read the problem statement thoroughly
- [ ] Understood what's already been tried
- [ ] Reviewed related proofs in the gallery
- [ ] Identified key mathematical objects involved

### Step 2: Apply Each Lens

Generate at least one idea for EACH of these lenses. Don't skip any.

---

## Lens 1: ANALOGY

**Prompt**: "This problem is like [X], which was solved by [Y technique]"

Think about:
- What does this problem remind you of?
- What solved problems share similar structure?
- Can we map this to a problem in another domain?

**Examples**:
- "Proving prime gaps is like proving irrationality—both need contradiction"
- "This feels like a pigeonhole argument—too many objects, not enough bins"
- "The structure is like graph coloring—maybe chromatic methods apply"

**Your ideas**:
```
1. This is like _________________ which was solved by _________________
2. The structure reminds me of _________________
3. In [other domain], this would be _________________
```

---

## Lens 2: CONSTRAINT RELAXATION

**Prompt**: "What if we only proved this for a special case?"

Think about:
- What's the simplest non-trivial case?
- Can we restrict to a specific class of objects?
- What if we assumed extra conditions?

**Examples**:
- "What if we only prove for n > 10^6?"
- "What if we assume the generalized Riemann hypothesis?"
- "What about primes of the form 4k+1 only?"

**Your ideas**:
```
1. Special case: only for _________________
2. With extra assumption: _________________
3. Restricted to: _________________
```

---

## Lens 3: CONSTRAINT TIGHTENING

**Prompt**: "Can we prove something stronger?"

Think about:
- Is there a more powerful statement that implies this?
- Can we prove effective bounds instead of just existence?
- Is there a uniform version?

**Examples**:
- "Instead of 'infinitely many', can we give explicit density?"
- "Instead of existence, can we construct explicitly?"
- "Can we prove it for all n simultaneously, not just one?"

**Your ideas**:
```
1. Stronger version: _________________
2. Effective bound: _________________
3. Constructive proof: _________________
```

---

## Lens 4: REPRESENTATION SHIFT

**Prompt**: "In [other field's] language, this becomes..."

Think about:
- How would an algebraist view this?
- What does this look like geometrically?
- Is there a combinatorial reformulation?
- Can we encode this analytically?

**Examples**:
- "Algebraically: this is about ideal structure in Z[√2]"
- "Geometrically: these are lattice points on a hyperbola"
- "Analytically: this is about zeta function zeros"
- "Categorically: this is about a functor preserving limits"

**Your ideas**:
```
1. Algebraic view: _________________
2. Geometric view: _________________
3. Analytic view: _________________
4. Combinatorial view: _________________
```

---

## Lens 5: DECOMPOSITION

**Prompt**: "What lemmas would make this trivial?"

Think about:
- If we could prove X, the rest would follow easily
- What are the independent sub-problems?
- What's the key technical lemma?

**Examples**:
- "If we had a good sieve bound, we could finish with standard arguments"
- "The problem splits into: (A) infinitely many primes, (B) gap bounded"
- "Key lemma: show the density is positive"

**Your ideas**:
```
1. Key enabling lemma: _________________
2. Subproblem A: _________________
3. Subproblem B: _________________
4. If we knew _________________, then _________________
```

---

## Lens 6: EXTREME CASES

**Prompt**: "What happens at the boundaries?"

Think about:
- n = 0, 1, 2
- n → ∞
- p = 2 (smallest prime)
- Edge cases in definitions

**Examples**:
- "For n = 1, the statement is vacuously true"
- "As n → ∞, the average gap grows like log(n)"
- "For p = 2, we need special handling"

**Your ideas**:
```
1. At n = 0: _________________
2. At n = 1: _________________
3. As n → ∞: _________________
4. Edge case: _________________
```

---

## Lens 7: NEGATION / CONTRAPOSITION

**Prompt**: "What would a counterexample look like?"

Think about:
- If this were false, what would exist?
- Can we prove the contrapositive instead?
- What's the minimal counterexample structure?

**Examples**:
- "If there were only finitely many such primes, we could list them"
- "A counterexample would need to avoid all primes in arithmetic progressions"
- "Contrapositive: if no such n exists, then [consequence]"

**Your ideas**:
```
1. Counterexample structure: _________________
2. Contrapositive: _________________
3. If false, then: _________________
```

---

## Lens 8: COMBINATION

**Prompt**: "What if we combined technique A with technique B?"

Think about:
- Sieve methods + analytic estimates
- Algebraic structure + counting arguments
- Induction + contradiction
- Probabilistic method + deterministic construction

**Examples**:
- "Combine circle method (analytic) with sieve (combinatorial)"
- "Use algebraic structure of Z[ω] with Dirichlet's theorem"
- "Ergodic theory + number theory (à la Furstenberg)"

**Your ideas**:
```
1. Combine _________________ with _________________
2. Combine _________________ with _________________
3. Hybrid approach: _________________
```

---

## Lens 9: WILD CARD

**Prompt**: "The craziest approach would be..."

Let go of feasibility. What if we:
- Used heavy machinery (algebraic geometry, model theory)
- Made an outrageous assumption and worked backwards
- Tried something that "shouldn't" work

**Examples**:
- "What if we used étale cohomology?"
- "What if we computed it probabilistically and then derandomized?"
- "What if the key is looking at the p-adic structure?"

**Your ideas**:
```
1. Crazy idea: _________________
2. Outrageous machinery: _________________
3. Why-not idea: _________________
```

---

## Lens 10: CROSS-DOMAIN PERSPECTIVE

**Prompt**: "How would a [X specialist] see this?"

Think about:
- Physicist: conservation laws, symmetry, variational principles
- Computer scientist: algorithms, complexity, reduction
- Statistician: distributions, expectations, concentration
- Topologist: continuity, compactness, invariants

**Examples**:
- "A physicist might see this as a minimum energy configuration"
- "A CS person might reduce this to a known hard problem"
- "A probabilist might model primes as random with density 1/log(n)"

**Your ideas**:
```
1. Physics view: _________________
2. CS view: _________________
3. Statistics view: _________________
4. [Other field] view: _________________
```

---

## Step 3: Compile Your Ideas

List ALL ideas generated (aim for 10+):

```markdown
## Brainstorm Results: [Problem Name]
Date: [DATE]

### Ideas Generated

1. [Lens]: [Idea]
2. [Lens]: [Idea]
3. [Lens]: [Idea]
...

### Most Promising (gut feeling)
- Idea X: because...
- Idea Y: because...

### Most Unusual
- Idea Z: worth exploring because...

### Combinations to Try
- Idea A + Idea B: might work because...
```

---

## Important Reminders

1. **Don't self-censor**: Write down bad ideas too
2. **Don't evaluate yet**: That's the convergent phase
3. **Quantity matters**: More ideas = more chances
4. **Build on ideas**: One idea can spark another
5. **Include failures**: "We could try X... wait, that's what failed before, but what about X'?"

---

## After Brainstorming

Pass your complete list to the **Convergent Thinking** phase for evaluation.

The goal was generation. Now comes selection.
