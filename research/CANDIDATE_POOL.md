# Research Candidate Pool

Pre-evaluated problems ready for random selection. All have EV > 40.

**Selection method**: Pick randomly. Don't overthink it.

---

## Pool A: High-Value Formalizations (EV 50-70)

Problems where the math is known but Lean formalization is significant.

| ID | Problem | Significance | Tractability | Notes |
|----|---------|--------------|--------------|-------|
| A1 | Bounded prime gaps (Zhang) | 9 | 3 | First Lean formalization of 2013 breakthrough |
| A2 | Weak Goldbach (Helfgott) | 8 | 3 | Every odd n>5 is sum of 3 primes |
| A3 | Szemerédi's theorem | 8 | 4 | Arithmetic progressions in dense sets |
| A4 | Green-Tao (existence) | 9 | 2 | Primes contain arbitrary AP |
| A5 | 2D Navier-Stokes regularity | 8 | 4 | Known result, major formalization |
| A6 | Prime Number Theorem (explicit) | 7 | 5 | With effective error bounds |

## Pool B: Partial Progress Targets (EV 40-60)

Problems where any progress is notable.

| ID | Problem | Significance | Tractability | Notes |
|----|---------|--------------|--------------|-------|
| B1 | Twin prime - specific forms | 8 | 4 | Prove for primes ≡ 1 (mod 4) or similar |
| B2 | Goldbach - residue classes | 7 | 4 | Prove for specific mod classes |
| B3 | Collatz - structured starts | 6 | 5 | Prove for 2^n-1, Mersenne numbers |
| B4 | Legendre partial | 7 | 3 | Prime between n² and (n+1)² for specific n |
| B5 | Cramér gaps - explicit | 7 | 3 | Improve explicit gap bounds |
| B6 | Bertrand improvement | 6 | 5 | Tighten prime existence bounds |

## Pool C: Novel Connections (EV 40-55)

Problems where we might find unexpected links.

| ID | Problem | Significance | Tractability | Notes |
|----|---------|--------------|--------------|-------|
| C1 | RH ↔ prime gaps | 8 | 2 | Formalize conditional results |
| C2 | Collatz ↔ p-adics | 6 | 4 | Novel formalization approach |
| C3 | Primes ↔ randomness | 7 | 4 | Cramér model formalization |
| C4 | Irrationality measures | 6 | 5 | Bounds on rational approximations |
| C5 | Diophantine obstacles | 7 | 3 | Why equations have no solutions |

## Pool D: Barrier/Impossibility Results (EV 45-60)

Proving why things CAN'T work is valuable.

| ID | Problem | Significance | Tractability | Notes |
|----|---------|--------------|--------------|-------|
| D1 | P≠NP barriers formalize | 8 | 4 | Relativization, natural proofs |
| D2 | Angle trisection complete | 5 | 6 | We have partial, finish it |
| D3 | Impossibility catalog | 6 | 5 | Systematic impossibilities |
| D4 | Independence results | 7 | 3 | What's unprovable in ZFC |

---

## Random Selection Protocol

```bash
# Generate random number 1-20
PICK=$(jot -r 1 1 20)

# Map to candidate
case $PICK in
  1) echo "A1" ;;  2) echo "A2" ;;  3) echo "A3" ;;
  4) echo "A4" ;;  5) echo "A5" ;;  6) echo "A6" ;;
  7) echo "B1" ;;  8) echo "B2" ;;  9) echo "B3" ;;
  10) echo "B4" ;; 11) echo "B5" ;; 12) echo "B6" ;;
  13) echo "C1" ;; 14) echo "C2" ;; 15) echo "C3" ;;
  16) echo "C4" ;; 17) echo "C5" ;;
  18) echo "D1" ;; 19) echo "D2" ;; 20) echo "D3" ;;
esac
```

---

## Exclusions (Already Done or In Progress)

- All nth root irrationality (done)
- √a + √b irrationality (done, pattern known)
- Hurwitz n=3 (in progress)
- Basic prime facts (in gallery)

---

## Adding to the Pool

To add a candidate:
1. Verify EV > 40 using VALUE_ASSESSMENT.md
2. Ensure it's not Tier D (stamp collecting)
3. Add to appropriate pool section
4. Update random selection range
