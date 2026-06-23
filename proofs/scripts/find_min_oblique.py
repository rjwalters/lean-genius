#!/usr/bin/env python3
"""
Find knight's tour minimizing obtuse (oblique) angles.
Uses randomized Warnsdorff with bias against creating obtuse angles.
"""

import random
import sys
from typing import List, Tuple, Set, Optional

Pos = Tuple[int, int]

def neighbors(r: int, c: int) -> List[Pos]:
    moves = [(1,2), (2,1), (2,-1), (1,-2), (-1,-2), (-2,-1), (-2,1), (-1,2)]
    return [(r+dr, c+dc) for dr, dc in moves if 0 <= r+dr < 8 and 0 <= c+dc < 8]

def dot(v1: Pos, v2: Pos) -> int:
    return v1[0] * v2[0] + v1[1] * v2[1]

def is_obtuse(prev: Pos, curr: Pos, next_: Pos) -> bool:
    v1 = (curr[0] - prev[0], curr[1] - prev[1])
    v2 = (next_[0] - curr[0], next_[1] - curr[1])
    return dot(v1, v2) < 0

def count_obtuse(tour: List[Pos]) -> int:
    n = len(tour)
    return sum(1 for i in range(n)
               if is_obtuse(tour[(i-1) % n], tour[i], tour[(i+1) % n]))

def warnsdorff_tour_biased(start: Pos, bias_against_obtuse: float = 0.9) -> Optional[List[Pos]]:
    """Warnsdorff with penalty for creating obtuse angles."""
    tour = [start]
    visited = {start}

    while len(tour) < 64:
        curr = tour[-1]
        candidates = []

        for next_ in neighbors(*curr):
            if next_ in visited:
                continue

            # Base Warnsdorff score (lower = better)
            base_score = len([n for n in neighbors(*next_) if n not in visited and n != next_])

            # Penalty for creating obtuse angle
            penalty = 0
            if len(tour) >= 2:
                prev = tour[-2]
                if is_obtuse(prev, curr, next_):
                    penalty = 100  # Large penalty

            score = base_score + penalty
            candidates.append((score, random.random(), next_))  # Random tiebreaker

        if not candidates:
            return None

        candidates.sort()
        next_pos = candidates[0][2]

        tour.append(next_pos)
        visited.add(next_pos)

    # Check if closed
    if start in neighbors(*tour[-1]):
        return tour
    return None

def search(max_attempts: int = 1000000):
    best_tour = None
    best_count = 100

    starts = [(r, c) for r in range(8) for c in range(8)]

    for attempt in range(max_attempts):
        start = random.choice(starts)
        tour = warnsdorff_tour_biased(start)

        if tour:
            count = count_obtuse(tour)
            if count < best_count:
                best_count = count
                best_tour = tour
                print(f"Attempt {attempt+1}: Found tour with {count} obtuse angles", flush=True)

                if count == 4:
                    return tour, count

        if (attempt + 1) % 100000 == 0:
            print(f"  ... {attempt+1} attempts, best so far: {best_count}", flush=True)

    return best_tour, best_count

def format_lean(tour: List[Pos]) -> str:
    squares = [f"(⟨{r}, by omega⟩, ⟨{c}, by omega⟩)" for r, c in tour]
    return "def minimalObliqueTour : Vector (Fin 8 × Fin 8) 64 := #v[\n  " + ",\n  ".join(squares) + "\n]"

if __name__ == "__main__":
    print("Searching for knight's tour with minimum obtuse angles...")
    print("Target: 4 obtuse angles (Knuth's unique tour)")
    print(flush=True)

    tour, count = search(max_attempts=2000000)

    if tour:
        print(f"\nBest tour found: {count} obtuse angles")
        print(f"Tour: {tour}")

        if count == 4:
            print("\nSUCCESS! Found the unique tour with 4 obtuse angles!")
            print("\nLean format:")
            print(format_lean(tour))
