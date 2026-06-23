#!/usr/bin/env python3
"""
Find tour (t) - the unique knight's tour with exactly 4 oblique turns.

Uses aggressive constraint propagation + randomized search.
"""

import random
from typing import Optional, List, Tuple, Set

Pos = Tuple[int, int]
CORNERS = frozenset([(0, 0), (0, 7), (7, 0), (7, 7)])

def knight_moves() -> List[Pos]:
    return [(1,2), (2,1), (2,-1), (1,-2), (-1,-2), (-2,-1), (-2,1), (-1,2)]

def neighbors(r: int, c: int) -> List[Pos]:
    result = []
    for dr, dc in knight_moves():
        nr, nc = r + dr, c + dc
        if 0 <= nr < 8 and 0 <= nc < 8:
            result.append((nr, nc))
    return result

def get_vec(p1: Pos, p2: Pos) -> Pos:
    return (p2[0] - p1[0], p2[1] - p1[1])

def dot(v1: Pos, v2: Pos) -> int:
    return v1[0] * v2[0] + v1[1] * v2[1]

def is_oblique(v_in: Pos, v_out: Pos) -> bool:
    return dot(v_in, v_out) < 0

def warnsdorff_score(pos: Pos, visited: Set[Pos], prev: Optional[Pos]) -> int:
    """Count available exits from pos (considering oblique constraint)."""
    if prev is None:
        return len([n for n in neighbors(*pos) if n not in visited])

    v_in = get_vec(prev, pos)
    count = 0
    for n in neighbors(*pos):
        if n in visited:
            continue
        v_out = get_vec(pos, n)
        if pos in CORNERS or not is_oblique(v_in, v_out):
            count += 1
    return count

def search_randomized(max_attempts: int = 100000) -> Optional[List[Pos]]:
    """Randomized search with Warnsdorff heuristic."""
    start = (0, 0)

    for attempt in range(max_attempts):
        tour = [start]
        visited = {start}
        prev = None

        while len(tour) < 64:
            current = tour[-1]
            candidates = []

            for next_pos in neighbors(*current):
                if next_pos in visited:
                    continue

                # Check oblique constraint
                if prev is not None and current not in CORNERS:
                    v_in = get_vec(prev, current)
                    v_out = get_vec(current, next_pos)
                    if is_oblique(v_in, v_out):
                        continue

                # Score by constrained Warnsdorff
                score = warnsdorff_score(next_pos, visited | {next_pos}, current)
                candidates.append((score, next_pos))

            if not candidates:
                break  # Dead end, restart

            # Pick randomly among minimum-score candidates
            min_score = min(c[0] for c in candidates)
            best = [c[1] for c in candidates if c[0] == min_score]
            next_pos = random.choice(best)

            visited.add(next_pos)
            tour.append(next_pos)
            prev = current

        # Check if we found a valid closed tour
        if len(tour) == 64:
            last = tour[-1]
            if start in neighbors(*last):
                # Check oblique at last position
                if last not in CORNERS:
                    v_in = get_vec(tour[-2], last)
                    v_out = get_vec(last, start)
                    if is_oblique(v_in, v_out):
                        continue

                oblique_count = count_oblique(tour)
                if oblique_count == 4:
                    print(f"Found tour with 4 oblique after {attempt + 1} attempts!")
                    return tour

        if (attempt + 1) % 50000 == 0:
            print(f"  ... {attempt + 1} attempts")

    return None

def count_oblique(tour: List[Pos]) -> int:
    count = 0
    n = len(tour)
    for i in range(n):
        prev = tour[(i - 1) % n]
        curr = tour[i]
        next_ = tour[(i + 1) % n]
        v_in = get_vec(prev, curr)
        v_out = get_vec(curr, next_)
        if is_oblique(v_in, v_out):
            count += 1
    return count

def validate_tour(tour: List[Pos]) -> bool:
    if len(tour) != 64:
        return False
    if len(set(tour)) != 64:
        return False
    for i in range(64):
        p1 = tour[i]
        p2 = tour[(i + 1) % 64]
        dr = abs(p1[0] - p2[0])
        dc = abs(p1[1] - p2[1])
        if not ((dr == 1 and dc == 2) or (dr == 2 and dc == 1)):
            return False
    return True

def tour_to_lean(tour: List[Pos]) -> str:
    squares = [f"(⟨{r}, by omega⟩, ⟨{c}, by omega⟩)" for r, c in tour]
    return "[\n  " + ",\n  ".join(squares) + "\n]"

if __name__ == "__main__":
    print("Searching for tour (t) with randomized Warnsdorff...")
    print("Constraint: exactly 4 oblique turns (all at corners)")
    print()

    tour = search_randomized(max_attempts=1000000)

    if tour:
        print()
        print("=" * 60)
        print("SUCCESS!")
        print(f"Valid: {validate_tour(tour)}, Oblique: {count_oblique(tour)}")
        print()
        print("Tour:", tour)
        print()
        print("Lean format:")
        print(tour_to_lean(tour))
    else:
        print("No tour found")
