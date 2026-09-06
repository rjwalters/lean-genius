"""Check the abstract rainbow-coloring counterledger, not an ambient graph."""

from itertools import combinations


def check(p: int) -> None:
    assert p >= 11 and all(p % d for d in range(2, int(p**0.5) + 1))
    n = p + 1
    edges = [(x, y) for x in range(p) for y in range(p) if (y - x) % p not in (0, 1)]
    slopes = [t for t in range(2, p) if all((1 + a * t) % p for a in (1, 2, 3))][:3]
    assert len(slopes) == 3
    recolored = []
    colors = []
    for a, t in zip((1, 2, 3), slopes):
        line = [(x, y) for x, y in edges if y == t * x % p]
        assert len(line) == p - 2
        chosen = set(line[: p - 3])
        recolored.append(chosen)
        colors.append({e: p if e in chosen else (e[0] + a * e[1]) % p for e in edges})
    assert len(edges) == n * (n - 4) + 3
    for coloring in colors:
        sizes = [sum(c == r for c in coloring.values()) for r in range(n)]
        assert sorted(sizes) == [n - 4] * (n - 3) + [n - 3] * 3
        # Exactly three missing colors at every vertex; every color is used.
        for side in (0, 1):
            for vertex in range(p):
                incident = [coloring[e] for e in edges if e[side] == vertex]
                assert len(incident) == len(set(incident)) == n - 3
        # Abstract owner profile: gamma_ij=1 for all pairs, u=0.
        high = [r for r, size in enumerate(sizes) if size == n - 3]
        gj, gk, slack = ({high[0]}, {high[1]}, {high[2]})
        assert all(sizes[r] == n - 4 + (r in gj) + (r in gk) + (r in slack) for r in range(n))
    for i, j in combinations(range(3), 2):
        assert len({(colors[i][e], colors[j][e]) for e in edges}) == len(edges)
        assert len(recolored[i] & recolored[j]) <= 1
    print(f"p={p}, q={p+3}, n={n}: PASS ({len(edges)} edges, three orthogonal proper colorings)")


if __name__ == "__main__":
    for prime in (11, 13, 17, 29, 61, 127):
        check(prime)
