#!/usr/bin/env python3
"""Check polarity witnesses at every order q^2+1 through q^2+q+1.

Finite calibration at q=4,8,16; the companion note gives the uniform proof.
No graph of minimum degree q at order q^2 is claimed. Standard library.
"""


def polarity_graph(q, modulus):
    def multiply(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & q:
                a ^= modulus
        return result

    # Confirm the chosen polynomial gives a field, independently of its label.
    assert all(any(multiply(a, b) == 1 for b in range(1, q))
               for a in range(1, q))
    points = ([(1, x, y) for x in range(q) for y in range(q)]
              + [(0, 1, x) for x in range(q)] + [(0, 0, 1)])

    def dot(v, w):
        return multiply(v[0], w[0]) ^ multiply(v[1], w[1]) ^ multiply(v[2], w[2])

    adjacency = [{j for j, w in enumerate(points) if i != j and dot(v, w) == 0}
                 for i, v in enumerate(points)]
    absolute = {i for i, v in enumerate(points) if dot(v, v) == 0}
    return adjacency, absolute, points.index((1, 1, 1))


def main():
    for q, modulus in [(4, 0b111), (8, 0b1011), (16, 0b10011)]:
        adjacency, absolute, nucleus = polarity_graph(q, modulus)
        vertices = set(range(len(adjacency)))
        assert len(vertices) == q*q + q + 1
        assert len(absolute) == q + 1 and nucleus not in absolute
        assert adjacency[nucleus] == absolute
        assert all(len(adjacency[v]) == (q if v in absolute else q + 1)
                   for v in vertices)
        assert all(v not in adjacency[v] for v in vertices)
        assert all((v in adjacency[w]) == (w in adjacency[v])
                   for v in vertices for w in vertices)
        assert all(len(adjacency[v] & adjacency[w]) <= 1
                   for v in vertices for w in range(v))
        assert all(len(adjacency[v] & absolute) == 1
                   for v in vertices - absolute - {nucleus})
        a = min(absolute)
        eligible = sorted(adjacency[a] - {nucleus})
        assert len(eligible) == q - 1
        assert all(not (adjacency[v] & adjacency[a]) for v in adjacency[a])
        orders = {len(vertices)}
        for count in range(q):
            deleted = {a, *eligible[:count]}
            retained = vertices - deleted
            degrees = [len(adjacency[v] & retained) for v in retained]
            assert min(degrees) == q
            if count == q - 1:
                assert set(degrees) == {q}
                after_nucleus = retained - {nucleus}
                assert len(after_nucleus) == q*q
                assert all(len(adjacency[v] & after_nucleus) == q - 1
                           for v in absolute - {a})
            orders.add(len(retained))
        assert orders == set(range(q*q + 1, q*q + q + 2))
        print(f"q={q}: orders {min(orders)}..{max(orders)} PASS; "
              f"q^2+1 regular, next deletion fails")


if __name__ == "__main__":
    main()
