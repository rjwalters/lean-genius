#!/usr/bin/env python3
"""Unit tests for exact sparse GF(2) elimination used by the H7 PC probe."""

from __future__ import annotations

from probe_h7_degree_two_pc import SparseGF2Eliminator


def test_consistent_affine_system() -> None:
    system = SparseGF2Eliminator()
    system.add({1, 2}, True)
    system.add({1}, False)
    assert not system.inconsistent
    assert len(system.pivots) == 2


def test_inconsistent_affine_system() -> None:
    system = SparseGF2Eliminator()
    system.add({1}, False)
    system.add({1}, True)
    assert system.inconsistent


def test_dependent_equation() -> None:
    system = SparseGF2Eliminator()
    system.add({1, 2}, True)
    system.add({2, 3}, False)
    system.add({1, 3}, True)
    assert not system.inconsistent
    assert len(system.pivots) == 2


if __name__ == "__main__":
    test_consistent_affine_system()
    test_inconsistent_affine_system()
    test_dependent_equation()
    print("ok")
