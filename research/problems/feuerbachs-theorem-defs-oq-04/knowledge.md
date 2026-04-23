# Knowledge: Feuerbach's Theorem — Mathlib Affine Geometry Framework

**Problem**: feuerbachs-theorem-defs-oq-04
**Knowledge Tier**: EMPTY (0 research findings yet)
**Created**: 2026-04-23

## Mathematical Background

### Core Problem

Bridge the existing custom-coordinate Feuerbach formalization to Mathlib's abstract
`EuclideanSpace ℝ (Fin 2)` framework. The key deliverable is a `toEuclidean` conversion
and sphere-based tangency statement.

### Key Mathlib Infrastructure

- `Mathlib.Geometry.Euclidean.Sphere.Basic` — `Sphere` type with `center : E`, `radius : ℝ`
- `Mathlib.Geometry.Euclidean.Circumcenter` — circumcenter/circumradius in `EuclideanSpace`
- `EuclideanSpace ℝ (Fin 2)` — abstract 2D plane with inner product

### Existing Gallery Infrastructure

- `FeuerbachsTheoremDefs.lean` — custom `Point = ℝ × ℝ`, `dist2`, `Triangle`
- `FeuerbachsTheoremOQ01.lean` — main tangency results using custom API

## Research Log

*(Empty — problem selected 2026-04-23, no OODA cycles completed yet)*
