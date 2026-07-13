# Problem: Gauss AGM Theorem M(a,b) = aπ/(2K(k'))

**Slug**: amgm-inequality-oq-04-oq-03
**Created**: 2026-04-04T02:46:36-07:00
**Status**: Active
**Source**: amgm-inequality-oq-04 <!-- gallery-gap -->

## Problem Statement

Prove Gauss's AGM theorem: M(a,b) = aπ/(2K(k')) where k' = √(1-k²), k = b/a, 
via the hypergeometric series identity K(k) = (π/2)·₂F₁(1/2,1/2;1;k²).

This connects the AGM limit to the complete elliptic integral K.

## Context

- Source: `amgm-inequality-oq-04` (Gauss AGM Iteration and Elliptic Integrals)  
- Category: extension (analysis, deep)
- Tractability: challenging (requires hypergeometric functions and AGM convergence)

## First Steps

1. Check existing AGM formalization in gallery (amgm-inequality-oq-04)
2. Look for Mathlib hypergeometric series support
3. Try proving just the AGM convergence rate first
