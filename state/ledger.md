# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles
**P¹ Riemann-Roch**: ✅ **COMPLETE** (sorry-free)
**Phase**: 3 - Serre Duality → Dimension Formula
**Cycle**: 241

---

## Cycle 241 Summary - P¹ RIEMANN-ROCH COMPLETE!

**Goal**: Fill the last sorry in `ell_ratfunc_projective_eq_deg_plus_one`

**What was accomplished**:
- ✅ `ell_ratfunc_projective_eq_deg_plus_one` - FULLY PROVED!
- ✅ DimensionScratch.lean is now SORRY-FREE (for P¹ critical path)
- ✅ P¹ Riemann-Roch theorem chain complete with no `sorryAx`

**Fixes applied**:
1. Line 918-921: Changed `add_le_add_left` proof to use `linarith` with explicit sum non-negativity
2. Line 917: Added `simp only [Finsupp.sum]` before rewrite to unfold Finsupp.sum to Finset.sum
3. Lines 842-856: Replaced circular proof with direct calc-based proof showing D effective with D(v) > 0 implies deg(D) > 0

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# No output = no sorries in proof chain

# Axioms used (all standard mathlib):
# 'RiemannRochV2.ell_ratfunc_projective_eq_deg_plus_one' depends on axioms:
#   [propext, Classical.choice, Quot.sound]
```

---

## P¹ Riemann-Roch Theorem (PROVED)

```lean
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1
```

For effective divisors D with linear support on P¹(Fq), the dimension of the Riemann-Roch space equals deg(D) + 1.

---

## Sorries

**0 sorries in main codebase.**

6 sorried lemmas moved to `RrLean/Archive/SorriedLemmas.lean`:
- `LRatFunc_eq_zero_of_neg_deg` + dependents (RatFuncPairing.lean)
- `residueAtIrreducible` + `residue_sum_eq_zero` (Residue.lean)
- `principal_divisor_degree_eq_zero_INCORRECT` (ProductFormula.lean)
- `finrank_dual_eq` (TraceDualityProof.lean)

The `exists_finite_integral_translate_with_infty_bound` sorry was eliminated by adding `1 ≤ bound` hypothesis (all callers use bound=1).

---

## Build Commands

```bash
# Full smoke test (verify no sorryAx)
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"

# Build specific module
lake build RrLean.RiemannRochV2.SerreDuality.DimensionScratch

# Check axioms
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "depends on axioms"
```

---

*For historical cycles 1-240, see `ledger_archive.md`*
