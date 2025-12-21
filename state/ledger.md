# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries
**Phase**: 3 - Serre Duality
**Cycle**: 213

### Active Sorries (2 in RatFuncPairing.lean)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 2 | HIGH | `LRatFunc_eq_zero_of_neg_deg`, `projective_LRatFunc_eq_zero_of_neg_deg` |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

---

## Cycle 213 Progress

**Completed**:
1. ✅ **Proved `add_mem'`** for `RRSpace_ratfunc_projective`
2. ✅ **Proved `constant_mem_projective_zero`**

**Key implementation details for `add_mem'`**:
- Used `RatFunc.intDegree_add_le` which shows `intDegree (x + y) ≤ max (intDegree x) (intDegree y)`
- `noPoleAtInfinity f` is equivalent to `intDegree f ≤ 0`
- Careful case analysis for zero cases before applying the lemma
- Pattern: `by_cases hab : a + b = 0` first, then `by_cases ha_ne : a = 0`, etc.

**Key implementation details for `constant_mem_projective_zero`**:
- Finite places: `v.valuation (RatFunc.C c) = 1` via `intValuation_eq_one_iff` (C c not in v.asIdeal)
- Infinity: `RatFunc.num_C`, `RatFunc.denom_C` give degree 0 for both

---

## Next Steps (Cycle 214)

### 1. Tackle `projective_LRatFunc_eq_zero_of_neg_deg` (line ~2240)

Main vanishing theorem showing L_proj(D) = {0} when deg(D) < 0.

**Mathematical argument** (from comments in file):
1. At finite places v: ord_v(f) ≥ -D(v) (from membership in L(D))
2. At infinity: ord_∞(f) = deg(denom) - deg(num) ≥ 0 (from noPoleAtInfinity)
3. Product formula: Σ_{all v} deg(v) * ord_v(f) + ord_∞(f) = 0
4. Contradiction: deg(D) + (sum of orders) ≥ 0 from effectiveness, but < 0 from assumption

**Key insight from ProductFormula.lean**:
- The naive Fq-rational product formula is FALSE (counterexample: 1/(X²+X+1) over F₂)
- Must use degree-weighted sum over ALL irreducible polynomials
- Formula: `Σ_P deg(P) * ord_P(f) + ord_∞(f) = 0` from unique factorization

**Approach options**:
1. Direct unique factorization argument using `UniqueFactorizationMonoid` API
2. Use that for f = p/q coprime: `deg(p) = Σ_P deg(P) * mult(P, p)`, similarly for q

### 2. Alternative: Prove `LRatFunc_eq_zero_of_neg_deg` (line ~1896)

This is the affine version (without infinity constraint). Same product formula needed.

---

## Critical Path

```
RatFuncPairing.lean: projective_LRatFunc_eq_zero_of_neg_deg
    ├─→ smul_mem' ✅ DONE (Cycle 212)
    ├─→ add_mem' ✅ DONE (Cycle 213)
    ├─→ constant_mem_projective_zero ✅ DONE (Cycle 213)
    └─→ L_proj(D) = {0} when deg(D) < 0 ← NEXT
        └─→ Serre duality RHS verified
```

---

## Quick Commands

```bash
# Build
lake build 2>&1 | tail -5

# Find sorries
grep -rn "sorry" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean

# Count sorries
grep -rn "sorry" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean | wc -l
```

---

*For strategy, see `playbook.md`*
*For historical cycles 1-211, see `ledger_archive.md`*
