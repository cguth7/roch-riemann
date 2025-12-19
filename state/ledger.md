# Ledger Vol. 3.3 (Cycles 133+) - Full Adeles Compactness

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*
*For Cycles 80-99, see `state/ledger_archive.md` (Vol. 3.1)*
*For Cycles 100-117, see `state/ledger_archive.md` (Vol. 3.2 Part 1 - AllIntegersCompact)*
*For Cycles 118-132, see `state/ledger_archive.md` (Vol. 3.2 Part 2 - FullAdeles Foundation)*

---

## 🎯 NEXT CLAUDE: Start Here (Cycle 134)

### What's Done
- ✅ `fq_discrete_in_fullAdeles` - K is discrete in full adeles
- ✅ `fq_closed_in_fullAdeles` - K is closed in full adeles
- ✅ Finite adeles compactness - via `RestrictedProduct.range_structureMap`

### What's Needed (2 sorries remain)

**1. `isCompact_integralFullAdeles` - Infinity component sorry**

The finite adeles part is DONE. Need to prove `IsCompact {x : FqtInfty Fq | Valued.v x ≤ 1}`.

**Blocking issue from Cycle 133**: ℝ≥0 literal proofs fail.
- `(2 : ℝ≥0) ≠ 0` and `(1 : ℝ≥0) < 2` don't work with `norm_num` or `native_decide`
- **FIX**: Use coercion trick: `NNReal.coe_lt_coe.mp (by norm_num : (1:ℝ) < 2)`

**Proof strategy** (documented in `FullAdeles.lean` line 687-718):
```lean
-- 1. RankOne instance (needs ℝ≥0 literal fix)
instance instRankOneFqtInfty : Valuation.RankOne (Valued.v (R := FqtInfty Fq)) where
  toIsNontrivial := inftyValuation_isNontrivial Fq  -- v(X) = exp(1) ≠ 0,1
  hom := WithZeroMulInt.toNNReal h2                  -- h2 : (2 : ℝ≥0) ≠ 0
  strictMono' := WithZeroMulInt.toNNReal_strictMono h1  -- h1 : (1 : ℝ≥0) < 2

-- 2. Apply compactSpace_iff (same pattern as AllIntegersCompactProof.lean)
-- Needs: CompleteSpace (closed in complete), DVR (value group ℤ), Finite residue (≅ Fq)
Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField

-- 3. Convert CompactSpace → IsCompact via continuous_subtype_val
```

**2. `exists_translate_in_integralFullAdeles` - Weak approximation**
- For any adele a, find x ∈ K such that a - diag(x) is integral
- Standard weak approximation for PIDs

### Key Files
| File | What's there |
|------|--------------|
| `FullAdeles.lean` | Main theorems, 2 sorries at lines ~727 and ~788 |
| `AllIntegersCompactProof.lean` | Pattern to follow for infinity compactness |
| `FqPolynomialInstance.lean` | Concrete Fq[X] instances |

### Key Mathlib APIs
| What | Lemma |
|------|-------|
| Integer = {v ≤ 1} | `Valuation.mem_integer_iff` |
| CompactSpace ↔ complete+DVR+finite | `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField` |
| ℤᵐ⁰ → ℝ≥0 embedding | `WithZeroMulInt.toNNReal`, `WithZeroMulInt.toNNReal_strictMono` |
| Closed subset complete | `IsClosed.completeSpace_coe` |

---

## Sorry Status

| File | Item | Status |
|------|------|--------|
| `FullAdeles.lean` | `isCompact_integralFullAdeles` | 🔶 Infinity sorry (finite DONE) |
| `FullAdeles.lean` | `exists_translate_in_integralFullAdeles` | ⚪ Sorry |
| `TraceDualityProof.lean` | `finrank_dual_eq` | ⚪ Not critical path |
| `FqPolynomialInstance.lean` | `discrete_diagonal_embedding` | ❌ FALSE (finite adeles only) |

**Build**: ✅ Compiles with 2 sorries in FullAdeles.lean

---

## Cycle 133 Summary

**Goal**: Complete infinity compactness for `isCompact_integralFullAdeles`

**Status**: 🔶 PARTIAL - Structure complete, blocked on ℝ≥0 tactics

**Progress**:
- Added imports for `WithZeroMulInt.toNNReal` and `LocallyCompact`
- Wrote full proof strategy in code comments
- Identified blocking issue: ℝ≥0 literals

**Next**: Fix ℝ≥0 proofs, complete RankOne instance, finish compactness

---

## Architecture Summary

```
FullAdeleRing Fq := FiniteAdeleRing Fq[X] (RatFunc Fq) × FqtInfty Fq

K = RatFunc Fq embeds diagonally:
  fqFullDiagonalEmbedding : K →+* FullAdeleRing

Key theorems (in FullAdeles.lean):
  ✅ fq_discrete_in_fullAdeles  -- K is discrete
  ✅ fq_closed_in_fullAdeles    -- K is closed
  🔶 isCompact_integralFullAdeles  -- integral adeles compact
  ⚪ exists_translate_in_integralFullAdeles  -- weak approximation
```

---

## References

- `AllIntegersCompactProof.lean` - Pattern for compactness via DVR+complete+finite
- `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean` - compactSpace_iff lemma
- `Mathlib/Data/Int/WithZero.lean` - WithZeroMulInt.toNNReal
