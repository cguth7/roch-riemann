# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries
**Phase**: 3 - Serre Duality
**Cycle**: 219 (IN PROGRESS)

### Active Sorries (1 in RatFuncPairing.lean)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 1 | HIGH | `projective_LRatFunc_eq_zero_of_neg_deg` Step 3 |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

---

## Cycle 219 Progress (IN PROGRESS)

**Goal**: Complete Step 3 of `projective_LRatFunc_eq_zero_of_neg_deg`

**Completed**:
1. ✅ **PROVED `not_isRoot_of_coprime_isRoot`** (helper lemma)
   - Location: RatFuncPairing.lean:2341-2358
   - Shows coprime polynomials cannot share a common root

2. ✅ **PROVED `pole_multiplicity_le_D`** (Lemma 1 from plan)
   - Location: RatFuncPairing.lean:2360-2420
   - At pole α: `rootMult(α, denom) ≤ D(linearPlace α)`
   - Uses bridge lemma + coprimality argument

3. ✅ **PROVED `zero_multiplicity_ge_neg_D`** (Lemma 3 from plan)
   - Location: RatFuncPairing.lean:2422-2481
   - At D < 0 place β: `rootMult(β, num) ≥ |D(linearPlace β)|`
   - Key insight: if β were a root of denom, D would be positive (contradicts D < 0)

**Remaining** (sorry at line ~2700):
- Need to derive final contradiction using the helper lemmas
- Strategy: Sum inequalities show num.natDegree > denom.natDegree, contradicting noPoleAtInfinity

---

## Next Steps (Cycle 220)

### GOAL: Complete the contradiction in Step 3

**Location**: `RatFuncPairing.lean:2700` (single sorry)

**Available facts at sorry location**:
- `hdenom_pos : 0 < f.denom.natDegree`
- `hf_nopole : f.num.natDegree ≤ f.denom.natDegree`
- `hD : D.deg < 0`
- `hDlin : IsLinearPlaceSupport D`
- `hf_val : ∀ v, v.valuation f ≤ exp(D v)` (from L(D) membership)
- All irreducible factors of denom are linear (from Step 2)

**Contradiction strategy**:
```
(A) Σ_{roots α of denom} rootMult(α) = denom.natDegree  [denom splits]
(B) For each root α: D(linearPlace α) ≥ rootMult(α)     [pole_multiplicity_le_D]
(C) So: Σ_{D>0} D(v) ≥ denom.natDegree

(D) For each β with D(linearPlace β) < 0:
    rootMult(β, num) ≥ |D(linearPlace β)|              [zero_multiplicity_ge_neg_D]
(E) So: Σ_{D<0} |D(v)| ≤ Σ rootMult(num) ≤ num.natDegree

(F) From deg(D) < 0: Σ_{D>0} D < Σ_{D<0} |D|

Combining: denom.natDegree ≤ Σ_{D>0} < Σ_{D<0} ≤ num.natDegree
⟹ denom.natDegree < num.natDegree
⟹ Contradiction with hf_nopole!
```

**Two approaches**:
1. **Sum lemmas approach**: Define explicit Finsupp sums and prove inequalities
2. **Direct approach**: Avoid sums, work with specific roots/places

**Recommended approach**: Try direct proof first using `exists_neg_of_deg_neg` to get a specific β with D(β) < 0, then use `zero_multiplicity_ge_neg_D` to show num has zeros. The tricky part is connecting the sum of multiplicities to natDegree.

**Key Mathlib lemmas needed**:
- `Polynomial.natDegree_eq_card_roots` (when polynomial splits)
- `Polynomial.splits_iff_card_roots`
- `Polynomial.count_roots` relates multiset count to rootMultiplicity
- Sum over multiset: `Multiset.card_eq_sum_ones`, `Finset.sum_le_sum`

---

## Critical Path

```
RatFuncPairing.lean: projective_LRatFunc_eq_zero_of_neg_deg
    ├─→ smul_mem' ✅ DONE (Cycle 212)
    ├─→ add_mem' ✅ DONE (Cycle 213)
    ├─→ constant_mem_projective_zero ✅ DONE (Cycle 213)
    ├─→ constant case ✅ DONE (Cycle 214)
    ├─→ IsLinearPlaceSupport assumption ✅ ADDED (Cycle 216)
    ├─→ non-constant Step 1 (denom positive degree) ✅ DONE (Cycle 216)
    ├─→ non-constant Step 2 (poles at linear places) ✅ DONE (Cycle 217)
    ├─→ intValuation_linearPlace_eq_exp_neg_rootMultiplicity ✅ DONE (Cycle 218)
    ├─→ not_isRoot_of_coprime_isRoot ✅ DONE (Cycle 219)
    ├─→ pole_multiplicity_le_D ✅ DONE (Cycle 219)
    ├─→ zero_multiplicity_ge_neg_D ✅ DONE (Cycle 219)
    └─→ non-constant Step 3 (final contradiction) ← NEXT (Cycle 220)
        └─→ L_proj(D) = {0} when deg(D) < 0
            └─→ Serre duality RHS verified
```

---

## Cycle 218 Progress (COMPLETED)

**Goal**: Prove the bridge lemma connecting valuation to rootMultiplicity

**Completed**:
1. ✅ **PROVED `intValuation_linearPlace_eq_exp_neg_rootMultiplicity`**
   - Location: RatFuncPairing.lean:2283
   - Key insight: Use `Ideal.count_associates_eq` with `exists_eq_pow_rootMultiplicity_mul_and_not_dvd`
   - This bridges valuation theory to polynomial algebra

**Lesson learned**: After proving the bridge lemma, attempted a 159-line "counting argument" inline that got stuck on type errors. Reverted to clean sorry with documented plan. Don't overreach after a win.

---

## Cycle 217 Progress

**Completed**:
1. ✅ **Proved Step 2 completely**: Irreducible factors of denom give poles at linear places
   - For any irreducible factor π | denom, constructed place v_π with asIdeal = span{π}
   - Proved v_π.intValuation(denom) < 1 (π ∈ v_π.asIdeal)
   - Proved v_π.intValuation(num) = 1 (coprimality: π ∤ num)
   - Therefore valuation(f) = val(num)/val(denom) > 1 (f has pole at v_π)
   - From L(D) membership: valuation(f) ≤ exp(D(v_π)), so exp(D(v_π)) > 1
   - Therefore D(v_π) > 0, so v_π ∈ D.support
   - By IsLinearPlaceSupport: v_π is a linear place
   - Conclusion: all irreducible factors of denom are linear (X - α)

---

## Cycle 216 Progress

**Completed**:
1. ✅ **Added `IsLinearPlaceSupport D` assumption** to `projective_LRatFunc_eq_zero_of_neg_deg` and downstream theorems
2. ✅ **Proved Step 1 completely**: For non-constant f with noPoleAtInfinity, denom has positive degree

**Key insight on IsLinearPlaceSupport**:
The theorem as originally stated (without IsLinearPlaceSupport) is actually FALSE for general divisors.

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
