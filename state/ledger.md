# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries
**Phase**: 3 - Serre Duality
**Cycle**: 219

### Active Sorries (1 in RatFuncPairing.lean)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 1 | HIGH | `projective_LRatFunc_eq_zero_of_neg_deg` Step 3 |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

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

## Next Steps (Cycle 219)

### GOAL: Complete Step 3 of `projective_LRatFunc_eq_zero_of_neg_deg`

**Location**: `RatFuncPairing.lean:2553` (single sorry)

**Strategy**: Build 4 clean helper lemmas, then combine for contradiction.

### Lemma 1: `pole_multiplicity_le_D`
```lean
lemma pole_multiplicity_le_D (α : Fq) (f : RatFunc Fq) (D : DivisorV2 (Polynomial Fq))
    (hf : f ∈ RRSpace_ratfunc_projective D) (hpole : f.denom.IsRoot α) :
    (f.denom.rootMultiplicity α : ℤ) ≤ D (linearPlace α)
```
**Proof sketch**:
- At pole: v(f) = exp(rootMult(denom,α)) (by bridge lemma + coprimality)
- From L(D): v(f) ≤ exp(D(linearPlace α))
- Therefore rootMult ≤ D

### Lemma 2: `denom_splits_linear` (may already follow from Step 2)
```lean
lemma denom_splits_linear (f : RatFunc Fq) (D : DivisorV2 (Polynomial Fq))
    (hDlin : IsLinearPlaceSupport D) (hf : f ∈ RRSpace_ratfunc_projective D) :
    f.denom.roots.card = f.denom.natDegree
```
**Proof sketch**: All irreducible factors are linear (X - α) by Step 2. Over Fq, linear factors have Fq-roots.

### Lemma 3: `zero_multiplicity_ge_neg_D`
```lean
lemma zero_multiplicity_ge_neg_D (β : Fq) (f : RatFunc Fq) (D : DivisorV2 (Polynomial Fq))
    (hf : f ∈ RRSpace_ratfunc_projective D) (hD_neg : D (linearPlace β) < 0)
    (hDlin : IsLinearPlaceSupport D) :
    (f.num.rootMultiplicity β : ℤ) ≥ -D (linearPlace β)
```
**Proof sketch**:
- At D < 0 place: v(f) ≤ exp(D) < 1
- By bridge lemma: v(f) = exp(rootMult(denom,β) - rootMult(num,β))
- Poles have D > 0, so β is not a pole, so rootMult(denom,β) = 0
- Therefore -rootMult(num,β) ≤ D, i.e., rootMult(num,β) ≥ |D|

### Lemma 4: `sum_inequality`
```lean
lemma sum_pos_ge_denom_deg (f : RatFunc Fq) (D : DivisorV2 (Polynomial Fq)) ... :
    (D.support.filter (D · > 0)).sum D ≥ f.denom.natDegree

lemma sum_neg_le_num_deg (f : RatFunc Fq) (D : DivisorV2 (Polynomial Fq)) ... :
    (D.support.filter (D · < 0)).sum (fun v => -D v) ≤ f.num.natDegree
```

### Final contradiction
```
deg(D) < 0
⟹ Σ_{D<0} |D| > Σ_{D>0} D           (algebra)
⟹ Σ_{D<0} |D| > denom.natDegree     (Lemma 4a)
⟹ num.natDegree > denom.natDegree   (Lemma 4b)
⟹ contradiction with noPoleAtInfinity
```

**DO NOT**:
- Build all 4 lemmas inline in the main theorem
- Use roots.count when factorization support is cleaner
- Add more than one sorry at a time

**Success criterion**: The single sorry in `projective_LRatFunc_eq_zero_of_neg_deg` becomes Qed.

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
    └─→ non-constant Step 3 (counting argument) ← NEXT (Cycle 219)
        ├─→ pole_multiplicity_le_D
        ├─→ denom_splits_linear
        ├─→ zero_multiplicity_ge_neg_D
        └─→ sum_inequality → contradiction
            └─→ L_proj(D) = {0} when deg(D) < 0
                └─→ Serre duality RHS verified
```

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
