# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Compiles (0 sorries in DimensionCore, 1 in DimensionScratch)
**Phase**: 3 - Serre Duality → Dimension Formula
**Cycle**: 241

---

## Cycle 240 Summary - `denom_is_power_of_X_sub` COMPLETED

**Goal**: Fill `denom_is_power_of_X_sub` (the last sorry in DimensionCore.lean)

**What was accomplished**:
- ✅ `denom_is_power_of_X_sub` - FULLY PROVED!
- ✅ DimensionCore.lean is now SORRY-FREE

**Proof structure** (all 4 steps complete):
1. **Step 1-2** (from previous cycle): Factor denom = (X-α)^m * R, show R.natDegree = 0
2. **Step 3**: Show R = 1 using monic leading coefficient
   - Key: `Polynomial.leadingCoeff_mul'` + `Polynomial.natDegree_eq_zero`
   - Since denom is monic, leadingCoeff = 1, and R = C c for constant c, we get c = 1
3. **Step 4**: Show m ≤ n from valuation bound
   - Key: `Polynomial.rootMultiplicity_X_sub_C_pow α m = m`
   - Used coprimality to show (X-α) ∤ num, hence v(num) = 1
   - v(f) = exp(m) ≤ exp(n) from RRSpace membership, so m ≤ n

**Sorries reduced**: 1 → 0 in DimensionCore.lean

**Key APIs used**:
- `Polynomial.leadingCoeff_mul'` - for computing leadingCoeff of product
- `Polynomial.rootMultiplicity_X_sub_C_pow` - rootMultiplicity((X-α)^m, α) = m
- `intValuation_linearPlace_eq_exp_neg_rootMultiplicity` - bridge to valuations
- `IsCoprime.dvd_add` pattern for coprimality contradiction

**Critical path update**: Only 1 sorry remains on P¹ critical path!
- DimensionCore.lean: 0 sorries (was 1)
- DimensionScratch.lean: 1 sorry (`ell_ratfunc_projective_eq_deg_plus_one`)

---

## Cycle 239 Summary - Priority 2 COMPLETED

**Goal**: Fill `RRSpace_ratfunc_projective_add_single_finite` (Priority 2 sorry)

**What was accomplished**:
- ✅ `RRSpace_ratfunc_projective_add_single_finite` - PROVED!

**Sorries reduced**: 2 → 1 in DimensionCore.lean

**Key technique**: Used `Module.Finite.of_submodule_quotient`:
1. View L(D) as submodule LD of L(D+[α]) via comap
2. Show LD ≅ L(D) (hence finite by hypothesis) via `Submodule.comap_equiv_self_of_inj_of_le`
3. Show quotient L(D+[α])/LD is finite (injects into κ(α) with dim 1)
4. Apply `Module.Finite.of_submodule_quotient`

**Refactoring**: Moved `RRSpace_ratfunc_projective_mono` and `linearPlace_residue_finrank`
from DimensionScratch.lean to DimensionCore.lean (needed by add_single_finite proof).

---

## Cycle 238 Summary

**Goal**: Fill "low-hanging fruit" sorries (linearity + injectivity)

**What was accomplished**:
- ✅ `partialClearPoles.map_add'` - PROVED
- ✅ `partialClearPoles.map_smul'` - PROVED
- ✅ `partialClearPoles_injective` - PROVED

**Sorries reduced**: 5 → 2 in DimensionCore.lean

**Key insight**: Refactored using "Extract and Conquer" pattern (see below).

---

## ✅ PATTERN: Extract and Conquer (Cycle 238)

When defining a `LinearMap` with non-trivial properties, DON'T try to prove everything inside the `where` block. This creates "context soup" that confuses Lean's `rw` tactic ("motive is not type correct" errors).

### The Mathlib Way (3 steps):

**Step 1: Define the raw function**
```lean
def partialClearPolesFun (α : Fq) (n : ℕ) (f : RRSpace...) : Polynomial.degreeLT Fq (n+1) := by
  have hpoly := mul_X_sub_pow_is_polynomial ...
  exact ⟨hpoly.choose, ...⟩
```

**Step 2: Prove the specification lemma**
```lean
lemma partialClearPolesFun_spec ... :
    algebraMap _ _ (partialClearPolesFun ...).val = (X-α)^n * f.val := by
  -- Full algebraic proof here
```

**Step 3: Bundle as LinearMap**
```lean
def partialClearPoles ... : ... →ₗ[Fq] ... where
  toFun := partialClearPolesFun α n
  map_add' := by ... rw [partialClearPolesFun_spec, ...]; ring  -- ONE-LINER!
  map_smul' := by ... rw [partialClearPolesFun_spec, ...]; ring  -- ONE-LINER!
```

This eliminates circular dependencies and makes linearity proofs trivial.

---

## Honest Sorry Audit (Cycle 240)

### CRITICAL PATH FOR P¹ (1 sorry total - down from 6!)

**DimensionCore.lean** (0 sorries): ✅ SORRY-FREE!

**DimensionScratch.lean** (1 sorry):
```
Line 836: ell_ratfunc_projective_eq_deg_plus_one - main theorem (strong induction)
```

### What's NOW PROVED (Cycles 238-240):
- ✅ `denom_is_power_of_X_sub` - denom = (X-α)^m with m ≤ n (Cycle 240)
- ✅ `partialClearPolesFun_spec` - the key algebraic equation
- ✅ `partialClearPoles` (full LinearMap) - linearity via spec
- ✅ `partialClearPoles_injective` - injectivity via spec
- ✅ `RRSpace_ratfunc_projective_single_linear_finite` - finiteness (uses injective embedding)
- ✅ `RRSpace_ratfunc_projective_add_single_finite` - finiteness for D + [α] (Cycle 239)
- ✅ `RRSpace_ratfunc_projective_mono` - monotonicity L(D) ⊆ L(D+[α])
- ✅ `linearPlace_residue_finrank` - dim_Fq(κ(v)) = 1 for linear places

### Dependency Graph (updated Cycle 240)

```
riemann_roch_ratfunc (NOT PROVED)
    ├─→ ell_ratfunc_projective_eq_deg_plus_one (1 sorry - ONLY REMAINING BLOCKER)
    │       ├─→ ell_ratfunc_projective_single_linear ✅ PROVED
    │       │       ├─→ RRSpace_single_linear_finite ✅ PROVED
    │       │       │       ├─→ denom_is_power_of_X_sub ✅ PROVED (Cycle 240)
    │       │       │       ├─→ partialClearPoles ✅ PROVED (LinearMap)
    │       │       │       └─→ partialClearPoles_injective ✅ PROVED
    │       │       └─→ ell_ratfunc_projective_gap_le ✅ PROVED
    │       ├─→ RRSpace_add_single_finite ✅ PROVED (Cycle 239)
    │       │       ├─→ RRSpace_ratfunc_projective_mono ✅ PROVED
    │       │       ├─→ linearPlace_residue_finrank ✅ PROVED
    │       │       └─→ kernel_evaluationMapAt_complete_proof ✅ PROVED
    │       ├─→ inv_X_sub_C_pow_mem_projective ✅
    │       └─→ inv_X_sub_C_pow_not_mem_projective_smaller ✅
    └─→ ell_canonical_sub_zero ✅ PROVED

REMAINING SORRIES: 1 (on critical path)
1. ell_ratfunc_projective_eq_deg_plus_one (DimensionScratch.lean:836)
```

---

## Next Steps for Future Claude (Cycle 241)

### Priority 1: Complete `ell_ratfunc_projective_eq_deg_plus_one` (Line 836)

This is the LAST sorry on the P¹ critical path!

**Structure**: Strong induction on deg(D)
- **Base**: D = 0 ⟹ ℓ(0) = 1 = 0 + 1 ✓
- **Step**: Pick v with D(v) > 0, let D' = D - [v]
  - D' effective with deg(D') = deg(D) - 1
  - By IH: ℓ(D') = deg(D') + 1 = deg(D)
  - Gap bound: ℓ(D) ≤ ℓ(D') + 1 = deg(D) + 1
  - Strict inclusion: 1/(X-α)^{D(v)} ∈ L(D) \ L(D')
  - Therefore: ℓ(D) = deg(D) + 1 ✓

**Key ingredients (all proved)**:
- `RRSpace_ratfunc_projective_single_linear_finite` - finiteness for single linear
- `RRSpace_ratfunc_projective_add_single_finite` - finiteness for D + [α]
- `ell_ratfunc_projective_gap_le` - ℓ(D+[v]) ≤ ℓ(D) + 1
- `inv_X_sub_C_pow_mem_projective` - explicit elements in L(D)
- `inv_X_sub_C_pow_not_mem_projective_smaller` - strict inclusion

**Gotchas from previous attempts**:
- Need to handle `IsLinearPlaceSupport` propagation through D → D - [v]

---

## API Lessons (Cycle 237-238)

### APIs that DON'T EXIST (don't use these):
```lean
Irreducible.not_unit           -- use Irreducible.not_isUnit
Associated.normalize_eq        -- not a method
RatFunc.mk_eq_div              -- doesn't exist
```

### APIs that DO work:
```lean
IsFractionRing.injective (Polynomial Fq) (RatFunc Fq)  -- algebraMap injective
RatFunc.num_div_denom f                                -- f = num/denom in RatFunc
Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd  -- factor out (X-α)^m
intValuation_linearPlace_eq_exp_neg_rootMultiplicity   -- valuation ↔ rootMultiplicity
IsScalarTower.algebraMap_apply                         -- normalize algebraMap paths
```

### Useful patterns from this session:
```lean
-- Prove polynomial equality via algebraMap injectivity
apply IsFractionRing.injective (Polynomial Fq) (RatFunc Fq)

-- Lift polynomial equation to RatFunc
have hspec_lifted := congrArg (algebraMap (Polynomial Fq) (RatFunc Fq)) hspec

-- Normalize algebraMap paths
simp only [← IsScalarTower.algebraMap_apply Fq (Polynomial Fq) (RatFunc Fq)]
```

---

## Build Commands

```bash
# Build DimensionCore and check sorries
lake build RrLean.RiemannRochV2.SerreDuality.DimensionCore 2>&1 | grep -E "(error|sorry)"

# Full smoke test
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"

# Count sorries in DimensionCore
grep -n "sorry" RrLean/RiemannRochV2/SerreDuality/DimensionCore.lean | grep -v "^[0-9]*:.*--"
```

---

## Historical Notes

### Cycle 237
- Attempted `denom_is_power_of_X_sub` with 150-line proof, hit API mismatches
- Lesson: Build incrementally, 10-20 lines at a time

### Cycle 236
- Created DimensionCore.lean architecture
- Fixed circular finrank-finiteness anti-pattern
- Added Smoke.lean for build hygiene

### Cycles 233-235
- Circular dependency trap (finrank needs Module.Finite needs finrank)
- See "Anti-Pattern" section in playbook.md

---

*For strategy, see `playbook.md`*
*For historical cycles 1-232, see `ledger_archive.md`*
