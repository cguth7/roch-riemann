# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Compiles (with 1 sorry in DimensionCore + 1 in DimensionScratch)
**Phase**: 3 - Serre Duality → Dimension Formula
**Cycle**: 240

---

## Cycle 240 Summary - `denom_is_power_of_X_sub` IN PROGRESS

**Goal**: Fill `denom_is_power_of_X_sub` (the last sorry in DimensionCore.lean)

**What was accomplished**:
- ✅ Added helper lemmas (all compile):
  - `RRSpace_valuation_le_one_at_other_places` - valuation ≤ 1 at places ≠ linearPlace α
  - `valuation_gt_one_at_other_irreducible` - if π | denom with π ≠ (X-α), then val > 1
  - `irreducible_place_ne_linearPlace` - place from π not associate to (X-α) is ≠ linearPlace α
  - `irreducible_factor_not_assoc_of_not_dvd` - if (X-α) ∤ R and π | R, then π not associate to (X-α)
- ✅ Step 1-2 of main proof COMPLETE: Factor denom, show cofactor R has degree 0

**What remains** (Steps 3-4):
1. **Step 3**: Show R = 1 (R is constant, denom is monic → R = 1)
   - Issue: `rw` patterns not matching due to `let denom := f.denom` scoping
   - Fix: Use `have hdenom_eq' : denom = (X-α)^m * C c` then substitute

2. **Step 4**: Show m ≤ n from valuation bound
   - Issue: Need `Polynomial.rootMultiplicity_X_sub_C_pow` or similar (name may differ)
   - The lemma should say: `rootMultiplicity α ((X - C α)^m) = m`
   - Search Mathlib for correct name

**Key insight from this cycle**: The "Extract and Conquer" pattern from Cycle 238 applies here too. Build intermediate `have` statements with explicit types rather than doing rewrites in-place.

**Proof structure that works (Steps 1-2)**:
```lean
-- Factor denom = (X-α)^m * R
obtain ⟨R, hdenom_factor, hR_not_dvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd ...

-- Show R.natDegree = 0 by contradiction
have hR_deg_zero : R.natDegree = 0 := by
  by_contra hR_pos'
  -- Get irreducible factor π of R
  obtain ⟨π, hπ_irr, hπ_dvd_R⟩ := Polynomial.exists_irreducible_of_natDegree_pos ...
  -- π not associate to (X-α) since (X-α) ∤ R
  have hπ_not_assoc := irreducible_factor_not_assoc_of_not_dvd ...
  -- At place v_π: valuation(f) > 1
  have hval_gt := valuation_gt_one_at_other_irreducible ...
  -- But RRSpace says valuation ≤ 1
  have hval_le := RRSpace_valuation_le_one_at_other_places ...
  exact not_lt.mpr hval_le hval_gt
```

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

## Honest Sorry Audit (Cycle 239)

### CRITICAL PATH FOR P¹ (2 sorries total - down from 6!)

**DimensionCore.lean** (1 sorry):
```
Line 61:  denom_is_power_of_X_sub           - KEY LEMMA: denom = (X-α)^m with m ≤ n
```

**DimensionScratch.lean** (1 sorry):
```
Line 836: ell_ratfunc_projective_eq_deg_plus_one - main theorem (strong induction)
```

### What's NOW PROVED (Cycles 238-239):
- ✅ `partialClearPolesFun_spec` - the key algebraic equation
- ✅ `partialClearPoles` (full LinearMap) - linearity via spec
- ✅ `partialClearPoles_injective` - injectivity via spec
- ✅ `RRSpace_ratfunc_projective_single_linear_finite` - finiteness (uses injective embedding)
- ✅ `RRSpace_ratfunc_projective_add_single_finite` - finiteness for D + [α] (Cycle 239)
- ✅ `RRSpace_ratfunc_projective_mono` - monotonicity L(D) ⊆ L(D+[α])
- ✅ `linearPlace_residue_finrank` - dim_Fq(κ(v)) = 1 for linear places

### Dependency Graph (updated Cycle 239)

```
riemann_roch_ratfunc (NOT PROVED)
    ├─→ ell_ratfunc_projective_eq_deg_plus_one (1 sorry - MAIN BLOCKER)
    │       ├─→ ell_ratfunc_projective_single_linear ✅ PROVED (modulo denom_is_power_of_X_sub)
    │       │       ├─→ RRSpace_single_linear_finite ✅ (needs denom_is_power_of_X_sub)
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

REMAINING SORRIES: 2 (both on critical path)
1. denom_is_power_of_X_sub (DimensionCore.lean:61)
2. ell_ratfunc_projective_eq_deg_plus_one (DimensionScratch.lean:836)
```

---

## Next Steps for Future Claude (Cycle 241)

### Priority 1: Complete `denom_is_power_of_X_sub` (Line 148) - Steps 3-4

**Current state**: Steps 1-2 are DONE (helper lemmas + R.natDegree = 0). Steps 3-4 remain.

**Step 3: Show R = 1** (R is constant, denom is monic)
```lean
have hR_const : R = 1 := by
  rw [Polynomial.natDegree_eq_zero] at hR_deg_zero
  obtain ⟨c, hR_eq⟩ := hR_deg_zero  -- R = C c
  -- Build explicit equation: denom = (X-α)^m * C c
  have hdenom_eq' : denom = (Polynomial.X - Polynomial.C α) ^ m * Polynomial.C c := by
    rw [hdenom_factor, hR_eq]
  -- leadingCoeff((X-α)^m * C c) = c (use leadingCoeff_mul')
  -- denom.Monic means leadingCoeff = 1, so c = 1
  -- Therefore R = C 1 = 1
```

**Step 4: Show m ≤ n** (valuation bound)
```lean
-- Key: find the correct name for rootMultiplicity((X-α)^m, α) = m
-- Try: Polynomial.rootMultiplicity_pow, Polynomial.rootMultiplicity_self_pow, etc.
-- Then use intValuation_linearPlace_eq_exp_neg_rootMultiplicity
```

**Gotchas encountered**:
- `let denom := f.denom` creates scoping issues with `rw`
- Solution: Build intermediate `have` statements with explicit types
- The `rootMultiplicity_pow_X_sub_C` name may not exist - search Mathlib

### ~~Priority 2: `RRSpace_ratfunc_projective_add_single_finite`~~ ✅ COMPLETED (Cycle 239)

Used `Module.Finite.of_submodule_quotient` with:
- N = comap of L(D) in L(D+[α]) (finite by hypothesis via `comap_equiv_self_of_inj_of_le`)
- Quotient embeds into κ(α) with dimension 1 (finite via `Module.Finite.of_injective`)

### Priority 2 (was 3): `ell_ratfunc_projective_eq_deg_plus_one` (DimensionScratch.lean line 836)

Strong induction on `deg(D)`. Once `denom_is_power_of_X_sub` is filled, this should "just work"
since all the finiteness instances are now in place.

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
