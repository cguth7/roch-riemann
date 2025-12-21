# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries
**Phase**: 3 - Serre Duality
**Cycle**: 220 (IN PROGRESS)

### Active Sorries (5 in RatFuncPairing.lean - needs cleanup!)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 5 | HIGH | Step 3 counting arg has 4 sub-sorries - NEEDS REVERT |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

**⚠️ WARNING**: Cycle 220 introduced 4 new sorries (lines 2939, 2942, 2952, 2961).
Next session should either complete these or revert to single sorry at ~2933.

---

## Cycle 220 Progress (IN PROGRESS)

**Goal**: Complete Step 3 counting argument

**Completed this session**:
1. ✅ Built proof structure from line 2670 to ~2970
2. ✅ Proved key intermediate facts:
   - `hv_neg_linear`: v_neg = linearPlace β (using IsLinearPlaceSupport)
   - `hzero_mult`: num.rootMultiplicity β ≥ |D(linearPlace β)|
   - `hα_root`: α is a root of denom (from Step 2's v_π = linearPlace α)
   - `hαβ_ne`: α ≠ β (D(α) > 0 but D(β) < 0)
   - `hβ_mult_le_deg`: num.rootMultiplicity β ≤ num.natDegree
   - `hneg_D_le_num`: -D(linearPlace β) ≤ num.natDegree
3. ✅ Set up final contradiction structure with calc chain

**Remaining sorries** (lines 2939, 2942, 2952, 2961):
1. `hdeg_split`: deg(D) = pos_sum - neg_abs_sum (sum decomposition)
2. `hsum_ineq`: pos_sum < neg_abs_sum (from hdeg_split and deg < 0)
3. `hpos_ge_denom`: pos_sum ≥ denom.natDegree (HARD - needs denom.Splits)
4. `hneg_le_num`: neg_abs_sum ≤ num.natDegree (sum over negative places)

**Key blocker**: `hpos_ge_denom` requires proving denom splits over Fq.
The Step 2 argument shows any ONE irreducible factor is linear, but
needs generalization to ALL factors to conclude denom.Splits.

---

## Cycle 219 Progress (COMPLETED)

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

## Next Steps (Cycle 221)

### OPTION A: Complete the 4 remaining sorries

Current proof structure at RatFuncPairing.lean:2925-2971 has 4 sorries:

1. **hdeg_split** (line 2939): `D.deg = pos_sum - neg_abs_sum`
   - Straightforward sum decomposition over Finsupp
   - Use `Finset.sum_filter_add_sum_filter_not`

2. **hsum_ineq** (line 2942): `pos_sum < neg_abs_sum`
   - Follows from hdeg_split and `hD : D.deg < 0`
   - Should be `omega` after hdeg_split

3. **hpos_ge_denom** (line 2952): `pos_sum ≥ denom.natDegree`
   - **HARD**: Requires proving denom.Splits over Fq
   - Step 2 shows ONE irreducible factor is linear
   - Need to generalize: ∀ π, Irreducible π → π ∣ denom → ∃ α, π = X - C α
   - Then use `Polynomial.splits_iff_card_roots`

4. **hneg_le_num** (line 2961): `neg_abs_sum ≤ num.natDegree`
   - Sum `zero_multiplicity_ge_neg_D` over all negative places
   - Use that different places give different roots (linearPlace injective)
   - Then sum of rootMultiplicities ≤ natDegree

### OPTION B: Revert and try simpler approach

Revert to single sorry (pre-Cycle 220 state) and try:
1. Extract `irreducible_factor_is_linear` as ≤15 line helper lemma
2. Use to prove `denom.Splits` directly
3. Then sum argument is cleaner

### Key Mathlib lemmas for sum approach:
- `Polynomial.splits_iff_card_roots`: p.Splits ↔ p.roots.card = p.natDegree
- `Polynomial.count_roots`: p.roots.count a = rootMultiplicity a p
- `Finset.sum_le_sum`: monotone function gives sum inequality
- `Multiset.count_le_card`: count of element ≤ total card

### CRITICAL: Frontier Freeze Rule
Current state has 5 sorries (was 1). Either complete all 4 new ones
or revert to single sorry. Do NOT add more sorries!

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
