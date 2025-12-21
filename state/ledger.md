# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Compiles (with sorries)
**Phase**: 3 - Serre Duality → Dimension Formula
**Cycle**: 234

---

## Cycle 234 Progress

**Goal**: Fix DimensionScratch.lean sorries to complete Riemann-Roch

### Sorries Fixed This Cycle

1. ✅ **`linearPlace_residue_finrank`** (lines 95-121)
   - `Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) (linearPlace α)) = 1`
   - **Solution**: Used `AlgEquiv.ofRingEquiv` to upgrade `RingEquiv.ofBijective` to AlgEquiv
   - Key insight: `rfl` works for algebra map compatibility because definitions align

2. ✅ **`ell_ratfunc_projective_gap_le`** (lines 135-281)
   - Gap bound: `ℓ(D + [v]) ≤ ℓ(D) + 1` for linear places
   - **Added hypothesis**: `[Module.Finite Fq (RRSpace_ratfunc_projective (D + ...))]`
   - Proof constructs Fq-linear eval map ψ, shows ker(ψ) = L(D), uses quotient bound

### Sorries Remaining (2)

| Lemma | Line | Status | Notes |
|-------|------|--------|-------|
| `ell_ratfunc_projective_single_linear` | ~624 | **IN PROGRESS** | Finiteness/type issues |
| `ell_ratfunc_projective_eq_deg_plus_one` | ~876 | sorry | MAIN THEOREM |

### Current Blocker: `ell_ratfunc_projective_single_linear`

**Goal**: Prove `ℓ(n·[linearPlace α]) = n + 1`

**Proof structure** (induction on n):
- Base: `ℓ(0) = 1` ✅ (uses `ell_ratfunc_projective_zero_eq_one`)
- Step: Uses gap bound + strict inclusion to show `ℓ((m+1)·[v]) = m+2`

**Current errors** (~8 type mismatches):
1. `Module.finite_of_finrank_pos` argument type mismatch at line 641
2. `Module.finrank_pos_iff` instance synthesis failure at line 653
3. Gap bound `convert` type mismatch at line 664
4. `Submodule.finrank_mono` instance issues at lines 699, 701
5. Final `omega` can't close at line 705

**Suggested fixes for next session**:
1. Explicitly provide `Module.Finite` instances where needed
2. Use `show` to clarify goal types before `omega`
3. May need helper lemma for finiteness of L(n·[v]) spaces

---

## Dependency Graph (Updated)

```
riemann_roch_ratfunc (NOT PROVED)
    ├─→ ell_ratfunc_projective_eq_deg_plus_one (sorry)
    │       ├─→ ell_ratfunc_projective_single_linear (IN PROGRESS)
    │       │       └─→ ell_ratfunc_projective_gap_le ✅ DONE (Cycle 234)
    │       │               └─→ linearPlace_residue_finrank ✅ DONE (Cycle 234)
    │       ├─→ inv_X_sub_C_pow_mem_projective_general ✅
    │       └─→ inv_X_sub_C_pow_not_mem_projective_general ✅
    └─→ ell_canonical_sub_zero ✅ DONE (Cycle 224)
```

---

## Key Techniques Used This Cycle

### AlgEquiv.ofRingEquiv pattern
```lean
-- Convert bijective algebraMap to AlgEquiv
let e_ring := RingEquiv.ofBijective _ hbij
have hcomm : ∀ c, e_ring (algebraMap Fq _ c) = algebraMap Fq _ c := fun c => rfl
let e_alg := AlgEquiv.ofRingEquiv hcomm
```

### Finiteness from finrank
```lean
-- Establish Module.Finite from positive finrank
have hpos : 0 < Module.finrank Fq M := ...
haveI : Module.Finite Fq M := Module.finite_of_finrank_pos hpos
```

---

## Files Modified This Cycle

- `DimensionScratch.lean` - Main work on dimension formulas

---

## Build Command

```bash
lake build RrLean.RiemannRochV2.SerreDuality.DimensionScratch 2>&1 | grep -E "(error|sorry)"
```

---

## Cycle 233 (SUPERSEDED)

Fixed build path issues. See Cycle 234 for actual sorry resolution progress.

---

*For strategy, see `playbook.md`*
*For historical cycles 1-232, see `ledger_archive.md`*
