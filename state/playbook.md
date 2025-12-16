# Playbook (Curator maintained)

## Heuristics
- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).

## Current Status Summary

**RR.lean (v1)**: Axiom-based approach with `FunctionFieldDataWithRR`. Complete but circular.

**RR_v2.lean (v2)**: Constructive Dedekind domain approach. Key results:
- `RRModuleV2_real`: Valuation-based L(D) definition (PROVED)
- `ellV2_real_mono`: Monotonicity via Module.length (PROVED)
- `riemann_inequality_real`: Conditional on `[SinglePointBound R K]` (PROVED)
- **BLOCKER**: `SinglePointBound.ell_zero_eq_one` is FALSE in affine model

---

## CYCLE 23 PLAN: Typeclass Hierarchy Refactor

### The Problem (from Cycle 22)
`SinglePointBound.ell_zero_eq_one : ellV2_real R K 0 = 1` cannot be satisfied because:
- `HeightOneSpectrum R` captures only FINITE places
- L(0) = R (all integrals), not k (constants)
- Module.length R R = ∞ for Dedekind domains

### The Solution: Two-Tier Typeclass Hierarchy

```
LocalGapBound R K          -- PROVABLE from finite places (gap ≤ 1)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE north star (adds ell_zero = 1)

BaseDim R K                -- SEPARATE: explicit base dimension constant
```

### Implementation Tasks

#### 1. Define `LocalGapBound` (the provable thing)
```lean
/-- The local gap bound: adding a single point increases dimension by at most 1.
This is provable from the evaluation map to the residue field κ(v).
Does NOT require ℓ(0) = 1; works for affine curves. -/
class LocalGapBound (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] where
  gap_le_one : ∀ (D : DivisorV2 R) (v : HeightOneSpectrum R),
    ellV2_real R K (D + DivisorV2.single v 1) ≤ ellV2_real R K D + 1
```

#### 2. Refactor `SinglePointBound` to extend `LocalGapBound`
```lean
/-- Full single-point bound for PROJECTIVE/COMPLETE curves.
Extends LocalGapBound with the base case ℓ(0) = 1.
This requires compactification (infinite places) to instantiate. -/
class SinglePointBound (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    extends LocalGapBound R K where
  ell_zero_eq_one : ellV2_real R K 0 = 1
```

#### 3. Define `BaseDim` for affine theorems
```lean
/-- Explicit base dimension for affine Riemann inequality.
For complete curves: base = 1 (constants only)
For affine curves: base = Module.length R R (possibly infinite, use with care) -/
class BaseDim (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] where
  base : ℕ
  ell_zero_eq : ellV2_real R K 0 = base
```

#### 4. Add `riemann_inequality_affine`
```lean
/-- Affine Riemann inequality: ℓ(D) ≤ deg(D) + ℓ(0) for effective divisors.
Uses LocalGapBound (provable) + BaseDim (explicit base).
For complete curves with BaseDim.base = 1, recovers standard ℓ(D) ≤ deg(D) + 1. -/
lemma riemann_inequality_affine [LocalGapBound R K] [BaseDim R K]
    {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + BaseDim.base R K
```

#### 5. Update helper lemma
```lean
-- Change from [SinglePointBound R K] to [LocalGapBound R K]
lemma ellV2_real_add_single_le_succ [LocalGapBound R K]
    (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    ellV2_real R K (D + DivisorV2.single v 1) ≤ ellV2_real R K D + 1 :=
  LocalGapBound.gap_le_one D v
```

#### 6. Keep `riemann_inequality_real` as the projective north star
The existing proof works unchanged with `[SinglePointBound R K]`.

### Victory Condition for Cycle 23
- [ ] Clean typeclass hierarchy committed
- [ ] `riemann_inequality_affine` stated and proved
- [ ] Documentation explaining affine vs projective model
- [ ] `ellV2_real_add_single_le_succ` uses `LocalGapBound`

### Future Work (Cycle 24+)
- Prove `instance : LocalGapBound R K` via evaluation map
- Explore compactification for `SinglePointBound` instance

---

## Historical Cycles (Summary)

| Cycle | Achievement |
|-------|-------------|
| 1-3 | RRData structure, statement elaborates |
| 4-6 | Divisor, FunctionFieldData, RRSpace as k-Submodule |
| 7-9 | ell = finrank, quotient infrastructure |
| 10-11 | SinglePointBound axiom, **Riemann inequality PROVED** |
| 12-16 | Full RR structure, Clifford's theorem |
| 17 | **PIVOT**: Created RR_v2.lean with Dedekind domains |
| 18-19 | Valuation-based L(D), RRModuleV2_real complete |
| 20 | ellV2_real_mono PROVED |
| 21 | SinglePointBound typeclass, riemann_inequality_real PROVED |
| 22 | **DISCOVERY**: Affine model limitation, residue field infrastructure |
| 23 | (PLANNED) Typeclass hierarchy refactor |

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
