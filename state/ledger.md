# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ 2375 jobs, compiles cleanly
**Phase**: 3 - Serre Duality
**Cycle**: 162 (complete)

### Sorry Count: 14 (down from 15: filled residueAtInfty_inv_X_sub)

| File | Count | Notes |
|------|-------|-------|
| `FullAdelesCompact.lean` | 1 | bound<1 edge case, not needed |
| `FqPolynomialInstance.lean` | 4 | concrete Fq[X] instance |
| `TraceDualityProof.lean` | 1 | abandoned approach |
| `SerreDuality.lean` | 5 | pairing types defined, proofs pending |
| `Residue.lean` | 3 | residueAtInfty_inv_X_sub filled ✅ |

---

## Next Steps (Cycle 163+): RESIDUE APPROACH

### Progress: Cycle 162 Complete ✅

Both X-adic residue and residue at infinity are now defined with key test cases proved:

**X-adic residue** (`residueAtX`):
- `residueAtX_add` ✅
- `residueAtX_smul` ✅
- `residueAtX_polynomial` ✅
- `residueAtX_inv_X = 1` ✅
- `residueAtX_inv_X_sq = 0` ✅
- `residueAtX_linearMap` ✅

**Residue at infinity** (`residueAtInfty`):
- Definition complete ✅ (uses degree-based formula with polynomial remainder)
- `residueAtInfty_zero` ✅
- `residueAtInfty_polynomial` ✅
- `residueAtInfty_inv_X_sub = -1` ✅ (just filled!)
- `residueAtInfty_add` - sorry (additivity)

### Cycle 163 Task: Fill `residueAtInfty_add` proof

Prove additivity: `residueAtInfty (f + g) = residueAtInfty f + residueAtInfty g`

**Challenge:** The degree-based formula doesn't immediately yield additivity.
Need to work through the algebra of num/denom for sums.

### Remaining Plan (~7-9 cycles)

**Phase A: Complete Residue Definitions ✅**
- Cycle 159: Fill `residueAtX_smul` proof ✅
- Cycle 160: Fill `residueAtX_polynomial` proof ✅
- Cycle 161: Define `residueAtInfty` ✅

**Phase B: Residue Theorem (Cycles 162-164)**
```lean
-- Use partial fractions: f = q + ∑ rᵢ/gᵢ where deg(rᵢ) < deg(gᵢ)
-- Polynomial q contributes 0 residue
-- Each rᵢ/gᵢ contributes residues only at roots of gᵢ
-- Sum cancels with infinity
theorem residue_sum_eq_zero (f : RatFunc Fq) :
    (∑ᶠ v, residue_at v f) + residue_infty f = 0 := ...
```

**Phase C: Wire to Serre Pairing (Cycles 165-167)**
```lean
-- The pairing: for [a] ∈ H¹(D) and f ∈ L(K-D)
-- ⟨[a], f⟩ := ∑_v res_v(aᵥ · f)
def serrePairing : H¹(D) →ₗ[k] L(K-D) →ₗ[k] k := ...
```

**Phase D: Non-degeneracy (Cycles 168-171)**
```lean
-- Left: if ⟨[a], f⟩ = 0 for all f, then [a] = 0
-- Right: if ⟨[a], f⟩ = 0 for all [a], then f = 0
-- Use: strong approximation + partial fractions
```

### Why This Works (Mathematical Justification)

For `F = RatFunc Fq` (NOT an extension):
1. Places = irreducible polynomials + ∞
2. Completion at p ≅ `Fq((t-α))` = Laurent series
3. Residue = coefficient of `(t-α)^{-1}`
4. Residue theorem = partial fractions sum to zero

**No trace needed** because we're working directly in F, not an extension K/F.

### Warning Signs (abort if you see these)

- ❌ Trying to define trace on adeles/completions
- ❌ Building abstract residue infrastructure for general extensions
- ❌ More than 3 cycles without `.coeff (-1)` appearing in code
- ✅ Using `HahnSeries.coeff`, `LaurentSeries`, partial fractions

---

## Key Lemmas to Prove

| Lemma | Purpose | Approach |
|-------|---------|----------|
| `residue_at_def` | res_p(f) = coeff of (t-α)^{-1} | Use LaurentSeries.coeff |
| `residue_sum_eq_zero` | ∑ res_v(f) = 0 | Partial fractions |
| `serrePairing_wellDefined` | Descends to H¹(D) | Use residue_sum_eq_zero |
| `serrePairing_left_nondegen` | Left kernel trivial | Strong approximation |
| `serrePairing_right_nondegen` | Right kernel trivial | Partial fractions |
| `serre_duality` | h¹(D) = ℓ(K-D) | Perfect pairing |

---

## Advice for This Phase

### Use these Mathlib tools
- `HahnSeries.coeff` - coefficient extraction
- `LaurentSeries` - abbreviation for `HahnSeries ℤ`
- `div_eq_quo_add_sum_rem_div` - partial fractions decomposition
- `LaurentSeriesRingEquiv` - completion ≅ Laurent series

### The bridge theorem exists
Once `AdelicRRData` is instantiated, `adelicRRData_to_FullRRData` gives full RR automatically. Focus on the 6 axioms:
- `h1_finite`, `ell_finite` - finiteness (use compactness)
- `h1_vanishing` - strong approximation (infrastructure exists)
- `adelic_rr` - Euler characteristic
- `serre_duality` - **NOW TRACTABLE via residues**
- `deg_canonical` - degree of K

---

## Quick Commands

```bash
# Build
lake build 2>&1 | tail -5

# Find sorries
grep -rn "sorry" RrLean/RiemannRochV2/*.lean | grep -v "sorry-free\|-- .*sorry"

# Build specific file
lake build RrLean.RiemannRochV2.DifferentIdealBridge
```

---

## Recent Cycles

### Cycle 162 (2025-12-19)
- **Filled `residueAtInfty_inv_X_sub` proof** - Key test case for residue at infinity
- Proves that `residueAtInfty (1/(X - c)) = -1` for any c ∈ Fq
- Proof technique:
  1. Express `(X - C c)⁻¹` as `1 / (X - C c)` using algebraMap
  2. Use `RatFunc.num_div` and `RatFunc.denom_div` to get num = 1, denom = X - C c
  3. Show gcd(1, X - C c) = 1 with `gcd_one_left`
  4. Prove remainder `1 % (X - C c) = 1` via `mod_eq_self_iff` and degree comparison
  5. Verify deg(1) + 1 = deg(X - C c), so the if-condition is true
  6. Compute `-leadingCoeff(1)/leadingCoeff(X-C c) = -1/1 = -1`
- Sorry count: 15 → 14

### Cycle 161 (2025-12-19)
- **Defined `residueAtInfty`** - Residue at infinity using degree-based formula
- Definition uses polynomial remainder: for f = p/q, compute rem = p % q
  - If deg(rem) + 1 = deg(q), then res_∞ = -leadingCoeff(rem)/leadingCoeff(q)
  - Otherwise res_∞ = 0
- Proved `residueAtInfty_zero` and `residueAtInfty_polynomial`
- Added `residueAtInfty_inv_X_sub` test case (proof outline documented, sorry for now)
- **Residue definitions now complete**: both residueAtX and residueAtInfty defined ✅
- Sorry count: 15→15 (filled definition, added test case sorry)

### Cycle 160 (2025-12-19)
- **Filled `residueAtX_polynomial` proof** - Polynomials have zero residue at X=0
- Proof technique:
  1. Use `RatFunc.coe_coe` to factor: `(p : RatFunc : LaurentSeries) = (p : PowerSeries : LaurentSeries)`
  2. Use `ofPowerSeries_apply` to expose `embDomain` structure
  3. Apply `embDomain_notin_range` since `-1 ∉ range(Nat.cast : ℕ → ℤ)`
  4. Finish with `Int.natCast_nonneg` and `omega`
- **X-adic residue foundation complete**: all lemmas for `residueAtX_linearMap` now proved
- Sorry count: 16→15

### Cycle 159 (2025-12-19)
- **Filled `residueAtX_smul` proof** - Key lemma for linear map structure
- Proof technique:
  1. Use `RatFunc.smul_eq_C_mul` to convert scalar mult to multiplication by constant
  2. Use `RatFunc.coe_coe` to factor coercion through PowerSeries
  3. Use `HahnSeries.C_mul_eq_smul` and `HahnSeries.coeff_smul`
- Partial progress on `residueAtX_polynomial`:
  - Set up: `RatFunc.coe_coe` gives `(p : PowerSeries : LaurentSeries)`
  - Remaining: show `embDomain` with `Nat.cast` has no `-1` in range
- Sorry count: 17→16

### Cycle 158 (2025-12-19)
- **Created `Residue.lean`** - Foundation for residue-based Serre duality
- Defined `residueAtX : RatFunc Fq → Fq` using `HahnSeries.coeff (-1)`
- Proved key lemmas:
  - `residueAtX_add` - additivity ✅
  - `residueAtX_inv_X = 1` - fundamental test case ✅
  - `residueAtX_inv_X_sq = 0` - only simple poles contribute ✅
- Defined `residueAtX_linearMap : RatFunc Fq →ₗ[Fq] Fq`
- Placeholder definitions for `residueAtInfty` and `residueAt` (general places)
- Placeholder for `residue_sum_eq_zero` (residue theorem)
- 6 new sorries (expected - structure first, proofs in subsequent cycles)
- Successfully uses `HahnSeries.coeff (-1)` as planned! ✅

### Cycle 157 (2025-12-19)
- **Investigation cycle**: Deep dive into trace dual vs residue approaches
- **Dead end found**: Trace dual gives `dual(L(D)) ↔ L(K+D)`, NOT `L(K-D)`
- **Breakthrough**: For `K = RatFunc Fq`, residues ARE tractable!
  - `LaurentSeries` with `.coeff (-1)` gives residue extraction
  - `div_eq_quo_add_sum_rem_div` gives partial fractions
  - No trace needed - working directly in F, not extension K/F
- **New plan**: Build explicit residues using Mathlib's Laurent series (~12-15 cycles)
- See "Next Steps" section for detailed roadmap
- No code changes; planning/research cycle

### Cycle 156 (2025-12-19)
- **Created `SerreDuality.lean`** with pairing type definitions
- Defined `serrePairing : H¹(D) × L(K-D) → k` (types compile, proof is sorry)
- Added supporting lemmas: `serrePairing_wellDefined`, `_left_nondegen`, `_right_nondegen`
- Added `serre_duality` theorem and `mkAdelicRRData` constructor
- Investigated Mathlib: no trace on adeles/completions, need algebraic approach
- 5 new sorries (expected, pairing construction pending)

### Cycle 155 (2025-12-18)
- Repo maintenance cycle
- Identified disconnected files needing wiring

### Cycle 154 (2025-12-18)
- Filled `exists_finite_integral_translate_with_infty_bound` for bound ≥ 1
- One sorry remains for bound < 1 (not needed)

### Cycle 153 (2025-12-18)
- Filled 3 sorries in `exists_finite_integral_translate`
- Sorry count: 4→1 in that theorem

### Cycles 133-152 (2025-12-17 to 2025-12-18)
- Full adeles compactness work
- K discrete, closed, integral adeles compact
- Weak approximation

### Cycles 76-132
- Adelic infrastructure build-out
- AdelicH1v2 with Mathlib's FiniteAdeleRing
- DifferentIdealBridge for canonical divisor

### Cycles 1-75
- Phase 1: Riemann Inequality ✅
- Tag: `v1.0-riemann-inequality`

---

## File Status

### In Build (2771 jobs)
- `RiemannRochV2.lean` (root)
- `Basic`, `Divisor`, `RRSpace`, `Typeclasses`
- `RiemannInequality` ✅
- `Infrastructure`, `RRDefinitions`
- `FullAdelesBase`, `FullAdelesCompact` ✅
- `Residue.lean` ✅ (NEW - X-adic residue foundation)

### Disconnected (need wiring)
- `DifferentIdealBridge.lean` ✅
- `TraceDualityProof.lean` (1 sorry, wrong approach)
- `AdelicH1v2.lean` ✅
- `Adeles.lean` (old model)
- `FullRRData.lean`
- `Projective.lean`
- `P1Instance.lean`
- `FqPolynomialInstance.lean` (4 sorries)

---

*For strategy and architecture, see `playbook.md`*
*For historical cycles 1-155, see `ledger_archive.md`*
