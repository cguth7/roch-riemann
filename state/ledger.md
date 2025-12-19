# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ 2523 jobs, compiles cleanly
**Phase**: 3 - Serre Duality
**Cycle**: 156 (complete)

### Sorry Count: 11 (5 new in SerreDuality, expected)

| File | Count | Notes |
|------|-------|-------|
| `FullAdelesCompact.lean` | 1 | bound<1 edge case, not needed |
| `FqPolynomialInstance.lean` | 4 | concrete Fq[X] instance |
| `TraceDualityProof.lean` | 1 | abandoned approach |
| `SerreDuality.lean` | 5 | **NEW** - pairing types defined, proofs pending |

---

## Next Steps (Cycle 157)

### Goal: Fill the Serre Pairing Construction

The types are defined in `SerreDuality.lean`. Now we need to:

1. **Replace the sorry in `serrePairing`** with an actual construction
2. **Options to explore:**
   - Use local traces on completions + sum over places (needs trace on `adicCompletion`)
   - Use global trace on a suitable subspace
   - Use `FractionalIdeal.dual` machinery from `DifferentIdealBridge.lean`

### Key Open Question

Mathlib has NO `Algebra.trace` on `adicCompletion` or `FiniteAdeleRing`.
We need to either:
- Build local trace infrastructure (significant work)
- Find an algebraic shortcut using `traceDual`

### Investigation Task

Read how `FractionalIdeal.dual_eq_mul_inv : dual I = dual 1 * I⁻¹` could help.
The different ideal gives `div(dual 1) = K` (canonical divisor).

### Warning Signs (abort and reassess if you see these)

- Trying to define `res_v` via Laurent series expansion
- Building coefficient extraction for local fields
- More than 100 lines without progress on the pairing
- Needing to construct uniformizers explicitly

---

## Key Lemmas to Prove

| Lemma | Purpose | Approach |
|-------|---------|----------|
| `residueSum_zero` | Sum of residues = 0 | Residue theorem or trace |
| `tracePairing_wellDefined` | Descends to H¹(D) | Use residueSum_zero |
| `tracePairing_leftNondegen` | Left kernel trivial | Use dual properties |
| `tracePairing_rightNondegen` | Right kernel trivial | Use dual_dual |
| `serre_duality` | h¹(D) = ℓ(K-D) | Perfect pairing |

---

## Advice for This Phase

### Use existing infrastructure
- `DifferentIdealBridge.lean` already has `fractionalIdealToDivisor_dual`
- `TraceDualityProof.lean` has `dual_dual_eq`
- `AdelicH1v2.lean` has `AdelicRRData` typeclass ready to instantiate

### Watch out for
- **Universe issues** with quotient modules - use explicit universe annotations
- **Coercion chains** between K, K_v, and adeles
- **Finiteness** - need to show H¹(D) is finite-dimensional

### The bridge theorem exists
Once `AdelicRRData` is instantiated, `adelicRRData_to_FullRRData` gives full RR automatically. Focus on the 6 axioms:
- `h1_finite`, `ell_finite` - finiteness
- `h1_vanishing` - strong approximation
- `adelic_rr` - Euler characteristic
- `serre_duality` - THE KEY ONE
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
