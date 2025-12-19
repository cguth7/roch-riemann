# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ 2771 jobs, compiles cleanly
**Phase**: 3 - Serre Duality
**Cycle**: 156

### Sorry Count: 6 (none critical)

| File | Count | Notes |
|------|-------|-------|
| `FullAdelesCompact.lean` | 1 | bound<1 edge case, not needed |
| `FqPolynomialInstance.lean` | 4 | concrete Fq[X] instance |
| `TraceDualityProof.lean` | 1 | abandoned approach |

---

## Next Steps (Cycle 156)

### Goal: Define the Serre Duality Pairing (Types Only)

**Do NOT start proving things.** First get the pairing definition to typecheck.

### Critical Insight: Trace vs Residue

Mathlib has **algebraic** `Submodule.traceDual` but NOT **geometric** residues for function fields. Building `res_v : K_v → k` from scratch is a major project.

**Key question to answer first:**
> Can we define the global pairing using `Algebra.trace` on adeles, avoiding explicit residue maps?

This would align with our existing `DifferentIdealBridge.lean` infrastructure.

### Step 1: Investigate (before writing code)

1. **Search Mathlib** for:
   - `Algebra.trace` on completions/adeles
   - Any "sum over places" or product formula machinery
   - How `traceDual` relates to pairings

2. **Check type compatibility**:
   - Can we pair `FiniteAdeleRing R K` with `K` using trace?
   - Does the sum over places make sense (almost all zero)?

3. **Look at what we have**:
   - `DifferentIdealBridge.lean` uses `FractionalIdeal.dual`
   - `TraceDualityProof.lean` has `dual_dual_eq`
   - How do these connect to a bilinear form?

### Step 2: Define the Pairing

Create `SerreDuality.lean` with:
```lean
-- The pairing (leave proof obligations as sorry initially)
def serrePairing (D : DivisorV2 R) :
    SpaceModule k R K D →ₗ[k] (RRModuleV2 k R K (canonical - D)) →ₗ[k] k := sorry
```

**Success criterion**: The types compile. Don't worry about the proof yet.

### Step 3: Then prove properties

Only after types work:
- `serrePairing_wellDefined` (descends to quotient)
- `serrePairing_left_nondegen`
- `serrePairing_right_nondegen`

### Warning Signs (abort and reassess if you see these)

- Trying to define `res_v` via Laurent series expansion
- Building coefficient extraction for local fields
- More than 100 lines without a compiling definition
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
