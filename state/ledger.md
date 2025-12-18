# Ledger Vol. 3 (Cycles 80+) - Full Riemann-Roch

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*

## Phase 3: Full Riemann-Roch via Adelic Abstraction

### Milestone Achieved (v1.0-riemann-inequality)

**Tag**: `git checkout v1.0-riemann-inequality`

**Completed Theorems**:
```lean
-- Affine (unconditional)
lemma riemann_inequality_affine [bd : BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + bd.basedim

-- Projective (with axioms)
theorem riemann_inequality_proj [ProperCurve k R K] [AllRational k R]
    {D : DivisorV2 R} (hD : D.Effective)
    [∀ E, Module.Finite k (RRSpace_proj k R K E)] :
    (ell_proj k R K D : ℤ) ≤ D.deg + 1
```

### New Goal: Full Riemann-Roch Theorem

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Where:
- `ℓ(D)` = dimension of the Riemann-Roch space L(D)
- `K` = canonical divisor (defined via differentials)
- `g` = genus of the curve
- `deg(D)` = degree of divisor D

### Strategy: Adelic Interface Approach

Decouple the linear algebra/cohomological logic from the geometric construction by:
1. Defining typeclasses that axiomatize the "Adelic" structure
2. Proving RR assuming these axioms
3. Later: instantiate the axioms for concrete curves

This mirrors the successful strategy from Phase 2 (LocalGapBound → SinglePointBound → ProperCurve).

---

## Roadmap

### Step 1: AdelicInterface.lean (~2-4 hours)

Create typeclasses:
- `GlobalCurveData k R K` - bundles finite adeles + infinite adeles
- `GlobalCurveLaws k R K` - axiomatizes residue theorem and duality

Key components:
- Finite adeles via Mathlib's `DedekindDomain.AdeleRing`
- Infinite adeles as abstract `Type*` with K-module structure
- Residue maps at finite and infinite places
- Integration with `KaehlerDifferential k K`

### Step 2: Canonical Divisor (~4-8 hours)

Define:
- `CanonicalDivisor K` - the canonical divisor via differentials or as axiom
- `deg_canonical : deg(K) = 2g - 2`

Options:
- Axiomatize K directly in `GlobalCurveLaws`
- Define K via differentials (requires more Mathlib infrastructure)

### Step 3: Serre Duality Bridge (~8-16 hours) - HARD

Prove or axiomatize:
- `SerreDuality : L(K-D) ≅ (L(D))*` - as vector space duality
- Non-degenerate pairing: `⟨f, ω⟩ = Σ Res(fω)`

This is the core mathematical difficulty. Options:
- Axiomatize as typeclass field
- Derive from residue theorem + non-degeneracy

### Step 4: Full RR Theorem (~4-8 hours)

Combine:
- Riemann inequality (proved)
- Serre duality (Step 3)
- Degree formula: `deg(K-D) = deg(K) - deg(D)`

Result:
```lean
theorem riemann_roch [FullRRData k R K] {D : DivisorV2 R} :
    ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

---

## Technical Dependencies

### Mathlib Imports Needed

```lean
import Mathlib.RingTheory.DedekindDomain.AdeleRing
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
```

### Key Mathlib Types

- `KaehlerDifferential k K` - Kähler differentials of K over k
- `DedekindDomain.ProdAdicCompletions` - Finite adeles
- `IsDedekindDomain.HeightOneSpectrum` - Finite places (already used)

### Potential Blockers

1. **KaehlerDifferential scalar action** - need `f • ω` to work correctly
2. **Residue map definition** - may need custom construction
3. **Infinite places formalization** - not in Mathlib for function fields
4. **Duality isomorphism** - requires careful linear algebra

---

## Cycle Log

### 2025-12-18

#### Cycle 80 - Phase 3 Kickoff (Pending)

**Goal**: Create `AdelicInterface.lean` with core typeclasses

**Plan**:
1. Add imports for `KaehlerDifferential` and `AdeleRing`
2. Define `GlobalCurveData k R K` typeclass
3. Define `GlobalCurveLaws k R K` typeclass
4. Verify everything compiles

**Status**: Not started

---

## References

- flt-regular project: `NumberTheory/Cyclotomic/Trace.lean` for trace pairing patterns
- Mathlib: `RingTheory.DedekindDomain.*` for Dedekind infrastructure
- Mathlib: `RingTheory.Kaehler.Basic` for differentials
- Hartshorne IV.1 for Riemann-Roch background
