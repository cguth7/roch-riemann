# Riemann-Roch Formalization

A Lean 4 formalization of the Riemann inequality for algebraic curves, built on Dedekind domain foundations.

**Live Documentation:** [cguth7.github.io/roch-riemann](https://cguth7.github.io/roch-riemann/)

## What We Proved

```
l(D) ≤ deg(D) + 1
```

The **Riemann inequality** for effective divisors D on algebraic curves. This is the "easy half" of the Riemann-Roch theorem, proven constructively from first principles with **zero sorries** in the main proof chain.

### Status

| Metric | Value |
|--------|-------|
| Cycles | 75 |
| Lines of Lean | 2493 |
| Modules | 9 |
| Sorries in main proof | **0** |

### Main Theorems (Sorry-Free)

```lean
-- Affine version (fully unconditional)
lemma riemann_inequality_affine [bd : BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + bd.basedim

-- Projective version (requires l(0) = 1 axiom for compactness)
lemma riemann_inequality_real [SinglePointBound R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + 1
```

The `LocalGapBound` typeclass is **automatically instantiated** for any Dedekind domain via `localGapBound_of_dedekind` - no axioms required for the core gap bound.

## Proof Architecture

The proof uses **degree induction** with a single-point bound derived from exact sequences:

```
0 → L(D) → L(D+v) → κ(v)
```

Where κ(v) is the residue field at v, which has Module.length = 1.

### Module Structure

```
RrLean/RiemannRochV2/
├── Basic.lean              # Shared mathlib imports (49 lines)
├── Divisor.lean            # DivisorV2, degree, Effective (134 lines)
├── RRSpace.lean            # L(D), l(D) definitions (201 lines)
├── Typeclasses.lean        # LocalGapBound, SinglePointBound (106 lines)
├── Infrastructure.lean     # Valuation rings, residue fields (399 lines)
├── RRDefinitions.lean      # Evaluation map, shifted elements (648 lines)
├── KernelProof.lean        # ker(eval) = L(D) (411 lines)
├── DimensionCounting.lean  # Gap ≤ 1 via Module.length (186 lines)
└── RiemannInequality.lean  # Main theorems (216 lines)
```

### Key Lemmas

| Lemma | Purpose |
|-------|---------|
| `localGapBound_of_dedekind` | l(D+v) ≤ l(D) + 1 for any Dedekind domain |
| `ker_evaluationMap_eq_RRModuleV2` | ker(eval) = L(D) |
| `evaluationMapAt_complete` | L(D+v) → κ(v) evaluation map |
| `residueField_length` | κ(v) has Module.length = 1 |
| `residueFieldBridge_explicit_clean` | Transport between residue field models |

## What's NOT Proven

The **full Riemann-Roch theorem** `l(D) - l(K-D) = deg(D) + 1 - g` requires:

- **Canonical divisor K** - defined via differentials
- **Serre duality** - isomorphism relating L(D) to differential forms
- **Genus g** - topological/cohomological invariant

These require algebraic geometry infrastructure that mathlib doesn't yet have. The current proof establishes the "easy half" (the inequality) constructively.

## Setup & Build

```bash
# Clone and setup
git clone https://github.com/cguth7/roch-riemann.git
cd roch-riemann

# Build (requires Lean 4 + mathlib)
lake update
lake build
```

## Verify Sorry-Free Status

```bash
# Check main proof files for sorries
grep -r "sorry" RrLean/RiemannRochV2/*.lean | grep -v archive | grep -v Test | grep -v "sorry-free"
# Should only return Projective.lean (work-in-progress alternative approach)
```

## Development History

This project evolved through 75 cycles of iterative development:

- **Cycles 1-16**: Axiom-based approach (RR.lean), derived 70+ lemmas
- **Cycle 17**: Pivot to constructive Dedekind domain foundations
- **Cycles 17-23**: Main theorems proven (conditional on typeclasses)
- **Cycles 24-53**: Infrastructure building (DVR bridges, residue fields)
- **Cycle 52**: `mapEquiv` discovery - bypassed 20 cycles of work
- **Cycles 56-71**: Kernel characterization proof
- **Cycle 73**: `LocalGapBound` instance complete - VICTORY
- **Cycles 74-75**: Cleanup and documentation

See [the story](https://cguth7.github.io/roch-riemann/) for the full journey.

## Archive

The `archive/` directories contain earlier approaches and dead-end code preserved for reference:
- `RR_v1_axiom_based.lean` - Original axiom-based development
- `RR_v2_monolithic.lean` - Pre-modularization monolithic file
- `LocalGapInstance.lean` - Earlier attempt at gap bound

These files contain sorries and are not part of the main proof.

## License

MIT
