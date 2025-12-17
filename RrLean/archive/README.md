# Archive

Historical versions of the Riemann-Roch formalization.

## Files

### RR_v1_axiom_based.lean (Cycles 1-16)
- **Approach**: Axiom-based with `FunctionFieldData` structure
- **Status**: Complete but mathematically circular (RR is an axiom)
- **Lines**: ~1,320
- **Key structures**: `FunctionFieldData`, `RRData`, `RRDataWithRR`

### RR_v2_monolithic.lean (Cycles 17-39)
- **Approach**: Constructive Dedekind domain (HeightOneSpectrum R)
- **Status**: Archived after Cycle 40 modularization
- **Lines**: ~2,531
- **Note**: This file had build errors in Cycle 37-39 sections

## Current Active Code

The active formalization is now modular, located in `RrLean/RiemannRochV2/`:

```
RiemannRochV2/
├── Basic.lean           - Shared imports
├── Divisor.lean         - DivisorV2, deg, Effective
├── RRSpace.lean         - L(D), ℓ(D), monotonicity
├── Typeclasses.lean     - LocalGapBound, SinglePointBound, BaseDim
├── RiemannInequality.lean - Main theorems (PROVED conditionally)
├── Infrastructure.lean  - Residue field, uniformizer
└── LocalGapInstance.lean - Cycles 25-39 work (WIP)
```

See `state/ledger.md` Cycle 40 for modularization details.
