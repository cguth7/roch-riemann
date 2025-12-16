# Ledger

## 2025-12-15
- Initial project setup: lakefile, toolchain, RR.lean stub
- Playbook initialized with 4 heuristic bullets
- ACE orchestration loop ready for Cycle 1

### Cycle 1
- **Discovery**: Searched mathlib for RR-related types
  - FOUND: `Scheme`, `IsSmooth`, `IsProper`, `Sheaf.H` (cohomology via Ext)
  - MISSING: WeilDivisor, CartierDivisor, InvertibleSheaf, LineBundle, genus, degree, canonical sheaf
- **Generator**: 8 candidates proposed, 6 BLOCKED due to missing mathlib types
- **Reflector**: No viable candidates. All blocked or fail relevance filter.
- **Decision**: RR.lean unchanged. Bootstrap invariant remains active.
- **Next step**: Need to either (1) define divisor/line bundle types in RR.lean, or (2) find alternative formulation using existing mathlib types.

### Cycle 2
- **Progress Gate triggered**: Same blockers for 2 consecutive cycles (mathlib lacks divisor, line bundle, genus, etc.)
- **Pivot decision**: Option 1 - Define internal interface `RRData`
- **Implementation**:
  - Created `structure RRData` bundling: X (Scheme), toSpec, Div (abstract type), divAddCommGroup, deg, ell, genus, K
  - Defined `RRData.riemannRochEq` as the RR equation proposition
  - Stated `theorem riemannRoch` and `riemannRoch'` with `sorry`
- **Result**: RR.lean elaborates successfully (only sorry warnings)
- **Bootstrap invariant**: DISABLED - theorem statement now typechecks
- **Next**: Fill sorry proofs; may need to add Serre duality or other axioms to RRData
