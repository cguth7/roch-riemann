# Riemann-Roch for P¹ in Lean 4

A "vibe-coded" formalization of Riemann-Roch for the projective line over finite fields.

**P¹ Riemann-Roch**: ✅ **PROVED** (sorry-free, ~241 cycles)

## The Theorem

```lean
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1
```

For effective divisors on P¹(Fq), dim L(D) = deg(D) + 1.

## How It Was Built

This proof was developed almost entirely by Claude Code running in ~241 automated cycles, with some Gemini assistance for research. The human operator has no algebraic geometry background - navigation was done by reading AI "thinking traces" for emotional texture (hedging, frustration, circling) rather than mathematical content.

## Build

```bash
lake update && lake build
```

Verify the proof is sorry-free:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# No output = complete proof
```

## File Structure

```
RrLean/RiemannRochV2/
├── Divisor.lean                 # Divisor definitions
├── RRSpace.lean                 # Riemann-Roch spaces L(D)
├── Infrastructure.lean          # Valuation rings, residue fields
├── KernelProof.lean             # ker(eval) = L(D)
├── DimensionCounting.lean       # Gap bounds
├── RiemannInequality.lean       # Riemann inequality (also proved)
│
└── SerreDuality/
    ├── DimensionCore.lean       # Core finiteness lemmas
    ├── DimensionScratch.lean    # Main theorem (ell = deg + 1)
    ├── RatFuncPairing.lean      # RatFunc-specific machinery
    └── Smoke.lean               # Build verification
```

## Sorries

**0 sorries in the main codebase.**

6 sorried lemmas were moved to `RrLean/Archive/SorriedLemmas.lean` (dead code not on critical path).

## License

MIT
