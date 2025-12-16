# Riemann-Roch Formalization

A Lean 4 formalization of the Riemann-Roch theorem for algebraic curves.

**Live Documentation:** [cguth7.github.io/roch-riemann](https://cguth7.github.io/roch-riemann/)

## Target Theorem

```
l(D) - l(K - D) = deg(D) + 1 - g
```

For a divisor D on a smooth projective curve of genus g, with canonical divisor K.

## Current Status

| Metric | Value |
|--------|-------|
| Cycles | 24 |
| Lemmas Proved | 80+ |
| Sorries Remaining | 2 (deprecated placeholders) |

### Key Results Proved

- **Riemann Inequality**: `l(D) ≤ deg(D) + 1` for effective divisors
- **Affine Riemann Inequality**: `l(D) ≤ deg(D) + l(0)` for affine models
- **Genus 0 formula**: `l(D) = deg(D) + 1`
- **Genus 1 formula**: `l(D) = deg(D)` for positive degree
- **Clifford's inequality** (with multiplication axiom)

## Two Approaches

### `RR.lean` - Axiom-Based
- Abstract `FunctionFieldData` structure
- Axiomatizes single-point bound and RR equation
- Derives genus 0, genus 1, high-degree formulas

### `RR_v2.lean` - Constructive (Dedekind Domains)
- Points = `HeightOneSpectrum R` (height-1 primes)
- L(D) defined via valuations at each prime
- Dimension = `Module.length` (additive in exact sequences)
- **Riemann inequality PROVED by degree induction**

## What's Next

| Task | Difficulty | Notes |
|------|------------|-------|
| `evaluationMapAt` | Medium | Needs DVR uniformizer API |
| Kernel condition | Medium | Valuation properties |
| `LocalGapBound` instance | Easy | Once φ is constructed |
| Compactification | Hard | Add infinite places |
| Serre duality | Very Hard | Differentials, residues |
| Full constructive RR | Very Hard | Multi-month project |

## Setup

```bash
lake update
lake build
```

## Run

```bash
# Check main file
lake env lean RrLean/RR.lean

# Check constructive approach
lake env lean RrLean/RR_v2.lean
```

## Cycle Workflow

```bash
# Commit after a development cycle
./scripts/commit_cycle.sh "short summary"
```

## Architecture

```
RrLean/
├── RR.lean      # Axiom-based approach (genus, canonical, Clifford)
└── RR_v2.lean   # Constructive Dedekind domain approach

state/
├── playbook.md  # Current plan and active tasks
└── ledger.md    # Historical record of all cycles

agents/
└── orchestrator.md  # ACE-style development loop
```

## License

MIT
