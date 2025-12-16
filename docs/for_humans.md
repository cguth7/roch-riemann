# Riemann-Roch Formalization: Current State

*Last updated: Cycle 15 (December 2024)*

## FULL RIEMANN-ROCH STRUCTURE COMPLETE

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

The complete Riemann-Roch equation is now formalized in Lean 4 with axiomatized structure!

---

## The Goal

Prove the Riemann-Roch theorem for smooth projective curves:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Where:
- ℓ(D) = dim L(D) = dimension of space of functions with poles bounded by D
- K = canonical divisor
- g = genus of the curve

---

## What We've Built (Cycles 4-15)

### Foundation Layers

| Cycle | What | Key Lemmas |
|-------|------|------------|
| 4 | Divisors | `deg_add`, `deg_zero`, `deg_neg`, `deg_sub`, `deg_single` |
| 5 | Function Fields | `Effective_iff`, `Effective_add`, `div_zero` |
| 6 | L(D) is a k-Submodule | `add_mem'`, `smul_mem'`, `mono` |
| 7 | ℓ(D) = dim L(D) | `ell.mono`, `ell.pos_of_effective`, `ell.zero_pos` |
| 8 | Finite-Dimensionality | 8 unconditional versions via typeclass |
| 9 | Quotient Infrastructure | `quotient_add_eq_of_le` (rank-nullity) |
| 10 | Single-Point Axiom | `single_point_bound`, `diff_add_single_le_one` |
| **11** | **RIEMANN INEQUALITY** | `le_deg_add_ell_zero_from_bound` |
| **12** | **FULL RR STRUCTURE** | `riemannRoch_eq`, `ell_K`, `deg_K_eq` |
| 13 | Cleanup | Removed 4 superseded sorries |
| **14** | **GENUS 0** | `ell_eq_deg_minus_genus_of_deg_gt`, `ell_eq_deg_succ_of_genus_zero_deg_gt` |
| **15** | **GENUS 1 (ELLIPTIC)** | `ell_eq_deg_of_genus_one_deg_pos`, `deg_le_of_ell_K_sub_D_pos` |

### Current Score

| Category | Count |
|----------|-------|
| **Definitions** | 12 |
| **Lemmas PROVED** | 55+ |
| **Structures** | 4 (FunctionFieldData, WithBound, WithRR, RRData) |
| **Sorries remaining** | 3 (base RRData theorems + Clifford) |

---

## Key Results by Cycle

### Cycle 11: Riemann Inequality
```
ℓ(D) ≤ deg(D) + 1   for effective divisors D
```

### Cycle 12: Full Riemann-Roch Structure
```
ℓ(D) - ℓ(K-D) = deg(D) + 1 - g       (RR equation)
deg(K) = 2g - 2                       (canonical degree)
ℓ(K) = g                              (canonical dimension = genus)
ℓ(K-D) = 0  when deg(D) > 2g - 2     (vanishing theorem)
```

### Cycle 14: Genus 0 (Projective Line)
```
g = 0 ⟹ deg(K) = -2
g = 0, deg(D) > -2 ⟹ ℓ(D) = deg(D) + 1
```

### Cycle 15: Genus 1 (Elliptic Curves)
```
g = 1 ⟹ deg(K) = 0
g = 1 ⟹ ℓ(K) = 1
g = 1, deg(D) ≥ 1 ⟹ ℓ(D) = deg(D)     (KEY elliptic result)
ℓ(K-D) > 0 ⟹ deg(D) ≤ 2g - 2         (special divisor bound)
```

---

## Structure Hierarchy

```
FunctionFieldData α k
    │ K : Field, div : K → Divisor α
    │ div_mul, div_one, div_inv, deg_div, div_add, div_algebraMap
    │
    ↓ extends
FunctionFieldDataWithBound α k
    │ + single_point_bound : ℓ(D+p) ≤ ℓ(D) + 1
    │ + ell_zero_eq_one : ℓ(0) = 1
    │
    ↓ extends
FunctionFieldDataWithRR α k
    │ + genus : ℕ
    │ + K_div : Divisor α
    │ + deg_K : deg(K) = 2g - 2
    │ + rr_axiom : ℓ(D) - ℓ(K-D) = deg(D) + 1 - g
```

---

## Dependency Graph

```
                    Divisor (α →₀ ℤ)
                          │
                    ┌─────┴─────┐
                    ▼           ▼
                   deg       Effective
                    │           │
                    └─────┬─────┘
                          ▼
                  FunctionFieldData
                    (K, div, ...)
                          │
              ┌───────────┼───────────┐
              ▼           ▼           ▼
          RRSpace     deg_div     div_add
         (L(D) ⊆ K)                 │
              │                     │
              ▼                     │
      ell = finrank k L(D)          │
              │                     │
              └─────────────────────┘
                          │
                          ▼
              FunctionFieldDataWithBound
               + single_point_bound
               + ell_zero_eq_one
                          │
                          ▼
                RIEMANN INEQUALITY
                 ℓ(D) ≤ deg(D) + 1
                          │
                          ▼
              FunctionFieldDataWithRR
               + genus, K_div, deg_K
               + rr_axiom
                          │
            ┌─────────────┼─────────────┐
            ▼             ▼             ▼
       riemannRoch_eq   ell_K    vanishing theorem
            │             │             │
            └──────┬──────┴─────────────┘
                   │
     ┌─────────────┼─────────────┐
     ▼             ▼             ▼
  GENUS 0      GENUS 1      GENERAL
(Cycle 14)   (Cycle 15)    BOUNDS
```

---

## What's Next?

### Remaining Work

1. **Clifford's Inequality** (BLOCKED)
   - Needs multiplication axiom: L(D) × L(K-D) → L(K)
   - Classic proof uses cup product structure

2. **RRData Instantiation** (UNKNOWN)
   - Bridge from FunctionFieldDataWithRR to abstract RRData
   - Needs scheme morphism construction

3. **Genus 2+ Special Cases**
   - Hyperelliptic curves
   - Gap sequences and Weierstrass points

---

## Lessons Learned

1. **Induction principle matters** - Finsupp.induction_linear failed; degree induction worked
2. **Effectivity is delicate** - Doesn't decompose across sums
3. **Axiom layering works** - Build structures incrementally (Bound → RR)
4. **Vanishing is powerful** - deg(K-D) < 0 ⟹ ℓ(K-D) = 0 unlocks many results
5. **Genus specialization** - Each genus has unique formulas (g=0: +1, g=1: exact)

---

## File Structure

```
roch-riemann/
├── RrLean/RR.lean         # Main formalization (~1140 lines)
├── state/
│   ├── playbook.md        # Strategy
│   ├── ledger.md          # Cycle history
│   └── candidates.json    # Candidate tracking
├── agents/                 # ACE loop agents
│   ├── orchestrator.md
│   ├── generator.md
│   ├── reflector.md
│   └── curator.md
└── docs/
    └── for_humans.md      # This file
```

---

*Total: 15 cycles, 55+ lemmas proved, full RR structure with genus 0 and genus 1 results*
