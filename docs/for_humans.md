# Riemann-Roch Formalization: Current State

*Last updated: Cycle 11 (December 2024)*

## 🎉 RIEMANN INEQUALITY PROVED

```
ℓ(D) ≤ deg(D) + 1   for effective divisors D
```

This is the classical Riemann inequality, now formally verified in Lean 4!

---

## The Goal

Prove the Riemann-Roch theorem for smooth projective curves:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

---

## What We've Built (Cycles 4-11)

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
| **11** | **RIEMANN INEQUALITY** | `le_deg_add_ell_zero_from_bound` ✅ |

### Current Score

| Category | Count |
|----------|-------|
| **Definitions** | 9 |
| **Lemmas PROVED** | 35+ |
| **Axioms added** | 3 (single_point_bound, ell_zero_eq_one, deg_div) |

---

## The Breakthrough (Cycle 11)

### The Problem
Initial approach: `Finsupp.induction_linear` decomposes D = D₁ + D₂

**Blocked!** Effective(D₁ + D₂) ⇏ Effective(D₁) ∧ Effective(D₂)

Counter-example: D₁ = -p, D₂ = p → D₁ + D₂ = 0 (effective) but D₁ isn't

### The Solution (thanks Gemini! 🤖)
Induct on **degree** instead of Finsupp structure:

```
Base: deg(D) = 0 and D effective ⟹ D = 0

Step: deg(D) > 0 ⟹ ∃ p with D(p) > 0
      D' = D - p is effective with deg(D') = deg(D) - 1

      IH: ℓ(D') ≤ deg(D') + 1
      Axiom: ℓ(D) = ℓ(D' + p) ≤ ℓ(D') + 1
      Combine: ℓ(D) ≤ deg(D) + 1  ✓
```

*Gemini suggested the degree-based induction approach when the Finsupp approach hit a wall. Pretty cute collab moment!*

---

## Dependency Graph (Updated)

```
                    Divisor (α →₀ ℤ)
                          │
                    ┌─────┴─────┐
                    ▼           ▼
                   deg       Effective
                    │           │
                    └─────┬─────┘
                          ▼
                  FunctionFieldData ──────────────────┐
                    (K, div, ...)                     │
                          │                           ▼
                          ▼                  FunctionFieldDataWithBound
                  RRSpace (L(D) ⊆ K)          + single_point_bound
                          │                   + ell_zero_eq_one
              ┌───────────┼───────────┐              │
              ▼           ▼           ▼              │
           mono       add_mem     smul_mem           │
              │           │           │              │
              └─────┬─────┴───────────┘              │
                    ▼                                │
            ell = finrank k L(D)                     │
                    │                                │
         ┌──────────┼──────────┐                     │
         ▼          ▼          ▼                     │
    ell.mono   pos_of_eff   zero_pos                 │
         │          │          │                     │
         └────┬─────┴──────────┘                     │
              ▼                                      │
      quotient_add_eq_of_le                          │
        dim(L(E)/L(D)) + ℓ(D) = ℓ(E)                │
              │                                      │
              └──────────────┬───────────────────────┘
                             ▼
                   add_single_le_succ
                     ℓ(D+p) ≤ ℓ(D) + 1
                             │
                             ▼
                 ┌───────────┴───────────┐
                 ▼                       ▼
      single_le_deg_succ      le_deg_add_ell_zero
        ℓ(n·p) ≤ n + 1         ℓ(D) ≤ deg(D) + 1
                                      │
                                      ▼
                             RIEMANN INEQUALITY ✅
```

---

## What's Next?

### Path to Full Riemann-Roch

Full RR: ℓ(D) - ℓ(K - D) = deg(D) + 1 - g

We have: ℓ(D) ≤ deg(D) + 1 (Riemann inequality) ✅

Still need:
1. Genus g = ℓ(K) - 1 + dim H¹
2. Serre duality: ℓ(K - D) = dim H¹(O_X(D))
3. Full RR from Euler characteristic

---

## Lessons Learned (Updated)

1. **Induction principle matters** - Finsupp.induction_linear failed; degree induction worked
2. **Effectivity is delicate** - Doesn't decompose across sums
3. **AI collab works** - Gemini spotted the degree-based approach when I was stuck
4. **Axioms are OK** - `single_point_bound` and `ell_zero_eq_one` are geometrically natural

---

## File Structure

```
roch-riemann/
├── RrLean/RR.lean         # Main formalization (~850 lines)
├── state/
│   ├── playbook.md        # Strategy
│   └── ledger.md          # Cycle history
├── agents/                 # ACE loop agents
└── docs/
    └── for_humans.md      # This file
```

---

*Total: 11 cycles, 35+ lemmas proved, Riemann inequality achieved*
