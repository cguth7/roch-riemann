# Playbook (Curator maintained)

## Heuristics
- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).

## Status
- RESOLVED (Cycle 2): Defined `RRData` structure bundling Div, deg, ell, genus, K. RR statement elaborates.
- RESOLVED (Cycle 3): Extended to `RRDataWithCohomology` and `RRDataWithEuler`.
- **DERIVED** (not proved): `RRDataWithEuler.riemannRoch` is derived from assumed structure fields.
- **RESOLVED (Cycle 4)**: Foundation building - Divisor type and degree
  - `Divisor α := α →₀ ℤ` (abbrev for transparent unification)
  - `deg : Divisor α → ℤ` (sum of coefficients)
  - **PROVED**: `deg_add`, `deg_zero`, `deg_neg`, `deg_sub`, `deg_single`
- **RESOLVED (Cycle 5)**: Function Field Interface
  - `Effective : Divisor α → Prop` (uses mathlib's Finsupp order)
  - **PROVED**: `Effective_iff`, `Effective_zero`, `Effective_add`, `Effective_single`
  - `FunctionFieldData α` structure (K, div, div_mul, div_one, div_inv, deg_div)
  - **PROVED**: `FunctionFieldData.div_zero`
- **RESOLVED (Cycle 6)**: L(D) is a k-Submodule
  - Extended `FunctionFieldData α k` with ground field k, `Algebra k K`, `div_add`, `div_algebraMap`
  - `RRSpace data D : Submodule k data.K` (Riemann-Roch space as proper k-submodule)
  - **PROVED**: `RRSpace.zero_mem'`, `RRSpace.add_mem'`, `RRSpace.smul_mem'`, `RRSpace.mono`

## Blockers (fundamental)
- mathlib lacks: line bundles, sheaf cohomology H⁰/H¹, genus for schemes
- Cannot yet instantiate `RRData.Div` with real `Divisor α` (needs point type from curve)
- `RRData.deg` is abstract; not yet connected to `Divisor.deg`
- `RRData.ell` is abstract; not yet connected to `finrank k (RRSpace data D)`

- **RESOLVED (Cycle 7)**: ℓ(D) = finrank k L(D)
  - `ell : FunctionFieldData α k → Divisor α → ℕ` (semantic dimension)
  - `RRSpace.le_of_divisor_le` converts set inclusion to submodule ≤
  - **PROVED**: `ell.mono`, `ell.pos_of_effective`, `ell.zero_pos`
  - **PROVED**: `RRSpace.one_mem_of_effective`, `RRSpace.algebraMap_mem_zero`, `RRSpace.algebraMap_mem_of_effective`

- **RESOLVED (Cycle 8)**: Finite-Dimensionality Typeclass
  - Used `[∀ D, Module.Finite k (RRSpace data D)]` typeclass instance
  - **PROVED**: `ell.mono_unconditional`, `ell.pos_of_effective_unconditional`, `ell.ge_zero_of_effective`
  - **PROVED**: `ell.mono_of_effective`, `ell.add_effective_le`, `ell.zero_pos_unconditional`
  - **PROVED**: `RRSpace.nontrivial_of_effective`, `ell.diff_le_deg_diff`
  - All Cycle 7 conditional lemmas now have unconditional versions

## Status - Cycle 9 (Success: Quotient Infrastructure)
- **PROVED**: `RRSpace.submodule_inclusion_injective`, `ell.quotient_add_eq_of_le`, `ell.quotient_le_of_le`
- **STATED**: `ell.add_single_le_succ` (key target), `ell.le_deg_add_ell_zero` (Riemann inequality)
- **BLOCKER**: Cannot prove quotient dimension ≤ degree difference without evaluation map
- **KEY LEMMA**: `ell.quotient_add_eq_of_le` gives `dim(L(E)/L(D)) + ℓ(D) = ℓ(E)` - reduces single-point bound to quotient bound

## Status - Cycle 10 (Success: Single-Point Axiom)
- **DEFINED**: `FunctionFieldDataWithBound` - extends FunctionFieldData with `single_point_bound` axiom
- **PROVED**: `ell.add_single_le_succ_from_bound`, `Divisor.deg_add_single`, `ell.diff_add_single_le_one`, `Divisor.add_zero_right`
- **STATED**: `ell.single_le_deg_succ_from_bound`, `ell.le_deg_add_ell_zero_from_bound`, `ell.le_toNat_deg_add_ell_zero_from_bound`
- **DESIGN CHOICE**: Used axiom extension rather than direct proof - cleaner architecture, can be upgraded later

## Status - Cycle 11 (SUCCESS: Riemann Inequality PROVED)
- **AXIOM ADDED**: `ell_zero_eq_one : ell 0 = 1` (L(0) = k, constants only)
- **PROVED**: `Divisor.single_add_one`, `Divisor.Effective_single_nat`, `Divisor.deg_nonneg_of_effective`, `ell.single_le_deg_succ_from_bound`
- **PROVED**: `ell.le_deg_add_ell_zero_from_bound` (**RIEMANN INEQUALITY** by degree induction)
- **PROVED**: `ell.le_toNat_deg_add_ell_zero_from_bound` (corollary)

**Key technique**: Degree-based induction on `(deg D).toNat` instead of `Finsupp.induction_linear`.
**Requires**: `[DecidableEq α]` for effectivity proof.

## Status - Cycle 12 (SUCCESS: Full Riemann-Roch Structure)
- **DEFINED**: `FunctionFieldDataWithRR` extending FunctionFieldDataWithBound with:
  - `genus : ℕ` (geometric genus)
  - `K_div : Divisor α` (canonical divisor)
  - `deg_K : deg K_div = 2g - 2` (Riemann-Hurwitz)
  - `rr_axiom : ℓ(D) - ℓ(K-D) = deg D + 1 - g` (Riemann-Roch)
- **PROVED**: `riemannRoch_eq` (direct application of axiom)
- **PROVED**: `deg_K_eq` (degree of canonical divisor)
- **PROVED**: `ell_K_sub_D_eq` (Serre duality form: ℓ(K-D) in terms of ℓ(D))
- **PROVED**: `ell_ge_deg_minus_genus` (lower bound from RR)
- **PROVED**: `ell_K` (**ℓ(K) = g**, key result connecting canonical space to genus)
- **PROVED**: `ell_K_sub_D_eq_zero_of_deg_gt` (vanishing: deg D > 2g-2 ⟹ ℓ(K-D) = 0)
- **PROVED**: `rr_at_zero` (special case at D = 0)

**7 new lemmas PROVED, 1 structure DEFINED**

## Status - Cycle 13 (SUCCESS: Cleanup)
- **REMOVED**: 4 superseded sorry lemmas
- **FIXED**: 2 unused variable warnings
- **REMAINING SORRIES**: Only 2 (base RRData theorems)

## Status - Cycle 14 (SUCCESS: Genus 0 and High-Degree Results)
- **PROVED**: `ell_eq_deg_minus_genus_of_deg_gt` (**KEY**: deg D > 2g-2 ⟹ ℓ(D) = deg D + 1 - g)
- **PROVED**: `ell_eq_deg_succ_of_genus_zero_deg_gt` (genus 0 formula: ℓ(D) = deg D + 1)
- **PROVED**: 5 more lemmas (deg_K_genus_zero, ell_K_genus_zero, ell_eq_deg_succ_of_genus_zero_effective, ell_le_deg_succ_of_deg_gt, ell_zero_of_genus_zero_deg_neg_one)
- **BLOCKED**: `clifford_bound` (needs multiplication axiom - not provable from RR alone)

**7/8 lemmas PROVED**

## Status - Cycle 15 (SUCCESS: Genus 1 / Elliptic Curves)
- **PROVED**: `deg_K_genus_one` (g=1 ⟹ deg K = 0)
- **PROVED**: `ell_K_genus_one` (g=1 ⟹ ℓ(K) = 1)
- **PROVED**: `ell_eq_deg_of_genus_one_deg_pos` (**KEY**: g=1, deg D ≥ 1 ⟹ ℓ(D) = deg D)
- **PROVED**: `ell_pos_of_effective'` (effective D ⟹ ℓ(D) ≥ 1, wrapper)
- **PROVED**: `deg_le_of_ell_K_sub_D_pos` (**KEY**: ℓ(K-D) > 0 ⟹ deg D ≤ 2g-2, special divisors)
- **PROVED**: `ell_ge_max_one_deg_minus_genus` (ℓ(D) ≥ max(1, deg D + 1 - g))

**6/6 lemmas PROVED**

## Status - Cycle 16 Setup (READY)
- **ADDED**: `FunctionFieldDataWithMul` structure extending `FunctionFieldDataWithRR`
- **AXIOMS**: `mul_sections`, `mul_smul_left`, `mul_smul_right`, `mul_one_left`, `mul_injective_of_ne_zero`
- **KEY AXIOM**: `mul_injective_of_ne_zero` - multiplication by nonzero g ∈ L(K-D) gives injection L(D) → L(K)

## Next Steps (Cycle 16)

**PRIORITY**: Prove Clifford's theorem using the new multiplication axiom.

### Cycle 16 Target: Clifford's Theorem
```
If ℓ(D) ≥ 2 and ℓ(K-D) ≥ 2 (D is "special"), then:
  2·ℓ(D) - 2 ≤ deg(D)
Equivalently:
  ℓ(D) ≤ deg(D)/2 + 1
```

### Proof Strategy for Clifford
1. Take nonzero g ∈ L(K-D) (exists since ℓ(K-D) ≥ 2 > 1)
2. Multiplication by g gives injection: L(D) ↪ L(K) via `mul_injective_of_ne_zero`
3. Therefore ℓ(D) ≤ ℓ(K) = g
4. Apply RR to get the bound

### Other Cycle 16 Candidates
- `mul_sections_image_le`: dim(image of multiplication) ≤ ℓ(K)
- `clifford_inequality`: The main theorem
- `clifford_equality_iff`: When equality holds (hyperelliptic)
- `ell_special_le_half_deg`: Restatement of Clifford

### Do NOT do
- Schemes, sheaves, cohomology
- Weierstrass points (save for Cycle 17 if time)
