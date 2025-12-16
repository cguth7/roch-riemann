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

## Next Steps (Cycle 8) - Degree-Dimension Inequality (Riemann's Theorem)

**WARNING**: Do NOT touch Schemes or Sheaf Cohomology. Complexity cliff.

**Goal**: Establish ℓ(D) - ℓ(0) ≤ deg(D) for effective D (weak Riemann inequality).

### Mathematical Background
Riemann's inequality: ℓ(D) ≥ deg(D) + 1 - g for effective D
This is half of Riemann-Roch. For now, aim for simpler bounds.

### Possible Deliverables
1. **Finite-dimensionality**: Add axiom to `FunctionFieldData`:
   - `finite_dimensional : ∀ D, Module.Finite k (RRSpace data D)`
   - This is needed for `ell.mono` to apply unconditionally

2. **Degree bounds** (if finite-dimensional holds):
   - Explore what can be said about ℓ(D) vs deg(D)
   - May need additional axioms about the function field

3. **Connect to RRData** (stretch goal):
   - Bridge between concrete `ell data D` and abstract `RRData.ell`

### Do NOT do
- Schemes, sheaves, cohomology
- Trying to instantiate FunctionFieldData with real objects yet
