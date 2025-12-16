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

## Next Steps (Cycle 10) - Evaluation Map or Axiom

**WARNING**: Do NOT touch Schemes or Sheaf Cohomology. Complexity cliff.

**Goal**: Unlock Riemann inequality by either axiomatizing or constructing evaluation machinery.

### Option A: Axiomatize Single-Point Bound (Simplest)
Add to `FunctionFieldData`:
```lean
single_point_bound : ∀ (D : Divisor α) (p : α),
    ell data (D + Divisor.single p 1) ≤ ell data D + 1
```
This directly gives Riemann inequality by induction.

### Option B: Add Evaluation Map (More Principled)
Extend `FunctionFieldData` with:
```lean
-- Evaluation at a point (well-defined for f ∈ L(D + p))
eval : α → data.K → k
eval_zero : ∀ p, eval p 0 = 0
eval_add : ∀ p f g, eval p (f + g) = eval p f + eval p g
eval_smul : ∀ p c f, eval p (c • f) = c * eval p f
-- Key property: f ∈ L(D) iff f ∈ L(D+p) and eval p f = 0
eval_kernel : ∀ D p f, f ∈ RRSpace data D ↔ (f ∈ RRSpace data (D + single p 1) ∧ eval p f = 0)
```
This gives a 1-dim quotient via first isomorphism theorem.

### Option C: Valuation Approach (Most General)
Add local valuations `v_p : K* → ℤ` for each point p.
Most mathematically faithful but requires more infrastructure.

### Recommendation
Start with **Option A** (axiom) to unblock progress. Later cycles can strengthen
to Option B/C if needed for deeper results.

### Do NOT do
- Schemes, sheaves, cohomology
- Trying to instantiate FunctionFieldData with real objects yet
