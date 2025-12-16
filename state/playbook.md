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

## Blockers (fundamental)
- mathlib lacks: line bundles, sheaf cohomology H⁰/H¹, genus for schemes
- Cannot yet instantiate `RRData.Div` with real `Divisor α` (needs point type from curve)
- `RRData.deg` is abstract; not yet connected to `Divisor.deg`

## Next Steps (Cycle 5) - Function Field Interface

**WARNING**: Do NOT touch Schemes or Sheaf Cohomology. Complexity cliff.

**Goal**: Define the Riemann-Roch space L(D) to give semantic meaning to ℓ(D).

### Deliverables (in order)
1. **Effective divisors** (warmup):
   - `def Effective (D : Divisor α) : Prop := ∀ p, 0 ≤ D p`
   - `instance : LE (Divisor α)` where `D ≤ E ↔ Effective (E - D)`
   - Prove: `le_refl`, `le_trans`, `le_antisymm` (partial order)

2. **FunctionFieldData structure** (main deliverable):
   ```
   structure FunctionFieldData (α : Type*) where
     K : Type*
     [field : Field K]
     div : K → Divisor α                           -- principal divisor map
     div_mul : ∀ f g, div (f * g) = div f + div g  -- homomorphism
     div_one : div 1 = 0
     deg_div : ∀ f, f ≠ 0 → Divisor.deg (div f) = 0  -- CRITICAL for RR
   ```

3. **Riemann-Roch space L(D)**:
   - `def L (data : FunctionFieldData α) (D : Divisor α) : Set data.K := { f | Effective (data.div f + D) }`
   - This gives `ℓ(D) = dim L(D)` (semantic, not opaque)

4. **Basic L(D) lemmas** (if time):
   - `L_zero : 0 ∈ L D` (zero function always in L(D))
   - `L_mono : D ≤ E → L D ⊆ L E` (monotonicity)

### Why this matters
| Old (RRData) | New (FunctionFieldData) |
|---|---|
| `Div : Type*` (fake) | `Divisor α` (grounded) |
| `deg : Div → ℤ` (opaque) | `Divisor.deg` (proved) |
| `ell : Div → ℕ` (opaque) | `dim L(D)` (semantic) |

### Do NOT do
- Schemes, sheaves, cohomology
- Trying to instantiate FunctionFieldData with real objects yet
- Connecting to RRData (that's Cycle 6+)
