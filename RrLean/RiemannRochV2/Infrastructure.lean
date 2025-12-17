import RrLean.RiemannRochV2.RRSpace

/-!
# Infrastructure for LocalGapBound Instance

This module provides the infrastructure needed to construct the `LocalGapBound` instance:

* **Residue Field** - κ(v) = R/v as a field
* **Linear Algebra Bridge** - Conditional dimension bound via evaluation map
* **Uniformizer Infrastructure** - π generating the maximal ideal

## Cycle 22: Residue Field Infrastructure

**ARCHITECTURAL DISCOVERY**:
The current model using `HeightOneSpectrum R` captures only FINITE places.
For a function field k(t)/k:
- Finite places = height-1 primes of k[t]
- Missing = place at infinity
- L(0) = {no poles at finite places} = k[t], NOT k!

**CONSEQUENCE**: Current model proves "affine Riemann inequality" only.
For complete curve RR, need to add compactification (infinite places).

## Cycle 24 Phase 1: Linear Algebra Bridge

The "Linear Algebra Bridge" lemma establishes the bound ℓ(D+v) ≤ ℓ(D) + 1 CONDITIONALLY
on the existence of a linear map φ : L(D+v) → κ(v) with the right kernel.

## Cycle 24 Phase 2: Uniformizer Infrastructure

The uniformizer π at a height-1 prime v is a generator of v (up to units).
It satisfies v.intValuation π = exp(-1), meaning ord_v(π) = 1.
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Cycle 22: Residue Field Infrastructure -/

-- Candidate 1 [tag: residue_field] [status: OK] [cycle: 22]
/-- The residue field at a height-1 prime v of a Dedekind domain R.
This is the quotient of the localization at v by its maximal ideal.

Geometrically: κ(v) is the "value field" at point v. For a curve over k,
this is a finite extension of k (dimension 1 when k is algebraically closed).

Uses: `Ideal.ResidueField (v.asIdeal)` from mathlib. -/
noncomputable abbrev residueFieldAtPrime (v : HeightOneSpectrum R) : Type _ :=
  v.asIdeal.ResidueField

-- Candidate 2 [tag: residue_field] [status: OK] [cycle: 22]
/-- The residue field at a height-1 prime is a field.
Automatic from mathlib's `Ideal.ResidueField` infrastructure. -/
noncomputable instance residueFieldAtPrime.field (v : HeightOneSpectrum R) :
    Field (residueFieldAtPrime R v) :=
  inferInstance

-- Candidate 3 [tag: residue_field] [status: OK] [cycle: 22]
/-- The residue map from R to κ(v), sending r ↦ r mod v.
This is the composition R → Localization.AtPrime v.asIdeal → κ(v).

Key property: r ∈ ker(residue) ⟺ r ∈ v (membership in the prime ideal).
From mathlib: `Ideal.algebraMap_residueField_eq_zero`. -/
noncomputable def residueMapAtPrime (v : HeightOneSpectrum R) :
    R →+* residueFieldAtPrime R v :=
  algebraMap R (residueFieldAtPrime R v)

/-! ## Cycle 24 Phase 1: Linear Algebra Bridge -/

section LinearAlgebraBridge

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Helper: D ≤ D + single v 1 always holds
lemma divisor_le_add_single (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    D ≤ D + DivisorV2.single v 1 := by
  intro w
  simp only [Finsupp.coe_add, Pi.add_apply, DivisorV2.single]
  by_cases h : w = v
  · subst h; simp only [Finsupp.single_eq_same]; omega
  · simp only [Finsupp.single_eq_of_ne h, add_zero]; exact le_refl _

-- Helper: v.asIdeal is maximal in a Dedekind domain
lemma HeightOneSpectrum.isMaximal (v : HeightOneSpectrum R) : v.asIdeal.IsMaximal :=
  v.isPrime.isMaximal v.ne_bot

-- Candidate 1 [tag: residue_field_equiv] [status: PROVED] [cycle: 24.2]
/-- Linear equivalence between R ⧸ v.asIdeal and κ(v).

Since v.asIdeal is maximal (via HeightOneSpectrum.isMaximal), R ⧸ v.asIdeal is a field.
The algebraMap `R ⧸ v.asIdeal → κ(v)` is bijective for maximal ideals
(via `Ideal.bijective_algebraMap_quotient_residueField`).

This bijective R-algebra homomorphism gives an R-linear isomorphism. -/
noncomputable def residueFieldAtPrime.linearEquiv (v : HeightOneSpectrum R) :
    (R ⧸ v.asIdeal) ≃ₗ[R] residueFieldAtPrime R v := by
  -- The algebraMap is bijective when v.asIdeal is maximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hbij := Ideal.bijective_algebraMap_quotient_residueField v.asIdeal
  -- Construct the linear equivalence from the bijective algebra map
  exact LinearEquiv.ofBijective
    { toFun := algebraMap (R ⧸ v.asIdeal) (residueFieldAtPrime R v)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        -- r • x in R ⧸ v.asIdeal means (algebraMap R (R ⧸ v.asIdeal) r) * x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        -- Need: algebraMap (R ⧸ v.asIdeal) κ(v) (algebraMap R (R ⧸ v.asIdeal) r)
        --     = algebraMap R κ(v) r
        rw [IsScalarTower.algebraMap_apply R (R ⧸ v.asIdeal) (residueFieldAtPrime R v) r] }
    hbij

-- Helper: The residue field is a simple R-module (length = 1)
-- This follows because v.asIdeal is maximal, so R/v.asIdeal is simple,
-- and κ(v) ≅ R/v.asIdeal as R-modules for Dedekind domains.
instance residueFieldAtPrime.isSimpleModule (v : HeightOneSpectrum R) :
    IsSimpleModule R (residueFieldAtPrime R v) := by
  -- R ⧸ v.asIdeal is simple as R-module since v.asIdeal is maximal (= coatom in ideal lattice)
  -- And κ(v) ≃ R ⧸ v.asIdeal as R-modules
  rw [isSimpleModule_iff_quot_maximal]
  refine ⟨v.asIdeal, v.isMaximal, ?_⟩
  -- Use the linear equivalence
  exact ⟨(residueFieldAtPrime.linearEquiv v).symm⟩

-- Helper: Module.length of residue field is 1
lemma residueFieldAtPrime.length_eq_one (v : HeightOneSpectrum R) :
    Module.length R (residueFieldAtPrime R v) = 1 :=
  Module.length_eq_one R (residueFieldAtPrime R v)

/-- The Linear Algebra Bridge:
    IF there exists a linear map φ : L(D+v) → κ(v) with ker φ = L(D) (as submodules of L(D+v)),
    THEN ℓ(D+v) ≤ ℓ(D) + 1.

This lemma establishes the dimension bound CONDITIONALLY on the existence of the evaluation map.
The actual construction of φ (Phase 2) will use uniformizers and the DVR structure.

PROOF OUTLINE:
1. By exact sequence additivity: length(L(D+v)) = length(ker φ) + length(range φ)
2. The kernel condition ensures ker φ = L(D), so length(ker φ) = length(L(D))
3. range φ ⊆ κ(v) and κ(v) is simple, so length(range φ) ≤ 1
4. Therefore: length(L(D+v)) ≤ length(L(D)) + 1 -/
lemma local_gap_bound_of_exists_map
    (D : DivisorV2 R) (v : HeightOneSpectrum R)
    (φ : ↥(RRModuleV2_real R K (D + DivisorV2.single v 1)) →ₗ[R] residueFieldAtPrime R v)
    (h_ker : LinearMap.ker φ = LinearMap.range (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v)))) :
    ellV2_real_extended R K (D + DivisorV2.single v 1) ≤ ellV2_real_extended R K D + 1 := by
  -- Define the inclusion map
  let ι := Submodule.inclusion (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))

  -- The inclusion ι is injective
  have hι_inj : Function.Injective ι := Submodule.inclusion_injective _

  -- Apply Module.length_eq_add_of_exact with rangeRestrict:
  -- length(LDv) = length(LD) + length(range φ)
  have h_add := Module.length_eq_add_of_exact ι (LinearMap.rangeRestrict φ) hι_inj
    (LinearMap.surjective_rangeRestrict φ) (by
      -- Need: Function.Exact ι (LinearMap.rangeRestrict φ)
      rw [LinearMap.exact_iff]
      ext x
      simp only [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hx
        -- x ∈ ker(rangeRestrict φ) means (φ x : κ(v)) = 0
        have hx' : φ x = 0 := Subtype.ext_iff.mp hx
        -- So x ∈ ker φ = range ι
        have hmem : x ∈ LinearMap.ker φ := hx'
        rw [h_ker] at hmem
        exact hmem
      · intro ⟨y, hy⟩
        -- x = ι y means x ∈ range ι = ker φ
        have hmem : x ∈ LinearMap.range ι := ⟨y, hy⟩
        rw [← h_ker] at hmem
        simp only [LinearMap.mem_ker] at hmem
        exact Subtype.ext hmem)

  -- Simplify: length(LDv) = length(LD) + length(range φ)
  unfold ellV2_real_extended
  rw [h_add]

  -- range φ is a submodule of κ(v), which has length 1
  -- So length(range φ) ≤ 1
  have h_range_le : Module.length R (LinearMap.range φ) ≤ 1 := by
    calc Module.length R (LinearMap.range φ)
        ≤ Module.length R (residueFieldAtPrime R v) :=
          Module.length_le_of_injective (LinearMap.range φ).subtype
            (Submodule.subtype_injective _)
      _ = 1 := residueFieldAtPrime.length_eq_one v

  -- Final calculation: length(LD) + length(range φ) ≤ length(LD) + 1
  -- h_range_le : Module.length R (LinearMap.range φ) ≤ 1
  -- Goal: Module.length R (RRModuleV2_real R K D) + Module.length R (LinearMap.range φ) ≤ ...
  have h_bound : Module.length R ↥(RRModuleV2_real R K D) + Module.length R ↥(LinearMap.range φ)
      ≤ Module.length R ↥(RRModuleV2_real R K D) + 1 := by
    gcongr
  exact h_bound

end LinearAlgebraBridge

/-! ## Cycle 24 Phase 2: Uniformizer Infrastructure -/

section UniformizerInfrastructure

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- Choose a uniformizer at v: an element π ∈ R with v.intValuation π = exp(-1).

This exists by `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer`.
Geometric meaning: π generates the maximal ideal v (up to units). -/
noncomputable def uniformizerAt (v : HeightOneSpectrum R) : R :=
  Classical.choose v.intValuation_exists_uniformizer

-- Candidate 2 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The chosen uniformizer satisfies v.intValuation π = exp(-1). -/
lemma uniformizerAt_val (v : HeightOneSpectrum R) :
    v.intValuation (uniformizerAt v) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec v.intValuation_exists_uniformizer

-- Candidate 3 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The uniformizer is nonzero in R. -/
lemma uniformizerAt_ne_zero (v : HeightOneSpectrum R) : uniformizerAt v ≠ 0 := by
  intro h
  have hval := uniformizerAt_val v
  rw [h, map_zero] at hval
  -- 0 ≠ exp(-1), use that 0 is the absorbing element
  exact (WithZero.coe_ne_zero).symm hval

-- Candidate 4 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The valuation of π^n is exp(-n) in the integral valuation. -/
lemma uniformizerAt_pow_val (v : HeightOneSpectrum R) (n : ℕ) :
    v.intValuation ((uniformizerAt v) ^ n) = WithZero.exp (-(n : ℤ)) := by
  induction n with
  | zero =>
    simp only [pow_zero, map_one, Nat.cast_zero, neg_zero, WithZero.exp_zero]
  | succ n ih =>
    rw [pow_succ, map_mul, ih, uniformizerAt_val]
    -- exp(-n) * exp(-1) = exp(-n + (-1)) = exp(-(n+1))
    rw [← WithZero.exp_add, Nat.cast_succ]
    ring_nf

-- Candidate 5 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The valuation of the uniformizer in K (via algebraMap). -/
lemma uniformizerAt_valuation (v : HeightOneSpectrum R) :
    v.valuation K (algebraMap R K (uniformizerAt v)) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact uniformizerAt_val v

-- Candidate 6 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The valuation of π^n in K (via algebraMap). -/
lemma uniformizerAt_pow_valuation (v : HeightOneSpectrum R) (n : ℕ) :
    v.valuation K (algebraMap R K ((uniformizerAt v) ^ n)) = WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact uniformizerAt_pow_val v n

-- Candidate 7 [tag: coercion_simplify] [status: SORRY] [cycle: 24.2]
/-- For f ∈ L(D+v), the shifted element f · π^{D(v)+1} has valuation ≤ 1 at v.

This is KEY: allows us to "evaluate f at v" by shifting the pole away.

PROOF OUTLINE:
- f ∈ L(D+v) means v(f) ≤ exp(D(v)+1)
- By uniformizer: v(π^{D(v)+1}) = exp(-(D(v)+1))
- Product: v(f·π^{D(v)+1}) ≤ exp(D(v)+1) · exp(-(D(v)+1)) = 1

TECHNICAL NOTE: The proof involves careful case analysis on whether D(v)+1 ≥ 0
and manipulation of WithZero.exp with integer arguments. -/
lemma shifted_element_valuation_le_one
    (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : K) (hf : f ∈ RRModuleV2_real R K (D + DivisorV2.single v 1)) :
    v.valuation K (f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)) ≤ 1 := by
  -- Handle f = 0 case
  rcases hf with rfl | hf'
  · simp only [zero_mul, map_zero, zero_le']
  -- f ≠ 0 case: use membership condition and uniformizer properties
  have hfv := hf' v
  simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_eq_same] at hfv
  rw [Valuation.map_mul]
  -- Technical proof: v(f) * v(π^n) ≤ 1 using uniformizer valuation
  sorry -- Valuation arithmetic with WithZero.exp

end UniformizerInfrastructure

end RiemannRochV2
