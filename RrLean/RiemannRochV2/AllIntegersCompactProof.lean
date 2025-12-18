/-
# AllIntegersCompact: Incremental Proof

Goal: Prove `CompactSpace (v.adicCompletionIntegers K)` using Mathlib's compactness theorem.

## Key Mathlib Theorem

```
Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField :
    CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K]
```

This requires `Valuation.RankOne` on the valuation.
-/

import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.RankOne
import RrLean.RiemannRochV2.AdelicTopology

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Valued NNReal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannRochV2.AllIntegersCompactProof

/-! ## Step 1: Understand what we need

The compactness theorem requires:
1. `RankOne` instance on `Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))`
2. `Finite` residue field

Let's first check what instances are available.
-/

-- Check: What is the type of adicCompletionIntegers?
#check @HeightOneSpectrum.adicCompletionIntegers
-- adicCompletionIntegers : (v : HeightOneSpectrum R) → K → ValuationSubring (adicCompletion K v)

-- Check: What is adicCompletion?
#check @HeightOneSpectrum.adicCompletion
-- adicCompletion : K → (v : HeightOneSpectrum R) → Type*
-- It's the completion of K with respect to v-adic valuation

-- Check: The Valued instance on adicCompletion
#check @Valued.v
-- For v.adicCompletion K, Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))

-- Check: The compactness theorem
#check @Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
-- Requires: [RankOne Valued.v]

/-! ## Step 2: The blocking issue

The compactness theorem requires `Valuation.RankOne` on `Valued.v`.

For NumberFields, Mathlib provides this via `instRankOneValuedAdicCompletion`.
For general Dedekind domains, we need to either:
1. Axiomatize it
2. Construct it from `MulArchimedean` + `IsNontrivial`

The valuation is nontrivial (it surjects onto WithZero (Multiplicative ℤ)).
-/

-- Check: Surjectivity of the valuation
#check @valuedAdicCompletion_surjective
-- valuedAdicCompletion_surjective K v : Function.Surjective Valued.v

-- Check: nonempty_rankOne_iff_mulArchimedean
#check @Valuation.nonempty_rankOne_iff_mulArchimedean
-- Says: Nonempty v.RankOne ↔ MulArchimedean Γ₀ (when v.IsNontrivial)

/-! ## Step 3: What's missing for general Dedekind domains

For NumberFields, Mathlib provides:
- `IsDiscreteValuationRing (v.adicCompletionIntegers K)` - FinitePlaces.lean:76
- `instRankOneValuedAdicCompletion` - FinitePlaces.lean:137

For general Dedekind domains, these are NOT provided!

We have two options:
1. Directly axiomatize `AllIntegersCompact`
2. Add the necessary axioms and derive compactness

Option 1 is simpler - it's what AdelicTopology.lean already does.
-/

variable (R K)

/-! ## Step 4: Verify the existing axiom approach works -/

-- The existing AllIntegersCompact is already the right abstraction
#check RiemannRochV2.AdelicTopology.AllIntegersCompact
-- class AllIntegersCompact : Prop where
--   compact : ∀ v, CompactSpace (v.adicCompletionIntegers K)

/-! ## Documenting the discharge path

To instantiate `AllIntegersCompact` for a specific function field k(C)/k:

1. **Finite residue fields**: For k finite, each residue field is a finite extension of k
2. **IsDiscreteValuationRing**: Each adicCompletionIntegers is a DVR
   - Proof: Local ring + principal ideals (follows from completing a DVR)
3. **CompleteSpace**: Automatic from completion construction
4. **RankOne**: Construct using |R/v| as exponential base
5. Apply compactSpace_iff... to get CompactSpace

For now, we keep `AllIntegersCompact` as an axiom (Track A approach).
The instances above would need to be proved for Track B.
-/

/-! ## Alternative: More granular axioms

If we want a more granular axiom structure, we could add:
-/

/-- Axiom: All adicCompletionIntegers are DVRs.
This is proven for NumberFields in Mathlib, but not for general Dedekind domains. -/
class AdicCompletionIntegersDVR : Prop where
  isDVR : ∀ v : HeightOneSpectrum R, IsDiscreteValuationRing (v.adicCompletionIntegers K)

/-- Axiom: All adic completion valuations have rank one. -/
class RankOneValuations where
  rankOne : ∀ v : HeightOneSpectrum R, Valuation.RankOne
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))

/-- Axiom: All residue fields of adic completions are finite. -/
class FiniteCompletionResidueFields : Prop where
  finite : ∀ v : HeightOneSpectrum R, Finite (Valued.ResidueField (v.adicCompletion K))

/-- The adicCompletionIntegers is a closed subset of adicCompletion. -/
lemma isClosed_adicCompletionIntegers (v : HeightOneSpectrum R) :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isClosed_valuationSubring (v.adicCompletion K)

/-- The adicCompletionIntegers is complete (as a closed subset of a complete space). -/
instance completeSpace_adicCompletionIntegers (v : HeightOneSpectrum R) :
    CompleteSpace (v.adicCompletionIntegers K) := by
  haveI : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isClosed_adicCompletionIntegers (R := R) K v
  exact IsClosed.completeSpace_coe

/-- Each adicCompletionIntegers is compact, given the granular axioms. -/
theorem compactSpace_adicCompletionIntegers
    [AdicCompletionIntegersDVR R K]
    [RankOneValuations R K]
    [FiniteCompletionResidueFields R K]
    (v : HeightOneSpectrum R) :
    CompactSpace (v.adicCompletionIntegers K) := by
  -- Get axiom instances
  letI hrank := RankOneValuations.rankOne (R := R) (K := K) v
  haveI hdvr := AdicCompletionIntegersDVR.isDVR (R := R) (K := K) v
  haveI hfinite := FiniteCompletionResidueFields.finite (R := R) (K := K) v
  -- adicCompletionIntegers K v = 𝒪[adicCompletion K v] by definition
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨completeSpace_adicCompletionIntegers (R := R) K v, hdvr, hfinite⟩

/-- AllIntegersCompact follows from our axioms. -/
theorem allIntegersCompact_of_axioms
    [AdicCompletionIntegersDVR R K]
    [RankOneValuations R K]
    [FiniteCompletionResidueFields R K] :
    RiemannRochV2.AdelicTopology.AllIntegersCompact R K :=
  ⟨fun v => compactSpace_adicCompletionIntegers R K v⟩

/-! ## Summary

**Axiom hierarchy** (more granular than just `AllIntegersCompact`):
```
AdicCompletionIntegersDVR R K
         +
RankOneValuations R K
         +
FiniteCompletionResidueFields R K
         |
         v
compactSpace_adicCompletionIntegers
         |
         v
AllIntegersCompact R K
```

**To discharge for function fields k(C) over finite k**:
1. `AdicCompletionIntegersDVR`: Each O_v is a DVR (completing a DVR gives a DVR)
2. `RankOneValuations`: Construct using |R/v| as exponential base
3. `FiniteCompletionResidueFields`: Residue field = R/v is finite extension of k

**Current approach**: Keep `AllIntegersCompact` as the primary axiom (Track A).
This file documents the finer structure needed for Track B (discharging axioms).
-/

end RiemannRochV2.AllIntegersCompactProof

end
