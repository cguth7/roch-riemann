import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import RrLean.RiemannRochV2.AdelicH1v2

/-!
# Topological Properties of Adele Rings

This module establishes topological properties of finite adele rings needed for
the finiteness of H¹(D) in Riemann-Roch theory.

## Main Results

We prove that under suitable hypotheses (finite residue fields), the finite adele ring
`FiniteAdeleRing R K` is locally compact, which is essential for proving that
H¹(D) = A_K / (K + A_K(D)) is finite-dimensional.

## Strategy

For function fields over finite base fields:
1. Each `adicCompletion K v` is locally compact (complete + DVR + finite residue)
2. Each `adicCompletionIntegers K v` is open (Mathlib: `Valued.isOpen_valuationSubring`)
3. Each `adicCompletionIntegers K v` is compact (from finite residue field)
4. The restricted product inherits local compactness via `locallyCompactSpace_of_group`

## Key Mathlib Results Used

- `Valued.isOpen_valuationSubring`: Valuation subrings are open
- `RestrictedProduct.locallyCompactSpace_of_group`: Restricted product local compactness
- `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`:
  Characterization of when valuation integers are compact

## References

- Mathlib's `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- Mathlib's `Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace`
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannRochV2.AdelicTopology

/-! ## Local Compactness of adic completions

For the restricted product to be locally compact, we need each `adicCompletion K v`
to be locally compact. This requires the valuation integers to be compact.
-/

section LocalCompactness

variable (K) (v : HeightOneSpectrum R)

/-- The valuation integers of an adic completion are open.
This is a direct application of Mathlib's `Valued.isOpen_valuationSubring`. -/
theorem isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

/-- If valuation integers are compact, the completion is locally compact.

This uses the fact that the valuation integers form an open neighborhood of 0,
and `IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup` gives local compactness.
-/
theorem locallyCompactSpace_adicCompletion_of_compact
    [hcompact : CompactSpace (v.adicCompletionIntegers K)] :
    LocallyCompactSpace (v.adicCompletion K) := by
  have hopen : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isOpen_adicCompletionIntegers K v
  have hc : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr hcompact
  have h0mem : (0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
    (v.adicCompletionIntegers K).zero_mem
  exact hc.locallyCompactSpace_of_mem_nhds_of_addGroup (hopen.mem_nhds h0mem)

end LocalCompactness

/-! ## Local Compactness of FiniteAdeleRing

We establish that the finite adele ring is locally compact under appropriate hypotheses.
-/

section FiniteAdeleRingTopology

variable (R K)

/-- Hypothesis: all adic completion integers are compact.
This is true for function fields over finite base fields. -/
class AllIntegersCompact : Prop where
  compact : ∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K)

/-- Each adicCompletion is locally compact when integers are compact. -/
instance locallyCompactSpace_adicCompletion [AllIntegersCompact R K]
    (v : HeightOneSpectrum R) :
    LocallyCompactSpace (v.adicCompletion K) := by
  haveI : CompactSpace (v.adicCompletionIntegers K) := AllIntegersCompact.compact v
  exact locallyCompactSpace_adicCompletion_of_compact K v

/-- The finite adele ring is locally compact when all integers are compact.

This follows from the restricted product theorem:
- Each `adicCompletion K v` is locally compact
- Each `adicCompletionIntegers K v` is open (Mathlib: `Valued.isOpen_valuationSubring`)
- All `adicCompletionIntegers K v` are compact

The instance `RestrictedProduct.instLocallyCompactSpace` applies automatically when:
- All R_i are groups with open subgroups B_i
- All B_i are compact
-/
instance locallyCompactSpace_finiteAdeleRing [AllIntegersCompact R K] :
    LocallyCompactSpace (FiniteAdeleRing R K) := by
  -- FiniteAdeleRing R K = Πʳ v, [v.adicCompletion K, v.adicCompletionIntegers K]
  -- We need to establish the Fact for openness
  haveI hopen : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun v => Valued.isOpen_valuationSubring _⟩
  -- Each adicCompletionIntegers is compact (from our hypothesis)
  haveI : ∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K) :=
    fun v => AllIntegersCompact.compact v
  -- FiniteAdeleRing is definitionally equal to the restricted product
  -- Use inferInstanceAs to explicitly match the type
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

end FiniteAdeleRingTopology

/-! ## Discreteness of K in Adeles

For H¹(D) to be finite-dimensional, we need K to embed discretely into the adeles.
-/

section DiscreteEmbedding

variable (R K)

/-- The diagonal embedding of K into FiniteAdeleRing.
This is just Mathlib's `FiniteAdeleRing.algebraMap`. -/
def diagonalEmbedding : K →+* FiniteAdeleRing R K :=
  FiniteAdeleRing.algebraMap R K

/-- The diagonal embedding is injective because K embeds into each completion.

This requires at least one height-one prime (otherwise the adele ring is trivial).
For Dedekind domains that are not fields, this is always satisfied. -/
theorem diagonalEmbedding_injective [Nonempty (HeightOneSpectrum R)] :
    Function.Injective (diagonalEmbedding R K) := by
  intro x y hxy
  -- Two elements of K are equal if their images in FiniteAdeleRing are equal
  -- Extract that x = y at each component
  have heq : ∀ v : HeightOneSpectrum R, (x : v.adicCompletion K) = (y : v.adicCompletion K) := by
    intro v
    have h := congrFun (Subtype.ext_iff.mp hxy) v
    exact h
  -- Pick any height-one prime
  obtain ⟨v⟩ : Nonempty (HeightOneSpectrum R) := inferInstance
  -- The coercion K → adicCompletion K v is injective
  -- adicCompletion K v = Completion (WithVal (v.valuation K))
  -- The coercion factors through WithVal, which has T0Space
  have hinj : Function.Injective (fun k : K => (k : v.adicCompletion K)) := by
    intro a b hab
    -- The coercion factors as: K ≃ WithVal (v.valuation K) → Completion (WithVal ...)
    -- Step 1: view a and b as elements of WithVal
    let a' : WithVal (v.valuation K) := a
    let b' : WithVal (v.valuation K) := b
    -- Step 2: hab says their images in the completion are equal
    have hcoe : (a' : v.adicCompletion K) = (b' : v.adicCompletion K) := hab
    -- Step 3: Use coe_injective on WithVal (which has T0Space from ValuedRing.separated)
    have hinj' := @UniformSpace.Completion.coe_injective (WithVal (v.valuation K)) _ _
    have hab' : a' = b' := hinj' hcoe
    -- Step 4: a' = b' as WithVal means a = b as K (same underlying type)
    exact hab'
  exact hinj (heq v)

/-- The image of K under the diagonal embedding is closed.

This is a key property for the adelic theory. Combined with discreteness,
it ensures K is a discrete closed subgroup.
-/
theorem closed_diagonal [AllIntegersCompact R K] :
    IsClosed (Set.range (diagonalEmbedding R K)) := by
  -- The proof uses the strong approximation theorem flavor:
  -- K ∩ (∏_v O_v) = R, and R is closed (actually discrete)
  sorry

/-- The image of K under the diagonal embedding is discrete.

This is a fundamental result: the global field K sits discretely
inside the adele ring. Combined with closedness, K is a discrete
closed subgroup.
-/
theorem discrete_diagonal [AllIntegersCompact R K] :
    DiscreteTopology (Set.range (diagonalEmbedding R K)) := by
  -- The discreteness follows from:
  -- 1. The "integral adeles" ∏_v O_v form an open subgroup
  -- 2. K ∩ (∏_v O_v) = R (elements integral at all places)
  -- 3. R is discrete in ∏_v O_v (in fact, finite inside any bounded region)
  sorry

end DiscreteEmbedding

/-! ## Cocompactness and Finiteness

The key result: the quotient A_K / (K + bounded subset) is compact,
which implies finite-dimensionality.
-/

section Cocompactness

variable (R K)

/-- The adelic Minkowski theorem:
The quotient A_K / K is compact (after suitable compactification).

More precisely, there exists a compact fundamental domain for the
action of K on the adele ring.

For our application to H¹(D), we use a relative version:
A_K / (K + A_K(D)) is compact (and finite-dimensional as k-space).
-/
theorem compact_adelic_quotient [AllIntegersCompact R K] :
    ∃ (F : Set (FiniteAdeleRing R K)), IsCompact F ∧
      ∀ a, ∃ x : K, a - diagonalEmbedding R K x ∈ F := by
  -- This is the adelic version of Minkowski's theorem
  -- For function fields, it follows from:
  -- 1. The adele ring is a locally compact topological ring
  -- 2. K embeds discretely with compact quotient
  -- 3. The proof uses reduction theory / fundamental domains
  sorry

end Cocompactness

/-! ## Main Theorem: H¹(D) is finite-dimensional

Combining local compactness, discrete embedding, and cocompactness,
we can prove that H¹(D) = A_K / (K + A_K(D)) is finite-dimensional.
-/

section MainTheorem

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (K : Type*) [Field K] [Algebra k K] [Algebra R K] [IsFractionRing R K]
variable [IsScalarTower k R K]

open RiemannRochV2 in
/-- Main theorem: H¹(D) is finite-dimensional under our hypotheses.

The proof uses:
1. The finite adele ring is locally compact (from `locallyCompactSpace_finiteAdeleRing`)
2. K embeds discretely and cocompactly
3. A_K(D) is an open subset containing the "integral" adeles for effective D
4. The quotient inherits compactness, hence finite-dimensionality as a k-space
-/
theorem h1_module_finite [AllIntegersCompact R K]
    (D : DivisorV2 R) (hD : DivisorV2.Effective D) :
    Module.Finite k (AdelicH1v2.SpaceModule k R K D) := by
  -- Strategy:
  -- 1. A_K(D) contains ∏_v O_v for effective D (bounded by 1 at each place)
  -- 2. The quotient A_K / (K + A_K(D)) is a quotient of A_K / (K + ∏_v O_v)
  -- 3. The latter is compact (adelic Minkowski)
  -- 4. A quotient of a compact space is compact
  -- 5. A compact quotient module over k is finite-dimensional
  sorry

end MainTheorem

end RiemannRochV2.AdelicTopology
