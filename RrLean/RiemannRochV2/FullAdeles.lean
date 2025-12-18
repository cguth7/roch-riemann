/-
# Full Adele Ring with Infinite Place

This file defines the full adele ring as a product of the finite adele ring and the
completion at infinity. This resolves the mathematical obstruction discovered in Cycle 121:
K is NOT discrete in the finite adeles, but IS discrete in the full adeles.

## Mathematical Background

For a function field K = Fq(t) over a finite field Fq:
- The finite adele ring A_f uses only finite places (HeightOneSpectrum primes)
- K is NOT discrete in A_f (every neighborhood of 0 contains infinitely many k ∈ K)
- The full adele ring A = A_f × K_∞ includes the infinite place
- K IS discrete in A (the product formula constrains elements at all places)

## Main Definitions

* `FullAdeleRing R K K_infty` - Product of FiniteAdeleRing and completion at infinity
* `fullDiagonalEmbedding` - Diagonal embedding K → FullAdeleRing
* `FullDiscreteCocompactEmbedding` - K is discrete and cocompact in full adeles

## For Polynomial Fq / RatFunc(Fq)

We use Mathlib's `FqtInfty Fq` (completion at infinity via `inftyValuation`) as K_∞.
This gives:
- `FullAdeleRing (Polynomial Fq) (RatFunc Fq) (FqtInfty Fq)`
- K is discrete in full adeles (provable)
- Cocompact fundamental domain (with class group considerations)

## References

- Cassels-Fröhlich "Algebraic Number Theory" Ch. II (adeles for number fields)
- Weil "Basic Number Theory" Ch. IV (adeles for function fields)
- Mathlib.NumberTheory.FunctionField (FqtInfty, inftyValuation)
-/

import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import RrLean.RiemannRochV2.AdelicTopology

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2.AdelicTopology
open scoped Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannRochV2.FullAdeles

/-! ## General Definition of Full Adele Ring

For any Dedekind domain R with fraction field K, the full adele ring is parameterized
by a type K_∞ representing the completion at infinity.
-/

section GeneralDefinition

variable (R K)
variable (K_infty : Type*) [Field K_infty] [Algebra K K_infty]

/-- The full adele ring is the product of finite adeles and completion at infinity.

For function fields, this includes ALL places, making K discrete in the full adeles.
For number fields, this generalizes to include all infinite (archimedean) places.
-/
def FullAdeleRing := FiniteAdeleRing R K × K_infty

instance instAddCommGroup : AddCommGroup (FullAdeleRing R K K_infty) :=
  Prod.instAddCommGroup

instance instRing : Ring (FullAdeleRing R K K_infty) :=
  Prod.instRing

variable [TopologicalSpace K_infty]

instance instTopologicalSpace :
    TopologicalSpace (FullAdeleRing R K K_infty) :=
  instTopologicalSpaceProd

variable [IsTopologicalRing K_infty]

-- The FiniteAdeleRing has IsTopologicalRing from Mathlib
-- and K_infty has it by assumption
-- Prod of two topological rings is a topological ring
instance instIsTopologicalRing :
    IsTopologicalRing (FullAdeleRing R K K_infty) := by
  unfold FullAdeleRing
  infer_instance

/-- The diagonal embedding into the full adele ring.

An element k ∈ K is sent to:
- Its diagonal image in FiniteAdeleRing (via Mathlib's algebraMap)
- Its image in K_∞ (via the provided algebra map)
-/
def fullDiagonalEmbedding : K →+* FullAdeleRing R K K_infty :=
  RingHom.prod (FiniteAdeleRing.algebraMap R K) (algebraMap K K_infty)

/-- The projection from full adeles to finite adeles. -/
def projFinite : FullAdeleRing R K K_infty →+* FiniteAdeleRing R K :=
  RingHom.fst _ _

/-- The projection from full adeles to the infinite place. -/
def projInfty : FullAdeleRing R K K_infty →+* K_infty :=
  RingHom.snd _ _

/-- The diagonal embedding is injective when both projections are injective.

For function fields over finite fields, this is always true:
- FiniteAdeleRing embedding is injective (Dedekind domain has height-one primes)
- K_∞ embedding is injective (field extension)
-/
theorem fullDiagonalEmbedding_injective
    [Nonempty (HeightOneSpectrum R)]
    (h_infty : Function.Injective (algebraMap K K_infty)) :
    Function.Injective (fullDiagonalEmbedding R K K_infty) := by
  intro x y hxy
  -- Extract equality in both components
  have h2 : projInfty R K K_infty (fullDiagonalEmbedding R K K_infty x) =
            projInfty R K K_infty (fullDiagonalEmbedding R K K_infty y) := by
    simp only [hxy]
  -- Use injectivity of K → K_∞
  simp only [fullDiagonalEmbedding, projInfty] at h2
  exact h_infty h2

end GeneralDefinition

/-! ## Full Discrete Cocompact Embedding

This is the corrected version of DiscreteCocompactEmbedding that uses full adeles.
K IS discrete in the full adele ring.
-/

section FullDiscreteCocompact

variable (R K)
variable (K_infty : Type*) [Field K_infty] [Algebra K K_infty]
variable [TopologicalSpace K_infty] [IsTopologicalRing K_infty]

/-- Hypothesis: The diagonal embedding of K is discrete and cocompact in FULL adeles.

This is the corrected version of DiscreteCocompactEmbedding. Unlike the finite adele
version (which is FALSE), this statement is TRUE for function fields when K_∞ is the
completion at infinity.

Key difference from finite adeles:
- In finite adeles: neighborhoods constrain only finitely many places
- In full adeles: neighborhoods constrain all places including infinity
- The product formula ∏_v |x|_v = 1 enforces discreteness when all places are included
-/
class FullDiscreteCocompactEmbedding : Prop where
  /-- K is discrete in the full adele ring. -/
  discrete : DiscreteTopology (Set.range (fullDiagonalEmbedding R K K_infty))
  /-- K is closed in the full adele ring. -/
  closed : IsClosed (Set.range (fullDiagonalEmbedding R K K_infty))
  /-- There exists a compact fundamental domain for K in the full adeles. -/
  compact_fundamental_domain : ∃ (F : Set (FullAdeleRing R K K_infty)), IsCompact F ∧
      ∀ a, ∃ x : K, a - fullDiagonalEmbedding R K K_infty x ∈ F

/-- The image of K under the full diagonal embedding is closed. -/
theorem full_closed_diagonal [FullDiscreteCocompactEmbedding R K K_infty] :
    IsClosed (Set.range (fullDiagonalEmbedding R K K_infty)) :=
  FullDiscreteCocompactEmbedding.closed

/-- The image of K under the full diagonal embedding is discrete. -/
theorem full_discrete_diagonal [FullDiscreteCocompactEmbedding R K K_infty] :
    DiscreteTopology (Set.range (fullDiagonalEmbedding R K K_infty)) :=
  FullDiscreteCocompactEmbedding.discrete

/-- The full adelic Minkowski theorem. -/
theorem full_compact_adelic_quotient [FullDiscreteCocompactEmbedding R K K_infty] :
    ∃ (F : Set (FullAdeleRing R K K_infty)), IsCompact F ∧
      ∀ a, ∃ x : K, a - fullDiagonalEmbedding R K K_infty x ∈ F :=
  FullDiscreteCocompactEmbedding.compact_fundamental_domain

end FullDiscreteCocompact

/-! ## Concrete Instance: Polynomial Fq / RatFunc(Fq)

For function fields, we would use Mathlib's `FqtInfty Fq` as the completion at infinity.
This is the completion of `RatFunc Fq` with respect to `inftyValuation`.

**Status**: The concrete instance requires careful navigation of Mathlib's completion API:
- `FunctionField.FqtInfty Fq` is the completion type
- The `Algebra (RatFunc Fq) (FqtInfty Fq)` instance comes from `UniformSpace.Completion`
- The valuation on completion elements uses `Valued.v` (not `inftyValuation` directly)

This will be instantiated in a future cycle once the API is better understood.
-/

/-! ### Why K IS discrete in full adeles

The key difference from finite adeles:

**Finite adeles (K NOT discrete)**:
- Neighborhoods of 0 constrain finitely many finite places
- For any finite set S of primes, the ideal ∏_{p∈S} p contains infinitely many polynomials
- Hence K ∩ U is infinite for every neighborhood U

**Full adeles (K IS discrete)**:
- Neighborhoods constrain all places including infinity
- For k ∈ K nonzero: ∏_v |k|_v = 1 (product formula)
- If |k|_p ≤ 1 for all finite p, then |k|_∞ ≥ 1 (forced by product formula)
- Conversely, if |k|_∞ < ε for small ε, then |k|_p > 1 for some finite p
- This extra constraint from infinity makes K discrete

**Mathematical proof sketch**:
1. Take neighborhood U = U_f × U_∞ where:
   - U_f constrains finitely many finite places (val ≥ 1)
   - U_∞ constrains infinity (val ≥ N for large N)
2. For k ∈ K with diagonal(k) ∈ U:
   - |k|_p ≤ 1 for almost all finite p (finitely many exceptions bounded by U_f)
   - |k|_∞ ≤ ε for small ε (from U_∞)
3. Product formula: if all |k|_v ≤ 1 and |k|_∞ ≤ ε, then |k|_v = 1 a.a. and k bounded
4. Only finitely many k ∈ K satisfy these bounds (Riemann-Roch!)
5. Hence K ∩ U is finite, making K discrete.
-/

/-! ## Summary

This file provides the corrected adelic framework:

### Completed (sorry-free)
- `FullAdeleRing R K K_infty` definition as product
- `fullDiagonalEmbedding` into full adeles
- `FullDiscreteCocompactEmbedding` class (corrected axioms)
- `fullDiagonalEmbedding_injective` theorem

### TODO (next cycles)
1. Instantiate for `Polynomial Fq / RatFunc Fq / FqtInfty Fq`
   - Need to navigate Mathlib's completion API carefully
   - Use `Valued.v` for valuation on completion elements
2. Prove discrete/closed/compact properties for concrete instances
3. Migrate `AdelicH1v2.lean` to use full adeles where needed

### Key Insight
The infinite place provides the "missing constraint" that makes K discrete.
In finite adeles: neighborhoods don't constrain enough places.
In full adeles: the product formula forces boundedness at all places.
-/

end RiemannRochV2.FullAdeles

end
