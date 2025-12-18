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
import Mathlib.Topology.Algebra.UniformRing
import RrLean.RiemannRochV2.AdelicTopology
import RrLean.RiemannRochV2.FqPolynomialInstance

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

/-! ## Concrete Instance: Polynomial Fq / RatFunc(Fq) / FqtInfty

For function fields over finite fields, we instantiate the full adeles using:
- R = Polynomial Fq (the integer ring)
- K = RatFunc Fq (the fraction field / function field)
- K_∞ = FqtInfty Fq (completion at infinity)
-/

section FqInstance

open FunctionField Polynomial
open scoped Polynomial

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-- There exist height-one primes in Fq[X] (e.g., the ideal generated by X). -/
instance : Nonempty (HeightOneSpectrum Fq[X]) := by
  -- X is irreducible in Fq[X], so (X) is a height-one prime
  have hX : Irreducible (X : Fq[X]) := Polynomial.irreducible_X
  have hX_ne : (X : Fq[X]) ≠ 0 := Polynomial.X_ne_zero
  have hprime : (Ideal.span {X} : Ideal Fq[X]).IsPrime :=
    (Ideal.span_singleton_prime hX_ne).mpr hX.prime
  have hne_bot : (Ideal.span {X} : Ideal Fq[X]) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact hX_ne
  exact ⟨⟨Ideal.span {X}, hprime, hne_bot⟩⟩

/-- Type alias for the full adele ring of Fq(t). -/
abbrev FqFullAdeleRing : Type _ := FullAdeleRing Fq[X] (RatFunc Fq) (FqtInfty Fq)

/-- The ring homomorphism from RatFunc Fq to FqtInfty Fq via completion.

FqtInfty is the uniform space completion of RatFunc Fq with respect to inftyValuation.
The coeRingHom provides the canonical embedding.
-/
noncomputable def inftyRingHom : RatFunc Fq →+* FqtInfty Fq := by
  -- FqtInfty Fq = UniformSpace.Completion (RatFunc Fq) with valued uniform structure
  -- UniformSpace.Completion.coeRingHom gives the embedding
  letI : Valued (RatFunc Fq) (WithZero (Multiplicative ℤ)) := FunctionField.inftyValuedFqt Fq
  exact UniformSpace.Completion.coeRingHom

/-- The Algebra instance from RatFunc Fq to FqtInfty Fq.

Constructed from the ring homomorphism given by the completion embedding.
-/
noncomputable instance instAlgebraRatFuncFqtInfty : Algebra (RatFunc Fq) (FqtInfty Fq) :=
  (inftyRingHom Fq).toAlgebra

/-- The embedding of RatFunc Fq into FqtInfty Fq is injective.

This is a standard property of completions: the original space embeds as a
dense subspace, and hence injectively (for separated spaces).
-/
theorem algebraMap_FqtInfty_injective :
    Function.Injective (algebraMap (RatFunc Fq) (FqtInfty Fq)) := by
  -- The algebraMap is inftyRingHom, which is the completion embedding
  -- Completion embeddings are injective for separated spaces (T0 spaces)
  -- coeRingHom is defined in terms of Completion.coe', which is injective
  -- Technical gap: need to show coeRingHom.toFun = Completion.coe'
  show Function.Injective (inftyRingHom Fq)
  intro x y hxy
  -- inftyRingHom is defined as coeRingHom, which maps x to (x : Completion)
  -- Since Completion.coe is injective for T0 spaces, this follows
  -- The types match via the definition of FqtInfty as a completion
  sorry

/-- The diagonal embedding for Fq(t) into full adeles.

Combines:
- Finite places: FiniteAdeleRing.algebraMap (the existing diagonal into finite adeles)
- Infinite place: algebraMap to FqtInfty (completion at infinity)
-/
def fqFullDiagonalEmbedding : RatFunc Fq →+* FqFullAdeleRing Fq :=
  fullDiagonalEmbedding Fq[X] (RatFunc Fq) (FqtInfty Fq)

/-- The full diagonal embedding for Fq(t) is injective. -/
theorem fqFullDiagonalEmbedding_injective :
    Function.Injective (fqFullDiagonalEmbedding Fq) := by
  apply fullDiagonalEmbedding_injective
  exact algebraMap_FqtInfty_injective Fq

/-! ### Integral Full Adeles

The integral full adeles are elements that are:
1. Integral at all finite places (a_v ∈ O_v)
2. Integral at infinity (|a_∞|_∞ ≤ 1)

For valuations on the completion, we use `Valued.v` which extends the valuation.
-/

/-- The integral full adeles for Fq(t).

An element (a_f, a_∞) is integral if:
- a_f ∈ ∏_v O_v (integral at all finite places)
- Valued.v a_∞ ≤ 1 (integral at infinity, using the extended valuation)
-/
def integralFullAdeles : Set (FqFullAdeleRing Fq) :=
  {a | (∀ v, a.1.val v ∈ v.adicCompletionIntegers (RatFunc Fq)) ∧
       Valued.v a.2 ≤ 1}

/-! ### Key Properties

The following properties establish that K IS discrete in the full adeles.
This is the key difference from finite adeles where K is NOT discrete.
-/

/-- Discreteness of Fq(t) in full adeles.

**Key insight**: The infinite place constrains elements globally.
- Product formula: ∏_v |k|_v = 1 for k ∈ K×
- If |k|_p ≤ 1 for all finite p AND |k|_∞ ≤ ε, then k has bounded degree
- Only finitely many k satisfy such bounds → K is discrete

The proof uses that for k ∈ Fq[X], we have:
- |k|_∞ = q^{deg k} (valuation at infinity = degree)
- Bounded |k|_∞ means bounded degree
- Finitely many polynomials of bounded degree over finite field
-/
theorem fq_discrete_in_fullAdeles :
    DiscreteTopology (Set.range (fqFullDiagonalEmbedding Fq)) := by
  -- The key is that |k|_∞ = q^{deg k} for polynomials
  -- So |k|_∞ < ε implies deg k < log_q(ε), which is finite
  -- Combined with integrality at finite places, only finitely many k satisfy this
  -- Hence every point is isolated, making the subspace discrete
  sorry

/-- Closedness of Fq(t) in full adeles.

Discrete subgroups of locally compact Hausdorff groups are closed.
-/
theorem fq_closed_in_fullAdeles :
    IsClosed (Set.range (fqFullDiagonalEmbedding Fq)) := by
  -- Standard result: discrete + locally compact + Hausdorff → closed
  -- The full adele ring is locally compact and Hausdorff
  -- K is discrete by fq_discrete_in_fullAdeles
  sorry

/-- Compactness of integral full adeles.

The integral full adeles form a compact set because:
1. ∏_v O_v is compact (AllIntegersCompact for finite adeles)
2. {x ∈ FqtInfty | |x|_∞ ≤ 1} is compact (integer ring of local field)
3. Product of compact sets is compact
-/
theorem isCompact_integralFullAdeles [AllIntegersCompact Fq[X] (RatFunc Fq)] :
    IsCompact (integralFullAdeles Fq) := by
  -- integralFullAdeles is a subset of (integral finite adeles) × (integers at ∞)
  -- Both factors are compact, so the product is compact
  sorry

/-- Weak approximation: every element can be shifted into integral adeles.

For Fq[X] (a PID), this is straightforward:
- Only finitely many places have non-integral components
- Find a polynomial that "clears denominators" at all these places
- The result lands in the integral adeles
-/
theorem exists_translate_in_integralFullAdeles [AllIntegersCompact Fq[X] (RatFunc Fq)]
    (a : FqFullAdeleRing Fq) :
    ∃ x : RatFunc Fq, a - fqFullDiagonalEmbedding Fq x ∈ integralFullAdeles Fq := by
  sorry

/-! ### Full Instance -/

/-- FullDiscreteCocompactEmbedding instance for Fq[X] / RatFunc Fq / FqtInfty.

This is the CORRECT axiom class for function fields over finite fields.
Unlike `DiscreteCocompactEmbedding` for finite adeles (which is FALSE),
this instance is TRUE because the infinite place is included.
-/
instance instFullDiscreteCocompactEmbedding [AllIntegersCompact Fq[X] (RatFunc Fq)] :
    FullDiscreteCocompactEmbedding Fq[X] (RatFunc Fq) (FqtInfty Fq) where
  discrete := fq_discrete_in_fullAdeles Fq
  closed := fq_closed_in_fullAdeles Fq
  compact_fundamental_domain := by
    refine ⟨integralFullAdeles Fq, isCompact_integralFullAdeles Fq, ?_⟩
    intro a
    exact exists_translate_in_integralFullAdeles Fq a

end FqInstance

/-! ## Summary

This file provides the corrected adelic framework:

### Completed (sorry-free, general definitions)
- `FullAdeleRing R K K_infty` definition as product
- `fullDiagonalEmbedding` into full adeles
- `FullDiscreteCocompactEmbedding` class (corrected axioms)
- `fullDiagonalEmbedding_injective` theorem

### Concrete Instance: Fq[X] / RatFunc Fq / FqtInfty (with sorries)
- `FqFullAdeleRing Fq` type alias
- `inftyEmbedding` : RatFunc Fq →+* FqtInfty Fq
- `fqFullDiagonalEmbedding` into full adeles
- `integralFullAdeles` using Valued.v
- `instFullDiscreteCocompactEmbedding` instance (sorries in proofs)

### Key Insight
The infinite place provides the "missing constraint" that makes K discrete.
- In finite adeles: neighborhoods constrain only finitely many places → K NOT discrete
- In full adeles: |k|_∞ = q^{deg k} constrains degree → K IS discrete
-/

end RiemannRochV2.FullAdeles

end
