import RrLean.RiemannRochV2.Adeles
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Adelic H¹(D) using Mathlib's FiniteAdeleRing (Track B v2)

This module defines H¹(D) using Mathlib's proper `FiniteAdeleRing` (restricted product)
instead of the simplified model in `Adeles.lean`.

## Key Advantage

Using `FiniteAdeleRing R K` (the restricted product Πʳ_v K_v) gives:
1. Elements are integral at almost all places (built-in)
2. For large deg(D), A_K(D) covers all finite adeles → H¹(D) = 0
3. Strong approximation theorem applies directly

## Main Definitions

* `AdelicH1v2.boundedSubset` : {a ∈ FiniteAdeleRing : v(a_v) ≤ exp(D(v)) for all v}
* `AdelicH1v2.globalPlusBounded` : K + A_K(D) as a subgroup
* `AdelicH1v2.Space` : H¹(D) = FiniteAdeleRing / (K + A_K(D))

## Mathematical Background

The adelic Riemann-Roch theorem states:
- h⁰(D) - h¹(D) = deg(D) + 1 - g

where h¹(D) = dim_k(A_K / (K + A_K(D))).

Combined with Serre duality h¹(D) = h⁰(K - D), this gives full Riemann-Roch.

## References

* Mathlib's `IsDedekindDomain.FiniteAdeleRing`
* Liu "Algebraic Geometry and Arithmetic Curves" Chapter 7
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (K : Type*) [Field K] [Algebra k K] [Algebra R K] [IsFractionRing R K]
variable [IsScalarTower k R K]

namespace AdelicH1v2

/-! ## Bounded Adeles using FiniteAdeleRing

We define A_K(D) as a subset of `FiniteAdeleRing R K`.
-/

open FiniteAdeleRing

/-- The diagonal embedding of K into FiniteAdeleRing.
This uses Mathlib's `FiniteAdeleRing.algebraMap`. -/
def diagonalK : K →+* FiniteAdeleRing R K :=
  FiniteAdeleRing.algebraMap R K

/-- Access the component of a finite adele at place v. -/
def component (a : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    v.adicCompletion K :=
  a v

/-- The valuation of the v-th component of a finite adele.
Uses `Valued.v` on the adicCompletion. -/
def valuationAt (a : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    WithZero (Multiplicative ℤ) :=
  Valued.v (a v)

/-- Predicate: an adele satisfies the divisor bound at v.
We say a satisfies the bound at v if v(a_v) ≤ exp(D(v)).
This allows poles up to order D(v) at v. -/
def satisfiesBoundAt (a : FiniteAdeleRing R K) (v : HeightOneSpectrum R)
    (D : DivisorV2 R) : Prop :=
  valuationAt R K a v ≤ WithZero.exp (D v)

/-- The set of adeles bounded by divisor D.
A_K(D) = {a ∈ FiniteAdeleRing : v(a_v) ≤ exp(D(v)) for all v} -/
def boundedSubset (D : DivisorV2 R) : Set (FiniteAdeleRing R K) :=
  {a | ∀ v, satisfiesBoundAt R K a v D}

/-- Zero is in A_K(D) for any D. -/
lemma zero_mem_boundedSubset (D : DivisorV2 R) :
    (0 : FiniteAdeleRing R K) ∈ boundedSubset R K D := by
  intro v
  unfold satisfiesBoundAt valuationAt
  -- (0 : FiniteAdeleRing) at v gives 0 in adicCompletion
  have h : (0 : FiniteAdeleRing R K) v = (0 : v.adicCompletion K) := rfl
  rw [h, Valuation.map_zero]
  exact WithZero.zero_le _

/-- A_K(D) is closed under addition (ultrametric inequality). -/
lemma add_mem_boundedSubset {D : DivisorV2 R} {a b : FiniteAdeleRing R K}
    (ha : a ∈ boundedSubset R K D) (hb : b ∈ boundedSubset R K D) :
    a + b ∈ boundedSubset R K D := by
  intro v
  simp only [satisfiesBoundAt, valuationAt]
  -- For the v-th component: (a + b) v = a v + b v
  -- Use ultrametric: v(a + b) ≤ max(v(a), v(b)) ≤ exp(D v)
  have ha_v := ha v
  have hb_v := hb v
  simp only [satisfiesBoundAt, valuationAt] at ha_v hb_v
  calc Valued.v ((a + b) v)
      = Valued.v (a v + b v) := by rfl
    _ ≤ max (Valued.v (a v)) (Valued.v (b v)) :=
        Valuation.map_add_le_max' _ (a v) (b v)
    _ ≤ WithZero.exp (D v) := max_le ha_v hb_v

/-- A_K(D) is closed under negation. -/
lemma neg_mem_boundedSubset {D : DivisorV2 R} {a : FiniteAdeleRing R K}
    (ha : a ∈ boundedSubset R K D) :
    -a ∈ boundedSubset R K D := by
  intro v
  unfold satisfiesBoundAt valuationAt
  have ha_v := ha v
  unfold satisfiesBoundAt valuationAt at ha_v
  -- (-a) v = -(a v) and v(−x) = v(x)
  have hneg : (-a) v = -(a v) := rfl
  rw [hneg, Valuation.map_neg]
  exact ha_v

/-- A_K(D) as an additive subgroup of FiniteAdeleRing. -/
def boundedAddSubgroup (D : DivisorV2 R) : AddSubgroup (FiniteAdeleRing R K) where
  carrier := boundedSubset R K D
  add_mem' := add_mem_boundedSubset R K
  zero_mem' := zero_mem_boundedSubset R K D
  neg_mem' := neg_mem_boundedSubset R K

/-! ## Global Elements

The image of K in FiniteAdeleRing via diagonal embedding.
-/

/-- The set of global elements (diagonal K).
Elements of the form (x, x, x, ...) for x ∈ K. -/
def globalSubset : Set (FiniteAdeleRing R K) :=
  Set.range (diagonalK R K)

/-- The diagonal of K is an additive subgroup. -/
def globalAddSubgroup : AddSubgroup (FiniteAdeleRing R K) where
  carrier := globalSubset R K
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, (diagonalK R K).map_add x y⟩
  zero_mem' := ⟨0, (diagonalK R K).map_zero⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, (diagonalK R K).map_neg x⟩

/-! ## H¹(D) Definition

H¹(D) = FiniteAdeleRing / (K + A_K(D))
-/

/-- K + A_K(D) as an additive subgroup.
This is the sum of the global diagonal and the bounded adeles. -/
def globalPlusBounded (D : DivisorV2 R) : AddSubgroup (FiniteAdeleRing R K) :=
  globalAddSubgroup R K ⊔ boundedAddSubgroup R K D

/-- H¹(D) = FiniteAdeleRing / (K + A_K(D)) as an additive quotient group. -/
abbrev Space (D : DivisorV2 R) : Type _ :=
  (FiniteAdeleRing R K) ⧸ (globalPlusBounded R K D)

/-- The quotient map from FiniteAdeleRing to H¹(D). -/
def quotientMap (D : DivisorV2 R) :
    FiniteAdeleRing R K →+ Space R K D :=
  QuotientAddGroup.mk' (globalPlusBounded R K D)

/-- Global elements map to zero in H¹(D). -/
lemma quotientMap_of_global (D : DivisorV2 R) (x : K) :
    quotientMap R K D (diagonalK R K x) = 0 := by
  unfold quotientMap
  -- QuotientAddGroup.mk' N x = 0 ↔ x ∈ N
  -- The goal is: (QuotientAddGroup.mk' ...) (diagonalK R K x) = 0
  -- Which means: diagonalK R K x ∈ globalPlusBounded R K D
  have hmem : diagonalK R K x ∈ globalPlusBounded R K D := by
    apply AddSubgroup.mem_sup_left
    exact ⟨x, rfl⟩
  simp only [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, hmem]

/-! ## Key Properties (To be proved)

1. **Monotonicity**: D ≤ E → A_K(D) ⊆ A_K(E)
2. **Cofinality**: For D >> 0, A_K(D) ⊇ {integral adeles} (almost all places)
3. **Vanishing**: h¹(D) = 0 for deg(D) >> 0
4. **Serre duality**: h¹(D) = ℓ(K - D)
-/

/-- Monotonicity: larger divisors give larger bounded subsets. -/
lemma boundedSubset_mono {D E : DivisorV2 R} (h : D ≤ E) :
    boundedSubset R K D ⊆ boundedSubset R K E := by
  intro a ha v
  have hD := ha v
  simp only [satisfiesBoundAt, valuationAt] at hD ⊢
  have hv : D v ≤ E v := h v
  calc Valued.v (a v) ≤ WithZero.exp (D v) := hD
    _ ≤ WithZero.exp (E v) := WithZero.exp_le_exp.mpr hv

/-- Elements of L(D) ⊆ K embed into A_K(D) via the diagonal.

If f ∈ L(D), meaning v(f) ≤ exp(D(v)) for all v, then the diagonal
embedding of f is in A_K(D). -/
lemma globalInBounded (D : DivisorV2 R) (f : K)
    (hf : satisfiesValuationCondition R K D f) :
    diagonalK R K f ∈ boundedSubset R K D := by
  intro v
  unfold satisfiesBoundAt valuationAt
  -- The diagonal embedding gives f at each place
  -- diagonalK R K = FiniteAdeleRing.algebraMap R K
  -- So (diagonalK R K f) v = (f : adicCompletion K v)
  -- Need: Valued.v (f : adicCompletion K v) ≤ exp(D v)
  -- This follows from hf : v(f) ≤ exp(D v) since adicCompletion extends K
  unfold satisfiesValuationCondition at hf
  rcases hf with rfl | hf'
  · -- f = 0 case
    -- (diagonalK R K 0) = 0 by map_zero, and (0 : FiniteAdeleRing) v = 0 in adicCompletion
    have h0 : (diagonalK R K 0) v = (0 : v.adicCompletion K) := by
      simp only [diagonalK, map_zero]
      rfl
    rw [h0, Valuation.map_zero]
    exact WithZero.zero_le _
  · -- f ≠ 0 case with valuation bounds
    specialize hf' v
    -- The key: (diagonalK R K f) v = (f : adicCompletion K v) by definition
    -- And Valued.v (f : adicCompletion K v) = valuation K v f by valuedAdicCompletion_eq_valuation'
    have heq : (diagonalK R K f) v = (f : v.adicCompletion K) := rfl
    rw [heq, valuedAdicCompletion_eq_valuation']
    exact hf'

end AdelicH1v2

/-! ## Connection to Previous Infrastructure

This module provides a more mathematically correct H¹(D) using the restricted
product structure. The previous `Adeles.lean` used all functions, which made
H¹(D) too large.

**Key Differences**:
1. `Adeles.lean`: Uses `HeightOneSpectrum R → K` (all functions)
2. `AdelicH1v2.lean`: Uses `FiniteAdeleRing R K` (restricted product)

The restricted product ensures that elements are integral at almost all places,
which is essential for:
- Finiteness of H¹(D)
- Strong approximation (vanishing for large degree)
- Connection to classical adelic theory
-/

end RiemannRochV2
