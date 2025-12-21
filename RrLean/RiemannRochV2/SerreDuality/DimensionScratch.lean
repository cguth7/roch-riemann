import RrLean.RiemannRochV2.SerreDuality.RatFuncFullRR
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Scratch file for dimension formula development

Goal: Prove ℓ(D) = deg(D) + 1 for effective D with linear place support on P¹.

For P¹ with g = 0:
- K has degree -2
- When deg(D) ≥ 0, deg(K-D) = -2 - deg(D) < 0
- So ℓ(K-D) = 0 (already proved: `ell_canonical_sub_zero`)
- Riemann-Roch becomes: ℓ(D) = deg(D) + 1
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Polynomial RatFunc
open scoped Classical

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Dimension Formula via Gap Bound

Strategy: Prove by induction on deg(D) using the gap bound.
- Base: ℓ(0) = 1 (proved in RatFuncFullRR)
- Step: ℓ(D + [v]) = ℓ(D) + 1 for linear v

For the step, we need:
1. ℓ(D + [v]) ≤ ℓ(D) + 1 (gap bound, need to prove for projective case)
2. ℓ(D + [v]) ≥ ℓ(D) + 1 (construct explicit element in L(D+[v]) \ L(D))
-/

/-! ## Upper bound: Gap ≤ 1 for projective space -/

/-- L_proj(D) ⊆ L_proj(D + [v]) for any linear place v. -/
lemma RRSpace_ratfunc_projective_mono (D : DivisorV2 (Polynomial Fq)) (α : Fq) :
    RRSpace_ratfunc_projective D ≤
    RRSpace_ratfunc_projective (D + DivisorV2.single (linearPlace α) 1) := by
  intro f hf
  rcases hf with ⟨hval, hinfty⟩
  constructor
  · -- Valuation condition for D + [v]
    rcases hval with hzero | hval'
    · left; exact hzero
    right
    intro w
    by_cases hw : w = linearPlace α
    · subst hw
      simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply, if_pos rfl]
      calc (linearPlace α).valuation (RatFunc Fq) f
          ≤ WithZero.exp (D (linearPlace α)) := hval' (linearPlace α)
        _ ≤ WithZero.exp (D (linearPlace α) + 1) := by
            apply WithZero.exp_le_exp.mpr; omega
    · simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply, hw,
                 if_neg (Ne.symm hw), add_zero]
      exact hval' w
  · exact hinfty

/-- Gap bound for projective RRSpace: ℓ(D + [v]) ≤ ℓ(D) + 1.

This uses the evaluation map which sends f to its "residue" at v.
The kernel equals L(D), so the quotient has dimension at most 1 (dim κ(v) = 1). -/
theorem ell_ratfunc_projective_gap_le (D : DivisorV2 (Polynomial Fq)) (α : Fq) :
    ell_ratfunc_projective (D + DivisorV2.single (linearPlace α) 1) ≤
    ell_ratfunc_projective D + 1 := by
  -- The proof follows the same structure as gap_le_one_proj_of_rational in Projective.lean
  -- Key: evaluation map has kernel = L(D) and image ⊆ κ(v) which has dim 1
  sorry

/-! ## Lower bound: Explicit elements -/

/-- The valuation of (X-α) at linearPlace α is exp(-1).
Uses intValuation_linearPlace_eq_exp_neg_rootMultiplicity and Polynomial.rootMultiplicity_X_sub_C. -/
lemma valuation_X_sub_at_self (α : Fq) :
    (linearPlace α).valuation (RatFunc Fq) (RatFunc.X - RatFunc.C α) = WithZero.exp (-1 : ℤ) := by
  have heq : RatFunc.X - RatFunc.C α = algebraMap (Polynomial Fq) (RatFunc Fq)
      (Polynomial.X - Polynomial.C α) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [heq, HeightOneSpectrum.valuation_of_algebraMap]
  rw [intValuation_linearPlace_eq_exp_neg_rootMultiplicity α _ (Polynomial.X_sub_C_ne_zero α)]
  -- rootMultiplicity_X_sub_C : (X - C a).rootMultiplicity a = 1
  simp only [Polynomial.rootMultiplicity_X_sub_C]
  rfl

/-- The valuation of (X-α)⁻¹^k at linearPlace α is exp(k).
Uses valuation_X_sub_at_self, WithZero.exp_inv_eq_neg_int, and WithZero.exp_nsmul. -/
lemma valuation_inv_X_sub_pow_at_self (α : Fq) (k : ℕ) :
    (linearPlace α).valuation (RatFunc Fq) ((RatFunc.X - RatFunc.C α)⁻¹ ^ k) =
    WithZero.exp (k : ℤ) := by
  rw [Valuation.map_pow, Valuation.map_inv, valuation_X_sub_at_self]
  rw [WithZero.exp_inv_eq_neg_int, neg_neg]
  rw [← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_one]

/-- At a place v ≠ linearPlace α, (X-α) has valuation 1.
Key: if (X-α) ∈ v.asIdeal then v = linearPlace α by maximality.
Proof: span{X-α} is maximal (irreducible in PID), contained in v.asIdeal, so they're equal. -/
lemma valuation_X_sub_at_other (α : Fq) (v : HeightOneSpectrum (Polynomial Fq))
    (hv : v ≠ linearPlace α) :
    v.valuation (RatFunc Fq) (RatFunc.X - RatFunc.C α) = 1 := by
  have heq : RatFunc.X - RatFunc.C α = algebraMap (Polynomial Fq) (RatFunc Fq)
      (Polynomial.X - Polynomial.C α) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [heq, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem; apply hv
  -- span{X-α} is maximal (X-α is irreducible in PID Fq[X])
  have hirr : Irreducible (Polynomial.X - Polynomial.C α) := Polynomial.irreducible_X_sub_C α
  have hmax_span : (Ideal.span {Polynomial.X - Polynomial.C α}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hirr
  -- span{X-α} ≤ v.asIdeal
  have hle : Ideal.span {Polynomial.X - Polynomial.C α} ≤ v.asIdeal := by
    rw [Ideal.span_le]; intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact hmem
  -- v.asIdeal ≠ ⊤ (since v is a HeightOneSpectrum element)
  have hv_ne_top : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  -- By maximality of span{X-α}, we have span{X-α} = v.asIdeal
  have heq' : Ideal.span {Polynomial.X - Polynomial.C α} = v.asIdeal :=
    hmax_span.eq_of_le hv_ne_top hle
  exact HeightOneSpectrum.ext heq'.symm

/-- 1/(X-α)^k satisfies the valuation condition for k·[linearPlace α]. -/
lemma inv_X_sub_C_pow_satisfies_valuation (α : Fq) (k : ℕ) (hk : k ≠ 0) :
    satisfiesValuationCondition (Polynomial Fq) (RatFunc Fq)
      ((k : ℤ) • DivisorV2.single (linearPlace α) 1)
      ((RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k) := by
  right
  intro v
  by_cases hv : v = linearPlace α
  · -- At linearPlace α: val = exp(k) ≤ exp(k)
    subst hv
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply,
               ↓reduceIte, mul_one]
    rw [valuation_inv_X_sub_pow_at_self]
  · -- At other places: val = 1 ≤ 1 = exp(0)
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply]
    have hne : linearPlace (Fq := Fq) α ≠ v := fun h => hv h.symm
    simp only [hne, ↓reduceIte, mul_zero, WithZero.exp_zero]
    rw [Valuation.map_pow, Valuation.map_inv, valuation_X_sub_at_other Fq α v hv]
    simp only [inv_one, one_pow, le_refl]

/-! ## intDegree-based lemmas for noPoleAtInfinity

The direct approach using num/denom is blocked by typeclass issues with gcd.
Instead, we use intDegree which provides clean lemmas without typeclass mismatches. -/

/-- X - C α is nonzero in RatFunc. -/
lemma RatFunc_X_sub_C_ne_zero (α : Fq) : (RatFunc.X : RatFunc Fq) - RatFunc.C α ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have h1 : (RatFunc.X : RatFunc Fq).intDegree = 1 := RatFunc.intDegree_X
  have h2 : (RatFunc.C α : RatFunc Fq).intDegree = 0 := RatFunc.intDegree_C α
  rw [h, h2] at h1
  exact zero_ne_one h1

/-- The intDegree of (X - C α)⁻¹ ^ k is -k. -/
lemma intDegree_inv_X_sub_C_pow (α : Fq) (k : ℕ) :
    ((RatFunc.X - RatFunc.C α : RatFunc Fq)⁻¹ ^ k).intDegree = -(k : ℤ) := by
  -- intDegree(X - C α) = 1
  have hXα_deg : (RatFunc.X - RatFunc.C α : RatFunc Fq).intDegree = 1 := by
    have heq : RatFunc.X - RatFunc.C α = algebraMap (Polynomial Fq) (RatFunc Fq)
        (Polynomial.X - Polynomial.C α) := by
      simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    rw [heq, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_sub_C]
    rfl
  -- intDegree((X - C α)⁻¹) = -1
  have hinv_deg : (RatFunc.X - RatFunc.C α : RatFunc Fq)⁻¹.intDegree = -1 := by
    rw [RatFunc.intDegree_inv, hXα_deg]
  -- Helper: (X - C α)⁻¹ ≠ 0
  have hinv_ne : (RatFunc.X - RatFunc.C α : RatFunc Fq)⁻¹ ≠ 0 :=
    inv_ne_zero (RatFunc_X_sub_C_ne_zero Fq α)
  -- Induction on k
  induction k with
  | zero => simp [RatFunc.intDegree_one]
  | succ m ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m hinv_ne) hinv_ne, ih, hinv_deg]
    omega

/-- noPoleAtInfinity is equivalent to intDegree ≤ 0. -/
lemma noPoleAtInfinity_iff_intDegree_le_zero (f : RatFunc Fq) :
    noPoleAtInfinity f ↔ f.intDegree ≤ 0 := by
  unfold noPoleAtInfinity
  simp only [RatFunc.intDegree, sub_nonpos, Int.ofNat_le]

/-- 1/(X-α)^k has no pole at infinity for any k ≥ 0.
Note: The proof uses intDegree and works for k = 0 too (when the function is 1). -/
lemma inv_X_sub_C_pow_noPoleAtInfinity (α : Fq) (k : ℕ) :
    noPoleAtInfinity ((RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k) := by
  rw [noPoleAtInfinity_iff_intDegree_le_zero, intDegree_inv_X_sub_C_pow]
  omega

/-- 1/(X-α)^k is in L_proj(k·[linearPlace α]). -/
lemma inv_X_sub_C_pow_mem_projective (α : Fq) (k : ℕ) :
    (RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k ∈
    RRSpace_ratfunc_projective ((k : ℤ) • DivisorV2.single (linearPlace α) 1) := by
  by_cases hk : k = 0
  · -- k = 0: 1 ∈ L(0)
    subst hk
    simp only [pow_zero, Nat.cast_zero, zero_smul]
    have h1 : (1 : RatFunc Fq) = algebraMap Fq (RatFunc Fq) 1 := by simp
    rw [h1]
    exact constant_mem_projective_zero (1 : Fq)
  · constructor
    · exact inv_X_sub_C_pow_satisfies_valuation Fq α k hk
    · right; exact inv_X_sub_C_pow_noPoleAtInfinity Fq α k

/-- 1/(X-α)^k is NOT in L_proj((k-1)·[linearPlace α]) for k ≥ 1.

This shows the gap is exactly 1, not just ≤ 1. -/
lemma inv_X_sub_C_pow_not_mem_projective_smaller (α : Fq) (k : ℕ) (hk : 0 < k) :
    (RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k ∉
    RRSpace_ratfunc_projective (((k : ℤ) - 1) • DivisorV2.single (linearPlace α) 1) := by
  intro ⟨hval, _⟩
  -- f = (X-α)⁻¹^k is nonzero
  have hf_ne : (RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k ≠ 0 :=
    pow_ne_zero k (inv_ne_zero (RatFunc_X_sub_C_ne_zero Fq α))
  -- The valuation condition must hold for all v
  rcases hval with hzero | hval_all
  · exact hf_ne hzero
  -- At linearPlace α, the valuation is exp(k)
  have hval_at_α := hval_all (linearPlace α)
  rw [valuation_inv_X_sub_pow_at_self] at hval_at_α
  -- But D(linearPlace α) = k - 1
  simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply,
             ↓reduceIte, mul_one] at hval_at_α
  -- So we need exp(k) ≤ exp(k-1), which is false for k ≥ 1
  have hcontra : ¬(WithZero.exp (k : ℤ) ≤ WithZero.exp ((k : ℤ) - 1)) := by
    rw [not_le]
    apply WithZero.exp_lt_exp.mpr
    omega
  exact hcontra hval_at_α

/-! ## Dimension formula for single-point divisors -/

/-- For D = n·[linearPlace α] with n ≥ 0, ℓ(D) = n + 1. -/
theorem ell_ratfunc_projective_single_linear (α : Fq) (n : ℕ) :
    ell_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1) = n + 1 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_smul, zero_add]
    exact ell_ratfunc_projective_zero_eq_one Fq
  | succ m ih =>
    -- ℓ((m+1)·[v]) = ℓ(m·[v] + [v])
    have h_eq : ((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) α) 1 =
        (m : ℤ) • DivisorV2.single (linearPlace α) 1 + DivisorV2.single (linearPlace α) 1 := by
      simp only [Nat.cast_succ, add_smul, one_smul]
    rw [h_eq]
    -- Use gap bound for upper and explicit element for lower
    have h_le := ell_ratfunc_projective_gap_le Fq ((m : ℤ) • DivisorV2.single (linearPlace α) 1) α
    have h_ge : ell_ratfunc_projective
        ((m : ℤ) • DivisorV2.single (linearPlace α) 1 + DivisorV2.single (linearPlace α) 1) ≥
        ell_ratfunc_projective ((m : ℤ) • DivisorV2.single (linearPlace α) 1) + 1 := by
      -- The explicit element 1/(X-α)^(m+1) is in L((m+1)·[v]) but not in L(m·[v])
      -- Rewrite divisor as (m+1)·[v]
      have hdiv_eq : (m : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) α) 1 +
          DivisorV2.single (linearPlace α) 1 =
          ((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1 := by
        simp only [Nat.cast_succ, add_smul, one_smul]
      rw [hdiv_eq]
      -- 1/(X-α)^(m+1) ∈ L((m+1)·[v])
      have h_in := inv_X_sub_C_pow_mem_projective Fq α (m + 1)
      -- 1/(X-α)^(m+1) ∉ L(m·[v])
      have h_not_in := inv_X_sub_C_pow_not_mem_projective_smaller Fq α (m + 1) (Nat.succ_pos m)
      simp only [Nat.cast_succ, add_sub_cancel_right] at h_not_in
      -- L(m·[v]) ⊆ L((m+1)·[v]) by monotonicity
      have h_mono := RRSpace_ratfunc_projective_mono Fq
          ((m : ℤ) • DivisorV2.single (linearPlace α) 1) α
      simp only [Nat.cast_succ, add_smul, one_smul] at h_mono
      -- Strict inclusion: L(m·[v]) < L((m+1)·[v])
      have h_strict : RRSpace_ratfunc_projective ((m : ℤ) • DivisorV2.single (linearPlace α) 1) <
          RRSpace_ratfunc_projective (((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1) := by
        constructor
        · convert h_mono using 1
          simp only [Nat.cast_succ, add_smul, one_smul]
        · intro heq
          rw [← heq] at h_in
          exact h_not_in h_in
      -- finrank strictly increases
      have h_finrank := Submodule.finrank_lt_finrank_of_lt h_strict
      omega
    omega

/-! ## General dimension formula -/

/-- For effective D with linear support and deg(D) ≥ 0, ℓ(D) = deg(D) + 1. -/
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1 := by
  -- Proof by induction on deg(D)
  -- Base case: deg(D) = 0 means D = 0 (since D is effective)
  -- Inductive case: D = D' + [v] for some linear v
  sorry

end RiemannRochV2
