import RrLean.RiemannRochV2.FullRRData
import RrLean.RiemannRochV2.SerreDuality.RatFuncPairing

/-!
# Full Riemann-Roch for RatFunc Fq (Genus 0)

This module instantiates `FullRRData` for `RatFunc Fq`, completing the proof of
Riemann-Roch for the projective line P¹ over a finite field.

## Mathematical Background

For P¹ over Fq:
- genus g = 0
- canonical divisor K has degree -2
- ℓ(D) = max(0, deg(D) + 1) for divisors with linear place support

Since `DivisorV2 R` only covers finite places, we represent the canonical divisor
K = -2[∞] by choosing an equivalent divisor -2·[linearPlace 0]. Any degree -2
divisor works since they're all linearly equivalent on P¹.

## Main Results

* `canonical_ratfunc` - The canonical divisor K = -2·[linearPlace 0]
* `deg_canonical_ratfunc` - deg(K) = -2
* `ell_canonical_sub_zero` - ℓ(K - D) = 0 when deg(D) ≥ -1

## References

* Hartshorne "Algebraic Geometry" Chapter IV, Section 1
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Canonical Divisor for P¹

For P¹, we choose K = -2·[linearPlace 0] as a representative of the canonical class.
Any degree -2 divisor on P¹ is linearly equivalent to K = -2[∞].
-/

/-- The canonical divisor for RatFunc Fq (P¹ over Fq).
We use -2·[linearPlace 0] as a finite-place representative of K = -2[∞]. -/
def canonical_ratfunc : DivisorV2 (Polynomial Fq) :=
  -2 • DivisorV2.single (linearPlace 0) 1

/-- The genus of P¹ is 0. -/
def genus_ratfunc : ℕ := 0

/-- The canonical divisor has degree -2. -/
theorem deg_canonical_ratfunc : (canonical_ratfunc Fq).deg = -2 := by
  -- Note: We write the proof without referencing genus_ratfunc
  unfold canonical_ratfunc DivisorV2.deg
  -- -2 • single(v, 1) = single(v, -2)
  have h : (-2 : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) 0) 1 =
      DivisorV2.single (linearPlace (Fq := Fq) 0) (-2) := by
    ext w
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply]
    by_cases hw : w = linearPlace (Fq := Fq) 0 <;> simp [hw]
  rw [h]
  simp only [DivisorV2.single, Finsupp.sum_single_index]

/-- deg(K) = 2g - 2 for g = 0. -/
theorem deg_canonical_eq_formula :
    (canonical_ratfunc Fq).deg = 2 * (genus_ratfunc : ℤ) - 2 := by
  rw [deg_canonical_ratfunc]
  unfold genus_ratfunc
  norm_num

/-! ## Linear Support Preservation

K - D has linear support when D has linear support.
-/

/-- The canonical divisor is supported on linear places. -/
theorem canonical_ratfunc_linear_support : IsLinearPlaceSupport (canonical_ratfunc Fq) := by
  intro v hv
  unfold canonical_ratfunc at hv
  simp only [Finsupp.mem_support_iff, ne_eq] at hv
  -- Support of -2 • single(linearPlace 0, 1) is just {linearPlace 0}
  by_cases heq : v = linearPlace (Fq := Fq) 0
  · exact ⟨0, heq⟩
  · -- v ≠ linearPlace 0, so (K)(v) = 0
    exfalso
    apply hv
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply]
    -- Goal: -2 * if linearPlace 0 = v then 1 else 0 = 0
    -- Since heq : v ≠ linearPlace 0, we have linearPlace 0 ≠ v
    have heq' : linearPlace (Fq := Fq) 0 ≠ v := fun h => heq h.symm
    simp only [heq', ↓reduceIte, mul_zero]

/-- K - D has linear support when D has linear support. -/
theorem sub_linear_support (D : DivisorV2 (Polynomial Fq))
    (hD : IsLinearPlaceSupport D) :
    IsLinearPlaceSupport (canonical_ratfunc Fq - D) := by
  intro v hv
  simp only [Finsupp.mem_support_iff, ne_eq] at hv
  -- (K - D)(v) = K(v) - D(v) ≠ 0 means K(v) ≠ D(v)
  -- So v ∈ supp(K) ∪ supp(D)
  rw [sub_eq_add_neg, Finsupp.add_apply, Finsupp.neg_apply] at hv
  by_cases hK : (canonical_ratfunc Fq) v ≠ 0
  · -- v ∈ supp(K), so v is linear
    exact canonical_ratfunc_linear_support Fq v (Finsupp.mem_support_iff.mpr hK)
  · -- K(v) = 0, so D(v) ≠ 0 (since K(v) - D(v) ≠ 0)
    push_neg at hK
    rw [hK, zero_add] at hv
    have hD_ne : D v ≠ 0 := by
      intro h
      apply hv
      rw [h, neg_zero]
    have hD_supp : v ∈ D.support := Finsupp.mem_support_iff.mpr hD_ne
    exact hD v hD_supp

/-! ## Serre Duality Equation

For deg(D) ≥ -1:
- deg(K - D) = -2 - deg(D) ≤ -1 < 0
- So ℓ(K - D) = 0 by `ell_ratfunc_projective_zero_of_neg_deg`
- RR becomes: ℓ(D) - 0 = deg(D) + 1
-/

/-- When deg(D) ≥ -1, we have deg(K - D) < 0. -/
theorem deg_canonical_sub_neg (D : DivisorV2 (Polynomial Fq))
    (hD : D.deg ≥ -1) :
    (canonical_ratfunc Fq - D).deg < 0 := by
  rw [sub_eq_add_neg, DivisorV2.deg_add, DivisorV2.deg_neg, deg_canonical_ratfunc]
  omega

/-- ℓ(K - D) = 0 when deg(D) ≥ -1 and D has linear support. -/
theorem ell_canonical_sub_zero (D : DivisorV2 (Polynomial Fq))
    (hD_deg : D.deg ≥ -1) (hD_lin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective (canonical_ratfunc Fq - D) = 0 := by
  apply ell_ratfunc_projective_zero_of_neg_deg
  · exact deg_canonical_sub_neg Fq D hD_deg
  · exact sub_linear_support Fq D hD_lin

/-! ## Projective L(0) = Constants

For the ProperCurve axiom, we need ℓ(0) = 1.
This is proved via `projective_L0_eq_constants` showing L_proj(0) = Fq.
-/

/-- The projective L(0) equals the constants. -/
theorem projective_L0_eq_constants :
    RRSpace_ratfunc_projective (0 : DivisorV2 (Polynomial Fq)) =
    Submodule.map (Algebra.linearMap Fq (RatFunc Fq)) ⊤ := by
  apply le_antisymm
  · -- L_proj(0) ⊆ constants
    intro f hf
    rw [Submodule.mem_map]
    -- f ∈ L_proj(0) means f has no poles anywhere and no pole at infinity
    -- This means f is a constant
    rcases hf with ⟨hval, hinfty⟩
    rcases hinfty with rfl | hf_nopole
    · -- f = 0, which is a constant
      exact ⟨0, Submodule.mem_top, by simp⟩
    · -- f ≠ 0 with no pole at infinity
      -- f has no poles at finite places (from hval with D = 0)
      -- and no pole at infinity (from hf_nopole)
      -- Such f must be constant
      -- This requires proving that RatFunc with no poles is constant
      sorry
  · -- constants ⊆ L_proj(0)
    intro f hf
    rw [Submodule.mem_map] at hf
    obtain ⟨c, _, hc⟩ := hf
    rw [← hc]
    exact constant_mem_projective_zero c

/-- ℓ_proj(0) = 1 for RatFunc Fq. -/
theorem ell_ratfunc_projective_zero_eq_one :
    ell_ratfunc_projective (0 : DivisorV2 (Polynomial Fq)) = 1 := by
  unfold ell_ratfunc_projective
  -- Need to show finrank(L_proj(0)) = 1
  -- L_proj(0) = constants ≅ Fq as Fq-vector space
  sorry

/-! ## FullRRData Instance

To complete the instantiation, we need:
1. ℓ(0) = 1 (projective L(0) = constants) ← `ell_ratfunc_projective_zero_eq_one`
2. ℓ(D) = deg(D) + 1 for deg(D) ≥ 0 (dimension formula) ← TODO
3. serre_duality_eq combining the above
-/

-- TODO: Complete the FullRRData instance once dimension formula is proved

end RiemannRochV2
