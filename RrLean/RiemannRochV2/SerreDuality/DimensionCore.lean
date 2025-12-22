import RrLean.RiemannRochV2.SerreDuality.RatFuncPairing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Core Finiteness Results for RRSpace

This module proves `Module.Finite` for `RRSpace_ratfunc_projective (n·[α])` using the
correct mathematical approach: embedding into a known finite-dimensional space.

## Key Principle

**DO NOT** prove `Module.Finite` using `finrank`. This is circular:
- `Module.finite_of_finrank_pos` requires `Module.finrank` to be positive
- `Module.finrank` only gives meaningful values when `Module.Finite` holds

**DO** prove `Module.Finite` by constructing a linear injection into a known finite-dim space:
1. Define `clearPoles : RRSpace(n·[α]) →ₗ[Fq] Polynomial.degreeLT Fq (n+1)`
   by `f ↦ (X-α)^n · f`
2. Show this is well-defined: if f ∈ RRSpace(n·[α]), then (X-α)^n · f is a polynomial
   of degree ≤ n (clears poles at α, and noPoleAtInfinity ⟹ degree ≤ 0 + n = n)
3. Show it's injective: multiplication by nonzero is injective in a domain
4. Conclude: codomain `Polynomial.degreeLT Fq (n+1)` is finite-dim ⟹ domain is finite-dim

## Main Results

* `RRSpace_ratfunc_projective_single_linear_finite` - Module.Finite for L(n·[α])

## References

This is the standard approach in algebraic geometry: L(D) ↪ k^{deg(D)+1} via pole clearing.
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Polynomial RatFunc
open scoped Classical

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Pole Clearing Map

For f ∈ RRSpace(n·[α]), the function (X-α)^n · f is a polynomial of degree ≤ n.
This gives a linear injection into the finite-dimensional space Fq[X]_{≤n}.
-/

/-- Helper: If f ∈ RRSpace_ratfunc_projective (n·[α]), then f.denom = (X-α)^m for some m ≤ n.
This is because:
1. At any place v ≠ linearPlace α, val_v(f) ≤ 1, so denom has no other irreducible factors
2. At linearPlace α, val_α(f) ≤ exp(n), so m ≤ n -/
lemma denom_is_power_of_X_sub (α : Fq) (n : ℕ) (f : RatFunc Fq) (hf_ne : f ≠ 0)
    (hf : f ∈ RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    ∃ m : ℕ, m ≤ n ∧ f.denom = (Polynomial.X - Polynomial.C α) ^ m := by
  -- The proof proceeds by:
  -- 1. Factor denom = (X-α)^m * R
  -- 2. Show R = 1 (no other factors) using valuation constraints
  -- 3. Show m ≤ n from the valuation bound at linearPlace α
  sorry

lemma mul_X_sub_pow_is_polynomial (α : Fq) (n : ℕ) (f : RatFunc Fq)
    (hf : f ∈ RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    ∃ p : Polynomial Fq, (Polynomial.X - Polynomial.C α)^n * RatFunc.num f =
        p * RatFunc.denom f ∧ p.natDegree ≤ n := by
  by_cases hf0 : f = 0
  · use 0
    simp [hf0]
  -- Get denom = (X-α)^m with m ≤ n
  obtain ⟨m, hm_le, hdenom_eq⟩ := denom_is_power_of_X_sub Fq α n f hf0 hf
  -- Define p = (X-α)^(n-m) * num
  use (Polynomial.X - Polynomial.C α) ^ (n - m) * f.num
  constructor
  · -- (X-α)^n * num = p * denom = (X-α)^(n-m) * num * (X-α)^m
    rw [hdenom_eq]
    have hpow : (Polynomial.X - Polynomial.C α) ^ n =
        (Polynomial.X - Polynomial.C α) ^ (n - m) * (Polynomial.X - Polynomial.C α) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hm_le]
    rw [hpow]
    ring
  · -- natDegree(p) ≤ n
    rcases hf with ⟨_, hinfty⟩
    rcases hinfty with rfl | hnopole
    · exact (hf0 rfl).elim
    -- noPoleAtInfinity: num.natDegree ≤ denom.natDegree = m
    have hnum_deg : f.num.natDegree ≤ m := by
      unfold noPoleAtInfinity at hnopole
      rw [hdenom_eq] at hnopole
      simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hnopole
      exact hnopole
    calc ((Polynomial.X - Polynomial.C α) ^ (n - m) * f.num).natDegree
        ≤ ((Polynomial.X - Polynomial.C α) ^ (n - m)).natDegree + f.num.natDegree := Polynomial.natDegree_mul_le
      _ = (n - m) * (Polynomial.X - Polynomial.C α).natDegree + f.num.natDegree := by
          rw [Polynomial.natDegree_pow]
      _ = (n - m) + f.num.natDegree := by simp [Polynomial.natDegree_X_sub_C]
      _ ≤ (n - m) + m := Nat.add_le_add_left hnum_deg _
      _ = n := Nat.sub_add_cancel hm_le

/-! ## Step 1: Raw function -/

/-- Raw function: extracts the polynomial part of (X-α)^n · f.
This is the underlying function before we prove it's linear. -/
def partialClearPolesFun (α : Fq) (n : ℕ)
    (f : RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    Polynomial.degreeLT Fq (n + 1) := by
  have hpoly := mul_X_sub_pow_is_polynomial Fq α n f.val f.property
  refine ⟨hpoly.choose, ?_⟩
  have hdeg := hpoly.choose_spec.2
  simp only [Polynomial.mem_degreeLT]
  calc hpoly.choose.degree
      ≤ hpoly.choose.natDegree := Polynomial.degree_le_natDegree
    _ ≤ n := Nat.cast_le.mpr hdeg
    _ < n + 1 := by exact_mod_cast Nat.lt_succ_self n

/-! ## Step 2: Specification lemma -/

/-- The polynomial extracted by partialClearPolesFun satisfies the key equation.
In RatFunc: algebraMap p = algebraMap (X-α)^n * f -/
lemma partialClearPolesFun_spec (α : Fq) (n : ℕ)
    (f : RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    algebraMap (Polynomial Fq) (RatFunc Fq) (partialClearPolesFun Fq α n f).val =
    algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ n) * f.val := by
  have hpoly := mul_X_sub_pow_is_polynomial Fq α n f.val f.property
  have hspec := hpoly.choose_spec.1
  have hdenom_ne : f.val.denom ≠ 0 := RatFunc.denom_ne_zero f.val
  have hdenom_alg_ne : algebraMap (Polynomial Fq) (RatFunc Fq) f.val.denom ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (Polynomial Fq) (RatFunc Fq))]
    exact hdenom_ne
  have hf_eq : f.val = algebraMap (Polynomial Fq) (RatFunc Fq) f.val.num /
                       algebraMap (Polynomial Fq) (RatFunc Fq) f.val.denom :=
    (RatFunc.num_div_denom f.val).symm
  rw [hf_eq, mul_div_assoc']
  have hspec_lifted := congrArg (algebraMap (Polynomial Fq) (RatFunc Fq)) hspec
  rw [map_mul, map_mul] at hspec_lifted
  rw [eq_div_iff hdenom_alg_ne]
  exact hspec_lifted.symm

/-! ## Step 3: Bundle as LinearMap -/

/-- Partial pole clearing: maps f to the polynomial part of (X-α)^n · f.
This is the linear map version bundled with linearity proofs. -/
def partialClearPoles (α : Fq) (n : ℕ) :
    RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1) →ₗ[Fq]
    Polynomial.degreeLT Fq (n + 1) where
  toFun := partialClearPolesFun Fq α n
  map_add' := fun f g => by
    apply Subtype.ext
    apply IsFractionRing.injective (Polynomial Fq) (RatFunc Fq)
    rw [Submodule.coe_add, map_add]
    rw [partialClearPolesFun_spec, partialClearPolesFun_spec, partialClearPolesFun_spec]
    -- Goal: (X-α)^n * ↑(f + g) = (X-α)^n * ↑f + (X-α)^n * ↑g
    -- Need to unfold ↑(f + g) = ↑f + ↑g first
    simp only [Submodule.coe_add]
    ring
  map_smul' := fun c f => by
    apply Subtype.ext
    apply IsFractionRing.injective (Polynomial Fq) (RatFunc Fq)
    rw [SetLike.val_smul, RingHom.id_apply]
    rw [Algebra.smul_def, map_mul]
    rw [partialClearPolesFun_spec, partialClearPolesFun_spec]
    -- Goal: (X-α)^n * ↑(c • f) = algebraMap c * ((X-α)^n * ↑f)
    simp only [SetLike.val_smul, Algebra.smul_def]
    -- Normalize algebraMap paths: algebraMap Fq (RatFunc Fq) = algebraMap Fq[X] (RatFunc Fq) ∘ algebraMap Fq Fq[X]
    simp only [← IsScalarTower.algebraMap_apply Fq (Polynomial Fq) (RatFunc Fq)]
    ring

/-- Alias: partialClearPoles uses partialClearPolesFun -/
lemma partialClearPoles_spec (α : Fq) (n : ℕ)
    (f : RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    algebraMap (Polynomial Fq) (RatFunc Fq) (partialClearPoles Fq α n f).val =
    algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ n) * f.val :=
  partialClearPolesFun_spec Fq α n f

/-- The pole clearing map is injective: if the cleared polynomials are equal, f = g.

The proof uses the fact that if p_f = p_g where (X-α)^n * num = p * denom,
then (X-α)^n * f = (X-α)^n * g (as RatFunc), hence f = g by cancellativity. -/
lemma partialClearPoles_injective (α : Fq) (n : ℕ) :
    Function.Injective (partialClearPoles Fq α n) := by
  intro f g heq
  -- From heq: the polynomials are equal
  have hp_eq : (partialClearPoles Fq α n f).val = (partialClearPoles Fq α n g).val :=
    congrArg Subtype.val heq
  -- Use the spec: algebraMap p_f = algebraMap (X-α)^n * f, same for g
  have hf_spec := partialClearPoles_spec Fq α n f
  have hg_spec := partialClearPoles_spec Fq α n g
  -- From hp_eq: algebraMap p_f = algebraMap p_g
  have halg_eq : algebraMap (Polynomial Fq) (RatFunc Fq) (partialClearPoles Fq α n f).val =
                 algebraMap (Polynomial Fq) (RatFunc Fq) (partialClearPoles Fq α n g).val := by
    rw [hp_eq]
  -- So algebraMap (X-α)^n * f = algebraMap (X-α)^n * g
  rw [hf_spec, hg_spec] at halg_eq
  -- Cancel (X-α)^n (nonzero) from both sides
  have hpow_ne : algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ n) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (Polynomial Fq) (RatFunc Fq))]
    exact pow_ne_zero n (Polynomial.X_sub_C_ne_zero α)
  have hval_eq : f.val = g.val := mul_left_cancel₀ hpow_ne halg_eq
  ext
  exact hval_eq

/-! ## Module.Finite Instance

The key instance: RRSpace_ratfunc_projective (n·[α]) is finite-dimensional.
-/

/-- For D = n·[linearPlace α] with n ≥ 0, RRSpace_ratfunc_projective D is finite-dimensional.

The proof constructs a linear injection into Fq[X]_{≤n}, which is finite-dimensional.
-/
instance RRSpace_ratfunc_projective_single_linear_finite (α : Fq) (n : ℕ) :
    Module.Finite Fq (RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) := by
  -- Strategy: embed into Polynomial.degreeLT Fq (n+1) which is finite-dim
  have hinj := partialClearPoles_injective Fq α n
  -- Module.Finite instance for degreeLT comes from Mathlib.RingTheory.Polynomial.DegreeLT
  haveI : Module.Finite Fq (Polynomial.degreeLT Fq (n + 1)) := inferInstance
  exact Module.Finite.of_injective (partialClearPoles Fq α n) hinj

/-! ## Helper lemmas for add_single_finite

These are used in the proof of RRSpace_ratfunc_projective_add_single_finite below.
-/

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

/-- The residue field at a linear place has dimension 1 over Fq.
Uses that κ(v) = Fq[X]/(X-α) ≅ Fq via evaluation at α. -/
lemma linearPlace_residue_finrank (α : Fq) :
    Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) (linearPlace α)) = 1 := by
  -- Fq[X]/span{X-Cα} ≃ₐ[Fq] Fq via quotientSpanXSubCAlgEquiv
  let e_alg : (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) ≃ₐ[Fq] Fq :=
    Polynomial.quotientSpanXSubCAlgEquiv α
  -- This gives finrank(Fq[X]/I) = finrank(Fq) = 1
  have h1 : Module.finrank Fq (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) = 1 := by
    rw [← Module.finrank_self Fq]
    exact LinearEquiv.finrank_eq e_alg.toLinearEquiv
  -- Now we need: finrank(κ(v)) = finrank(R/I) via the bijective algebraMap
  haveI hmax : (linearPlace (Fq := Fq) α).asIdeal.IsMaximal := (linearPlace α).isMaximal
  have hbij := Ideal.bijective_algebraMap_quotient_residueField (linearPlace (Fq := Fq) α).asIdeal
  -- Build RingEquiv from the bijective algebraMap
  let e_ring : (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) ≃+*
      residueFieldAtPrime (Polynomial Fq) (linearPlace α) :=
    RingEquiv.ofBijective _ hbij
  -- Upgrade to AlgEquiv: need to show algebraMap commutes
  have hcomm : ∀ c : Fq, e_ring (algebraMap Fq (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) c) =
      algebraMap Fq (residueFieldAtPrime (Polynomial Fq) (linearPlace α)) c := fun c => by
    simp only [e_ring, RingEquiv.ofBijective_apply]
    rfl
  let e_alg' : (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) ≃ₐ[Fq]
      residueFieldAtPrime (Polynomial Fq) (linearPlace α) :=
    AlgEquiv.ofRingEquiv hcomm
  rw [← h1]
  exact LinearEquiv.finrank_eq e_alg'.symm.toLinearEquiv

/-- Finiteness for D + [v] when D is finite-dim and v is a linear place.

The proof uses Module.Finite.of_submodule_quotient: if N ⊆ M is a submodule and both
N and M/N are Module.Finite, then M is Module.Finite.

We take M = L(D + [α]), N = LD (the embedding of L(D)).
- N ≅ L(D) is finite by hypothesis
- M/N injects into κ(α) which has dimension 1 (from gap bound proof structure)
-/
instance RRSpace_ratfunc_projective_add_single_finite (α : Fq)
    (D : DivisorV2 (Polynomial Fq))
    [hD : Module.Finite Fq (RRSpace_ratfunc_projective D)] :
    Module.Finite Fq (RRSpace_ratfunc_projective (D + DivisorV2.single (linearPlace α) 1)) := by
  let v := linearPlace (Fq := Fq) α
  let big := RRSpace_ratfunc_projective (D + DivisorV2.single v 1)
  let small := RRSpace_ratfunc_projective D

  -- small ≤ big as submodules of RatFunc Fq
  have hmono : small ≤ big := RRSpace_ratfunc_projective_mono Fq D α

  -- LD := small viewed as a submodule of ↥big
  let LD := small.comap big.subtype

  -- Step 1: LD is Module.Finite (isomorphic to small which is finite by hD)
  have h_range : small ≤ LinearMap.range big.subtype := by
    rw [Submodule.range_subtype]; exact hmono
  let e : LD ≃ₗ[Fq] small :=
    Submodule.comap_equiv_self_of_inj_of_le (Submodule.injective_subtype big) h_range
  haveI hLD : Module.Finite Fq LD := Module.Finite.equiv e.symm

  -- Step 2: The quotient big/LD is Module.Finite
  -- The quotient injects into κ(v) which has dimension 1

  -- Build the projective evaluation map ψ : ↥big →ₗ[Fq] κ(v)
  have h_proj_to_affine : ∀ f, f ∈ big →
      f ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1) :=
    fun f hf => hf.1
  let φ := evaluationMapAt_complete (R := Polynomial Fq) (K := RatFunc Fq) v D
  let ψ : ↥big →ₗ[Fq] residueFieldAtPrime (Polynomial Fq) v := {
    toFun := fun x => φ ⟨x.val, h_proj_to_affine x.val x.property⟩
    map_add' := fun x y => by
      have := φ.map_add ⟨x.val, h_proj_to_affine x.val x.property⟩
          ⟨y.val, h_proj_to_affine y.val y.property⟩
      convert this using 1 <;> rfl
    map_smul' := fun c x => by
      have h1 : (c • x).val = (algebraMap Fq (Polynomial Fq) c) • x.val :=
        (IsScalarTower.algebraMap_smul (Polynomial Fq) c x.val).symm
      have hmem : (algebraMap Fq (Polynomial Fq) c) • x.val ∈
          RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1) :=
        Submodule.smul_mem _ _ (h_proj_to_affine x.val x.property)
      have h2 : φ ⟨(algebraMap Fq (Polynomial Fq) c) • x.val, hmem⟩ =
          (algebraMap Fq (Polynomial Fq) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := by
        convert φ.map_smul (algebraMap Fq (Polynomial Fq) c) ⟨x.val, h_proj_to_affine x.val x.property⟩
      have h3 : (algebraMap Fq (Polynomial Fq) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ =
          c • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ :=
        IsScalarTower.algebraMap_smul (Polynomial Fq) c _
      simp only [RingHom.id_apply]
      calc φ ⟨(c • x).val, h_proj_to_affine (c • x).val (c • x).property⟩
          = φ ⟨(algebraMap Fq (Polynomial Fq) c) • x.val, hmem⟩ := by simp only [h1]
        _ = (algebraMap Fq (Polynomial Fq) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := h2
        _ = c • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := h3
  }

  -- Show LD ≤ ker(ψ)
  have hle := divisor_le_add_single D v
  have h_LD_le_ker : LD ≤ LinearMap.ker ψ := by
    intro x hx
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_comap] at hx
    have h_affine_mem : x.val ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := hx.1
    have h_in_affine_Dv : x.val ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1) :=
      RRModuleV2_mono_inclusion (Polynomial Fq) (RatFunc Fq) hle h_affine_mem
    let y_affine : RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := ⟨x.val, h_affine_mem⟩
    have hinc : (⟨x.val, h_in_affine_Dv⟩ : RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1)) =
        Submodule.inclusion (RRModuleV2_mono_inclusion (Polynomial Fq) (RatFunc Fq) hle) y_affine := rfl
    show ψ x = 0
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    have hx_eq : (⟨x.val, h_proj_to_affine x.val x.property⟩ :
        RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1)) =
        ⟨x.val, h_in_affine_Dv⟩ := rfl
    rw [hx_eq, hinc]
    exact LD_element_maps_to_zero v D y_affine

  -- Show ker(ψ) ≤ LD
  have h_ker_le_LD : LinearMap.ker ψ ≤ LD := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk] at hx
    have h_in_ker : (⟨x.val, h_proj_to_affine x.val x.property⟩ :
        RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1)) ∈
        LinearMap.ker φ := hx
    rw [kernel_evaluationMapAt_complete_proof, LinearMap.mem_range] at h_in_ker
    obtain ⟨y, hy⟩ := h_in_ker
    rw [Submodule.mem_comap, Submodule.coe_subtype]
    have hval : y.val = x.val := congrArg Subtype.val hy
    have h_affine : x.val ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := by
      rw [← hval]; exact y.property
    have h_infty : x.val = 0 ∨ noPoleAtInfinity x.val := x.property.2
    exact ⟨h_affine, h_infty⟩

  -- LD = ker(ψ)
  have h_eq_ker : LD = LinearMap.ker ψ := le_antisymm h_LD_le_ker h_ker_le_LD

  -- κ(v) is finite-dimensional over Fq (dimension 1)
  haveI hκv_finite : Module.Finite Fq (residueFieldAtPrime (Polynomial Fq) v) := by
    have hfr : Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) v) = 1 :=
      linearPlace_residue_finrank Fq α
    have hpos : 0 < Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) v) := by omega
    exact Module.finite_of_finrank_pos hpos

  -- The quotient big/LD injects into κ(v), so it's finite
  haveI hquot : Module.Finite Fq (↥big ⧸ LD) := by
    let desc := Submodule.liftQ LD ψ h_LD_le_ker
    have h_desc_inj : Function.Injective desc := by
      rw [← LinearMap.ker_eq_bot]
      have hker := Submodule.ker_liftQ LD ψ h_LD_le_ker
      rw [hker, h_eq_ker, Submodule.mkQ_map_self]
    exact Module.Finite.of_injective desc h_desc_inj

  -- Apply Module.Finite.of_submodule_quotient
  exact Module.Finite.of_submodule_quotient LD

/-! ## Zero Divisor Finiteness

The base case: RRSpace_ratfunc_projective 0 is 1-dimensional (just the constants).
-/

/-- RRSpace_ratfunc_projective 0 is finite-dimensional (dimension 1). -/
instance RRSpace_ratfunc_projective_zero_finite :
    Module.Finite Fq (RRSpace_ratfunc_projective (0 : DivisorV2 (Polynomial Fq))) := by
  -- L(0) consists of functions with no poles and no pole at infinity
  -- These are exactly the constants: k ⊆ L(0) ⊆ k
  -- So dim L(0) = 1
  -- Use the single linear place instance with n = 0
  have h_eq : (0 : DivisorV2 (Polynomial Fq)) =
      ((0 : ℕ) : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) 0) 1 := by simp
  rw [h_eq]
  exact RRSpace_ratfunc_projective_single_linear_finite Fq 0 0

end RiemannRochV2
