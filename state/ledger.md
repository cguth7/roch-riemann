# Ledger Vol. 3.3 (Cycles 133+) - Full Adeles Compactness

**Ultimate Goal**: Formalize Riemann-Roch for curves over finite fields in Lean 4 — **no axioms, no sorries**.

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*
*For Cycles 80-99, see `state/ledger_archive.md` (Vol. 3.1)*
*For Cycles 100-117, see `state/ledger_archive.md` (Vol. 3.2 Part 1 - AllIntegersCompact)*
*For Cycles 118-132, see `state/ledger_archive.md` (Vol. 3.2 Part 2 - FullAdeles Foundation)*

---

## 🎯 NEXT CLAUDE: Start Here (Cycle 140)

### Current State
Build: ✅ Compiles with 2 sorries in FullAdeles.lean

### What's Done
- ✅ `fq_discrete_in_fullAdeles` - K is discrete in full adeles
- ✅ `fq_closed_in_fullAdeles` - K is closed in full adeles
- ✅ `isCompact_integralFullAdeles` - Integral adeles are compact (Cycle 136!)
- ✅ `isOpen_ball_le_one_FqtInfty` - Closed unit ball is open (discrete valuation)
- ✅ `denseRange_inftyRingHom` - K is dense in FqtInfty
- ✅ `exists_approx_in_ball_infty` - Can approximate any FqtInfty element to within O_∞
- ✅ `polynomial_integral_at_finite_places` - Polynomials are integral at all finite places
- ✅ `exists_local_approximant` - For any a_v ∈ K_v, ∃ y ∈ K with a_v - y ∈ O_v
- ✅ Main theorem structure complete (modulo 2 helper lemmas)
- ✅ **Cycle 139**: Proof structure for CRT with enlarged set approach

### What's Needed (2 sorries remain)

**`exists_finite_integral_translate` (line ~1100)**
- For any finite adele a, find k ∈ K such that a - diag(k) is integral at all finite places
- **Cycle 139 progress**: Set up D = ∏ denominators, proved D·y_v ∈ R
- **Remaining**: Apply CRT with enlarged set T = S ∪ {primes dividing D outside S}

**`exists_finite_integral_translate_with_infty_bound` (line ~1140)**
- Same as above, but with bound on |k|_∞
- Depends on resolving the first sorry

### Cycle 139 CRT Approach (CORRECT, needs formalization)
1. S = bad places (finite), get y_v ∈ K with a_v - y_v ∈ O_v for v ∈ S
2. D = ∏_{v∈S} denom(y_v) - clears all denominators
3. T = S ∪ {primes dividing D but not in S} - still finite
4. CRT targets:
   - For v ∈ S: target Py_v = D·y_v (mod p_v^{N_v}) where N_v > val_v(D)
   - For w ∈ T\S: target 0 (mod p_w^{val_w(D)})
5. Apply `exists_forall_sub_mem_ideal` to get P
6. Set k = P/D
7. Verify: val_v(k - y_v) ≥ 0 for v ∈ S, val_w(k) ≥ 0 for w ∉ S

**Key lemma needed**: `{v : HeightOneSpectrum | v.intValuation D < 1}.Finite`
(set of primes dividing D is finite - should follow from UFD properties)

### Axioms Used
| Axiom | Purpose |
|-------|---------|
| `[AllIntegersCompact Fq[X] (RatFunc Fq)]` | Finite adeles compactness |
| `[Finite (Valued.ResidueField (FqtInfty Fq))]` | Infinity compactness |

---

## Cycle 139 Summary

**Goal**: Prove `exists_finite_integral_translate` via CRT approach

**Status**: 🔶 PARTIAL - Proof structure complete, CRT application pending

**Key accomplishments**:
1. Rejected principal parts / pole degree approaches (too complex for Lean)
2. Identified correct approach: CRT with enlarged set T
3. Set up proof structure with D = product of denominators
4. Proved `hDy_in_R`: D · y_v ∈ R for all v ∈ S (key intermediate step)
5. Documented the CRT application strategy

**Key insight**:
- Don't try to define n_v = ⌈-val_v(a_v)⌉ for a_v ∈ K_v (completion elements)
- Work entirely with global elements y_v ∈ K from density
- Enlarge the set to include ALL primes dividing D, not just S
- CRT gives P with the right divisibility properties, then k = P/D works

**What remains for Cycle 140**:
1. Construct T = {v : HeightOneSpectrum | v.intValuation D < 1} and prove finite
2. Set up CRT index type and targets
3. Apply `exists_forall_sub_mem_ideal`
4. Verify the valuation conditions

**Mathlib APIs needed**:
- `UniqueFactorizationMonoid.normalizedFactors` or `primeFactors` for factorization
- `exists_forall_sub_mem_ideal` for CRT
- `intValuation` properties for relating polynomial primes to HeightOneSpectrum

---

## Cycle 138 Summary

**Goal**: Prove weak approximation lemmas (`exists_finite_integral_translate`)

**Status**: 🔶 PARTIAL - Proved density step, CRT gluing still needed

**Key accomplishments**:
1. Proved `exists_local_approximant` - For any a_v ∈ K_v, ∃ y ∈ K with a_v - y ∈ O_v
   - Uses `UniformSpace.Completion.denseRange_coe` for density of K in K_v
   - Uses `Valued.isOpen_valuationSubring` to show O_v is open
   - Uses `DenseRange.exists_mem_open` to get the approximant

2. Restructured proof approach based on external feedback:
   - **Abandoned**: Principal part extraction (requires Laurent series machinery)
   - **Abandoned**: Induction on bad set (plumbing hell, bad set depends on a)
   - **Adopted**: Density + CRT gluing approach

**Key insight discovered**:
- The naive density approach doesn't quite work: each y_v from `exists_local_approximant`
  might have poles outside S, creating new bad places
- To avoid this, we actually NEED y_v with poles only at v (i.e., principal parts)
- This means partial fractions are unavoidable for the global gluing step
- The density lemma IS useful as a stepping stone, but not sufficient alone

**What remains for Cycle 139**:
- Either formalize partial fractions for RatFunc Fq, OR
- Find an alternative approach that controls pole locations

**Key mathlib APIs used**:
- `UniformSpace.Completion.denseRange_coe` - K is dense in completion
- `Valued.isOpen_valuationSubring` - valuation ring is open
- `DenseRange.exists_mem_open` - density implies intersection with open sets

---

## Cycle 137 Summary

**Goal**: Work on weak approximation (`exists_translate_in_integralFullAdeles`)

**Status**: 🔶 PARTIAL - Main structure complete, 2 helper sorries remain

**Key accomplishments**:
1. Proved `isOpen_ball_le_one_FqtInfty` - {v ≤ 1} = {v < exp(1)} for discrete valuation
2. Proved `denseRange_inftyRingHom` - density of K in completion
3. Proved `exists_approx_in_ball_infty` - existence of approximation at infinity
4. Proved `polynomial_integral_at_finite_places` - polynomials integral at finite places
5. Structured main theorem proof using:
   - Step 1: Find P with |a.2 - P|_∞ ≤ 1 (done via density)
   - Step 2: Work with b = a - diag(P)
   - Step 3: Find z clearing finite places with |z|_∞ ≤ 1 (needs CRT lemma)
   - Step 4: Combine x = P + z, verify via ultrametric inequality

**Key techniques used**:
- `UniformSpace.Completion.denseRange_coe` for density
- `Valued.isClopen_ball` for openness of valuation balls
- `WithZero.exp_lt_exp` and `omega` for discrete value group reasoning
- `Valued.v.map_sub_le_max'` for ultrametric inequality

**Remaining work for Cycle 138**:
- Prove CRT-based lemmas using `IsDedekindDomain.exists_forall_sub_mem_ideal`
- Key challenge: targets are in K_v (completion), need density argument

---

## Cycle 136 Summary

**Goal**: Prove infinity compactness (`isCompact_integralFullAdeles`)

**Status**: ✅ COMPLETE

**Key accomplishments**:
1. Proved `valued_FqtInfty_eq_inftyValuationDef` - connects Valued.v to inftyValuationDef
2. Proved `isNontrivial_FqtInfty` - 1/X has valuation exp(-1) < 1
3. Defined `rankOne_FqtInfty` - from MulArchimedean via `nonempty_rankOne_iff_mulArchimedean`
4. Proved `range_nontrivial_FqtInfty` - valuation range is nontrivial
5. Proved `isPrincipalIdealRing_integer_FqtInfty` - PID from non-dense ordering
6. Proved `isDiscreteValuationRing_integer_FqtInfty` - DVR with 1/X as uniformizer
7. Proved `completeSpace_integer_FqtInfty` - closed subset of complete space
8. Proved `isCompact_integralFullAdeles` - using compactSpace_iff theorem

**Pattern used** (same as AllIntegersCompactProof.lean):
```
CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ DVR 𝒪[K] ∧ Finite 𝓀[K]
```

**Key mathlib APIs**:
- `Valued.extension_extends` - connects valuation on completion to original
- `FunctionField.inftyValuation.X_inv` - v(1/X) = exp(-1)
- `Valuation.nonempty_rankOne_iff_mulArchimedean` - RankOne without ℝ≥0 literals
- `WithZero.exp_lt_exp` - ordering on exp values

---

## Cycle 135 Summary

**Goal**: Work on weak approximation (`exists_translate_in_integralFullAdeles`)

**Status**: ⚠️ DISCOVERED BUILD REGRESSION

**Findings**:
1. Cycle 134 commit (799bb5d) introduced broken code that never compiled
2. Used non-existent mathlib APIs:
   - `UniformSpace.Completion.coeRingHom_apply` ❌
   - `RatFunc.inv_X_ne_zero` ❌ (correct: `RatFunc.X_ne_zero`)
   - `WithZero.map_inv` ❌
3. Reverted FullAdeles.lean to Cycle 133 (aaa7633) which builds correctly

**Action Taken**: Reverted to Cycle 133 state

---

## Cycle 134 Postmortem

**What was attempted**:
- Prove `inftyValuation_isNontrivial` (X⁻¹ has valuation exp(-1) < 1)
- Get `rankOne_FqtInfty` via MulArchimedean
- Prove `instDVR_FqtInfty` (DVR with X⁻¹ as uniformizer)
- Prove `completeSpace_integer_FqtInfty`

**Why it failed**:
- Code used mathlib APIs that don't exist
- Commit was made without running build (stale cache issue?)

**Correct approach for Cycle 136**:
1. Use `RatFunc.X_ne_zero` (not `inv_X_ne_zero`)
2. For completion embedding, use `UniformSpace.Completion.coe_inj`
3. For valuation of inverse, use `map_inv₀` or direct calculation
4. Test build BEFORE committing

---

## Cycle 133 Summary

**Goal**: Complete infinity compactness for `isCompact_integralFullAdeles`

**Status**: 🔶 PARTIAL - Structure complete, blocked on ℝ≥0 tactics

**Progress**:
- Added imports for `WithZeroMulInt.toNNReal` and `LocallyCompact`
- Wrote full proof strategy in code comments
- Identified key approach: use `nonempty_rankOne_iff_mulArchimedean`

---

## Architecture Summary

```
FullAdeleRing Fq := FiniteAdeleRing Fq[X] (RatFunc Fq) × FqtInfty Fq

K = RatFunc Fq embeds diagonally:
  fqFullDiagonalEmbedding : K →+* FullAdeleRing

Key theorems (in FullAdeles.lean):
  ✅ fq_discrete_in_fullAdeles  -- K is discrete
  ✅ fq_closed_in_fullAdeles    -- K is closed
  ✅ isCompact_integralFullAdeles  -- integral adeles compact
  ⚪ exists_translate_in_integralFullAdeles  -- weak approximation (sorry)
```

---

## References

- `AllIntegersCompactProof.lean` - Pattern for compactness via DVR+complete+finite
- `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean` - compactSpace_iff lemma
- `Valuation.nonempty_rankOne_iff_mulArchimedean` - KEY: gets RankOne without ℝ≥0 literals
