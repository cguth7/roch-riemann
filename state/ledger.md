# Ledger Vol. 3.3 (Cycles 133+) - Full Adeles Compactness

**Ultimate Goal**: Formalize Riemann-Roch for curves over finite fields in Lean 4 — **no axioms, no sorries**.

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*
*For Cycles 80-99, see `state/ledger_archive.md` (Vol. 3.1)*
*For Cycles 100-117, see `state/ledger_archive.md` (Vol. 3.2 Part 1 - AllIntegersCompact)*
*For Cycles 118-132, see `state/ledger_archive.md` (Vol. 3.2 Part 2 - FullAdeles Foundation)*

---

## 🎯 NEXT CLAUDE: Start Here (Cycle 138)

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
- ✅ Main theorem structure complete (modulo 2 helper lemmas)

### What's Needed (2 sorries remain)

**`exists_finite_integral_translate` (line ~1012)**
- For any finite adele a, find k ∈ K such that a - diag(k) is integral at all finite places
- Approach: Use CRT for PIDs - only finitely many bad places

**`exists_finite_integral_translate_with_infty_bound` (line ~1022)**
- Same as above, but with bound on |k|_∞
- Key insight: CRT solution can be chosen with deg(num) < deg(denom)
- This gives |k|_∞ < 1

### Axioms Used
| Axiom | Purpose |
|-------|---------|
| `[AllIntegersCompact Fq[X] (RatFunc Fq)]` | Finite adeles compactness |
| `[Finite (Valued.ResidueField (FqtInfty Fq))]` | Infinity compactness |

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
