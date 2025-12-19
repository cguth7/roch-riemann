# Ledger Vol. 3.3 (Cycles 133+) - Full Adeles Compactness

**Ultimate Goal**: Formalize Riemann-Roch for curves over finite fields in Lean 4 — **no axioms, no sorries**.

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*
*For Cycles 80-99, see `state/ledger_archive.md` (Vol. 3.1)*
*For Cycles 100-117, see `state/ledger_archive.md` (Vol. 3.2 Part 1 - AllIntegersCompact)*
*For Cycles 118-132, see `state/ledger_archive.md` (Vol. 3.2 Part 2 - FullAdeles Foundation)*

---

## 🎯 NEXT CLAUDE: Start Here (Cycle 136)

### Current State
**REVERTED TO CYCLE 133** - Cycle 134 introduced broken code (see postmortem below).

Build: ✅ Compiles with 2 sorries in FullAdeles.lean

### What's Done
- ✅ `fq_discrete_in_fullAdeles` - K is discrete in full adeles
- ✅ `fq_closed_in_fullAdeles` - K is closed in full adeles

### What's Needed (2 sorries remain)

**1. `isCompact_integralFullAdeles` - Infinity compactness (line ~727)**
- Need: RankOne instance for FqtInfty valuation
- Need: DVR instance for integer ring
- Need: Finite residue field
- Pattern: Use `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`

**2. `exists_translate_in_integralFullAdeles` - Weak approximation (line ~788)**
- For any adele a, find x ∈ K such that a - diag(x) is integral
- Uses: Density of K in completions + CRT for PIDs

### Axioms Used
| Axiom | Purpose |
|-------|---------|
| `[AllIntegersCompact Fq[X] (RatFunc Fq)]` | Finite adeles compactness |
| `[Finite (Valued.ResidueField (FqtInfty Fq))]` | Infinity compactness |

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
  ⚪ isCompact_integralFullAdeles  -- integral adeles compact (sorry)
  ⚪ exists_translate_in_integralFullAdeles  -- weak approximation (sorry)
```

---

## References

- `AllIntegersCompactProof.lean` - Pattern for compactness via DVR+complete+finite
- `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean` - compactSpace_iff lemma
- `Valuation.nonempty_rankOne_iff_mulArchimedean` - KEY: gets RankOne without ℝ≥0 literals
