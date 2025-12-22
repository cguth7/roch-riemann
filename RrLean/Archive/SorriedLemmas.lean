/-!
# Archived Sorried Lemmas

This file contains lemmas with `sorry` that were removed from the main codebase.
These are NOT on the P¹ Riemann-Roch critical path and are preserved here for
potential future development.

## Contents

1. `LRatFunc_eq_zero_of_neg_deg` - General negative degree vanishing (needs product formula)
2. `RRSpace_ratfunc_eq_bot_of_neg_deg` - Depends on above
3. `RRSpace_proj_subsingleton_of_neg_deg` - Depends on above
4. `ell_proj_zero_of_neg_deg` - Depends on above
5. `residueAtIrreducible` - Residue at higher-degree places (needs extension fields)
6. `residue_sum_eq_zero` - Full residue theorem (needs above)
7. `principal_divisor_degree_eq_zero_INCORRECT_DO_NOT_USE` - Known to be FALSE
8. `finrank_dual_eq` - Wrong approach for Serre duality

Note: The sorry in `exists_finite_integral_translate_with_infty_bound` (FullAdelesCompact.lean)
is kept in place because:
- It's only in the `bound < 1` branch
- All actual uses call it with `bound = 1`
- It's not on the P¹ critical path anyway
-/

-- This file is documentation only. The actual lemma code was removed from:
-- - RatFuncPairing.lean (lines 1896-1988)
-- - Residue.lean (lines 1282-1284, 1397-1401)
-- - ProductFormula.lean (lines 111-116)
-- - TraceDualityProof.lean (lines 144-150)
