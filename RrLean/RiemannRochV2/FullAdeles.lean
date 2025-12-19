/-
# Full Adele Ring - Main Import File

This file re-exports from the split files:
- FullAdelesBase.lean: General definitions, basic FqInstance (COMPILES ✅)
- FullAdelesCompact.lean: Compactness, weak approximation (HAS ERRORS ❌)

Split for faster incremental builds.
-/

import RrLean.RiemannRochV2.FullAdelesBase
-- import RrLean.RiemannRochV2.FullAdelesCompact  -- Commented out until errors fixed
