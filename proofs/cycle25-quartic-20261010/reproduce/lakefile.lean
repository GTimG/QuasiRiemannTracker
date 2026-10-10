import Lake
open Lake DSL

package Cycle25 where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Sources are authenticated by dependencies/dependency-pins.json.
require «rellich-kondrachov» from ".lake/packages/rellich-kondrachov"
require PrimeNumberTheoremAnd from ".lake/packages/PrimeNumberTheoremAnd"
require mathlib from ".lake/packages/mathlib"

lean_lib OAI
lean_lib ZetaZeroFree
@[default_target] lean_lib Cycle25
