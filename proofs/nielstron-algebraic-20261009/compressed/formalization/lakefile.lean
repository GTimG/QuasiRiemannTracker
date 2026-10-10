import Lake
open Lake DSL
package QRH where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
-- These are source slices of immutable, separately pinned upstream checkouts.
-- Exact commits and OpenAI compatibility patches are in ../audit/.
lean_lib OAI where
  srcDir := "../upstream/openai-math/lean"
lean_lib RellichKondrachov where
  srcDir := ".lake/packages/rellich-kondrachov"
lean_lib MathlibExtensions where
  srcDir := ".lake/packages/rellich-kondrachov"
@[default_target] lean_lib QRH
