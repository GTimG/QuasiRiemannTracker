import Lake
open Lake DSL
package QRH where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]
require «rellich-kondrachov» from git
  "https://github.com/abenenson/rellich-kondrachov.git" @ "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23"
require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "c39a751132c88b6e8080b74c74023fd95b3d8be0"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI where
  roots := #[`OAI.NumberTheory.DirichletL.Nonvanishing]
lean_lib Challenge
lean_lib Candidate where
  globs := #[`Candidate.+]
lean_lib Solution
