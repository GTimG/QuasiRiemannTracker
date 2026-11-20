/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/DyadicLength.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DyadicColumns.lean.
-/

namespace DedekindZetaZeroFree.LargeSieve.Vendor

noncomputable def dyadicLength (X : ℝ) : ℕ := ⌈Real.log X / Real.log 2⌉₊

end DedekindZetaZeroFree.LargeSieve.Vendor
