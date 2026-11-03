/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/ExceptionalParameterExponents.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalExceptionalParameter

open KPGlobalEisensteinData
open scoped NNReal

def realLogPower (r : ℝ) (u : ℂ) : ℂ :=
  Complex.exp (u * (Real.log r : ℂ))

end DedekindZetaZeroFree.KPGlobalExceptionalParameter

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalExceptionalParameter

open KPGlobalEisensteinData
open scoped NNReal

def sourceExponent (s : ℂ) : ℂ := 2 / 3 + s

def weylExponent (s : ℂ) : ℂ := 1 / 3 - s

theorem source_multiplier (r : ℝ) (hr : 0 < r) (s : ℂ) :
    realLogPower r (1 / 2) * realLogPower r (1 / 6) * realLogPower r s =
      realLogPower r (sourceExponent s) := by
  unfold realLogPower sourceExponent
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

end DedekindZetaZeroFree.KPGlobalExceptionalParameter

end
end
