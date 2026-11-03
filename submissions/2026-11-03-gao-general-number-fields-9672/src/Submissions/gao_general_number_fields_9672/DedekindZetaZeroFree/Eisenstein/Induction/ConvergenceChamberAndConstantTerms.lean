/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/ConvergenceChamberAndConstantTerms.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPEisensteinChamber

open MeasureTheory KPGlobalEisensteinData

def chamber : Set ℂ := {s | (1 / 3 : ℝ) < s.re}

section AlgebraicHelpers

variable {G Q A Y : Type*} [Group G] [MeasurableSpace A] [MeasurableSpace Y]

end AlgebraicHelpers
end DedekindZetaZeroFree.KPEisensteinChamber

end
