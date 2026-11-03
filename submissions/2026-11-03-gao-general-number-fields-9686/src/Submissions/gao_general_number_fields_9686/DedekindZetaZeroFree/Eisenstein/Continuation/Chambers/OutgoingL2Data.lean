/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/Chambers/OutgoingL2Data.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPChamberOutgoingL2

open MeasureTheory Filter Topology
open scoped ENNReal

def compactDecayRate (d : ℕ) (L : Set ℂ) : ℝ :=
  (d : ℝ) * sInf ((fun s : ℂ => (1 / 3 : ℝ) + 2 * s.re) '' L)

def outgoingFactor (d : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((d : ℂ) * ((2 / 3 : ℂ) - 2 * s) * (t : ℂ))

section Charts
variable (F : Type*) [Field F] [NumberField F]
variable {G Q N A H : Type*} [Group G] [MeasurableSpace N] [Finite A]
    [AddCommGroup H] [Module ℂ H]

end Charts

end DedekindZetaZeroFree.KPChamberOutgoingL2

end
