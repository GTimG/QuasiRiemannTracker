/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/Unramified/SphericalEulerNormalization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.UnramifiedSphericalImage

@[expose] public section

namespace DedekindZetaZeroFree.KPGlobalGoodEulerFactor

open KPLocalStoneVonNeumann KPLocalPrincipalSeries MeasureTheory
open scoped Valued

noncomputable section

def convergenceChamber : Set ℂ := {s | -(1 / 6 : ℝ) < s.re}

def sphericalCoefficient (q m : ℝ) (s : ℂ) : ℂ :=
  (m : ℂ) *
    (1 - Complex.exp ((-2 - 6 * s) * (Real.log q : ℂ))) /
    (1 - Complex.exp ((-1 - 6 * s) * (Real.log q : ℂ)))

def traceSelfDualIntegerMass (q : ℝ) (differentExponent : ℕ) : ℝ :=
  q ^ (-(differentExponent : ℝ) / 2)

@[simp] theorem traceSelfDualIntegerMass_unramified (q : ℝ) :
    traceSelfDualIntegerMass q 0 = 1 := by
  simp [traceSelfDualIntegerMass]

variable {K : Type*} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

end

end DedekindZetaZeroFree.KPGlobalGoodEulerFactor
