/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/RankOne/TameSphericalFactor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.UnramifiedSphericalImage
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.RootParameterCompactPicture

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneTameSphericalFactor

open scoped Valued
open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPRankOneRootParameter
open KPLocalStoneVonNeumann KPLocalGoodSphericalImage

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

def haarMass (μ : Measure K) : ℝ :=
  (μ ((valuation K).integer : Set K)).toReal

def forwardFactorInRoot (μ : Measure K) (z : ℂ) : ℂ :=
  (haarMass K μ : ℂ) *
    (1 - (residueCardinality K : ℂ)⁻¹ *
      ((residueCardinality K : ℂ)⁻¹ * z ^ 6)) /
    (1 - (residueCardinality K : ℂ)⁻¹ * z ^ 6)

def forwardFactor (μ : Measure K) (s : ℂ) : ℂ :=
  forwardFactorInRoot K μ (r K s)

def IsSphericalVector
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign)
    (φ : compactPicture A P I ε) : Prop :=
  (∀ s : ℂ,
    ((compactTrivialization A P I ε s φ).val 1).val 1 = 1) ∧
  ∀ (s : ℂ) (k : I.compact.toOpenSubgroup),
    principalSeries A P ε s (k : G)
      (compactTrivialization A P I ε s φ) =
        compactTrivialization A P I ε s φ

end
end DedekindZetaZeroFree.KPRankOneTameSphericalFactor
