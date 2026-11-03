/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/AdditiveFundamentalDomainMeasure.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Lattices.TraceCovolumeHaarCancellation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Quotients.CompactOpenLevelTori

@[expose] public section

namespace DedekindZetaZeroFree.QuotientProbability
noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

local instance quotientProbability_finiteMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
local instance quotientProbability_adeleMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
local instance quotientProbability_quotientMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := borel _

def finiteLevelInfiniteHaar (F : Type) [Field F] [NumberField F] :
    Measure (mixedEmbedding.mixedSpace F) :=
  ENNReal.ofReal (PoissonArch.haarScalar F) • volume

def additiveProductHaar (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) : Measure (AdeleRing (𝓞 F) F) :=
  Measure.map
    (fun x : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1, x.2) :
        AdeleRing (𝓞 F) F))
    ((finiteLevelInfiniteHaar F).prod μf)

def additiveQuotientMeasureFromDomain (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) (Ω : Set (AdeleRing (𝓞 F) F)) :
    Measure (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) :=
  Measure.map (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F))
    ((additiveProductHaar F μf).restrict Ω)

def finiteLevelProductDomain {F : Type} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (D : Set (mixedEmbedding.mixedSpace F)) : Set (AdeleRing (𝓞 F) F) :=
  {a | InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 ∈ D ∧ a.2 ∈ K}

end
end DedekindZetaZeroFree.QuotientProbability
