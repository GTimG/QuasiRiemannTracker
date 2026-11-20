/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0. -/
import Candidate.C092.transport.ColoredGaussFrameProviderChildren
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussFrameProvider
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.TwistedRawSource QRH.Cycle092.RegularColoredForward
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) reindexSumDecEq {κ κ₂ : Type*} : DecidableEq (κ⊕κ₂) := Classical.decEq _
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem originalColumn_reindex (e : ι≃κ) (ω₁ ω₂ : Id→*₀ℂ)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal) (pool : ι→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id) (ν : ι→Id→ℂ)
    (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    frameOriginalColumn ω₁ ω₂ S H (fun k=>pool (e.symm k)) d hd R seed
      (fun k=>ν (e.symm k)) (fun k=>Wslot (e.symm k)) (fun k=>P (e.symm k)) W₁ W₂
      b X₁ X₂ Y₁ Y₂ =
    frameOriginalColumn ω₁ ω₂ S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  funext I
  unfold frameOriginalColumn finiteColumnCoefficient
  apply Finset.sum_nbij' (tunmap e) (tmap e)
  · intro v hv
    simp only [Finset.mem_filter,Fintype.mem_piFinset] at hv ⊢
    refine ⟨?_,?_⟩
    · exact (mem_pools_tunmap e pool (residualPool d.1 hd.1 (plainSupportPool b X₁ Y₁))
        (residualPool d.2 hd.2 (plainSupportPool b X₂ Y₂)) v).mpr hv.1
    · have hh := finiteTupleProduct_tmap e (tunmap e v)
      rw [tmap_tunmap] at hh
      exact hh.symm.trans hv.2
  · intro v hv
    simp only [Finset.mem_filter,Fintype.mem_piFinset] at hv ⊢
    refine ⟨?_,?_⟩
    · exact (mem_pools_tmap e pool (residualPool d.1 hd.1 (plainSupportPool b X₁ Y₁))
        (residualPool d.2 hd.2 (plainSupportPool b X₂ Y₂)) v).mpr hv.1
    · exact (finiteTupleProduct_tmap e v).trans hv.2
  · intro v _; exact tmap_tunmap e v
  · intro v _; exact tunmap_tmap e v
  · intro v _
    have h1 := tupleWeight_tmap e (punctureProduct S H) (tunmap e v)
    have h2 := profileCoefficient_tmap e R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed (tunmap e v)
    rw [tmap_tunmap] at h1 h2
    rw [h1,h2]
    rfl

theorem sourceColumn_reindex {a b : ℝ} (s : Source ι a b) (e : ι≃κ) (ha : 0<a)
    (ω₁ ω₂ : Id→*₀ℂ) (seed : Id) :
    sourceColumn (reindexSource s e) ha ω₁ ω₂ seed = sourceColumn s ha ω₁ ω₂ seed := by
  rw [sourceColumn_original,sourceColumn_original]
  exact originalColumn_reindex e ω₁ ω₂ s.S s.H s.pool s.d s.hd s.R seed s.ν s.Wslot s.P _ _ _ _ _ _ _

open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSectorLocalization CenteredMomentSecondEnergySplit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentCanonicalFirst
open CenteredMomentHeckeColumnWindow CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondRetainedAggregate

/-- Source-free form of the literal physical ledger; this permits dependent
    common-label transports without rewriting inside support certificates. -/
def physicalTerms (part : Bool) (S : Finset Id) (c : Id→ℂ) (ψ : Character)
    (χ₀ : RayFourExpansion.RayCharacter) (Q : Id) (m : HeckeFamily.O)
    (t K Tsec Z ξ H : ℝ) : ℝ :=
  ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
    ‖rhoC p.val.1‖ * ∑U : Finset (CommonIndex p.val.1 p.val.2),
      ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ‖physicalBlock ψ t S c p.val.1 p.val.2
          (commonLabels_supported S _ _ p.property).1
          (commonLabels_supported S _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
          (partRows part ψ χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          ballProfile K (fun i=>(n i:ℤ))‖

theorem groupedPartTerms_reindex {a b : ℝ} (s : Source ι a b) (e : ι≃κ) (ha : 0<a)
    (ω₁ ω₂ : Id→*₀ℂ) (part : Bool) (ψ : Character) (χ₀ : RayFourExpansion.RayCharacter)
    (Q : Id) (m : HeckeFamily.O) (t K Tsec Z ξ H : ℝ) :
    RootColoredSeed.groupedPartTerms part (reindexSource s e) ha ω₁ ω₂ ψ χ₀ Q m t K Tsec Z ξ H =
      RootColoredSeed.groupedPartTerms part s ha ω₁ ω₂ ψ χ₀ Q m t K Tsec Z ξ H := by
  have hc := sourceColumn_reindex s e ha ω₁ ω₂ 1
  have hA : RootColoredSeed.active (reindexSource s e) ha ω₁ ω₂ =
      RootColoredSeed.active s ha ω₁ ω₂ := by
    unfold RootColoredSeed.active
    rw [sourceColumns_reindex,hc]
  exact congrArg₂ (fun S c=>physicalTerms part S c ψ χ₀ Q m t K Tsec Z ξ H) hA hc

#print axioms sourceColumn_reindex
#print axioms groupedPartTerms_reindex
end
end QRH.Cycle092.ColoredGaussFrameProvider
