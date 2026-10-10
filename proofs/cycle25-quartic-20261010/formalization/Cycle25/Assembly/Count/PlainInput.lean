import Cycle25.Assembly.Count.MomentDetectorPlainMarkedFineField
import Cycle25.Energy.Endpoint
import Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedField
namespace OAI.SevenEighths.Cycle25ProbeDetectorPlainMarkedFineField
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter HeckeFamily CenteredMomentEnergyBands
open Cycle25ProbeFinalAssembly Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentDetectorPlainMomentParameters
open Cycle25CenteredMomentDetectorPlainSlotProfile

/-- One mesh works for all fixed detector inducing characters and the eventual
finite physical slot count. No improved terminal bound is used. -/
theorem terminal_plain_input {D : Cycle25.Weighted.MomentData}
    (S : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤HeckeZeroSupremum.beta) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain) :
    weighted_PositiveFineSourceInput S κplain (Cycle25.Energy.commonMesh 2 0 1 (weighted_stageError D)) := by
  intro bΦ hbΦ
  obtain ⟨J,controls,he⟩ := Cycle25.Energy.terminal_positive_at (α:=Fin D.N)
    S.modulus ⊤ le_top (fun x=>conj (S.W x)) 1 2 (1/4) (9/4) bΦ 0 1
    (33/50) (33/50) 2 κplain (weighted_stageError D)
    (by norm_num) (weighted_conjugate_source_support S)
    (HeckeInverseAmplification.conjugate_profile_smooth _ (S.W.smooth ⊤)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbΦ
    (by norm_num) (by norm_num) hk hk1 (weighted_fixed_parameters D).2.2.1 hbeta hκbeta
  refine ⟨J,controls,?_⟩
  intro η₀
  obtain ⟨C,hC,hbound⟩ := he η₀ (weighted_sourceFixedIdeal S) (weighted_sourceFixedIdeal_le_modulus S)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero S) η₀)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) η₀)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 S))
  exact ⟨C,hC,hbound.mono (fun _ hz=>hz.2)⟩

open Cycle25ProbeDetectorPlainUnmarkedField CenteredMomentEnergyCappedWidthInduction
/-- Unmarked plain input extracted from the zero-slot part of the completed
Cycle25 certificate; fixed inducing characters are removed by the dictionary. -/
theorem terminal_zero_input {D : Cycle25.Weighted.MomentData}
    (S : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤HeckeZeroSupremum.beta) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain) :
    ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal S) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A := by
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate (α:=Fin D.N)
    S.modulus ⊤ le_top (fun x=>conj (S.W x)) 1 2 (1/4) (9/4) weighted_radialSupportUpper
    0 1 (33/50) (33/50) 2 κplain (weighted_stageError D)
    (by norm_num) (weighted_conjugate_source_support S)
    (HeckeInverseAmplification.conjugate_profile_smooth _ (S.W.smooth ⊤))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) weighted_radialSupportUpper_spec.1
    (by norm_num) (by norm_num) hk (weighted_fixed_parameters D).2.2.1 hbeta hκbeta
  obtain ⟨J,controls,he⟩ := certified_terminal (α:=Fin D.N) S.modulus ⊤ le_top
    (fun x=>conj (S.W x)) 2 (1/4) (9/4) weighted_radialSupportUpper 0 1 (33/50) (33/50)
    2 κplain (weighted_stageError D) (by norm_num) (by norm_num) (by linarith)
    (weighted_fixed_parameters D).2.2.1 hcert
  refine ⟨J,controls,?_⟩
  intro η₀
  obtain ⟨Cz,Cp,hCz,hCp,hbound⟩ := he η₀ (weighted_sourceFixedIdeal S) (weighted_sourceFixedIdeal_le_modulus S)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero S) η₀)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) η₀)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 S))
  exact ⟨Cz,hCz,hbound.mono (fun _ hz=>hz.2.1)⟩
end
end OAI.SevenEighths.Cycle25ProbeDetectorPlainMarkedFineField
