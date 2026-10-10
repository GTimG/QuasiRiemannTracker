import WeightedQRH.MomentTerminalInput
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.ProbeFinalAssemblyCertifiedBands
open HeckeFamily ProbeFinalAssembly
open CenteredMomentEnergyCertifiedExistence CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges CenteredMomentEnergyBands
open CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainSlotProfile
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
/-- Exact κ=3/4 certified terminal input for arbitrary new probe slots. -/
theorem weighted_terminal_certificate_two {D : WeightedQRH.MomentData}
    (F : WeightedSourceData D) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top
      (fun x=>conj (F.W x)) 2 (1/4) (9/4) bΦ 0 2 (33/50) (33/50) 2
      (weighted_kappaPlain D) (weighted_stageError D)
      (count 2 (weighted_stageError D)) := by
  have hp := weighted_fixed_parameters D
  apply terminal_certificate (α:=Fin D.N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 2 (33/50) (33/50) 2
      (weighted_kappaPlain D) (weighted_stageError D)
  · norm_num
  · exact weighted_conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1
  · exact hp.2.2.1
  · exact hbeta
  · unfold weighted_kappaPlain
    linarith [weighted_background_beta]

/-- Unrestricted two-profile positive energy endpoint and zero-slot endpoint.
The positive part is available to the weighted physical numerator, with arbitrary profiles. -/
theorem weighted_terminal_energy_two {D : WeightedQRH.MomentData}
    (F : WeightedSourceData D) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    ∃degree:ℕ, ∃control:Finset (ℕ×ℕ), ∀η₀:Character,
      ∃Czero Cpositive:ℝ, 0 < Czero ∧ 0 < Cpositive ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 2 2
        (weighted_stageError D) U degree control Czero ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
        2 (1/4) (9/4) bΦ 0 2 (fineMesh 2 0 2 (3/4) (D.t/4))
        (33/50) (33/50) 2 (weighted_stageError D) (weighted_kappaPlain D)
        U η₀ (weighted_sourceFixedIdeal F) degree control Cpositive := by
  have hp := weighted_fixed_parameters D
  obtain ⟨degree,control,hbound⟩ :=
    certified_terminal F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 2 (33/50) (33/50) 2
      (weighted_kappaPlain D) (weighted_stageError D)
      (by norm_num) (by norm_num) hp.2.2.2.2.2.le hp.2.2.1
      (weighted_terminal_certificate_two F hbeta bΦ hbΦ)
  refine ⟨degree,control,?_⟩
  intro η₀
  obtain ⟨Cz,Cp,hCz,hCp,hbound⟩ := hbound η₀ (weighted_sourceFixedIdeal F)
    (weighted_sourceFixedIdeal_le_modulus F) (weighted_source_fixed_gates F η₀).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η₀)
    (weighted_source_fixed_gates F η₀).2.2.2
  exact ⟨Cz,Cp,hCz,hCp,hbound.mono (fun U h=>⟨h.2.1,h.2.2⟩)⟩
end SevenEighths.ProbeFinalAssemblyCertifiedBands
end
end OAI
