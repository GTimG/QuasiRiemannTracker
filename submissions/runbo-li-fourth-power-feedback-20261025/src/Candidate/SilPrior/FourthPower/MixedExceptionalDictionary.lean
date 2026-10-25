/- Copyright (c) 2026 Sil. Apache-2.0.
Exact second-exceptional source dictionary. This module keeps the literal
tuple coefficient, prefix norms, seed, common mask and all height phases.
It does not assert an exceptional count after fourth-power completion.
-/
import Candidate.SilPrior.FourthPower.MixedHeightEnergy
import Candidate.SilPrior.FourthPower.PrincipalPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedExceptionalDictionary
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss RayFourExpansion ConcretePrimeRowBridge FourierBridge
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildAssembly
open CenteredMomentSecondHeightFamily CenteredMomentSmooth CenteredMomentRowNorm
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentPlainWindowEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorEnergy CenteredMomentSecondMaskedWindow
open CenteredMomentSecondScaled
open CenteredMomentRestrictedEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskEnergy
open CenteredMomentSecondEnergySplit CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondExceptionalSourceFamily CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentNaturalRowSource CenteredMomentFixedRowMask
open MixedHeightEnergy MixedOriginalSource MixedCommonHeights MixedLiveNormalization
open MixedRestrictedDictionary MixedLiteralAllocation
open ReferencePrimeEnclosure
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

section Original
variable (S H : Finset PrimeIdeal) (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
  (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
  (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ) (W₁ W₂ : ℝ→ℂ)
  (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ)
  (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
  (hXY : X₁*X₂=Y₁*Y₂)
local notation "Qsource" => finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
local notation "βoriginal" => originalColumn S H pool d hd R seed ν Wslot P
  (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
include hp hX₁ hX₂ hY₁ hY₂ hXY

/-- A second-sector row at any independent height. The complete common
extraction is performed after this exact identity, so seed|G is not needed. -/
theorem original_sector_height (τ : Character) (G : Id) (hG : Supported G)
    (L : Id) (v : ℝ) (z : O) (hz : z≠0) :
    normalization (X₁*X₂) P*
      rowPolynomial Finset.univ (sectorElement G hG.1 Qsource)
        (fun I : sectorPool G hG.1 Qsource=>(if L∣I.val then βoriginal (G*I) else 0)*
          heightCoeff τ v I) z=
      residualPhase (X₁*X₂) d G v*
        originalMaskedRow (naturalCharacter τ z) S H pool d hd G R seed L hG.1
          (fun i=>heightCoefficient (ν i) v) Wslot P
          (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
          b X₁ X₂ Y₁ Y₂ := by
  rw [sector_rowPolynomial Qsource
    (fun I=>(if L∣I then βoriginal (G*I) else 0)*heightCoeff τ v I) G hG z]
  have hc : (fun I : supportedColumns (residualPool G hG.1 Qsource)=>
      if IsCoprime G (I:Id) then (if L∣(I:Id) then βoriginal (G*I) else 0)*heightCoeff τ v I else 0)=
      (fun I : supportedColumns (residualPool G hG.1 Qsource)=>
        (if IsCoprime G (I:Id) ∧ L∣(I:Id) then βoriginal (G*I) else 0)*heightCoeff τ v I) := by
    funext I
    split_ifs <;> simp_all
  rw [hc,height_source_natural_character τ v (residualPool G hG.1 Qsource)
    (fun I=>if IsCoprime G I ∧ L∣I then βoriginal (G*I) else 0) z hz]
  exact original_masked_height_row (naturalCharacter τ z) v S H pool hp d hd
    G R seed L hG.1 ν Wslot P W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY

/-- The actual divisor/moving/ray coefficient is kept inside its window.
Family.height_eq supplies hτ. The Fourier variable shifts both ordinary
profile phases as well as the marked coefficients; none is discarded. -/
theorem original_sector_window (η τ : Character) (χ : RayCharacter) (A : O)
    (G : Id) (hG : Supported G)
    (hτ : ∀I : Id,Supported I→IsCoprime G I→∀v : ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (L : Id) (t θ Xwindow : ℝ) (hXwindow : 0<Xwindow)
    (V : ℝ→ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) (hz : z≠0) :
    normalization (X₁*X₂) P*
      rowPolynomial Finset.univ (sectorElement G hG.1 Qsource)
        (fun I : sectorPool G hG.1 Qsource=>divisorCoefficient L (sectorElement G hG.1 Qsource)
          (movingCoefficient A (sectorElement G hG.1 Qsource)
            (fun J : sectorPool G hG.1 Qsource=>βoriginal (G*J)*heightCoeff η t J)) χ I*
          columnPhase V (Real.log ((I.val.absNorm:ℝ)/Xwindow)) θ) z=
      ∫w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log Xwindow)*
        (residualPhase (X₁*X₂) d G (t+2*Real.pi*(w-θ))*
          originalMaskedRow (naturalCharacter τ z) S H pool d hd G R seed L hG.1
            (fun i=>heightCoefficient (ν i) (t+2*Real.pi*(w-θ))) Wslot P
            (phaseProfile W₁ (t₁+(t+2*Real.pi*(w-θ))/(2*Real.pi)))
            (phaseProfile W₂ (t₂+(t+2*Real.pi*(w-θ))/(2*Real.pi))) b X₁ X₂ Y₁ Y₂) := by
  simp_rw [masked_divisor_coefficient η τ χ A G hG hτ Qsource βoriginal L t]
  have he := plain_column_integral Finset.univ (sectorElement G hG.1 Qsource)
    (sectorElement_supported G hG.1 Qsource)
    (fun I : sectorPool G hG.1 Qsource=>if L∣I.val then βoriginal (G*I) else 0)
    τ t θ Xwindow hXwindow V hVc hVs z
  simp only [sectorElement_span] at he
  rw [he,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have hr := original_sector_height S H pool hp d hd R seed ν Wslot P W₁ W₂
    t₁ t₂ b X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY τ G hG L (t+2*Real.pi*(w-θ)) z hz
  calc
    _ = columnDensity V hVc hVs w*logPhase (θ-w) (Real.log Xwindow)*
      (normalization (X₁*X₂) P*rowPolynomial Finset.univ (sectorElement G hG.1 Qsource)
        (fun I : sectorPool G hG.1 Qsource=>(if L∣I.val then βoriginal (G*I) else 0)*
          heightCoeff τ (t+2*Real.pi*(w-θ)) I) z) := by ring
    _ = _ := by rw [hr]
end Original

/-- The genuine exceptional predicate, with the actual canonical Family.
This equality applies before any exceptional count is inserted. The
radial scale is explicit and may be the actual dyadic K4 scale. -/
theorem actual_exceptional_height_energy
    (η : Character) (χ₀ χ : RayCharacter) (Q₀ : Id) (m : O)
    (C D : Id) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter→Character) (hf : Family η C D hC hD U τ) (radius : ℝ)
    (S H : Finset PrimeIdeal) (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed L : Id)
    (ν : α→Character) (R₀ : α→Finset Id) (t : ℝ)
    (Wslot : α→ℝ→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (v : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let Qsource := finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    let β := originalColumn S H pool d hd R seed (MixedCanonicalSource.slotCoefficient ν R₀ t)
      Wslot P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
    restrictedEnergy (fun z=>z∈partRows true η χ₀ Q₀ m C D U radius)
      Finset.univ (sectorElement C hC.1 Qsource)
      (divisorCoefficient L (sectorElement C hC.1 Qsource)
        (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
          (sectorElement C hC.1 Qsource)
          (fun I : sectorPool C hC.1 Qsource=>β (C*I)*heightCoeff η v I)) χ) Φ K/
      (X₁*X₂*∏i,P i)=
    radialEnergy (fun z=>originalMaskedRow (naturalCharacter (τ χ) z) S H pool d hd C R seed L hC.1
      (MixedCanonicalSource.slotCoefficient ν R₀ (t+v)) Wslot P
      (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi))) b X₁ X₂ Y₁ Y₂)
      (fun z=>z∈partRows true η χ₀ Q₀ m C D U radius) Φ K := by
  dsimp only
  rw [masked_child_energy η (τ χ) χ _ C hC
    (fun I hI hcop v=>hf.height_eq χ I hI (Or.inl hcop) v)]
  exact canonical_source_height_energy (τ χ) v S H pool hp d hd C R seed L hC.1
    ν R₀ t Wslot P hP W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY
    _ (fun z hz=>exceptional_part_nonzero η χ₀ Q₀ m C D U radius z hz) Φ K

/-- A common puncture is a genuine physical sixth-power mask. This
exact presentation is the input of PrincipalPhysical.uniform_physical. -/
theorem excluded_natural_presentation (η : Character) (z : O) (hz : z≠0)
    (F : Id) (hF : F≠0) (n : O) :
    elementCoeff (excluded (naturalCharacter η z) F) n=
      rowTwist (HeckeRowClosure.elementHom η) (fixedBadMask*idealGenerator F) 1 (1*z) n := by
  rw [naturalCharacter_eq η z hz,one_mul]
  exact (naturalRow η z hz).masked_element F hF n

/-- Both actual exceptional characters remain fixed-inducing after
every nonzero extracted puncture. This is not a source-energy premise. -/
theorem actual_excluded_both_inducing (η : Character) (χ₀ χ ξ : RayCharacter)
    (Q : Id) (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Id) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter→Character) (hf : Family η C D hC hD U τ)
    (radius : ℝ) (z : O) (hz : z∈partRows true η χ₀ Q m C D U radius)
    (F₁ F₂ : Id) (hF₁ : F₁≠0) (hF₂ : F₂≠0) :
    CenteredExceptionalProfile.FixedInducingRow (τ χ) Q
      (fixedBadMask*idealGenerator F₁) 1 z ∧
    CenteredExceptionalProfile.FixedInducingRow (CenteredMomentReflectedSource.reflected (τ ξ)) Q
      (fixedBadMask*idealGenerator F₂) 1 z := by
  have hz0 := exceptional_part_nonzero η χ₀ Q m C D U radius z hz
  have hχ := (actual_family_both_rows η χ₀ Q hQ m hm hml hm2 C D hC hD U τ hf radius).1 χ z hz
  have hξ := hf.both_inducing χ ξ Q hQ m z hm hz0 hml hm2
    ((hf.inducing_iff χ Q m z hm hz0 hml hm2).mpr hχ)
  constructor
  · exact (fixedInducingRow_mul_mask_iff (τ χ) Q fixedBadMask (idealGenerator F₁) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero F₁ hF₁) one_ne_zero hz0
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hξ.1
  · exact (fixedInducingRow_mul_mask_iff (CenteredMomentReflectedSource.reflected (τ ξ)) Q
      fixedBadMask (idealGenerator F₂) 1 z fixedBadMask_ne_zero
      (idealGenerator_ne_zero F₂ hF₂) one_ne_zero hz0
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hξ.2

end
end Candidate.SilPrior.FourthPower.MixedExceptionalDictionary
