/- Copyright (c) 2026 Sil. Apache-2.0.
Coefficient-agnostic interface from canonical source envelopes to the
actual second physical block. The envelope premises are explicit: this
adapter is not itself the unconditional mixed moment estimate.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.MixedPhysicalEnvelopes
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss ConcreteTraceCRT RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentSupport CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns
open CenteredMomentSecondWindowBudget CenteredMomentRestrictedSource CenteredMomentFirstSectors
open CenteredMomentSecondWindowSource CenteredMomentSecondIdealBlockBound
open CenteredMomentSecondSupportedChildren CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondHeightFamily
open CenteredMomentSecondNonexceptionalPhysical CenteredMomentEnergyChildState
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Arbitrary literal column coefficients are allowed. In particular this
does not replace a tuple restriction by the unrestricted baseline source. -/
theorem actual_canonical_source_envelopes
    (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C0 : ℝ,0<C0 ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀Kphys : ℝ,0<Kphys → ∀n : Fin 4→ℤ,
    let r := dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
    ∀(η : Character)(τ : RayCharacter→Character)(t : ℝ)(S : Finset Id)(β : Id→ℂ),
    ∀(C D : Id)(hC : Supported C)(hD : Supported D),
    primeSupport C=primeSupport D → ∀U : Finset (CommonIndex C D),
    Family η C D hC hD U τ →
    ∀Hsource : ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
    Hsource/(D.absNorm:ℝ)≤Z^B →
    ∀(R : ℝ)(Q : Id)(m : O)(χ₀ : RayCharacter),Q≤Ideal.span {(72:O)} →
    m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Id)),
      (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ : RayCharacter,∀v : ℝ,
      sourceRestrictedEnergy (canonicalRadial (τ χ) Q n).keep (residualPool C hC.1 S)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff (τ χ) v) ballProfile (dyadicScale (n 1))
        ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Id)),
      (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ : RayCharacter,∀v : ℝ,
      sourceRestrictedEnergy (canonicalRadial (τ χ) Q n).keep (residualPool D hD.1 S)
        (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0)
        (heightCoeff (τ χ) v) ballProfile (dyadicScale (n 1))
        ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    ‖physicalBlock η t S β C D hC hD U R
        (partRows false η χ₀ Q m C D U R) W Kphys n‖ ≤
      C0*Z^δ*(outerScalar C D Kphys n*normalizer C D U)*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂)/(1+r)^decay := by
  obtain ⟨C0,hC0,hkernel⟩ := actual_block_from_supported_envelopes W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,hC0,hkernel.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n r η τ t S β C D hC hD hCD U hf
    Hsource hβ hHD R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  let rows := partRows false η χ₀ Q m C D U R
  have hr : 0<r := div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hpow : 0<(1+r)^decay := pow_pos (by linarith) _
  have hrows : ∀z∈dyadicRows rows n,nonexceptional η χ₀ Q m A z := by
    intro z hz
    have hh := Finset.mem_filter.mp ((dyadicRows_subset rows n) hz)
    simpa only [rows,partRows,Bool.false_eq_true,ite_false] using hh.2
  have hmajor : ∀z∈dyadicRows rows n,1≤(ballProfile (normValue z/dyadicScale (n 1))).re := by
    intro z hz
    have hb := ballProfile_majorizes (dyadicScale (n 1)) (dyadicScale_pos _) z
      (dyadicRows_norm rows n z hz).2.le
    simpa only [normValue_eq_embedding] using hb
  have hkeep (χ : RayCharacter) : nonexceptional η χ Q m A = (canonicalRadial (τ χ) Q n).keep := by
    funext z
    exact propext (hf.nonexceptional_iff χ Q m z hm hml hm2)
  have hh := hZ.2 r hr η τ t S β C D hC hD hCD U hf.height_eq Hsource hβ hHD
    R (dyadicRows rows n) (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1)))
    (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
    Q m χ₀ hQ hml hm2 hrows ballProfile (dyadicScale (n 1)) (dyadicScale_pos _)
    (fun _=>ballProfile_nonneg _) hmajor E₁ E₂ hE₁ hE₂
    (by intro L hL hLN hsf χ v; rw [hkeep]; exact hleft L hL hLN hsf χ v)
    (by intro L hL hLN hsf χ v; rw [hkeep]; exact hright L hL hLN hsf χ v)
  change (1+r)^decay*‖normalizedBlock η t S β C D hC hD U R (dyadicRows rows n) W Kphys n‖≤_ at hh
  have ho : 0≤outerScalar C D Kphys n := by unfold outerScalar; positivity
  have hno : 0≤normalizer C D U := (normalizer_pos C D hC U).le
  have hp := mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)
  have hphys : ‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖ =
      outerScalar C D Kphys n*normalizer C D U*
        ‖normalizedBlock η t S β C D hC hD U R (dyadicRows rows n) W Kphys n‖ := by
    rw [physicalBlock_dyadic_rows,
      physicalBlock_eq η t S β C D hC hD U R (dyadicRows rows n)
        (fun z hz=>(hrows z hz).1) W Kphys hKphys n,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  change ‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖ ≤ _
  rw [hphys]
  apply (le_div_iff₀ hpow).mpr
  convert hp using 1 <;> ring

/-- The common raw volume cancels exactly when the physical block is
normalized. The genuine common-divisor factors survive the pairing. -/
theorem paired_normalized_windows (V A E₁ E₂ c d t : ℝ)
    (hV : 0<V)(hA : 0≤A)(hE₁ : 0≤E₁)(hE₂ : 0≤E₂)(hc : 0<c)(hd : 0<d)
    (J₁ J₂ : ℕ) :
    windowBudget J₁ t (V*A*E₁/c)*windowBudget J₂ t (V*A*E₂/d)/V =
      A/Real.sqrt (c*d)*Real.sqrt (E₁*E₂)*
        heightEnvelope t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ := by
  have hs := paired_sqrt (V*A) E₁ E₂ c d (mul_nonneg hV.le hA) hE₁ hE₂ hc hd
  simp only [windowBudget,pow_add]
  calc
    _ = (Real.sqrt (V*A*E₁/c)*Real.sqrt (V*A*E₂/d))*
        (heightEnvelope t^J₁*heightEnvelope t^J₂)*profileMoment J₁*profileMoment J₂/V := by ring
    _ = _ := by rw [hs]; field_simp [hV.ne']

end
end Candidate.Feedback.FourthPower.MixedPhysicalEnvelopes
