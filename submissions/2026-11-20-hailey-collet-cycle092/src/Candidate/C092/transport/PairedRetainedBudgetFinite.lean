/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Original-root whole ball from literal colored second fixed/regular costs. -/
import Candidate.C092.transport.PairedRetainedBudgetBall
import Candidate.C092.transport.TwistedRawBallRootRows
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentEnergyBands
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open RayFourExpansion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentFirstPhysicalSource CenteredMomentCompleteCommon CenteredMomentFirstSectors
open CenteredMomentSecondHeightFamily
open CenteredMomentHeckeExpansion CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentCanonicalFirst CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentLogDyadic
open CenteredMomentFirstSectorTransform CenteredMomentActiveSource CenteredMomentSourceRow
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedPrincipalAllocations
open MixedFirstRetainedFixed MixedInnerExceptionalBlock MixedOriginalTail MixedOriginalNormCap
open MixedFirstExceptionalWindow MixedFirstPhysicalApplication
open QRH.Cycle092.TwistedRawBallRootProducer
open QRH.Cycle092.TwistedRawBall
open ConcreteTraceCRT CenteredMomentLattice
open CenteredMomentAllocatedNaturalRadial
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

theorem finite_signed_of_averaged_physical_sides (N J : ℕ)
    (cRad Cp ξfirst κ ξsecond εmass εout : ℝ)
    (hcRad : 1 ≤ cRad) (hCp : 0<Cp) (hξfirst : 0<ξfirst) (hκ : 0<κ)
    (hξsecond : 0<ξsecond) (hsmall : ξfirst/2+κ ≤ 22)
    (hεmass : 0<εmass) (hεout : 0<εout) (η : Character) :
    ∃Cfull Cz Ct : ℝ,0<Cfull ∧ 0<Cz ∧ 0<Ct ∧
    ∀ᶠZ : ℝ in atTop,3 ≤ Z ∧
    ∀(η₁ η₂ : Character)(s : Source ι (1/4) (9/4))(cover : OriginalEnclosure s),
      Fintype.card ι ≤ N → s.H=∅ → s.R=1 → s.d=(1,1) →
      Z^(-8:ℝ) ≤ s.L → s.X₁ ≤ Z^(8:ℝ) → s.X₂ ≤ Z^(8:ℝ) →
      s.Y₁ ≤ Z^(8:ℝ) → s.Y₂ ≤ Z^(8:ℝ) → (∏i,s.P i) ≤ Z^(8:ℝ) →
      poolCap s ≤ Z^(8:ℝ) → sourceNormCap s.P (9/4) s.T s.d ≤ Z^(8:ℝ) →
      sourceVolume s ≤ Z^(8:ℝ) →
    ∀w : ι→ℝ,(∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    ∀n y : ℝ,sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑i,w i) →
    ∀(χ₀ : RayCharacter)(Q : Id)(m : O)(A loss : ℝ),0 ≤ A → profileCap s^2 ≤ Cp*A →
      loss+εmass ≤ εout →
      AveragedRetainedSidesQ s cover w η₁ η₂ η χ₀ Q m (cRad*Z) Z ξfirst κ
        (Z^(8:ℝ)) A loss ξsecond Cz Ct J →
      ∀rows : Finset O,(∀z∈rows,z≠0) → (∀z∈rows,‖eisEmbedding z‖^2 ≤ Z) →
      (∑z∈rows,‖sourceSignedRow s (by norm_num) (naturalCharacter η z)
        (idealCoeff η₁) (idealCoeff η₂)‖^2) ≤ Cfull*A*Z^(1+εout) := by
  obtain ⟨Cfull,Cz,Ct,hCfull,hCz,hCt,hfull⟩ := full_ball_of_averaged_physical_sides
    (ι:=ι) N J cRad Cp ξfirst κ ξsecond εmass εout
    hcRad hCp hξfirst hκ hξsecond hsmall hεmass hεout η
  refine ⟨Cfull,Cz,Ct,hCfull,hCz,hCt,?_⟩
  filter_upwards [hfull] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η₁ η₂ s cover hN hH hR hd hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm hvol w hw hPw
    n y hy hy' hn hboxX χ₀ Q m A loss hA hprofile hloss hprice rows hnz hrad
  have hz : 0<Z := by linarith [hZ.1]
  have hball := hZ.2 η₁ η₂ s cover hN hd hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm hvol
    w hw hPw n y hy hy' hn hboxX χ₀ Q m A loss hA hprofile hloss hprice
  have hrow := finite_signed_rows_le_fixed_ball s (by norm_num) (by norm_num)
    cover hH hd hR (idealCoeff η₁) (idealCoeff η₂) η (cRad*Z)
    (mul_pos (zero_lt_one.trans_le hcRad) hz) rows hnz
    (fun z hzrow=>(hrad z hzrow).trans (le_mul_of_one_le_left hz.le hcRad))
  exact hrow.trans hball

#print axioms finite_signed_of_averaged_physical_sides
end
end QRH.Cycle092.PairedRetainedBudget
