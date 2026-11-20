/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Original-root whole ball from literal colored second fixed/regular costs. -/
import Candidate.C092.transport.PairedRetainedBudgetRaw
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
open QRH.Cycle092.TwistedRawBall
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

theorem retained_sides_of_averaged_Q (N : ℕ) (ξsecond cRad ξfirst κ : ℝ)
    (hξsecond : 0<ξsecond) (hcRad : 1 ≤ cRad) (hκ : 0<κ) (hsmall : ξfirst/2+κ ≤ 22) :
    ∃Cz Ct : ℝ,0<Cz ∧ 0<Ct ∧ ∀ᶠZ : ℝ in atTop,3 ≤ Z ∧
    ∀s : Source ι (1/4) (9/4),Fintype.card ι ≤ N →
    ∀(cover : OriginalEnclosure s)(w : ι→ℝ),(∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    ∀n y : ℝ,sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑i,w i) →
      poolCap s ≤ Z^(8:ℝ) →
    sourceVolume s ≤ Z^(8:ℝ) →
    ∀(η₁ η₂ η : Character)(χ₀ : RayCharacter)(Q : Id)(m : O)(H A loss : ℝ)(J : ℕ),
      AveragedRetainedSidesQ s cover w η₁ η₂ η χ₀ Q m (cRad*Z) Z ξfirst κ H A loss ξsecond Cz Ct J →
      SummedRetainedRawSides s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) η
        (cRad*Z) Z ξfirst κ H A loss J := by
  obtain ⟨Cz,Ct,hCz,hCt,hr⟩ := balanced_sides_of_averaged_Q (ι:=ι) N ξsecond hξsecond
  refine ⟨Cz,Ct,hCz,hCt,?_⟩
  filter_upwards [hr,eventually_padding κ hκ] with Z hZ hpad
  refine ⟨hZ.1,?_⟩
  intro s hN cover w hw hP n y hy hy' hn hX hpool hvol η₁ η₂ η χ₀ Q m H A loss J hphys
    p E hE band hdy
  have hp := commonLabels_supported (activeSource (sourceColumns s)
    (TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1)) p
  have hCD := (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2
  have hc := actual_child_Q_range s p.val.1 p.val.2 E cRad Z ξfirst κ H hcRad
    (by linarith [hZ.1]) hpad hsmall hvol band hdy
  exact hZ.2 s hN cover w hw hP n y hy hy' hn hX hpool η₁ η₂ η χ₀ Q m
    p.val.1 p.val.2 hp.1 hp.2 hCD E _ _ A loss J hc.1 hc.2 hc.1 hc.2
    (hphys p E hE band hdy)

/-- The whole original independently weighted ball. First zero/tail and
    original-Q selected second zero/tail are proved inside. The remaining
    price refers only to actual finite fixed/regular physical terms and their
    explicit numeric remainder costs, with original first divisors unweighted. -/
theorem full_ball_of_averaged_physical_sides (N J : ℕ)
    (cRad Cp ξfirst κ ξsecond εmass εout : ℝ)
    (hcRad : 1 ≤ cRad) (hCp : 0<Cp) (hξfirst : 0<ξfirst) (hκ : 0<κ)
    (hξsecond : 0<ξsecond) (hsmall : ξfirst/2+κ ≤ 22)
    (hεmass : 0<εmass) (hεout : 0<εout) (η : Character) :
    ∃Cfull Cz Ct : ℝ,0<Cfull ∧ 0<Cz ∧ 0<Ct ∧
    ∀ᶠZ : ℝ in atTop,3 ≤ Z ∧
    ∀(η₁ η₂ : Character)(s : Source ι (1/4) (9/4))(cover : OriginalEnclosure s),
      Fintype.card ι ≤ N → s.d=(1,1) →
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
      ‖finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
        (TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1)
        ballProfile (cRad*Z)‖/sourceVolume s ≤ Cfull*A*Z^(1+εout) := by
  obtain ⟨Cfull,hCfull,hfull⟩ := fullBallCost_of_raw_sides (ι:=ι) N J cRad Cp ξfirst κ εmass εout
    hcRad hCp hξfirst hκ hεmass hεout η
  obtain ⟨Cz,Ct,hCz,hCt,hphys⟩ := retained_sides_of_averaged_Q (ι:=ι) N ξsecond cRad ξfirst κ
    hξsecond hcRad hκ hsmall
  refine ⟨Cfull,Cz,Ct,hCfull,hCz,hCt,?_⟩
  filter_upwards [hfull,hphys] with Z hf hp
  refine ⟨hp.1,?_⟩
  intro η₁ η₂ s cover hN hd hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm hvol w hw hPw
    n y hy hy' hn hboxX χ₀ Q m A loss hA hprofile hloss hprice
  exact hf.2 η₁ η₂ s hN hd hL hX₁ hX₂ hY₁ hY₂ hP hpool hnorm hvol A loss hA hprofile hloss
    (hp.2 s hN cover w hw hPw n y hy hy' hn hboxX hpool hvol η₁ η₂ η χ₀ Q m
      (Z^(8:ℝ)) A loss J hprice)

#print axioms retained_sides_of_averaged_Q
#print axioms full_ball_of_averaged_physical_sides
end
end QRH.Cycle092.PairedRetainedBudget
