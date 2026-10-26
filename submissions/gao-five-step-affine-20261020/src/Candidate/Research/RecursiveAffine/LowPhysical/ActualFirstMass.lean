/- Copyright (c) 2026 Hailey Collet; recursive source assembly (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeSourceSide
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowSelected
import Candidate.Cycle63.Physical.InitialMass.GeometryLowSidePayment
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle153LowPhysical
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass Cycle153RegionalLow
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonHeightEnvelope
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentCanonicalFirst CenteredMomentFirstExceptionalPrefactor

/-- The same actual first geometry bin supplies BOTH the supported-label
old allowance exponent and the bound on its literal first-column mass.
The mass-dyad loss cancels the side exponent; it is not declared small. -/
theorem actual_first_mass_and_old_side
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (reflected : Bool) (N : ℕ) (lo ap : ℝ) (hlo : 0< lo) (hap : 0< ap)
    (s : Input alpha) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ))
    (Mrow Z xi Bmass epsMass : ℝ) (hZ : 1< Z)
    (hcard : Fintype.card alpha≤ N) (hlower : lo≤ s.lower)
    (hseed : Squarefree seed) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^Bmass) (heps : 0≤ epsMass)
    (hs1 : ∀x,s.W₁ x≠0→ap≤ x) (hs2 : ∀x,s.W₂ x≠0→ap≤ x)
    (key : ℤ×(Fin 5→ℤ)) :
    let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
    ∃exponent sideLower : ℝ,
      ((key.2 2:ℝ)+1)*Real.logb Z 2+exponent-sideLower=6*Real.logb Z 2 ∧
      ∀j : FirstColumnIndex (geometryFirstSource s R seed (Z^Mrow) Z xi hK key),
        let first:=geometryFirstLabel s R seed (Z^Mrow) Z xi hK key j
        lowAllowedExponent reflected Z (Real.logb Z (volume s)) first≤ exponent ∧
        geometryFirstHighMass reflected s R seed W Mrow Z xi epsMass hK key j≤
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) key*
            Z^(Bmass*epsMass-sideLower) ∧
        (Bmass*epsMass-sideLower)+lowLabelSide reflected Z (Real.logb Z (volume s)) first≤
          Bmass*epsMass+6*Real.logb Z 2 := by
  intro hK
  obtain ⟨exponent,sideLower,hledger,hgate⟩:=actual_first_bin_side_cancellation s R seed
    (Z^Mrow) Z xi Bmass (Real.logb Z (volume s)) hK hZ hseed hz1 hz2 hsource key reflected
  refine ⟨exponent,sideLower,hledger,?_⟩
  intro j first
  have hg:=hgate j
  refine ⟨(lowAllowedExponent_le_lowSideExponent reflected Z (Real.logb Z (volume s)) first).trans hg.2.1,?_,?_⟩
  · exact actual_geometry_low_uniform_mass reflected N lo ap hlo hap s R seed W Mrow Z xi Bmass epsMass
      sideLower hZ hK heps hcard hlower hseed hz1 hz2 hsource hs1 hs2 key j hg.2.2.1
  · exact hg.2.2.2 (Bmass*epsMass)

/-- Exact OLD payment after the actual AtState outer scale. All intermediate
row scales and amplifiers cancel only here. The source-bin cost is the
literal factor 64, and the original first-seed reciprocal stays outside. -/
theorem actual_old_raw_bin_normalization
    (Z Mrow delta amp driverError massError sideLower p exponent error unit epsV normCap shellLoss labelLoss
      C seedNorm : ℝ)
    (hZ : 1< Z) (hledger : p+exponent-sideLower=6*Real.logb Z 2) :
    Z^(Mrow+3*delta-amp+driverError)*
      (C*Z^((massError-sideLower)+amp+p+exponent+error+(unit-Mrow)+epsV+normCap*shellLoss+labelLoss)/seedNorm)=
      64*(C*Z^(unit+3*delta+driverError+massError+error+epsV+normCap*shellLoss+labelLoss)/seedNorm) := by
  have hZ0:=zero_lt_one.trans hZ
  have he : (Mrow+3*delta-amp+driverError)+
      ((massError-sideLower)+amp+p+exponent+error+(unit-Mrow)+epsV+normCap*shellLoss+labelLoss)=
      (unit+3*delta+driverError+massError+error+epsV+normCap*shellLoss+labelLoss)+6*Real.logb Z 2 := by
    linarith only [hledger]
  calc
    _=C*(Z^(Mrow+3*delta-amp+driverError)*
      Z^((massError-sideLower)+amp+p+exponent+error+(unit-Mrow)+epsV+normCap*shellLoss+labelLoss))/seedNorm := by ring
    _=C*Z^((unit+3*delta+driverError+massError+error+epsV+normCap*shellLoss+labelLoss)+6*Real.logb Z 2)/seedNorm := by
      rw [←Real.rpow_add hZ0,he]
    _=_ := by rw [Real.rpow_add hZ0,geometry_low_bin_slack_six_payment Z hZ];ring
end
end OAI.SevenEighths.Cycle153LowPhysical
#print axioms OAI.SevenEighths.Cycle153LowPhysical.actual_first_mass_and_old_side
#print axioms OAI.SevenEighths.Cycle153LowPhysical.actual_old_raw_bin_normalization
