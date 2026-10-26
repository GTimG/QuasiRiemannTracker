/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual modified geometry pays every selected HIGH sector and the exact
normalization lost under complete-prime extraction and singleton deletion. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSectorPartition
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.NonregularModified
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths Record12518109Natural Record1252270103CommonGeometry
open Cycle61HighGeometry Cycle61InitialMass JointHigh LocalMoment
open Record1252270103Finite PhysicalScalar CanonicalQuadraticSieve HeckeFamily
open CenteredMomentCommonRadialData CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonical CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentRankinRadical Cycle61Moment
open Record1252270103Source.Collision Admission HighScalar
open HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def selectedSectorGain (high : Option Source) (sector : HighSector)
    (ν slots tiny : ℝ) : ℝ→ℝ :=
  if sector=.regular then gainAt high ν slots else sectorSharpGain sector ν slots tiny

theorem modified_selected_sector_singleton_payment (n low : Source) (high : Option Source)
    (hp : GainParameters high) (s : Input ι) (A₁ A₂ Dmark Kmark R seed : Ideal O)
    (F : Ideal O→ℂ) (H Z ξ : ℝ) (hH : 0<H) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (High.CoupledFirst.geometryFirstSource s
      (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ hH key))
    (reflected second : Bool) (d2 : SecondInputDatum ι) (U : Finset (CommonIndex d2.C d2.D))
    (D A amp reserveGeom err errv ν b live small forced reserve : ℝ)
    (hZ : 1<Z) (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hD0 : 0≤D)
    (hforced : 0≤forced) (hsmall : small≤live) (hlive : live≤D*b)
    (hA : A≤D*(sourceTReal n b+b)) (hamp : amp≤D*sourceAReal n low b)
    (hOmega : frequencyLoss Z 32 ξ+reserveGeom≤D*(n.allowance:ℝ)) (herr : 0≤err)
    (hg : ActualGaps n low high b ν reserve) (core : Prop) [Decidable core] :
    let l:=FirstFamily.firstLabel s (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ hH key j
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U
      Z D A amp ξ reserveGeom err) errv
    let side:=balancedGeometrySide reflected A
      (High.CoupledFirst.geometryExponents s (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ j.1.val)
    D*(b-2*(n.allowance:ℝ))≤live+labelC reflected l Z+
      Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)+forced →
    ∀w:NonzeroFrequency,rawFrequencyNorm w≤Z^(x 2) →
    retainedHighExponent ν
      (selectedSectorGain high (selectedHighSector core (x 2) (D/50)) ν small (D/50))
      (lostWidthCoordinates x (forced+live-small))≤
      side+((1-unmarkedDensity ν)*(frequencyLoss Z 32 ξ+reserveGeom)+
        unmarkedDensity ν*err+errv)-D*((n.highFee:ℝ)+reserve) := by
  intro l x side hslots w hw
  let sector:=selectedHighSector core (x 2) (D/50)
  have hgates:=selected_high_sector_gates core Z (x 2) (D/50) hZ w hw
  by_cases hs:sector=.regular
  · have hpaid:=modified_retained_high_exponent n low high hp s A₁ A₂ Dmark Kmark R seed F
      H Z ξ hH key j reflected second d2 U D A amp reserveGeom err errv ν b live forced reserve
      hZ hν0 hν1 hD0 hforced hA hamp hOmega herr hg hslots
    have hc : 0≤labelC reflected l Z := by
      apply Real.logb_nonneg hZ
      have hC:Supported l.1.1:=
        (High.CoupledFirst.geometryFirstSource s (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ hH key j.1).hC
      have hD:Supported l.1.2:=
        (High.CoupledFirst.geometryFirstSource s (markedSourceModifier A₁ A₂ Dmark Kmark F) R seed H Z ξ hH key j.1).hD
      cases reflected
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
    have hd : 0≤Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
      apply Real.logb_nonneg hZ
      cases second
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr d2.hC.1)
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr d2.hD.1)
    have hsubset:=full_singleton_subset_payment high hp hν0 hν1 hsmall x (forced:=forced)
    change retainedHighExponent ν (selectedSectorGain high sector ν small (D/50)) _≤_
    simp only [selectedSectorGain,hs,if_true]
    exact hsubset.trans (hpaid.trans (by dsimp only [l,x,side] at hc hd ⊢;linarith))
  · have hpaid:=nonregular_modified_retained_high_exponent n low high sector hs s A₁ A₂ Dmark Kmark R seed F
      H Z ξ hH key j reflected second d2 U D A amp reserveGeom err errv ν b live forced reserve
      hZ hν0 hν1 hD0 hforced hA hamp hOmega herr hlive hg hgates.1
      (fun ht=>(hgates.2.2.2 ht).1)
    have hsubset:=nonregular_singleton_subset_payment sector hs ν small live (D/50) forced x hsmall
    change retainedHighExponent ν (selectedSectorGain high sector ν small (D/50)) _≤_
    simp only [selectedSectorGain,hs,if_false]
    exact hsubset.trans hpaid

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_selected_sector_singleton_payment
