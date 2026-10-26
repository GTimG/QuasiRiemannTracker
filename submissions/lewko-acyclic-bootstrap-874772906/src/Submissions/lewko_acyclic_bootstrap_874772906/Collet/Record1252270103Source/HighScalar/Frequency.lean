/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.HighScalar.LabelPayment
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open OAI OAI.SevenEighths Record12518109Natural Cycle61HighGeometry Cycle61InitialMass
open Record1252270103Finite PhysicalScalar CanonicalQuadraticSieve LocalMoment
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentRankinRadical Cycle61Moment
open ConcretePrimeRowBridge
variable {α : Type} [Fintype α] [DecidableEq α]

theorem actual_label_frequency_lower (n low : Source) (b : ℝ)
    (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (d2 : SecondInputDatum α) (U : Finset (CommonIndex d2.C d2.D))
    (Z D A amp ξ reserveGeom err errv : ℝ) (hZ : 1<Z)
    (hamp : amp≤D*sourceAReal n low b)
    (hOmega : frequencyLoss Z 32 ξ+reserveGeom≤D*(n.allowance:ℝ)) (herr : 0≤err) :
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U
      Z D A amp ξ reserveGeom err) errv
    D*(sourceFReal n low b-(n.allowance:ℝ))≤x 2+2*labelC reflected l Z+
      2*Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
  intro x
  have hc : 0≤labelC reflected l Z := by
    apply Real.logb_nonneg hZ
    cases reflected <;> first | exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1) | exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hd : 0≤labelD reflected l Z := by
    apply Real.logb_nonneg hZ
    cases reflected <;> first | exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1) | exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hb : 0≤Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases second <;> first | exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr d2.hC.1) | exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr d2.hD.1)
  have hg:=actual_first_gates (!reflected) l hC hD Z hZ
  have hR : labelR l Z≤labelC reflected l Z := by
    cases reflected
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.1
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.2.1
  have hLc : 0≤Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ) :=
    Real.logb_nonneg hZ (normValue_ge_one _ (first_source_numerator_ne_zero (!reflected) l hC))
  have hh:=raw_frequency_moving D (labelC reflected l Z) (labelD reflected l Z)
    (Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)) amp (labelR l Z)
    (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
    (frequencyLoss Z 32 ξ+reserveGeom) err (x 2) (sourceAReal n low b) (n.allowance:ℝ)
    hc hd hb hR hLc hamp hOmega herr
    (by simp [x,childHighCoordinates,actualHighCoordinates,labelC,labelD,labelR])
  dsimp only [sourceFReal]
  linarith only [hh]

end
end QRH.Record1252270103Source.HighScalar
#print axioms QRH.Record1252270103Source.HighScalar.actual_label_frequency_lower
