/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual retained signed rows use exactly the LOW radial exponent. The
threshold precedes every moving label, datum, puncture and original slot set. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularLowRetainedRadial
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowRetainedRadial
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentAmplificationChildInput
open Cycle61Moment Cycle61InitialMass Cycle61HighGeometry
open LocalMoment
open Record12518109Natural Record12518109Raw Record1252270103CommonGeometry
open Record1252270103Finite QRH.Record1252270103Source.Admission
open Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O

theorem eventual_literal_low_frequency (profileUpper err:ℝ) (N:ℕ)
    (hb:0<profileUpper) (herr:0<err) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α DataLabel:Type}[Fintype α][DecidableEq α][Fintype DataLabel]
      (n low:Source) (b:ℝ) (reflected second:Bool) (s:Input α)
      (A₁ A₂ D K R seed:Ideal O) (F:Ideal O→ℂ) (ξ:ℝ) (hH:0<Z^(1:ℝ))
      (bin:ℤ×(Fin 5→ℤ))
      (column:FirstColumnIndex (High.CoupledFirst.geometryFirstSource s
        (markedSourceModifier A₁ A₂ D K F) R seed (Z^(1:ℝ)) Z ξ hH bin))
      (datum:DataLabel→SecondInputDatum α) (first:DataLabel→FirstSourceLabel)
      (row:secondLiveRows (fun l=>(datum l).block))
      (hfirst:first row.val.1=FirstFamily.firstLabel s (markedSourceModifier A₁ A₂ D K F)
        R seed (Z^(1:ℝ)) Z ξ hH bin column)
      (reserve errv radialRound:ℝ),ξ≤err→0≤radialRound→
      (datum row.val.1).radius=frequencyRadius
        (firstMainFourierScale reflected (Z^(1:ℝ)) (volume s) Z ξ (3*sourceAReal n low b)
          reserve profileUpper N (FirstFamily.firstLabel s (markedSourceModifier A₁ A₂ D K F)
            R seed (Z^(1:ℝ)) Z ξ hH bin column)) Z ξ→
      let modifier:=markedSourceModifier A₁ A₂ D K F
      let l:=FirstFamily.firstLabel s modifier R seed (Z^(1:ℝ)) Z ξ hH bin column
      let left:=!reflected
      let unit:=fun l=>(fixedParentUnit left s.η l:O)
      let hf:=FirstFamily.first_frequency_ne_zero reflected s modifier R seed (Z^(1:ℝ)) Z ξ hH
        bin column datum first row hfirst
      let key₀:=secondEncodedNonzeroRow (fun l=>(datum l).block) first row left 1 unit hf
      let key:=if second then reflectedNonzeroJointLabel key₀ else key₀
      let delta:=max (labelD reflected l Z-labelC reflected l Z) 0
      let rho:=frequencyLoss Z 32 ξ+reserve-err
      let Q:=sourceFReal n low b-delta-rho
      let d₂:=datum row.val.1
      let x:=childHighCoordinates (actualHighCoordinates reflected left second l d₂.C d₂.D d₂.inactive
        Z 1 (Real.logb Z (volume s)) (sourceAReal n low b) ξ reserve err) errv
      delta≤labelC reflected l Z ∧ x 2=Q ∧
        rawFrequencyNorm (nonzeroJointSourceRow key)≤Z^Q ∧ Q≤x 2+radialRound := by
  filter_upwards [FirstFamily.eventual_literal_high_frequency profileUpper err N hb herr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α DataLabel instα instDec instLabel n low b reflected second s A₁ A₂ D K R seed F ξ hH
    bin column datum first row hfirst reserve errv radialRound hξ hround hradius
    modifier l left unit hf key₀ key delta rho Q d₂ x
  have hg:=modified_deficit_and_coordinate n low b s A₁ A₂ D K R seed F (Z^(1:ℝ)) Z ξ hH hZ.1
    bin column reflected second d₂.C d₂.D d₂.inactive (Real.logb Z (volume s)) reserve err errv
  change delta≤labelC reflected l Z ∧ x 2=Q at hg
  have hfreq:=hZ.2 reflected second s modifier R seed 1 ξ hH bin column datum first row hfirst
    (sourceAReal n low b) reserve errv hξ hradius
  change rawFrequencyNorm (nonzeroJointSourceRow key)≤Z^(x 2) at hfreq
  refine ⟨hg.1,hg.2,?_,?_⟩
  · rwa [hg.2] at hfreq
  · rw [hg.2]
    linarith

end
end QRH.Record1252270103Source.RegularLowRetainedRadial
#print axioms QRH.Record1252270103Source.RegularLowRetainedRadial.eventual_literal_low_frequency
