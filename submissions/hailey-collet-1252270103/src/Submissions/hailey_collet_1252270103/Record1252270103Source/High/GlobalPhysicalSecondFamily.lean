/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact second-family column identities with modified coefficients retained.
Adapted from pinned Cycle61 SecondWindows/SecondFamily. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondWindow
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonWindowColumn CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentSmooth CenteredMomentCauchy CenteredMomentLogDyadic
open CenteredMomentConjugateWindow CenteredMomentSectorLocalization
open Cycle61InitialMass Cycle61Moment RayFourExpansion
local notation "O"=>HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem modified_second_left_window (d : SecondInputDatum α)
    (modifier : Tuple d.slots→ℂ) (L : Ideal O) (χ ψ : RayCharacter)
    (V : ℝ→ℂ) (z : O) (θ : ℝ) :
    let src:=(modifiedDatumBlock d modifier).sector L χ ψ
    (Real.sqrt (volume d.input.toData):ℂ)⁻¹*
      leftColumn Finset.univ (fun I=>src.leftCoefficient I*idealRowHom z I) V src.leftLog θ=
      modifiedWindowColumn d.input modifier d.C d.hC d.R d.seed L (d.τ χ) d.input.t θ
        (dyadicScale (d.dyad 2)) V z := by
  dsimp only
  rw [←actual_modified_sector_window d.input modifier d.input.η (d.τ χ) χ
    d.block.frequency d.C d.hC d.R d.seed L d.input.t θ (dyadicScale (d.dyad 2)) V z
    (fun I hI hc v=>d.family.height_eq χ I hI (Or.inl hc) v)]
  congr 1
  simp only [leftColumn,rowPolynomial,CanonicalSectorSource.leftCoefficient,
    CanonicalSectorSource.leftLog,modifiedDatumBlock,SecondInputDatum.block,originalSecondBlock,
    SecondBlockSource.sector,SecondBlockSource.frequency,sectorElement_span]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem modified_second_right_window (d : SecondInputDatum α)
    (modifier : Tuple d.slots→ℂ) (L : Ideal O) (χ ψ : RayCharacter)
    (V : ℝ→ℂ) (z : O) (θ : ℝ) :
    let src:=(modifiedDatumBlock d modifier).sector L χ ψ
    (Real.sqrt (volume d.input.toData):ℂ)⁻¹*
      rightColumn Finset.univ (fun I=>src.rightCoefficient I*idealRowHom (-z) I) V src.rightLog θ=
      star (modifiedWindowColumn d.input modifier d.D d.hD d.R d.seed L (d.τ ψ⁻¹) d.input.t (-θ)
        (dyadicScale (d.dyad 3)) (fun x=>star (V x)) (-z)) := by
  dsimp only
  rw [←actual_modified_sector_window d.input modifier d.input.η (d.τ ψ⁻¹) ψ⁻¹
    d.block.frequency d.D d.hD d.R d.seed L d.input.t (-θ) (dyadicScale (d.dyad 3))
    (fun x=>star (V x)) (-z)
    (fun I hI hc v=>d.family.height_eq ψ⁻¹ I hI (Or.inr hc) v)]
  have hs : star ((Real.sqrt (volume d.input.toData):ℂ)⁻¹)=
      (Real.sqrt (volume d.input.toData):ℂ)⁻¹ := by simp
  simp only [rightColumn,rowPolynomial,CanonicalSectorSource.rightCoefficient,
    CanonicalSectorSource.rightLog,modifiedDatumBlock,SecondInputDatum.block,originalSecondBlock,
    SecondBlockSource.sector,SecondBlockSource.frequency,sectorElement_span,star_mul,star_sum,hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [←star_columnPhase,star_star]
  ring

theorem modified_second_family_left_column {Label : Type*}
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ) (w : Label→ℂ)
    (q : SecondSector (fun l=>modifiedDatumBlock (d l) (modifier l))) (t : ℝ) :
    leftColumn Finset.univ (secondJointLeft (fun l=>modifiedDatumBlock (d l) (modifier l)) w q)
      logAnnulus (secondLeftLog (modifiedDatumBlock (d q.1) (modifier q.1))) t=
      secondFamilyLeftScalar d w q*modifiedWindowColumn (d q.1).input (modifier q.1)
        (d q.1).C (d q.1).hC (d q.1).R (d q.1).seed q.2.1.val
        ((d q.1).τ q.2.2.1) (d q.1).input.t t (dyadicScale ((d q.1).dyad 2))
        logAnnulus q.2.2.2.2.val := by
  let v:=d q.1
  have he:=modified_second_left_window v (modifier q.1) q.2.1.val q.2.2.1 q.2.2.2.1
    logAnnulus q.2.2.2.2.val t
  have hS : (Real.sqrt (volume v.input.toData):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (volume_pos v.input.toData)).ne'
  have he':=congrArg (fun z : ℂ=>(Real.sqrt (volume v.input.toData):ℂ)*z) he
  simp only [←mul_assoc,mul_inv_cancel₀ hS,one_mul] at he'
  unfold secondFamilyLeftScalar
  rw [mul_assoc,←he']
  simp only [leftColumn,secondJointLeft,Finset.mul_sum,secondLeftLog,
    CanonicalSectorSource.leftLog,SecondBlockSource.sector,secondJointSource]
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [v,modifiedDatumBlock,SecondInputDatum.block,originalSecondBlock,SecondBlockSource.outside]
  ring

theorem modified_second_family_right_column {Label : Type*}
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ)
    (q : SecondSector (fun l=>modifiedDatumBlock (d l) (modifier l))) (t : ℝ) :
    rightColumn Finset.univ (secondJointRight (fun l=>modifiedDatumBlock (d l) (modifier l)) q)
      logAnnulus (secondRightLog (modifiedDatumBlock (d q.1) (modifier q.1))) t=
      secondFamilyRightScalar d q*star (modifiedWindowColumn (d q.1).input (modifier q.1)
        (d q.1).D (d q.1).hD (d q.1).R (d q.1).seed q.2.1.val
        ((d q.1).τ q.2.2.2.1⁻¹) (d q.1).input.t (-t) (dyadicScale ((d q.1).dyad 3))
        (fun x=>star (logAnnulus x)) (-q.2.2.2.2.val)) := by
  let v:=d q.1
  have he:=modified_second_right_window v (modifier q.1) q.2.1.val q.2.2.1 q.2.2.2.1
    logAnnulus q.2.2.2.2.val t
  have hS : (Real.sqrt (volume v.input.toData):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (volume_pos v.input.toData)).ne'
  have he':=congrArg (fun z : ℂ=>(Real.sqrt (volume v.input.toData):ℂ)*z) he
  simp only [←mul_assoc,mul_inv_cancel₀ hS,one_mul] at he'
  dsimp only [secondJointRight,secondJointSource,secondFamilyRightScalar,secondRightLog,
    modifiedDatumBlock,SecondInputDatum.block,originalSecondBlock,SecondBlockSource.sector]
  dsimp only [v,CanonicalSectorSource.rightLog,modifiedDatumBlock,SecondInputDatum.block,
    originalSecondBlock,SecondBlockSource.sector] at he'
  exact he'

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_left_window
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_right_window
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_family_left_column
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_family_right_column
