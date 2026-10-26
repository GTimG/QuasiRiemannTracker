/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform ambient-type version of the checked modified second-ratio contraction.
Adapted from GlobalPhysicalSecondContraction and the pinned Cycle61
SecondRetainedContraction; their inherited notices remain required. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondContraction
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Contraction
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentLogDyadic
open CenteredMomentSecondPhysicalBlock
open Cycle61InitialMass Cycle61Moment
local notation "O"=>HeckeFamily.O
open QRH.Record1252270103Source.High.GlobalPhysical

/-- Joint restricted physical block contraction from literal positive sums
on each exact ratio fiber. Constants precede the moving datum family. -/
theorem restricted_modified_second_ratio_uniform (W : 𝓢(ℝ,ℂ))(A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀{α : Type*}[Fintype α][DecidableEq α]
      {Label : Type*}[Fintype Label]
    (d : Label→SecondInputDatum α)(modifier : ∀l,Tuple (d l).slots→ℂ)(w : Label→ℂ)(E H : ℤ→ℝ),
      (∀r∈secondRatioBins (fun l=>modifiedDatumBlock (d l) (modifier l)),0≤E r) →
      (∀r∈secondRatioBins (fun l=>modifiedDatumBlock (d l) (modifier l)),0<H r) →
      ModifiedSecondNormalizedBound W degree windowDegree d modifier w E H →
      ‖∑l,w l*(modifiedDatumBlock (d l) (modifier l)).value W‖≤
        C*∑r∈secondRatioBins (fun l=>modifiedDatumBlock (d l) (modifier l)),E r/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hcon⟩:=actual_second_ratio_contraction W A degree
  let IL:=|∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity logAnnulus hc hs u‖|
  let IR:=|∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hs) u‖|
  refine ⟨C*IL*IR,by dsimp [IL,IR];positivity,?_⟩
  intro α _ _ Label _ d modifier w E H hE hH hnorm
  have hh:=hcon (fun l=>modifiedDatumBlock (d l) (modifier l)) w (fun r=>E r*IL*IR)
    (fun r hr=>by have he:=hE r hr; dsimp [IL,IR];positivity) ?_
  · apply hh.trans_eq
    simp_rw [show ∀ r : ℤ, E r*IL*IR/(1+dyadicScale r)^A =
      E r/(1+dyadicScale r)^A*IL*IR by intro r; ring]
    rw [←Finset.sum_mul,←Finset.sum_mul]
    ring
  · intro r hr t
    let datum:=fun l : SecondRatioFiber (fun l=>modifiedDatumBlock (d l) (modifier l)) r=>d l.val
    let src:=fun l : SecondRatioFiber (fun l=>modifiedDatumBlock (d l) (modifier l)) r=>modifiedDatumBlock (datum l) (modifier l.val)
    let weight:=fun l : SecondRatioFiber (fun l=>modifiedDatumBlock (d l) (modifier l)) r=>w l.val
    let ew:=secondEffectiveWeight src weight W
    have hleft:=hnorm r hr false t
    have hright:=hnorm r hr true t
    have hEt : 0≤E r*H r*(1+‖t‖)^degree := by have he:=hE r hr; have hh:=hH r hr; positivity
    have hEr : 0≤E r/H r*(1+‖t‖)^degree := by have he:=hE r hr; have hh:=hH r hr; positivity
    have hb:=modified_balanced_energy_from_normalized datum (fun l=>modifier l.val) ew t windowDegree
      (E r*H r*(1+‖t‖)^degree) (E r/H r*(1+‖t‖)^degree) hEt hEr hc hs
      (fun u=>by simpa only [modifiedSecondNormalizedSum,Bool.false_eq_true,ite_false] using hleft u)
      (fun u=>by simpa only [modifiedSecondNormalizedSum,ite_true] using hright u)
    rw [normalized_balance_sqrt (E r) (H r) ((1+‖t‖)^degree) (hE r hr) (hH r hr)
      (by positivity)] at hb
    exact hb.trans_eq (by dsimp [IL,IR];ring)

end
end QRH.Record1252270103Source.Contraction
#print axioms QRH.Record1252270103Source.Contraction.restricted_modified_second_ratio_uniform
