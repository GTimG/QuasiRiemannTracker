/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted from Cycle61 SecondFullNormalizedContraction, preserving the full
modified coefficient and a constant uniform in ambient and label types. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Contraction.SelectedFullNormalizedRestriction
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Contraction
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentLogDyadic
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentAddedZeroUniform
open CenteredMomentSecondPhysicalBlock
open Cycle61InitialMass Cycle61Moment
open QRH.Record1252270103Source.High.GlobalPhysical
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

theorem modified_normalized_bound_of_full (W : 𝓢(ℝ,ℂ)) (degree windowDegree : ℕ)
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ)
    (w : Label→ℂ) (E : ℝ)
    (hfull : ∀(reflected : Bool)(t u : ℝ),
      modifiedSecondNormalizedSum reflected d modifier
        (secondEffectiveWeight (fun l=>modifiedDatumBlock (d l) (modifier l)) w W) t u≤
      (E*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) :
    ModifiedSecondNormalizedBound W degree windowDegree d modifier w (fun _=>E) (fun _=>1) := by
  intro r _ reflected t u
  have hh:=(modified_normalized_ratio_le W r reflected d modifier w t u).trans (hfull reflected t u)
  simpa only [div_one,mul_one,ite_self] using hh

/-- Only ratio bins are paid, and the constant precedes both moving types. -/
theorem modified_retained_from_full_normalized
    (W : 𝓢(ℝ,ℂ)) (degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀{α : Type*}[Fintype α][DecidableEq α]
      {Label : Type*}[Fintype Label]
      (d : Label→SecondInputDatum α)(modifier : ∀l,Tuple (d l).slots→ℂ)
      (w : Label→ℂ)(E : ℝ),0≤E→
      (∀(reflected : Bool)(t u : ℝ),
        modifiedSecondNormalizedSum reflected d modifier
          (secondEffectiveWeight (fun l=>modifiedDatumBlock (d l) (modifier l)) w W) t u≤
        (E*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree))→
      ‖∑l,w l*(modifiedDatumBlock (d l) (modifier l)).value W‖≤
        C*((secondRatioBins (fun l=>modifiedDatumBlock (d l) (modifier l))).card:ℝ)*E := by
  obtain ⟨C,hC,hcon⟩:=restricted_modified_second_ratio_uniform W 0 degree windowDegree hc hs
  refine ⟨C,hC,?_⟩
  intro α _ _ Label _ d modifier w E hE hfull
  have hh:=hcon d modifier w (fun _=>E) (fun _=>1)
    (fun _ _=>hE) (fun _ _=>by norm_num)
    (modified_normalized_bound_of_full W degree windowDegree d modifier w E hfull)
  simpa only [pow_zero,div_one,Finset.sum_const,nsmul_eq_mul,mul_assoc] using hh

end
end QRH.Record1252270103Source.Contraction
#print axioms QRH.Record1252270103Source.Contraction.modified_normalized_bound_of_full
#print axioms QRH.Record1252270103Source.Contraction.modified_retained_from_full_normalized
