/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.SecondNormalizedRestriction

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentLogDyadic
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- A uniform estimate for the whole positive family also estimates each
ratio fiber. The two inner Mellin energies use H=1; any outer physical
height factor remains in E. -/
theorem second_normalized_bound_of_full (W : 𝓢(ℝ,ℂ)) (degree windowDegree : ℕ)
    (d : Label→SecondInputDatum α)(w : Label→ℂ)(E : ℝ)
    (hfull : ∀(reflected : Bool)(t u : ℝ),
      secondNormalizedSum reflected d
        (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
      (E*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) :
    SecondNormalizedBound W degree windowDegree d w (fun _=>E) (fun _=>1) := by
  intro r _ reflected t u
  have hh:=(second_normalized_ratio_le W r reflected d w t u).trans (hfull reflected t u)
  simpa only [div_one,mul_one,ite_self] using hh

/-- Complete normalized energies control the retained block sum. Only the
number of ratio bins is paid; the source-label count never appears. -/
theorem retained_from_full_normalized (W : 𝓢(ℝ,ℂ))(degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀{L : Type*}[Fintype L]
      (d : L→SecondInputDatum α)(w : L→ℂ)(E : ℝ),0≤E →
      (∀(reflected : Bool)(t u : ℝ),
        secondNormalizedSum reflected d
          (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
        (E*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) →
      ‖∑l,w l*(d l).block.value W‖≤
        C*((secondRatioBins (fun l=>(d l).block)).card:ℝ)*E := by
  obtain ⟨C,hC,hcon⟩:=restricted_second_ratio_from_normalized (α:=α)
    W 0 degree windowDegree hc hs
  refine ⟨C,hC,?_⟩
  intro L _ d w E hE hfull
  have hh:=hcon d w (fun _=>E) (fun _=>1)
    (fun _ _=>hE) (fun _ _=>by norm_num)
    (second_normalized_bound_of_full W degree windowDegree d w E hfull)
  simpa only [pow_zero,div_one,Finset.sum_const,nsmul_eq_mul,mul_assoc] using hh

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.second_normalized_bound_of_full
#print axioms OAI.SevenEighths.Cycle62InitialMass.retained_from_full_normalized
