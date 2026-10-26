import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondNormalizedRestriction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
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

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
