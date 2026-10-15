/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryFinalParameters
import Candidate.Cycle62.Moment.HighParameters

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open Cycle62Moment

/-- Use one common cutoff for both canonical branches after the high density
degree is known. All other high-source parameters stay unchanged. -/
def geometryCommonHighParameters (P : HighSourceParameters) (μ : ℝ) (J : ℕ)
    (hμ : 0<μ) (hs : 0<P.vslot) (hp : 0<P.vplain) : HighSourceParameters :=
  { P with
    τ := geometryFinalHeight μ P.d P.vslot P.vplain J
    hτ := (geometry_final_height_gates μ P.d P.vslot P.vplain J hμ P.hd hs hp).1 }

/-- These are the exact high gates and the strict low gate for the same
selector threshold. The low dictionary rate is the high slot rate. -/
theorem geometry_common_high_parameter_gates (P : HighSourceParameters) (μ : ℝ)
    (J : ℕ) (hμ : 0<μ) (hs : 0<P.vslot) (hp : 0<P.vplain) :
    let Q := geometryCommonHighParameters P μ J hμ hs hp
    Q.τ=geometryFinalHeight μ P.d P.vslot P.vplain J ∧
      Q.e=P.e ∧ Q.κ=P.κ ∧ Q.vslot=P.vslot ∧ Q.vplain=P.vplain ∧ Q.d=P.d ∧
      0<Q.τ ∧ Q.τ≤μ/16 ∧ 2*Q.τ<Q.d*Q.vslot ∧
      8*Q.τ≤Q.d*Q.vslot ∧ 16*Q.τ≤Q.d*Q.vplain ∧
      2*Q.τ*((J:ℝ)+1)≤μ/8 := by
  intro Q
  have h := geometry_final_height_gates μ P.d P.vslot P.vplain J hμ P.hd hs hp
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,h.1,h.2.1,?_,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  change 2*(geometryFinalHeight μ P.d P.vslot P.vplain J)<P.d*P.vslot
  linarith [h.1,h.2.2.1]

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_common_high_parameter_gates
