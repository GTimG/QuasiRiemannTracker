import Cycle25.Assembly.MomentData
import Cycle25.Assembly.SlotLengths
import OAI.NumberTheory.DirichletL.ParametersDetectorScales
import OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum

noncomputable section
open scoped BigOperators
namespace Cycle25.HighParameters

structure HighData (Δ : ℝ) where
  momentKappa : ℝ
  momentKappa_lo : 7/10 ≤ momentKappa
  momentKappa_hi : momentKappa ≤ 3/4
  momentKappa_beta : 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1 ≤ momentKappa
  momentKappa_exact : momentKappa = 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1
  t : ℝ
  N : ℕ
  ell : Fin N→ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0 < t
  t_delta : t<Δ/4
  t_gap : t ≤ Δ/100000
  t_small : t≤1/100000000
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=Cycle25.ell
  slots_bounds : ∀j,0 < ell j ∧ (7/8)*rmin ≤ ell j ∧ ell j≤(1/200)*t
  rmin_pos : 0 < rmin
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  epsilon_gap : ε < rmin*t
  e_pos : 0 < e
  e_small : e<1/1000
  kappa_pos : 0<κ
  kappa_small : κ≤1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps≤1
  sigma_pos : 0 < sigma
  detector_budget : 288*e+8*κ+2*cost≤ε/2
  phase_budget : 8*e*t+κ≤ε
  central_budget : (159*ε+t+t+7*t)+(12*e+eps*(N+8))+
    (t+t+t+t+t*Cycle25.ell+(13243/1000)*e)+2*t ≤ Δ/100
  geometric_budget : sigma+8*e+t/8 ≤ 1/20
  principal_budget : sigma+t/8 ≤ 1/4000
  window_budget : sigma+e ≤ Cycle25.theta*((7/8)*rmin)
  floor_budget : 26*e+(N+8)*eps+t+t*Cycle25.ell+t/8+sigma ≤ 1/100
  high_saving : sigma+t/8+t/8 ≤ Δ/100
  weighted_top : 3*t ≤ Cycle25.rowExtension
  height_choice : ∀J : ℝ,0 ≤ J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ < t ∧ 2*τ*(1+J) ≤ t ∧ τ*(2+4*eps) < t

def HighData.toMomentData {Δ : ℝ} (D : HighData Δ) : Cycle25.Weighted.MomentData where
  N := D.N
  ell := D.ell
  t := D.t
  ε := D.ε
  e := D.e
  t_pos := D.t_pos
  t_small := D.t_small
  slots_injective := D.slots_injective
  slots_bounds := fun j=>⟨(D.slots_bounds j).1,by
    have hh := (D.slots_bounds j).2.2
    linarith only [hh,D.t_small]⟩
  epsilon_pos := D.epsilon_pos
  epsilon_small := D.epsilon_small
  e_pos := D.e_pos

end Cycle25.HighParameters

end


/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the actual moment parameter and a loss budget relative to beta-theta. -/
