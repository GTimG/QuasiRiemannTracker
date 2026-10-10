import WeightedQRH.MomentData
import WeightedQRH.HighRows.SlotLengths
import OAI.NumberTheory.DirichletL.ParametersDetectorScales

noncomputable section
open scoped BigOperators
namespace WeightedQRH.HighParameters

structure HighData (Δ : ℝ) where
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
  t_small : t≤1/100000000
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=167/1000
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
    (t+t+t+t+t*167/1000+(13243/1000)*e)+2*t ≤ 1/40000
  geometric_budget : sigma+8*e+t/8 ≤ 1/20
  principal_budget : sigma+t/8 ≤ 1/4000
  window_budget : sigma+e ≤ WeightedQRH.theta*((7/8)*rmin)
  floor_budget : 26*e+(N+8)*eps+t+t*167/1000+t/8+sigma ≤ 1/100
  high_saving : sigma+t/8+t/8 ≤ 1/40000
  weighted_top : 3*t ≤ WeightedQRH.rowExtension
  height_choice : ∀J : ℝ,0 ≤ J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ < t ∧ 2*τ*(1+J) ≤ t ∧ τ*(2+4*eps) < t

def HighData.toMomentData {Δ : ℝ} (D : HighData Δ) : WeightedQRH.MomentData where
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

end WeightedQRH.HighParameters

end

