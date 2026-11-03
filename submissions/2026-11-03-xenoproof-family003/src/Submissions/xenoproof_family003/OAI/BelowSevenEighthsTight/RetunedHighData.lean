import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSlotLengths
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersDetectorScales

/- Parameter selection only. This record does not assert existence of an
   analytic detector, moment estimate, contour identity, or common probe. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.Parameters
noncomputable section
open scoped BigOperators

structure RetunedHighData (Δ L margin mesh : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N → ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0 < t
  t_delta : t < Δ/4
  t_mesh : t < mesh
  t_small : t ≤ 1/100000000
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑ j, ell j) = L
  slots_bounds : ∀ j, 0 < ell j ∧ (7/8)*rmin ≤ ell j ∧ ell j ≤ (1/200)*t
  rmin_pos : 0 < rmin
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1/1000
  epsilon_gap : ε < rmin*t
  e_pos : 0 < e
  e_small : e < 1/1000
  kappa_pos : 0 < κ
  kappa_small : κ ≤ 1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  sigma_pos : 0 < sigma
  detector_budget : 288*e+8*κ+2*cost ≤ ε/2
  phase_budget : 8*e*t+κ ≤ ε
  count_budget : 159*ε+t+t+7*t ≤ 1/32
  central_budget : ∀ W : ℝ, 0 ≤ W → W ≤ 1 →
    W*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
      (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t ≤ margin
  geometric_budget : sigma+8*e+t/8 ≤ 63/800
  principal_budget : sigma+t/8 ≤ 17/48000
  window_budget : sigma+e ≤ (7/8)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+t/6+t/8+sigma ≤ 7/1200
  high_saving : sigma+t/8+t/8 ≤ t
  height_choice : ∀ J : ℝ, 0 ≤ J → ∃ τ : ℝ, 0 < τ ∧ τ < (1/200)/2 ∧
    4*τ < (1/200)*cost ∧ τ < t ∧ 2*τ*(1+J) ≤ t ∧ τ*(2+4*eps) < t

theorem exists_retuned_high_data (Δ L margin mesh : ℝ)
    (hΔ : 0 < Δ) (hL : 0 < L) (hm : 0 < margin) (hmesh : 0 < mesh) :
    Nonempty (RetunedHighData Δ L margin mesh) := by
  let t := min (Δ/8) (min (mesh/2) (min (1/1000000000000) (margin/1000)))
  have ht : 0 < t := lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by norm_num) (by positivity)))
  have htΔ : t ≤ Δ/8 := min_le_left _ _
  have htmesh : t ≤ mesh/2 := (min_le_right _ _).trans (min_le_left _ _)
  have htt : t ≤ min (1/1000000000000) (margin/1000) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have ht1 : t ≤ 1/1000000000000 := htt.trans (min_le_left _ _)
  have htm : t ≤ margin/1000 := htt.trans (min_le_right _ _)
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_retuned_physical_slot_lengths L (1/200) (7/8) t t
      hL (by norm_num) (by norm_num) ht ht
  let small := t/((N:ℝ)+2000)
  have hsmall : 0 < small := div_pos ht (by positivity)
  have hst0 : small ≤ t/2000 :=
    div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
      hdet,hphase,_,_,_,_,_⟩ :=
    OAI.SevenEighths.Parameters.exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepss : eps ≤ small := by dsimp [eps]; linarith only [hsmall]
  have heps1 : eps ≤ 1 := by linarith only [hepss,hst0,ht1]
  have heN : ((N:ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ (show 0 < (N:ℝ)+2000 by positivity)).mp hepss
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps ≤ t := by nlinarith only [heN,heps.le]
  have het : 2000*e ≤ t := by linarith only [hea,hst0]
  have hεt : 2000*ε ≤ t := by linarith only [hεa,hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ t/2 := min_le_left _ _
  have hsell : sigma ≤ ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=by linarith,t_mesh:=by linarith,t_small:=by linarith
    slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.1⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs
    detector_budget:=by linarith only [hdet]
    phase_budget:=hphase
    count_budget:=by linarith only [hεt,ht1]
    central_budget:=?_
    geometric_budget:=by linarith only [hst2,het,ht1]
    principal_budget:=by linarith only [hst2,ht1]
    window_budget:=by change sigma+e ≤ (7/8)*ellMin; linarith only [hsell,heell,hmin]
    floor_budget:=by linarith only [hst2,het,he8,ht1]
    high_saving:=by linarith only [hst2,ht]
    height_choice:=?_ }⟩
  · intro W hW hWu
    have hcount : 0 ≤ 159*ε+t+t+7*t := by positivity
    have hw := mul_le_mul_of_nonneg_right hWu hcount
    linarith only [hw,hεt,het,he8,htm,ht]
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0 < τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ ≤ (1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ ≤ 1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0 ≤ τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc,hcost],
      by nlinarith only [hτJ,hprod,htau],by nlinarith only [hτJ,hprod,htau],
      by nlinarith only [hτJ,hprod,hprodeps,htau]⟩

#print axioms exists_retuned_high_data
end
end BelowSevenEighthsTight.Parameters
