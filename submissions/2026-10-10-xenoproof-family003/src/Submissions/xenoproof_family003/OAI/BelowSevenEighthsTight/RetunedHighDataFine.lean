import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedHighData

/- UNVERIFIED: fine mesh selected after t but before N and the late height.
   Includes the actual total-length mesh loss; no analytic moment assertion. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.Parameters
noncomputable section
open scoped BigOperators

theorem exists_retuned_high_data_fine (Δ L margin mesh : ℝ)
    (hΔ : 0 < Δ) (hL : 0 < L) (hm : 0 < margin) (hmesh : 0 < mesh)
    (hL1 : L≤1/5) (fine : ℝ→ℝ) (hfine : ∀t : ℝ,0<t→0<fine t) :
    ∃D : RetunedHighData Δ L margin mesh,
      (∀j,D.ell j≤fine D.t/200) ∧
      (∀W : ℝ,0≤W→W≤1→
        W*(159*D.ε+D.t+D.t+7*D.t)+2*D.t+(3/2)*(2*D.t)+
          (26*D.e+(D.N+8)*D.eps+D.t+L*D.t)+(D.t+D.t+D.t)+D.t≤margin) := by
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
    exists_retuned_physical_slot_lengths L (1/200) (7/8) (min t (fine t)) t
      hL (by norm_num) (by norm_num) (lt_min ht (hfine t ht)) ht
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
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.2⟩
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
    height_choice:=?_ },?_,?_⟩
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

  · intro j
    change ell j≤fine t/200
    calc
      ell j≤(1/200:ℝ)*min t (fine t) := (hbounds j).2.2.1
      _≤(1/200:ℝ)*fine t := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=fine t/200 := by ring
  · intro W hW hWu
    change W*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
      (26*e+(N+8)*eps+t+L*t)+(t+t+t)+t≤margin
    have hcount : 0≤159*ε+t+t+7*t := by positivity
    have hw := mul_le_mul_of_nonneg_right hWu hcount
    have hLt := mul_le_mul_of_nonneg_right hL1 ht.le
    linarith only [hw,hεt,het,he8,htm,ht,hLt]

theorem retuned_fine_slot_widths {Δ L margin mesh : ℝ}
    (D : RetunedHighData Δ L margin mesh) (fine : ℝ) (hfine : 0<fine)
    (hslots : ∀j,D.ell j≤fine/200) (d : ℝ) (hd : (1/200:ℝ)≤d) (j : Fin D.N) :
    0<D.ell j/d ∧ D.ell j/d≤fine := by
  have hd0 : 0<d := by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0,(div_le_iff₀ hd0).mpr ?_⟩
  nlinarith [hslots j]

#print axioms exists_retuned_high_data_fine
#print axioms retuned_fine_slot_widths
end
end BelowSevenEighthsTight.Parameters
