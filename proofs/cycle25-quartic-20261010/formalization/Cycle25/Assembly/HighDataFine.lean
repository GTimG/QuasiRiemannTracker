import Cycle25.Assembly.HighData

noncomputable section
open scoped BigOperators

namespace Cycle25.HighParameters
open OAI.SevenEighths.Parameters

theorem exists_high_data_fine (Δ:ℝ)(hΔ:0<Δ)
    (kap : ℝ) (hkaplo : 7/10 ≤ kap) (hkaphi : kap ≤ 3/4)
    (hkapbeta : 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1 ≤ kap)
    (hkapexact : kap = 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1)
    (mesh:ℝ→ℝ)
    (hmesh:∀t:ℝ,0 < t→0 < mesh t):
    ∃D:HighData Δ,∀j,D.ell j ≤ mesh D.t/200:=by
  let t := min (Δ/100000) (1/100000000)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htΔ : t < Δ/4 := by have hh := min_le_left (Δ/100000) (1/100000000); dsimp [t]; linarith only [hh,hΔ]
  have htgap : t ≤ Δ/100000 := min_le_left _ _
  have ht1 : t ≤ 1/100000000 := min_le_right _ _
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    Cycle25.HighParameters.exists_physical_slot_lengths (1/200) (7/8) (min t (mesh t)) t (by norm_num) (by norm_num)
      (lt_min ht (hmesh t ht)) ht
  let allowance := t/((N:ℝ)+2000)
  have ha : 0 < allowance := div_pos ht (by positivity)
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0 < small := lt_min ha (div_pos ht (by positivity))
  have hsa : small ≤ allowance := min_le_left _ _
  have hst : small ≤ t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small ≤ t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0 < eps := by dsimp [eps];positivity
  have hepss : eps ≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have heN : ((N:ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps ≤ t := by nlinarith only [heN, heps.le]
  have het : 2000*e ≤ t := by linarith only [hea, hst0]
  have hεt : 2000*ε ≤ t := by linarith only [hεa,hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ t/2 := min_le_left _ _
  have hsell : sigma ≤ ellMin/4 := min_le_right _ _
  refine ⟨{
    momentKappa:=kap,momentKappa_lo:=hkaplo,momentKappa_hi:=hkaphi,momentKappa_beta:=hkapbeta,
    momentKappa_exact:=hkapexact,
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_gap:=htgap,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.2⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,central_budget:=by
      have hell := Cycle25.ell_lt_one_fifth
      have hprod := mul_le_mul_of_nonneg_left hell.le ht.le
      nlinarith only [hεt,het,he8,ht1,htgap,hprod,ht]
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by
      change sigma+e ≤ Cycle25.theta*ellMin
      have hc := mul_le_mul_of_nonneg_right Cycle25.theta_gt_half.le hmin.le
      linarith only [hsell,heell,hmin,hc]
    floor_budget:=by
      have hprod := mul_le_mul_of_nonneg_left Cycle25.ell_lt_one_fifth.le ht.le
      linarith only [hst2,het,he8,ht1,hprod]
    high_saving:=by linarith only [hst2,htgap,ht]
    weighted_top:=by norm_num [Cycle25.rowExtension]; linarith only [ht1]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0≤τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · intro j
    change ell j ≤ mesh t/200
    calc
      ell j≤(1/200:ℝ)*min t (mesh t):=(hbounds j).2.2.1
      _≤(1/200:ℝ)*mesh t:=mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=mesh t/200:=by ring

theorem fine_slot_widths {Δ:ℝ}(D:HighData Δ)(mesh:ℝ→ℝ)
    (hmesh:0 < mesh D.t)(hfine:∀j,D.ell j ≤ mesh D.t/200)
    (d:ℝ)(hd:(1/200:ℝ) ≤ d)(j:Fin D.N):
    0 < D.ell j/d ∧ D.ell j/d ≤ mesh D.t:=by
  have hd0:0 < d:=by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0,(div_le_iff₀ hd0).mpr ?_⟩
  have hh:=hfine j
  nlinarith

end Cycle25.HighParameters

end


/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
