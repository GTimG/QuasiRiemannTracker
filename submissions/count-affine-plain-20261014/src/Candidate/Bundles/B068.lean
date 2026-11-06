/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B003
import Candidate.Bundles.B020
import Candidate.Bundles.B059
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSlotSelection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersDetectorScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersSlotLengths

/- BEGIN ORIGINAL Cycle25.Assembly.SlotLengths; sha256 2ede21ea3758219ef65c85f5566be816d590e9d44dd8cef9ab17d877a1794b7d -/
section
                                  
                                                        
namespace Cycle25.HighParameters
noncomputable section
open scoped BigOperators

theorem exists_distinct_slot_lengths (L : ℝ) (hL : 0 < L) :
    ∃N : ℕ,0 < N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0 < ell j ∧ ell j < L) ∧ (∑j,ell j)=Cycle25.ell := by
  have hscale : 0 < 6*Cycle25.ell := mul_pos (by norm_num) ell_pos
  obtain ⟨N,hN,old,hi,hb,hs⟩ := OAI.SevenEighths.Parameters.exists_distinct_slot_lengths
    (L/(6*Cycle25.ell)) (by positivity)
  refine ⟨N,hN,(fun j=>(6*Cycle25.ell:ℝ)*old j),?_,?_,?_⟩
  · intro j k he
    apply hi
    exact (mul_left_cancel₀ hscale.ne' he)
  · intro j
    constructor
    · exact mul_pos hscale (hb j).1
    · have hh := (hb j).2
      have hc := (lt_div_iff₀ hscale).mp hh
      nlinarith only [hc]
  · rw [←Finset.mul_sum,hs]
    ring

theorem exists_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0 < dmin) (hd : dmin ≤ dmax) (hm : 0 < mesh) (hR : 0 < R) :
    ∃N : ℕ,0 < N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0 < rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=Cycle25.ell ∧
      (∀j,0 < ell j ∧ dmax*rmin ≤ ell j ∧ ell j ≤ dmin*mesh ∧ ell j ≤ dmin*R) ∧
      (∀d : ℝ,dmin ≤ d → d ≤ dmax → ∀j,rmin ≤ ell j/d ∧ ell j/d ≤ mesh ∧ ell j/d ≤ R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0 < dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0 < rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin ≤ ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k ≤ dmin*mesh ∧ ell k ≤ dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0 < d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d ≤ dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end
end Cycle25.HighParameters

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Assembly.SlotLengths -/

/- BEGIN ORIGINAL Cycle25.Assembly.HighData; sha256 3a5f7d4a45e99294329af20a8ba2391baf6ac3c1e0a9c0c8478f3b99c2db42fa -/
section
                                  
                                   
                                                           
                                                     

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

end
/- END ORIGINAL Cycle25.Assembly.HighData -/

/- BEGIN ORIGINAL Cycle25.Assembly.HighDataFine; sha256 e760738de7c4bfd5033f9e40f5e5b48c6d730a896956e62db7b4cf68553a2b49 -/
section
                                

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

end
/- END ORIGINAL Cycle25.Assembly.HighDataFine -/

/- BEGIN ORIGINAL Cycle25.Numerator.SlotSelection; sha256 1effe0bfeef42bad8e019c9acc4e5a4584e5714229f7ddff57a2bd2cc996b0b5 -/
section
                                    
                            
                                                              
                                                                  

/-!
Greedy prime-slot selection for the reflected numerator. Error slots have gain zero,
but retain their lengths in the denominator of q. No amplitude frontier is assumed.
-/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Numerator.SlotSelection
open OAI.SevenEighths
open HeckeDetectorSlotSelection HeckeDetectorPhysicalSelection
open Cycle25

def baseCapacity (kap d : ℝ) : ℝ := (2*ly/d-1)/(6*kap)
def reflectedCapacity (kap d v : ℝ) : ℝ := max 0 (baseCapacity kap d-v/(3*kap))

theorem reflectedCapacity_nonneg (kap d v : ℝ) : 0 ≤ reflectedCapacity kap d v := le_max_left _ _

theorem baseCapacity_lt_supply {kap d : ℝ} (hk : 7/10 ≤ kap) (hd : (1/2:ℝ) ≤ d) :
    baseCapacity kap d < ell/d := by
  have hd0 : 0 < d := by linarith
  have hk0 : kap ≠ 0 := by linarith
  have hh := div_lt_div_of_pos_right (numerator_supply_all hk hd) hd0
  have heq : ((2*ly-d)/(6*kap))/d = baseCapacity kap d := by
    unfold baseCapacity
    field_simp
  rwa [heq] at hh

theorem reflectedCapacity_le_supply {kap d v : ℝ} (hk : 7/10 ≤ kap)
    (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) : reflectedCapacity kap d v ≤ ell/d := by
  apply max_le
  · exact div_nonneg ell_pos.le (by linarith)
  · have hh := baseCapacity_lt_supply hk hd
    have hdiv : 0 ≤ v/(3*kap) := div_nonneg hv (by linarith)
    linarith

theorem reflectedCapacity_gain {kap d v q : ℝ} (hq : 0 ≤ q) :
    q*baseCapacity kap d-q*v/(3*kap) ≤ q*reflectedCapacity kap d v := by
  have hh := mul_le_mul_of_nonneg_left (le_max_right 0 (baseCapacity kap d-v/(3*kap))) hq
  simpa only [mul_sub, mul_div_assoc, reflectedCapacity] using hh

/-- Exact selection from a main mask. Zero-gain error slots remain in the mean's
normalizing sum, and are excluded only from the selected product. -/
theorem zero_error_whole_slots {α : Type*} (slots main : Finset α) (w g : α→ℝ)
    (δ mesh z : ℝ) (hδ : 0 ≤ δ) (hmesh : 0 ≤ mesh)
    (hw : ∀i∈slots,0 ≤ w i) (hwm : ∀i∈slots,w i ≤ mesh)
    (hL : 0 < ∑i∈slots,w i)
    (hg : ∀i∈slots,0 ≤ g i ∧ g i ≤ δ/2)
    (herror : ∀i∈slots,i∉main → g i=0)
    (hz : 0 ≤ z) (hzL : z ≤ ∑i∈slots,w i) :
    ∃selected : Finset α,selected⊆slots ∧ selected⊆main ∧
      (∀i∈selected,0 < g i) ∧ (∑i∈selected,w i) ≤ z ∧
      weightedMean slots w g*z-(δ/2)*mesh ≤ ∑i∈selected,w i*g i ∧
      ∀U : ℝ,1 ≤ U → ∀Q : α→ℂ,
        (∀i∈slots,0 < g i → U^(2*w i*g i) ≤ ‖Q i‖^2) →
        U^(2*weightedMean slots w g*z-δ*mesh) ≤ ‖∏i∈selected,Q i‖^2 := by
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ hw hL hg
  have hmean : weightedMean slots w g*(∑i∈slots,w i) ≤ ∑i∈slots,w i*max (g i) 0 := by
    have he : (∑i∈slots,w i*max (g i) 0)=∑i∈slots,w i*g i :=
      Finset.sum_congr rfl (fun i hi=>by rw [max_eq_left (hg i hi).1])
    rw [he]
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨T,hTs,hTpos,hTz,hgain⟩ := whole_positive_slots slots w g (δ/2) mesh
    (by positivity) hmesh hw hwm (fun i hi=>(hg i hi).2)
    (weightedMean slots w g) z hq hqδ hz hzL hmean
  have hTm : T⊆main := by
    intro i hi
    by_contra hn
    have he := herror i (hTs hi) hn
    have hh := hTpos i hi
    rw [he] at hh
    exact lt_irrefl 0 hh
  refine ⟨T,hTs,hTm,hTpos,hTz,hgain,?_⟩
  intro U hU Q hQ
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  calc
    _ ≤ U^(∑i∈T,2*w i*g i) := Real.rpow_le_rpow_of_exponent_le hU (by
      have he : (∑i∈T,2*w i*g i)=2*(∑i∈T,w i*g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linarith only [hgain])
    _ = ∏i∈T,U^(2*w i*g i) := Real.rpow_sum_of_pos hU0 _ _
    _ ≤ ∏i∈T,‖Q i‖^2 := Finset.prod_le_prod₀ (fun i hi=>Real.rpow_nonneg hU0.le _)
      (fun i hi=>hQ i (hTs hi) (hTpos i hi))
    _ = _ := by rw [norm_prod,Finset.prod_pow]

theorem highData_weighted_selection {Δ : ℝ} (D : HighParameters.HighData Δ)
    (hfine : ∀j,D.ell j ≤ sourceMesh D.t/200)
    (d v δ : ℝ) (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (main : Finset (Fin D.N)) (g : Fin D.N→ℝ)
    (hg : ∀j,0 ≤ g j ∧ g j ≤ δ/2) (herror : ∀j,j∉main → g j=0) :
    let widths := fun j=>D.ell j/d
    let q := weightedMean Finset.univ widths g
    let mesh := sourceMesh D.t
    q = (∑j,widths j*g j)/(ell/d) ∧ 0 ≤ q ∧ q ≤ δ/2 ∧
    ∃selected : Finset (Fin D.N),selected⊆main ∧ (∀j∈selected,0 < g j) ∧
      (∑j∈selected,widths j) ≤ reflectedCapacity D.momentKappa d v ∧
      q*reflectedCapacity D.momentKappa d v-(δ/2)*mesh ≤ ∑j∈selected,widths j*g j ∧
      q*baseCapacity D.momentKappa d-q*v/(3*D.momentKappa)-(δ/2)*mesh ≤ ∑j∈selected,widths j*g j ∧
      ∀U : ℝ,1 ≤ U → ∀Q : Fin D.N→ℂ,
        (∀j,0 < g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) →
        U^(2*q*reflectedCapacity D.momentKappa d v-δ*mesh) ≤ ‖∏j∈selected,Q j‖^2 := by
  have hd0 : 0 < d := by linarith only [hd]
  let widths := fun j=>D.ell j/d
  have hsum : (∑j,widths j)=ell/d := by
    dsimp [widths]
    rw [←Finset.sum_div,D.slots_sum]
  have hL : 0 < ∑j,widths j := by rw [hsum];exact div_pos ell_pos hd0
  have hw (j : Fin D.N) : 0 ≤ widths j := (div_pos (D.slots_bounds j).1 hd0).le
  have hmesh := sourceMesh_pos D.t_pos
  have hwm (j : Fin D.N) : widths j ≤ sourceMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have hj := hfine j
    nlinarith only [hj,hd,hmesh]
  have hzL : reflectedCapacity D.momentKappa d v ≤ ∑j,widths j := by
    rw [hsum]
    exact reflectedCapacity_le_supply D.momentKappa_lo hd hv
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds Finset.univ widths g δ (fun j _=>hw j) hL (fun j _=>hg j)
  obtain ⟨T,_,hT,hTpos,hTz,hgain,hspike⟩ := zero_error_whole_slots Finset.univ main widths g δ
    (sourceMesh D.t) (reflectedCapacity D.momentKappa d v) hδ hmesh.le (fun j _=>hw j)
    (fun j _=>hwm j) hL (fun j _=>hg j) (fun j _=>herror j)
    (reflectedCapacity_nonneg D.momentKappa d v) hzL
  refine ⟨?_,hq,hqδ,T,hT,hTpos,hTz,hgain,?_,?_⟩
  · unfold weightedMean
    rw [hsum]
  · exact (sub_le_sub_right (reflectedCapacity_gain hq) _).trans hgain
  · intro U hU Q hQ
    exact hspike U hU Q (fun j _=>hQ j)

end Cycle25.Numerator.SlotSelection

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.SlotSelection -/
