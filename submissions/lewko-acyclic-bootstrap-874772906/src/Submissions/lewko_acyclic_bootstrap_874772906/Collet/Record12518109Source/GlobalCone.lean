/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.FiniteCone
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.PairedValuations
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open scoped BigOperators
open Record12518109Admission

def minMaxLinear (A B C D E : ℝ) (a x : Fin 8→ℝ) : ℝ :=
  minMaxCone A B C D E (x 0) (x 1)+firstLinear a x

theorem minMaxLinear_weighted {ι : Type*} (s : Finset ι) (i j : ι→ℕ)
    (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t) (A B C D E : ℝ) (a : Fin 8→ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (∑t∈s,w t*minMaxLinear A B C D E a (firstPoint (i t) (j t))) ≤
      minMaxLinear A B C D E a (firstWeighted s i j w) := by
  have h := minMaxCone_weighted s w (fun t => (i t:ℝ)) (fun t => (j t:ℝ))
    hw A B C D E hC hD hE
  simp only [minMaxLinear,mul_add,Finset.sum_add_distrib,firstLinear_weighted]
  simpa only [firstWeighted,firstPoint,Matrix.cons_val_zero,Matrix.cons_val_one,add_comm] using
    add_le_add_right h (∑t∈s,w t*firstLinear a (firstPoint (i t) (j t)))

def globalOrdered (c : Cell) (v : Fin 8→ℝ) : ℝ :=
  let k:=c.q/K
  let ell:=c.q/c.priorL
  let B:=c.priorB
  let ws:ℝ:=17/50
  let wl:ℝ:=17/25
  firstLinear ![-(2-ws-wl)*k-1-ws*ell-wl*ell*B,-1-wl*ell+wl*ell*B,
    2,1+ws*(-2+ell*B)+wl*(-2+ell*B),ws*(1-ell*B),wl*(1-ell*B),ws,wl] v

def globalMixed (c : Cell) (ν : ℝ) (v : Fin 8→ℝ) : ℝ :=
  minMaxLinear (d ν*(1+omega*(c.q/c.priorL))) (d ν+etaD ν)
    (d ν*(1-omega)*(c.q/K)) (d ν*omega*(c.q/c.priorL)*c.priorB)
    (d ν-rr ν)
    ![0,0,-2*d ν,2*d ν*omega-d ν*omega*(c.q/c.priorL)*c.priorB+rr ν,
      -d ν*omega*(1-(c.q/c.priorL)*c.priorB),-rr ν,-d ν*omega,-d ν] v

def globalPaired (c : Cell) (l r : ℝ) (v : Fin 8→ℝ) : ℝ :=
  minMaxLinear (l+1-gamma c) (r+1-gamma c) 0 (1-rho l) (1-rho r)
    ![0,0,-2,1+rho l+rho r,-rho l,-rho r,-1,-1] v

theorem globalOrdered_point (c : Cell) (i j : ℕ) :
    globalOrdered c (firstPoint i j) = orderedLow c i j := by
  simp [globalOrdered,firstLinear,firstPoint,orderedLow]
  ring

theorem globalMixed_point (c : Cell) (ν : ℝ) (i j : ℕ) :
    globalMixed c ν (firstPoint i j) = mixedLowHigh c i j ν := by
  rw [mixedLowHigh_eq]
  simp [globalMixed,minMaxLinear,firstLinear,firstPoint,mixedPeriodic]
  ring

theorem globalPaired_point (c : Cell) (l r : ℝ) (i j : ℕ) :
    globalPaired c l r (firstPoint i j) = pairedGap c i j l r := by
  rw [pairedGap_eq]
  simp [globalPaired,minMaxLinear,firstLinear,firstPoint,pairedPeriodic]
  ring

theorem globalOrdered_weighted {ι : Type*} (k : Fin 15) (s : Finset ι)
    (i j : ι→ℕ) (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t)
    (hi : ∀t∈s,0 < i t) (hj : ∀t∈s,0 < j t) :
    globalOrdered (rawCells k) (firstWeighted s i j w) ≤ 0 := by
  unfold globalOrdered
  rw [firstLinear_weighted]
  apply Finset.sum_nonpos
  intro t ht
  have h := raw_ordered_all k (i t) (j t) (hi t ht) (hj t ht)
  rw [←globalOrdered_point] at h
  exact mul_nonpos_of_nonneg_of_nonpos (hw t ht) h

theorem globalMixed_weighted {ι : Type*} (k : Fin 15) {ν : ℝ}
    (hν : ν ∈ Set.Icc (rawCells k).q (3/4)) (s : Finset ι)
    (i j : ι→ℕ) (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t)
    (hi : ∀t∈s,0 < i t) (hj : ∀t∈s,0 < j t) :
    0 ≤ globalMixed (rawCells k) ν (firstWeighted s i j w) := by
  rcases raw_mixed_parameters k with ⟨hk,hell,hB,hstep,hq,hqhi⟩
  have hn : 0 ≤ ν := by linarith [hν.1]
  have hd : 0 ≤ d ν := by unfold d; linarith [hν.2]
  have hp := minMaxLinear_weighted s i j w hw
    (d ν*(1+omega*((rawCells k).q/(rawCells k).priorL))) (d ν+etaD ν)
    (d ν*(1-omega)*((rawCells k).q/K))
    (d ν*omega*((rawCells k).q/(rawCells k).priorL)*(rawCells k).priorB)
    (d ν-rr ν)
    ![0,0,-2*d ν,2*d ν*omega-d ν*omega*((rawCells k).q/(rawCells k).priorL)*(rawCells k).priorB+rr ν,
      -d ν*omega*(1-((rawCells k).q/(rawCells k).priorL)*(rawCells k).priorB),-rr ν,-d ν*omega,-d ν]
    (mul_nonneg (mul_nonneg hd (by norm_num [omega])) hk)
    (mul_nonneg (mul_nonneg (mul_nonneg hd (by norm_num [omega])) hell) hB)
    (by unfold rr; linarith)
  apply le_trans (b:=∑t∈s,w t*globalMixed (rawCells k) ν (firstPoint (i t) (j t))) ?_ hp
  apply Finset.sum_nonneg
  intro t ht
  rw [globalMixed_point]
  exact mul_nonneg (hw t ht) (raw_mixed_all k hν (i t) (j t) (hi t ht) (hj t ht))

theorem globalPaired_weighted {ι : Type*} (k : Fin 15) {l r : ℝ}
    (hl : l ∈ Set.Icc (rawCells k).q (3/4))
    (hr : r ∈ Set.Icc (rawCells k).q (3/4)) (s : Finset ι)
    (i j : ι→ℕ) (w : ι→ℝ) (hw : ∀t∈s,0 ≤ w t)
    (hi : ∀t∈s,0 < i t) (hj : ∀t∈s,0 < j t) :
    0 ≤ globalPaired (rawCells k) l r (firstWeighted s i j w) := by
  have hq := (raw_mixed_parameters k).2.2.2.2.1
  have hρl := rho_bounds (ν:=l) ⟨hq.trans hl.1,hl.2⟩
  have hρr := rho_bounds (ν:=r) ⟨hq.trans hr.1,hr.2⟩
  have hp := minMaxLinear_weighted s i j w hw
    (l+1-gamma (rawCells k)) (r+1-gamma (rawCells k)) 0 (1-rho l) (1-rho r)
    ![0,0,-2,1+rho l+rho r,-rho l,-rho r,-1,-1]
    le_rfl (by linarith) (by linarith)
  apply le_trans (b:=∑t∈s,w t*globalPaired (rawCells k) l r (firstPoint (i t) (j t))) ?_ hp
  apply Finset.sum_nonneg
  intro t ht
  rw [globalPaired_point]
  exact mul_nonneg (hw t ht) (raw_paired_all k hl hr (i t) (j t) (hi t ht) (hj t ht))

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.globalOrdered_weighted
#print axioms QRH.Record12518109Source.globalMixed_weighted
#print axioms QRH.Record12518109Source.globalPaired_weighted
