/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The admitted exact count pays the complete limiting conductor range.
Interpolation retains the minimum of both capacity branches. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactReturnEdges
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.ConductorInterpolation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open Set IntervalPolynomial
open Qrh.TwoSlot.AnchorZeroLoss (min_capacity_interval)

def y : ℝ := stationaryCutoff-2*ell
def oldCapacity (D : ℝ) : ℝ := min D (2*y-D)/(6*kappa)
def newCapacity (D : ℝ) : ℝ := min ((3/40)*D) ((2*y-D)/2)
def common (d p : ℝ) : ℝ := 1/2+13*stationaryCutoff/75-y/2-ell/2+d/2+d*p*ell
def slope (d p : ℝ) : ℝ := -9/100+(3/4)*envelope d p

theorem edge_values (e : Fin 4) :
    (edgeD e).value = (![1/200,19/25,19/25,stationaryCutoff] : Fin 4 → ℝ) e ∧
    (edgeC e).value = (![1/200/(6*kappa),(2*y-19/25)/(6*kappa),
      (3/40)*(19/25),(stationaryCutoff-4*ell)/2] : Fin 4 → ℝ) e := by
  fin_cases e <;>
    dsimp [edgeD,edgeC,R,Coeff.rat,Coeff.div,Coeff.add,Coeff.sub,Coeff.neg,Coeff.mul,
      k6,kappaC,thetaC,hC,ellC,yC,kappa,y] <;>
    norm_num only [Rat.cast_ofNat,Rat.cast_div,Rat.cast_one]
  all_goals simp only [sub_eq_add_neg,true_and,and_self]

theorem y_bounds : (2343/5000:ℝ) < y ∧ y < 4689/10000 := by
  have hh := stationaryCutoff_tight
  have he := ell_bounds
  unfold y
  constructor <;> linarith [hh.1,hh.2,he.1,he.2]

theorem old_cap_left : oldCapacity (1/200) = 1/200/(6*kappa) := by
  have hy := y_bounds.1
  unfold oldCapacity
  rw [min_eq_left (by linarith : (1/200:ℝ) ≤ 2*y-1/200)]

theorem old_cap_right : oldCapacity (19/25) = (2*y-19/25)/(6*kappa) := by
  have hy := y_bounds.2
  unfold oldCapacity
  rw [min_eq_right (by linarith : 2*y-19/25 ≤ (19/25:ℝ))]

theorem new_cap_left : newCapacity (19/25) = (3/40)*(19/25) := by
  have hy := y_bounds.1
  unfold newCapacity
  rw [min_eq_left (by linarith : (3/40:ℝ)*(19/25) ≤ (2*y-19/25)/2)]

theorem new_cap_right : newCapacity stationaryCutoff = (stationaryCutoff-4*ell)/2 := by
  have hc := critical_capacity_active.2
  unfold newCapacity y
  have he : (2*(stationaryCutoff-2*ell)-stationaryCutoff)/2 = (stationaryCutoff-4*ell)/2 := by ring
  rw [he,min_eq_right hc.le]

theorem row_antitone_capacity {d p : ℝ} (hd : 0 ≤ d) (hp : 0 ≤ p)
    (D a b : ℝ) (hab : a ≤ b) : row D b d p ≤ row D a d p := by
  have hh := mul_nonneg (mul_nonneg hd hp) (sub_nonneg.mpr hab)
  unfold row price
  nlinarith only [hh]

theorem old_rows {D d p : ℝ} (hcon : D ∈ Icc (1/200:ℝ) (19/25))
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    row D (oldCapacity D) d p ≤ theta := by
  have hden : 0 ≤ 6*kappa := by linarith [kappa_bounds.1]
  have hm (x : ℝ) : min (x/(6*kappa)) ((2*y-x)/(6*kappa)) = oldCapacity x :=
    min_div_div_right hden _ _
  rw [←hm D]
  apply min_capacity_interval (fun x c => row x c d p)
    (fun x => x/(6*kappa)) (fun x => (2*y-x)/(6*kappa)) hcon
    (row_antitone_capacity hd.1 hp.1)
  · refine ⟨common d p,slope d p-d*p/(12*kappa),?_⟩
    intro x
    unfold row price common slope y
    ring
  · refine ⟨common d p-d*p*y/(6*kappa),slope d p+d*p/(12*kappa),?_⟩
    intro x
    unfold row price common slope y
    ring
  · rw [hm]
    have hh := edge_bound 0 hd hp
    rw [(edge_values 0).1,(edge_values 0).2] at hh
    simpa only [Matrix.cons_val_zero,old_cap_left] using hh
  · rw [hm]
    have hh := edge_bound 1 hd hp
    rw [(edge_values 1).1,(edge_values 1).2] at hh
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,old_cap_right] using hh

theorem new_rows {D d p : ℝ} (hcon : D ∈ Icc (19/25:ℝ) stationaryCutoff)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    row D (newCapacity D) d p ≤ theta := by
  unfold newCapacity
  apply min_capacity_interval (fun x c => row x c d p)
    (fun x => (3/40)*x) (fun x => (2*y-x)/2) hcon
    (row_antitone_capacity hd.1 hp.1)
  · refine ⟨common d p,slope d p-d*p*(3/40)/2,?_⟩
    intro x
    unfold row price common slope y
    ring
  · refine ⟨common d p-d*p*y/2,slope d p+d*p/4,?_⟩
    intro x
    unfold row price common slope y
    ring
  · have hh := edge_bound 2 hd hp
    rw [(edge_values 2).1,(edge_values 2).2] at hh
    change row (19/25) (newCapacity (19/25)) d p ≤ theta
    rw [new_cap_left]
    simpa using hh
  · have hh := edge_bound 3 hd hp
    rw [(edge_values 3).1,(edge_values 3).2] at hh
    change row stationaryCutoff (newCapacity stationaryCutoff) d p ≤ theta
    rw [new_cap_right]
    simpa using hh

theorem complete_limiting_return {D d p : ℝ}
    (hcon : D ∈ Icc (1/200:ℝ) stationaryCutoff)
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    row D (if D ≤ 19/25 then oldCapacity D else newCapacity D) d p ≤ theta := by
  by_cases hD : D ≤ 19/25
  · rw [if_pos hD]
    exact old_rows ⟨hcon.1,hD⟩ hd hp
  · rw [if_neg hD]
    exact new_rows ⟨le_of_not_ge hD,hcon.2⟩ hd hp

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.old_rows
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.new_rows
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.complete_limiting_return
