/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B001
import Candidate.Bundles.B022
import Candidate.Bundles.B060

/- BEGIN ORIGINAL Cycle61.Assembly.Count.ArithmeticIdentity; sha256 f2d1c9921d8e0a55f9dd9cee34af4f8a1facd47a865129d5582e51522a381b90 -/
section
                                       
                                      

namespace Cycle61.Assembly.Count
noncomputable section
open Arithmetic.Bernstein
open OAI.SevenEighths.Cycle25DetectorRowCount

theorem cutoff_eq {κ delta p : ℝ} (hk : 7/10≤κ) :
    cutoff delta p κ = Physical.witnessCutoff κ delta p := by
  simp only [cutoff, Physical.witnessCutoff, V, rowDen, Physical.coefficient_eq_old hk]

theorem rowCount_eq {κ delta p : ℝ} (hk : 7/10≤κ) :
    rowCount delta p κ = countingR κ delta p := by
  simp only [rowCount, countingR, V, rowDen, Physical.coefficient_eq_old hk]
end
end Cycle61.Assembly.Count

end
/- END ORIGINAL Cycle61.Assembly.Count.ArithmeticIdentity -/

/- BEGIN ORIGINAL Cycle61.Numerator.Scalar.Exponent; sha256 5fd81ad38931e609dbfa3b53252e61dbc0264df7bee8f3e0ea55d9781d7a37c7 -/
section
/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Physical exponent bookkeeping adapted from Cycle25/Numerator/Scalar;
weighted PR6 predecessor 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/
                                
                                                

noncomputable section
namespace Cycle61.Numerator.Scalar
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein

theorem coefficient_binding {kap p : ℝ} (hk : 7/10 ≤ kap) :
    OAI.SevenEighths.Cycle25DetectorRowCount.coefficient p kap =
      countingCoefficient kap p := (Physical.coefficient_eq_old hk).symm

theorem count_binding {kap delta p : ℝ} (hk : 7/10 ≤ kap) :
    OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap =
      countingR kap delta p := Assembly.Count.rowCount_eq hk

/-- C is total selected capacity in Z units, not capacity relative to U=Z^d. -/
def numeratorExponent (kap d C delta p : ℝ) : ℝ :=
  -y/2+ell*(17/50-1/2)+ell*delta*p+
    d*((3*countingR kap delta p+1)/4-17/50)-delta*p*C/2

def kernelExponent (a e : ℝ) : ℝ :=
  x*(1/2-17/50)+a+16*e+17/50-1

/-- Literal physical weights, frequency damping and the two external Mellin
scales give the variable-kappa row expression at the supplied capacity. -/
theorem numerator_kernel_exponent (kap d C delta p e : ℝ) :
    numeratorExponent kap d C delta p+kernelExponent ((1+delta)/2) e =
      rowExponentAt kap d C delta p+Assembly.signalShift+16*e := by
  unfold numeratorExponent kernelExponent rowExponentAt Assembly.signalShift
  rw [x_eq,y_eq]
  ring

theorem numerator_packet_exponent (kap d C delta q scalar mass count moment selection mesh slack : ℝ)
    (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    -y/2-(4/25)*ell+slack*ell+
      d*(scalar+mass+q*(ell/d)-q*(C/d)/2+
        (3*(countingR kap delta (q/delta)+count)+1+moment)/4+
        selection/2+delta*mesh/4-17/50) =
      numeratorExponent kap d C delta (q/delta)+slack*ell+
        d*(scalar+mass+(3*count+moment)/4+selection/2+delta*mesh/4) := by
  unfold numeratorExponent
  have hq : delta*(q/delta)=q := by field_simp
  rw [hq]
  field_simp
  ring

end Cycle61.Numerator.Scalar

end
/- END ORIGINAL Cycle61.Numerator.Scalar.Exponent -/

/- BEGIN ORIGINAL Cycle61.Numerator.Scalar.Schedule; sha256 e088c2dde23b969485001222b3b2a5d29c0c438482e8556ba4a230e1394b723c -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                        
                                          

noncomputable section
namespace Cycle61.Numerator.Scalar
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein

theorem zeroCapacity_binding {d : ℝ} (hd : d ≠ 0) :
    d*Capacity.zeroCapacity d = newCapacity d := Capacity.scaled_zeroCapacity hd

def scheduledBinExponent (kap d delta p v xi : ℝ) : ℝ :=
  numeratorExponent kap d (d*Capacity.scheduledCapacity d (v+xi)) delta p-
    d*delta*v/4

/-- Both the affine small-shift schedule and the clipped large-shift schedule
pay the loss from the zero-shift capacity, including an explicit damping gain. -/
theorem scheduled_bin_damping {kap d delta p v xi : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hdelta : 0 ≤ delta)
    (hp : 0 ≤ p ∧ p ≤ 1/2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) :
    scheduledBinExponent kap d delta p v xi ≤
      numeratorExponent kap d (newCapacity d) delta p+d*delta*xi/4-
        d*Capacity.dampingRate*delta*(v+xi) := by
  have hdpos := Physical.physical_d_pos hd.1
  have hq : 0 ≤ delta*p := mul_nonneg hdelta hp.1
  have hq1 : delta*p ≤ delta/2 := by nlinarith [mul_le_mul_of_nonneg_left hp.2 hdelta]
  have hh := Capacity.scheduled_capacity_damping hd (add_nonneg hv hxi) hq hq1 hdelta
  have hm := mul_le_mul_of_nonneg_left hh hdpos.le
  rw [←zeroCapacity_binding hdpos.ne']
  unfold scheduledBinExponent numeratorExponent
  nlinarith only [hm]

theorem scheduled_small_capacity {d v : ℝ} (hv : v ≤ 2*t0) :
    Capacity.scheduledCapacity d v = Physical.affineCapacity d (v/2) := by
  simp only [Capacity.scheduledCapacity,ite_eq_left hv]

theorem scheduled_large_capacity {d v : ℝ} (hv : 2*t0 < v) :
    Capacity.scheduledCapacity d v = Physical.oldCapacity (Physical.shiftBase d) (v/2) := by
  simp only [Capacity.scheduledCapacity,ite_eq_right (not_le.mpr hv)]

theorem scheduled_clipped_capacity {d v : ℝ} (hv : 2*t0 < v)
    (hclip : Physical.shiftBase d ≤ v) : Capacity.scheduledCapacity d v = 0 := by
  rw [scheduled_large_capacity hv]
  exact Physical.oldCapacity_zero (by linarith)

theorem scheduled_kernel_bound {kap d delta p v xi e : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hdelta : 0 ≤ delta)
    (hp : 0 ≤ p ∧ p ≤ 1/2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) :
    scheduledBinExponent kap d delta p v xi+kernelExponent ((1+delta)/2) e ≤
      newExponentAt kap d delta p+Assembly.signalShift+16*e+d*delta*xi/4-
        d*Capacity.dampingRate*delta*(v+xi) := by
  have hh := scheduled_bin_damping (kap:=kap) hd hdelta hp hv hxi
  have hi := numerator_kernel_exponent kap d (newCapacity d) delta p e
  unfold newExponentAt
  linarith only [hh,hi]

end Cycle61.Numerator.Scalar

end
/- END ORIGINAL Cycle61.Numerator.Scalar.Schedule -/

/- BEGIN ORIGINAL Cycle61.Numerator.Scalar.Loss; sha256 7977286b9c97407859e37ffee0a438192afa95098361cd7eb27065ee92af22d7 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                        

noncomputable section
namespace Cycle61.Numerator.Scalar
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein

/-- Fixed scalar costs from the literal physical reconstruction. All entries
are exponents, with count, mass, selection and mesh measured relative to U. -/
structure LossData where
  front : ℝ
  frequency : ℝ
  scalar : ℝ
  mass : ℝ
  count : ℝ
  moment : ℝ
  selection : ℝ
  mesh : ℝ
  slack : ℝ

def weightedSourceLoss (d delta : ℝ) (L : LossData) : ℝ :=
  L.front+L.frequency+L.slack*ell+
    d*(L.scalar+L.mass+(3*L.count+L.moment)/4+L.selection/2+delta*L.mesh/4)

def uniformSourceLoss (L : LossData) : ℝ :=
  L.front+L.frequency+L.slack*ell+
    L.scalar+L.mass+(3*L.count+L.moment)/4+L.selection/2+3*L.mesh/16

theorem weightedSourceLoss_le_uniform {d delta : ℝ} (L : LossData)
    (hd : d ≤ 1) (hdelta : 0 ≤ delta ∧ delta ≤ 3/4)
    (hscalar : 0 ≤ L.scalar) (hmass : 0 ≤ L.mass) (hcount : 0 ≤ L.count)
    (hmoment : 0 ≤ L.moment) (hselection : 0 ≤ L.selection) (hmesh : 0 ≤ L.mesh) :
    weightedSourceLoss d delta L ≤ uniformSourceLoss L := by
  have hi : 0 ≤ L.scalar+L.mass+(3*L.count+L.moment)/4+
      L.selection/2+delta*L.mesh/4 := by have := hdelta.1; positivity
  have hm := mul_le_mul_of_nonneg_right hd hi
  have hx := mul_le_mul_of_nonneg_right hdelta.2 hmesh
  unfold weightedSourceLoss uniformSourceLoss
  linarith only [hm,hx]

theorem source_packet_exponent (kap d C delta q : ℝ) (L : LossData)
    (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    L.front+L.frequency-y/2-(4/25)*ell+L.slack*ell+
      d*(L.scalar+L.mass+q*(ell/d)-q*(C/d)/2+
        (3*(countingR kap delta (q/delta)+L.count)+1+L.moment)/4+
        L.selection/2+delta*L.mesh/4-17/50) =
      numeratorExponent kap d C delta (q/delta)+weightedSourceLoss d delta L := by
  have hh := numerator_packet_exponent kap d C delta q L.scalar L.mass
    L.count L.moment L.selection L.mesh L.slack hd hdelta
  unfold weightedSourceLoss
  linarith only [hh]

/-- A budget on finite scalar costs closes the actual-supremum new rows.
No numerator estimate is a premise of this arithmetic certificate. -/
theorem new_packet_certificate {beta d delta p e height : ℝ} (L : LossData)
    (hbeta : theta < beta) (hupper : beta ≤ 7/8)
    (hd : d ∈ Set.Icc dMinus dPlus) (hdelta : delta ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2))
    (hbudget : 16*e+weightedSourceLoss d delta L+height ≤ (beta-theta)/4) :
    numeratorExponent (2*beta-1) d (newCapacity d) delta p+
      kernelExponent ((1+delta)/2) e+weightedSourceLoss d delta L <
      Assembly.signal beta-4999/5000000000-(beta-theta)/2-height := by
  have hh := new_supremum_deficit hbeta hupper hd hdelta hp
  have hi := numerator_kernel_exponent (2*beta-1) d (newCapacity d) delta p e
  unfold newExponentAt at hh
  unfold Assembly.signal
  linarith only [hh,hi,hbudget,hbeta]

theorem old_packet_certificate {beta d delta p e height : ℝ} (L : LossData)
    (hbeta : theta < beta) (hupper : beta ≤ 7/8)
    (hd : d ∈ Set.Icc d0 dMinus) (hdelta : delta ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2))
    (hbudget : 16*e+weightedSourceLoss d delta L+height ≤ (beta-theta)/4) :
    numeratorExponent (2*beta-1) d (oldCapacityAt (2*beta-1) d) delta p+
      kernelExponent ((1+delta)/2) e+weightedSourceLoss d delta L <
      Assembly.signal beta-1/100000-(beta-theta)/2-height := by
  have hh := old_supremum_deficit hbeta hupper hd hdelta hp
  have hi := numerator_kernel_exponent (2*beta-1) d (oldCapacityAt (2*beta-1) d) delta p e
  unfold oldExponentAt at hh
  unfold Assembly.signal
  linarith only [hh,hi,hbudget]

theorem scheduled_packet_certificate {beta d delta p v xi e loss height : ℝ}
    (hbeta : theta < beta) (hupper : beta ≤ 7/8)
    (hd : d ∈ Set.Icc dMinus dPlus) (hdelta : delta ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) (hv : 0 ≤ v) (hxi : 0 ≤ xi)
    (hbudget : 16*e+loss+d*delta*xi/4+height ≤ (beta-theta)/4) :
    scheduledBinExponent (2*beta-1) d delta p v xi+
      kernelExponent ((1+delta)/2) e+loss <
      Assembly.signal beta-4999/5000000000-(beta-theta)/2-height-
        d*Capacity.dampingRate*delta*(v+xi) := by
  have hh := new_supremum_deficit hbeta hupper hd hdelta hp
  have hi := scheduled_kernel_bound (kap:=2*beta-1) (e:=e) hd hdelta.1 hp hv hxi
  unfold Assembly.signal
  linarith only [hh,hi,hbudget,hbeta]

end Cycle61.Numerator.Scalar

end
/- END ORIGINAL Cycle61.Numerator.Scalar.Loss -/
