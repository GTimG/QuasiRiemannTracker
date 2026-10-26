import Candidate.Cycle63.Assembly.Geometry
import Candidate.Cycle63.Assembly.Count.ArithmeticIdentity
import Candidate.Cycle63.Numerator.Capacity.Schedule

/- Original module: Candidate.Cycle63.Numerator.Scalar.Exponent. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Physical exponent bookkeeping adapted from Cycle25/Numerator/Scalar;
weighted PR6 predecessor 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/
                                
                                                

noncomputable section
namespace Cycle63.Numerator.Scalar
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein

theorem coefficient_binding {kap p : ℝ} (hk : 7/10 ≤ kap) :
    OAI.SevenEighths.Cycle25DetectorRowCount.coefficient p kap =
      countingCoefficient kap p := (Physical.coefficient_eq_old hk).symm

theorem count_binding {kap delta p : ℝ} (hk : 7/10 ≤ kap) :
    OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap =
      countingR0 kap delta p := Assembly.Count.rowCount_eq hk

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

end Cycle63.Numerator.Scalar
end

/- Original module: Candidate.Cycle63.Numerator.Scalar.Schedule. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/

noncomputable section
namespace Cycle63.Numerator.Scalar
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein

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

end Cycle63.Numerator.Scalar
end

/- Original module: Candidate.Cycle63.Numerator.Scalar.Loss. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/

noncomputable section
namespace Cycle63.Numerator.Scalar
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein

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
      Assembly.signal beta-499/5000000000-(beta-theta)/2-height := by
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
      Assembly.signal beta-499/5000000000-(beta-theta)/2-height-
        d*Capacity.dampingRate*delta*(v+xi) := by
  have hh := new_supremum_deficit hbeta hupper hd hdelta hp
  have hi := scheduled_kernel_bound (kap:=2*beta-1) (e:=e) hd hdelta.1 hp hv hxi
  unfold Assembly.signal
  linarith only [hh,hi,hbudget,hbeta]

end Cycle63.Numerator.Scalar
end

/- Original module: Candidate.Cycle63.Numerator.Scalar.SourcePacket. -/
section
/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Finite physical slot bookkeeping adapted from Cycle25/Numerator/Scalar;
weighted PR6 predecessor 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/

noncomputable section
open scoped Classical BigOperators
namespace Cycle63.Numerator.Scalar
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein

theorem error_main_source_scale {K : ℕ} (J : Finset (Fin K))
    (Y : Fin K→ℝ) (r : ℝ) :
    (∏j:J,(Y j.val)^r)*(∏j:{i:Fin K//i∉J},(Y j.val)^r)=∏j,(Y j)^r := by
  convert Fintype.prod_subtype_mul_prod_subtype (fun j=>j∈J) (fun j=>(Y j)^r) using 1
  congr 1
  apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl

theorem error_main_source_power {K : ℕ} (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0 < Z) (lengths : Fin K→ℝ) :
    (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) =
      Z^(-(4/25:ℝ)*(∑j,lengths j)) := by
  have hm : (∏j:{i:Fin K//i∉J},(Z^(lengths j.val))^(-(4/25:ℝ))) =
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) := by
    simp_rw [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _=>mul_comm _ _)
  have hp := error_main_source_scale J (fun j=>Z^(lengths j)) (-(4/25:ℝ))
  rw [hm] at hp
  rw [hp]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul]
  congr 1
  ring

/-- Error and main slots partition the original source widths. The selected
capacity C is in Z units; neither the row endpoint nor kappa is specialized. -/
theorem source_packet_multiplicative_identity {K : ℕ} (J : Finset (Fin K))
    (lengths : Fin K→ℝ) (hlengths : ∑j,lengths j=ell)
    (Z kap d C delta q A : ℝ) (L : LossData)
    (hZ : 0 < Z) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    ((Z^d)^L.scalar*(Z^d)^(-(17/50:ℝ))*Z^L.frequency*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)))*
    (A*Z^L.front*((Z^d)^(y/d))^(-(1/2:ℝ))*
      (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      (Z^d)^(L.mass+q*(ell/d)-q*(C/d)/2+
        (3*(countingR kap delta (q/delta)+L.count)+1+L.moment)/4+
        L.selection/2+delta*L.mesh/4+L.slack*(ell/d))) =
    A*Z^(numeratorExponent kap d C delta (q/delta)+weightedSourceLoss d delta L) := by
  have hsplit := error_main_source_power J Z hZ lengths
  rw [hlengths] at hsplit
  let E := L.mass+q*(ell/d)-q*(C/d)/2+
    (3*(countingR kap delta (q/delta)+L.count)+1+L.moment)/4+
    L.selection/2+delta*L.mesh/4+L.slack*(ell/d)
  calc
    _ = A*((Z^d)^L.scalar*(Z^d)^(-(17/50:ℝ))*Z^L.frequency*
        Z^(-(4/25:ℝ)*ell)*Z^L.front*((Z^d)^(y/d))^(-(1/2:ℝ))*(Z^d)^E) := by
      rw [←hsplit]
      dsimp only [E]
      ring
    _ = A*Z^(d*L.scalar+d*(-(17/50:ℝ))+L.frequency+(-(4/25))*ell+
        L.front+(d*(y/d))*(-(1/2:ℝ))+d*E) := by
      simp_rw [←Real.rpow_mul hZ.le]
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
        ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by
      congr 2
      rw [←source_packet_exponent kap d C delta q L hd hdelta]
      dsimp only [E]
      field_simp
      ring

theorem source_kernel_multiplicative_identity (Z kap d C delta p e A : ℝ)
    (L : LossData) (hZ : 0 < Z) :
    A*Z^(numeratorExponent kap d C delta p+weightedSourceLoss d delta L)*
      (Z^x)^(1/2-17/50:ℝ)*Z^((1+delta)/2+16*e+17/50-1) =
    A*Z^(rowExponentAt kap d C delta p+Assembly.signalShift+16*e+weightedSourceLoss d delta L) := by
  rw [←Real.rpow_mul hZ.le,mul_assoc,←Real.rpow_add hZ,mul_assoc,←Real.rpow_add hZ]
  congr 2
  have hi := numerator_kernel_exponent kap d C delta p e
  unfold kernelExponent at hi
  linarith only [hi]

end Cycle63.Numerator.Scalar
end
