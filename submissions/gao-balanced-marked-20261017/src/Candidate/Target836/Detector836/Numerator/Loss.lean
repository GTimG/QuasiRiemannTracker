/- Private .874836 scalar specialization. Adapted from accepted Hailey Collet,
OpenAI, weighted PR6 and Cycle63 sources; Apache-2.0. -/
import Candidate.Target836.Detector836.Numerator.Schedule
noncomputable section
namespace Target836.Numerator.Scalar
open Target836.Arithmetic Target836.EndpointArithmetic

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
        (3*(Detector836.count kap delta (q/delta)+L.count)+1+L.moment)/4+
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
  have hh := new_supremum_deficit hbeta hd hdelta hp
  have hi := numerator_kernel_exponent (2*beta-1) d (newCapacity d) delta p e
  unfold newExponentAt at hh
  unfold Assembly.signal
  norm_num [reserve] at hh
  linarith only [hh,hi,hbudget,hbeta]

theorem old_packet_certificate {beta d delta p e height : ℝ} (L : LossData)
    (hbeta : theta < beta) (hupper : beta ≤ 7/8)
    (hd : d ∈ Set.Icc d0 dMinus) (hdelta : delta ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2))
    (hbudget : 16*e+weightedSourceLoss d delta L+height ≤ (beta-theta)/4) :
    numeratorExponent (2*beta-1) d (oldCapacityAt (2*beta-1) d) delta p+
      kernelExponent ((1+delta)/2) e+weightedSourceLoss d delta L <
      Assembly.signal beta-499/5000000000-(beta-theta)/2-height := by
  have hh := old_supremum_deficit hbeta hd hdelta hp
  have hi := numerator_kernel_exponent (2*beta-1) d (oldCapacityAt (2*beta-1) d) delta p e
  unfold oldExponentAt at hh
  unfold Assembly.signal
  norm_num [reserve] at hh
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
  have hh := new_supremum_deficit hbeta hd hdelta hp
  have hi := scheduled_kernel_bound (kap:=2*beta-1) (e:=e) hd hdelta.1 hp hv hxi
  unfold Assembly.signal
  norm_num [reserve] at hh
  linarith only [hh,hi,hbudget,hbeta]

end Target836.Numerator.Scalar

#print axioms Target836.Numerator.Scalar.new_packet_certificate
#print axioms Target836.Numerator.Scalar.old_packet_certificate
#print axioms Target836.Numerator.Scalar.scheduled_packet_certificate
