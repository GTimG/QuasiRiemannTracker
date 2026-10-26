/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Literal Target830 physical exponents and complete source-loss ledger.
Adapted from accepted Hailey Collet/OpenAI/Cycle25 sources. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.GenericFeedback

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped BigOperators
namespace QRH.LewkoStage1Return.GenericPhysical.Scalar
open QRH.LewkoStage1Return GenericArithmetic
variable [Geometry.Parameters] [Geometry.Bounds] [CountScheme] [PhysicalSchedule]

/-- C is total selected capacity in Z units, not capacity relative to U=Z^d. -/
def numeratorExponent (bs : List Branch) (kap d C delta p : ℝ) : ℝ :=
  -y/2+ell*(17/50-1/2)+ell*delta*p+
    d*((3*envelope bs kap delta p+1)/4-17/50)-delta*p*C/2

def kernelExponent (a e : ℝ) : ℝ :=
  x*(1/2-17/50)+a+16*e+17/50-1

/-- Literal physical weights, frequency damping and the two external Mellin
scales give the variable-kappa row expression at the supplied capacity. -/
theorem numerator_kernel_exponent (bs : List Branch) (kap d C delta p e : ℝ) :
    numeratorExponent bs kap d C delta p+kernelExponent ((1+delta)/2) e =
      rowAt bs kap d C delta p+Assembly.signalShift+16*e := by
  unfold numeratorExponent kernelExponent rowAt Ebase Assembly.signalShift
  dsimp [Assembly.signalShift, LewkoStage1Return.Transport.Assembly.signalShift, h, Geometry.h]
  ring

theorem numerator_packet_exponent (bs : List Branch) (kap d C delta q scalar mass count moment selection mesh slack : ℝ)
    (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    -y/2-(4/25)*ell+slack*ell+
      d*(scalar+mass+q*(ell/d)-q*(C/d)/2+
        (3*(envelope bs kap delta (q/delta)+count)+1+moment)/4+
        selection/2+delta*mesh/4-17/50) =
      numeratorExponent bs kap d C delta (q/delta)+slack*ell+
        d*(scalar+mass+(3*count+moment)/4+selection/2+delta*mesh/4) := by
  unfold numeratorExponent
  have hq : delta*(q/delta)=q := by field_simp
  rw [hq]
  field_simp
  ring

end QRH.LewkoStage1Return.GenericPhysical.Scalar



namespace QRH.LewkoStage1Return.GenericPhysical.Scalar
noncomputable section
open QRH.LewkoStage1Return GenericArithmetic
variable [Geometry.Parameters] [Geometry.Bounds] [CountScheme] [PhysicalSchedule]
def sourceReserve : ℝ := rowFee/2

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

theorem source_packet_exponent (bs : List Branch) (kap d C delta q : ℝ) (L : LossData)
    (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    L.front+L.frequency-y/2-(4/25)*ell+L.slack*ell+
      d*(L.scalar+L.mass+q*(ell/d)-q*(C/d)/2+
        (3*(envelope bs kap delta (q/delta)+L.count)+1+L.moment)/4+
        L.selection/2+delta*L.mesh/4-17/50) =
      numeratorExponent bs kap d C delta (q/delta)+weightedSourceLoss d delta L := by
  have hh := numerator_packet_exponent bs kap d C delta q L.scalar L.mass
    L.count L.moment L.selection L.mesh L.slack hd hdelta
  unfold weightedSourceLoss
  linarith only [hh]

/-- A budget on finite scalar costs closes the actual-supremum new rows.
No numerator estimate is a premise of this arithmetic certificate. -/
theorem new_packet_certificate (bs : List Branch) {beta d delta p e height : ℝ} (L : LossData)
    (hbeta : theta < beta) (hupper : beta ≤ 7/8)
    (hd : d ∈ Set.Icc dm dp) (hdelta : delta ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2))
    (hbase : newExponent bs d delta p ≤ theta-rowFee)
    (hbudget : 16*e+weightedSourceLoss d delta L+height ≤ (beta-theta)/4) :
    numeratorExponent bs (2*beta-1) d (newCapacity d) delta p+
      kernelExponent ((1+delta)/2) e+weightedSourceLoss d delta L <
      Assembly.signal beta-sourceReserve-(beta-theta)/2-height := by
  have hh := new_supremum_deficit bs hbeta hd hdelta hp hbase
  have hi := numerator_kernel_exponent bs (2*beta-1) d (newCapacity d) delta p e
  unfold newExponentAt at hh
  change _ < beta+Assembly.signalShift-sourceReserve-(beta-theta)/2-height
  have hfee : 0 < rowFee := by norm_num [rowFee]
  unfold sourceReserve
  linarith only [hh,hi,hbudget,hbeta,hfee]

theorem old_packet_certificate (bs : List Branch) {beta d delta p e height : ℝ} (L : LossData)
    (hbeta : theta < beta) (hupper : beta ≤ 7/8)
    (hd : d ∈ Set.Icc d0 dm) (hdelta : delta ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2))
    (hbase : oldExponent bs d delta p ≤ theta-rowFee)
    (hbudget : 16*e+weightedSourceLoss d delta L+height ≤ (beta-theta)/4) :
    numeratorExponent bs (2*beta-1) d (oldCapacityAt (2*beta-1) d) delta p+
      kernelExponent ((1+delta)/2) e+weightedSourceLoss d delta L <
      Assembly.signal beta-sourceReserve-(beta-theta)/2-height := by
  have hh := old_supremum_deficit bs hbeta hd hdelta hp hbase
  have hi := numerator_kernel_exponent bs (2*beta-1) d (oldCapacityAt (2*beta-1) d) delta p e
  unfold oldExponentAt at hh
  change _ < beta+Assembly.signalShift-sourceReserve-(beta-theta)/2-height
  have hfee : 0 < rowFee := by norm_num [rowFee]
  unfold sourceReserve
  linarith only [hh,hi,hbudget,hfee]

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
theorem source_packet_multiplicative_identity (bs : List Branch) {K : ℕ} (J : Finset (Fin K))
    (lengths : Fin K→ℝ) (hlengths : ∑j,lengths j=ell)
    (Z kap d C delta q A : ℝ) (L : LossData)
    (hZ : 0 < Z) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    ((Z^d)^L.scalar*(Z^d)^(-(17/50:ℝ))*Z^L.frequency*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)))*
    (A*Z^L.front*((Z^d)^(y/d))^(-(1/2:ℝ))*
      (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      (Z^d)^(L.mass+q*(ell/d)-q*(C/d)/2+
        (3*(envelope bs kap delta (q/delta)+L.count)+1+L.moment)/4+
        L.selection/2+delta*L.mesh/4+L.slack*(ell/d))) =
    A*Z^(numeratorExponent bs kap d C delta (q/delta)+weightedSourceLoss d delta L) := by
  have hsplit := error_main_source_power J Z hZ lengths
  rw [hlengths] at hsplit
  let E := L.mass+q*(ell/d)-q*(C/d)/2+
    (3*(envelope bs kap delta (q/delta)+L.count)+1+L.moment)/4+
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
      rw [←source_packet_exponent bs kap d C delta q L hd hdelta]
      dsimp only [E]
      field_simp
      ring

theorem source_kernel_multiplicative_identity (bs : List Branch) (Z kap d C delta p e A : ℝ)
    (L : LossData) (hZ : 0 < Z) :
    A*Z^(numeratorExponent bs kap d C delta p+weightedSourceLoss d delta L)*
      (Z^x)^(1/2-17/50:ℝ)*Z^((1+delta)/2+16*e+17/50-1) =
    A*Z^(rowAt bs kap d C delta p+Assembly.signalShift+16*e+weightedSourceLoss d delta L) := by
  rw [←Real.rpow_mul hZ.le,mul_assoc,←Real.rpow_add hZ,mul_assoc,←Real.rpow_add hZ]
  congr 2
  have hi := numerator_kernel_exponent bs kap d C delta p e
  unfold kernelExponent at hi
  linarith only [hi]


end
end QRH.LewkoStage1Return.GenericPhysical.Scalar

#print axioms QRH.LewkoStage1Return.GenericPhysical.Scalar.new_packet_certificate
#print axioms QRH.LewkoStage1Return.GenericPhysical.Scalar.old_packet_certificate
#print axioms QRH.LewkoStage1Return.GenericPhysical.Scalar.source_packet_multiplicative_identity
