/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.CorrectedJointBudget
import Candidate.Research.RecursiveAffine.Geometry.CorrectedCertificate1
import Candidate.Research.RecursiveAffine.Geometry.CorrectedCertificate2
import Candidate.Research.RecursiveAffine.Geometry.CorrectedCertificate3
import Candidate.Research.RecursiveAffine.Geometry.CorrectedCertificate4

set_option autoImplicit false
set_option maxHeartbeats 0
namespace Cycle153
noncomputable section
open OAI.SevenEighths.Cycle153Geometry Cycle63.Optimization

/-- Finite negative coordinate error is charged in the all-bin extension. -/
theorem commonLoss_bounds {q : ℝ} (hq0 : 3/5≤q) (hq : q≤3/4) :
    0≤commonLoss q ∧ commonLoss q≤1 := by
  constructor
  · exact le_trans (by norm_num) (le_max_left _ _)
  · have hh:=commonLoss_antitone hq0 hq
    have hbase : commonLoss (3/5)≤1 := by
      norm_num [commonLoss,Cycle63.Optimization.density]
    exact hh.trans hbase

/-- A junction certificate and its paid derivative cover every later HIGH
bin. The reduction may be negative by 10^-12; this error is not discarded. -/
theorem corrected_all_bins_with_finite_error
    {q0 q W L a C V Red : ℝ} (hq0 : 3/5≤q0) (hq : q0≤q) (hqhi : q≤3/4)
    (hW : 0≤W) (hV : 0≤V) (hRed : -(1/1000000000000:ℝ)≤Red)
    (hgrowth : 0≤((50/3)/(5-2*q0)^2)*W-L)
    (hjunction : (124899651/1000000000000000:ℝ)<
      correctedJointBudget q0 W L a C V Red) :
    (1/10000000:ℝ)<correctedJointBudget q W L a C V Red := by
  have hb:=correctedJointBudget_all_bins (ampl:=a) (previousPayment:=C)
    (eta:=0) hq hqhi hW hV hRed hgrowth
  have h0:=commonLoss_bounds hq0 (hq.trans hqhi)
  have h1:=commonLoss_bounds (hq0.trans hq) hqhi
  have he : (1/1000000000000:ℝ)*(commonLoss q0-commonLoss q)≤1/1000000000000 := by
    linarith only [h0.2,h1.1]
  linarith only [hb,hjunction,he]

/-- The actual path retains a finite negative missing-coordinate error as
well as the reduction error. Both differences of terminal-bin coefficients
are charged against the same strict junction reserve. -/
theorem corrected_all_bins_with_robust_missing
    {q0 q W L a C V Red : ℝ} (hq0 : 3/5≤q0) (hq : q0≤q) (hqhi : q≤3/4)
    (hW : 0≤W) (hV : -(1/1000000000000:ℝ)≤V)
    (hRed : -(1/1000000000000:ℝ)≤Red)
    (hgrowth : 0≤((50/3)/(5-2*q0)^2)*W-L)
    (hjunction : (124899651/1000000000000000:ℝ)<
      correctedJointBudget q0 W L a C V Red) :
    (1/10000000:ℝ)<correctedJointBudget q W L a C V Red := by
  let e : ℝ:=1/1000000000000
  have hVp : 0≤V+e := by dsimp only [e];linarith only [hV]
  have hb:=correctedJointBudget_all_bins (ampl:=a) (previousPayment:=C)
    (eta:=0) hq hqhi hW hVp hRed hgrowth
  have h0:=commonLoss_bounds hq0 (hq.trans hqhi)
  have h1:=commonLoss_bounds (hq0.trans hq) hqhi
  have hr0:=density_antitone hq0 (hq.trans hqhi)
  have hr1:=density_antitone hqhi (by norm_num : (3/4:ℝ)≤3/4)
  have hrho : density q0-density q≤1 := by
    rw [show density (3/5)=9/19 by norm_num [density]] at hr0
    rw [show density (3/4)=2/7 by norm_num [density]] at hr1
    linarith only [hr0,hr1]
  have hd : ((1-density q)-commonLoss q)-((1-density q0)-commonLoss q0)≤2 := by
    linarith only [hrho,h0.2,h1.1]
  have heV : e*(((1-density q)-commonLoss q)-((1-density q0)-commonLoss q0))≤e*2 :=
    mul_le_mul_of_nonneg_left hd (by norm_num [e] : 0≤e)
  have heR : e*(commonLoss q0-commonLoss q)≤e := by
    have he:=mul_le_mul_of_nonneg_left (show commonLoss q0-commonLoss q≤1 by
      linarith only [h0.2,h1.1]) (by norm_num [e] : 0≤e)
    simpa only [mul_one] using he
  change correctedJointBudget q0 W L a C (V+e) Red+
    0*(q-q0)-e*(commonLoss q0-commonLoss q)≤
    correctedJointBudget q W L a C (V+e) Red at hb
  unfold correctedJointBudget at hb hjunction ⊢
  dsimp only [e] at heV heR hb
  nlinarith only [hb,hjunction,heV,heR]

def previousPayment1 (x : Fin 14→ℝ) : ℝ := Coordinates.q0*Coordinates.d0 x

def paidAt1 (q : ℝ) (x : Fin 14→ℝ) : ℝ :=
  correctedJointBudget q (Coordinates.outgoing1 x) (Coordinates.returnedLength1 x)
    (Coordinates.totalAmplification1 x) (previousPayment1 x)
    (Coordinates.historicalMissing1 x) (Coordinates.historicalReduction1 x)

theorem paidAt1_junction (x : Fin 14→ℝ) :
    paidAt1 Coordinates.q1 x=CorrectedPayment.paid1 x := by
  unfold paidAt1 correctedJointBudget jointBudget previousPayment1
    Coordinates.outgoing1 Coordinates.returnedLength1 CorrectedPayment.paid1
    Coordinates.joint1 Coordinates.totalDeletion1 Coordinates.lossCoefficient
  have hr : Cycle63.Optimization.density Coordinates.q1=Coordinates.rho Coordinates.q1 := rfl
  have hh : commonLoss Coordinates.q1=CorrectedPayment.h Coordinates.q1 := rfl
  rw [hr,hh]
  ring

/-- The actual history constructor supplies the robust selected physical
constraints, the nonnegative multiplier growth, and its finite reduction
error. These facts license all terminal bins, not only the junction. -/
theorem paidAt1_all_bins (x : Fin 14→ℝ) (q : ℝ)
    (hq : Coordinates.q1≤q) (hqhi : q≤3/4)
    (hV : 0≤Coordinates.historicalMissing1 x)
    (hRed : -(1/1000000000000:ℝ)≤Coordinates.historicalReduction1 x)
    (hc : ∀i : Fin 48,-(1/1000000000000000:ℝ)≤Coordinates.rows i x) :
    (1/10000000:ℝ)<paidAt1 q x := by
  have hj:=CorrectedCertificate1.robust_lower x (1/1000000000000000) le_rfl
    (fun i=>hc (CorrectedCertificate1.selected i))
  have hw:=robust_for_physical_coordinates 14 x (1/1000000000000000) le_rfl
    (fun i=>hc ((gates 14).selected i))
  have hg:=robust_for_physical_coordinates 15 x (1/1000000000000000) le_rfl
    (fun i=>hc ((gates 15).selected i))
  change (1568511/1000000000000000:ℝ)<Coordinates.outgoing1 x at hw
  change (1568511/1000000000000000:ℝ)<Coordinates.allBinGrowth1 x at hg
  have hW : 0≤Coordinates.outgoing1 x := by linarith only [hw]
  have hG : 0≤((50/3)/(5-2*Coordinates.q1)^2)*Coordinates.outgoing1 x-
      Coordinates.returnedLength1 x := by
    change 0≤Coordinates.allBinGrowth1 x
    linarith only [hg]
  rw [←paidAt1_junction] at hj
  exact corrected_all_bins_with_finite_error (by norm_num [Coordinates.q1])
    hq hqhi hW hV hRed hG hj

def previousPayment2 (x : Fin 14→ℝ) : ℝ := Coordinates.q0*Coordinates.d0 x + Coordinates.q1*Coordinates.d1 x

def paidAt2 (q : ℝ) (x : Fin 14→ℝ) : ℝ :=
  correctedJointBudget q (Coordinates.outgoing2 x) (Coordinates.returnedLength2 x)
    (Coordinates.totalAmplification2 x) (previousPayment2 x)
    (Coordinates.historicalMissing2 x) (Coordinates.historicalReduction2 x)

theorem paidAt2_junction (x : Fin 14→ℝ) :
    paidAt2 Coordinates.q2 x=CorrectedPayment.paid2 x := by
  unfold paidAt2 correctedJointBudget jointBudget previousPayment2
    Coordinates.outgoing2 Coordinates.returnedLength2 CorrectedPayment.paid2
    Coordinates.joint2 Coordinates.totalDeletion2 Coordinates.lossCoefficient
  have hr : Cycle63.Optimization.density Coordinates.q2=Coordinates.rho Coordinates.q2 := rfl
  have hh : commonLoss Coordinates.q2=CorrectedPayment.h Coordinates.q2 := rfl
  rw [hr,hh]
  ring

/-- The actual history constructor supplies the robust selected physical
constraints, the nonnegative multiplier growth, and its finite reduction
error. These facts license all terminal bins, not only the junction. -/
theorem paidAt2_all_bins (x : Fin 14→ℝ) (q : ℝ)
    (hq : Coordinates.q2≤q) (hqhi : q≤3/4)
    (hV : 0≤Coordinates.historicalMissing2 x)
    (hRed : -(1/1000000000000:ℝ)≤Coordinates.historicalReduction2 x)
    (hc : ∀i : Fin 48,-(1/1000000000000000:ℝ)≤Coordinates.rows i x) :
    (1/10000000:ℝ)<paidAt2 q x := by
  have hj:=CorrectedCertificate2.robust_lower x (1/1000000000000000) le_rfl
    (fun i=>hc (CorrectedCertificate2.selected i))
  have hw:=robust_for_physical_coordinates 30 x (1/1000000000000000) le_rfl
    (fun i=>hc ((gates 30).selected i))
  have hg:=robust_for_physical_coordinates 31 x (1/1000000000000000) le_rfl
    (fun i=>hc ((gates 31).selected i))
  change (1568511/1000000000000000:ℝ)<Coordinates.outgoing2 x at hw
  change (1568511/1000000000000000:ℝ)<Coordinates.allBinGrowth2 x at hg
  have hW : 0≤Coordinates.outgoing2 x := by linarith only [hw]
  have hG : 0≤((50/3)/(5-2*Coordinates.q2)^2)*Coordinates.outgoing2 x-
      Coordinates.returnedLength2 x := by
    change 0≤Coordinates.allBinGrowth2 x
    linarith only [hg]
  rw [←paidAt2_junction] at hj
  exact corrected_all_bins_with_finite_error (by norm_num [Coordinates.q2])
    hq hqhi hW hV hRed hG hj

def previousPayment3 (x : Fin 14→ℝ) : ℝ := Coordinates.q0*Coordinates.d0 x + Coordinates.q1*Coordinates.d1 x + Coordinates.q2*Coordinates.d2 x

def paidAt3 (q : ℝ) (x : Fin 14→ℝ) : ℝ :=
  correctedJointBudget q (Coordinates.outgoing3 x) (Coordinates.returnedLength3 x)
    (Coordinates.totalAmplification3 x) (previousPayment3 x)
    (Coordinates.historicalMissing3 x) (Coordinates.historicalReduction3 x)

theorem paidAt3_junction (x : Fin 14→ℝ) :
    paidAt3 Coordinates.q3 x=CorrectedPayment.paid3 x := by
  unfold paidAt3 correctedJointBudget jointBudget previousPayment3
    Coordinates.outgoing3 Coordinates.returnedLength3 CorrectedPayment.paid3
    Coordinates.joint3 Coordinates.totalDeletion3 Coordinates.lossCoefficient
  have hr : Cycle63.Optimization.density Coordinates.q3=Coordinates.rho Coordinates.q3 := rfl
  have hh : commonLoss Coordinates.q3=CorrectedPayment.h Coordinates.q3 := rfl
  rw [hr,hh]
  ring

/-- The actual history constructor supplies the robust selected physical
constraints, the nonnegative multiplier growth, and its finite reduction
error. These facts license all terminal bins, not only the junction. -/
theorem paidAt3_all_bins (x : Fin 14→ℝ) (q : ℝ)
    (hq : Coordinates.q3≤q) (hqhi : q≤3/4)
    (hV : 0≤Coordinates.historicalMissing3 x)
    (hRed : -(1/1000000000000:ℝ)≤Coordinates.historicalReduction3 x)
    (hc : ∀i : Fin 48,-(1/1000000000000000:ℝ)≤Coordinates.rows i x) :
    (1/10000000:ℝ)<paidAt3 q x := by
  have hj:=CorrectedCertificate3.robust_lower x (1/1000000000000000) le_rfl
    (fun i=>hc (CorrectedCertificate3.selected i))
  have hw:=robust_for_physical_coordinates 46 x (1/1000000000000000) le_rfl
    (fun i=>hc ((gates 46).selected i))
  have hg:=robust_for_physical_coordinates 47 x (1/1000000000000000) le_rfl
    (fun i=>hc ((gates 47).selected i))
  change (1568511/1000000000000000:ℝ)<Coordinates.outgoing3 x at hw
  change (1568511/1000000000000000:ℝ)<Coordinates.allBinGrowth3 x at hg
  have hW : 0≤Coordinates.outgoing3 x := by linarith only [hw]
  have hG : 0≤((50/3)/(5-2*Coordinates.q3)^2)*Coordinates.outgoing3 x-
      Coordinates.returnedLength3 x := by
    change 0≤Coordinates.allBinGrowth3 x
    linarith only [hg]
  rw [←paidAt3_junction] at hj
  exact corrected_all_bins_with_finite_error (by norm_num [Coordinates.q3])
    hq hqhi hW hV hRed hG hj

def previousPayment4 (x : Fin 14→ℝ) : ℝ := Coordinates.q0*Coordinates.d0 x + Coordinates.q1*Coordinates.d1 x + Coordinates.q2*Coordinates.d2 x + Coordinates.q3*Coordinates.d3 x

def paidAt4 (q : ℝ) (x : Fin 14→ℝ) : ℝ :=
  correctedJointBudget q (Coordinates.outgoing4 x) (Coordinates.returnedLength4 x)
    (Coordinates.totalAmplification4 x) (previousPayment4 x)
    (Coordinates.historicalMissing4 x) (Coordinates.historicalReduction4 x)

theorem paidAt4_junction (x : Fin 14→ℝ) :
    paidAt4 Coordinates.q4 x=CorrectedPayment.paid4 x := by
  unfold paidAt4 correctedJointBudget jointBudget previousPayment4
    Coordinates.outgoing4 Coordinates.returnedLength4 CorrectedPayment.paid4
    Coordinates.joint4 Coordinates.totalDeletion4 Coordinates.lossCoefficient
  have hr : Cycle63.Optimization.density Coordinates.q4=Coordinates.rho Coordinates.q4 := rfl
  have hh : commonLoss Coordinates.q4=CorrectedPayment.h Coordinates.q4 := rfl
  rw [hr,hh]
  ring

/-- The actual history constructor supplies the robust selected physical
constraints, the nonnegative multiplier growth, and its finite reduction
error. These facts license all terminal bins, not only the junction. -/
theorem paidAt4_all_bins (x : Fin 14→ℝ) (q : ℝ)
    (hq : Coordinates.q4≤q) (hqhi : q≤3/4)
    (hV : 0≤Coordinates.historicalMissing4 x)
    (hRed : -(1/1000000000000:ℝ)≤Coordinates.historicalReduction4 x)
    (hc : ∀i : Fin 48,-(1/1000000000000000:ℝ)≤Coordinates.rows i x) :
    (1/10000000:ℝ)<paidAt4 q x := by
  have hj:=CorrectedCertificate4.robust_lower x (1/1000000000000000) le_rfl
    (fun i=>hc (CorrectedCertificate4.selected i))
  have hw:=robust_for_physical_coordinates 60 x (1/1000000000000000) le_rfl
    (fun i=>hc ((gates 60).selected i))
  have hg:=robust_for_physical_coordinates 61 x (1/1000000000000000) le_rfl
    (fun i=>hc ((gates 61).selected i))
  change (1568511/1000000000000000:ℝ)<Coordinates.outgoing4 x at hw
  change (1568511/1000000000000000:ℝ)<Coordinates.allBinGrowth4 x at hg
  have hW : 0≤Coordinates.outgoing4 x := by linarith only [hw]
  have hG : 0≤((50/3)/(5-2*Coordinates.q4)^2)*Coordinates.outgoing4 x-
      Coordinates.returnedLength4 x := by
    change 0≤Coordinates.allBinGrowth4 x
    linarith only [hg]
  rw [←paidAt4_junction] at hj
  exact corrected_all_bins_with_finite_error (by norm_num [Coordinates.q4])
    hq hqhi hW hV hRed hG hj

end
end Cycle153

#print axioms Cycle153.paidAt1_all_bins

#print axioms Cycle153.paidAt2_all_bins

#print axioms Cycle153.paidAt3_all_bins

#print axioms Cycle153.paidAt4_all_bins

#print axioms Cycle153.corrected_all_bins_with_robust_missing
