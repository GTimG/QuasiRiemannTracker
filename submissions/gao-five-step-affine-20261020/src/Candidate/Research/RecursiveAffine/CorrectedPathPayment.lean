/- Full physical path price, retaining raw scales and historical radicals. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.PhysicalPathPrice
import Candidate.Research.RecursiveAffine.CorrectedJointBudget
import Candidate.Research.RecursiveAffine.ActualCoordinateLift

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped BigOperators
open Cycle153RegionalLow

/-- The actual raw path telescope and the actual common/F capacity credit
pay precisely the corrected aggregate budget. In particular X1 stays on
the left with coefficient one. The actual row scale is used at each node;
no positive part of one minus that scale is inserted. -/
theorem finite_corrected_physical_path_price
    (n : ℕ) (delta rho cost h terminalExponent terminalMissing terminalRow terminalLoss
      rootLength modelAmp ampError error : ℝ)
    (m A amp prefixLog X0 X1 X2 X3 small Gamma D extra scalePad volumePad q fees
      V Red pad : ℕ→ℝ)
    (hrho : rho=Cycle63.Optimization.density delta)
    (hcost : cost=5-6*rho) (hh : h=Cycle153.commonLoss delta)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hcost0 : 0 ≤ cost) (hcost5 : cost ≤ 5)
    (hdelta : 0 ≤ delta) (hampError : 0 ≤ ampError)
    (hparent : ∀i<n,X0 i+X1 i+rho*X2 i+delta*X3 i ≤
      small i-(m i*(1-rho)-delta*A i-amp i*cost)-Gamma i)
    (hscale : ∀i<n,m (i+1)+prefixLog (i+1)-prefixLog i ≤ X2 i+scalePad i)
    (hvolume : ∀i<n,A (i+1) ≤ X3 i-D i-extra i+volumePad i)
    (hterminal : terminalExponent-m n+terminalMissing+rho*(terminalRow-prefixLog n) ≤
      terminalLoss-(m n*(1-rho)-delta*A n-amp n*cost))
    (hrootM : m 0 ≤ 1) (hrootA : A 0 ≤ rootLength)
    (hamp : (∑i∈Finset.range n,amp i)+amp n ≤ modelAmp+ampError)
    (hcredit : ∀i<n,(delta-h)*(V i+Red i) ≤ Gamma i+delta*extra i+h*pad i)
    (herror : terminalLoss+5*ampError+
      (∑i∈Finset.range n,(small i+fees i+rho*scalePad i+delta*volumePad i+h*pad i)) ≤ error) :
    (∑i∈Finset.range n,(m i+X0 i+q i*D i+fees i))+terminalExponent+
      (∑i∈Finset.range n,X1 i)+terminalMissing+rho*(terminalRow-prefixLog 0) ≤
    1-Cycle153.correctedJointBudget delta
      (1-(∑i∈Finset.range n,V i)-6*modelAmp)
      (rootLength-(∑i∈Finset.range n,V i)-(∑i∈Finset.range n,Red i)-(∑i∈Finset.range n,D i))
      modelAmp (∑i∈Finset.range n,q i*D i)
      (∑i∈Finset.range n,V i) (∑i∈Finset.range n,Red i)+error := by
  have ht:=finite_physical_path_price n rho delta cost terminalExponent terminalMissing terminalRow terminalLoss
    m m A amp prefixLog X0 X1 X2 X3 small Gamma D extra scalePad volumePad q fees hrho0 hrho1 hdelta
    (fun _ _=>le_rfl) hparent hscale hvolume hterminal
  have hsum : (∑i∈Finset.range n,
      (small i+fees i+rho*scalePad i+delta*volumePad i-
        (Gamma i+delta*extra i+(delta-q i)*D i))) ≤
    ∑i∈Finset.range n,
      (small i+fees i+rho*scalePad i+delta*volumePad i+h*pad i-
        (delta-h)*(V i+Red i)-(delta-q i)*D i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hc:=hcredit i (Finset.mem_range.mp hi)
    linarith only [hc]
  have hm:=mul_le_mul_of_nonneg_left hrootM hrho0
  have hA:=mul_le_mul_of_nonneg_left hrootA hdelta
  have ha:=mul_le_mul_of_nonneg_left hamp hcost0
  have hae:=mul_le_mul_of_nonneg_right hcost5 hampError
  have hid : rho+delta*rootLength+cost*modelAmp+terminalLoss+5*ampError+
      (∑i∈Finset.range n,
        (small i+fees i+rho*scalePad i+delta*volumePad i+h*pad i-
          (delta-h)*(V i+Red i)-(delta-q i)*D i)) =
      1-Cycle153.correctedJointBudget delta
        (1-(∑i∈Finset.range n,V i)-6*modelAmp)
        (rootLength-(∑i∈Finset.range n,V i)-(∑i∈Finset.range n,Red i)-(∑i∈Finset.range n,D i))
        modelAmp (∑i∈Finset.range n,q i*D i)
        (∑i∈Finset.range n,V i) (∑i∈Finset.range n,Red i)+
      (terminalLoss+5*ampError+
        (∑i∈Finset.range n,(small i+fees i+rho*scalePad i+delta*volumePad i+h*pad i))) := by
    rw [hcost,hrho,hh]
    unfold Cycle153.correctedJointBudget Cycle153.jointBudget
    simp_rw [sub_mul,mul_add]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
    ring
  have hbind : rho*m 0+delta*A 0+cost*((∑i∈Finset.range n,amp i)+amp n)+terminalLoss+
      (∑i∈Finset.range n,(small i+fees i+rho*scalePad i+delta*volumePad i-
        (Gamma i+delta*extra i+(delta-q i)*D i))) ≤
      rho+delta*rootLength+cost*modelAmp+terminalLoss+5*ampError+
        (∑i∈Finset.range n,
          (small i+fees i+rho*scalePad i+delta*volumePad i+h*pad i-
            (delta-h)*(V i+Red i)-(delta-q i)*D i)) := by
    nlinarith only [hm,hA,ha,hae,hsum]
  rw [hid] at hbind
  linarith only [ht,hbind,herror]

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.finite_corrected_physical_path_price
