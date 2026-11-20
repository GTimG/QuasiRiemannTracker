/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Pure early scalar payment of the genuine middle-source exponent and outer fee. -/
import Candidate.C092.transport.MixedUpperFinalEnvelopeCount
import Candidate.C092.transport.PacketJoinE49PaddedFinalFee
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open OAI OAI.SevenEighths
open QRH.Cycle092.MixedOffsetCount

/-- The source uses the actual divided d and independent meshBank. The
small freely chosen errors are fixed explicitly before any live source data. -/
theorem middle_fee_le_early_reserve
    (epsD t mesh meshBank ez epsP affineError loss rowPad ell d δ p : ℝ)
    (hD : 0 ≤ epsD) (ht : 0 ≤ t) (hmesh0 : 0 ≤ meshBank) (hmesh : meshBank ≤ mesh)
    (hez : 0 ≤ ez) (hepsP : 0 ≤ epsP) (haff : 0 ≤ affineError) (hloss : 0 ≤ loss)
    (hpad : 0 ≤ rowPad) (hd : 0 < d) (hd1 : d ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (hell : ell ≤ 1/5) :
    d*(δ*p*min (1/1000:ℝ) (affineError/1000)+t*(ell/d)+δ*meshBank/2+epsD+
      (countLoss epsD meshBank t+affineError/1000+loss/1000)/2+affineError/1000)+
      (16*ez+2*epsP*d+17*t/25) ≤
      159*epsD+12*t+mesh+16*ez+2*epsP+affineError/4+loss+2*rowPad := by
  let dec := min (1/1000:ℝ) (affineError/1000)
  have hdec0 : 0 ≤ dec := le_min (by norm_num) (by positivity)
  have hdec : dec ≤ affineError/1000 := min_le_right _ _
  have hδp : δ*p ≤ 3/8 := by
    have h := mul_le_mul hδ1 hp1 hp (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at h ⊢
    exact h
  have hdecPaid : δ*p*dec ≤ 3*affineError/8000 := by
    have h := mul_le_mul hδp hdec hdec0 (by norm_num : (0:ℝ) ≤ 3/8)
    nlinarith only [h]
  have hδmesh : δ*meshBank/2 ≤ 3*mesh/8 := by
    have h := mul_le_mul hδ1 hmesh hmesh0 (by norm_num : (0:ℝ) ≤ 3/4)
    nlinarith only [h]
  let B := δ*p*dec+δ*meshBank/2+epsD+
    (countLoss epsD meshBank t+affineError/1000+loss/1000)/2+affineError/1000
  have hB0 : 0 ≤ B := by dsimp [B,countLoss]; positivity
  have hB : B ≤ 159*epsD+11*t+mesh+affineError/4+loss := by
    have hm : 0 ≤ mesh := hmesh0.trans hmesh
    dsimp only [B,countLoss]
    nlinarith only [hdecPaid,hδmesh,hmesh,hD,ht,haff,hloss,hm]
  have hprod : d*B ≤ B := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 hB0
  have hEll : t*ell ≤ t/5 := by
    have h := mul_le_mul_of_nonneg_left hell ht
    nlinarith only [h]
  have hP : epsP*d ≤ epsP := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 hepsP
  have heq : d*(δ*p*min (1/1000:ℝ) (affineError/1000)+t*(ell/d)+δ*meshBank/2+epsD+
      (countLoss epsD meshBank t+affineError/1000+loss/1000)/2+affineError/1000)+
      (16*ez+2*epsP*d+17*t/25) = d*B+t*ell+16*ez+2*epsP*d+17*t/25 := by
    dsimp only [B,dec]
    field_simp
    <;> ring
  rw [heq]
  nlinarith only [hprod,hB,hEll,hP,ht,hpad]

/-- The prescribed early reserve pays the literal
middle source expression. Padding is an additional nonnegative debit. -/
theorem middle_fee_paid_from_early_reserve
    (epsD t mesh meshBank ez epsP affineError loss rowPad ell d δ p paddingDebit : ℝ)
    (hD : 0 ≤ epsD) (ht : 0 ≤ t) (hmesh0 : 0 ≤ meshBank) (hmesh : meshBank ≤ mesh)
    (hez : 0 ≤ ez) (hepsP : 0 ≤ epsP) (haff : 0 ≤ affineError) (hloss : 0 ≤ loss)
    (hpad : 0 ≤ rowPad) (hd : 0 < d) (hd1 : d ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (hell : ell ≤ 1/5)
    (hdebit : 0 ≤ paddingDebit)
    (hreserve : 159*epsD+12*t+mesh+16*ez+2*epsP+affineError/4+loss+2*rowPad ≤ 1/100000000000000) :
    d*(δ*p*min (1/1000:ℝ) (affineError/1000)+t*(ell/d)+δ*meshBank/2+epsD+
      (countLoss epsD meshBank t+affineError/1000+loss/1000)/2+affineError/1000)+
      (16*ez+2*epsP*d+17*t/25) ≤ paddingDebit+1/100000000000000 := by
  exact (middle_fee_le_early_reserve epsD t mesh meshBank ez epsP affineError loss rowPad ell d δ p
    hD ht hmesh0 hmesh hez hepsP haff hloss hpad hd hd1 hδ hδ1 hp hp1 hell).trans
    (hreserve.trans (by linarith only [hdebit]))

section Native
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.PacketJoin
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

theorem native_early_fee_le_reserve (D : BaselineData) (P : TransportParameters D)
    (a d eps affineError loss : ℝ) (hd : 0 < d) (hd' : d ≤ 1)
    (ha : 1/2 ≤ a) (ha' : a ≤ 7/8) (heps : 0 ≤ eps)
    (haff : 0 ≤ affineError) (hloss : 0 ≤ loss) (hm : 0 ≤ P.mesh)
 :
    d*(3*(159*D.ε+8*D.t+P.mesh)/4+nativeMoment D affineError/4+nativeMass D a d)+
      (16*D.e+2*eps*d+17*D.t/25)+d*loss+2*Cycle090.rowPad ≤ 159*D.ε+12*D.t+P.mesh+16*D.e+2*eps+affineError/4+loss+2*Cycle090.rowPad := by
  have hDt := D.t_pos
  have hDep := D.epsilon_pos
  have hmass := native_mass_cost_le D a d hd hd' ha ha'
  have hcount := mul_le_mul_of_nonneg_right hd'
    (show 0 ≤ 3*(159*D.ε+8*D.t+P.mesh)/4 by positivity)
  have hmoment := mul_le_mul_of_nonneg_right hd'
    (show 0 ≤ nativeMoment D affineError/4 by unfold nativeMoment;positivity)
  have he := mul_le_mul_of_nonneg_left hd' heps
  have hl := mul_le_mul_of_nonneg_right hd' hloss
  unfold nativeMoment at hmoment ⊢
  nlinarith only [D.epsilon_pos,D.t_pos,hmass,hcount,hmoment,he,hl,hm,heps,haff,hloss]

#print axioms native_early_fee_le_reserve
end Native

#print axioms middle_fee_le_early_reserve
#print axioms middle_fee_paid_from_early_reserve
end
end QRH.Cycle092.MixedUpperFinal
