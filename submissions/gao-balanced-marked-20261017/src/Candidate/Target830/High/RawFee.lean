import Candidate.Target830.Marked.Schedule
import Candidate.Target830.High.RawBudget
import Candidate.Cycle63.Marked.GeometryRawGates

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open Marked830Plain Cycle63MarkedPlain Target830
open scoped BigOperators

theorem raw_fee830 (plane : SourcePlane) (D S rho mesh normfee heightfee : ℝ)
    (hD : D ≤ 130) (hS : S ≤ 1/25) (hrho : rho ≤ 1)
    (hmesh : mesh ≤ rawRate830) (hnorm : normfee ≤ 1/1000000000)
    (hheight : heightfee ≤ 1/1000000000) :
    D*rawRate830+2*rawBin830*S+
      131*(156*rawRate830+mesh+rawRate830+rawRate830)+rawPad830*rho+
      normfee+heightfee+D*plane.rootCutoff*rawTail830 ≤ highRawFee := by
  have hroot : plane.rootCutoff ≤ 7/1000 := by
    cases plane <;> norm_num [SourcePlane.rootCutoff]
  have hn : 0 ≤ rawTail830 := by norm_num [rawTail830]
  have hDroot : D*plane.rootCutoff ≤ 130*(7/1000) := by
    have hp : 0 ≤ plane.rootCutoff := by cases plane <;> norm_num [SourcePlane.rootCutoff]
    nlinarith
  have ht:=mul_le_mul_of_nonneg_right hDroot hn
  norm_num [rawRate830,rawBin830,rawPad830,rawTail830,highRawFee] at *
  linarith

/-- The literal detector/root output pays all additions and keeps both
branches of the exact G/root minimum. -/
theorem raw_bound_paid830 (plane : SourcePlane)
    (Z tau D S rho delta normfee C Q : ℝ) (I J : ℕ)
    (hZ : 1 ≤ Z) (htau : 0 ≤ tau) (hC : 0 ≤ C)
    (hD0 : 0 ≤ D) (hD : D ≤ 130) (hS : S ≤ 1/25) (hrho : rho ≤ 1)
    (hnorm : normfee ≤ 1/1000000000) (hheight : tau*(J:ℝ) ≤ 1/1000000000)
    (hbound : Q ≤ C*(1+geometryRawHeight Z tau I)^J*
      Z^(D*(rho+rawRate830)+(delta+2*rawBin830)*S+
        131*(156*rawRate830+rawMesh830+rawRate830+rawRate830)+rawPad830*rho-
        min (Marked830.VariableSupply.physicalGain delta S ((1-6*plane.rootCutoff)*D))
          (D*plane.rootCutoff*(6*(rho+rawRate830)-1-rawTail830)))) :
    Z^normfee*Q ≤ (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*
      Z^(D*rho+delta*S-min
        (Marked830.VariableSupply.physicalGain delta S ((1-6*plane.rootCutoff)*D))
        (D*plane.rootCutoff*(6*rho-1))+highRawFee) := by
  have hp : 0<Z := zero_lt_one.trans_le hZ
  have hroot : 0 ≤ plane.rootCutoff := by cases plane <;> norm_num [SourcePlane.rootCutoff]
  let G:=Marked830.VariableSupply.physicalGain delta S ((1-6*plane.rootCutoff)*D)
  let E:=D*(rho+rawRate830)+(delta+2*rawBin830)*S+
    131*(156*rawRate830+rawMesh830+rawRate830+rawRate830)+rawPad830*rho-
      min G (D*plane.rootCutoff*(6*(rho+rawRate830)-1-rawTail830))
  have hfee:=raw_fee830 plane D S rho rawMesh830 normfee (tau*(J:ℝ)) hD hS hrho
    raw_mesh830_gates.2.2 hnorm hheight
  have hdef:=raw_gain_defect G D plane.rootCutoff rho rawRate830 rawTail830 hD0 hroot
    (by norm_num [rawRate830]) (by norm_num [rawTail830])
  have he : E+normfee+tau*(J:ℝ) ≤ D*rho+delta*S-
      min G (D*plane.rootCutoff*(6*rho-1))+highRawFee := by
    dsimp only [E]
    nlinarith only [hfee,hdef]
  calc
    _ ≤ Z^normfee*(C*(1+geometryRawHeight Z tau I)^J*Z^E) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hp.le _)
    _ ≤ Z^normfee*(C*((1+2*Real.pi+6*(I+1:ℕ))^J*Z^(tau*(J:ℝ)))*Z^E) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
      exact mul_le_mul_of_nonneg_left (geometry_raw_height_power hZ htau I J) hC
    _ = (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*Z^(E+normfee+tau*(J:ℝ)) := by
      rw [Real.rpow_add hp,Real.rpow_add hp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he)
      (by positivity)

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.raw_fee830
#print axioms OAI.SevenEighths.TargetHigh830.raw_bound_paid830
