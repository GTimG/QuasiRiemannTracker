import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalErrorCapacity.Paid
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FinalError
noncomputable section
open Cycle63.AffineLedger
open HeckeFamily CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open Cycle63FinalErrorCapacity
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedNormalization
local notation "O" => HeckeFamily.O

variable [Cycle63.AffineLedger] in
/-- The reserve of the error branch with `k` prime widths. -/
def branchReserve (k : ℕ) : ℝ :=
  if k=1 then firstErrorReserve else
    if k=6 then sixthErrorReserve else seventhErrorReserve

variable [Cycle63.AffineLedger] in
theorem paid_branch_exponent {b M width nominal allowance total padding primeWidth : ℝ}
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hb : Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) (hM : 0≤M)
    (hwidth : width-nominal≤allowance) (hallow : 0≤allowance)
    (hprime : primeFraction*(M*amp b)≤primeWidth) (hpadding : 0≤padding)
    (hcap : total-nominal≤M*g b+3*(M*amp b)+
      ((k:ℝ)*primeWidth-(if k=6 then 0 else primeWidth))+padding) :
    width+(1/6)*max (total-width) 0 ≤
      nominal+allowance+(k:ℝ)*primeWidth-M*branchReserve k+padding/6 := by
  have he : total-nominal-(width-nominal)=total-width := by ring
  rcases hk with rfl|rfl|rfl
  · have hp := first_paid_error_reserve hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith
  · have hp := sixth_paid_error_reserve hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith
  · have hp := seventh_paid_error_reserve hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith

theorem normalize_error_energy (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) (E D exponent : ℝ) (hD : 0≤D)
    (hE : E≤D*Z^(exponent+errorRemoval p Z k)) :
    localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*E≤D*Z^exponent := by
  have hz := zero_lt_one.trans hZ
  have hc := localErrorCost_nonneg p (k-1)
  have hs := mul_le_mul_of_nonneg_right (actual_error_weight p hp Z hZ k hk)
    (Real.rpow_nonneg hz.le (errorMoving p Z k))
  rw [←Real.rpow_add hz,neg_add_cancel,Real.rpow_zero] at hs
  calc
    _ ≤ localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*
        (D*Z^(exponent+errorRemoval p Z k)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = D*(localErrorCost p (k-1)*Z^(errorMoving p Z k))*Z^exponent := by
      calc
        _ = D*localErrorCost p (k-1)*(Z^(-errorRemoval p Z k+errorMoving p Z k)*
            Z^(exponent+errorRemoval p Z k)) := by ring
        _ = _ := by rw [←Real.rpow_add hz,show -errorRemoval p Z k+errorMoving p Z k+
          (exponent+errorRemoval p Z k)=errorMoving p Z k+exponent by ring,Real.rpow_add hz]; ring
    _ ≤ D*Z^exponent := by nlinarith [mul_le_mul_of_nonneg_left hs hD,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hD) (Real.rpow_nonneg hz.le exponent)]

end
end OAI.SevenEighths.Cycle63FinalError

end Record1252270103Bootstrap.PR67
