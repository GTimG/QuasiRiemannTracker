import Candidate.Uneven.MainCellGeometry
import Candidate.Cycle63.Physical.FinalErrorCapacity.Physical
import Candidate.Cycle63.Physical.TerminalLedger
import Candidate.Cycle63.Physical.FinalError.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalization

/- Original module: Candidate.Uneven.MainErrorPaid. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.MainError
noncomputable section
open Sil.Uneven.MainSource
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalErrorCapacity
open HeckeFamily CompletedGauss CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable (P : Plane)


/-- The width defect is paid at the same global deletion rate as the
 original retained energy. Outside extraction and squared scalar costs
 remain separate, so the three literal alternatives can be substituted. -/
theorem paid_error_excess_bound {b M widthDefect allowance F w wo scalarLoss padding : ℝ}
    (hb : widthLo ≤ b ∧ b ≤ widthHi) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hwo : wo  ≤  w) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Sil.Uneven.MainSource.gap P b+3*(M*Sil.Uneven.MainSource.amp P b)+(w-wo)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-(w-wo)-scalarLoss  ≤ 
      M*Sil.Uneven.MainSource.gap P b/6+M*Sil.Uneven.MainSource.amp P b/2-(5/6)*(w-wo)-scalarLoss+padding/6 := by
  have hpaid := Cycle63.Physical.paid_deletion_bound (F := F) hd hallowance
    (show 0  ≤  (1/6:ℝ) ∧ (1/6:ℝ)  ≤  1 by norm_num)
  have hcap : 0  ≤  M*Sil.Uneven.MainSource.gap P b+3*(M*Sil.Uneven.MainSource.amp P b)+(w-wo)+padding := by
    have hg := (scheduling_guards P hb).1
    have ha : 0< Sil.Uneven.MainSource.amp P b := lt_of_lt_of_le (scheduling_guards P hb).2.1 (scheduling_guards P hb).2.2.1
    have hw : 0  ≤  w-wo := sub_nonneg.mpr hwo
    positivity
  have hmax := max_le hF hcap
  linarith

theorem first_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : widthLo ≤ b ∧ b ≤ widthHi) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hprime : 3*(M*Sil.Uneven.MainSource.amp P b)/4  ≤  primeWidth) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Sil.Uneven.MainSource.gap P b+3*(M*Sil.Uneven.MainSource.amp P b)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-primeWidth  ≤ 
      -M*errorReserve+padding/6 := by
  have hp := paid_error_excess_bound P (F := F) (w := primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance le_rfl hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (error_reserves P hb).1.le hM
  nlinarith

theorem sixth_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : widthLo ≤ b ∧ b ≤ widthHi) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hprime : 3*(M*Sil.Uneven.MainSource.amp P b)/4  ≤  primeWidth) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Sil.Uneven.MainSource.gap P b+3*(M*Sil.Uneven.MainSource.amp P b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-6*primeWidth  ≤ 
      -M*errorReserve+padding/6 := by
  have ha : 0< Sil.Uneven.MainSource.amp P b := lt_of_lt_of_le (scheduling_guards P hb).2.1 (scheduling_guards P hb).2.2.1
  have hl : 0  ≤  primeWidth := by nlinarith
  have hp := paid_error_excess_bound P (F := F) (w := 6*primeWidth) (wo := 0) (scalarLoss := 0)
    hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (error_reserves P hb).2.1.le hM
  nlinarith

theorem seventh_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : widthLo ≤ b ∧ b ≤ widthHi) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hprime : 3*(M*Sil.Uneven.MainSource.amp P b)/4  ≤  primeWidth) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Sil.Uneven.MainSource.gap P b+3*(M*Sil.Uneven.MainSource.amp P b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-7*primeWidth  ≤ 
      -M*errorReserve+padding/6 := by
  have ha : 0< Sil.Uneven.MainSource.amp P b := lt_of_lt_of_le (scheduling_guards P hb).2.1 (scheduling_guards P hb).2.2.1
  have hl : 0  ≤  primeWidth := by nlinarith
  have hp := paid_error_excess_bound P (F := F) (w := 7*primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (error_reserves P hb).2.2.le hM
  nlinarith

end
end OAI.SevenEighths.MainError
end

/- Original module: Candidate.Uneven.MainErrorPayment. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.MainError
noncomputable section
open Sil.Uneven.MainSource
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalError
open HeckeFamily CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open Cycle63FinalErrorCapacity
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedNormalization
local notation "O" => HeckeFamily.O
variable (P : Plane)

def branchReserve (_k : ℕ) : ℝ := errorReserve

theorem paid_branch_exponent {b M width nominal allowance total padding primeWidth : ℝ}
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hb : widthLo ≤ b ∧ b ≤ widthHi) (hM : 0 ≤ M)
    (hwidth : width-nominal ≤ allowance) (hallow : 0 ≤ allowance)
    (hprime : 3*(M*Sil.Uneven.MainSource.amp P b)/4 ≤ primeWidth) (hpadding : 0 ≤ padding)
    (hcap : total-nominal ≤ M*Sil.Uneven.MainSource.gap P b+3*(M*Sil.Uneven.MainSource.amp P b)+
      ((k:ℝ)*primeWidth-(if k=6 then 0 else primeWidth))+padding) :
    width+(1/6)*max (total-width) 0  ≤ 
      nominal+allowance+(k:ℝ)*primeWidth-M*branchReserve k+padding/6 := by
  have he : total-nominal-(width-nominal)=total-width := by ring
  rcases hk with rfl|rfl|rfl
  · have hp  := MainError.first_paid_error_reserve P hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith
  · have hp  := MainError.sixth_paid_error_reserve P hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith
  · have hp  := MainError.seventh_paid_error_reserve P hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith


theorem normalize_error_energy (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1 < Z)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) (E D exponent : ℝ) (hD : 0 ≤ D)
    (hE : E ≤ D*Z^(exponent+errorRemoval p Z k)) :
    localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*E ≤ D*Z^exponent := by
  have hz := zero_lt_one.trans hZ
  have hc := localErrorCost_nonneg p (k-1)
  have hs := mul_le_mul_of_nonneg_right (actual_error_weight p hp Z hZ k hk)
    (Real.rpow_nonneg hz.le (errorMoving p Z k))
  rw [←Real.rpow_add hz,neg_add_cancel,Real.rpow_zero] at hs
  calc
    _  ≤  localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*
        (D*Z^(exponent+errorRemoval p Z k)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = D*(localErrorCost p (k-1)*Z^(errorMoving p Z k))*Z^exponent := by
      calc
        _ = D*localErrorCost p (k-1)*(Z^(-errorRemoval p Z k+errorMoving p Z k)*
            Z^(exponent+errorRemoval p Z k)) := by ring
        _ = _ := by rw [←Real.rpow_add hz,show -errorRemoval p Z k+errorMoving p Z k+
          (exponent+errorRemoval p Z k)=errorMoving p Z k+exponent by ring,Real.rpow_add hz]; ring
    _  ≤  D*Z^exponent := by nlinarith [mul_le_mul_of_nonneg_left hs hD,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hD) (Real.rpow_nonneg hz.le exponent)]

end
end OAI.SevenEighths.MainError
end
