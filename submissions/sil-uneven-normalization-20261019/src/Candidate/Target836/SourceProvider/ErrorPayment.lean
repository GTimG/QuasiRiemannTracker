import Candidate.Target836.SourceProvider.ErrorNamed
import Candidate.Cycle63.Physical.FinalErrorCapacity.Physical
import Candidate.Cycle63.Physical.TerminalLedger
import Candidate.Cycle63.Physical.FinalError.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalization

/- Original module: Candidate.Target836.SourceProvider.ErrorPaid. -/
section

set_option autoImplicit false
namespace Target874836.SourceProvider.ErrorCapacity
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalErrorCapacity
open HeckeFamily CompletedGauss CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem actual_prime_widths (p : O) (hp : p ≠ 0) (Z : ℝ) (hZ : 1 < Z)
    (k : ℕ) (hk : 1  ≤  k) :
    errorRemoval p Z k = (k:ℝ)*Real.logb Z ((Ideal.span {p}).absNorm:ℝ) ∧
      0  ≤  errorMoving p Z k ∧ errorMoving p Z k  ≤  errorRemoval p Z k := by
  have hQ := Ideal.span_singleton_eq_bot.not.mpr hp
  have hn := CenteredMomentAmplificationChildSourceCaps.norm_ge_one (Ideal.span {p}) hQ
  have hl : 0  ≤  Real.logb Z (normValue p) := Real.logb_nonneg hZ hn
  have hk' : (1:ℝ)  ≤  k := by exact_mod_cast hk
  constructor
  · rfl
  · unfold errorMoving errorRemoval
    split_ifs <;> constructor <;> nlinarith

/-- The width defect is paid at the same global deletion rate as the
 original retained energy. Outside extraction and squared scalar costs
 remain separate, so the three literal alternatives can be substituted. -/
theorem paid_error_excess_bound {b M widthDefect allowance F w wo scalarLoss padding : ℝ}
    (hb : 3401/100000  ≤  b ∧ b  ≤  1/25) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hwo : wo  ≤  w) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Named.errorGap b+3*(M*Named.amp b)+(w-wo)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-(w-wo)-scalarLoss  ≤ 
      M*Named.errorGap b/6+M*Named.amp b/2-(5/6)*(w-wo)-scalarLoss+padding/6 := by
  have hpaid := Cycle63.Physical.paid_deletion_bound (F := F) hd hallowance
    (show 0  ≤  (1/6:ℝ) ∧ (1/6:ℝ)  ≤  1 by norm_num)
  have hcap : 0  ≤  M*Named.errorGap b+3*(M*Named.amp b)+(w-wo)+padding := by
    have hg := Named.errorGap_pos hb
    have ha := Named.amp_pos hb
    have hw : 0  ≤  w-wo := sub_nonneg.mpr hwo
    positivity
  have hmax := max_le hF hcap
  linarith

theorem first_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : 3401/100000  ≤  b ∧ b  ≤  1/25) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hprime : 3*(M*Named.amp b)/4  ≤  primeWidth) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Named.errorGap b+3*(M*Named.amp b)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-primeWidth  ≤ 
      -M*(1/1000)+padding/6 := by
  have hp := paid_error_excess_bound (F := F) (w := primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance le_rfl hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (Named.first_error_reserve hb) hM
  nlinarith

theorem sixth_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : 3401/100000  ≤  b ∧ b  ≤  1/25) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hprime : 3*(M*Named.amp b)/4  ≤  primeWidth) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Named.errorGap b+3*(M*Named.amp b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-6*primeWidth  ≤ 
      -M*(11360006033/482529600000)+padding/6 := by
  have ha := Named.amp_pos hb
  have hl : 0  ≤  primeWidth := by nlinarith
  have hp := paid_error_excess_bound (F := F) (w := 6*primeWidth) (wo := 0) (scalarLoss := 0)
    hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (Named.sixth_error_reserve hb) hM
  nlinarith

theorem seventh_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : 3401/100000  ≤  b ∧ b  ≤  1/25) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hprime : 3*(M*Named.amp b)/4  ≤  primeWidth) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Named.errorGap b+3*(M*Named.amp b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-7*primeWidth  ≤ 
      -M*(3516816899/120632400000)+padding/6 := by
  have ha := Named.amp_pos hb
  have hl : 0  ≤  primeWidth := by nlinarith
  have hp := paid_error_excess_bound (F := F) (w := 7*primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (Named.seventh_error_reserve hb) hM
  nlinarith

#print axioms actual_prime_widths
#print axioms paid_error_excess_bound
#print axioms first_paid_error_reserve
#print axioms sixth_paid_error_reserve
#print axioms seventh_paid_error_reserve
end
end Target874836.SourceProvider.ErrorCapacity
end

/- Original module: Candidate.Target836.SourceProvider.ErrorPayment. -/
section

set_option autoImplicit false
namespace Target874836.SourceProvider.ErrorPhysical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalError
open HeckeFamily CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open Cycle63FinalErrorCapacity
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedNormalization
local notation "O" => HeckeFamily.O

def branchReserve (k : ℕ) : ℝ :=
  if k=1 then 1/1000 else
    if k=6 then 11360006033/482529600000 else 3516816899/120632400000

theorem paid_branch_exponent {b M width nominal allowance total padding primeWidth : ℝ}
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hwidth : width-nominal ≤ allowance) (hallow : 0 ≤ allowance)
    (hprime : 3*(M*Named.amp b)/4 ≤ primeWidth) (hpadding : 0 ≤ padding)
    (hcap : total-nominal ≤ M*Named.errorGap b+3*(M*Named.amp b)+
      ((k:ℝ)*primeWidth-(if k=6 then 0 else primeWidth))+padding) :
    width+(1/6)*max (total-width) 0  ≤ 
      nominal+allowance+(k:ℝ)*primeWidth-M*branchReserve k+padding/6 := by
  have he : total-nominal-(width-nominal)=total-width := by ring
  rcases hk with rfl|rfl|rfl
  · have hp  := Target874836.SourceProvider.ErrorCapacity.first_paid_error_reserve hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith
  · have hp  := Target874836.SourceProvider.ErrorCapacity.sixth_paid_error_reserve hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith
  · have hp  := Target874836.SourceProvider.ErrorCapacity.seventh_paid_error_reserve hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith

#print axioms paid_branch_exponent

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

#print axioms normalize_error_energy
end
end Target874836.SourceProvider.ErrorPhysical
end
