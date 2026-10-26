import Candidate.Cycle63.Physical.InitialMass.MarkedParameters
import Candidate.Target836.Marked836.MarkedRate

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Marked836Plain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section

/-- The original sixth-root cutoff pays the changing coefficient, using the
actual density at the same zero bin. No independent density is substituted. -/
theorem marked_tail_dominates (D ρ ordloss S δ : ℝ) (hD : 0≤D)
    (hδ0 : (839/1250:ℝ)≤δ) (hδ : δ≤7/10)
    (hρ : Marked836.VariableSupply.density δ≤ρ) (hord : 0≤ordloss) :
    min (Marked836.VariableSupply.coefficient δ*min S ((13/400)*((1-6*markedRootCutoff)*D)))
      (D*markedRootCutoff*(6*(ρ+ordloss)-1-(9/100))) =
        Marked836.VariableSupply.coefficient δ*min S ((13/400)*((1-6*markedRootCutoff)*D)) := by
  apply min_eq_left
  have hc := Marked836.VariableSupply.coefficient_nonneg (show 13/20≤δ by linarith) hδ
  have hcap := mul_le_mul_of_nonneg_left
    (min_le_right S ((13/400)*((1-6*markedRootCutoff)*D))) hc
  have ht := Marked836.VariableSupply.old_root_tail_dominates (show 13/20≤δ by linarith) hδ
  have htd := mul_le_mul_of_nonneg_right ht hD
  have hr := mul_le_mul_of_nonneg_left hρ (show 0≤D/250 by positivity)
  have ho := mul_nonneg hD hord
  dsimp [markedRootCutoff] at hcap ⊢
  nlinarith

/-- The accepted mesh, bin, padding and height prices remain explicit. -/
theorem marked_raw_exponent_paid (D S ρ δ mesh μ normfee heightfee : ℝ)
    (hD0 : 0≤D) (hD : D≤130) (hS : S≤1/25)
    (hδ0 : (839/1250:ℝ)≤δ) (hδ : δ≤7/10)
    (hρeq : ρ=Marked836.VariableSupply.density δ)
    (hρ : ρ≤1) (hmesh : mesh≤markedRate)
    (hμ : μ≤1/100000000) (hnorm : normfee≤μ/32) (hheight : heightfee≤μ/8) :
    D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
      131*(156*markedRate+mesh+markedRate+markedRate)+markedPad*ρ-
      min (Marked836.VariableSupply.coefficient δ*min S ((13/400)*((1-6*markedRootCutoff)*D)))
        (D*markedRootCutoff*(6*(ρ+markedRate)-1-(9/100)))+normfee+heightfee≤
      D*ρ+δ*S-Marked836.VariableSupply.coefficient δ*min S ((13/400)*((1-6*markedRootCutoff)*D))+(1/200000:ℝ) := by
  rw [marked_tail_dominates D ρ markedRate S δ hD0 hδ0 hδ
    (by rw [hρeq]) (by norm_num [markedRate])]
  have h := marked_raw_error_budget D S ρ mesh μ normfee heightfee
    hD hS hρ hmesh hμ hnorm hheight
  nlinarith

end
end OAI.SevenEighths.Marked836Plain
#print axioms OAI.SevenEighths.Marked836Plain.marked_tail_dominates
#print axioms OAI.SevenEighths.Marked836Plain.marked_raw_exponent_paid
