/- Adapted from PR63 gao-balanced-marked-20261017; Apache-2.0. Exact source provenance is in evidence/homogeneous-gain/upstream-provenance.json. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DeletionBounds

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109GainDeletion
noncomputable section
open HeckeFamily
local notation "O" => HeckeFamily.O

/-- The number of deleted prime columns has arbitrary subpower growth in
the actual hole ideal, with one constant for every nonzero ideal. -/
theorem prime_support_card_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : Ideal O, R ≠ 0 →
      ((CompletedGauss.primeSupport R).card : ℝ) ≤ C * (R.absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 2 ε
    (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro R hR
  have hc : ((CompletedGauss.primeSupport R).card : ℝ) ≤
      (2 : ℝ)^(CompletedGauss.primeSupport R).card := by
    exact_mod_cast (show (CompletedGauss.primeSupport R).card <
      2^(CompletedGauss.primeSupport R).card from Nat.lt_two_pow_self).le
  apply hc.trans
  simpa only [CompletedGauss.primeSupport,IdealMobiusDivisorSum.primeSupport]
    using hbound R hR

end
end OAI.SevenEighths.Record12518109GainDeletion
#print axioms OAI.SevenEighths.Record12518109GainDeletion.prime_support_card_subpower
