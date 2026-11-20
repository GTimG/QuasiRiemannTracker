/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The native physical average uses only nonzero original allocations.
Masking the zero weights preserves the exact sum and removes no row. -/
import Candidate.C092.transport.PairedRetainedBudgetPay
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.PairedRetainedBudget QRH.Cycle092.TwistedRawBall
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) positiveSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {ι:Type}[Fintype ι]

/-- The exact original weighted sum permits the physical class theorem to
use its genuine nonzero-allocation hypothesis for the commonH window. -/
theorem part_average_nonzero_allocations (part:Bool)(s:Source ι (1/4) (9/4))
    (cover:OriginalEnclosure s)(G:Id)
    (Js:∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (M:actualAllocations (tuplePools s) G→ℝ)(η₁ η₂ τ:Character)(χ₀:RayCharacter)(Q:Id)(m:O)
    (t K Z ξ:ℝ) :
    averagedPartSideCost part s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ =
      coloredOuterAverage s cover G Js η₁ η₂ τ t M (fun B ζ=>
        if allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B=0 then 0 else
          selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ) := by
  unfold averagedPartSideCost coloredOuterAverage
  apply congrArg (fun x:ℝ=>((actualAllocations (tuplePools s) G).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  by_cases h:allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B=0
  · simp only [h,zero_mul]
  · simp only [if_neg h]

/-- This is the native H.25 price, requiring physical estimates only on
actual positive-weight allocations. Its conclusion is the unchanged sum. -/
theorem positive_part_le_balanced (part:Bool)
    (s:Source ι (1/4) (9/4))(cover:OriginalEnclosure s)(G opp:Id)
    (Js:∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ:Character)(χ₀:RayCharacter)(Q:Id)(m:O)(t K Z ξ A loss share:ℝ)
    (M Λ:actualAllocations (tuplePools s) G→ℝ)(N J:ℕ)(Mc Kl NV:ℝ)
    (hJ:∀B,Fintype.card (Js B) ≤ N)(hM:∀B,0 ≤ M B ∧ M B ≤ Mc)(hKl:0 ≤ Kl)
    (hΛ:∀B,Λ B ≤ Kl*sourceVolume (renorm (restOf s (by norm_num) cover G B (Js B)))^2*
      (∏j:Js B,(allocatedLiveSource s (by norm_num) cover G B).P j.val)*NV)
    (hΛ0:∀B,0 ≤ Λ B)(hNV:0 ≤ NV)(hopp:opp≠0)
    (hpack:NV*(opp.absNorm:ℝ) ≤ (τ.modulus.absNorm:ℝ)*(G.absNorm:ℝ))(hG:G≠0)
    (hF:∀B,allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B≠0 → ∀ζ,
      selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ ≤ Λ B*(1+‖t‖)^(2*J))
    (hscalar:labelScalar s G N Mc Kl ≤
      share*A*Z^(CenteredMomentFirstMixedAllowance.allowance G opp Z)*Z^loss) :
    averagedPartSideCost part s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ ≤
      share*balancedBudget s τ G opp A Z loss*(1+‖t‖)^(2*J) := by
  have hop:0<(opp.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hopp)
  let F:=fun (B:actualAllocations (tuplePools s) G)(ζ:RayCharacter)=>
    if allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B=0 then 0 else
      selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ
  have hF0:∀B ζ,0 ≤ F B ζ:=by
    intro B ζ;dsimp [F]
    split_ifs
    · exact le_rfl
    · exact selectedPartTerm_nonneg part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ
  have hFb:∀B ζ,F B ζ ≤ Λ B*(1+‖t‖)^(2*J):=by
    intro B ζ;dsimp [F]
    split_ifs with h
    · exact mul_nonneg (hΛ0 B) (by positivity)
    · exact hF B h ζ
  have hmain:=colored_average_le_native_main s cover G Js η₁ η₂ τ t M Λ N J Mc Kl NV
    (opp.absNorm:ℝ) (τ.modulus.absNorm:ℝ) hJ hM hKl hΛ hΛ0 hNV hop hpack hG F hF0 hFb
  rw [←part_average_nonzero_allocations part s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ] at hmain
  have hcore:0 ≤ (τ.modulus.absNorm:ℝ)*sourceVolume s^2/((G.absNorm:ℝ)*(opp.absNorm:ℝ)):=by positivity
  have hpaid:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscalar hcore)
    (show (0:ℝ) ≤ (1+‖t‖)^(2*J) by positivity)
  exact hmain.trans (hpaid.trans_eq (by unfold balancedBudget;ring))

#print axioms part_average_nonzero_allocations
#print axioms positive_part_le_balanced
end
end QRH.Cycle092.ActualStageFrameBudget
