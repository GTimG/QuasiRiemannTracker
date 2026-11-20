/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Concrete corrected positive-part prices against the native H.25 side budget. -/
import Candidate.C092.transport.PairedRetainedBudgetAverageScalar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
local instance (priority := 2000) pairedPaySubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.Provider
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

theorem selectedPartTerm_nonneg (part : Bool) (s : Source ι (1/4) (9/4))
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (Js : Finset (liveIndices B.val)) (η₁ η₂ τ : Character)
    (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Z ξ : ℝ) (ζ : RayCharacter) :
    0 ≤ selectedPartTerm part s cover G B Js η₁ η₂ τ χ₀ Q m t K Z ξ ζ := by
  unfold selectedPartTerm RootColoredSeed.groupedPartTerms
  positivity

/-- Native H.26 numerical collection plus the actual packed first-side
    identity proves the literal fixed or regular cost. The scalar premise
    contains only finite counts/constants and the numerical chosen fee. -/
theorem averagedPartSideCost_le_balanced (part : Bool)
    (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s) (G opp : Id)
    (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Z ξ A loss share : ℝ)
    (M Λ : actualAllocations (tuplePools s) G→ℝ) (N J : ℕ) (Mc Kl NV₀ : ℝ)
    (hJ : ∀B,Fintype.card (Js B) ≤ N) (hM : ∀B,0 ≤ M B ∧ M B ≤ Mc) (hKl : 0 ≤ Kl)
    (hΛ : ∀B,Λ B ≤ Kl*(sourceVolume (renorm (restOf s (by norm_num) cover G B (Js B))))^2*
      (∏j : Js B,(allocatedLiveSource s (by norm_num) cover G B).P j.val)*NV₀)
    (hΛ0 : ∀B,0 ≤ Λ B) (hNV : 0 ≤ NV₀) (hopp : opp≠0)
    (hpack : NV₀*(opp.absNorm:ℝ) ≤ (τ.modulus.absNorm:ℝ)*(G.absNorm:ℝ)) (hG : G≠0)
    (hF : ∀B ζ,selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ ≤
      Λ B*(1+‖t‖)^(2*J))
    (hscalar : labelScalar s G N Mc Kl ≤ share*A*Z^(CenteredMomentFirstMixedAllowance.allowance G opp Z)*Z^loss) :
    averagedPartSideCost part s cover G Js M η₁ η₂ τ χ₀ Q m t K Z ξ ≤
      share*balancedBudget s τ G opp A Z loss*(1+‖t‖)^(2*J) := by
  have hop : 0<(opp.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hopp)
  have hmain := colored_average_le_native_main s cover G Js η₁ η₂ τ t M Λ N J Mc Kl NV₀
    (opp.absNorm:ℝ) (τ.modulus.absNorm:ℝ) hJ hM hKl hΛ hΛ0 hNV hop hpack hG
    (fun B ζ=>selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ)
    (fun B ζ=>selectedPartTerm_nonneg part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ) hF
  have hcore : 0 ≤ (τ.modulus.absNorm:ℝ)*sourceVolume s^2/((G.absNorm:ℝ)*(opp.absNorm:ℝ)) := by positivity
  have hpaid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscalar hcore)
    (show (0:ℝ) ≤ (1+‖t‖)^(2*J) by positivity)
  exact hmain.trans (hpaid.trans_eq (by unfold balancedBudget;ring))

#print axioms selectedPartTerm_nonneg
#print axioms averagedPartSideCost_le_balanced
end
end QRH.Cycle092.PairedRetainedBudget
