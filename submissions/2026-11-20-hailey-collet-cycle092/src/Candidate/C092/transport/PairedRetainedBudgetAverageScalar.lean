/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   H.25 scalar assembly for the corrected selected-image average. -/
import Candidate.C092.transport.PairedRetainedBudgetAverage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
local instance (priority := 2000) pairedAverageScalarSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAddedZeroUniform
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.TwistedRawBall
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

/-- All native finite allocation, ray, Gauss and frozen-profile constants. -/
def labelScalar (s : Source ι (1/4) (9/4)) (G : Id) (N : ℕ) (Mc Kl : ℝ) : ℝ :=
  ((actualAllocations (tuplePools s) G).card : ℝ)^2 *
    ((∏i,s.M i)^2*(pcMass*(∏i,s.M i)^2*(256:ℝ)^N)*((2:ℝ)^N*Mc)*
      ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))*Kl*(4:ℝ)^Fintype.card ι)

/-- Corrected image-multiplicity collection, followed by exact native Π and
    live-volume cancellation, restores the original H.25 denominator.
    F remains the actual fixed or regular positive physical child. -/
theorem colored_average_le_native_main (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (G : Id) (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t : ℝ) (M Λ : actualAllocations (tuplePools s) G→ℝ)
    (N J : ℕ) (Mc Kl NV₀ Nopp Nτ : ℝ)
    (hJ : ∀B,Fintype.card (Js B) ≤ N) (hM : ∀B,0 ≤ M B ∧ M B ≤ Mc) (hKl : 0 ≤ Kl)
    (hΛ : ∀B,Λ B ≤ Kl*sourceVolume (renorm (restOf s (by norm_num) cover G B (Js B)))^2*
      (∏j : Js B,(allocatedLiveSource s (by norm_num) cover G B).P j.val)*NV₀)
    (hΛ0 : ∀B,0 ≤ Λ B) (hNV : 0 ≤ NV₀) (hNopp : 0<Nopp)
    (hpack : NV₀*Nopp ≤ Nτ*(G.absNorm:ℝ)) (hG : G≠0)
    (F : actualAllocations (tuplePools s) G→RayCharacter→ℝ)
    (hF0 : ∀B ζ,0 ≤ F B ζ) (hF : ∀B ζ,F B ζ ≤ Λ B*(1+‖t‖)^(2*J)) :
    coloredOuterAverage s cover G Js η₁ η₂ τ t M F ≤
      labelScalar s G N Mc Kl*(Nτ*sourceVolume s^2/((G.absNorm:ℝ)*Nopp))*(1+‖t‖)^(2*J) := by
  have ho := colored_outerAverage_bound s cover G Js η₁ η₂ τ t M Λ F J (fun B=>(hM B).1) hF0 hF
  have hb := colored_label_budget s η₁ η₂ (by norm_num) cover G Js M Λ N Mc Kl NV₀ Nopp Nτ
    hJ hM hKl hΛ hΛ0 hNV hNopp hpack hG
  have hb' :
      (((actualAllocations (tuplePools s) G).card : ℝ)*
        ∑B : actualAllocations (tuplePools s) G,allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B*
          (AtotP (allocatedLiveSource s (by norm_num) cover G B) (Js B)*
            ((2:ℝ)^Fintype.card (Js B)*M B)*
              ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ)*Λ B))) ≤
      labelScalar s G N Mc Kl*(Nτ*sourceVolume s^2/((G.absNorm:ℝ)*Nopp)) := by
    simpa only [Finset.card_univ,Fintype.card_coe,labelScalar] using hb
  exact ho.trans (mul_le_mul_of_nonneg_right hb' (by positivity))

#print axioms colored_average_le_native_main
end
end QRH.Cycle092.PairedRetainedBudget
