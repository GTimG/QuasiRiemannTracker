/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Native H.25/H.26 allocation budget with the two exact ordinary color contractions. -/
import Candidate.C092.transport.PairedRetainedBudgetVolumes
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderLabelBudget
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
local instance (priority := 2000) pairedScalarSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAddedZeroUniform
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedInnerExceptionalBlock
open MixedFirstLiveSource MixedCommonCoefficient
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.TwistedRawBall
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι] {a b : ℝ}

/-- The original common scalar can only decrease when the two authentic
    ordinary colors are installed; no quotient by a color is taken. -/
theorem colored_allocation_weight_le (s : Source ι a b) (η₁ η₂ : Character)
    (G : Id) (B : actualAllocations (tuplePools s) G) :
    allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B ≤ ‖allocWeight s G B‖^2 := by
  have hc := TwistedRawSource.ordinaryColor_norm_le_one η₁ η₂ B.val
  have he : allocationScalar s (idealCoeff η₁) (idealCoeff η₂) G B =
      allocWeight s G B*TwistedRawSource.ordinaryColor (idealCoeff η₁) (idealCoeff η₂) B.val := by
    unfold allocationScalar allocWeight
    ring
  unfold allocationWeight
  rw [he,norm_mul]
  exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (norm_nonneg _) hc) 2

/-- This is native label_budget on the ACTUAL independently colored
    allocation weights. It retains the selected Π, full original volume,
    packed orientation and denominator NG*Nopp. The inputs Λ and M are
    numerical bounds for the literal selected physical classes. -/
theorem colored_label_budget (s : Source ι a b) (η₁ η₂ : Character) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (M Λ : actualAllocations (tuplePools s) G → ℝ) (N : ℕ) (Mc Kl NV₀ Nopp Nτ : ℝ)
    (hJ : ∀ B, Fintype.card (JB B) ≤ N) (hM : ∀ B, 0 ≤ M B ∧ M B ≤ Mc) (hKl : 0 ≤ Kl)
    (hΛ : ∀ B, Λ B ≤ Kl * sourceVolume (renorm (restOf s hb cover G B (JB B)))^2 *
      (∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val) * NV₀)
    (hΛ0 : ∀ B, 0 ≤ Λ B) (hNV : 0 ≤ NV₀) (hNopp : 0 < Nopp) (hpack : NV₀ * Nopp ≤ Nτ * (Ideal.absNorm G : ℝ))
    (hG : G ≠ 0) :
    ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
          (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B)) ≤
      ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ)^2 *
        ((∏ i, s.M i)^2 * (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N) * ((2:ℝ)^N * Mc) *
          ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ)) * Kl *
          (4:ℝ)^(Fintype.card ι)) *
        (Nτ * sourceVolume s^2 / ((Ideal.absNorm G : ℝ) * Nopp)) := by
  have hn := QRH.SilDensitySplit.CubeFree.Second.Provider.label_budget s hb cover G JB
    M Λ N Mc Kl NV₀ Nopp Nτ hJ hM hKl hΛ hΛ0 hNV hNopp hpack hG
  apply LE.le.trans _ hn
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B hB
  apply mul_le_mul_of_nonneg_right (colored_allocation_weight_le s η₁ η₂ G B)
  have hA := AtotP_nonneg (allocatedLiveSource s hb cover G B) (JB B)
  have hM0 := (hM B).1
  have hΛB := hΛ0 B
  positivity

#print axioms colored_allocation_weight_le
#print axioms colored_label_budget
end
end QRH.Cycle092.PairedRetainedBudget
