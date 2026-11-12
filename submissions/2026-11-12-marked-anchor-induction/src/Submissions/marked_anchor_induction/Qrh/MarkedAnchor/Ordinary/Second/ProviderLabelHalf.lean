/- Copyright (c) 2026 Sil. Apache-2.0.
Provider: the label half of a block.

* `outer_bound_pointwise`: a pointwise height-uniform bound `F t B ξ ≤ Λ_B (1+|t|)^{2J}` gives the
  outer weighted bound (the `hlabel` form, for any nonnegative per-split family).
* `labelAvgT_zero_of_cap`: an allocation whose residual norm cap is `< 1` has no residual column
  and contributes no label part.
* `labelHalf_of_split`: per-split label bounds on both sides of the Λ-form of `label_budget`, the
  packed twist identities and the constant inequality `K_main ≤ θ·A·Z^loss` give `LabelHalf`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderLabelData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second QRH.SilDensitySplit.CubeFree.Second.Provider
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentActiveSource
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open RepairedRawContext
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
open RayFourExpansion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeProviderLH {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- **The outer bound from a pointwise per-split bound.** -/
theorem outer_bound_pointwise (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (G : Id) (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (M Λ : actualAllocations (tuplePools s) G → ℝ)
    (F : ℝ → actualAllocations (tuplePools s) G → RayCharacter → ℝ) (J : ℕ)
    (hM : ∀ B, 0 ≤ M B) (hF0 : ∀ t B ξ, 0 ≤ F t B ξ)
    (hF : ∀ t B ξ, allocWeight s G B ≠ 0 → F t B ξ ≤ Λ B * (1 + ‖t‖)^(2*J)) :
    ∀ t : ℝ, outerAvg s hb cover G JB τ t M (F t) ≤
      (((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
          (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B))) *
        (1 + ‖t‖)^(2*J) := by
  intro t
  unfold outerAvg
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum; intro B _
  by_cases hw0 : allocWeight s G B = 0
  · rw [hw0, norm_zero]; simp
  have hA := Atot_le (allocatedLiveSource s hb cover G B) (JB B) τ t
  have h2M : 0 ≤ (2:ℝ)^(Fintype.card (JB B)) * M B := mul_nonneg (by positivity) (hM B)
  have hsum : (∑ _χ : RayCharacter, ∑ ξ : RayCharacter, F t B ξ) ≤
      (Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B *
        (1 + ‖t‖)^(2*J) := by
    calc (∑ _χ : RayCharacter, ∑ ξ : RayCharacter, F t B ξ)
        ≤ ∑ _χ : RayCharacter, ∑ _ξ : RayCharacter, Λ B * (1 + ‖t‖)^(2*J) :=
          Finset.sum_le_sum fun χ _ => Finset.sum_le_sum fun ξ _ => hF t B ξ hw0
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hsum0 : 0 ≤ ∑ _χ : RayCharacter, ∑ ξ : RayCharacter, F t B ξ :=
    Finset.sum_nonneg fun χ _ => Finset.sum_nonneg fun ξ _ => hF0 t B ξ
  have hAP0 := AtotP_nonneg (allocatedLiveSource s hb cover G B) (JB B)
  have key : Atot (allocatedLiveSource s hb cover G B) (JB B) τ t *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) * (∑ _χ : RayCharacter, ∑ ξ : RayCharacter, F t B ξ)
      ≤ AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B *
          (1 + ‖t‖)^(2*J)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hA h2M) hsum hsum0 (mul_nonneg hAP0 h2M)
  calc ‖allocWeight s G B‖^2 * (Atot (allocatedLiveSource s hb cover G B) (JB B) τ t *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) * (∑ _χ : RayCharacter, ∑ ξ : RayCharacter, F t B ξ))
      ≤ ‖allocWeight s G B‖^2 * (AtotP (allocatedLiveSource s hb cover G B) (JB B) *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B *
          (1 + ‖t‖)^(2*J))) := mul_le_mul_of_nonneg_left key (sq_nonneg _)
    _ = _ := by ring

theorem labelAvgT_nonneg (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K : ℝ)
    (T : actualAllocations (tuplePools s) G → ℝ) (Z ξr : ℝ)
    (W : actualAllocations (tuplePools s) G → ℝ) (B : actualAllocations (tuplePools s) G)
    (ξ : RayCharacter) : 0 ≤ labelAvgT s ha hb cover G J τ χ₀ Q m t K T Z ξr W B ξ := by
  unfold labelAvgT labelAvg; positivity

/-- **An allocation with residual cap `< 1` has no label part.** -/
theorem labelAvgT_zero_of_cap (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K : ℝ)
    (T : actualAllocations (tuplePools s) G → ℝ) (Z ξr : ℝ)
    (W : actualAllocations (tuplePools s) G → ℝ) (B : actualAllocations (tuplePools s) G)
    (ξ : RayCharacter)
    (hcap : sourceNormCap (restOf s hb cover G B (J B)).P b (restOf s hb cover G B (J B)).T
      (restOf s hb cover G B (J B)).d < 1) :
    labelAvgT s ha hb cover G J τ χ₀ Q m t K T Z ξr W B ξ = 0 := by
  have hS0 : ∀ I, I ∉ S0 (restOf s hb cover G B (J B)) ha := by
    intro I hI
    unfold S0 at hI
    rw [mem_activeSource] at hI
    obtain ⟨hI0, hIc⟩ := original_coefficient_cap _ ha 1 I hI.2
    have h1 : (1:ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
    linarith
  unfold labelAvgT labelAvg
  apply Finset.sum_eq_zero
  intro p _
  exfalso
  obtain ⟨q, hq, _⟩ := Finset.mem_image.mp p.property
  exact hS0 _ (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).1

/-- The constant of the label main term of one side. -/
def labelConst (s : Source ι a b) (G : Id) (N : ℕ) (Mc Kl : ℝ) : ℝ :=
  ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ)^2 *
    ((∏ i, s.M i)^2 * (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N) * ((2:ℝ)^N * Mc) *
      ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ)) * Kl *
      (4:ℝ)^(Fintype.card ι))

/-- **The label half of a block from per-split bounds.** -/
theorem labelHalf_of_split (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (η : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (K A Z loss : ℝ) (Jd : ℕ)
    (c : BlockChoice s hb cover C D K) (θl : ℝ)
    (ΛL : actualAllocations (tuplePools s) C → ℝ) (ΛR : actualAllocations (tuplePools s) D → ℝ)
    (hsL : ∀ χ ξ B ξ' (t : ℝ), allocWeight s C B ≠ 0 → labelAvgT s ha hb cover C c.JL (fixedPair η C D hC E χ (ξ⁻¹)).left
      c.χ₀ c.Q c.m t K c.TL c.Zs c.ξr c.WL B ξ' ≤ ΛL B * (1 + ‖t‖)^(2*Jd))
    (hsR : ∀ χ ξ B ξ' (t : ℝ), allocWeight s D B ≠ 0 → labelAvgT s ha hb cover D c.JR (fixedPair η C D hC E χ (ξ⁻¹)).right
      c.χ₀ c.Q c.m t K c.TR c.Zs c.ξr c.WR B ξ' ≤ ΛR B * (1 + ‖t‖)^(2*Jd))
    (hΛL0 : ∀ B, 0 ≤ ΛL B) (hΛR0 : ∀ B, 0 ≤ ΛR B) (N : ℕ) (Mc KlL KlR : ℝ)
    (hJL : ∀ B, Fintype.card (c.JL B) ≤ N) (hJR : ∀ B, Fintype.card (c.JR B) ≤ N)
    (hML : ∀ B, c.ML B ≤ Mc) (hMR : ∀ B, c.MR B ≤ Mc) (hKlL : 0 ≤ KlL) (hKlR : 0 ≤ KlR)
    (hΛL : ∀ B, ΛL B ≤ KlL * sourceVolume (renorm (restOf s hb cover C B (c.JL B)))^2 *
      (∏ j : c.JL B, (allocatedLiveSource s hb cover C B).P j.val) *
      (Ideal.absNorm (Ideal.span {Packet.firstPacked C D hC E}) : ℝ))
    (hΛR : ∀ B, ΛR B ≤ KlR * sourceVolume (renorm (restOf s hb cover D B (c.JR B)))^2 *
      (∏ j : c.JR B, (allocatedLiveSource s hb cover D B).P j.val) *
      (Ideal.absNorm (Ideal.span {Packet.firstPackedRight C D hC E}) : ℝ))
    (hcf : Packet.CubeFreeCommon C D) (hcpC : CenteredMomentCompleteCommon.commonPart C D = C)
    (hcpD : CenteredMomentCompleteCommon.commonPart D C = D)
    (hkL : labelConst s C N Mc KlL ≤ θl * A * Z^loss) (hkR : labelConst s D N Mc KlR ≤ θl * A * Z^loss)
    (hZ : 1 ≤ Z) (hθ : 0 ≤ θl) (hA : 0 ≤ A) :
    LabelHalf s ha hb cover η C D hC E K A Z loss Jd c θl := by
  have hML0 : ∀ B, 0 ≤ c.ML B := fun B => (c.hML B).1
  have hMR0 : ∀ B, 0 ≤ c.MR B := fun B => (c.hMR B).1
  refine ⟨fun _ _ => ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) C, ‖allocWeight s C B‖^2 *
          (AtotP (allocatedLiveSource s hb cover C B) (c.JL B) *
            ((2:ℝ)^(Fintype.card (c.JL B)) * c.ML B) *
            ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * ΛL B)),
    fun _ _ => ((Finset.univ : Finset (actualAllocations (tuplePools s) D)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) D, ‖allocWeight s D B‖^2 *
          (AtotP (allocatedLiveSource s hb cover D B) (c.JR B) *
            ((2:ℝ)^(Fintype.card (c.JR B)) * c.MR B) *
            ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * ΛR B)),
    ?_, ?_, ?_, ?_⟩
  · intro χ ξ v
    exact outer_bound_pointwise s hb cover C c.JL _ c.ML ΛL
      (fun t B ξ' => labelAvgT s ha hb cover C c.JL (fixedPair η C D hC E χ (ξ⁻¹)).left
        c.χ₀ c.Q c.m t K c.TL c.Zs c.ξr c.WL B ξ') Jd hML0
      (fun t B ξ' => labelAvgT_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (fun t B ξ' hw => hsL χ ξ B ξ' t hw) v
  · intro χ ξ v
    exact outer_bound_pointwise s hb cover D c.JR _ c.MR ΛR
      (fun t B ξ' => labelAvgT s ha hb cover D c.JR (fixedPair η C D hC E χ (ξ⁻¹)).right
        c.χ₀ c.Q c.m t K c.TR c.Zs c.ξr c.WR B ξ') Jd hMR0
      (fun t B ξ' => labelAvgT_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (fun t B ξ' hw => hsR χ ξ B ξ' t hw) v
  · intro χ ξ
    have hpack := packed_norm_left C D hC E hcf hcpC hcpD (fixedPair η C D hC E χ (ξ⁻¹)).left η
      (fixedPair η C D hC E χ (ξ⁻¹)).left_modulus
    have hb1 := label_budget s hb cover C c.JL c.ML ΛL N Mc KlL
      (Ideal.absNorm (Ideal.span {Packet.firstPacked C D hC E}) : ℝ) (Ideal.absNorm D : ℝ)
      (Ideal.absNorm (fixedPair η C D hC E χ (ξ⁻¹)).left.modulus : ℝ) hJL
      (fun B => ⟨hML0 B, hML B⟩) hKlL hΛL hΛL0 (Nat.cast_nonneg _) (nrm_pos hD.1) hpack hC.1
    have hb2 := label_main_le_budget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D hC.1 hD.1 A Z loss
      (labelConst s C N Mc KlL) θl hZ hθ hkL hA
    exact hb1.trans hb2
  · intro χ ξ
    have hpack := packed_norm_right C D hC E hcf hcpC hcpD (fixedPair η C D hC E χ (ξ⁻¹)).right η
      (fixedPair η C D hC E χ (ξ⁻¹)).right_modulus
    have hb1 := label_budget s hb cover D c.JR c.MR ΛR N Mc KlR
      (Ideal.absNorm (Ideal.span {Packet.firstPackedRight C D hC E}) : ℝ) (Ideal.absNorm C : ℝ)
      (Ideal.absNorm (fixedPair η C D hC E χ (ξ⁻¹)).right.modulus : ℝ) hJR
      (fun B => ⟨hMR0 B, hMR B⟩) hKlR hΛR hΛR0 (Nat.cast_nonneg _) (nrm_pos hC.1) hpack hD.1
    have hb2 := label_main_le_budget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C hD.1 hC.1 A Z loss
      (labelConst s D N Mc KlR) θl hZ hθ hkR hA
    exact hb1.trans hb2

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
