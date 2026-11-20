/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Physical support conversion is made before querying a terminal estimate.
It applies at every radius and preserves the empty original subset. -/
import Candidate.C092.transport.FixedRayPairLeaf
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorPlainFiberSource CenteredMomentWholeSlotDeletion
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair QRH.Cycle092.OrdinaryColumn
namespace QRH.Cycle092.FixedRayPair
local notation "O" => HeckeFamily.O
variable {Slot:Type} [Fintype Slot] [DecidableEq Slot]

theorem drop_bounded (F T:Finset Slot) (hf:F⊆T) (s:Finset FreeRow)
    (η₁ η₂:Character) (W₁ W₂:ℝ→ℂ) (t₁ t₂ X₁ X₂:ℝ) (mark:Slot→FreeRow→ℂ)
    (B:ℝ) (hb:1≤B) (h:∀ u∈s,∀ i∈T\F,‖mark i u‖≤B) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
    B^(2*Fintype.card Slot)*finiteEnergyOn F s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  classical
  unfold finiteEnergyOn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum;intro u hu
  have hB : 1≤B^2 := by nlinarith
  have hp : (∏ i∈T\F,‖mark i u‖^2) ≤ B^(2*Fintype.card Slot) := by
    calc
      _ ≤ ∏ _i∈T\F,B^2 := Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) (fun i hi=>pow_le_pow_left₀ (norm_nonneg _) (h u hu i hi) _)
      _ = (B^2)^(T\F).card := by simp
      _ ≤ _ := by rw [pow_mul];exact pow_le_pow_right₀ hB (Finset.card_le_univ _)
  have hsplit := Finset.prod_sdiff (f:=fun i=>‖mark i u‖^2) hf
  rw [←hsplit]
  have hmul:=mul_le_mul_of_nonneg_right hp (show 0 ≤
      ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
      ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
      ∏ i∈F,‖mark i u‖^2 by positivity)
  convert hmul using 1 <;> ring

variable (rayM:Ideal O) [NeZero rayM] (Hr:Subgroup (O⧸rayM)ˣ)
variable (hHr:RayOrthogonality.globalUnits rayM≤Hr)

theorem original_product_support (W:ℝ→ℂ) (hW:Continuous W)
    (hs:Function.support W ⊆ Set.Icc (1:ℝ) 2) (ω₁ ω₂:Character) :
    ∃ B:ℝ,1≤B ∧ ∀ (Z:ℝ),1<Z → ∀ (old base:Character) (θ:Slot→RayQuotient.Characters rayM Hr)
    (w σ v:Slot→ℝ) (t t₁ t₂:ℝ), (∀ i,0≤w i) → (∀ i,0≤σ i) → ∀ T:Finset Slot,
    ∃ F:Finset Slot,F⊆T ∧ (∑ i∈F,w i)≤∑ i∈T,w i ∧
      (∀ u:FreeRow,∀ i∈F,
        ‖originalMark rayM Hr hHr old base θ W Z w σ v t i u‖=
        ‖originalMark rayM Hr hHr (old.product ω₁) (base.product ω₁) θ W Z w σ (fun i=>t+v i-t₁) t₁ i u‖ ∧
        ‖originalMark rayM Hr hHr old base θ W Z w σ v t i u‖=
        ‖originalMark rayM Hr hHr (old.product ω₂) (base.product ω₂) θ W Z w σ (fun i=>t+v i-t₂) t₂ i u‖) ∧
      ∀ (rows:Finset FreeRow) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ),
        finiteEnergyOn T rows (old.product ω₁) (old.product ω₂) W₁ W₂ t₁ t₂ X₁ X₂
          (originalMark rayM Hr hHr old base θ W Z w σ v t) ≤
        B^(2*Fintype.card Slot)*finiteEnergyOn F rows (old.product ω₁) (old.product ω₂) W₁ W₂ t₁ t₂ X₁ X₂
          (originalMark rayM Hr hHr old base θ W Z w σ v t) := by
  obtain ⟨B,hB,hbank⟩:=short_mark_bank rayM Hr hHr W hW hs ω₁ ω₂
  refine ⟨B,hB,?_⟩
  intro Z hZ old base θ w σ v t t₁ t₂ hw hσ T
  let F:=T.filter (fun i=>max (ω₁.modulus.absNorm:ℝ) (ω₂.modulus.absNorm:ℝ)<Z^(w i))
  have hF:F⊆T:=Finset.filter_subset _ _
  refine ⟨F,hF,Finset.sum_le_sum_of_subset_of_nonneg hF (fun i _ _=>hw i),?_,?_⟩
  · intro u i hi
    have hp:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (w i)
    have hl:= (Finset.mem_filter.mp hi).2
    exact ⟨(slot_norm rayM Hr hHr base old ω₁ (θ i) (fixedBadMask*idealGenerator 1) 1 u.val (Z^(w i))
      (σ i) t t₁ (v i) hp W hs ((le_max_left _ _).trans_lt hl)).symm,
      (slot_norm rayM Hr hHr base old ω₂ (θ i) (fixedBadMask*idealGenerator 1) 1 u.val (Z^(w i))
      (σ i) t t₂ (v i) hp W hs ((le_max_right _ _).trans_lt hl)).symm⟩
  · intro s W₁ W₂ X₁ X₂
    apply drop_bounded F T hF s _ _ W₁ W₂ _ _ X₁ X₂ _ B hB
    intro u hu i hi
    have hlarge : Z^(w i) ≤ max (ω₁.modulus.absNorm:ℝ) (ω₂.modulus.absNorm:ℝ) :=
      le_of_not_gt (fun h=>(Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1,h⟩))
    exact hbank old base (θ i) (fixedBadMask*idealGenerator 1) 1 u.val (Z^(w i)) (σ i) (v i) t (Real.one_le_rpow hZ.le (hw i)) hlarge (hσ i)

#print axioms original_product_support
end QRH.Cycle092.FixedRayPair
