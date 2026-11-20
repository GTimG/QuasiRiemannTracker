/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All original common marks: fixed bounded annuli are paid whole, and only the
true large original subproduct is re-anchored into the native pair source. -/
import Candidate.C092.transport.StrongPairPhysical

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands CenteredMomentPrimeSlot
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary QRH.Cycle092.PairMarkAnchor
local notation "O" => ActualEisensteinCubic.O

variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

def ShortMarkBank (W : ℝ→ℂ) (η₁ η₂ : Character) (B : ℝ) : Prop :=
  ∀ (old base : Character) (θ : RayQuotient.Characters rayM Hr)
    (m A z : O) (P σ v t : ℝ), 1 ≤ P →
    P ≤ max (η₁.modulus.absNorm:ℝ) (η₂.modulus.absNorm:ℝ) → 0 ≤ σ →
    ‖normalizedSlot old m A z (primePool rayM Hr 2 P)
      (fun I=>idealCoeff (relativeCharacter rayM Hr hHr base θ) I*
        HeckePrimeAnnular.annularWeight W P σ v I) t P‖ ≤ B

/-- B is fixed before the ambient scale, every moving row, all live pitches,
all slot characters and all original ordinary profiles. -/
theorem short_mark_bank (W : ℝ→ℂ) (hW : Continuous W)
    (hs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (η₁ η₂ : Character) :
    ∃ B : ℝ,1 ≤ B ∧ ShortMarkBank rayM Hr hHr W η₁ η₂ B := by
  obtain ⟨B₁,hB₁,h₁⟩ := short_annulus_bound rayM Hr hHr W hW hs η₁
  obtain ⟨B₂,hB₂,h₂⟩ := short_annulus_bound rayM Hr hHr W hW hs η₂
  refine ⟨B₁+B₂+1,by linarith,?_⟩
  intro old base θ m A z P σ v t hP hPN hσ
  rcases le_max_iff.mp hPN with hN | hN
  · exact (h₁ old base θ m A z P σ v t hP hN hσ).trans (by linarith)
  · exact (h₂ old base θ m A z P σ v t hP hN hσ).trans (by linarith)

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]

/-- A complete original common-mark bound from the proved pair source.
The exact presentation equalities are derived, including arbitrary original
small/zero-width slots. There is no assumed substitute-energy estimate. -/
theorem physical_pair_all_at {N Y l bΦ mesh ε Z C B : ℝ} {W : ℝ→ℂ}
    {old base η₁ η₂ : Character} {Q₁ Q₂ : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z
      η₁ η₂ (anchoredBase base old η₁) (anchoredBase base old η₂) Q₁ Q₂ degree controls C)
    (hB : 1 ≤ B) (hbank : ShortMarkBank rayM Hr hHr W η₁ η₂ B)
    (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (tOld t₁ t₂ height : ℝ) (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i ≤ mesh)
    (hσlo : ∀ i,(33/50:ℝ) ≤ σ i) (hσhi : ∀ i,σ i ≤ (33/50:ℝ))
    (hh : 0 ≤ height) (hv : ∀ i,|v i| ≤ height) (hsum : (∑ i,w i) ≤ l)
    (hW : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hZ : 1 < Z)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hXN : length Z X₁ ≤ N) (hXY : length Z X₂ ≤ Y) (s : Finset FreeRow)
    (hk₁ : ∀ u∈s,initialKeep η₁ (internalQ Q₁ (anchoredBase base old η₁)) u.val)
    (hk₂ : ∀ u∈s,initialKeep η₂ (internalQ Q₂ (anchoredBase base old η₂)) u.val)
    (hy : ∀ u∈s,rowNorm u ≤ Z) :
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
      (originalMark rayM Hr hHr old base θ W Z w σ v tOld) ≤
    (B^(2*Fintype.card Slot)*C)*QuadraticInitialBound.diagonalControl radialMajorant*
      (p.control controls)^2*(1+|t₁|+|t₂|+(|tOld|+|t₁|+|t₂|+height))^degree*Z^(1+ε) := by
  let T : Finset Slot := Finset.univ.filter
    (fun i=>max (η₁.modulus.absNorm:ℝ) (η₂.modulus.absNorm:ℝ) < Z^(w i))
  have hTsum : (∑ i∈T,w i) ≤ l :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun i _ _=>hw i)).trans hsum
  have hlarge₁ : ∀ i∈T,(η₁.modulus.absNorm:ℝ) < Z^(w i) := by
    intro i hi
    exact (le_max_left _ _).trans_lt (Finset.mem_filter.mp hi).2
  have hlarge₂ : ∀ i∈T,(η₂.modulus.absNorm:ℝ) < Z^(w i) := by
    intro i hi
    exact (le_max_right _ _).trans_lt (Finset.mem_filter.mp hi).2
  have hsmall : ∀ u∈s,∀ i∈Finset.univ\T,
      ‖originalMark rayM Hr hHr old base θ W Z w σ v tOld i u‖ ≤ B := by
    intro u hu i hi
    have hnot := (Finset.mem_sdiff.mp hi).2
    have hPN : Z^(w i) ≤ max (η₁.modulus.absNorm:ℝ) (η₂.modulus.absNorm:ℝ) := by
      apply le_of_not_gt
      intro hh
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
    exact hbank old base (θ i) (fixedBadMask*idealGenerator 1) 1 u.val (Z^(w i)) (σ i)
      (v i) tOld (Real.one_le_rpow hZ.le (hw i)) hPN ((by norm_num : (0:ℝ) ≤ 33/50).trans (hσlo i))
  have hE := physical_pair_at rayM Hr hHr hsrc T θ w σ v tOld t₁ t₂ height hw hwm
    hσlo hσhi hh hv hTsum hW hZ hlarge₁ hlarge₂ p X₁ X₂ hX₁ hX₂ hXN hXY s hk₁ hk₂ hy
  have h := (finite_bounded_marks T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
    (originalMark rayM Hr hHr old base θ W Z w σ v tOld) B hB hsmall).trans
    (mul_le_mul_of_nonneg_left hE (pow_nonneg (by linarith : 0 ≤ B) _))
  convert h using 1 <;> ring

#print axioms short_mark_bank
#print axioms physical_pair_all_at
end
end QRH.Cycle092.StrongPair
