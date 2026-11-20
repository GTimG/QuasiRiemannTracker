/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual common original marks at independent ordinary anchors. Large annuli
re-anchor exactly; whole bounded annuli have a fixed absolute cost. -/
import Candidate.C092.transport.StrongPairSource
import Candidate.C092.transport.PairMarkAnnulus

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
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary QRH.Cycle092.PairMarkAnchor
local notation "O" => ActualEisensteinCubic.O

/-- Removing only uniformly bounded whole marks changes neither ordinary
factor, row set, character, height, profile nor mask. -/
theorem finite_bounded_marks {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T : Finset Slot) (s : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot→FreeRow→ℂ) (C : ℝ) (hC : 1 ≤ C)
    (hmark : ∀ u∈s,∀ i∈Finset.univ\T,‖mark i u‖ ≤ C) :
    finiteEnergy s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      C^(2*Fintype.card Slot)*finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  unfold finiteEnergy finiteEnergyOn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hp : (∏ i∈Finset.univ\T,‖mark i u‖^2) ≤ C^(2*Fintype.card Slot) := by
    have h := Finset.prod_le_prod₀ (fun i _=>sq_nonneg ‖mark i u‖)
      (fun i hi=>pow_le_pow_left₀ (norm_nonneg _) (hmark u hu i hi) 2)
    have hc : (Finset.univ\T).card ≤ Fintype.card Slot := by
      simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ (Finset.univ\T))
    apply h.trans
    rw [Finset.prod_const]
    have hC₂ : 1 ≤ C^2 := by nlinarith
    simpa only [←pow_mul] using pow_le_pow_right₀ hC₂ hc
  have he := Finset.prod_sdiff (f:=fun i=>‖mark i u‖^2) (Finset.subset_univ T)
  rw [←he]
  have hmul := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
      ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
      ∏ i∈T,‖mark i u‖^2 by positivity)
  convert hmul using 1 <;> ring

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

def originalMark (old base : Character) (θ : Slot→RayQuotient.Characters rayM Hr)
    (W : ℝ→ℂ) (Z : ℝ) (w σ v : Slot→ℝ) (t : ℝ) : Slot→FreeRow→ℂ :=
  fun i u=>normalizedSlot old (fixedBadMask*idealGenerator 1) 1 u.val
    (originalPools rayM Hr 2 Z w i)
    (originalCoefficients rayM Hr hHr base θ W Z w σ v i) t (Z^(w i))

/-- Exact actual common-mark specialization on all selected large annuli.
Each ordinary keeps its own fixed ray and pitch. No prime profile is changed. -/
theorem physical_pair_at {N Y l bΦ mesh ε Z C : ℝ} {W : ℝ→ℂ}
    {old base η₁ η₂ : Character} {Q₁ Q₂ : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z
      η₁ η₂ (anchoredBase base old η₁) (anchoredBase base old η₂) Q₁ Q₂ degree controls C)
    (T : Finset Slot) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (tOld t₁ t₂ height : ℝ) (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i ≤ mesh)
    (hσlo : ∀ i,(33/50:ℝ) ≤ σ i) (hσhi : ∀ i,σ i ≤ (33/50:ℝ))
    (hh : 0 ≤ height) (hv : ∀ i,|v i| ≤ height) (hsum : (∑ i∈T,w i) ≤ l)
    (hW : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hZ : 1 < Z)
    (hlarge₁ : ∀ i∈T,(η₁.modulus.absNorm:ℝ) < Z^(w i))
    (hlarge₂ : ∀ i∈T,(η₂.modulus.absNorm:ℝ) < Z^(w i))
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hXN : length Z X₁ ≤ N) (hXY : length Z X₂ ≤ Y)
    (s : Finset FreeRow)
    (hk₁ : ∀ u∈s,initialKeep η₁ (internalQ Q₁ (anchoredBase base old η₁)) u.val)
    (hk₂ : ∀ u∈s,initialKeep η₂ (internalQ Q₂ (anchoredBase base old η₂)) u.val)
    (hy : ∀ u∈s,rowNorm u ≤ Z) :
    finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
      (originalMark rayM Hr hHr old base θ W Z w σ v tOld) ≤
    C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
      (1+|t₁|+|t₂|+(|tOld|+|t₁|+|t₂|+height))^degree*Z^(1+ε) := by
  have hv₁ : ∀ i,|tOld+v i-t₁| ≤ |tOld|+|t₁|+|t₂|+height := by
    intro i
    have h := abs_sub (tOld+v i) t₁
    have ha := abs_add_le tOld (v i)
    linarith [hv i,abs_nonneg t₂]
  have hv₂ : ∀ i,|tOld+v i-t₂| ≤ |tOld|+|t₁|+|t₂|+height := by
    intro i
    have h := abs_sub (tOld+v i) t₂
    have ha := abs_add_le tOld (v i)
    linarith [hv i,abs_nonneg t₁]
  apply hsrc T θ θ w σ σ (fun i=>tOld+v i-t₁) (fun i=>tOld+v i-t₂) t₁ t₂
    (|tOld|+|t₁|+|t₂|+height) hw hwm hσlo hσhi hσlo hσhi (by positivity)
    hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hXN hXY s _ hk₁ hk₂ hy
  · intro u hu i hi
    exact (full_annulus_norm rayM Hr hHr base old η₁ (θ i)
      (fixedBadMask*idealGenerator 1) 1 u.val (Z^(w i)) (σ i) tOld t₁ (v i)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) W hW (hlarge₁ i hi)).symm
  · intro u hu i hi
    exact (full_annulus_norm rayM Hr hHr base old η₂ (θ i)
      (fixedBadMask*idealGenerator 1) 1 u.val (Z^(w i)) (σ i) tOld t₂ (v i)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) W hW (hlarge₂ i hi)).symm

#print axioms physical_pair_at
#print axioms finite_bounded_marks
end
end QRH.Cycle092.StrongPair
