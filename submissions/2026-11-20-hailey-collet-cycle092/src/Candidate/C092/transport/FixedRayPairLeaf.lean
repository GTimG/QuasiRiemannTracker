/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedRayPairMark
import Candidate.C092.transport.StrongPairAll
namespace QRH.Cycle092.FixedRayPair
noncomputable section
set_option autoImplicit false
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

open QRH.Cycle092.StrongPair
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
theorem colored_pair_at {N Y l bΦ mesh ε Z C : ℝ} {W : ℝ→ℂ}
    {old base ω₁ ω₂ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z
      (old.product ω₁) (old.product ω₂) (base.product ω₁) (base.product ω₂) Q Q degree controls C)
    (T : Finset Slot) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (tOld t₁ t₂ height : ℝ) (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i ≤ mesh)
    (hσlo : ∀ i,(33/50:ℝ) ≤ σ i) (hσhi : ∀ i,σ i ≤ (33/50:ℝ))
    (hh : 0 ≤ height) (hv : ∀ i,|v i| ≤ height) (hsum : (∑ i∈T,w i) ≤ l)
    (hW : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hZ : 1 < Z)
    (hlarge₁ : ∀ i∈T,(ω₁.modulus.absNorm:ℝ) < Z^(w i))
    (hlarge₂ : ∀ i∈T,(ω₂.modulus.absNorm:ℝ) < Z^(w i))
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hXN : length Z X₁ ≤ N) (hXY : length Z X₂ ≤ Y)
    (s : Finset FreeRow)
    (hc₁ : Q ≤ ω₁.modulus) (hc₂ : Q ≤ ω₂.modulus)
    (hk : ∀ u∈s,initialKeep old (internalQ Q base) u.val)
    (hy : ∀ u∈s,rowNorm u ≤ Z) :
    finiteEnergyOn T s (old.product ω₁) (old.product ω₂) (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
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
    hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hXN hXY s _ (fun u hu=>(product_keep Q base old ω₁ hc₁ _).mpr (hk u hu))
    (fun u hu=>(product_keep Q base old ω₂ hc₂ _).mpr (hk u hu)) hy
  · intro u hu i hi
    exact (slot_norm rayM Hr hHr base old ω₁ (θ i)
      (fixedBadMask*idealGenerator 1) 1 u.val (Z^(w i)) (σ i) tOld t₁ (v i)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) W hW (hlarge₁ i hi)).symm
  · intro u hu i hi
    exact (slot_norm rayM Hr hHr base old ω₂ (θ i)
      (fixedBadMask*idealGenerator 1) 1 u.val (Z^(w i)) (σ i) tOld t₂ (v i)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) W hW (hlarge₂ i hi)).symm

#print axioms colored_pair_at
end
end QRH.Cycle092.FixedRayPair
