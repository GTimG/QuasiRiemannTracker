/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual P3 on the detector's authentic fixed witness anchors. All original
prime factors, including bounded scales and zeros, are EXACTLY the same. -/
import Candidate.C092.transport.StrongPairLowAbove
import Candidate.C092.transport.WitnessOriginalMark

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
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.MediumReplace.Source
local notation "O" => ActualEisensteinCubic.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

theorem witness_low_pair_paid {N Y l bΦ mesh ε U V C e Cslot buffer L rounding allowance : ℝ}
    {W : ℝ→ℂ} (η base : Character) (j₁ j₂) (Q : Ideal O)
    {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε (U^V)
      (witnessBase rayM Hr hHr η base j₁) (witnessBase rayM Hr hHr η base j₂)
      (witnessBase rayM Hr hHr base base j₁) (witnessBase rayM Hr hHr base base j₂)
      Q Q degree controls C)
    (F : Finset Slot) (θ : Slot→RayQuotient.Characters rayM Hr)
    (w σ v : Slot→ℝ) (tOld t₁ t₂ height : ℝ)
    (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i/V ≤ mesh)
    (hσlo : ∀ i,(33/50:ℝ) ≤ σ i) (hσhi : ∀ i,σ i ≤ (33/50:ℝ))
    (hh : 0 ≤ height) (hv : ∀ i,|v i| ≤ height)
    (hretain : (∑ i∈F,w i) ≤ V*l) (hU : 1 ≤ U) (hV : 0 < V)
    (hC : 0 ≤ C) (hCslot : 0 ≤ Cslot) (he : 0 ≤ e)
    (hwidth : (∑ i,w i) ≤ L)
    (hdelete : (∑ i∈Finset.univ\F,w i) ≤ max 0 ((∑ i,w i)-V*l+rounding))
    (hprice : e*max 0 (L-V*l+rounding) < (u:ℝ)-(rho:ℝ)/2+allowance)
    (herr : buffer*((Finset.univ\F).card:ℝ)+V*ε ≤ (rho:ℝ)/4)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hXN : length (U^V) X₁ ≤ N) (hXY : length (U^V) X₂ ≤ Y)
    (s : Finset FreeRow) (hQM : Q ≤ rayM)
    (hk : ∀ u∈s,initialKeep η (internalQ Q base) u.val) (hy : ∀ u∈s,rowNorm u ≤ U^V)
    (hlow : ∀ u∈s,∀ i∈Finset.univ\F,
      ‖originalMark rayM Hr hHr η base θ W U w σ v tOld i u‖^2 ≤ (Cslot*U^buffer)*U^(e*w i)) :
    finiteEnergy s (witnessBase rayM Hr hHr η base j₁) (witnessBase rayM Hr hHr η base j₂)
      (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ (originalMark rayM Hr hHr η base θ W U w σ v tOld) ≤
      Cslot^(Finset.univ\F).card*(C*QuadraticInitialBound.diagonalControl radialMajorant*
        (p.control controls)^2*(1+|t₁|+|t₂|+(|tOld|+|t₁|+|t₂|+height))^degree)*
        U^(V+(u:ℝ)-(rho:ℝ)/4+allowance) := by
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
  apply low_pair_paid rayM Hr hHr hsrc F θ θ w σ σ (fun i=>tOld+v i-t₁)
    (fun i=>tOld+v i-t₂) t₁ t₂ (|tOld|+|t₁|+|t₂|+height) hw hwm hσlo hσhi hσlo hσhi
    (by positivity) hv₁ hv₂ hretain hU hV hC hCslot he hwidth hdelete hprice herr
    p X₁ X₂ hX₁ hX₂ hXN hXY s _
    (fun u hu=>(witness_initialKeep rayM Hr hHr Q hQM η base j₁ u).mpr (hk u hu))
    (fun u hu=>(witness_initialKeep rayM Hr hHr Q hQM η base j₂ u).mpr (hk u hu)) hy
  · intro u hu i hi
    exact (witness_original_mark_norm rayM Hr hHr η base j₁ (θ i)
      (fixedBadMask*idealGenerator 1) 1 u.val (originalPools rayM Hr 2 U w i) W
      (U^(w i)) (σ i) tOld t₁ (v i) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)).symm
  · intro u hu i hi
    exact (witness_original_mark_norm rayM Hr hHr η base j₂ (θ i)
      (fixedBadMask*idealGenerator 1) 1 u.val (originalPools rayM Hr 2 U w i) W
      (U^(w i)) (σ i) tOld t₂ (v i) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)).symm
  · exact hlow

#print axioms witness_low_pair_paid
end
end QRH.Cycle092.StrongPair
