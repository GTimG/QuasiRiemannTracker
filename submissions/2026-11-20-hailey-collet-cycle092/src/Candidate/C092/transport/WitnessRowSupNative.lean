/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal PairAt specialization consumed by the proved rectangular supremum. -/
import Candidate.C092.transport.WitnessRowSupPair

set_option autoImplicit false
namespace QRH.Cycle092.WitnessRowSup
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O

/-- Freeze every arithmetic mark and the long height. The witness's common
height is zero because its entire relative pitch is in the interpolated
fixed profile, whose polynomial controls were proved in WitnessRowSupPair.
This is the exact native PairAt conclusion, not an extra energy assumption. -/
theorem pairAt_fixed_height {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    {N Y l bΦ mesh ε Z C : ℝ} {W : ℝ→ℂ}
    {ηL ηS η₀L η₀S : Character} {QL QS : Ideal O}
    {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hpair : PairAt (Slot:=Slot) M H hH N Y l W bΦ mesh ε Z
      ηL ηS η₀L η₀S QL QS degree controls C)
    (Tslots : Finset Slot) (θL θS : Slot→RayQuotient.Characters M H)
    (w σL σS vL vS : Slot→ℝ) (tL height XL XS : ℝ)
    (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i ≤ mesh)
    (hσLlo : ∀ i,(33/50:ℝ) ≤ σL i) (hσLhi : ∀ i,σL i ≤ (33/50:ℝ))
    (hσSlo : ∀ i,(33/50:ℝ) ≤ σS i) (hσShi : ∀ i,σS i ≤ (33/50:ℝ))
    (hh : 0 ≤ height) (hvL : ∀ i,|vL i| ≤ height) (hvS : ∀ i,|vS i| ≤ height)
    (hsum : (∑ i∈Tslots,w i) ≤ l) (hXL : 0 < XL) (hXS : 0 < XS)
    (hXN : length Z XL ≤ N) (hXY : length Z XS ≤ Y)
    (rows : Finset FreeRow) (mark : Slot→FreeRow→ℂ)
    (hkL : ∀ u∈rows,initialKeep ηL (internalQ QL η₀L) u.val)
    (hkS : ∀ u∈rows,initialKeep ηS (internalQ QS η₀S) u.val)
    (hy : ∀ u∈rows,rowNorm u ≤ Z)
    (hmL : ∀ u∈rows,∀ i∈Tslots,‖mark i u‖=
      ‖normalizedSlot ηL (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools M H 2 Z w i)
        (originalCoefficients M H hH η₀L θL W Z w σL vL i) tL (Z^(w i))‖)
    (hmS : ∀ u∈rows,∀ i∈Tslots,‖mark i u‖=
      ‖normalizedSlot ηS (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools M H 2 Z w i)
        (originalCoefficients M H hH η₀S θS W Z w σS vS i) 0 (Z^(w i))‖) :
    ∀ p : Profiles (1/4) (9/4),
      finiteEnergyOn Tslots rows ηL ηS (p.profile 0) (p.profile 1) tL 0 XL XS mark ≤
        (C*QuadraticInitialBound.diagonalControl radialMajorant*
          (1+|tL|+height)^degree*Z^(1+ε))*(p.control controls)^2 := by
  intro p
  have h := hpair Tslots θL θS w σL σS vL vS tL 0 height hw hwm hσLlo hσLhi hσSlo hσShi
    hh hvL hvS hsum p XL XS hXL hXS hXN hXY rows mark hkL hkS hy hmL hmS
  simpa only [abs_zero,add_zero,mul_assoc,mul_left_comm,mul_comm] using h

/-- Apply original_pair_rowwise to this profile for the normalized first
relative norm-log test. Its compact support and smoothness are proved here;
its second derivative chain uses the original log tests through order three. -/
theorem first_log_profile_data (W : ℝ→ℂ)
    (hs : Function.support W ⊆ Icc (1/4:ℝ) (9/4)) (hW : ContDiff ℝ ∞ W) :
    Function.support (HeckeDetectorRowwisePolynomial.logProfile W) ⊆ Icc (1/4:ℝ) (9/4) ∧
      ContDiff ℝ ∞ (HeckeDetectorRowwisePolynomial.logProfile W) :=
  ⟨(HeckeDetectorRowwisePolynomial.logProfile_support W).trans hs,
    HeckeDetectorRowwisePolynomial.logProfile_smooth W (1/4) (9/4) (by norm_num) hs hW⟩

#print axioms pairAt_fixed_height
#print axioms first_log_profile_data
end
end QRH.Cycle092.WitnessRowSup
