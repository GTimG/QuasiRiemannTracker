/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native earlier PairAt presentation before selecting a complete source-width
main subproduct. Every dictionary is on the original physical slots. -/
import Candidate.C092.transport.MixedPacketScaleSource
import Candidate.C092.transport.MixedMiddleReturnSelection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ConcretePrimeRowBridge CanonicalRowCompletion HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open HeckeDetectorRawFiber HeckeDetectorPhysicalSelection
open QRH.Cycle092.WholeSlot QRH.Cycle092.MixedPacketScale
local notation "O" => HeckeFamily.O

structure WholePresentation {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    {Label : Type} {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε cutoff T allowance i) (ηW : Character)
    (controls : Finset (ℕ×ℕ)) where
  seed : EarlierPair M H hH S hS F ηW controls
  widths : ∀s∈F.slots,seed.w s=F.widths s
  mark : ∀s∈F.slots,∀u∈F.rows,seed.mark s u=
    physical M H (fun v : FreeRow=>v.val) F.profile F.upper F.widths F.external U u s
  markL : ∀u∈F.rows,∀s∈F.slots,‖seed.mark s u‖=
    ‖normalizedSlot (fixedSourcePrincipal S hS) (fixedBadMask*idealGenerator 1) 1 u.val
      (originalPools M H 2 U seed.w s)
      (originalCoefficients M H hH seed.η₀L seed.thetaL seed.W U seed.w seed.sigmaL seed.vL s) 0 (U^(seed.w s))‖
  markW : ∀u∈F.rows,∀s∈F.slots,‖seed.mark s u‖=
    ‖normalizedSlot ηW (fixedBadMask*idealGenerator 1) 1 u.val
      (originalPools M H 2 U seed.w s)
      (originalCoefficients M H hH seed.η₀W seed.thetaW seed.W U seed.w seed.sigmaW seed.vW s) 0 (U^(seed.w s))‖

/-- Select a genuine earlier PairAt instance at the saturated whole-slot
quota. No new energy statement or amplitude estimate is a field. -/
def WholePresentation.select {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H} {S : Finset (Ideal O)} {hS : ∀P∈S,Prime P}
    {Label : Type} {U a ε cutoff T allowance : ℝ} {i : ℕ}
    {F : Fiber M H Label Slot U a ε cutoff T allowance i} {ηW : Character}
    {controls : Finset (ℕ×ℕ)} (P : WholePresentation M H hH S hS F ηW controls)
    (selected : Finset Slot) (hsub : selected⊆F.slots)
    (hlen : (∑s∈selected,F.widths s)≤P.seed.l) :
    EarlierPair M H hH S hS F ηW controls :=
  {P.seed with
    selected := selected
    hsum := by
      convert hlen using 1
      exact Finset.sum_congr rfl (fun s hs=>P.widths s (hsub hs))
    markL := fun u hu s hs=>P.markL u hu s (hsub hs)
    markW := fun u hu s hs=>P.markW u hu s (hsub hs)}

#print axioms WholePresentation.select
end
end QRH.Cycle092.MixedMiddleReturn
