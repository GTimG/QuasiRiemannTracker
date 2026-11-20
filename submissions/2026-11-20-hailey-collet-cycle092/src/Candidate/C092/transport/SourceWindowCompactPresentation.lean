/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Construct the whole native physical-mark presentation required by the middle
return. Only actual row keeps and elementary prime-size gates remain inputs;
the two normalized-mark identities are proved from the native dictionary. -/
import Candidate.C092.transport.SourceWindowCompactMarks
set_option autoImplicit false
namespace QRH.Cycle092.SourceWindowCompact
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyBands
open CenteredMomentDetectorPlainFiberSource
open HeckeDetectorRawFiber HeckeDetectorPhysicalSelection
open QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
open QRH.Cycle092.MixedPacketScale QRH.Cycle092.MixedMiddleReturn
local notation "O" => ActualEisensteinCubic.O

/-- The seed selects no marks yet. WholePresentation.select subsequently
inserts the genuine saturated complementary main subproduct, preserving this
PairAt and the fixed source metadata. All original physical marks are already
presented at BOTH independent anchors, with their actual z heights. -/
def wholePresentation_of_native {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    {Label : Type} {U a eps cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a eps cutoff T allowance i) (etaW : Character)
    (controls : Finset (ℕ×ℕ))
    (N Y quota bPhi mesh epsilon C : ℝ) (degree : ℕ) (V : ℝ→ℂ)
    (QL QW : Ideal O)
    (hsource : PairAt (Slot:=Slot) M H hH N Y quota (fun x=>star (V x))
      bPhi mesh epsilon U (fixedSourcePrincipal S hS) etaW
      (fixedSourcePrincipal S hS) etaW QL QW degree controls C)
    (hU : 0 < U) (hquota : 0≤quota) (hmesh : 0 ≤ mesh) (hFmesh : F.mesh ≤ mesh)
    (hM : M≤Ideal.span {fixedBadMask})
    (hVs : Function.support V⊆Set.Icc (1:ℝ) 2)
    (hprofile : ∀s∈F.slots,F.profile s=V)
    (hupper : ∀s∈F.slots,F.upper s=2)
    (hreal : ∀s∈F.slots,(F.external s).re=17/50)
    (height : ℝ) (hh : 0≤height) (him : ∀s∈F.slots,|(F.external s).im|≤height)
    (hlargeL : ∀s∈F.slots,((fixedSourcePrincipal S hS).modulus.absNorm:ℝ)<U^(F.widths s))
    (hlargeW : ∀s∈F.slots,(etaW.modulus.absNorm:ℝ)<U^(F.widths s))
    (hkeepL : ∀u∈F.rows,initialKeep (fixedSourcePrincipal S hS)
      (internalQ QL (fixedSourcePrincipal S hS)) u.val)
    (hkeepW : ∀u∈F.rows,initialKeep etaW (internalQ QW etaW) u.val) :
    WholePresentation M H hH S hS F etaW controls := by
  let w := fun s=>if s∈F.slots then F.widths s else 0
  let pitch := fun s=>if s∈F.slots then -(F.external s).im else 0
  let theta : Slot→RayQuotient.Characters M H := fun _=>1
  let mark := fun s u=>physical M H (fun v : FreeRow=>v.val)
    F.profile F.upper F.widths F.external U u s
  have hmark (eta : Character)
      (hlarge : ∀s∈F.slots,(eta.modulus.absNorm:ℝ)<U^(F.widths s)) :
      ∀u∈F.rows,∀s∈F.slots,‖mark s u‖=
        ‖normalizedSlot eta (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M H 2 U w s)
          (originalCoefficients M H hH eta theta (fun x=>star (V x)) U w
            (fun _=>33/50) pitch s) 0 (U^(w s))‖ := by
    intro u hu s hs
    have hp := canonical_mark_norm M H hH eta hM theta V hVs U F.widths F.external
      u s hU (hreal s hs) (hlarge s hs)
    dsimp only [mark,physical]
    rw [hprofile s hs,hupper s hs]
    have hc : originalCoefficients M H hH eta theta (fun x=>star (V x)) U F.widths
        (fun _=>33/50) (fun k=>-(F.external k).im) s =
        originalCoefficients M H hH eta theta (fun x=>star (V x)) U w
          (fun _=>33/50) pitch s := by
      funext I
      simp only [QRH.Cycle092.WholeSlot.originalCoefficients,w,pitch,ite_eq_left hs]
    rw [hc] at hp
    simpa only [originalPools,w,ite_eq_left hs] using hp
  refine {
    seed := {
      N:=N, Y:=Y, l:=quota, bΦ:=bPhi, mesh:=mesh, epsilon:=epsilon, C:=C,
      W:=(fun x=>star (V x)), η₀L:=fixedSourcePrincipal S hS, η₀W:=etaW,
      QL:=QL, QW:=QW, degree:=degree, pair:=hsource,
      selected:=∅, mark:=mark, thetaL:=theta, thetaW:=theta, w:=w,
      sigmaL:=(fun _=>33/50), sigmaW:=(fun _=>33/50), vL:=pitch, vW:=pitch,
      height:=height,
      hw:=?_, hwm:=?_, hsigmaL:=(fun _=>rfl), hsigmaW:=(fun _=>rfl),
      height_nonneg:=hh, hvL:=?_, hvW:=?_, hsum:=?_, keepL:=hkeepL, keepW:=hkeepW,
      markL:=(fun _ _ _ hs=>False.elim (Finset.notMem_empty _ hs)),
      markW:=(fun _ _ _ hs=>False.elim (Finset.notMem_empty _ hs)) },
    widths:=?_, mark:=(fun _ _ _ _=>rfl), markL:=hmark _ hlargeL, markW:=hmark _ hlargeW }
  · intro s
    dsimp [w]
    split_ifs with hs
    · exact (F.widths_pos s hs).le
    · exact le_rfl
  · intro s
    dsimp [w]
    split_ifs with hs
    · exact (F.widths_mesh s hs).trans hFmesh
    · exact hmesh
  · intro s
    dsimp [pitch]
    split_ifs with hs
    · simpa only [abs_neg] using him s hs
    · simpa only [abs_zero] using hh
  · intro s
    dsimp [pitch]
    split_ifs with hs
    · simpa only [abs_neg] using him s hs
    · simpa only [abs_zero] using hh
  · simpa only [Finset.sum_empty] using hquota
  · intro s hs
    exact if_pos hs

end
end QRH.Cycle092.SourceWindowCompact
#print axioms QRH.Cycle092.SourceWindowCompact.wholePresentation_of_native
