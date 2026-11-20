/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Componentwise actual-scale shortening of the earlier ordinary pair source.
Both ordinary scales, profiles, pitches, rows and prime marks remain literal.
Native source definitions and their attribution remain in the imports. -/
import Candidate.C092.transport.StrongPairSource
set_option autoImplicit false
namespace QRH.Cycle092.SourceWindowCompact
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyBands
open CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.StrongPair
local notation "O" => ActualEisensteinCubic.O

/-- Independent live ordinary caps and the selected whole-mark quota may all
shrink. This uses inequalities on the SAME X1 and X2, not an identification
or rescaling of the two actual ordinary factors. -/
theorem pairAt_componentwise_shorter {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    {N Y quota n y live bPhi mesh epsilon Z C : ℝ} {W : ℝ→ℂ}
    {eta1 eta2 base1 base2 : Character} {Q1 Q2 : Ideal O}
    {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hn : n≤N) (hy : y≤Y) (hl : live≤quota)
    (hsource : PairAt (Slot:=Slot) M H hH N Y quota W bPhi mesh epsilon Z
      eta1 eta2 base1 base2 Q1 Q2 degree controls C) :
    PairAt (Slot:=Slot) M H hH n y live W bPhi mesh epsilon Z
      eta1 eta2 base1 base2 Q1 Q2 degree controls C := by
  intro T theta1 theta2 w sigma1 sigma2 v1 v2 t1 t2 height hw hwm hs1lo hs1hi
    hs2lo hs2hi hh hv1 hv2 hsum p X1 X2 hX1 hX2 hXN hXY
  exact hsource T theta1 theta2 w sigma1 sigma2 v1 v2 t1 t2 height hw hwm hs1lo hs1hi
    hs2lo hs2hi hh hv1 hv2 (hsum.trans hl) p X1 X2 hX1 hX2
    (hXN.trans hn) (hXY.trans hy)

end
end QRH.Cycle092.SourceWindowCompact
#print axioms QRH.Cycle092.SourceWindowCompact.pairAt_componentwise_shorter
