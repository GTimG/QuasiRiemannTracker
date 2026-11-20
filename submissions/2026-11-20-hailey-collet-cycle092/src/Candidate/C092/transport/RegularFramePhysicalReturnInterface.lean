/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The sole analytic inlet for the regular physical-frame consumer: the genuine
all-response P2 estimate at the original ordered pair, at every radial core.
The reference-arm and bounded exceptional-slot payments are constructed later. -/
import Candidate.C092.transport.ReferenceArmRadialCollars
import Candidate.C092.transport.FixedBaseOriginal
import Candidate.C092.transport.FixedRayPairSupport
import Candidate.C092.transport.RegularColoredTerminalLeafGeometry
import Candidate.C092.transport.RegularColoredTerminalLeafEmpty
import Candidate.C092.transport.TerminalProfileUniformSup
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
local notation "O" => HeckeFamily.O

/-- All ordinary/mark heights remain live. Both coefficient colors, the
original mark, selected slots, finite rows and the exact ordered n,y are retained.
This proposition does not assert its own analytic proof. -/
def OrderedP2At (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
    (hHr : RayOrthogonality.globalUnits M≤ Hr)
    (W : ℝ→ℂ) (n y mesh U : ℝ)
    (old base omega1 omega2 : Character) (Q : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀ V : ℝ, 0≤ V → V≤2 →
  ∀ (T : Finset Slot) (theta : Slot→RayQuotient.Characters M Hr)
    (w sigma freq : Slot→ℝ) (tOld t1 t2 height : ℝ),
    (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,sigma i=33/50) →
    0≤ height → |tOld|≤ height → (∀i,|freq i|≤ height) →
    (∀i,|tOld+freq i-t1|≤ height) → (∀i,|tOld+freq i-t2|≤ height) →
    (∑i∈T,w i)≤ sourceWidth n y-(u:ℝ) →
  ∀ (p : Profiles (1/4) (9/4)) (X1 X2 : ℝ),0< X1 → 0< X2 →
    X1≤ U^n → X2≤ U^y →
  ∀ rows : Finset FreeRow,
    (∀z∈rows,initialKeep old (internalQ Q base) z.val) →
    (∀z∈rows,initialKeep (old.product omega1) (internalQ Q (base.product omega1)) z.val) →
    (∀z∈rows,initialKeep (old.product omega2) (internalQ Q (base.product omega2)) z.val) →
    (∀z∈rows,rowNorm z≤ U^V) →
    (∀z∈rows,∀i∈T,‖originalMark M Hr hHr old base theta W U w sigma freq tOld i z‖=
      ‖originalMark M Hr hHr (old.product omega1) (base.product omega1) theta W U w sigma
        (fun i=> tOld+freq i-t1) t1 i z‖) →
    (∀z∈rows,∀i∈T,‖originalMark M Hr hHr old base theta W U w sigma freq tOld i z‖=
      ‖originalMark M Hr hHr (old.product omega2) (base.product omega2) theta W U w sigma
        (fun i=> tOld+freq i-t2) t2 i z‖) →
    finiteEnergyOn T rows (old.product omega1) (old.product omega2)
      (p.profile 0) (p.profile 1) t1 t2 X1 X2 (originalMark M Hr hHr old base theta W U w sigma freq tOld)≤
      C*(p.control controls)^2*(1+|t1|+|t2|+height)^degree*U^(terminalFramePrice V)

/-- Reindexing a genuine later subset does not identify it with an exhausted
original prefix. In particular this equality remains valid for T=empty. -/
theorem finiteEnergyOn_subtype {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (A : Finset Slot) (T : Finset A) (rows : Finset FreeRow)
    (eta1 eta2 : Character) (W1 W2 : ℝ→ℂ) (t1 t2 X1 X2 : ℝ) (mark : Slot→FreeRow→ℂ) :
    finiteEnergyOn T rows eta1 eta2 W1 W2 t1 t2 X1 X2 (fun i=> mark i.val)=
      finiteEnergyOn (T.map (Function.Embedding.subtype (fun i=> i∈A))) rows
        eta1 eta2 W1 W2 t1 t2 X1 X2 mark := by
  unfold finiteEnergyOn
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.prod_map]
  rfl

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.finiteEnergyOn_subtype
