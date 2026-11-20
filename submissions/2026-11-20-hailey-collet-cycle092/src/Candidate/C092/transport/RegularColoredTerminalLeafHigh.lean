/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairHighZeroDegreeP2
import Candidate.C092.transport.RegularColoredTerminalLeafGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
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
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

open QRH.Cycle092.StrongPair
open QRH.Record12518109Source QRH.Record12518109Existence

open CenteredMomentEnergyState Qrh.JointDetector

theorem terminal_high_selected_rows {n y : ℝ}
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn1 : n ≤ sourceRatio*y)
    (amax : ℝ) (ha : 1 ≤ amax) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ (W : ℝ→ℂ),Continuous W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ buffer Cslot : ℝ,0 < buffer → 0 < Cslot →
    ∀ old base : Character,
    ∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ V : ℝ,(98/100:ℝ) ≤ V → V ≤ amax →
    ∀ (J : Finset Slot) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
      (tOld t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ) ≤ σ i) → (∀ i,σ i ≤ (33/50:ℝ)) →
      0 ≤ height → (∑ i∈J,w i) ≤ sourceWidth n y →
    ∀ (η₁ η₂ : Character) (Q₁ Q₂ : Ideal O),
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ (s : Finset FreeRow),
      (∀ z∈s,initialKeep η₁ Q₁ z.val) → (∀ z∈s,initialKeep η₂ Q₂ z.val) →
      (∀ z∈s,rowNorm z ≤ U^V) →
      finiteEnergyOn J (s.filter (fun z=>(5002/10000:ℝ) < LowActual.originalResponse old (fixedBadMask*idealGenerator 1) 1
        tOld U (Cslot*U^buffer) (fun i:J=>w i.val)
        (originalPools rayM Hr 2 U (fun i:J=>w i.val))
        (originalCoefficients rayM Hr hHr base (fun i:J=>θ i.val) W U
          (fun i:J=>w i.val) (fun i:J=>σ i.val) (fun i:J=>v i.val))
        (fun i:J=>U^(w i.val)) z.val)) η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
        (originalMark rayM Hr hHr old base θ W U w σ v tOld) ≤
        C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control {(0,0)})^2*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  obtain ⟨mesh,hm,hsource⟩ := high_selected_pair_p2_zero_degree hy0 hy1 hn1 amax ha
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ W hW hWs buffer Cslot hb hCslot old base
  obtain ⟨C,hC,hsource⟩ := hsource Slot W hW hWs buffer Cslot hb hCslot old base
  refine ⟨C,hC,?_⟩
  filter_upwards [hsource] with U hsource
  intro rayM _ Hr hHr V hV0 hV1 J θ w σ v tOld t₁ t₂ height hw hwm hσlo hσhi hh hwidth
    η₁ η₂ Q₁ Q₂ p X₁ X₂ hX₁ hX₂ hXN hXY rows hk₁ hk₂ hy
  exact hsource rayM Hr hHr V hV0 hV1 J θ w σ v tOld t₁ t₂ height hw hwm hσlo hσhi hh hwidth
    η₁ η₂ Q₁ Q₂ p X₁ X₂ hX₁ hX₂ hXN hXY _
    (fun u hu=>hk₁ u (Finset.mem_filter.mp hu).1)
    (fun u hu=>hk₂ u (Finset.mem_filter.mp hu).1)
    (fun u hu=>hy u (Finset.mem_filter.mp hu).1)
    (fun u hu=>(Finset.mem_filter.mp hu).2)

#print axioms terminal_high_selected_rows
end
end QRH.Cycle092.RegularColoredForward
