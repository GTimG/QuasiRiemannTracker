/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One real scale horizon controls all actual first allocations and whole-slot
selections, including zero remaining slots, before their native labels. -/
import Candidate.C092.transport.ActualStageFrameBudgetSelect
import Candidate.C092.transport.ActualRootFrameHitAll
import Candidate.C092.transport.RawSidesZeroTailGeometry
import Candidate.C092.transport.ActualFrameFeeGates
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentEnergyBands
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock MixedOriginalNormCap
open QRH.SilDensitySplit.CubeFree.Second.Provider QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.NativeStrip QRH.Cycle090 QRH.Cycle092.FixedFramePacking
local notation "Id"=>Ideal HeckeFamily.O
local instance (priority := 2000) scaleSubtypeDecEq {κ:Type*}{p:κ→Prop} : DecidableEq (Subtype p):=Classical.decEq _

/-- Every cap here belongs to the original actual source or its literal
allocated residual. Constants depend only on the early cardinality bound. -/
theorem eventual_actual_scales (N:ℕ)(δ ξ mesh:ℝ)(hδ:0 < δ)(hsep:ξ/2 < mesh) :
    ∀ᶠZ:ℝ in atTop,1 < Z ∧ 4096  ≤  Z ∧ Real.logb Z 2  ≤  δ ∧
      (∀j  ≤  N,Real.logb Z (64*((2:ℝ)^j)^4)  ≤  δ ∧ Real.logb Z ((2:ℝ)^j)  ≤  δ) ∧
    ∀(ι:Type)[Fintype ι](s:Source ι (1/4) (9/4)),Fintype.card ι  ≤  N →
    ∀(cover:OriginalEnclosure s)(w:ι→ℝ),(∀i,0  ≤  w i) → (∀i,s.P i=Z^(w i)) →
    ∀n y:ℝ,sourceY0  ≤  y → y  ≤  sourceY → n  ≤  sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑i,w i) →
      sourceVolume s  <  Z ∧ sourceVolume s  ≤  Z^(9179599/10000000:ℝ) ∧
      ∀(G:Id)(B:actualAllocations (tuplePools s) G)(Js:Finset (liveIndices B.val)),
      (∑j∈Js,w j.val)  ≤  3/5000 →
      let ws:=QRH.Cycle092.RawSides.selectionScaleQ s (by norm_num) cover G B Js
      let rest:=restOf s (by norm_num) cover G B Js
      let xcap:=QRH.Cycle092.RawSides.residualCapQ rest
      1  ≤  ws ∧ ws  ≤  Z^(1/1000:ℝ) ∧ 1  ≤  xcap ∧ xcap  ≤  Z^(919/1000:ℝ) ∧
        32*((9/4:ℝ)^2*(2:ℝ)^Fintype.card (Rest Js))^2*Z^(ξ/2)  ≤  Z^mesh := by
  filter_upwards [QRH.Cycle092.RawSides.allocated_residual_caps_Q N,
    QRH.Cycle092.RawSides.selected_width_Q N,early_constants N δ hδ,
    QRH.Cycle092.ActualRootFrameHit.actual_cutoff_fee N ξ mesh hsep,
    eventually_ge_atTop (4096:ℝ)] with Z hc hw he hcut hlarge
  refine ⟨hc.1,hlarge,he.2.1,he.2.2,?_⟩
  intro ι inst s hN cover w hw0 hP n y hy0 hy1 hn hbox
  have hcaps:=hc.2 ι s hN cover w hP n y hy0 hy1 hn hbox
  refine ⟨hcaps.1,QRH.Cycle092.RawSides.root_volume_of_box s w hP hc.1 hy0 hy1 hn hbox,?_⟩
  intro G B Js hsum ws rest xcap
  have hnLive:Fintype.card (liveIndices B.val)  ≤  N:=
    (Fintype.card_le_of_injective (fun j:liveIndices B.val=>j.val) Subtype.val_injective).trans hN
  have hwidth:=hw.2 (liveIndices B.val) (fun j=>w j.val) hnLive (fun j=>hw0 j.val) Js hsum
  have hscale:ws=(∏j∈Js,2*Z^(w j.val)):=by
    change (∏j∈Js,2*s.P j.val)=_
    simp only [hP]
  refine ⟨hscale.symm ▸ hwidth.1,hscale.symm ▸ hwidth.2,le_max_left _ _,?_,hcut.2 ι s hN cover G B Js⟩
  exact max_le (Real.one_le_rpow hc.1.le (by norm_num)) (hcaps.2 G B Js)

#print axioms eventual_actual_scales
end
end QRH.Cycle092.ActualStageFrameBudget
