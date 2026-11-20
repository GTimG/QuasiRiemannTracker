/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early-mesh native centered source reduction to actual averaged physical
children. No recurrence, source energy or arbitrary-height price is assumed. -/
import Candidate.C092.transport.OrderedPairActualRestoredStage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairActualRestored
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentLattice
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyBands
open QRH.SilDensitySplit.CubeFree.FP
open QRH.Cycle092.CofactorOrdinary
open QRH.Cycle092.NativeStrip QRH.Cycle092.WholeSlot
open QRH.Cycle092.OrderedPairPhase QRH.Cycle092.ReferenceShortP3
open QRH.Cycle090
local notation "O"=>HeckeFamily.O

/-- The degree and controls are chosen before the finite source fees; the
single concrete original Q presentation then precedes all live scales. -/
def AveragedStageSupply (N Y l mesh ε cRad ξ κ loss ξsecond:ℝ)
    (hmesh:mesh ≤ 1/6) : Prop :=
  ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
  ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM  ≤  Hr),
  ∀ W : ℝ→ℂ, ∀hW:ContDiff ℝ ∞ W, ∀hWs:Function.support W⊆Set.Icc (1:ℝ) 2,
  ∀ bΦ : ℝ, 2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
  ∀ (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O),
    Q₁ ≤ rayM → internalQ Q₁ η₀₁ ≠ 0 → internalQ Q₁ η₀₁ ≠ ⊤ →
    internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)} →
    Q₂ ≤ rayM → internalQ Q₂ η₀₂ ≠ 0 → internalQ Q₂ η₀₂ ≠ ⊤ →
    internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)} →
    ∃ J degree : ℕ, ∃ controls : Finset (ℕ×ℕ), (0,0)∈controls ∧
    ∀ Cz Ct : RepairedSourceSideSupply.RootShape Slot→ℝ, (∀k,0<Cz k ∧ 0<Ct k) →
    ∃Qprice:Ideal O, ∀ᶠZ:ℝ in atTop, ∀hZ:1<Z,
      CenteredAveragedAt rayM Hr hHr N Y l W hW.continuous hWs bΦ mesh ε Z hZ hmesh
        η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls J cRad ξ κ loss ξsecond Cz Ct Qprice


/-- Closing the actual native invariant from its literal physical prices. -/
theorem centered_unit_of_averaged_stage (N Y l mesh ε:ℝ)
    (hy0:sourceY0 ≤ Y)(hy1:Y ≤ sourceY)(hn:N ≤ sourceRatio*Y)
    (hl:l ≤ sourceWidth N Y)(hmesh:mesh ≤ 1/6)(hε:0<ε)
    (cRad ξ κ ξsecond εmass loss:ℝ)(hcRad:1 ≤ cRad)(hξ:0<ξ)(hκ:0<κ)
    (hξsecond:0<ξsecond)(hsmall:ξ/2+κ ≤ 22)(hεmass:0<εmass)(hloss:loss+εmass ≤ ε/2)
    (supply:AveragedStageSupply N Y l mesh ε cRad ξ κ loss ξsecond hmesh) :
    CenteredUnitBox N Y l mesh ε := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨J,degree,controls,h00,hprice⟩:=supply Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨C,Cz,Ct,hC,hconstants,hbound⟩:=centered_at_of_averaged (Slot:=Slot) rayM Hr hHr
    N Y l mesh ε hy0 hy1 hn hl hmesh hε J degree W hW.continuous hWs controls h00
    cRad ξ κ ξsecond εmass loss hcRad hξ hκ hξsecond hsmall hεmass hloss
  obtain ⟨Qprice,hphysical⟩:=hprice Cz Ct hconstants
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hbound,hphysical] with Z hb hp
  exact hb.2 hb.1 bΦ η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ Qprice (hp hb.1)

theorem centered_unit_mono_mesh {N Y l mesh₀ mesh ε:ℝ}
    (hmesh:mesh ≤ mesh₀)(hsource:CenteredUnitBox N Y l mesh₀ ε) :
    CenteredUnitBox N Y l mesh ε := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨degree,controls,C,hC,hbound⟩:=hsource Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hbound] with Z hb
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm
  exact hb T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw (fun i=>(hwm i).trans hmesh)

/-- The final mesh is chosen before Slot, ray data, profiles and arithmetic,
inside both the genuine physical bank and the live open-width margin. -/
theorem centered_uniform_of_averaged_stage (N Y l:ℝ)
    (hy0:sourceY0 ≤ Y)(hy1:Y ≤ sourceY)(hn:N ≤ sourceRatio*Y)(hl:l<sourceWidth N Y)
    (supply:∀ε:ℝ,0<ε → ∃mesh cRad ξ κ ξsecond εmass loss:ℝ,
      0 < mesh ∧ ∃hmesh:mesh ≤ 1/6,
        1 ≤ cRad ∧ 0<ξ ∧ 0<κ ∧ 0<ξsecond ∧ ξ/2+κ ≤ 22 ∧ 0<εmass ∧ loss+εmass ≤ ε/2 ∧
        AveragedStageSupply N Y l mesh ε cRad ξ κ loss ξsecond hmesh) :
    CenteredUniformBox N Y l := by
  intro ε hε
  obtain ⟨mesh₀,cRad,ξ,κ,ξsecond,εmass,loss,hm₀,hmesh₀,hcRad,hξ,hκ,hξsecond,hsmall,hεmass,hloss,hprice⟩:=supply ε hε
  have hsource:=centered_unit_of_averaged_stage N Y l mesh₀ ε hy0 hy1 hn hl.le hmesh₀ hε
    cRad ξ κ ξsecond εmass loss hcRad hξ hκ hξsecond hsmall hεmass hloss hprice
  let mesh:=min mesh₀ ((sourceWidth N Y-l)/4)
  have hm:0 < mesh:=lt_min hm₀ (by linarith)
  exact ⟨mesh,hm,centered_unit_mono_mesh (min_le_left _ _) hsource⟩

#print axioms centered_unit_of_averaged_stage
#print axioms centered_unit_mono_mesh
#print axioms centered_uniform_of_averaged_stage
end
end QRH.Cycle092.OrderedPairActualRestored
