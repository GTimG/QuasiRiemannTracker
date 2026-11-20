/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early-mesh native centered source reduction to actual averaged physical
children. No recurrence, source energy or arbitrary-height price is assumed. -/
import Candidate.C092.transport.OrderedPairActualRestoredUniform
import Candidate.C092.transport.FirstStageModulus
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
open QRH.Cycle092.FixedRayPair
open QRH.Cycle090
local notation "O"=>HeckeFamily.O

/-- The physical supplier receives every positivity, properness and native
base/color presentation guard for the exact fixed original classifier. -/
def NativeAveragedStageSupply (N Y l mesh ε cRad ξ κ loss ξsecond:ℝ)
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
    let base:=η₀₁.product η₁.inverse
    let q:=stageQ Q₁ η₀₁ base η₁ η₂
    q≠0 → q≠⊤ → q ≤ rayM → q ≤ Ideal.span {(72:O)} → q ≤ base.modulus →
    q ≤ η₁.modulus → q ≤ η₂.modulus → internalQ q base=q →
    internalQ q (base.product η₁)=q → internalQ q (base.product η₂)=q →
    ∃ J degree : ℕ, ∃ controls : Finset (ℕ×ℕ), (0,0)∈controls ∧
    ∀ Cz Ct : RepairedSourceSideSupply.RootShape Slot→ℝ, (∀k,0<Cz k ∧ 0<Ct k) →
    ∀ᶠZ:ℝ in atTop, ∀hZ:1<Z,
      CenteredAveragedAt rayM Hr hHr N Y l W hW.continuous hWs bΦ mesh ε Z hZ hmesh
        η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls J cRad ξ κ loss ξsecond Cz Ct q

/-- All native classifier guards follow from the original proper keep.
The second split never replaces or narrows that original row restriction. -/
theorem averaged_stage_of_native_modulus (N Y l mesh ε cRad ξ κ loss ξsecond:ℝ)
    (hmesh:mesh ≤ 1/6)
    (supply:NativeAveragedStageSupply N Y l mesh ε cRad ξ κ loss ξsecond hmesh) :
    AveragedStageSupply N Y l mesh ε cRad ξ κ loss ξsecond hmesh := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  let base:=η₀₁.product η₁.inverse
  let q:=stageQ Q₁ η₀₁ base η₁ η₂
  have hg:=stageQ_admissible rayM Q₁ η₀₁ base η₁ η₂ hQ₁ray hQ₁0 hQ₁top hQ₁72
  obtain ⟨J,degree,controls,h00,hprice⟩:=supply Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1
    hg.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.2
  exact ⟨J,degree,controls,h00,fun Cz Ct hc=>⟨q,hprice Cz Ct hc⟩⟩

/-- Actual early-mesh CenteredUniformBox from prices on the one original
native Q classifier and the literal restored children. -/
theorem centered_uniform_of_native_averaged (N Y l:ℝ)
    (hy0:sourceY0 ≤ Y)(hy1:Y ≤ sourceY)(hn:N ≤ sourceRatio*Y)(hl:l<sourceWidth N Y)
    (supply:∀ε:ℝ,0<ε → ∃mesh cRad ξ κ ξsecond εmass loss:ℝ,
      0 < mesh ∧ ∃hmesh:mesh ≤ 1/6,
        1 ≤ cRad ∧ 0<ξ ∧ 0<κ ∧ 0<ξsecond ∧ ξ/2+κ ≤ 22 ∧ 0<εmass ∧ loss+εmass ≤ ε/2 ∧
        NativeAveragedStageSupply N Y l mesh ε cRad ξ κ loss ξsecond hmesh) :
    CenteredUniformBox N Y l := by
  apply centered_uniform_of_averaged_stage N Y l hy0 hy1 hn hl
  intro ε hε
  obtain ⟨mesh,cRad,ξ,κ,ξsecond,εmass,loss,hm,hmesh,hcRad,hξ,hκ,hξsecond,hsmall,hεmass,hloss,hprice⟩:=supply ε hε
  exact ⟨mesh,cRad,ξ,κ,ξsecond,εmass,loss,hm,hmesh,hcRad,hξ,hκ,hξsecond,hsmall,hεmass,hloss,
    averaged_stage_of_native_modulus N Y l mesh ε cRad ξ κ loss ξsecond hmesh hprice⟩

#print axioms averaged_stage_of_native_modulus
#print axioms centered_uniform_of_native_averaged
end
end QRH.Cycle092.OrderedPairActualRestored
