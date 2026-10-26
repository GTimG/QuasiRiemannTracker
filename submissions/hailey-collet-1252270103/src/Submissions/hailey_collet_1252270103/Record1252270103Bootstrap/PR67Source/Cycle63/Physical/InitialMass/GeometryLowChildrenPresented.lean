import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoLowPresented
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The final daughters of the LOW children of a parent that is presented by an excluded natural row of the fixed
dictionary are presented by a predicate at their child multipliers: the presentation premise of the main LOW payment at
a parent whose children are run through a second step. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentNaturalRowSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion CenteredMomentCommonRadialData
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentEnergyState
open CenteredMomentAmplificationChildInput Cycle63FinalNatural Cycle63FinalLow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondCanonicalFrequency

set_option linter.unusedVariables false in
/-- For a parent `s` presented by the excluded natural row `F₀` of the dictionary `η₀` at the row `u₀ ≠ 0`, every final
daughter of a LOW child of `s`, at the retained state of a live second-stage row widened to any width, is presented by
`Presented` at its child multiplier, the multiplier of the prefix of the row with the unit of the dictionary, at the
height `Z^τT`. The presentation may use that the puncture of the child has norm at most `Z^Bchild`. -/
def GeometryLowChildrenPresented {α : Type} [Fintype α] [DecidableEq α] {Bmask : ℝ}
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) (τT : ℝ) (η₀ : Character) (u₀ : O)
    (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (Bchild : ℝ) : Prop :=
  u₀≠0 → ∀(reflected second : Bool)(s : Input α),ParentPresentation s.η F₀ R₀ →
    ∀(R seed : Ideal O)(Z Mrow amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1<Z)(bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q),
    let d := geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
    let src := geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
    ∀(B₂ : actualAllocations src.pools (if second then d.D else d.C))
      (r : secondLiveRows (fun _:Unit=>d.block))
      (hf₁ : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)
      (hf₂ : frozenCoefficient B₂.val (if second then d.D else d.C) d.R src.ν src.W src.P≠0)
      (χ : RayCharacter)(Q : Ideal O),
    let chain := geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂
    let g := geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂
      r hf₁ hf₂
    ∀(hP : chain.R₂*chain.E₂≠0)(hPN : ((chain.R₂*chain.E₂).absNorm:ℝ)≤Z^Bmask)
      (hPNc : ((chain.R₂*chain.E₂).absNorm:ℝ)≤Z^Bchild)(W' : ℝ)
      (hW' : (retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (chain.R₂*chain.E₂) hP hPN g.datum.radius
        g.datum.C g.datum.D g.datum.inactive).width≤W'),
    Presented η₀ Z (LowBranch.widenState (retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀)
        (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive) W' hW')
      (childMultiplier (!reflected) u₀ (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l : O))
        ⟨geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val,
          actualSecondArithmeticLabel _ _ _ _ _ _ _ n⟩) (Z^τT)

/-- The trivial predicate presents every final daughter. -/
theorem geometryLowChildrenPresented_true {α : Type} [Fintype α] [DecidableEq α] {Bmask : ℝ} (τT : ℝ)
    (η₀ : Character) (u₀ : O) (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (Bchild : ℝ) :
    GeometryLowChildrenPresented (α:=α) (Bmask:=Bmask) (fun _ _ _ _ _=>True) τT η₀ u₀ F₀ R₀ Bchild := by
  unfold GeometryLowChildrenPresented
  intros
  trivial

/-- The final daughters of the LOW children of a parent presented by an excluded natural row of the dictionary are
presented in the sense of `DepthTwoPresented` at the height `Z^τT`, and their punctures have norm at most `Z^Bchild`. -/
theorem geometryLowChildrenPresented_depthTwo {α : Type} [Fintype α] [DecidableEq α] {Bmask : ℝ} (τT : ℝ)
    (η₀ : Character) (u₀ : O) (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (Bchild : ℝ) :
    GeometryLowChildrenPresented (α:=α) (Bmask:=Bmask)
      (fun η Z s v T=>DepthTwoPresented τT η Z s v T ∧ (s.puncture.absNorm:ℝ)≤Z^Bchild) τT η₀ u₀ F₀ R₀ Bchild := by
  intro hu₀ reflected second s hη R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n d src B₂ r hf₁ hf₂ χ Q chain g
    hP hPN hPNc W' hW'
  exact ⟨depth_two_presented_low_child τT reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed Z Mrow amp ξ reserve b t N hZ
    bin q hw₁ hw₂ n B₂ r hf₁ hf₂ χ Bmask Q hP hPN W' hW',hPNc⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
