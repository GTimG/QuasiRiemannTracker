/- A final daughter of a first-level LOW child is presented by its child multiplier in the four-ray dictionary, at the
retained state of its second-stage row. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryLowAdmission
import Candidate.Cycle63.Physical.InitialMass.GeometryDictionary
import Candidate.Cycle63.Physical.InitialMass.SecondEncodedGates
import Candidate.Cycle63.Physical.InitialMass.DepthTwoLowPresented
import Candidate.Research.RecursiveAffine.PrefixHighPhysicalWitness
import Candidate.Cycle63.Moment.DepthTwoCount
import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle153HighProvider
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic Cycle63InitialMass
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentNaturalRowSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion CenteredMomentCommonRadialData
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentEnergyState
open CenteredMomentAmplificationChildInput Cycle63FinalNatural Cycle63FinalLow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondCanonicalFrequency
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem prefix_presented_low_child {Base : Type} (base : Base → Character)
    (reflected second : Bool) (s : Input α) (R seed : Ideal O)
    (P : PrefixHighPresentation base s.η R)
(Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q) :
    let d := geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
    let src := geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
    ∀ (B₂ : actualAllocations src.pools (if second then d.D else d.C))
      (r : secondLiveRows (fun _:Unit=>d.block))
      (hf₁ : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)
      (hf₂ : frozenCoefficient B₂.val (if second then d.D else d.C) d.R src.ν src.W src.P≠0)
      (χ : RayCharacter) (Bmask : ℝ),
    let chain := geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂
    let g := geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂
      r hf₁ hf₂
    ∀ (hP : chain.R₂*chain.E₂≠0) (hPN : ((chain.R₂*chain.E₂).absNorm:ℝ)≤Z^Bmask),
    ∃ Next : PrefixHighPresentation (extendFixedDictionary base) (g.datum.τ χ) (chain.R₂*chain.E₂),
      Next.mult = childMultiplier (!reflected) P.mult (P.unit (!reflected))
        ⟨geometryFirstLabel s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val,
          actualSecondArithmeticLabel _ _ _ _ _ _ _ n⟩ := by
  intro d src B₂ r hf₁ hf₂ χ Bmask chain g hP hPN
  let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ 1 s.η)
    (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
  have hlocal := Cycle63InitialMass.depth_two_presented_low_child 1 reflected second s.η 1
    P.selfRow 1 one_ne_zero s P.self_parent_presentation R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
    B₂ r hf₁ hf₂ χ Bmask 1 hP hPN st.width (le_refl _)
  obtain ⟨localP,hvP⟩ := DepthTwoPresented.presentation hlocal
  have hRchild : R ∣ chain.R₂*chain.E₂ := by
    change R ∣ (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*_
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hRholes : R ∣ localP.χ₁.modulus*(chain.R₂*chain.E₂) := dvd_mul_of_dvd_right hRchild _
  have hchar : g.datum.τ χ = localP.τ₁ localP.j₁.2 := localP.hη
  let c : ChildPrefix :=
    ⟨geometryFirstLabel s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val,
      actualSecondArithmeticLabel _ _ _ _ _ _ _ n⟩
  have hmult : childMultiplier (!reflected) P.mult (P.unit (!reflected)) c = P.mult*localP.mult := by
    calc childMultiplier (!reflected) P.mult (P.unit (!reflected)) c
        = P.mult*childMultiplier (!reflected) 1 (P.unit (!reflected)) c := by
          dsimp only [childMultiplier]
          ring
      _ = P.mult*localP.mult := congrArg (fun z=>P.mult*z) hvP
  refine ⟨{ mult := childMultiplier (!reflected) P.mult (P.unit (!reflected)) c
            masked := ?_
            supported := ?_ },rfl⟩
  · rw [hmult]
    apply Eq.mpr (congrArg (fun η=>MaskedPrefixPresentation (extendFixedDictionary base)
      η (chain.R₂*chain.E₂) (P.mult*localP.mult)) hchar)
    exact P.masked.advance localP.j₁ localP.χ₁ localP.w₁ localP.first₁ localP.hfirst₁
      localP.C₁ localP.D₁ localP.hC₁ localP.hD₁ localP.hCD₁ localP.U₁ localP.τ₁ localP.hf₁
      localP.hv (chain.R₂*chain.E₂) hP hRholes localP.hcop
  · apply Eq.mpr (congrArg (fun η=>∀z,elementCoeff η z≠0→Supported (Ideal.span {z})) hchar)
    exact family_element_supported localP.χ₁ localP.C₁ localP.D₁ localP.hC₁ localP.hD₁ localP.U₁
      localP.τ₁ localP.hf₁ localP.j₁.2

#print axioms prefix_presented_low_child
end
end OAI.SevenEighths.Cycle153HighProvider
