/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualCoordinateLift
import Candidate.Cycle63.Physical.InitialMass.SecondLowGeometry

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153ContinuationUnit
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSectorLocalization CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentCommonProfile
open Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open Cycle153RegionalLow

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The continuing base is the native retained-width ceiling. It may
widen the state, but never exceeds the exponent already paid by the
actual LOW source. -/
def nativeUnit (U Z amp omega reserve xi : ℝ) (C₁ D₁ C₂ D₂ : Ideal O)
    (inactive : Finset (CommonIndex C₂ D₂)) : ℝ :=
  secondNominal U Z amp omega C₁ D₁ C₂ D₂ inactive + reserve*U + xi/2

def commonWidthLoss (Z : ℝ) (C₁ D₁ C₂ D₂ : Ideal O)
    (inactive : Finset (CommonIndex C₂ D₂)) : ℝ :=
  max (Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (D₁.absNorm:ℝ)) 0 +
    Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))-
    Real.logb Z ((∏P∈inactive,P.val).absNorm:ℝ)

/-- The frequency-bin half-width and the chosen width reserve cancel
literally. Only log_Z(128) remains, and it is retained in the geometry. -/
theorem nativeUnit_eq
    (U Z amp reserve xi : ℝ) (C₁ D₁ C₂ D₂ : Ideal O)
    (inactive : Finset (CommonIndex C₂ D₂)) :
    nativeUnit U Z amp (frequencyLoss Z 32 xi+reserve*U) reserve xi
      C₁ D₁ C₂ D₂ inactive =
      U-6*amp-commonWidthLoss Z C₁ D₁ C₂ D₂ inactive-Real.logb Z 128 := by
  unfold nativeUnit secondNominal commonWidthLoss frequencyLoss
  norm_num
  ring

/-- This is the actual native width theorem at the SAME supported live
source. The bound on its old main term is an identity, rather than a
separate assumed energy inequality. -/
theorem actual_native_unit
    {s : Input α} {q : Chain s} {Z U Mrow amp omega xi b reserve : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega xi b N)
    (Bmask : ℝ) (hZ : 1<Z) (hb : 0<b)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ) ≤ Z^Bmask)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ U+(reserve/2)*U)
    (hconstants : Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(N:ℝ)*Real.logb Z b+Real.logb Z 1+
      Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)) ≤ (reserve/2)*U)
    (homega : omega=frequencyLoss Z 32 xi+reserve*U) :
    let st := retainedState Z Bmask hZ (g.datum.τ χ) Q (q.R₂*q.E₂) hP hPN
      g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let next := nativeUnit U Z amp omega reserve xi q.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive
    st.width ≤ next ∧
      next=U-6*amp-commonWidthLoss Z q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive-
        Real.logb Z 128 ∧ 0 ≤ Real.logb Z 128 := by
  intro st next
  have hw := live_main_state_width_unit g Bmask hZ hb χ Q hP hPN hfit hconstants
  refine ⟨?_,?_,Real.logb_nonneg hZ (by norm_num)⟩
  · change st.width ≤ secondNominal U Z amp omega q.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive+reserve*U+xi/2
    linarith only [hw]
  · dsimp only [next]
    exact (congrArg (fun omegaNew : ℝ => nativeUnit U Z amp omegaNew reserve xi
      q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive) homega).trans
        (nativeUnit_eq U Z amp reserve xi q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive)

end
end OAI.SevenEighths.Cycle153ContinuationUnit
#print axioms OAI.SevenEighths.Cycle153ContinuationUnit.actual_native_unit
