/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeContinuationUnit
import Candidate.Research.RecursiveAffine.ActualPhysicalTransition

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle153ContinuationUnit
noncomputable section
open scoped Classical BigOperators HeckeNotation
open CanonicalQuadraticSieve CenteredMomentSectorLocalization
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentCommonProfile
open CenteredMomentCommonRawScale CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open CenteredMomentDivisorRaw CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open Cycle63Moment.LowBranch Cycle153RegionalLow

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Obtain the scalar model coordinates from the SAME actual live LOW
source and attaining residual daughter. Neither width recurrence nor
common-norm cancellation is supplied as a desired hypothesis. -/
theorem actual_native_physical_coordinates
    (s : Input α) (ch : Chain s) (χ : Character) (t Z : ℝ)
    (hZ : 1<Z) (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (Mrow ampActual omega xi reserve : ℝ)
    (g : LiveMainGeometry s ch Z Mrow ampActual omega xi b N)
    (hcard : Fintype.card α ≤ N) (hs : s.upper ≤ b) (hlower : 1 ≤ s.lower)
    (hP : ∀i,1 ≤ s.P i) (w : α → ℝ) (hscale : ∀i,s.P i=Z^(w i))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L alloc row≠0)
    (Rdel : Finset α) (hRdel : Rdel ⊆ ch.indices L alloc)
    (A U aModel da D mesh : ℝ)
    (hA : length Z s.X₁+length Z s.X₂+(∑i,w i) ≤ A)
    (hda : 0 ≤ da) (ha : ampActual=aModel+da)
    (hdel : D ≤ ∑i∈Rdel,w i) (hdelmesh : (∑i∈Rdel,w i) ≤ D+mesh)
    (homega : omega=frequencyLoss Z 32 xi+reserve*U) :
    let next := nativeUnit U Z ampActual omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive
    let v := commonWidthLoss Z ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let commonRed := min (Real.logb Z (ch.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
      Real.logb Z (ch.E₂.absNorm:ℝ)-Real.logb Z (normValue
        (commonFrequencyGenerator g.datum.C g.datum.D))+
      Real.logb Z ((∏P∈g.datum.inactive,P.val).absNorm:ℝ)
    let Achild := length Z (rawDaughterScale (ch.final χ t) second L alloc 0)+
      length Z (rawDaughterScale (ch.final χ t) second L alloc 1)+(∑i∈ch.indices L alloc\Rdel,w i)
    let pad := 2*(N:ℝ)*Real.logb Z b+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
    let V := v+(Real.logb Z 128+6*da)
    let Red := A-D-V-Achild
    let ell := (∑i,w i)-(∑i∈ch.indices L alloc,w i)+((∑i∈Rdel,w i)-D)
    let zchild := ∑i∈ch.indices L alloc\Rdel,w i
    0 ≤ V ∧ next=U-6*aModel-V ∧
      -(Real.logb Z 128+6*da+pad) ≤ Red ∧
      v+commonRed ≤ V+Red+pad ∧
      0 ≤ ell ∧ ell ≤ V+Red+pad ∧
      zchild=(∑i,w i)-D-ell ∧ Achild=A-D-V-Red ∧
      (∀ slack : ℝ, Real.logb Z 128+6*da+pad ≤ slack →
        D+slack ≤ ∑i∈Rdel,w i → 0 ≤ Red) := by
  intro next v commonRed Achild pad V Red ell zchild
  have normLog (I : Ideal O) (hI : Supported I) : 0 ≤ Real.logb Z (I.absNorm:ℝ) :=
    Real.logb_nonneg hZ (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1))
  have hc := normLog ch.C₁ g.hC₁
  have hd := normLog g.D₁ g.hD₁
  have hif := CenteredMomentSecondActualWidth.actual_common_log_ge_unit
    g.datum.C g.datum.D g.datum.hC g.datum.inactive Z hZ
  have hfe : Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
      Real.logb Z ((∏P∈g.datum.inactive,P.val).absNorm:ℝ) ≤ Real.logb Z (ch.E₂.absNorm:ℝ) := by
    rcases g.label with h | h
    · rw [h]
      exact Cycle63FinalCapacity.actual_common_shift_le
        g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
    · rw [h]
      exact Cycle63FinalCapacity.actual_common_shift_le_right
        g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
  have hv : 0 ≤ v := by
    dsimp only [v,commonWidthLoss]
    linarith only [le_max_right
      (Real.logb Z (ch.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0,hif]
  have hr : 0 ≤ commonRed := by
    dsimp only [commonRed]
    linarith only [le_min hc hd,hfe]
  have ht : 0 ≤ Real.logb Z 128 := Real.logb_nonneg hZ (by norm_num)
  have hcommon : v+commonRed=Real.logb Z (ch.C₁.absNorm:ℝ)+Real.logb Z (ch.E₂.absNorm:ℝ) :=
    common_puncture_coordinate_identity _ _ _ _ _
  have hnext : next=U-6*ampActual-v-Real.logb Z 128 := by
    dsimp only [next]
    exact (congrArg (fun omegaNew : ℝ => nativeUnit U Z ampActual omegaNew reserve xi
      ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive) homega).trans
        (nativeUnit_eq U Z ampActual reserve xi ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive)
  have hcoords := actual_physical_transition_coordinates s ch χ t Z hZ N b hb hcard hs hlower
    hP w hscale g.first_nonzero g.second_nonzero second L alloc row hne Rdel hRdel
    A U next aModel ampActual da D mesh v commonRed (Real.logb Z 128) 0
    hA hv (by simpa using hr) hcommon ht hda ha hdel hdelmesh hnext
  rcases hcoords with ⟨hV,hEll,hEllmax,hU,hSlots,hAchild,hRed,hF,hSlot,hCommon⟩
  refine ⟨hV,hU,?_,hCommon,hEll,hSlot,hSlots,hAchild,?_⟩
  · dsimp only [pad,Red,V,Achild]
    linarith only [hRed]
  · intro slack hslack hdeleted
    have hPfinal : ∀i, 1 ≤ (ch.final χ t).P i := fun i => hP i.val.val
    have hF0 : 0 ≤ Real.logb Z (formalReductionFactor L alloc (ch.final χ t).P) :=
      Real.logb_nonneg hZ (formalReduction_ge_one L alloc (ch.final χ t).P hPfinal)
    dsimp only [pad,Red,V,Achild] at hslack ⊢
    linarith only [hF,hr,hF0,hslack,hdeleted]

end
end OAI.SevenEighths.Cycle153ContinuationUnit
#print axioms OAI.SevenEighths.Cycle153ContinuationUnit.actual_native_physical_coordinates
