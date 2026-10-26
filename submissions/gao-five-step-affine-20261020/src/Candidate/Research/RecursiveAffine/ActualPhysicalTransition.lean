/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualDeletedCapacity

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentAllocatedNaturalSource
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands
open CenteredMomentEnergyInputParentCapacity
open Cycle63FinalLow Cycle63Moment.LowBranch Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- The literal attaining source daughter and its actual original ray
slots determine the model coordinates. The capacity and slot-loss inputs
are discharged by the native physical chain, not supplied as desired
recurrences. Upward amplifier displacement and every finite common error
are retained. This theorem concerns the source geometry, not its still
separate recursively returned energy estimate. -/
theorem actual_physical_transition_coordinates
    (s : Input iota) (ch : Chain s) (chi : Character) (t Z : ℝ)
    (hZ : 1 < Z) (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (hcard : Fintype.card iota ≤ N) (hs : s.upper ≤ b) (hlower : 1 ≤ s.lower)
    (hP : ∀ i, 1 ≤ s.P i) (w : iota → ℝ) (hscale : ∀ i, s.P i = Z ^ w i)
    (hn1 : frozenCoefficient ch.B₁.val ch.C₁ ch.R₁ s.ν s.W s.P ≠ 0)
    (hn2 : frozenCoefficient ch.B₂.val ch.E₂ ch.R₂
      ch.first.ν ch.first.W ch.first.P ≠ 0)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val) ⊕ Fin 2)))
    (row : O)
    (hne : Cycle63.Physical.sourcePositiveRow (ch.final chi t).toSource second L alloc row ≠ 0)
    (Rdel : Finset iota) (hRdel : Rdel ⊆ ch.indices L alloc)
    (A U Uchild aModel aActual da D mesh v commonRed widthError commonError : ℝ)
    (hA : length Z s.X₁+length Z s.X₂+(∑i,w i) ≤ A)
    (hv : 0 ≤ v) (hr : -commonError ≤ commonRed)
    (hcommon : v+commonRed = Real.logb Z (ch.C₁.absNorm : ℝ)+
      Real.logb Z (ch.E₂.absNorm : ℝ))
    (ht : 0 ≤ widthError) (hda : 0 ≤ da) (ha : aActual = aModel+da)
    (hdel : D ≤ ∑i∈Rdel,w i) (hdelmesh : (∑i∈Rdel,w i) ≤ D+mesh)
    (hU : Uchild = U-6*aActual-v-widthError) :
    let J := ch.indices L alloc
    let Achild := length Z (rawDaughterScale (ch.final chi t) second L alloc 0)+
      length Z (rawDaughterScale (ch.final chi t) second L alloc 1)+(∑i∈J\Rdel,w i)
    let zchild := ∑i∈J\Rdel,w i
    let ell0 := (∑i,w i)-(∑i∈J,w i)
    let F := Real.logb Z (formalReductionFactor L alloc (ch.final chi t).P)
    let pad := 2*(N:ℝ)*Real.logb Z b+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
    let V := v+(widthError+6*da)
    let Red := A-D-V-Achild
    let ell := ell0+((∑i∈Rdel,w i)-D)
    0 ≤ V ∧ 0 ≤ ell ∧ ell ≤ ell0+mesh ∧
      Uchild = U-6*aModel-V ∧ zchild = (∑i,w i)-D-ell ∧
      Achild = A-D-V-Red ∧ -(commonError+widthError+6*da+pad) ≤ Red ∧
      commonRed+F+((∑i∈Rdel,w i)-D) ≤ Red+(widthError+6*da)+pad ∧
      ell ≤ V+Red+pad ∧ v+commonRed ≤ V+Red+pad := by
  have hcap := actual_deleted_daughter_total_capacity s ch chi t Z hZ N b hb
    hcard hs hP w hscale hn1 hn2 second L alloc row hne Rdel hRdel
  have hslot := actual_original_dictionary_slot_loss s ch chi t Z hZ hlower hP w hscale
    hn1 hn2 L alloc
  have hPfinal : ∀i, 1 ≤ (ch.final chi t).P i := fun i => hP i.val.val
  have hF : 0 ≤ Real.logb Z (formalReductionFactor L alloc (ch.final chi t).P) :=
    Real.logb_nonneg hZ (formalReduction_ge_one L alloc (ch.final chi t).P hPfinal)
  have hsum := Finset.sum_sdiff hRdel (f:=w)
  apply actual_low_coordinate_lift_with_common_error A
    (length Z (rawDaughterScale (ch.final chi t) second L alloc 0)+
      length Z (rawDaughterScale (ch.final chi t) second L alloc 1)+
      (∑i∈ch.indices L alloc\Rdel,w i))
    (∑i,w i) (∑i∈ch.indices L alloc\Rdel,w i) U Uchild aModel aActual da
    D (∑i∈Rdel,w i) mesh v commonRed
    (Real.logb Z (formalReductionFactor L alloc (ch.final chi t).P))
    ((∑i,w i)-(∑i∈ch.indices L alloc,w i)) widthError
    (2*(N:ℝ)*Real.logb Z b+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) commonError
    hv hr hF ht hda hslot.1 ha hdel hdelmesh
  · linarith only [hslot.2, hcommon]
  · linarith only [hsum]
  · exact hU
  · linarith only [hcap, hA, hcommon]

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_physical_transition_coordinates
