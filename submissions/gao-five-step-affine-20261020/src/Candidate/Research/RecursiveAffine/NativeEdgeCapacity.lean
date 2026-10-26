/- Genuine selected-source residual capacity used by a native trace edge. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeNodeStep
import Candidate.Research.RecursiveAffine.TerminalSourceReceipt
import Candidate.Research.RecursiveAffine.ActualDeletedCapacity

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open Cycle153RegionalLow Cycle63FinalLow CenteredMomentAllocatedChildCapacity
open CenteredMomentEnergyInputParentCapacity

variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M≤H}
  {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- The formal residual factor remains the actual selected source
factor. The capacity is obtained from native two-stage source arithmetic,
not supplied as a desired recursive energy or daughter-length bound. -/
theorem actual_inner_trace_capacity
    (N : ReachableNode C j) (s : Input N.slots) (ch : Chain s) (chi : Character) (t : ℝ)
    (budget : ℕ) (b : ℝ) (hb : 1 ≤ b) (hcard : Fintype.card N.slots ≤ budget)
    (hs : s.upper ≤ b)
    (hX1 : s.X₁=N.X1) (hX2 : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (hn1 : frozenCoefficient ch.B₁.val ch.C₁ ch.R₁ s.ν s.W s.P≠0)
    (hn2 : frozenCoefficient ch.B₂.val ch.E₂ ch.R₂ ch.first.ν ch.first.W ch.first.P≠0)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final chi t).toSource second L alloc row≠0)
    (Rdel : Finset N.slots) (hRdel : Rdel ⊆ ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ nodeDetectorDeletion N ≤ ∑i∈Rdel,C.originalWeight i/N.unit) :
    let F:=N.unit*Real.logb N.localBase (formalReductionFactor L alloc (ch.final chi t).P)
    let Achild:=N.unit*(length N.localBase (rawDaughterScale (ch.final chi t) second L alloc 0)+
      length N.localBase (rawDaughterScale (ch.final chi t) second L alloc 1)+
        (∑i∈ch.indices L alloc\Rdel,C.originalWeight i/N.unit))
    let pad:=N.unit*(2*(budget:ℝ)*Real.logb N.localBase b+
      Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂))
    0 ≤ F ∧ Achild ≤ N.unit*Real.logb N.localBase (volume (N.input hH))-
      pathDeletion j.val N.coordinates-
      N.unit*(Real.logb N.localBase (ch.C₁.absNorm:ℝ)+Real.logb N.localBase (ch.E₂.absNorm:ℝ))-
      F+pad := by
  intro F Achild pad
  have hw : ∀i : N.slots,0 ≤ C.originalWeight i/N.unit :=
    fun i=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le
  have hP : ∀i,1 ≤ s.P i := by
    intro i
    rw [hscale]
    exact Real.one_le_rpow N.localBase_gt_one.le (hw i)
  have hcap:=actual_deleted_daughter_total_capacity s ch chi t N.localBase N.localBase_gt_one
    budget b hb hcard hs hP (fun i=>C.originalWeight i/N.unit) hscale hn1 hn2
    second L alloc row hne Rdel hRdel
  have hF : 0 ≤ Real.logb N.localBase (formalReductionFactor L alloc (ch.final chi t).P) :=
    Real.logb_nonneg N.localBase_gt_one
      (formalReduction_ge_one L alloc (ch.final chi t).P (fun i=>hP i.val.val))
  have hD := hcover.resolve_left hproper
  have hdet:=nodeDetectorDeletion_bounds N
  have hDlocal : pathDeletion j.val N.coordinates/N.unit ≤ ∑i∈Rdel,C.originalWeight i/N.unit := by
    linarith only [hD,hdet.1]
  have hDglobal : pathDeletion j.val N.coordinates ≤
      N.unit*(∑i∈Rdel,C.originalWeight i/N.unit) := by
    have h:=mul_le_mul_of_nonneg_left hDlocal N.unit_pos.le
    simpa only [mul_div_cancel₀ _ N.unit_pos.ne'] using h
  have hparent : N.unit*(length N.localBase s.X₁+length N.localBase s.X₂+
      ∑i : N.slots,C.originalWeight i/N.unit)=N.unit*Real.logb N.localBase (volume (N.input hH)) := by
    rw [hX1,hX2]
    exact N.length_eq.trans (N.volume_model (hH:=hH)).symm
  have hcapglobal:=mul_le_mul_of_nonneg_left hcap N.unit_pos.le
  refine ⟨mul_nonneg N.unit_pos.le hF,?_⟩
  dsimp only [Achild,F,pad] at *
  nlinarith only [hcapglobal,hparent,hDglobal]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_inner_trace_capacity
