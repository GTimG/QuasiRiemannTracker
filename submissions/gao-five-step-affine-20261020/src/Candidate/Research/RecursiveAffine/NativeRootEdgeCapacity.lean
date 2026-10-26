/- Genuine root-source residual capacity at the explicit plane majorant. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootStep
import Candidate.Research.RecursiveAffine.ActualDeletedCapacity

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153RootStep Cycle153RegionalLow
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open Cycle63FinalLow CenteredMomentAllocatedChildCapacity
open CenteredMomentEnergyInputParentCapacity

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The native daughter capacity is bounded by the genuine root plane.
This uses an explicit volume majorant, without identifying it with the
actual raw volume. The selected formal residual factor stays attached. -/
theorem actual_root_trace_capacity
    (s : Input α) (ch : Chain s) (chi : Character) (t Z : ℝ) (hZ : 1 < Z)
    (budget : ℕ) (b : ℝ) (hb : 1 ≤ b) (hcard : Fintype.card α ≤ budget)
    (hs : s.upper ≤ b) (w : α→ℝ) (hw : ∀i,0 ≤ w i)
    (hscale : ∀i,s.P i=Z^(w i))
    (hwindow : @Cycle63.AffineLedger.PlainWindow Cycle153.Root.rootLedger
      (length Z s.X₁) (length Z s.X₂) (∑i,w i))
    (hn1 : frozenCoefficient ch.B₁.val ch.C₁ ch.R₁ s.ν s.W s.P≠0)
    (hn2 : frozenCoefficient ch.B₂.val ch.E₂ ch.R₂ ch.first.ν ch.first.W ch.first.P≠0)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final chi t).toSource second L alloc row≠0)
    (Rdel : Finset α) (hRdel : Rdel ⊆ ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ rootDetectorDeletion w ≤ ∑i∈Rdel,w i) :
    let F:=Real.logb Z (formalReductionFactor L alloc (ch.final chi t).P)
    let Achild:=length Z (rawDaughterScale (ch.final chi t) second L alloc 0)+
      length Z (rawDaughterScale (ch.final chi t) second L alloc 1)+(∑i∈ch.indices L alloc\Rdel,w i)
    let pad:=2*(budget:ℝ)*Real.logb Z b+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
    0 ≤ F ∧ Achild ≤ rootSourceLength w-rootSourceDeletion w-
      (Real.logb Z (ch.C₁.absNorm:ℝ)+Real.logb Z (ch.E₂.absNorm:ℝ))-F+pad := by
  intro F Achild pad
  have hP : ∀i,1 ≤ s.P i := by
    intro i
    rw [hscale]
    exact Real.one_le_rpow hZ.le (hw i)
  have hcap:=actual_deleted_daughter_total_capacity s ch chi t Z hZ budget b hb hcard hs hP
    w hscale hn1 hn2 second L alloc row hne Rdel hRdel
  have hF : 0 ≤ F := Real.logb_nonneg hZ
    (formalReduction_ge_one L alloc (ch.final chi t).P (fun i=>hP i.val.val))
  have hD:=hcover.resolve_left hproper
  dsimp only [rootDetectorDeletion] at hD
  have hparent:=(actual_root_cell_slack s Z w hwindow).2.2.2.2.1
  refine ⟨hF,?_⟩
  dsimp only [Achild,F,pad]
  nlinarith only [hcap,hparent,hD]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_trace_capacity
