import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.DaughterState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ClippedProjectorShell
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily ConcreteTraceCRT CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentDivisorRectangle
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The literal final positive daughter aggregate, after the second common
allocation and residual squarefree allocation. No radial or row supremum. -/
def finalPositiveEnergy (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2)))
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then
    ‖Cycle63.Physical.sourcePositiveRow s.toSource second L a z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0

/-- Exact identification of the final aggregate with the old moment energy.
Only the two retained plain cutoffs are clipped; the puncture and slot widths
are unchanged. The two rectangles are addressed independently. -/
theorem final_positive_energy_eq (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2)))
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let X := Cycle63.Physical.sourcePlainScales s.toSource second
    let X₁ := X 0/(Ideal.absNorm (selectedPlain L a 0):ℝ)
    let X₂ := X 1/(Ideal.absNorm (selectedPlain L a 1):ℝ)
    finalPositiveEnergy s second L a keep Φ K =
      energy s.η s.m s.A s.t (dilated s.W₁ (clipDilation X₁))
        (dilated s.W₂ (clipDilation X₂))
        (fun i : liveIndices L a => s.slots i)
        (fun i : liveIndices L a => s.coefficient i)
        (fun i : liveIndices L a => s.P i)
        (clippedScale X₁) (clippedScale X₂) keep Φ K := by
  rfl

/-- Exact final daughter scales, including the independent rectangle. -/
def finalPlain (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (j : Fin 2) : ℝ :=
  clippedScale (Cycle63.Physical.sourcePlainScales s.toSource second j/
    (Ideal.absNorm (selectedPlain L a j):ℝ))

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
