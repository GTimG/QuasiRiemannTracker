import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DivisorRetained
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace Cycle63.Physical

noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorExtraction
local notation "O" => ActualEisensteinCubic.O

def negativeTotal (x : Fin 2 → ℝ) : ℝ := ∑ i, max 0 (-x i)

def clippedReduction (r : ℝ) (x a : Fin 2 → ℝ) : ℝ :=
  r - (negativeTotal (fun i => x i-a i)-negativeTotal x)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualPlainReduction (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (j : Fin 2) : ℝ :=
  Real.logb Z (Ideal.absNorm (selectedPlain D a j) : ℝ)

end
end Cycle63.Physical

end Record1252270103Bootstrap.PR67
