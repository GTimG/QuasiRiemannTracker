/- UNVERIFIED new-cutoff predicate over ORIGINAL Batch/Fiber and Moments. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedRawFiberBranches
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedAdaptiveCutoff
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def SourceMomentsAt_retuned {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (κ₀ capacity c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (_root_.BelowSevenEighthsTight.FiberExtension.cutoff κ₀ (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=>ell j/d) → B.profile=W → B.upper=(fun _=>b) → B.external=(fun _=>z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      _root_.BelowSevenEighthsTight.FiberExtension.CapacityMoments (B.fiber bin j J K hne) capacity c κ C height εm


theorem sourceMomentsAt_retuned_mono_constant {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (κ₀ capacity c κ C D height εm : ℝ) (hZ : 0≤Z) (hCD : C≤D)
    (h : SourceMomentsAt_retuned M H hH S hS η rows ell W Z d a ε τ dmax b slotMesh binWidth i z
      κ₀ capacity c κ C height εm) :
    SourceMomentsAt_retuned M H hH S hS η rows ell W Z d a ε τ dmax b slotMesh binWidth i z
      κ₀ capacity c κ D height εm := by
  intro q B hrows hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  exact ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _)
    (h q B hrows hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne) hCD

end SevenEighths.ProbeHighRowFamily

end

end OAI

#print axioms OAI.SevenEighths.ProbeHighRowFamily.sourceMomentsAt_retuned_mono_constant
