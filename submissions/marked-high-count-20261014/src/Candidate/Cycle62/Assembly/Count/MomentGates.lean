import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Candidate.Cycle62.Assembly.Count.Data
import Candidate.Cycle25.Assembly.Count.SourceMomentInput

namespace OAI.SevenEighths.Cycle62DetectorCount
noncomputable section
open scoped Classical BigOperators
open HeckeFamily ProbePhysical ProbeHighRowFamily HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch

/-- Actual physical detector fiber moments on the new slot lengths. This is
an integration input, not an endpoint or a claimed affine moment theorem. -/
def SourceMomentBound (D : Data) (F : SourceData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)
    (η : Character) (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ,(1/200:ℝ)≤d→d≤7/8→51/100<a→a≤7/8→
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t))→
    ∀i : ℕ,∀z : ℂ,z.re=17/50→|z.im|≤height→
    Cycle25ProbeHighRowFamily.SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η
      rows D.length (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z
      D.momentKappa counts.c counts.k C height D.t

lemma SourceMomentBound.mono_constant {D : Data} {F : SourceData}
    {counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t}
    {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤Z) (h : SourceMomentBound D F counts η Z τ C height)
    (hC : C≤C') : SourceMomentBound D F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots hwidth
    hprof hupp hext hmesh hbin hfam bin j J K hne
  have hm := h rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots
    hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  refine ⟨ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _) hm.original hC,?_⟩
  intro selected hsel hcap j k hj s hs t ht
  exact (hm.plain_marked selected hsel hcap j k hj s hs t ht).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))

/-- The exact genuine physical gates needed by the optimized detector count.
The original fields contain MI/raw and unmarked plain estimates; the marked
plain gate uses 2m+6κz≤1. The original 3/4 marked gate is deduced. -/
def FiberFields {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (κplain c inverseKappa C height εm : ℝ) : Prop :=
  Cycle25DetectorRawFiber.BaseMoments F c inverseKappa C height εm ∧
    Cycle25DetectorRawFiber.MarkedPlainMoment F κplain C height εm

theorem moments_of_physical_fields {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {κplain c inverseKappa C height εm : ℝ} (hk : κplain≤3/4)
    (h : FiberFields F κplain c inverseKappa C height εm) :
    Cycle25DetectorRawFiber.Moments F κplain c inverseKappa C height εm :=
  Cycle25DetectorRawFiber.Moments.of_fields F hk h.1 h.2
end
end OAI.SevenEighths.Cycle62DetectorCount
