import Candidate.Target830.Physical.SourceCountInitial
import Candidate.Target830.Physical.Data
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono

namespace OAI.SevenEighths.Target830.Physical
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open HeckeFamily ProbePhysical ProbeHighRowFamily HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch

/-- Actual physical detector fiber moments on the new slot lengths. This is
an integration input, not an endpoint or a claimed affine moment theorem. -/
def SourceMomentBound (D : BaselineData) (F : SourceData)
    (counts : DetectorCount.CountParameters F.modulus ⊤ D.t)
    (η : Character) (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ,(1/200:ℝ)≤d→d≤7/8→51/100<a→a≤7/8→
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t))→
    ∀i : ℕ,∀z : ℂ,z.re=17/50→|z.im|≤height→
    SourceCount.SourceMomentsAtA F.modulus ⊤ le_top F.S F.exclusions.prime η
      rows D.length (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z
      D.momentKappa counts.c counts.k C height D.t

lemma SourceMomentBound.mono_constant {D : BaselineData} {F : SourceData}
    {counts : DetectorCount.CountParameters F.modulus ⊤ D.t}
    {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤Z) (h : SourceMomentBound D F counts η Z τ C height)
    (hC : C≤C') : SourceMomentBound D F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots hwidth
    hprof hupp hext hmesh hbin hfam bin j J K hne
  obtain ⟨hm,haf⟩ := h rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots
    hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  refine ⟨⟨ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _) hm.original hC,?_⟩,?_⟩
  · intro selected hsel hcap j k hj s hs t ht
    exact (hm.plain_marked selected hsel hcap j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))
  · intro P hmlo hmhi selected hsel h1 h2 h3 j k hj s hs t ht
    exact (haf P hmlo hmhi selected hsel h1 h2 h3 j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))

end
end OAI.SevenEighths.Target830.Physical
#print axioms OAI.SevenEighths.Target830.Physical.SourceMomentBound.mono_constant
