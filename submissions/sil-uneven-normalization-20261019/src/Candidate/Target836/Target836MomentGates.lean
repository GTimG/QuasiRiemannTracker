/- Adapted from OpenAI, Hailey Collet, DaysSky and accepted PR60. Apache-2.0.
Private .874836 assembly; the new affine analytic input remains explicit. -/
import Candidate.Target836.Target836DetectorData
import Candidate.Target836.Target836SourceCount
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Candidate.Cycle63.Assembly.Count.Data
import Candidate.Cycle25.Assembly.Count.SourceMomentInput
import Candidate.Affine.SourceCount

                                                                   
                                  
                                               

namespace OAI.SevenEighths.Target836DetectorCount
noncomputable section
open scoped Classical BigOperators
open HeckeFamily ProbePhysical ProbeHighRowFamily HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch

/-- Actual physical detector fiber moments on the new slot lengths. This is
an integration input, not an endpoint or a claimed affine moment theorem. -/
def SourceMomentBound (D : Data) (F : SourceData)
    (counts : Target836Count.CountParameters F.modulus ⊤ D.t)
    (η : Character) (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ,(1/200:ℝ)≤d→d≤7/8→51/100<a→a≤7/8→
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t))→
    ∀i : ℕ,∀z : ℂ,z.re=17/50→|z.im|≤height→
    Target836SourceCount.SourceMomentsAtA F.modulus ⊤ le_top F.S F.exclusions.prime η
      rows D.length (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z
      D.momentKappa counts.c counts.k C height D.t

lemma SourceMomentBound.mono_constant {D : Data} {F : SourceData}
    {counts : Target836Count.CountParameters F.modulus ⊤ D.t}
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
  · intro selected hsel h1 h2 h3 h4 h5 j k hj s hs t ht
    exact (haf selected hsel h1 h2 h3 h4 h5 j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))

end
end OAI.SevenEighths.Target836DetectorCount

#print axioms OAI.SevenEighths.Target836DetectorCount.SourceMomentBound.mono_constant
