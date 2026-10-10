import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput
import Cycle25.Assembly.Count.SourceMomentInput
import Cycle25.Assembly.SourceData
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Cycle25ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters Cycle25ProbeHighRowFamily
open HeckeInverseAmplification

def weighted_SourceMomentBound {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D)
    (κplain : ℝ) (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100<a → a ≤ 7/8 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im| ≤ height →
    Cycle25ProbeHighRowFamily.SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z κplain counts.c counts.k C height D.t

lemma weighted_SourceMomentBound.mono_constant {D : Cycle25.Weighted.MomentData}
    {F : WeightedSourceData D} {κplain : ℝ}
    {counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t}
    {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤Z) (h : weighted_SourceMomentBound F κplain counts η Z τ C height)
    (hC : C≤C') : weighted_SourceMomentBound F κplain counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots hwidth
    hprof hupp hext hmesh hbin hfam bin j J K hne
  have hm := h rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots
    hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  refine ⟨ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _) hm.original hC,?_⟩
  intro selected hsel hcap j k hj s hs t ht
  exact (hm.plain_marked selected hsel hcap j k hj s hs t ht).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))

end SevenEighths.Cycle25ProbeFinalAssembly
end
end OAI
