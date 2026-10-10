import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import WeightedQRH.MomentData
import OAI.NumberTheory.DirichletL.ParametersFixedSource
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

structure WeightedSourceData (D : WeightedQRH.MomentData) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀P∈S,P.IsMaximal
  first : FirstTail (4*D.e) S
  w : ℝ→ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded : ∀x,0 ≤ w x ∧ w x ≤ 1
  nonzero : w≠0
  complex_eq : ∀x,W x=(w x:ℂ)
  complex_nonzero : W≠0
  complex_support : Function.support W⊆Set.Icc 1 2
  real : ∀x,(W x).im=0
  nonnegative : ∀x,0 ≤ (W x).re

theorem weighted_exists_source_data (D : WeightedQRH.MomentData) : Nonempty (WeightedSourceData D) := by
  obtain ⟨S,_,hS,hfirst,hmax⟩ := exists_fixed_source D.e D.e_pos ∅ (by simp)
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
  exact ⟨⟨S,hS,hmax,hfirst,w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩⟩

def WeightedSourceData.modulus {D : WeightedQRH.MomentData} (F : WeightedSourceData D) : Ideal O := ∏P∈F.S,P

instance {D : WeightedQRH.MomentData} (F : WeightedSourceData D) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance {D : WeightedQRH.MomentData} (F : WeightedSourceData D) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem weighted_source_count_parameters {D : WeightedQRH.MomentData} (F : WeightedSourceData D) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

end SevenEighths.ProbeFinalAssembly
end
end OAI
