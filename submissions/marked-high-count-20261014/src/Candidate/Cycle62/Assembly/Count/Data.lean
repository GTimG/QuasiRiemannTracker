import Candidate.Cycle62.Assembly.Count.Geometry
import Candidate.Cycle25.Assembly.Count.Parameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource

namespace OAI.SevenEighths.Cycle62DetectorCount
noncomputable section
open scoped Classical BigOperators ContDiff
open HeckeFamily HeckeInverseAmplification ProbePhysical

/-- Actual small prime-slot lengths at the new rational total. All scalar
parameters are fixed before the live character, row height and amplitude class. -/
structure Data where
  N : ℕ
  length : Fin N→ℝ
  t : ℝ
  ε : ℝ
  e : ℝ
  witnessKappa : ℝ
  cost : ℝ
  momentKappa : ℝ
  t_pos : 0<t
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  e_pos : 0<e
  e_small : e<1/1000
  witnessKappa_pos : 0<witnessKappa
  witnessKappa_small : witnessKappa≤1
  cost_pos : 0<cost
  momentKappa_lo : 7/10≤momentKappa
  momentKappa_hi : momentKappa≤3/4
  slots_pos : ∀j,0<length j
  slots_small : ∀j,length j≤(1/200)*t
  slots_sum : ∑j,length j=Cycle62.Arithmetic.ell
  detector_budget : 12*e*((22:ℝ)+2)+8*witnessKappa+2*cost≤ε/2

/-- Source exclusions and a genuine common physical window; no probe theorem
or endpoint is stored in this structure. -/
structure SourceData where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀P∈S,P.IsMaximal
  w : ℝ→ℝ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded : ∀x,0≤w x ∧ w x≤1
  nonzero : w≠0

def SourceData.modulus (F : SourceData) : Ideal O := ∏P∈F.S,P
instance (F : SourceData) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
instance (F : SourceData) : Finite (O⧸F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem fresh_count_parameters (D : Data) (F : SourceData) :
    Nonempty (Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) := by
  exact Cycle25ProbeHighRowFamily.exists_count_parameters F.modulus ⊤ le_top F.S F.w
    F.smooth F.compact F.positive_support (fun x=>(F.bounded x).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support
    (fun x=>(F.bounded x).2) D.t D.t_pos
end
end OAI.SevenEighths.Cycle62DetectorCount
