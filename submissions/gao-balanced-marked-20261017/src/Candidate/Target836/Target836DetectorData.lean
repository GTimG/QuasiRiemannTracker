/- Adapted from OpenAI, Hailey Collet, DaysSky and accepted PR60. Apache-2.0.
Private .874836 assembly; the new affine analytic input remains explicit. -/
import Candidate.Cycle63.Assembly.Count.Data
import Candidate.Target836.Target836Counts
import Candidate.Target836.Target836Geometry
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Candidate.Cycle63.Assembly.Count.Geometry
import Candidate.Cycle25.Assembly.Count.Parameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource

                                      
                                        
                                                               

namespace OAI.SevenEighths.Target836DetectorCount
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
  t_le : t≤1/100
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/100000
  e_pos : 0<e
  e_small : e<1/1000
  witnessKappa_pos : 0<witnessKappa
  witnessKappa_small : witnessKappa≤1
  cost_pos : 0<cost
  momentKappa_lo : 7/10≤momentKappa
  momentKappa_hi : momentKappa≤3/4
  slots_pos : ∀j,0<length j
  slots_small : ∀j,length j≤(1/200)*t
  slots_sum : ∑j,length j=Target836.Arithmetic.ell
  detector_budget : 12*e*((22:ℝ)+2)+8*witnessKappa+2*cost≤ε/2

abbrev SourceData := Cycle63DetectorCount.SourceData

theorem count_slot_supply : (7:ℝ)/37*(7/8)≤Target836.Arithmetic.ell := by
  norm_num [Target836.Arithmetic.ell]

theorem fresh_count_parameters (D : Data) (F : SourceData) :
    Nonempty (Target836Count.CountParameters F.modulus ⊤ D.t) := by
  exact Target836Count.exists_count_parameters F.modulus ⊤ le_top F.S F.w
    F.smooth F.compact F.positive_support (fun x=>(F.bounded x).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support
    (fun x=>(F.bounded x).2) D.t D.t_pos
end
end OAI.SevenEighths.Target836DetectorCount


#print axioms OAI.SevenEighths.Target836DetectorCount.fresh_count_parameters
