import Candidate.Cycle63.Numerator.Finite.Summation
import Candidate.Cycle63.Numerator.Source.FullW

set_option autoImplicit false
namespace Cycle63.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle63DetectorCount FinalAssembly Cycle63HighTransport Cycle25.Numerator

/-- Source's genuine cell theorem is specialized to the actual buffered partition. -/
theorem actual_cells_of_affine (hgap : Arithmetic.theta<HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Numerator.Source.ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ActualFullWCellInput A J := by
  obtain ⟨J,hJ,hcells⟩:=Numerator.Source.actual_fullW_cells hgap A hAffine
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  obtain ⟨C,hC,hcells⟩:=hcells τ hheight n η
  refine ⟨C,hC,?_⟩
  filter_upwards [hcells,actual_cell_geometry A η τ n] with Z hc hg
  intro C0 hC0 hmom idx grid hsel k hk i hi j hj hne
  have hf:=hg idx grid hsel k i j hne
  have hrow : ∀u∈cellRows A.D A.F Z idx grid k i j,
      (rowCharacter A.F.S A.F.exclusions.prime u).residue≠1 := by
    intro u hu
    exact calibrated_row_nonprincipal A.F.S A.F.exclusions.prime A.F.maximal A.F.exclusions.bad
      u (hf.source_rows u hu).1 (hf.source_rows u hu).2.2.1
  have hb:=hc C0 hC0 hmom (cellRows A.D A.F Z idx grid k i j)
    (sourceDyadConductor Z A.D.t k) (51/100+A.D.e*j) i hf.d_lower hf.d_upper hf.a_lower hf.a_upper
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hf.source_rows hf.moment_rows hrow
    hf.frequency_lower hf.next_maximum hf.current_maximum
  convert hb using 1 <;> rfl
end
end Cycle63.FiniteNumerator
