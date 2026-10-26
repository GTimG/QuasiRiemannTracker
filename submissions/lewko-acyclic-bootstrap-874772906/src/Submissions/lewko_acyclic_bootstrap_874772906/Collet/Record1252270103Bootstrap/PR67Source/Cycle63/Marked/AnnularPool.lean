import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.NaturalSlotHeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeSlot
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators
open Set HeckeFamily CenteredMomentCommonMaskExpansion HeckePrimeAnnular
local notation "O" => HeckeFamily.O

/-- The finite source prime pool with the actual annular support exposed. -/
def annularPool (pool : Finset (Ideal O)) (P : ℝ) : Finset (Ideal O) :=
  pool.filter (fun I=>(I.absNorm:ℝ)/P∈Icc (1:ℝ) 2)

theorem annularPool_subset (pool : Finset (Ideal O)) (P : ℝ) : annularPool pool P⊆pool :=
  Finset.filter_subset _ _

theorem annularPool_ratio (pool : Finset (Ideal O)) (P : ℝ) (I : Ideal O)
    (hI : I∈annularPool pool P) : (I.absNorm:ℝ)/P∈Icc (1:ℝ) 2 :=
  (Finset.mem_filter.mp hI).2

theorem naturalSlot_annular_filter (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (hW : Function.support W⊆Icc (1:ℝ) 2)
    (P σ t : ℝ) :
    naturalSlot χ (annularPool pool P) (fun I=>ν I*annularWeight W P σ t I) P=
      naturalSlot χ pool (fun I=>ν I*annularWeight W P σ t I) P := by
  unfold naturalSlot annularPool
  rw [Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun I hI => ?_
  by_cases ha : (I.absNorm:ℝ)/P∈Icc (1:ℝ) 2
  · exact ite_eq_left ha
  · rw [ite_eq_right ha]
    have hw : W ((I.absNorm:ℝ)/P)=0 := by
      by_contra hn
      exact ha (hW hn)
    simp [annularWeight,hw]

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
