import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondInput
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointColumnExtraction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource Cycle63Moment
open CenteredMomentCommonWindowColumn CenteredMomentCommonHeightEnvelope
open CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
local instance secondExtractionDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- One extraction constant for every surviving subset of the original
finite slot dictionary, chosen before all moving source data. -/
theorem actual_uniform_second_column_extraction {α : Type*} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀ S : Finset α,∀s : Input S,∀C : Ideal O,∀hC : Supported C,
      ∀R seed L : Ideal O,seed∣C → Squarefree L → ∀z : O,
      ‖normalizedColumn s C hC R seed L z‖^2≤
        K*(L.absNorm:ℝ)^ε*commonRetainedCost s C R L z := by
  have he (S : Finset α) := actual_common_column_extraction (ι:=S) ε hε
  choose K hK hb using he
  let Ksum := 1+∑S : Finset α,K S
  have hs : 0≤∑S : Finset α,K S := Finset.sum_nonneg (fun S _=>(hK S).le)
  refine ⟨Ksum,by dsimp [Ksum]; linarith,?_⟩
  intro S s C hC R seed L hseed hL z
  have hle : K S≤Ksum := by
    have hh := Finset.single_le_sum (fun S _=>(hK S).le) (Finset.mem_univ S)
    dsimp [Ksum]
    linarith
  exact (hb S s C hC R seed L hseed hL z).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (common_retained_cost_nonneg _ _ _ _ _))

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
