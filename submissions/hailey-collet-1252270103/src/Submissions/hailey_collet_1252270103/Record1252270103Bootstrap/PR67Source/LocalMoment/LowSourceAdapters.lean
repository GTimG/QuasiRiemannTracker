import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorZeros
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.LocalMomentSourceAudit
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondNonexceptionalChosenBlock HeckePrimeRay HeckeDetectorZeros
open HeckeFiniteDeletion CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O

/-- Greedy removal uses the incumbent capacity, while its payment uses the low
bin rate.  Exhaustion is a valid alternative and needs no extra residual cost. -/
theorem greedy_low_selection {α : Type*}
    (J : Finset α) (w : α → ℝ) (l₁ l₂ width κbase κlow mesh : ℝ)
    (hb : 0 < κbase) (hl : 0 ≤ κlow) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh) :
    let F := max (l₁+l₂+6*κbase*(∑ i ∈ J, w i)-width) 0
    ∃ R : Finset α, R ⊆ J ∧
      (R = J ∨ l₁+l₂+6*κbase*(∑ i ∈ J \ R, w i) ≤ width) ∧
      κlow*(∑ i ∈ R, w i) ≤ κlow/(6*κbase)*F+κlow*mesh := by
  classical
  dsimp only
  let F := max (l₁+l₂+6*κbase*(∑ i ∈ J, w i)-width) 0
  obtain ⟨R,hR,hbound,hpay,_⟩ := whole_removal J w F κbase mesh
    (le_max_right _ _) hb hm hw hwm
  refine ⟨R,hR,?_,?_⟩
  · rcases hpay with he | hp
    · exact Or.inl he
    · right
      have hsum := Finset.sum_sdiff hR (f := w)
      have hF : l₁+l₂+6*κbase*(∑ i ∈ J, w i)-width ≤ F := le_max_left _ _
      nlinarith
  · have hp := mul_le_mul_of_nonneg_left (hbound.trans (min_le_right _ _)) hl
    convert hp using 1; dsimp only [F]; ring

end SevenEighths.LocalMomentSourceAudit
end
end OAI

end Record1252270103Bootstrap.PR67
