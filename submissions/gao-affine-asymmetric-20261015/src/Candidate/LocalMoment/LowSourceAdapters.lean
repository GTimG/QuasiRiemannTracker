import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorZeros
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.LocalMomentSourceAudit
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondNonexceptionalChosenBlock HeckePrimeRay HeckeDetectorZeros
open HeckeFiniteDeletion CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O

/-- The moving child character is τ.  The relative-slot base η₀ and the
fixed exclusion ideal internalQ Q η₀ remain independent of τ. -/
theorem canonical_all_twists
    (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (τ η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (n : Fin 4 → ℤ) (z : O)
    (hz : (canonicalRadial τ (internalQ Q η₀) n).keep z)
    (F : NaturalRow τ z) :
    ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH (F.character.product η₀.inverse) θ).residue ≠ 1 := by
  exact natural_relative_twists M H hH F hz.1 η₀ Q hQM hz.2

/-- Removing Euler factors does not change any buffered maximum; this includes
height T and the sentinel 51/100, rather than only individual positive zeros. -/
theorem zeroMaximum_eq_of_mask {ι : Type*} [Fintype ι]
    (χ ψ : ι → Character)
    (hχ : ∀ i, (χ i).residue ≠ 1) (hψ : ∀ i, (ψ i).residue ≠ 1)
    (hm : ∀ i I, idealCoeff (χ i) I =
      if IsCoprime I (χ i).modulus then idealCoeff (ψ i) I else 0)
    (T : ℝ) : zeroMaximum χ hχ T = zeroMaximum ψ hψ T := by
  have he (i : ι) (s : ℂ) (hs : (51/100 : ℝ) ≤ s.re) :
      LFunction (χ i) s = 0 ↔ LFunction (ψ i) s = 0 := by
    have hs0 : 0 < s.re := by linarith
    rw [LFunction_eq_of_mask_nonprincipal (χ i) (ψ i) (hm i) (hχ i) hs0,
      mul_eq_zero]
    exact or_iff_left (factors_ne_zero (χ i).modulus (ψ i) hs0)
  apply le_antisymm
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with h | h
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T h
      have hr : (51/100 : ℝ) ≤ s.re := by rw [hs]; exact h.le
      have hh := zero_re_le_maximum ψ hψ T i hr ht ((he i s hr).mp hz)
      simpa only [hs] using hh
    · exact h.trans (zeroMaximum_bounds ψ hψ T).1
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum ψ hψ T) with h | h
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained ψ hψ T h
      have hr : (51/100 : ℝ) ≤ s.re := by rw [hs]; exact h.le
      have hh := zero_re_le_maximum χ hχ T i hr ht ((he i s hr).mpr hz)
      simpa only [hs] using hh
    · exact h.trans (zeroMaximum_bounds χ hχ T).1

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
    convert hp using 1 <;> dsimp only [F] <;> ring

/-- Canonical children have an exact width, possibly smaller than the nominal
ledger width.  Pay width and defect together instead of dropping that deficit. -/
theorem width_plus_low_defect (d F pad rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) (hpad : 0 ≤ pad) (hd : d ≤ pad) :
    d + rate*max (F-d) 0 ≤ pad + rate*max F 0 := by
  by_cases h : 0 ≤ F-d
  · rw [max_eq_left h]
    by_cases hf : 0 ≤ F
    · rw [max_eq_left hf]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hf)]
      nlinarith
  · rw [max_eq_right (le_of_not_ge h)]
    have hnn : 0 ≤ rate*max F 0 := mul_nonneg hrate0 (le_max_right _ _)
    linarith

#print axioms canonical_all_twists
#print axioms zeroMaximum_eq_of_mask
#print axioms greedy_low_selection
#print axioms width_plus_low_defect
end SevenEighths.LocalMomentSourceAudit
end
end OAI
