/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One genuine Mellin profile bank for the original and independently shortened
ordinary columns, selected before zero bands, rows, heights or late tau. -/
import Candidate.C092.transport.TerminalActualRowShort
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicProfiles
set_option autoImplicit false
namespace QRH.Cycle092.TerminalActualRow
noncomputable section
open scoped Classical ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeDetectorDyadicProfiles

def shortProfile (V W : ℝ→ℂ) (opened : Bool) (Dstar D : ℝ) : ℝ→ℂ :=
  if opened then HeckeDetectorDyadicBridge.inverseProfile V W Dstar D else W

/-- Every Mellin order has a fixed positive bound BEFORE any actual band,
frequency, row or cofactor/rectangular choice. Both original and opened
profiles retain the literal W support and smoothness. -/
theorem actual_short_profile_bank (V W : ℝ→ℂ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (A B : ℝ) (hA : 0< A) (hs : Function.support W⊆Icc A B) :
    ∃ bound : ℕ→ℝ,(∀j,0< bound j) ∧
    ∀(opened : Bool) (Dstar D : ℝ),0< Dstar → 0≤ D → D≤4*Dstar →
      Function.support (shortProfile V W opened Dstar D)⊆Icc A B ∧
      ContDiff ℝ ∞ (shortProfile V W opened Dstar D) ∧
      ∀j : ℕ,∀a ez : ℝ,51/100≤ a → a≤7/8 → 0< ez → ez<1/1000 →
      ∀sigma∈Icc (1-a-6*ez) 2,∀t : ℝ,
        (1+|t|)^j*‖mellin (shortProfile V W opened Dstar D) ((sigma:ℂ)+t*Complex.I)‖≤ bound j := by
  obtain ⟨bound,hbound,hplain,hopened⟩:=exists_profile_bounds V W hV hW A B hA hs (-1) 2
  refine ⟨bound,hbound,?_⟩
  intro opened Dstar D hDs hD hDcap
  have harg {a ez sigma : ℝ} (ha : 51/100≤ a) (ha' : a≤7/8) (he : 0< ez) (he' : ez<1/1000)
      (hsigma : sigma∈Icc (1-a-6*ez) 2) : sigma∈Icc (-1:ℝ) 2 := by
    constructor <;> linarith only [hsigma.1,hsigma.2,ha,ha',he,he']
  cases opened with
  | false =>
    refine ⟨hs,hW,?_⟩
    intro j a ez ha ha' he he' sigma hsigma t
    exact hplain j sigma (harg ha ha' he he' hsigma) t
  | true =>
    refine ⟨?_,?_,?_⟩
    · exact (by
        rw [shortProfile,if_pos rfl,inverseProfile_eq_ratio]
        exact (ratioProfile_support V W (D/Dstar)).trans hs)
    · rw [shortProfile,if_pos rfl,inverseProfile_eq_ratio]
      unfold ratioProfile
      fun_prop
    · intro j a ez ha ha' he he' sigma hsigma t
      exact hopened j Dstar D hDs hD hDcap sigma (harg ha ha' he he' hsigma) t

end
end QRH.Cycle092.TerminalActualRow
#print axioms QRH.Cycle092.TerminalActualRow.actual_short_profile_bank
