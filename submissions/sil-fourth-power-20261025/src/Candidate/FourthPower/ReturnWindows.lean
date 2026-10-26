/- Copyright (c) 2026 Sil. Apache-2.0.
exact interface to PR69's generic actual-count machinery.
No source theorem, moment bound or endpoint conclusion is assumed here.
Not imported into src and not Lean checked. -/
import Candidate.FourthPower.ReturnMonotone
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountScheme

set_option autoImplicit false
namespace Candidate.FourthPower.ReturnWindows
noncomputable section
open ReturnCertificate ReturnCountData ReturnFinite ReturnMonotone

/-- The fixed incumbent cap for improved branches, distinct from the variable
contrary kappa in the old count. This definition asserts no bound on beta. -/
def naturalKappa : ℝ := 2*incumbent-1

theorem natural_kappa_bounds : 7/10 ≤ naturalKappa ∧ naturalKappa ≤ 3/4 := by
  norm_num [naturalKappa, incumbent]

theorem plain_interval_bounds : 0 ≤ mMinus ∧ 2/5 ≤ mHigh ∧ mHigh < 1/2 := by
  norm_num [mMinus, mHigh, incumbentCost, incumbent, sMinus]

theorem natural_tail_width : (1-2*mHigh)/(6*naturalKappa) = sMinus := by
  norm_num [mHigh, incumbentCost, incumbent, naturalKappa, sMinus]

theorem branch_slope_gt_one (b : ImprovedBranch) : 1 < b.face.slope := by
  cases hr : b.role <;>
    norm_num [ImprovedBranch.face, roleFace, hr, countFace, physicalFace,
      xFace, yFace, sourceSlope, physicalSlope]

theorem branch_cap_bounds (b : ImprovedBranch) :
    eta < capWidth b ∧ capWidth b ≤ b.face.cap ∧ capWidth b ≤ 7/37 := by
  cases hr : b.role <;>
    norm_num [capWidth, ImprovedBranch.face, roleFace, hr, countFace,
      physicalFace, xFace, yFace, eta]

theorem plain_buffer (b : ImprovedBranch) {δ p : ℝ} (hg : Admitted b δ p) :
    mMinus+eta ≤ cutoff b δ p-inverse b δ p := by
  obtain ⟨hD,hJ,_,_,_,_,hm,_⟩ := admitted_witness_ranges b hg
  have hs := lengths b hD hJ
  have hl : mMinus+eta ≤ lowerM b := by
    by_cases hc : b.capped=true
    · simp [lowerM,hc]
    · simp only [lowerM,hc,if_false]
      exact le_max_left _ _
  linarith

/-- The whole continuation from mMinus through mHigh, not only its crossing. -/
theorem continuation_widths (b : ImprovedBranch) {δ p : ℝ}
    (hg : Admitted b δ p) {ν m : ℝ} (hν : ν ≤ eta) (hm : m ≤ mHigh) :
    ν < min (capWidth b) ((b.face.intercept-2*m)/b.face.slope) := by
  have hL : 0 < b.face.slope := improved_slope_positive b
  have hguard : 0 < b.face.intercept-2*mHigh-
      b.face.slope*(sMinus+eta)-2*eta := by
    simpa only [admissionGuard] using (hg ⟨13, by decide⟩)
  have hwidth : ν < (b.face.intercept-2*m)/b.face.slope := by
    apply (lt_div_iff₀ hL).2
    have hv := mul_le_mul_of_nonneg_right hν hL.le
    have hs := mul_nonneg hL.le (show 0 ≤ sMinus by norm_num [sMinus])
    have he : 0 < eta := by norm_num [eta]
    nlinarith
  exact lt_min (hν.trans_lt (branch_cap_bounds b).1) hwidth

/-- One concrete PR69 window for each of our seventeen checked admission boxes.
The six actual branch choices are inherited verbatim from ReturnFinite.window. -/
def admittedWindow (i : Fin 17) : QRH.Record1252270103Return.AdmittedWindow naturalKappa where
  B := (window i).branch.face.intercept
  lam := (window i).branch.face.slope
  cap := capWidth (window i).branch
  sourceCap := (window i).branch.face.cap
  mLo := mMinus
  mHi := mHigh
  lam_gt_one := branch_slope_gt_one _
  mLo_nonneg := plain_interval_bounds.1
  mHi_lo := plain_interval_bounds.2.1
  mHi_hi := plain_interval_bounds.2.2
  cap_le_source := (branch_cap_bounds _).2.1
  cap_small := (branch_cap_bounds _).2.2
  value := count (window i).branch
  cutoff := cutoff (window i).branch
  crossing := inverse (window i).branch
  deltaLo := (window i).deltaLo
  deltaHi := (window i).deltaHi
  pLo := (window i).pLo
  deltaBounds := ⟨(window_bounds i).1,(window_bounds i).2.2.1⟩
  pBounds := ⟨(window_bounds i).2.2.2.1,(window_bounds i).2.2.2.2.le⟩
  cutoff_bounds := by
    intro δ p hδ hp
    obtain ⟨_,_,ht0,ht1,_,_,_,_⟩ :=
      admitted_witness_ranges _ (window_admitted i ⟨hδ,hp⟩)
    exact ⟨ht0.le,by linarith⟩
  inverse_bounds := by
    intro δ p hδ hp
    obtain ⟨_,_,_,_,hr0,hr1,_,_⟩ :=
      admitted_witness_ranges _ (window_admitted i ⟨hδ,hp⟩)
    exact ⟨hr0.le,hr1.le⟩
  plain_buffer := by
    intro δ p hδ hp
    exact plain_buffer _ (window_admitted i ⟨hδ,hp⟩)
  inverse_crossing := by
    intro δ p hδ hp
    have hg := admitted_witness_ranges _ (window_admitted i ⟨hδ,hp⟩)
    exact inverse_crossing _ hg.1 hg.2.1
  plain_crossing := by
    intro δ p hδ hp
    have hg := window_admitted i ⟨hδ,hp⟩
    have hr := admitted_witness_ranges _ hg
    have hs : cutoff (window i).branch δ p-inverse (window i).branch δ p =
        plain (window i).branch δ p := by
      linarith [lengths (window i).branch hr.1 hr.2.1]
    have hδ0 : 0 ≤ δ := (window_bounds i).1.trans hδ.1
    have hp0 : 0 ≤ p := (window_bounds i).2.2.2.1.trans hp.1
    rw [hs, QRH.Record1252270103Return.plainCurve_eq _ _ _ _ _ _ hδ0 hp0]
    simpa only [plainWidth] using (plain_crossing (window i).branch hg).le
  natural_tail := by
    intro δ p hδ hp
    have ht := admitted_tail (window i).branch (window_admitted i ⟨hδ,hp⟩)
    calc
      _ = 1-2*δ*mHigh-2*(δ*p)*((1-2*mHigh)/(6*naturalKappa)) := by ring
      _ = 1-2*δ*mHigh-2*δ*p*sMinus := by rw [natural_tail_width]; ring
      _ ≤ count (window i).branch δ p := ht.le
  widths := by
    intro δ p hδ hp ν hν m _hmlo hmhi
    exact continuation_widths _ (window_admitted i ⟨hδ,hp⟩) hν hmhi
  long_crossing := by
    intro δ p hδ hp
    have hg := admitted_witness_ranges _ (window_admitted i ⟨hδ,hp⟩)
    calc
      _ = 1/6+V δ*cutoff (window i).branch δ p := by dsimp only [V]; ring
      _ = count (window i).branch δ p := long_crossing _ hg.2.1
  antitone := by
    intro δ hδ
    apply admitted_count_antitone _ ((window_bounds i).1.trans hδ.1)
      (hδ.2.trans (window_bounds i).2.2.1)
    intro p hp
    exact window_admitted i ⟨hδ,hp⟩

theorem admittedWindow_available (i : Fin 17) (δ p : ℝ) :
    (admittedWindow i).Available δ p ↔ (window i).Contains δ p := Iff.rfl

theorem admittedWindow_value (i : Fin 17) (δ p : ℝ) :
    (admittedWindow i).value δ p = count (window i).branch δ p := rfl

theorem admittedWindow_face (i : Fin 17) :
    (admittedWindow i).face = QRH.Record1252270103Return.broadFace
      (window i).branch.face.intercept (window i).branch.face.slope
      (window i).branch.face.cap := rfl

/-- Arithmetic assembly only: no natural moment or incumbent theorem is hidden
in this scheme. Those actual analytic inputs are required by its count theorem. -/
def countScheme : QRH.Record1252270103Return.CountScheme where
  naturalκ := naturalKappa
  natural_lo := natural_kappa_bounds.1
  natural_hi := natural_kappa_bounds.2
  windows := List.ofFn admittedWindow

theorem countScheme_window_count : countScheme.windows.length = 17 := by
  exact List.length_ofFn (f := admittedWindow)

end
end Candidate.FourthPower.ReturnWindows
