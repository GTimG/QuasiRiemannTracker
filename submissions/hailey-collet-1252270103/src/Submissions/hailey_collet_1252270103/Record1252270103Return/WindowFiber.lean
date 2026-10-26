/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual finite row cardinality at an admitted capped or affine witness. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.AdmittedWindow
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Return
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths QRH.Record12518109Count
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber Cycle25DetectorBranchBudget
open Cycle25DetectorRawFiber Cycle25DetectorRowCount

theorem count_fiber_at_window
 (M:Ideal O) [NeZero M] (H:Subgroup (O⧸M)ˣ)
 (hH:RayOrthogonality.globalUnits M≤H) (S:Finset (Ideal O))
 (φ:ℝ→ℝ) (hφ:ContDiff ℝ ∞ φ) (hφc:HasCompactSupport φ)
 (hφp:tsupport φ⊆Ioi 0) (hφ0:∀y,0≤φ y) (hφne:φ≠0)
 (a₀ b₀ B₀:ℝ) (ha₀:0<a₀) (hab₀:a₀≤b₀) (hB₀:0<B₀)
 (hφs:Function.support φ⊆Ioo a₀ b₀) (hφB:∀y,φ y≤B₀)
 (εm:ℝ) (hεm:0<εm) :
 ∃c κ K₀:ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU:ℝ in atTop,
 ∀naturalκ:ℝ,7/10≤naturalκ → naturalκ≤3/4 →
 ∀w:AdmittedWindow naturalκ,∀(a ε tstar T allowance ν C height:ℝ) (i:ℕ),
 1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
 0<ν → ν≤1/10000000 → 0≤C → 0≤height →
 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
 ∀{Label Slot:Type} (F:Fiber M H Label Slot U a ε tstar T allowance i),
 w.Available (2*a-1) (F.q/(2*a-1)) →
 tstar=w.cutoff (2*a-1) (F.q/(2*a-1)) →
 Cycle25DetectorRawFiber.Moments F naturalκ c κ C height εm →
 AffineMarkedMoment F w.face C height εm →
 (F.rows.card:ℝ)≤fiberConstant C height K₀*
  U^(w.value (2*a-1) (F.q/(2*a-1))+159*ε+εm+F.mesh+7*ν) := by
 obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hh⟩ := count_from_piecewise_moments
  M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
 refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
 filter_upwards [hh] with U hh
 intro naturalκ hk hk1 w a ε tstar T allowance ν C height i hU ha hδhi hε hεhi hν hνhi hC hheight hfreq Label Slot F hg ht moments affine
 let δ:=2*a-1
 let p:=F.q/δ
 have ht1:1≤tstar := by rw [ht];exact (w.cutoff_bounds hg.1 hg.2).1
 have ht2:tstar≤3/2 := by rw [ht];exact (w.cutoff_bounds hg.1 hg.2).2
 have hcount := hh w.B w.lam w.cap w.sourceCap w.mLo w.mHi w.lam_gt_one
  w.mLo_nonneg w.mHi_lo w.mHi_hi w.cap_le_source w.cap_small
  a ε tstar T allowance naturalκ ν C height i hU ha hδhi hε (by linarith)
  ht1 ht2 hk hk1 hν (by linarith) hC hheight hfreq F (w.crossing δ p) (w.value δ p)
  (w.inverse_bounds hg.1 hg.2).1 (w.inverse_bounds hg.1 hg.2).2
  (by rw [ht];linarith [w.plain_buffer hg.1 hg.2])
  (w.inverse_crossing hg.1 hg.2) (by simpa only [ht] using w.plain_crossing hg.1 hg.2)
  (w.natural_tail hg.1 hg.2) (w.widths hg.1 hg.2 ν hνhi) moments affine
 have hlong : 1-δ+(5/6-δ)*(tstar-1)=w.value δ p := by
  rw [ht];exact w.long_crossing hg.1 hg.2
 change (F.rows.card:ℝ)≤fiberConstant C height K₀*
  U^(max (w.value δ p) (1-δ+(5/6-δ)*(tstar-1))+159*ε+εm+F.mesh+7*ν) at hcount
 rw [hlong,max_self] at hcount
 exact hcount

end
end QRH.Record1252270103Return
#print axioms QRH.Record1252270103Return.count_fiber_at_window
