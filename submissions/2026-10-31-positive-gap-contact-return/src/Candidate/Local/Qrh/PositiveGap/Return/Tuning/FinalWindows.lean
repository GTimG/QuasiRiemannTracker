/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module FinalWindows (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): namespace QRH.SilDensitySplit.Return; the windows come from the generated `Windows.lean` -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
/- Modified by ArviFoxy (2026-10-29): forked into Submissions.arvi_return_tuning, namespace QRH.ArviDensity.Return.Tuning, over the reflective windows and edge covers of this package (`w.toAdmitted` written as `ReturnCountWindow.toAdmitted w`). -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.AdmittedWindow
import Candidate.Local.Qrh.PositiveGap.Return.CountWidth
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.Windows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PositiveGap.Return.Tuning
open QRH.Record1252270103Return QRH.PositiveGap.ReturnTuning
noncomputable section


def ReturnCountWindow.toAdmitted (w:ReturnCountWindow) : AdmittedWindow (naturalK/6) where
 B := branchB w.branch
 lam := branchL w.branch
 cap := branchZ w.branch
 sourceCap := branchCap w.branch
 mLo := witnessLower w.branch
 mHi := naturalM
 lam_gt_one := branch_lambda_gt_one w.branch w.nonold
 mLo_nonneg := witnessLower_nonneg w.branch
 mHi_lo := natural_join_bounds.1
 mHi_hi := natural_join_bounds.2
 cap_le_source := (branch_cap_bounds w.branch w.nonold).1
 cap_small := (branch_cap_bounds w.branch w.nonold).2.1
 value := branchCount w.branch
 cutoff := branchCutoff w.branch
 crossing := branchInverse w.branch
 deltaLo := w.deltaLo
 deltaHi := w.deltaHi
 pLo := w.pLo
 deltaBounds := w.deltaBounds
 pBounds := w.pBounds
 cutoff_bounds := by
  intro δ p hd hp
  obtain ⟨_,_,hl,hh,_⟩ := admitted_witness_ranges w.branch w.nonold (w.certificate hd hp)
  exact ⟨hl.le,by linarith⟩
 inverse_bounds := by
  intro δ p hd hp
  obtain ⟨_,_,_,_,hl,hh,_⟩ := admitted_witness_ranges w.branch w.nonold (w.certificate hd hp)
  exact ⟨hl.le,hh.le⟩
 plain_buffer := by
  intro δ p hd hp
  exact admitted_buffered_plain w.branch w.nonold (w.certificate hd hp) le_rfl
 inverse_crossing := by
  intro δ p hd hp
  have hg := admitted_witness_ranges w.branch w.nonold (w.certificate hd hp)
  exact inverse_at_branch_crossing w.branch w.nonold hg.1 hg.2.1
 plain_crossing := by
  intro δ p hd hp
  have hg := admitted_witness_ranges w.branch w.nonold (w.certificate hd hp)
  have hm : branchCutoff w.branch δ p-branchInverse w.branch δ p=branchPlain w.branch δ p := by
   linarith [branch_lengths w.branch hg.1 hg.2.1]
  rw [hm]
  exact branch_plain_crossing w.branch w.nonold (w.deltaBounds.1.trans hd.1)
   (w.pBounds.1.trans hp.1) (w.certificate hd hp)
 natural_tail := by
  intro δ p hd hp
  exact admitted_natural_tail w.branch w.nonold (w.certificate hd hp)
 widths := by
  intro δ p hd hp ν hν
  exact admitted_widths w.branch w.nonold (w.certificate hd hp) hν
 long_crossing := by
  intro δ p hd hp
  exact long_at_branch_crossing w.branch w.nonold (admitted_witness_ranges w.branch w.nonold (w.certificate hd hp)).2.1
 antitone := w.antitone

def finalAdmittedWindows : List (AdmittedWindow (naturalK/6)) :=
 returnWindows.map ReturnCountWindow.toAdmitted
end
end QRH.PositiveGap.Return.Tuning
