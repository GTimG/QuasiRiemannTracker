/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCountConcrete

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.MainCount
noncomputable section
open Target830.Count

theorem old_count_mono {a κ d p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    oldCount a d p ≤ oldCount κ d p := by
  have hk := ha.trans hak
  have hc := Cycle63.Arithmetic.Bernstein.counting_gap ha hak hp
  have hSa := Cycle63.Arithmetic.Bernstein.rowDen_pos ha hd hp
  have hSk := Cycle63.Arithmetic.Bernstein.rowDen_pos hk hd hp
  have hid : oldCount κ d p-oldCount a d p =
      (d*((5/6:ℝ)-d)^2/
        (2*Cycle63.Arithmetic.Bernstein.rowDen κ d p*Cycle63.Arithmetic.Bernstein.rowDen a d p))*
        (Cycle63.Arithmetic.Bernstein.countingCoefficient κ p-
          Cycle63.Arithmetic.Bernstein.countingCoefficient a p) := by
    unfold oldCount Cycle63.Arithmetic.Bernstein.countingR0
    field_simp [hSa.ne',hSk.ne']
    simp only [Cycle63.Arithmetic.Bernstein.rowDen]
    ring
  apply sub_nonneg.mp
  rw [hid]
  exact mul_nonneg (div_nonneg (mul_nonneg hd.1 (sq_nonneg _)) (by positivity)) hc.1

theorem envelope_mono {base : ℝ → ℝ → ℝ → ℝ} (bs : List Branch)
    {a κ d p : ℝ} (hb : base a d p ≤ base κ d p) :
    finiteEnvelope base bs a d p ≤ finiteEnvelope base bs κ d p := by
  induction bs with
  | nil => exact hb
  | cons b bs ih =>
    simp only [finiteEnvelope]
    split_ifs
    · exact min_le_min_left _ ih
    · exact ih

theorem count_mono (stage : Stage) {a κ d p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    count stage a d p ≤ count stage κ d p := by
  apply envelope_mono (branches stage)
  exact envelope_mono Target830.Count.branches (old_count_mono ha hak hd hp)

end
end OAI.SevenEighths.MainCount
