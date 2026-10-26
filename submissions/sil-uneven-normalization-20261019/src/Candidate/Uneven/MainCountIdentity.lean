/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Target830.Count.Arithmetic

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.MainCount
noncomputable section
open Target830.Count

/-- The old count is the same affine rational expression at B=1, lambda=6*kappa.
This identity applies at each frozen incumbent used by the two new stages. -/
theorem old_count_affine {κ d p : ℝ} (hk : 7/10 ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    oldCount κ d p = affineR (6*κ) 1 d p := by
  have hk0 : 0 < κ := by linarith
  let D := 3-p-2*p/(3*κ)
  let P := 2*(1-p)*(1-p/(3*κ))
  let J := (5/6-d)*D+d*P
  have hv : 2*p/(3*κ) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 3*κ)).mpr
    linarith [hp.2]
  have hD : 0 < D := by dsimp [D]; linarith [hp.2]
  have hv' : p/(3*κ) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 3*κ)).mpr
    linarith [hp.2]
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [hp.2])) (by linarith)
  have hJ : 0 < J := by
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith [hd.2]) hD)
      (mul_nonneg hd.1 hP)
  have he : (5/6-d)+d*(P/D)=J/D := by
    dsimp [J]
    field_simp
  have hL : affineJ (6*κ) d p=J := by
    dsimp [affineJ,affineD,affineA,J,D,P]
    field_simp
    <;> ring
  unfold oldCount Cycle63.Arithmetic.Bernstein.countingR0
    Cycle63.Arithmetic.Bernstein.rowDen
  rw [Cycle63.Arithmetic.Bernstein.canonical_counting_formula hk]
  change 1-d+d*(P/D)*(5/6-d)/(2*((5/6-d)+d*(P/D))) = _
  rw [he]
  unfold affineR
  rw [hL]
  dsimp [affineU,affineC,P]
  field_simp [hD.ne',hJ.ne',hk0.ne']
  <;> ring

end
end OAI.SevenEighths.MainCount
