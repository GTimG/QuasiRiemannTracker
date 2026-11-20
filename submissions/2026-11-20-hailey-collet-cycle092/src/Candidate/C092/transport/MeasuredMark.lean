/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A large observed response forces a real slot of uniformly positive width. -/
import Candidate.C092.transport.SelectedMark
import Candidate.C092.transport.LowActualResponse
namespace QRH.Cycle092.MeasuredMark
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily CenteredMomentSourceMass
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O

theorem trivial_sq {N : ℕ} (d : SelectedSlotData N) {Z mesh B : ℝ} (hd : d.Bounded Z mesh B)
    (hZ : 0 < Z) (j : Fin N) (z : O) : ‖d.polynomial j z‖^2 ≤ (256*B)*Z^(d.width j) := by
  have hh : d.sources j ⊆ idealBall (2*Z^(d.width j)) := fun I hi =>
    (mem_idealBall _ I).mpr ⟨hd.source_nonzero j I hi,hd.source_norm j I hi⟩
  have hc := (show ((d.sources j).card:ℝ) ≤ (idealBall (2*Z^(d.width j))).card by exact_mod_cast Finset.card_le_card hh).trans (idealBall_card _ (by positivity))
  have hn : ‖d.polynomial j z‖ ≤ ∑ I ∈ d.sources j, ‖d.coefficient j I‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum; intro I _; rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (idealRowHom_norm _ _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (d.sources j) (fun _ => (1:ℝ)) (fun I => ‖d.coefficient j I‖)
  simp only [one_mul,one_pow,Finset.sum_const, nsmul_eq_mul,mul_one] at hcs
  calc
    _ ≤ (∑ I ∈ d.sources j, ‖d.coefficient j I‖)^2 := by gcongr
    _ ≤ _ := hcs
    _ ≤ (128*(2*Z^(d.width j)))*B := mul_le_mul hc (hd.coefficient_mass j) (by positivity) (by positivity)
    _ = _ := by ring

theorem exists_wide {N : ℕ} (d : SelectedSlotData N) {Z mesh B pay b : ℝ}
    (hd : d.Bounded Z mesh B) (hZ : 1 < Z) (hb : 0 < b) (hp : 1 ≤ pay)
    (hpay : (256*B)*Z^b ≤ pay) (z : O)
    (h : 5002/10000 < LowActual.response Z pay d.width (fun j => ‖d.polynomial j z‖^2)) :
    ∃ j, b ≤ d.width j ∧ Z^((5001/10000:ℝ)*d.width j) ≤ ‖d.polynomial j z‖^2 := by
  have hnot : ¬ ∀ j, LowActual.slotResponse Z pay (d.width j) (‖d.polynomial j z‖^2) ≤ 5002/10000 := by
    intro ha; exact h.not_ge ((LowActual.response_le_iff ..).2 ⟨by norm_num,ha⟩)
  obtain ⟨j,hj⟩ := Classical.not_forall.mp hnot
  have hw : 0 < d.width j := lt_of_le_of_ne (hd.width_nonneg j) (by intro he; apply hj; norm_num [←he,LowActual.slotResponse])
  have hh := lt_of_not_ge (fun ha => hj ((LowActual.slotResponse_le_iff hZ (zero_lt_one.trans_le hp) hw (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 5002/10000)).2 ha))
  have hone : 1 ≤ Z^((5002/10000:ℝ)*d.width j) := Real.one_le_rpow hZ.le (mul_nonneg (by norm_num) hw.le)
  have hBp : 0 ≤ B := (show 0 ≤ ∑ I ∈ d.sources j, ‖d.coefficient j I‖^2 by positivity).trans (hd.coefficient_mass j)
  refine ⟨j,?_,?_⟩
  · by_contra! hs
    have ha := (trivial_sq d hd (zero_lt_one.trans hZ) j z).trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hs.le) (by positivity : 0 ≤ 256*B)).trans hpay)
    exact (not_lt_of_ge ha) ((le_mul_of_one_le_right (zero_le_one.trans hp) hone).trans_lt hh)
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith : (5001/10000:ℝ)*d.width j ≤ (5002/10000:ℝ)*d.width j)).trans ((le_mul_of_one_le_left (by positivity) hp).trans hh.le)

#print axioms exists_wide
end
end QRH.Cycle092.MeasuredMark
