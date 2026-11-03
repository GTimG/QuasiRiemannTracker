/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/TunedData.lean
Original SHA-256: 4826da8ca95f201a372cd90efd74c1dd4826024560fbcf02cf1000ca23b59d88
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.Parameters
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.EnergyMesh

/-!
# Complete tuned high-side scalar data

The reserved high loss and capacity are fixed first. The energy mesh is
therefore fixed before K. The slot construction allows any prior lower
bound on K. The positive allowance may depend on the later contradiction
gap; it only affects post-slot errors, not the selected slots.
-/

namespace LW56e2.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators

abbrev reservedLoss : ℝ := 1 / 1000000000000000
noncomputable def conductorCap : ℝ := TunedCandidate.h + TunedCandidate.zeta + 2 * reservedLoss

lemma reservedLoss_pos : 0 < reservedLoss := by norm_num
lemma reservedLoss_le_one : reservedLoss ≤ 1 := by norm_num
lemma conductorCap_pos : 0 < conductorCap := by
  norm_num [conductorCap, TunedCandidate.h, TunedCandidate.hAt, TunedCandidate.ell,
    Geometry.ell, TunedCandidate.p, TunedCandidate.b, TunedCandidate.zeta]
lemma conductorCap_le_one : conductorCap ≤ 1 := by
  norm_num [conductorCap, TunedCandidate.h, TunedCandidate.hAt, TunedCandidate.ell,
    Geometry.ell, TunedCandidate.p, TunedCandidate.b, TunedCandidate.zeta]
lemma conductorCap_ge_dmin : (1 / 200 : ℝ) ≤ conductorCap := by
  norm_num [conductorCap, TunedCandidate.h, TunedCandidate.hAt, TunedCandidate.ell,
    Geometry.ell, TunedCandidate.p, TunedCandidate.b, TunedCandidate.zeta]
lemma conductorCap_supply : (7 / 37 : ℝ) * conductorCap ≤ TunedCandidate.ell := by
  norm_num [conductorCap, TunedCandidate.h, TunedCandidate.hAt, TunedCandidate.ell,
    Geometry.ell, TunedCandidate.p, TunedCandidate.b, TunedCandidate.zeta]

structure TunedData (Kmin : ℕ) (allowance : ℝ) where
  K : ℕ
  K_large : Kmin ≤ K
  K_pos : 0 < K
  K_even : Even K
  ell : Fin K → ℝ
  ellMin : ℝ
  rmin : ℝ
  ellMin_eq : ellMin = TunedCandidate.ell / (2 * K)
  rmin_eq : rmin = ellMin / conductorCap
  ellMin_pos : 0 < ellMin
  rmin_pos : 0 < rmin
  slots_injective : Function.Injective ell
  slots_sum : (∑ j, ell j) = TunedCandidate.ell
  slots_pos : ∀ j, 0 < ell j
  slots_lower : ∀ j, ellMin ≤ ell j
  slots_upper : ∀ j, ell j ≤ (1 / 200 : ℝ) * reservedLoss
  slots_fine : ∀ j, ell j ≤ plainMesh reservedLoss / 200
  P : DetectorScales reservedLoss K rmin ellMin allowance

theorem exists_tuned_data (Kmin : ℕ) (allowance : ℝ) (ha : 0 < allowance) :
    Nonempty (TunedData Kmin allowance) := by
  have htotal : 0 < TunedCandidate.ell := by
    norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]
  let cap := min (reservedLoss / 200) (plainMesh reservedLoss / 200)
  have hcap : 0 < cap := lt_min (by norm_num) (div_pos (plainMesh_pos reservedLoss_pos) (by norm_num))
  obtain ⟨K, hKmin, hK, hEven, hcapK⟩ := fine_even_slot_count cap hcap Kmin
  let ell := Classical.choose (distinct_slots_for_size TunedCandidate.ell htotal K hK)
  have hell := Classical.choose_spec (distinct_slots_for_size TunedCandidate.ell htotal K hK)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  let ellMin := TunedCandidate.ell / (2 * K)
  let rmin := ellMin / conductorCap
  have hmin : 0 < ellMin := div_pos htotal (by positivity)
  have hr : 0 < rmin := div_pos hmin conductorCap_pos
  obtain ⟨P⟩ := exists_detector_scales_after_slots reservedLoss rmin ellMin allowance K
    reservedLoss_pos reservedLoss_le_one hr hmin ha
  refine ⟨{
    K := K, K_large := hKmin, K_pos := hK, K_even := hEven
    ell := ell, ellMin := ellMin, rmin := rmin
    ellMin_eq := rfl, rmin_eq := rfl, ellMin_pos := hmin, rmin_pos := hr
    slots_injective := hell.1, slots_sum := hell.2.1
    slots_pos := fun j => hmin.trans_le (hell.2.2 j).1
    slots_lower := fun j => (hell.2.2 j).1
    slots_upper := ?_, slots_fine := ?_, P := P }⟩
  · intro j
    have hb := ((hell.2.2 j).2.le.trans hcapK).trans (min_le_left _ _)
    change ell j ≤ reservedLoss / 200 at hb
    convert hb using 1 <;> ring
  · intro j
    exact ((hell.2.2 j).2.le.trans hcapK).trans (min_le_right _ _)

namespace TunedData
variable {Kmin : ℕ} {allowance : ℝ} (D : TunedData Kmin allowance)

lemma conductor_minimum : conductorCap * D.rmin = D.ellMin := by
  rw [D.rmin_eq]
  field_simp [conductorCap_pos.ne']

lemma slot_conductor_lower (j : Fin D.K) : conductorCap * D.rmin ≤ D.ell j := by
  rw [D.conductor_minimum]
  exact D.slots_lower j

lemma high_budget (heightCost : ℝ) (hh : heightCost ≤ reservedLoss) :
    (159 * D.P.ε + reservedLoss + reservedLoss + 7 * reservedLoss) + 2 * reservedLoss +
      (26 * D.P.e + (D.K + 8) * D.P.eps + reservedLoss + reservedLoss * TunedCandidate.ell) +
      (reservedLoss + heightCost + reservedLoss) + reservedLoss ≤ 3 / 4000000000000 := by
  have hc := D.P.central_budget
  have ht : (18 : ℝ) * reservedLoss ≤ 3 / 4000000000000 := by norm_num
  calc
    _ ≤ (159 * D.P.ε + reservedLoss + reservedLoss + 7 * reservedLoss) + 2 * reservedLoss +
      (26 * D.P.e + (D.K + 8) * D.P.eps + reservedLoss + reservedLoss * TunedCandidate.ell) +
      (reservedLoss + reservedLoss + reservedLoss) + reservedLoss := by gcongr
    _ ≤ 18 * reservedLoss := hc
    _ ≤ 3 / 4000000000000 := ht

lemma principal_budget : D.P.sigma + reservedLoss / 8 ≤ 1 / 4000 := by
  have hs := D.P.sigma_t
  norm_num at hs ⊢
  linarith

lemma geometric_budget : D.P.sigma + 8 * D.P.e + reservedLoss / 8 ≤ 1 / 20 := by
  have hs := D.P.sigma_t
  have he := D.P.e_small
  norm_num at hs ⊢
  linarith

lemma window_budget : D.P.sigma + D.P.e ≤ TunedCandidate.B * D.ellMin := by
  have hB : (1 / 2 : ℝ) ≤ TunedCandidate.B := by rw [TunedCandidate.boundary_value]; norm_num
  have hs := D.P.sigma_slot
  have he := D.P.e_slot
  have hh := mul_le_mul_of_nonneg_right hB D.ellMin_pos.le
  linarith

lemma floor_budget : 26 * D.P.e + (D.K + 8) * D.P.eps + reservedLoss +
    reservedLoss * TunedCandidate.ell + reservedLoss / 8 + D.P.sigma ≤ 1 / 200 := by
  have hc := D.P.central_budget
  have hs := D.P.sigma_t
  have hε := D.P.epsilon_pos
  norm_num at hc hs ⊢
  linarith

lemma central_saving : D.P.sigma + reservedLoss / 8 + reservedLoss / 8 ≤ reservedLoss := by
  have hs := D.P.sigma_t
  norm_num at hs ⊢
  linarith

end TunedData
end
end LW56e2.Transport.PhysicalHigh
