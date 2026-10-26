import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionSlots
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open Filter

/-- Fixed pointwise constants and a sufficiently small additive high-slot
loss fit the per-width cap required by the amplitude bins. -/
theorem eventually_amplitude_cap (C ε bw wmin : ℝ) (hbw : 0<bw) (hmin : 0<wmin)
    (hε : ε≤bw*wmin) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀δ w : ℝ,wmin≤w→∀A : ℂ,
      ‖A‖^2≤C*Z^(δ*w+ε)→‖A‖≤(Z^w)^(δ/2+bw) := by
  have hconst : ∀ᶠZ : ℝ in atTop,C≤Z^(bw*wmin):=
    (tendsto_rpow_atTop (mul_pos hbw hmin)).eventually (eventually_ge_atTop C)
  filter_upwards [hconst,eventually_gt_atTop (1:ℝ)] with Z hC hZ
  refine ⟨hZ,?_⟩
  intro δ w hw A hA
  have hZp : 0<Z:=zero_lt_one.trans hZ
  have hpow : ((Z^w)^(δ/2+bw))^2=Z^((δ+2*bw)*w) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Real.rpow_nonneg hZp.le w),←Real.rpow_mul hZp.le]
    congr 1
    ring
  have hs : ‖A‖^2≤((Z^w)^(δ/2+bw))^2 := by
    rw [hpow]
    calc
      _≤C*Z^(δ*w+ε):=hA
      _≤Z^(bw*wmin)*Z^(δ*w+ε):=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
      _=Z^(bw*wmin+(δ*w+ε)) := (Real.rpow_add hZp _ _).symm
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith [mul_le_mul_of_nonneg_left hw hbw.le])
  have hp : 0≤(Z^w)^(δ/2+bw):=Real.rpow_nonneg (Real.rpow_nonneg hZp.le _) _
  nlinarith [norm_nonneg A]

theorem slot_cap_of_nearby (A Q : ℂ) (E : ℝ)
    (hA : (max 1 ‖A‖)^2≤E) (hclose : ‖Q-A‖≤1/2) :
    (max 1 ‖Q‖)^2≤4*E := by
  have hq:=Deletion26.max_amplitude_of_deletion_error hclose
  have hp : 0≤ max (1:ℝ) ‖A‖:=le_trans zero_le_one (le_max_left _ _)
  have hq0 : 0≤ max (1:ℝ) ‖Q‖:=le_trans zero_le_one (le_max_left _ _)
  nlinarith

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
