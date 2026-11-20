/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The authentic Geometry.Parameters interface is inherited from Collet's physical
return, with the original OpenAI, Akash Levy and Gao attributions retained by its
import. The widened five-field contract follows Joseph Bebel's Apache-2.0
BoundsCore adapter and Sil's coarse-box extension; no historical instance is used. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Submissions.hailey_collet_1252270103.Record1252270103Return.IntermediateGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Return.TransportGeometry
import Candidate.C092.Intake.QRH.Geometry
import Candidate.C092.Evidence.Cycle092CoarseGeometry

/-!
# Genuine upstream geometry at the Cycle092 Q parameters

Manuscript Q0 fixes h = h_* + .0022595743, not h = hLower. Its directed interval
is [.8175840773,.8175840793]. This module constructs genuine upstream parameters
for every h in that interval. Thus no endpoint substitutes for the actual h.
The separate widened coarse contract retains all five fields, with upper conductor
.818. No instance of the false historical .816 contract is constructed.
-/

set_option autoImplicit false
namespace QRH.Cycle092.ActualGeometry
noncomputable section
open QRH.Record1252270103Return

/-- The complete authentic upstream parameter record, throughout the directed Q interval. -/
@[instance_reducible] def parameters (h : ℝ)
    (hl : QRH.Cycle090.hLower ≤ h) (hu : h ≤ QRH.Cycle090.hUpper) : Geometry.Parameters where
  theta := QRH.Cycle090.theta
  ell := QRH.Cycle090.ell
  x := QRH.Cycle090.xLength h
  y := QRH.Cycle090.yLength h
  ell_pos := by norm_num [QRH.Cycle090.ell, QRH.Cycle090.theta]
  sixth_lt_ell := by norm_num [QRH.Cycle090.ell, QRH.Cycle090.theta]
  ell_lt_fifth := by norm_num [QRH.Cycle090.ell, QRH.Cycle090.theta]
  ell_lt_x := (QRH.Cycle090.physical_geometry hl hu).2.1
  x_lt_y := (QRH.Cycle090.physical_geometry hl hu).2.2.1
  y_lt_half := (QRH.Cycle090.physical_geometry hl hu).2.2.2.1
  x_add_y := QRH.Cycle090.physical_length_sum h
  dilation_gap := (QRH.Cycle090.physical_geometry hl hu).2.2.2.2.1
  tuple_margin_neg := QRH.Cycle090.gram_extra_negative h
  signal_boundary := by
    dsimp [QRH.Cycle090.xLength, QRH.Cycle090.yLength, QRH.Cycle090.ell]
    ring

/-- The upstream derived conductor equals the chosen h, exactly. -/
theorem parameters_h (h : ℝ) (hl : QRH.Cycle090.hLower ≤ h) (hu : h ≤ QRH.Cycle090.hUpper) :
    @Geometry.h (parameters h hl hu) = h := by
  change 1 + QRH.Cycle090.ell - QRH.Cycle090.xLength h = h
  dsimp [QRH.Cycle090.xLength]
  ring

/-- Every native length projection agrees with the manuscript's Q construction. -/
theorem parameter_projections (h : ℝ)
    (hl : QRH.Cycle090.hLower ≤ h) (hu : h ≤ QRH.Cycle090.hUpper) :
    @Geometry.theta (parameters h hl hu) = QRH.Cycle090.theta ∧
    @Geometry.ell (parameters h hl hu) = QRH.Cycle090.ell ∧
    @Geometry.x (parameters h hl hu) = QRH.Cycle090.xLength h ∧
    @Geometry.y (parameters h hl hu) = QRH.Cycle090.yLength h := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The actual native signal shift is minus the original physical normalization exponent. -/
theorem signalShift_eq (h : ℝ)
    (hl : QRH.Cycle090.hLower ≤ h) (hu : h ≤ QRH.Cycle090.hUpper) :
    @Geometry.signalShift (parameters h hl hu) = -QRH.Cycle090.kPhys h := by
  change -(4 + QRH.Cycle090.yLength h - QRH.Cycle090.xLength h) / 6 = _
  dsimp [QRH.Cycle090.kPhys, QRH.Cycle090.xLength, QRH.Cycle090.yLength]
  ring

/-- This is the genuine upstream signal at the exact advertised target. -/
theorem signal_at_target (h : ℝ)
    (hl : QRH.Cycle090.hLower ≤ h) (hu : h ≤ QRH.Cycle090.hUpper) :
    @Geometry.signal (parameters h hl hu) QRH.Cycle090.theta =
      QRH.Cycle090.theta - QRH.Cycle090.kPhys h := by
  unfold Geometry.signal
  rw [signalShift_eq]
  ring

/-- The five retained coarse obligations, with Q's necessary .818 upper conductor. -/
class WidenedCoreBounds [Geometry.Parameters] : Prop where
  theta_bounds : 873 / 1000 < Geometry.theta ∧ Geometry.theta < 7 / 8
  h_interval : 793 / 1000 < Geometry.h ∧ Geometry.h < 818 / 1000
  ly_coarse : 458 / 1000 < Geometry.y ∧ Geometry.y < 473 / 1000
  ell_interval : 1672 / 10000 < Geometry.ell ∧ Geometry.ell < 175 / 1000
  small_saving : 7 / 100 < Geometry.y / 2 - Geometry.h * (17 / 50 - 1 / 6) - 1 / 50

/-- Every genuine Q parameter record satisfies the complete widened coarse box. -/
theorem widenedBounds (h : ℝ)
    (hl : QRH.Cycle090.hLower ≤ h) (hu : h ≤ QRH.Cycle090.hUpper) :
    @WidenedCoreBounds (parameters h hl hu) := by
  have hc := QRH.Cycle090.cycle092_coarse_geometry hl hu
  refine @WidenedCoreBounds.mk (parameters h hl hu) ?_ ?_ ?_ ?_ ?_
  · change 873 / 1000 < QRH.Cycle090.theta ∧ QRH.Cycle090.theta < 7 / 8
    exact hc.1
  · rw [parameters_h h hl hu]
    exact hc.2.1
  · change 458 / 1000 < QRH.Cycle090.yLength h ∧ QRH.Cycle090.yLength h < 473 / 1000
    exact hc.2.2.1
  · change 1672 / 10000 < QRH.Cycle090.ell ∧ QRH.Cycle090.ell < 175 / 1000
    exact hc.2.2.2.1
  · rw [parameters_h h hl hu]
    change 7 / 100 < QRH.Cycle090.yLength h / 2 - h * (17 / 50 - 1 / 6) - 1 / 50
    exact hc.2.2.2.2

/-- The new interval cannot provide the old .816 conductor field. -/
theorem not_old_conductor_field (h : ℝ)
    (hl : QRH.Cycle090.hLower ≤ h) (hu : h ≤ QRH.Cycle090.hUpper) :
    ¬ @Geometry.h (parameters h hl hu) < 816 / 1000 := by
  rw [parameters_h h hl hu]
  exact QRH.Cycle090.cycle092_not_old_conductor_bound hl

/-- The averaged-floor scalar margin remains valid throughout the widened coarse box. -/
theorem widened_floor_margin [Geometry.Parameters] [WidenedCoreBounds] {D : ℝ}
    (hD : D ≤ Geometry.h + 1 / 10000000000) :
    1 / 1000 < Geometry.theta -
      (51 / 100 - 49 / 150 * Geometry.h + 51 / 100 * Geometry.ell + 33 / 50 * D) -
      1 / 100000 - 1 / 1000000000000 := by
  have ht := WidenedCoreBounds.theta_bounds.1
  have hh := WidenedCoreBounds.h_interval.2
  have he := WidenedCoreBounds.ell_interval.2
  linarith

/-- Q's exact shift of the earlier contact conductor stays in the proved interval. -/
theorem shifted_contact_mem {hStar : ℝ}
    (hl : 815324503 / 1000000000 ≤ hStar) (hu : hStar ≤ 815324505 / 1000000000) :
    QRH.Cycle090.hLower ≤ hStar + 22595743 / 10000000000 ∧
      hStar + 22595743 / 10000000000 ≤ QRH.Cycle090.hUpper := by
  norm_num [QRH.Cycle090.hLower, QRH.Cycle090.hUpper]
  constructor <;> linarith

/-- The exact Q conductor, with its earlier contact enclosure, has genuine native geometry. -/
@[instance_reducible] def shiftedContactParameters (hStar : ℝ)
    (hl : 815324503 / 1000000000 ≤ hStar) (hu : hStar ≤ 815324505 / 1000000000) :
    Geometry.Parameters :=
  parameters (hStar + 22595743 / 10000000000) (shifted_contact_mem hl hu).1
    (shifted_contact_mem hl hu).2

/-- Exact lower endpoint data are checks of the interval family, not substitutions for h. -/
theorem lower_endpoint_values :
    QRH.Cycle090.ell = 65000809 / 375000000 ∧
    QRH.Cycle090.xLength QRH.Cycle090.hLower = 10672542401 / 30000000000 ∧
    QRH.Cycle090.yLength QRH.Cycle090.hLower = 14127392879 / 30000000000 := by
  norm_num [QRH.Cycle090.ell, QRH.Cycle090.theta, QRH.Cycle090.xLength,
    QRH.Cycle090.yLength, QRH.Cycle090.hLower]

end
end QRH.Cycle092.ActualGeometry

#print axioms QRH.Cycle092.ActualGeometry.parameters
#print axioms QRH.Cycle092.ActualGeometry.widenedBounds
#print axioms QRH.Cycle092.ActualGeometry.signal_at_target
#print axioms QRH.Cycle092.ActualGeometry.widened_floor_margin
#print axioms QRH.Cycle092.ActualGeometry.shiftedContactParameters
