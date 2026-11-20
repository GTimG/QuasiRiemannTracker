/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One positive height below both the original floor and packet degree budgets. -/
import Candidate.C092.transport.SelectedNonfloorPointwise
import Candidate.C092.transport.SelectedFloorEstimate

noncomputable section
set_option autoImplicit false
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- After a finite common polynomial degree is fixed, one positive height
works before every later finite truncation order. It remains admissible for
the already-proved actual floor/transport. -/
theorem exists_joint_height (D : BaselineData) (P : TransportParameters D)
    (allowance degree : ℝ) (hallowance : 0 < allowance) (hdegree : 0 ≤ degree) :
    ∃ tau : ℝ, SelectedFloorEstimate.HeightAdmissible D P tau ∧
      2*tau*(1+degree+2*P.eps) ≤ allowance := by
  obtain ⟨tau0, htau0⟩ := SelectedFloorEstimate.exists_height D P
  let tau := min tau0 (allowance/(4*(1+degree+2*P.eps)))
  have he := P.eps_pos
  have hp : 0 < 1+degree+2*P.eps := by positivity
  have htau : 0 < tau := lt_min htau0.1 (by positivity)
  have hle : tau ≤ tau0 := min_le_left _ _
  have hbudget : tau*(4*(1+degree+2*P.eps)) ≤ allowance :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨tau, ⟨htau, ?_, ?_⟩, ?_⟩
  · have h := htau0.2.1
    linarith
  · have h := htau0.2.2
    have hm := mul_le_mul_of_nonneg_right hle (show 0 ≤ 1+2*P.eps by positivity)
    nlinarith
  · nlinarith

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.exists_joint_height
