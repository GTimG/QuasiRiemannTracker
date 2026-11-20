/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual transport at Q with its genuine supported floor discharged. -/
import Candidate.C092.transport.SelectedFloorEstimate

noncomputable section
set_option autoImplicit false
open scoped Classical
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedFloorEstimate
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Every admissible fixed height has literal SelectedTransport. Its source,
slots, padding, and positive saving precede every live character. -/
theorem selected_transport
    (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D)
    (padding : ℝ) (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta)
    (tau : ℝ) (htau : HeightAdmissible D P tau) :
    ∃ n : ℕ, 0 < n ∧ ∀ η : Character,
      SelectedTransport D F padding tau P.sigma n η := by
  have hp : padding ≤ 1/1000000000000 := hpadSmall.trans (by
    norm_num [Cycle090.rowPad, pow_succ])
  have hpad : padding+2*D.t ≤ 1/10000000000 := by linarith [P.t_padding]
  have heq : Cycle090.rowPad =
      QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension := by
    norm_num [Cycle090.rowPad,
      QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension, pow_succ]
  apply SelectedActualTransport.selected_transport_of_floor D F P padding tau hpadding hpadSmall htau.1 hbeta
  intro n hn η
  exact floor_bound D F P padding hpadding hpad (heq ▸ hpadSmall) hbeta tau htau n η

/-- An admissible positive height exists before both the finite label budget
and the live character. No analytic floor or finite-numerator premise occurs. -/
theorem exists_selected_transport
    (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D)
    (padding : ℝ) (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta) :
    ∃ tau : ℝ, 0 < tau ∧ ∃ n : ℕ, 0 < n ∧ ∀ η : Character,
      SelectedTransport D F padding tau P.sigma n η := by
  obtain ⟨tau, htau⟩ := exists_height D P
  exact ⟨tau, htau.1, selected_transport D F P padding hpadding hpadSmall hbeta tau htau⟩

end QRH.Cycle092.SelectedFloorEstimate
#print axioms QRH.Cycle092.SelectedFloorEstimate.selected_transport
#print axioms QRH.Cycle092.SelectedFloorEstimate.exists_selected_transport
