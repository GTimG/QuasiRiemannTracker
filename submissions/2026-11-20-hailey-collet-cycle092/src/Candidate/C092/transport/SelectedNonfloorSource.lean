/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact common-degree/height/grid quantifiers for the genuine pointwise source.
This is a conditional analytic assembly, not a proof that the source exists. -/
import Candidate.C092.transport.SelectedNonfloorMixed
import Candidate.C092.transport.SelectedFloorEstimateTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The true residual pointwise source contract. A single finite degree comes
BEFORE the physical height exponent, which comes before EVERY later positive
truncation order. This source has no normalization, physical energy, integral,
probe or endpoint field. Its actual existence is not asserted here. -/
def PointwisePacketSource (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D)
    (padding saving allowance source : ℝ) (η : Character) : Prop :=
  ∃ degree : ℝ, 0 ≤ degree ∧ ∀ tau : ℝ,
    SelectedFloorEstimate.HeightAdmissible D P tau →
    2*tau*(1+degree+2*P.eps) ≤ allowance →
    ∀ n : ℕ, 0 < n → PointwisePacketCells D F padding tau saving allowance P.eps degree source n η

/-- Exact original transport/numerator data for every fixed presented
character, from only the finer pointwise packet/source/count contract. Both
positive savings are fixed before eta; no floor or transport input remains. -/
theorem finite_data_of_pointwise_source (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding saving allowance source : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hsaving : saving ≤ 1) (hallowance : 0 < allowance)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta)
    (hsource : ∀ η : Character, PointwisePacketSource D F P padding saving allowance source η) :
    ∀ η : Character, ∃ tau : ℝ, 0 < tau ∧ ∃ n : ℕ, 0 < n ∧
      SelectedTransport D F padding tau P.sigma n η ∧
      FiniteNumeratorBound D F padding tau saving n η := by
  have hp : padding ≤ 1/1000000000000 := hpadSmall.trans (by
    norm_num [Cycle090.rowPad, pow_succ])
  have hpad : padding+2*D.t ≤ 1/10000000000 := by linarith [P.t_padding]
  have hupper : Geometry.h+padding ≤ 1 := by
    have hh := ActualGeometry.WidenedCoreBounds.h_interval.2
    linarith
  have heq : Cycle090.rowPad =
      QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension := by
    norm_num [Cycle090.rowPad,
      QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension, pow_succ]
  intro η
  obtain ⟨degree, hdegree, hpacket⟩ := hsource η
  obtain ⟨tau, htau, hheight⟩ := exists_joint_height D P allowance degree hallowance hdegree
  obtain ⟨n, hn, htransport⟩ := SelectedFloorEstimate.selected_transport D F P padding hpadding hpadSmall hbeta tau htau
  refine ⟨tau, htau.1, n, hn, htransport η, ?_⟩
  exact finite_numerator_of_pointwise_packets D F padding tau saving allowance P.eps degree source
    hpadding hpad htau.1 hsaving hallowance P.eps_pos hdegree hheight hupper
    (heq ▸ hpadSmall) hbeta n η (hpacket tau htau hheight n hn)

/-- The ONLY missing analytic input is now the genuine pointwise packet
source on the actual rows. Once supplied in the contrary case, it provides the
literal ActualFiniteInput consumed by the checked ordinary/Hecke probe proof. -/
theorem actual_finite_of_pointwise_source (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding saving allowance : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hsaving : 0 < saving) (hsavingSmall : saving ≤ 1) (hallowance : 0 < allowance)
    (hsource : Geometry.theta < HeckeZeroSupremum.beta →
      ∀ η : Character, PointwisePacketSource D F P padding saving allowance Cycle090.sourceCost η) :
    ActualFiniteInput := by
  intro hgap
  exact ⟨D, F, padding, P.sigma, saving, hpadding, P.sigma_pos, hsaving,
    finite_data_of_pointwise_source D F P padding saving allowance Cycle090.sourceCost hpadding hpadSmall
      hsavingSmall hallowance hgap.le (hsource hgap)⟩

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.finite_data_of_pointwise_source
#print axioms QRH.Cycle092.SelectedNonfloor.actual_finite_of_pointwise_source
