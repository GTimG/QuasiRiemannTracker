/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One native transport order suffices after the common packet degree and height.
The packet supplier need not work at every positive natural number. -/
import Candidate.C092.transport.SelectedNonfloorSource

noncomputable section
set_option autoImplicit false
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- This is exactly a choice from the already proved floor/transport law.
It is chosen after tau, before the live character, scale, indices and cells.
It is a finite bin budget, not the separate Mellin tail-decay order. -/
def nativeTransportOrder (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding tau : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta)
    (htau : SelectedFloorEstimate.HeightAdmissible D P tau) : ℕ :=
  Classical.choose (SelectedFloorEstimate.selected_transport D F P padding
    hpadding hpadSmall hbeta tau htau)

theorem nativeTransportOrder_spec (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding tau : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta)
    (htau : SelectedFloorEstimate.HeightAdmissible D P tau) :
    0 < nativeTransportOrder D F P padding tau hpadding hpadSmall hbeta htau ∧
      ∀ η : Character, SelectedTransport D F padding tau P.sigma
        (nativeTransportOrder D F P padding tau hpadding hpadSmall hbeta htau) η :=
  Classical.choose_spec (SelectedFloorEstimate.selected_transport D F P padding
    hpadding hpadSmall hbeta tau htau)

/-- The source is required only at the one native bin budget. The common
polynomial degree still precedes tau. All grids are the very same selected
indices accepted by the native transport and the physical Batch producer.
This contract has no normalization, integral, energy or endpoint field. -/
def NativePointwisePacketSource (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding saving allowance source : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta) (η : Character) : Prop :=
  ∃ degree : ℝ, 0 ≤ degree ∧ ∀ tau : ℝ,
    ∀ htau : SelectedFloorEstimate.HeightAdmissible D P tau,
    2*tau*(1+degree+2*P.eps) ≤ allowance →
    PointwisePacketCells D F padding tau saving allowance P.eps degree source
      (nativeTransportOrder D F P padding tau hpadding hpadSmall hbeta htau) η

/-- Compatibility with the previous stronger all-positive-orders interface. -/
theorem native_source_of_pointwise_source (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding saving allowance source : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta) (η : Character)
    (hs : PointwisePacketSource D F P padding saving allowance source η) :
    NativePointwisePacketSource D F P padding saving allowance source
      hpadding hpadSmall hbeta η := by
  obtain ⟨degree,hdegree,hs⟩ := hs
  refine ⟨degree,hdegree,?_⟩
  intro tau htau hheight
  exact hs tau htau hheight _
    (nativeTransportOrder_spec D F P padding tau hpadding hpadSmall hbeta htau).1

/-- The same native n and the same selected grids feed both analytic bounds.
No arbitrary-n strengthening of the physical source supplier is needed. -/
theorem finite_data_of_native_source (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding saving allowance source : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hsaving : saving ≤ 1) (hallowance : 0 < allowance)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta)
    (hsource : ∀ η : Character, NativePointwisePacketSource D F P padding saving allowance source
      hpadding hpadSmall hbeta η) :
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
  obtain ⟨degree,hdegree,hpacket⟩ := hsource η
  obtain ⟨tau,htau,hheight⟩ := exists_joint_height D P allowance degree hallowance hdegree
  let n := nativeTransportOrder D F P padding tau hpadding hpadSmall hbeta htau
  have hn := nativeTransportOrder_spec D F P padding tau hpadding hpadSmall hbeta htau
  refine ⟨tau,htau.1,n,hn.1,hn.2 η,?_⟩
  exact finite_numerator_of_pointwise_packets D F padding tau saving allowance P.eps degree source
    hpadding hpad htau.1 hsaving hallowance P.eps_pos hdegree hheight hupper
    (heq ▸ hpadSmall) hbeta n η (hpacket tau htau hheight)

/-- Exact original finite-input contract from only the native-order packets. -/
theorem actual_finite_of_native_source (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding saving allowance : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad)
    (hsaving : 0 < saving) (hsavingSmall : saving ≤ 1) (hallowance : 0 < allowance)
    (hsource : ∀ hgap : Geometry.theta < HeckeZeroSupremum.beta,
      ∀ η : Character, NativePointwisePacketSource D F P padding saving allowance Cycle090.sourceCost
        hpadding hpadSmall hgap.le η) : ActualFiniteInput := by
  intro hgap
  exact ⟨D,F,padding,P.sigma,saving,hpadding,P.sigma_pos,hsaving,
    finite_data_of_native_source D F P padding saving allowance Cycle090.sourceCost
      hpadding hpadSmall hsavingSmall hallowance hgap.le (hsource hgap)⟩

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.nativeTransportOrder_spec
#print axioms QRH.Cycle092.SelectedNonfloor.finite_data_of_native_source
#print axioms QRH.Cycle092.SelectedNonfloor.actual_finite_of_native_source
