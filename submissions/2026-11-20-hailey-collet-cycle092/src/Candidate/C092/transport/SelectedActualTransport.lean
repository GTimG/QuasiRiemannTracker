/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The raw full-row contour/principal theorem is re-elaborated in
SelectedActualKernel00--34 from the original credited OpenAI/Collet/Levy/Gao
transport and Bebel's fork, using the true widened .818 coarse contract. -/
import Candidate.C092.transport.SelectedActualKernel34
import Candidate.C092.transport.SelectedActualFloor

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.ProbeHighRowFamily OAI.SevenEighths.HeckeInverseAmplification
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.PrincipalSignalComparison
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedActualTransport
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Actual full-row transport at Q: the source, slots and positive saving are
fixed before the live character. Only the genuine floor remains to be removed.
No finite-numerator estimate or false historical conductor field is used. -/
theorem actual_full_transport (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding tau : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad) (htau : 0 < tau)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta) :
    ∃ n : ℕ, 0 < n ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      normalizer D F Z ≠ 0 ∧ ∃ idx grid : FreeRow → ℕ,
        selected D F padding tau n η Z idx grid ∧
        ‖residual D F η Z-SelectedActualFloor.whole D F padding tau η Z idx grid/normalizer D F Z‖ ≤
          C*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-P.sigma) := by
  have hsignal : 0 < Geometry.signal Geometry.theta := by
    rw [Geometry.signal_at_boundary]
    have hx : 0 < Geometry.x := Geometry.ell_pos.trans Geometry.ell_lt_x
    linarith [Geometry.x_lt_y]
  have hlarge : P.sigma+P.nu ≤ 1+Geometry.signal Geometry.theta := by
    have hs := P.sigma_small
    have hn := P.nu_eq
    have ht := D.t_small
    linarith
  have hzeta : padding ≤
      (1/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    simpa only [Cycle090.rowPad, show (10 : ℝ)^(258 : ℕ) =
      1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 by norm_num [pow_succ]] using hpadSmall
  have hlarge' : P.sigma+P.nu ≤
      1+QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Assembly.signal
        QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.theta := by
    have heq : QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Assembly.signalShift =
        Geometry.signalShift := by
      rw [QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Assembly.signalShift_eq]
      change -(4+(Geometry.y-Geometry.x))/6 = -(4+Geometry.y-Geometry.x)/6
      ring
    simpa only [QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Assembly.signal,
      Geometry.signal, heq] using hlarge
  obtain ⟨n, hn, htransport⟩ :=
    OAI.SevenEighths.Cycle092SelectedActualReturn.TransportHighRowFamily.actual_normalized_probe_transport_saving
      F.modulus ⊤ le_top D.N D.e (1/100) 1 2 1 padding 1 tau P.ellMin P.nu
      D.e_pos D.e_small (by norm_num) (by norm_num) hpadding hzeta htau
      (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos hbeta SelectedActual.baseline_beta
      F.S F.exclusions F.maximal F.first D.length P.slots_min D.slots_injective D.slots_sum
      (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
      (fun _ => F.bounded) (fun _ => F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
      F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
      F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos P.geometric_budget
      P.principal_budget P.window_budget hlarge'
  refine ⟨n, hn, ?_⟩
  intro η
  obtain ⟨C, hC, hb⟩ := htransport η
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with Z hb
  dsimp only at hb
  obtain ⟨hN, idx, grid, hlabels, hbins, hray, herr⟩ := hb
  refine ⟨hN, idx, grid, ⟨hlabels, hbins, hray⟩, ?_⟩
  have hshift : -(4+QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.b)/6 =
      ProbeAssembly.shift :=
    QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.signalShift_eq
  have hfrac : (4+QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.b)/6 =
      -ProbeAssembly.shift := by linarith
  rw [hfrac, hshift] at herr
  simp only [sub_neg_eq_add] at herr
  simpa only [ProbeAssembly.residual, sourceProbe, Record1252270103Low.normalizedProbe,
    normalizer, OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport.actualNormalizer,
    SelectedActualFloor.whole, SelectedActualFloor.cube,
    ProbeAssembly.shift, sub_eq_add_neg, neg_div] using herr

/-- The full contour estimate and the source's genuine normalized floor bound
now supply literal SelectedTransport, at the same source/height and saving. -/
theorem selected_transport_of_floor (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding tau : ℝ)
    (hpadding : 0 < padding) (hpadSmall : padding ≤ Cycle090.rowPad) (htau : 0 < tau)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta)
    (hfloor : ∀ n : ℕ, 0 < n → ∀ η : Character,
      SelectedActualFloor.FloorBound D F padding tau P.sigma n η) :
    ∃ n : ℕ, 0 < n ∧ ∀ η : Character,
      SelectedTransport D F padding tau P.sigma n η := by
  obtain ⟨n, hn, hfull⟩ := actual_full_transport D F P padding tau hpadding hpadSmall htau hbeta
  refine ⟨n, hn, ?_⟩
  intro η
  obtain ⟨Ct, hCt, ht⟩ := hfull η
  obtain ⟨Cf, hCf, hf⟩ := hfloor n hn η
  refine ⟨Ct+Cf, by positivity, ?_⟩
  filter_upwards [ht, hf] with Z ht hf
  obtain ⟨hN, idx, grid, hsel, herr⟩ := ht
  refine ⟨hN, idx, grid, hsel, ?_⟩
  have hfloor := hf idx grid hsel
  have heq : residual D F η Z-numerator D F padding tau η Z idx grid/normalizer D F Z =
      (residual D F η Z-SelectedActualFloor.whole D F padding tau η Z idx grid/normalizer D F Z)+
        SelectedActualFloor.floor D F padding tau η Z idx grid/normalizer D F Z := by
    rw [SelectedActualFloor.whole_split]
    ring
  rw [heq]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ Ct*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-P.sigma)+
        Cf*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-P.sigma) := add_le_add herr hfloor
    _ = _ := by ring

end QRH.Cycle092.SelectedActualTransport
#print axioms QRH.Cycle092.SelectedActualTransport.actual_full_transport
#print axioms QRH.Cycle092.SelectedActualTransport.selected_transport_of_floor
