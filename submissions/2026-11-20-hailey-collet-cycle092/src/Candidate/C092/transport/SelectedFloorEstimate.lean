/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Selected genuine averaged floor at Q. The row proof is adapted from Joseph
Bebel's PositiveFloorSelection; the physical analytic imports retain the
original Collet/OpenAI/Levy/Gao attributions. -/
import Candidate.C092.transport.SelectedFloorEstimateCube

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators Topology ContDiff
open Filter
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open HeckeDetectorPhysicalSelection Cycle25.Numerator Cycle25.Weighted.FullWContour
open BoundaryDensitySplitReturn.TransportHighTransport
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedFloorEstimate
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Every admissible physical height gives the literal supported floor bound.
The constant is uniform in the character before its modulus factor. -/
theorem actual_selected_floor
    (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D)
    (padding : ℝ) (hpadding : 0 < padding)
    (hpad : padding+2*D.t ≤ 1/10000000000)
    (hpadSmall : padding ≤ QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta)
    (tau : ℝ) (htau : HeightAdmissible D P tau) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ idx grid : FreeRow → ℕ,
      selected D F padding tau n η Z idx grid →
      ‖SelectedActualFloor.floor D F padding tau η Z idx grid/normalizer D F Z‖ ≤
        C*(η.modulus.absNorm:ℝ)^(2+2*P.eps)*Z^(Geometry.signal Geometry.theta-1/4000) := by
  obtain ⟨C, hC, hf⟩ := actual_averaged_floor_cube_rows D F P padding hpadding hpad hpadSmall hbeta tau htau n
  refine ⟨C, hC, ?_⟩
  intro η
  filter_upwards [hf η] with Z hf
  intro idx grid hs
  let rows := supportedFloorRows F.S F.maximal
    (rowBand (Z^(1/100:ℝ)) (Z^(Geometry.h+padding))) grid
  have hm (u : FreeRow) (hu : u ∈ rows) :
      u ∈ rowBand (Z^(1/100:ℝ)) (Z^(Geometry.h+padding)) ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧ grid u = 0 :=
    (mem_supportedFloorRows F.S F.maximal _ grid u).mp hu
  have hb := hf rows idx
    (fun u hu => by
      have hr := mem_rowBand.mp (hm u hu).1
      exact ⟨hr.1, hr.2.1, (hm u hu).2.1, hr.2.2.le⟩)
    (fun u hu => calibrated_row_nonprincipal F.S F.exclusions.prime F.maximal F.exclusions.bad
      u (mem_rowBand.mp (hm u hu).1).1 (hm u hu).2.1)
    (fun u hu => (hs.1 u).2.1)
    (fun u hu => by
      have hb := (hs.2.1 u).2.2.2.2.1
      simpa only [(hm u hu).2.2, Nat.cast_zero, mul_zero, add_zero] using hb)
  have hW : (fun (_ : Fin D.N) y => (F.w y:ℂ)) = (fun _ => ⇑F.W) := by
    funext j y
    exact (F.complex_eq y).symm
  unfold SelectedActualFloor.floor SelectedActualFloor.cube
  rw [hW]
  exact hb.2

/-- The fixed height may be chosen before the character and all row labels. -/
theorem exists_height (D : BaselineData) (P : TransportParameters D) :
    ∃ tau : ℝ, HeightAdmissible D P tau := by
  let tau := min (D.cost/1600) (D.t/(4*(1+2*P.eps)))
  have hc := D.cost_pos
  have ht := D.t_pos
  have he := P.eps_pos
  have hp : 0 < 1+2*P.eps := by positivity
  have htau : 0 < tau := lt_min (by positivity) (by positivity)
  refine ⟨tau, htau, ?_, ?_⟩
  · have hh : tau ≤ D.cost/1600 := min_le_left _ _
    linarith
  · have hh : tau*(4*(1+2*P.eps)) ≤ D.t :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith

/-- No floor hypothesis remains: the genuine floor has the same positive
saving as the actual transport, at every admissible fixed height. -/
theorem floor_bound
    (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D)
    (padding : ℝ) (hpadding : 0 < padding)
    (hpad : padding+2*D.t ≤ 1/10000000000)
    (hpadSmall : padding ≤ QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta)
    (tau : ℝ) (htau : HeightAdmissible D P tau) (n : ℕ) (η : Character) :
    SelectedActualFloor.FloorBound D F padding tau P.sigma n η := by
  obtain ⟨C, hC, hf⟩ := actual_selected_floor D F P padding hpadding hpad hpadSmall hbeta tau htau n
  refine ⟨C*(η.modulus.absNorm:ℝ)^(2+2*P.eps), by
    have hm := HeckeLogarithmicInput.modulus_norm_ge_one η
    positivity, ?_⟩
  filter_upwards [hf η, eventually_ge_atTop (1:ℝ)] with Z hf hZ
  intro idx grid hs
  have hshift : Geometry.signalShift = ProbeAssembly.shift := by
    dsimp [Geometry.signalShift, ProbeAssembly.shift,
      Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signalShift,
      Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signalShift]
    change -(4+Geometry.y-Geometry.x)/6 = -(5/6-Geometry.x/3-Geometry.ell/6)
    linarith [Geometry.x_add_y]
  have hexp : Geometry.signal Geometry.theta-1/4000 ≤
      HeckeZeroSupremum.beta+ProbeAssembly.shift-P.sigma := by
    rw [Geometry.signal, hshift]
    linarith [P.sigma_small, D.t_small]
  exact (hf idx grid hs).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity))

end QRH.Cycle092.SelectedFloorEstimate
#print axioms QRH.Cycle092.SelectedFloorEstimate.actual_selected_floor
#print axioms QRH.Cycle092.SelectedFloorEstimate.floor_bound
#print axioms QRH.Cycle092.SelectedFloorEstimate.exists_height
