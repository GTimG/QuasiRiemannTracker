/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual original row cells to the literal finite numerator, including all
cube-versus-FullW tails. The source/count suppliers remain explicit. -/
import Candidate.C092.transport.SelectedNonfloorCube

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Entire retained FullW row bound to the actual finite nonfloor numerator.
The original reciprocal and every prime mask remain in both expressions. -/
theorem finite_numerator_of_fullW (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving : ℝ) (htau : 0 < tau) (hsaving : saving ≤ 1)
    (hpadSmall : padding ≤ QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta) (n : ℕ) (η : Character)
    (hfull : FullWBound D F padding tau saving n η) :
    FiniteNumeratorBound D F padding tau saving n η := by
  obtain ⟨Cf, hCf, hf⟩ := hfull
  obtain ⟨Ce, hCe, he⟩ := cube_fullW_error D F padding tau htau hpadSmall
  refine ⟨Cf+Ce*(η.modulus.absNorm:ℝ)^2, by positivity, ?_⟩
  filter_upwards [hf, he, eventually_gt_atTop (1:ℝ)] with Z hf he hZ
  intro idx grid hs
  have herr := he n η idx grid hs
  have hN := herr.1
  have hh := hf idx grid hs
  have hshift : Geometry.signalShift = ProbeAssembly.shift := by
    dsimp [Geometry.signalShift, ProbeAssembly.shift,
      Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signalShift,
      Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signalShift]
    change -(4+Geometry.y-Geometry.x)/6 = -(5/6-Geometry.x/3-Geometry.ell/6)
    linarith [Geometry.x_add_y]
  have hpositive : 0 < Geometry.signal Geometry.theta := by
    rw [Geometry.signal_at_boundary]
    linarith [Geometry.ell_pos, Geometry.ell_lt_x, Geometry.x_lt_y]
  have hexp : (-1:ℝ) ≤ HeckeZeroSupremum.beta+ProbeAssembly.shift-saving := by
    rw [Geometry.signal, hshift] at hpositive
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hexp
  have hnorm : ‖numerator D F padding tau η Z idx grid/normalizer D F Z‖ ≤
      (Cf+Ce*(η.modulus.absNorm:ℝ)^2)*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving) := by
    have ht := norm_le_norm_add_norm_sub
      (fullW D F padding tau η Z idx grid/normalizer D F Z)
      (numerator D F padding tau η Z idx grid/normalizer D F Z)
    rw [norm_sub_rev] at ht
    calc
      _ ≤ _ := ht
      _ ≤ Cf*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving)+
          (Ce*(η.modulus.absNorm:ℝ)^2)*Z^(-(1:ℝ)) := add_le_add hh herr.2
      _ ≤ Cf*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving)+
          (Ce*(η.modulus.absNorm:ℝ)^2)*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving) := by
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpow
          (show 0 ≤ Ce*(η.modulus.absNorm:ℝ)^2 by positivity))
      _ = _ := by ring
  have hNnorm : ‖normalizer D F Z‖ ≠ 0 := norm_ne_zero_iff.mpr hN
  have heq : ‖numerator D F padding tau η Z idx grid‖ =
      ‖numerator D F padding tau η Z idx grid/normalizer D F Z‖*‖normalizer D F Z‖ := by
    rw [norm_div, div_mul_cancel₀ _ hNnorm]
  rw [heq]
  exact (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_eq (by ring)

/-- Every genuine finite row cell, all original grids and complete cube tails
have been assembled. Only the per-cell packet/source/count bound remains. -/
theorem finite_numerator_of_cells (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving allowance : ℝ) (htau : 0 < tau) (hsaving : saving ≤ 1)
    (hallowance : 0 < allowance) (hupper : Geometry.h+padding ≤ 1)
    (hpadSmall : padding ≤ QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta) (n : ℕ) (η : Character)
    (hcell : CellBound D F padding tau saving allowance n η) :
    FiniteNumeratorBound D F padding tau saving n η :=
  finite_numerator_of_fullW D F padding tau saving htau hsaving hpadSmall hbeta n η
    (fullW_bound_of_cells D F padding tau saving allowance hallowance hupper n η hcell)

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.finite_numerator_of_fullW
#print axioms QRH.Cycle092.SelectedNonfloor.finite_numerator_of_cells
