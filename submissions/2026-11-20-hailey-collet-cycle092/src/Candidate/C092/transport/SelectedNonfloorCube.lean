/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original finite cube versus FullW tails, with no numerator estimate assumed. -/
import Candidate.C092.transport.SelectedNonfloorCells
import Candidate.C092.transport.SelectedNonfloorRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeMellinBoundary
open OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The complete finite-cube Fourier error is independent of a source/count
estimate. Only the original buffered selection is used. -/
theorem cube_fullW_error (D : BaselineData) (F : BaselineSourceData D)
    (padding tau : ℝ) (htau : 0 < tau)
    (hpadSmall : padding ≤ QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop, ∀ (n : ℕ) (η : Character)
      (idx grid : FreeRow → ℕ), selected D F padding tau n η Z idx grid →
      normalizer D F Z ≠ 0 ∧
      ‖numerator D F padding tau η Z idx grid/normalizer D F Z-
        fullW D F padding tau η Z idx grid/normalizer D F Z‖ ≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) := by
  obtain ⟨C,hC,herror⟩ :=
    QRH.Cycle092.SelectedActualKernel.Return.GenericPhysical.PhysicalDirect.PhysicalHighRowFamily.actual_normalized_cube_fullW_arbitrary_saving
      F.modulus ⊤ le_top D.N tau 1 1 2 1 padding (D.t/8)
      htau (by norm_num) (by norm_num) (by norm_num) hpadSmall
      (by have := D.t_pos; positivity) D.e D.e_pos D.e_small
      F.S F.exclusions F.maximal F.first D.length D.slots_pos D.slots_injective D.slots_sum
      (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
      (fun _ => F.bounded) (fun _ => F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
      F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
      F.complex_nonzero F.complex_nonzero
  refine ⟨C,hC,?_⟩
  filter_upwards [herror, (tendsto_rpow_atTop htau).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z he hT hZ
  intro n η idx grid hs
  let rows := SelectedActualIntegral.selectedRows D F padding Z grid
  have hR (u : FreeRow) (hu : u ∈ rows) : u.val ≠ 1 ∧ rowNorm u ≤ Z^(Geometry.h+padding) := by
    have h := (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu
    have hb := mem_rowBand.mp h.1
    exact ⟨hb.1, hb.2.2.le⟩
  have hbin (u : FreeRow) (_hu : u ∈ rows) :
      (51/100:ℝ) ≤ 51/100+D.e*grid u ∧ 51/100+D.e*grid u ≤ 1 ∧ 2 < Z^tau ∧
      Z^tau ≤ (3*idx u+1:ℕ)*Z^tau ∧ (3*idx u+1:ℕ)*Z^tau ≤ (3*idx u+2:ℕ)*Z^tau ∧
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(idx u+1:ℕ)*Z^tau) < 51/100+D.e*grid u+2*D.e := by
    have hb := hs.2.1 u
    have hp : 0 ≤ Z^tau := Real.rpow_nonneg (zero_lt_one.trans hZ).le tau
    refine ⟨hb.1, hb.2.1.trans (by norm_num), hT, ?_, ?_, hb.2.2.2.2.1⟩
    · have hn : (1:ℝ) ≤ (3*idx u+1:ℕ) := by exact_mod_cast (by omega : 1≤3*idx u+1)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hn hp
    · push_cast
      nlinarith
  have hb := he η rows hR (fun u => 51/100+D.e*grid u) (fun _ => Z^tau)
    (fun u => (3*idx u+1:ℕ)*Z^tau) idx hbin
  have hW : (fun (_ : Fin D.N) y => (F.w y:ℂ)) = (fun _ => ⇑F.W) := by
    funext j y
    exact (F.complex_eq y).symm
  refine ⟨hb.1, ?_⟩
  have hn : numerator D F padding tau η Z idx grid =
      finiteCentralCubeRows F.S F.exclusions F.maximal η rows
        (SelectedActualIntegral.primePool D F Z) (SelectedActualIntegral.pool_outside D F Z)
        (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
        (Z^Geometry.x) (Z^Geometry.y) Z D.e (fun u => 51/100+D.e*grid u)
        (fun u => (3*idx u+1:ℕ)*Z^tau) := by
    unfold ProbeAssembly.numerator finiteNonfloorNumerator
    rw [hW]
    rfl
  rw [hW] at hb
  rw [hn]
  exact hb.2

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.cube_fullW_error
