/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Buffered-bin, ray-character and normalizer proofs reuse the original OpenAI
development and the Collet/Levy/Gao return, retaining those imports' credits.
The separation from the old coarse instance follows Bebel's transport fork. -/
import Candidate.C092.transport.ProbeAssembly
import Candidate.C092.transport.ActualGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

/-!
Actual buffered choices, nonzero normalization, and arbitrarily fine baseline
source data at Q. None uses the historical .816 conductor or .075 source cap.
The error estimate in `SelectedTransport` is not asserted by the selection
theorem. Its separate contour/principal and floor-removal obligations remain.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.ProbeHighRowFamily OAI.SevenEighths.HeckeInverseAmplification
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.PrincipalSignalComparison
open OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly

namespace QRH.Cycle092.SelectedActual

theorem baseline_beta : HeckeZeroSupremum.beta ≤ (7/8 : ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

variable [Geometry.Parameters]

/-- A single finite buffer works before the character and scale. These are
actual zeros of the masked family, with actual supported ray-twist facts. -/
theorem buffered_selection (D : BaselineData) (F : BaselineSourceData D)
    (padding tau : ℝ) (htau : 0 < tau) :
    ∃ n : ℕ, 0 < n ∧ ∀ᶠ Z : ℝ in atTop, ∀ η : Character,
      ∃ idx grid : FreeRow → ℕ, selected D F padding tau n η Z idx grid := by
  obtain ⟨n, hn, hwidth⟩ := exists_source_cube_bin_number D.e D.e_pos
  refine ⟨n, hn, ?_⟩
  filter_upwards [source_cube_height_eventually tau htau,
    ProbeRayCharacterFamily.large_supported_twists_eventually F.modulus (1/100) (by norm_num)]
      with Z hZ hlarge
  intro η
  obtain ⟨idx, grid, hbins⟩ := exists_source_cube_bins D.e (Z^tau) D.e_pos hZ.2
    n hn hwidth F.S F.exclusions.prime η (rayCubeFamily F.modulus ⊤ le_top)
  refine ⟨idx, grid, ?_⟩
  change _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro u
    exact ⟨(hbins u).1, (hbins u).2.1, (hbins u).2.2.1,
      (hbins u).2.2.2.2.2.2.1⟩
  · intro u
    rcases hbins u with ⟨hi, hin, hgrid, ha0, ha1, hBH, hbuffer, hlo, hhi, hnext, hzero⟩
    have hcap : (51/100 : ℝ) + D.e*grid u ≤ 7/8 := by
      by_cases hgt : (51/100 : ℝ) < 51/100+D.e*grid u
      · obtain ⟨j, s, hz, hpole, has, _⟩ := hzero hgt
        have hs : 0 < s.re := by linarith
        have hpole' : s ≠ 1 ∨
            (sourceDetectorFamily F.S F.exclusions.prime η u
              (rayCubeFamily F.modulus ⊤ le_top u) j).residue ≠ 1 := by tauto
        exact has.trans ((HeckeZeroSupremum.zero_re_le_beta _ hs hpole' hz).trans baseline_beta)
      · linarith
    exact ⟨ha0, hcap, hlo, hhi, hnext, hzero⟩
  · intro u hu hcal
    have hs := calibration_nonzero_supported F.S F.maximal F.exclusions.bad u.val hcal
    have hnp : ∀ ψ, (rayCubeFamily F.modulus ⊤ le_top u ψ).residue ≠ 1 :=
      hlarge u (mem_rowBand.mp hu).2.1 hs ⊤ le_top
    refine ⟨hnp, ProbeRayCharacterFamily.raw_twisted_conductor F.modulus ⊤ le_top u, ?_⟩
    intro hnp'
    exact (ProbeRayCharacterFamily.source_nonprincipal_maximum_dominates
      F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u) hnp' _).trans_lt
      (hbins u).2.2.2.2.2.2.2.2.2.1

/-- The literal normalizer in ProbeAssembly is nonzero eventually, and its
inverse has arbitrarily small positive power growth. -/
theorem actual_normalizer_inverse (D : BaselineData) (F : BaselineSourceData D)
    (nu : ℝ) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      normalizer D F Z ≠ 0 ∧ ‖(normalizer D F Z)⁻¹‖ ≤ C*Z^nu := by
  have h := Record1252270103LowNormalizer.actual_ray_normalizer_inverse
    F.modulus ⊤ le_top F.S F.exclusions 1 2 (by norm_num) (by norm_num)
    D.length D.slots_pos D.slots_sum
    (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
    (fun _ y => (F.bounded y).1) (fun _ => F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero nu hnu
  exact h

/-- The non-error clauses of SelectedTransport are fully constructed. -/
theorem normalized_buffered_selection (D : BaselineData) (F : BaselineSourceData D)
    (padding tau : ℝ) (htau : 0 < tau) :
    ∃ n : ℕ, 0 < n ∧ ∀ᶠ Z : ℝ in atTop,
      normalizer D F Z ≠ 0 ∧ ∀ η : Character,
        ∃ idx grid : FreeRow → ℕ, selected D F padding tau n η Z idx grid := by
  obtain ⟨n, hn, hselection⟩ := buffered_selection D F padding tau htau
  obtain ⟨C, _hC, hnormalizer⟩ := actual_normalizer_inverse D F 1 (by norm_num)
  refine ⟨n, hn, ?_⟩
  filter_upwards [hselection, hnormalizer] with Z hs hN
  exact ⟨hN.1, hs⟩

/-- Arbitrarily fine common source meshes and arbitrarily small detector losses
can be chosen before the character. This constructs genuine source data and
buffered choices, without claiming any marked initial-energy estimates. -/
theorem fine_data_with_selection {kappa budget : ℝ}
    (hk : 7/10 ≤ kappa) (hk' : kappa ≤ 3/4) (hbudget : 0 < budget)
    (mesh : ℝ → ℝ) (hmesh : ∀ t : ℝ, 0 < t → 0 < mesh t)
    (padding tau : ℝ) (htau : 0 < tau) :
    ∃ D : BaselineData, ∃ F : BaselineSourceData D,
      D.momentKappa = kappa ∧ 159*D.ε+609*D.t ≤ budget ∧
      (∀ j, D.length j ≤ Cycle25.sourceMesh D.t/200) ∧
      (∀ j, D.length j ≤ mesh D.t/200) ∧
      ∃ n : ℕ, 0 < n ∧ ∀ᶠ Z : ℝ in atTop,
        normalizer D F Z ≠ 0 ∧ ∀ η : Character,
          ∃ idx grid : FreeRow → ℕ, selected D F padding tau n η Z idx grid := by
  obtain ⟨D, hkappa, hloss, hfine, hcommon⟩ :=
    exists_baseline_data_common_mesh hk hk' hbudget mesh hmesh
  obtain ⟨F⟩ := exists_baseline_source D
  exact ⟨D, F, hkappa, hloss, hfine, hcommon,
    normalized_buffered_selection D F padding tau htau⟩

/-- All four raw contour/principal error exponents are absorbed at Q's widened
geometry. The old h<.816 field is not needed for this step. -/
theorem raw_exponents [ActualGeometry.WidenedCoreBounds]
    {beta sigma e nu saving ellMin : ℝ}
    (hbeta : Geometry.theta ≤ beta)
    (hgeom : sigma+8*e+nu ≤ 1/20) (hprincipal : sigma+nu ≤ 1/4000)
    (hwindow : sigma+e ≤ Geometry.theta*ellMin)
    (hlarge : sigma+nu ≤ saving+Geometry.signal Geometry.theta) :
    (7/8 : ℝ)+ProbeAssembly.shift-(Geometry.y/2-Geometry.h*(17/50-1/6)-1/50)+8*e+nu ≤ beta+ProbeAssembly.shift-sigma ∧
    -saving+nu ≤ beta+ProbeAssembly.shift-sigma ∧
    beta+ProbeAssembly.shift-1/4000+nu ≤ beta+ProbeAssembly.shift-sigma ∧
    beta+ProbeAssembly.shift+e-Geometry.theta*ellMin ≤ beta+ProbeAssembly.shift-sigma := by
  have htheta := ActualGeometry.WidenedCoreBounds.theta_bounds.1
  have hsmall := ActualGeometry.WidenedCoreBounds.small_saving
  have hshift : Geometry.signalShift = ProbeAssembly.shift := by
    change -(4+Geometry.y-Geometry.x)/6 = -(5/6-Geometry.x/3-Geometry.ell/6)
    linarith [Geometry.x_add_y]
  dsimp only [Geometry.signal] at hlarge
  rw [hshift] at hlarge
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end QRH.Cycle092.SelectedActual

#print axioms QRH.Cycle092.SelectedActual.buffered_selection
#print axioms QRH.Cycle092.SelectedActual.actual_normalizer_inverse
#print axioms QRH.Cycle092.SelectedActual.fine_data_with_selection
#print axioms QRH.Cycle092.SelectedActual.raw_exponents
