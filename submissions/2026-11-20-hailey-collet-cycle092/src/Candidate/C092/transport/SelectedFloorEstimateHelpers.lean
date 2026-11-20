/- Adapted from credited Bebel/Collet source phase-bin helpers, Apache-2.0. -/
import Candidate.C092.transport.SelectedFloorEstimateFloorFullW
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open HeckePrimeAmplitudeBins ProbeMellinBoundary
namespace QRH.Cycle092.SelectedFloorEstimate
variable [Geometry.Parameters]
 theorem source_prime_bins (D : BaselineData) (F : BaselineSourceData D) (P : Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.TransportParameters D)
    (τ : ℝ) (n : ℕ) (hτ : 0 < τ) (hheight : 4*τ < (1/200:ℝ)*D.cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 →
      ∀(η : Character) (u : FreeRow),Z^(1/100:ℝ) ≤ rowNorm u →
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 → rowNorm u ≤ Z^(d-D.t) →
      ∀(a : ℝ) (i : ℕ),i ≤ n → (51/100:ℝ) ≤ a → a ≤ 1 →
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ) < a+2*D.e →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ → ∀j : Fin D.N,
      let Q := HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
      let g := amplitude (Z^(D.length j)) (a-1/2) D.t Q
      0 ≤ g ∧ g ≤ a-1/2 ∧ g∈labels (a-1/2) D.t ∧
      ‖Q‖ ≤ (Z^(D.length j))^(g+D.t) ∧
      (0 < g → (Z^d)^(2*(D.length j/d)*g) ≤ ‖Q‖^2) := by
  have hp := actual_phase_bins_on_cube F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad F.maximal F.W 1 2 (by norm_num) (by norm_num)
    (Cycle25.Numerator.source_complex_support_open F) (F.W.smooth ⊤)
    D.t (1/200) (7/8) P.rmin τ P.phaseEpsilon D.e P.phaseKappa D.cost D.t (1/100) D.t n
    D.t_pos.le (by norm_num) (by norm_num) P.rmin_pos hτ P.phaseEpsilon_pos D.e_pos D.e_small
    P.phaseKappa_pos D.cost_pos.le D.t_pos (by norm_num) P.phase_budget (lt_of_lt_of_le P.phase_gap (mul_le_mul_of_nonneg_left P.mesh_small P.rmin_pos.le))
    D.t_pos (by linarith)
  filter_upwards [hp,HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) 2 (by norm_num),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hp hscale hT hZ
  intro d hd hd' η u hulo hcal huhi a i hi ha ha' hbin z hz hzim j
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  have hrlo : P.rmin ≤ D.length j/d := by
    apply (le_div_iff₀ hdpos).mpr
    have hh := (P.slots_lower j)
    nlinarith only [hh,hd',P.rmin_pos]
  have hrhi : D.length j/d ≤ D.t := by
    apply (div_le_iff₀ hdpos).mpr
    have hh := (D.slots_small j)
    nlinarith only [hh,hd,D.t_pos]
  have hH : 0 ≤ ((3*i+1:ℕ):ℝ)*Z^τ := by positivity
  have hhh : ((|((0,z.im),0).1.1| ≤ (3*i+1:ℕ)*Z^τ ∧
      |((0,z.im),0).2| ≤ (3*i+1:ℕ)*Z^τ) ∧
      |((0,z.im),0).1.2| ≤ (3*i+1:ℕ)*Z^τ) := by
    simpa only [abs_zero] using And.intro (And.intro hH hH) hzim
  have hh := hp d hd hd' (hscale d hd) hT η u hulo hcal huhi a i hi ha ha' hbin
    (D.length j/d) ((0,z.im),0) hrlo hrhi hhh
  have he : (Z^d)^(D.length j/d)=Z^(D.length j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hz' : (17/50:ℂ)+z.im*Complex.I=z := by
    apply Complex.ext <;> simp [hz]
  dsimp only at hh ⊢
  rw [he,hz'] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩
theorem eventually_uniform_source_conductor {P : ℝ→Prop} (dmin : ℝ) (hdmin : 0 < dmin)
    (hP : ∀ᶠU : ℝ in atTop,P U) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin ≤ d → P (Z^d) := by
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hP
  filter_upwards [(tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U0),
    eventually_ge_atTop (1:ℝ)] with Z hZmin hZ
  intro d hd
  exact hU0 (Z^d) (hZmin.trans (Real.rpow_le_rpow_of_exponent_le hZ hd))


end QRH.Cycle092.SelectedFloorEstimate
