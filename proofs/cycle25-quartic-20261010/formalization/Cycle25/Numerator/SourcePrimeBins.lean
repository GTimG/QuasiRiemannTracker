import Cycle25.Assembly.HighDataFine
import Cycle25.Numerator.PhysicalFront
import OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins

/-! The original canonical prime-amplitude estimates, specialized to the new
source slots and the two external heights of the full-w representation. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
namespace OAI.SevenEighths.Cycle25NumeratorHighFinalAssembly
open Cycle25ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical
open HeckeInverseAmplification ProbeMellinBoundary HeckePrimeAmplitudeBins

 theorem weighted_source_prime_bins {Δ : ℝ}
    (D : Cycle25.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (τ : ℝ) (n : ℕ) (hτ : 0 < τ) (hheight : 4*τ < (1/200:ℝ)*D.cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 →
      ∀(η : Character) (u : FreeRow),Z^(1/100:ℝ) ≤ rowNorm u →
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 → rowNorm u ≤ Z^(d-D.t) →
      ∀(a : ℝ) (i : ℕ),i ≤ n → (51/100:ℝ) ≤ a → a ≤ 1 →
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ) < a+2*D.e →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ → ∀j : Fin D.N,
      let Q := HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
      let g := amplitude (Z^(D.ell j)) (a-1/2) D.t Q
      0 ≤ g ∧ g ≤ a-1/2 ∧ g∈labels (a-1/2) D.t ∧
      ‖Q‖ ≤ (Z^(D.ell j))^(g+D.t) ∧
      (0 < g → (Z^d)^(2*(D.ell j/d)*g) ≤ ‖Q‖^2) := by
  have hp := actual_phase_bins_on_cube F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad F.maximal F.W 1 2 (by norm_num) (by norm_num)
    (Cycle25.Numerator.source_complex_support_open F) (F.W.smooth ⊤)
    D.t (1/200) (7/8) D.rmin τ D.ε D.e D.κ D.cost D.t (1/100) D.t n
    D.t_pos.le (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.e_pos D.e_small
    D.kappa_pos D.cost_pos.le D.t_pos (by norm_num) D.phase_budget D.epsilon_gap
    D.t_pos (by linarith)
  filter_upwards [hp,HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) 2 (by norm_num),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hp hscale hT hZ
  intro d hd hd' η u hulo hcal huhi a i hi ha ha' hbin z hz hzim j
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  have hrlo : D.rmin ≤ D.ell j/d := by
    apply (le_div_iff₀ hdpos).mpr
    have hh := (D.slots_bounds j).2.1
    nlinarith only [hh,hd',D.rmin_pos]
  have hrhi : D.ell j/d ≤ D.t := by
    apply (div_le_iff₀ hdpos).mpr
    have hh := (D.slots_bounds j).2.2
    nlinarith only [hh,hd,D.t_pos]
  have hH : 0 ≤ ((3*i+1:ℕ):ℝ)*Z^τ := by positivity
  have hhh : ((|((0,z.im),0).1.1| ≤ (3*i+1:ℕ)*Z^τ ∧
      |((0,z.im),0).2| ≤ (3*i+1:ℕ)*Z^τ) ∧
      |((0,z.im),0).1.2| ≤ (3*i+1:ℕ)*Z^τ) := by
    simpa only [abs_zero] using And.intro (And.intro hH hH) hzim
  have hh := hp d hd hd' (hscale d hd) hT η u hulo hcal huhi a i hi ha ha' hbin
    (D.ell j/d) ((0,z.im),0) hrlo hrhi hhh
  have he : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hz' : (17/50:ℂ)+z.im*Complex.I=z := by
    apply Complex.ext <;> simp [hz]
  dsimp only at hh ⊢
  rw [he,hz'] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩

end OAI.SevenEighths.Cycle25NumeratorHighFinalAssembly
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
