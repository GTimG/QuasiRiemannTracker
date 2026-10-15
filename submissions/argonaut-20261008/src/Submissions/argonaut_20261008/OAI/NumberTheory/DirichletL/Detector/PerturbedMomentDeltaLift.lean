import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedCountProjection
import Submissions.argonaut_20261008.HighDataMomentGeometry
import Submissions.argonaut_20261008.PerturbedCentralExponent

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set

namespace SevenEighths.PerturbedMomentConstruction

open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeHighRowFamily ProbeFinalAssembly Parameters
open HighFrontierTargets
open SevenEighths.PerturbedCentral
open SevenEighths.PerturbedCountBridge
open SevenEighths.PerturbedCountProjection
open ProbePhysical (SourceExclusions)

local notation "O" => HeckeFamily.O

/-! ## Definitional identifications of the fixed geometry -/

lemma rho_names :
    PerturbedCentral.rho0 = HighFrontierTargets.rho ∧
      Parameters.perturbedRho = HighFrontierTargets.rho := by
  constructor <;> rfl

lemma totalE_names :
    PerturbedCentral.totalE = HighFrontierTargets.totalE ∧
      Parameters.perturbedTotalE = HighFrontierTargets.totalE := by
  constructor <;> rfl

lemma height_names :
    PerturbedCentral.physicalHeight = HighFrontierTargets.rowHeight ∧
      Parameters.perturbedHeight = HighFrontierTargets.rowHeight := by
  constructor <;> rfl

lemma boundary_names :
    PerturbedCentral.boundary = HighFrontierTargets.sigmaBoundary ∧
      Parameters.perturbedBoundary = HighFrontierTargets.sigmaBoundary := by
  constructor <;> rfl

lemma source_scale_names :
    PerturbedCentral.sourceLx = HighFrontierTargets.lx ∧
      PerturbedCentral.sourceLy = HighFrontierTargets.ly := by
  constructor <;> rfl

lemma positiveGap_eq_deltaGap :
    HighFrontierTargets.positiveGap =
      PerturbedCentral.deltaGap HeckeZeroSupremum.beta := by
  rfl

lemma momentGamma_eq_gammaCount :
    momentGamma = PerturbedCentral.gammaCount HeckeZeroSupremum.beta := by
  rfl

/-!
For `b0 < beta`, the Gamma used by the terminal energy package is no larger
than the actual boundary gap.  This is exactly the direction in which
`Moments` is monotone.
-/
theorem gammaCount_le_deltaGap {beta : ℝ}
    (hbeta : PerturbedCentral.boundary < beta) :
    PerturbedCentral.gammaCount beta ≤ PerturbedCentral.deltaGap beta := by
  unfold PerturbedCentral.gammaCount PerturbedCentral.deltaGap
  unfold PerturbedCentral.boundary PerturbedCentral.rho0 at hbeta ⊢
  by_cases h : beta ≤ 7 / 8
  · rw [max_eq_left (by linarith)]
    norm_num at hbeta ⊢
    linarith
  · rw [max_eq_right (by linarith)]
    norm_num <;> linarith

lemma momentGamma_le_positiveGap
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta) :
    momentGamma ≤ HighFrontierTargets.positiveGap := by
  rw [momentGamma_eq_gammaCount, positiveGap_eq_deltaGap]
  have hbeta' : PerturbedCentral.boundary < HeckeZeroSupremum.beta := by
    rw [boundary_names.1]
    exact hbeta
  exact gammaCount_le_deltaGap hbeta'

/-! ## Record-level and capsule-level forward monotonicity in Delta -/

/--
Lift `SourceMomentsAt` on the same batch and the same fiber.  Every binder in
the public capsule is retained; only the `Delta` field of the terminal
`Moments` record is enlarged.
-/
theorem sourceMomentsAt_mono_delta
    (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S, Prime P)
    (eta : Character) (rows : Finset FreeRow) (ell : Fin N → ℝ)
    (W : Fin N → ℝ → ℂ)
    (Z d a epsilon theta dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Delta1 Delta2 c kappa C height epsilonM : ℝ)
    (hDelta : Delta1 ≤ Delta2)
    (h : SourceMomentsAt M H hH S hS eta rows ell W
      Z d a epsilon theta dmax b slotMesh binWidth i z
      Delta1 c kappa C height epsilonM) :
    SourceMomentsAt M H hH S hS eta rows ell W
      Z d a epsilon theta dmax b slotMesh binWidth i z
      Delta2 c kappa C height epsilonM := by
  intro q B hrows hdata hreverse hslots hwidths hprofile hupper hexternal
    hmesh hbinWidth hfamily bin label left right hne
  exact PerturbedCentral.moments_mono_delta hDelta
    (h q B hrows hdata hreverse hslots hwidths hprofile hupper hexternal
      hmesh hbinWidth hfamily bin label left right hne)

/-- Forward monotonicity of the row-uniform moment capsule. -/
theorem sourceMomentBoundAt_mono_delta
    {N : ℕ} {M : Ideal O} [NeZero M] [Finite (O ⧸ M)]
    {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {S : Finset (Ideal O)} {hS : SourceExclusions S}
    {hmax : ∀P∈S, P.IsMaximal} {ell : Fin N → ℝ}
    {W : Fin N → ℝ → ℝ}
    {dmin dmax b epsilon rowMargin slotMesh binWidth epsilonM : ℝ}
    {counts : CountParameters M H epsilonM} {eta : Character}
    {Z theta C height Delta1 Delta2 : ℝ}
    (hDelta : Delta1 ≤ Delta2)
    (h : SourceMomentBoundAt M H hH S hS hmax ell W
      dmin dmax b epsilon rowMargin slotMesh binWidth Delta1 epsilonM
      counts eta Z theta C height) :
    SourceMomentBoundAt M H hH S hS hmax ell W
      dmin dmax b epsilon rowMargin slotMesh binWidth Delta2 epsilonM
      counts eta Z theta C height := by
  intro rows d a hdmin hdmax ha ha1 hrows i z hz hzim
  exact sourceMomentsAt_mono_delta M H hH S hS.prime eta rows ell
    (fun j y => (W j y : ℂ)) Z d a epsilon theta dmax b slotMesh binWidth
    i z Delta1 Delta2
    (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
    (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
    C height epsilonM hDelta
    (h rows d a hdmin hdmax ha ha1 hrows i z hz hzim)

/-- Preserve the `J -> eta -> C -> theta` quantifier order under the lift. -/
theorem highJointMomentOutputAt_mono_delta
    {N : ℕ} {M : Ideal O} [NeZero M] [Finite (O ⧸ M)]
    {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {S : Finset (Ideal O)} {hS : SourceExclusions S}
    {hmax : ∀P∈S, P.IsMaximal} {ell : Fin N → ℝ}
    {W : Fin N → ℝ → ℝ}
    {dmin dmax b epsilon rowMargin slotMesh binWidth epsilonM : ℝ}
    {counts : CountParameters M H epsilonM} {Delta1 Delta2 : ℝ}
    (hDelta : Delta1 ≤ Delta2)
    (h : HighJointMomentOutputAt M H hH S hS hmax ell W
      dmin dmax b epsilon rowMargin slotMesh binWidth Delta1 epsilonM counts) :
    HighJointMomentOutputAt M H hH S hS hmax ell W
      dmin dmax b epsilon rowMargin slotMesh binWidth Delta2 epsilonM counts := by
  obtain ⟨J, hJ, hbound⟩ := h
  refine ⟨J, hJ, ?_⟩
  intro eta
  obtain ⟨C, hC, hbound⟩ := hbound eta
  refine ⟨C, hC, ?_⟩
  intro theta htheta htheta1
  filter_upwards [hbound theta htheta htheta1] with Z hZ
  exact sourceMomentBoundAt_mono_delta hDelta hZ

/-- The actual terminal moments, promoted from Gamma to `beta-b0`. -/
theorem high_joint_moments_deltaGap
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (G : MomentGeometry) (F : PerturbedSourceData G)
    (counts : CountParameters F.modulus ⊤ G.t) :
    HighJointMomentOutputAt F.modulus ⊤ le_top F.S F.exclusions F.maximal
      G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
      HighFrontierTargets.positiveGap G.t counts := by
  apply highJointMomentOutputAt_mono_delta (momentGamma_le_positiveGap hbeta)
  exact high_joint_moments hbeta G F counts

/--
Choose the height after the common polynomial degree, while retaining the
promoted `DeltaGap` capsule.  The estimate has constant `C * Z^G.t` and
height exactly `Z^(2*theta)`; the interval is not enlarged to `Z^G.t`.
-/
theorem chosen_height_deltaGap
    (G : MomentGeometry) (F : PerturbedSourceData G)
    (counts : CountParameters F.modulus ⊤ G.t)
    (hmom : HighJointMomentOutputAt F.modulus ⊤ le_top F.S F.exclusions
      F.maximal G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε
      G.t G.t G.t HighFrontierTargets.positiveGap G.t counts) :
    ∃theta : ℝ, 0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
      4 * theta < (1 / 200 : ℝ) * G.cost ∧ theta < G.t ∧
      2 * theta ≤ G.t ∧ theta * (2 + 4 * G.eps) < G.t ∧
      ∀eta : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBoundAt F.modulus ⊤ le_top F.S F.exclusions F.maximal
          G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
          HighFrontierTargets.positiveGap G.t counts eta Z theta
          (C * Z ^ G.t) (Z ^ (2 * theta)) := by
  obtain ⟨J, hJ, hbound⟩ := hmom
  obtain ⟨theta, htheta, hthetad, hthetacost, hthetat, hthetaJ, hthetaeps⟩ :=
    G.height_choice J hJ
  have htheta1 : theta ≤ 1 := by linarith
  refine ⟨theta, htheta, hthetad, hthetacost, hthetat,
    by nlinarith, hthetaeps, ?_⟩
  intro eta
  obtain ⟨C, hC, hbound⟩ := hbound eta
  refine ⟨C * 2 ^ J, by positivity, ?_⟩
  filter_upwards [hbound theta htheta htheta1,
    eventually_ge_atTop (1 : ℝ)] with Z hb hZ
  exact SourceMomentBoundAt.mono_constant (by linarith) hb
    (ProbeFinalAssembly.polynomial_height_absorption C Z theta J G.t
      hC.le hZ htheta.le hJ hthetaJ)

/-! ## Same actual D, G, F and count constants -/

/--
The entire moment package on the actual f630 scalar datum.  `G` is exactly the
PI adapter `momentGeometryOfPerturbed D hfine`; the official count record is
the projection of the displayed wide record.
-/
theorem exists_actual_same_data_deltaGap_moments
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta) :
    ∃D : HighDataPerturbed HighFrontierTargets.positiveGap,
      ∃hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200,
      let G := momentGeometryOfPerturbed D hfine
      ∃F : PerturbedSourceData G,
      ∃wide : WideCountParameters F.modulus ⊤ G.t,
        HighJointMomentOutputAt F.modulus ⊤ le_top F.S F.exclusions F.maximal
          G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
          HighFrontierTargets.positiveGap G.t wide.toCountParameters := by
  have hgap : 0 < HighFrontierTargets.positiveGap := by
    unfold HighFrontierTargets.positiveGap
    linarith
  obtain ⟨D, hfine, _ht, _hN, _hell, _he⟩ :=
    exists_perturbed_data_with_moment_geometry
      HighFrontierTargets.positiveGap hgap
  let G := momentGeometryOfPerturbed D hfine
  obtain ⟨F⟩ := exists_perturbed_source_data G
  obtain ⟨wide⟩ := source_wide_count_parameters G F
  refine ⟨D, hfine, F, wide, ?_⟩
  exact high_joint_moments_deltaGap hbeta G F wide.toCountParameters

/-- Same-data package after the height has been selected. -/
theorem exists_actual_same_data_chosen_height
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta) :
    ∃D : HighDataPerturbed HighFrontierTargets.positiveGap,
      ∃hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200,
      let G := momentGeometryOfPerturbed D hfine
      ∃F : PerturbedSourceData G,
      ∃wide : WideCountParameters F.modulus ⊤ G.t,
      ∃theta : ℝ, 0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
        4 * theta < (1 / 200 : ℝ) * G.cost ∧ theta < G.t ∧
        2 * theta ≤ G.t ∧ theta * (2 + 4 * G.eps) < G.t ∧
        ∀eta : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop,
          SourceMomentBoundAt F.modulus ⊤ le_top F.S F.exclusions F.maximal
            G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
            HighFrontierTargets.positiveGap G.t wide.toCountParameters
            eta Z theta (C * Z ^ G.t) (Z ^ (2 * theta)) := by
  obtain ⟨D, hfine, F, wide, hmom⟩ :=
    exists_actual_same_data_deltaGap_moments hbeta
  refine ⟨D, hfine, F, wide, ?_⟩
  exact chosen_height_deltaGap
    (momentGeometryOfPerturbed D hfine) F wide.toCountParameters hmom

end SevenEighths.PerturbedMomentConstruction

end

end OAI
