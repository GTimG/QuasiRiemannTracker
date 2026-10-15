import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedPrincipalPerCharacterInterfaces
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedJointSource
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowPerturbedSourceConsumer
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Hecke.CommonProbeBoundaryGeneric
import Submissions.argonaut_20261008.PrincipalProductSigma

namespace OAI.SevenEighths.PerturbedCommonProbeAssembly

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set Asymptotics
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeFinalAssembly
open Parameters PrincipalSignalComparison
open PerturbedMomentConstruction PerturbedCountBridge PerturbedCountProjection
open PerturbedCentral PerturbedCanonicalFrontier
open PerturbedPrincipalPerCharacterInterfaces

local notation "O" => HeckeFamily.O

/-!
Additive assembly candidate, NOT_RUN. All owner estimates remain explicitly
OPEN inputs. No common-probe goal or final nonvanishing is assumed as a datum
field. Every physical function below uses the same D, F, S and count record.
-/

/-- Exactly the shared physical function, retaining the total-E normalizer. -/
def sameProbe {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (eta : Character) : ℝ → ℂ :=
  HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions F.maximal
    D.ell 1 2 (fun _ => F.w) F.W F.W totalE sourceLx sourceLy eta

/-- The height is chosen from the actual joint moment output BEFORE eta. -/
def chosenTheta {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (wide : WideCountParameters F.modulus ⊤ D.t)
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta) : ℝ :=
  Classical.choose (chosen_height_deltaGap (momentGeometryOfPerturbed D hfine)
    F wide.toCountParameters
    (high_joint_moments_deltaGap hbeta (momentGeometryOfPerturbed D hfine)
      F wide.toCountParameters))

/-- Actual C_eta*Z^D.t moments at the exact Z^(2*theta) height. -/
theorem chosenTheta_spec {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (wide : WideCountParameters F.modulus ⊤ D.t)
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta) :
    let theta := chosenTheta D hfine F wide hbeta
    0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
      4 * theta < (1 / 200 : ℝ) * D.cost ∧ theta < D.t ∧
      2 * theta ≤ D.t ∧ theta * (2 + 4 * D.eps) < D.t ∧
      ∀eta : Character, ∃C0 : ℝ, 0 < C0 ∧ ∀ᶠZ : ℝ in atTop,
        HighFrontierTargets.SourceMomentBoundAt F.modulus ⊤ le_top F.S
          F.exclusions F.maximal D.ell (fun _ => F.w)
          (1 / 200) (7 / 8) 2 D.ε D.t D.t D.t
          HighFrontierTargets.positiveGap D.t wide.toCountParameters
          eta Z theta (C0 * Z ^ D.t) (Z ^ (2 * theta)) := by
  exact Classical.choose_spec
    (chosen_height_deltaGap (momentGeometryOfPerturbed D hfine) F
      wide.toCountParameters
      (high_joint_moments_deltaGap hbeta (momentGeometryOfPerturbed D hfine)
        F wide.toCountParameters))

/-- Terminal real-power Big-O conversion using the actual existing lemma. -/
lemma power_bigO (f : ℝ → ℂ) (r : ℝ)
    (h : ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop, ‖f Z‖ ≤ C * Z ^ r) :
    f =O[atTop] (fun Z : ℝ => Z ^ r) := by
  exact ProbeFinalAssembly.isBigO_rpow_of_eventual_norm_bound f r h

/-- The low result is for the identical high-parent physical function. -/
theorem same_probe_low_power_bigO {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (loss : ℝ) (hloss : 0 < loss) (eta : Character) :
    sameProbe D hfine F eta =O[atTop]
      (fun Z : ℝ => Z ^ (HighFrontierTargets.sigmaBoundary - 11 / 16 + loss)) := by
  simpa only [sameProbe, momentGeometryOfPerturbed,
    HighFrontierTargets.totalE, HighFrontierTargets.lx, HighFrontierTargets.ly,
    HighFrontierTargets.rho, PerturbedCentral.totalE, PerturbedCentral.sourceLx,
    PerturbedCentral.sourceLy, PerturbedCentral.rho0] using
    LowPerturbedSourceConsumer.normalizedProbeAt_low_perturbed
      D hfine F loss hloss eta

/-- Owner outputs are consumed on the same D/F/counts and the chosen height.
The moments premise of HighProbeOutputAt is supplied internally, not assumed. -/
theorem same_probe_error_power_bigO {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (wide : WideCountParameters F.modulus ⊤ D.t)
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (hcanonical : SameDataCanonicalPhysicalAt D hfine F
      (chosenTheta D hfine F wide hbeta))
    (heuler : EulerPrincipalRawPerCharacterAt D hfine F) :
    ∀eta : Character,
      (fun Z => sameProbe D hfine F eta Z -
        HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection eta F.S) (-11 / 16) Z) =O[atTop]
        (fun Z : ℝ => Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma)) := by
  obtain ⟨htheta, hthetad, hthetacost, _hthetat, htheta2, hthetaeps, hsource⟩ :=
    chosenTheta_spec D hfine F wide hbeta
  have hbeta' : boundary < HeckeZeroSupremum.beta := by
    simpa only [boundary, rho0, HighFrontierTargets.sigmaBoundary,
      HighFrontierTargets.rho] using hbeta
  have hhigh := highProbeOutputAt_of_remaining_interfaces_per_character
    D hfine F wide hbeta' htheta hthetad hthetacost htheta2 hthetaeps
    ⟨hcanonical, heuler⟩
  unfold HighFrontierTargets.HighProbeOutputAt at hhigh
  obtain ⟨C, hC, hhigh⟩ := hhigh
  intro eta
  obtain ⟨Ct, hCt, hhighEta⟩ := hhigh eta
  obtain ⟨C0, hC0, hsourceEta⟩ := hsource eta
  apply power_bigO
  refine ⟨Ct + C * C0 * (eta.modulus.absNorm : ℝ) ^ (2 * D.eps),
    by positivity, ?_⟩
  filter_upwards [hhighEta, hsourceEta] with Z hhighZ hsourceZ
  simpa only [sameProbe] using hhighZ C0 hC0.le hsourceZ

/-- The actual principal product cutoff, chosen before the source F. -/
def principalCutoff : ℕ :=
  Classical.choose ProbeEuler.exists_uniform_principal_cutoff_tau

theorem principalCutoff_spec :
    4 ≤ principalCutoff ∧ ∀S : Finset (Ideal O),
      (∀P : PrimeIdeal, P.val.absNorm ≤ principalCutoff → P.val ∈ S) →
      ∀eta : Character,
        AnalyticOnNhd ℂ (ProbeEuler.principalCorrection eta S)
          {s : ℂ | HighFrontierTargets.sigmaBoundary < s.re} ∧
        ∀s : ℂ, HighFrontierTargets.sigmaBoundary < s.re →
          ‖ProbeEuler.principalCorrection eta S s - 1‖ ≤ 1 / 2 := by
  have hboundary : HighFrontierTargets.sigmaBoundary = (3499999 / 4000000 : ℝ) := by
    norm_num [HighFrontierTargets.sigmaBoundary, HighFrontierTargets.rho]
  simpa only [principalCutoff, hboundary] using
    Classical.choose_spec ProbeEuler.exists_uniform_principal_cutoff_tau

/-- The coefficient mask and correction are on the SAME S as the probe. -/
theorem same_source_analytic_at_boundary {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hcut : ∀P : PrimeIdeal, P.val.absNorm ≤ principalCutoff → P.val ∈ F.S)
    (eta : Character) :
    (∀I, idealCoeff (eta.excludePrimes F.S F.exclusions.prime) I =
      if IsCoprime I (eta.excludePrimes F.S F.exclusions.prime).modulus
        then idealCoeff eta I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection eta F.S)
      {s : ℂ | HighFrontierTargets.sigmaBoundary < s.re} ∧
    (∀s : ℂ, HighFrontierTargets.sigmaBoundary < s.re →
      ‖sourceCorrection eta F.S s - 1‖ ≤ 1 / 2) := by
  have hprincipal := principalCutoff_spec.2 F.S hcut eta
  have heq : sourceCorrection eta F.S = ProbeEuler.principalCorrection eta F.S :=
    sourceCorrection_eq_principal eta F.S F.exclusions
  refine ⟨excludePrimes_mask eta F.S F.exclusions.prime, ?_, ?_⟩
  · simpa only [heq] using hprincipal.1
  · simpa only [heq] using hprincipal.2

/-- The actual final contract; only canonical/Euler owner estimates remain OPEN. -/
theorem primitive_contract_of_same_data_owner_outputs
    (D : HighDataPerturbed HighFrontierTargets.positiveGap)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (wide : WideCountParameters F.modulus ⊤ D.t)
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (hcut : ∀P : PrimeIdeal, P.val.absNorm ≤ principalCutoff → P.val ∈ F.S)
    (hcanonical : SameDataCanonicalPhysicalAt D hfine F
      (chosenTheta D hfine F wide hbeta))
    (heuler : EulerPrincipalRawPerCharacterAt D hfine F) :
    HeckeCommonProbe.PrimitiveContractBoundary
      HighFrontierTargets.sigmaBoundary D.t D.sigma := by
  intro eta _hprimitive
  obtain ⟨hmask, hanalytic, hhalf⟩ :=
    same_source_analytic_at_boundary D hfine F hcut eta
  refine ⟨eta.excludePrimes F.S F.exclusions.prime,
    sourceCorrection eta F.S, sameProbe D hfine F eta,
    hmask, hanalytic, hhalf, ?_, ?_⟩
  · exact same_probe_low_power_bigO D hfine F D.t D.t_pos eta
  · exact same_probe_error_power_bigO D hfine F wide hbeta hcanonical heuler eta

/-- Merge the two finite cutoffs before D/F/windows/counts/eta. This constructs
the pure common data, not the unresolved canonical or Euler estimate. -/
theorem exists_cutoff_same_data_assembly_inputs
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (Nowner : ℕ) :
    ∃Ncut : ℕ, Nowner ≤ Ncut ∧ principalCutoff ≤ Ncut ∧
      ∃D : HighDataPerturbed HighFrontierTargets.positiveGap,
      ∃hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200,
      ∃F : PerturbedSourceData (momentGeometryOfPerturbed D hfine),
        (∀P : PrimeIdeal, P.val.absNorm ≤ Ncut → P.val ∈ F.S) ∧
        Nonempty (WideCountParameters F.modulus ⊤ D.t) := by
  let Ncut := max Nowner principalCutoff
  have hgap : 0 < HighFrontierTargets.positiveGap := by
    unfold HighFrontierTargets.positiveGap
    linarith
  obtain ⟨D, hfine, _ht, _hN, _hell, _he⟩ :=
    exists_perturbed_data_with_moment_geometry HighFrontierTargets.positiveGap hgap
  obtain ⟨F, hcut⟩ := exists_perturbed_source_data_with_norm_cutoff
    (momentGeometryOfPerturbed D hfine) Ncut
  obtain ⟨wide⟩ := source_wide_count_parameters (momentGeometryOfPerturbed D hfine) F
  exact ⟨Ncut, le_max_left _ _, le_max_right _ _, D, hfine, F, hcut, ⟨wide⟩⟩

/-- Full common-probe assembly, conditional on supplying the two actual owner
outputs on the constructed common data. No final goal is an assumed field. -/
theorem commonProbeConstructionGoalAt_of_same_data_owner_supply
    (hsupply : ∀hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta,
      ∃D : HighDataPerturbed HighFrontierTargets.positiveGap,
      ∃hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200,
      ∃F : PerturbedSourceData (momentGeometryOfPerturbed D hfine),
      ∃wide : WideCountParameters F.modulus ⊤ D.t,
        (∀P : PrimeIdeal, P.val.absNorm ≤ principalCutoff → P.val ∈ F.S) ∧
        SameDataCanonicalPhysicalAt D hfine F (chosenTheta D hfine F wide hbeta) ∧
        EulerPrincipalRawPerCharacterAt D hfine F) :
    HighFrontierTargets.CommonProbeConstructionGoalAt
      HighFrontierTargets.sigmaBoundary := by
  intro hbeta
  obtain ⟨D, hfine, F, wide, hcut, hcanonical, heuler⟩ := hsupply hbeta
  have hgap : 0 < HighFrontierTargets.positiveGap := by
    unfold HighFrontierTargets.positiveGap
    linarith
  have homega : D.t < HeckeZeroSupremum.beta - HighFrontierTargets.sigmaBoundary := by
    have ht := D.t_delta
    unfold HighFrontierTargets.positiveGap at ht hgap
    linarith
  refine ⟨D.t, D.sigma, D.t_pos, homega, D.sigma_pos, ?_⟩
  exact primitive_contract_of_same_data_owner_outputs
    D hfine F wide hbeta hcut hcanonical heuler

/-- Thin handoff to the actual existing boundary consumer, not a new goal. -/
theorem uniformCommonProbeBoundary_of_construction_goal
    (hgoal : HighFrontierTargets.CommonProbeConstructionGoalAt
      HighFrontierTargets.sigmaBoundary) :
    HeckeCommonProbe.UniformCommonProbeBoundary HighFrontierTargets.sigmaBoundary := by
  refine ⟨by norm_num [HighFrontierTargets.sigmaBoundary, HighFrontierTargets.rho],
    by norm_num [HighFrontierTargets.sigmaBoundary, HighFrontierTargets.rho], ?_⟩
  intro hbeta
  obtain ⟨omega, saving, homega, hgap, hsaving, hcontract⟩ := hgoal hbeta
  exact ⟨omega, saving, homega, hgap, hsaving, hcontract⟩

end
end OAI.SevenEighths.PerturbedCommonProbeAssembly
