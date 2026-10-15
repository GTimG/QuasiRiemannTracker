import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedMomentDeltaLift
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalProduct

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.PerturbedMomentConstruction

open HeckeFamily ProbeHighRowFamily ProbeFinalAssembly Parameters
open HighFrontierTargets PerturbedCountBridge PerturbedCountProjection
open ProbePhysical (PrimeIdeal)

local notation "O" => HeckeFamily.O

/-!
# A single source set chosen after all finite cutoff seeds

The future Euler producer may require finitely many additional prime ideals.
They must be supplied before the product modulus, window and count constants
are fixed.  This module exposes precisely that ordering: a finite prime seed is
first enlarged once, and the resulting `F` is thereafter the common source for
moments, First-region estimates and the principal handoff.
-/

structure SourceCutoffSeed where
  primes : Finset (Ideal O)
  prime : ∀P∈primes, Prime P

/-- Construct the perturbed source while retaining every prime in the seed. -/
theorem exists_perturbed_source_data_extending
    (G : MomentGeometry) (seed : SourceCutoffSeed) :
    ∃F : PerturbedSourceData G, seed.primes ⊆ F.S := by
  obtain ⟨S0, hseed, hS0, hfirst0, _hmax0⟩ :=
    Parameters.exists_fixed_source auxiliaryHighData.e auxiliaryHighData.e_pos
      seed.primes seed.prime
  obtain ⟨S, hsub, hS, hfirst, hmax⟩ :=
    Parameters.exists_fixed_source G.e G.e_pos S0 hS0.prime
  have hfirstAux : FirstTail (4 * auxiliaryHighData.e) S :=
    FirstTail.mono_finset hsub hfirst0
  obtain ⟨w, W, hw, hc, hs, hp, hb, hn, he, hWn, hWs, hr, hWpos⟩ :=
    Parameters.exists_fixed_probe_window
  let core : ProbeFinalAssembly.SourceData auxiliaryHighData := {
    S := S
    exclusions := hS
    maximal := hmax
    first := hfirstAux
    w := w
    W := W
    smooth := hw
    compact := hc
    support := hs
    positive_support := hp
    bounded := hb
    nonzero := hn
    complex_eq := he
    complex_nonzero := hWn
    complex_support := hWs
    real := hr
    nonnegative := hWpos }
  refine ⟨⟨core, hfirst⟩, ?_⟩
  exact hseed.trans hsub

/--
After the seed is fixed, construct the one common source, one wide package and
its projected official moment output.  Hence the modulus and all four count
constants are chosen only after the future finite cutoff has been incorporated.
-/
theorem exists_seeded_source_counts_and_delta_moments
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (G : MomentGeometry) (seed : SourceCutoffSeed) :
    ∃F : PerturbedSourceData G, seed.primes ⊆ F.S ∧
      ∃wide : WideCountParameters F.modulus ⊤ G.t,
        HighFrontierTargets.HighJointMomentOutputAt
          F.modulus ⊤ le_top F.S F.exclusions F.maximal
          G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
          HighFrontierTargets.positiveGap G.t wide.toCountParameters := by
  obtain ⟨F, hseed⟩ := exists_perturbed_source_data_extending G seed
  obtain ⟨wide⟩ := source_wide_count_parameters G F
  refine ⟨F, hseed, wide, ?_⟩
  exact high_joint_moments_deltaGap hbeta G F wide.toCountParameters

/--
Full actual f630 ordering with a predeclared finite Euler seed and chosen
height.  The returned moment height remains `Z^(2*theta)`.
-/
theorem exists_actual_seeded_same_data_chosen_height
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (seed : SourceCutoffSeed) :
    ∃D : Parameters.HighDataPerturbed HighFrontierTargets.positiveGap,
      ∃hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200,
      let G := momentGeometryOfPerturbed D hfine
      ∃F : PerturbedSourceData G, seed.primes ⊆ F.S ∧
      ∃wide : WideCountParameters F.modulus ⊤ G.t,
      ∃theta : ℝ, 0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
        4 * theta < (1 / 200 : ℝ) * G.cost ∧ theta < G.t ∧
        2 * theta ≤ G.t ∧ theta * (2 + 4 * G.eps) < G.t ∧
        ∀eta : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in Filter.atTop,
          HighFrontierTargets.SourceMomentBoundAt
            F.modulus ⊤ le_top F.S F.exclusions F.maximal
            G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
            HighFrontierTargets.positiveGap G.t wide.toCountParameters
            eta Z theta (C * Z ^ G.t) (Z ^ (2 * theta)) := by
  have hgap : 0 < HighFrontierTargets.positiveGap := by
    unfold HighFrontierTargets.positiveGap
    linarith
  obtain ⟨D, hfine, _ht, _hN, _hell, _he⟩ :=
    exists_perturbed_data_with_moment_geometry
      HighFrontierTargets.positiveGap hgap
  let G := momentGeometryOfPerturbed D hfine
  obtain ⟨F, hseed, wide, hmom⟩ :=
    exists_seeded_source_counts_and_delta_moments hbeta G seed
  refine ⟨D, hfine, F, hseed, wide, ?_⟩
  exact chosen_height_deltaGap G F wide.toCountParameters hmom

/-- Empty seed recovers the source construction used by the moment file. -/
theorem exists_perturbed_source_data_from_empty (G : MomentGeometry) :
    Nonempty (PerturbedSourceData G) := by
  let seed : SourceCutoffSeed := {
    primes := ∅
    prime := by simp }
  obtain ⟨F, _⟩ := exists_perturbed_source_data_extending G seed
  exact ⟨F⟩

/--
A finite norm cutoff can be incorporated before source construction.  This is
the concrete interface a principal/Euler producer can use once it returns a
natural cutoff.
-/
theorem exists_perturbed_source_data_with_norm_cutoff
    (G : MomentGeometry) (N : ℕ) :
    ∃F : PerturbedSourceData G,
      ∀P : PrimeIdeal, P.val.absNorm ≤ N → P.val ∈ F.S := by
  let seedSet : Finset (Ideal O) := ProbeEuler.smallPrimeSet N
  let seed : SourceCutoffSeed := {
    primes := seedSet
    prime := by
      intro P hP
      exact (Finset.mem_filter.mp hP).2 }
  obtain ⟨F, hseed⟩ := exists_perturbed_source_data_extending G seed
  refine ⟨F, ?_⟩
  intro P hP
  apply hseed
  exact (ProbeEuler.mem_smallPrimeSet N P).mpr hP


/--
The norm-cutoff version of the complete same-data construction.  The cutoff is
inserted before `F.modulus`, the window and both count interfaces are chosen.
This is the concrete ordering required by the future Euler producer.
-/
theorem exists_actual_norm_cutoff_same_data_chosen_height
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (Ncut : ℕ) :
    ∃D : Parameters.HighDataPerturbed HighFrontierTargets.positiveGap,
      ∃hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200,
      let G := momentGeometryOfPerturbed D hfine
      ∃F : PerturbedSourceData G,
        (∀P : PrimeIdeal, P.val.absNorm ≤ Ncut → P.val ∈ F.S) ∧
      ∃wide : WideCountParameters F.modulus ⊤ G.t,
      ∃theta : ℝ, 0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
        4 * theta < (1 / 200 : ℝ) * G.cost ∧ theta < G.t ∧
        2 * theta ≤ G.t ∧ theta * (2 + 4 * G.eps) < G.t ∧
        ∀eta : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in Filter.atTop,
          HighFrontierTargets.SourceMomentBoundAt
            F.modulus ⊤ le_top F.S F.exclusions F.maximal
            G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
            HighFrontierTargets.positiveGap G.t wide.toCountParameters
            eta Z theta (C * Z ^ G.t) (Z ^ (2 * theta)) := by
  let seedSet : Finset (Ideal O) := ProbeEuler.smallPrimeSet Ncut
  let seed : SourceCutoffSeed := {
    primes := seedSet
    prime := by
      intro P hP
      exact (Finset.mem_filter.mp hP).2 }
  obtain ⟨D, hfine, F, hseed, wide, hheight⟩ :=
    exists_actual_seeded_same_data_chosen_height hbeta seed
  refine ⟨D, hfine, F, ?_, wide, hheight⟩
  intro P hP
  apply hseed
  exact (ProbeEuler.mem_smallPrimeSet Ncut P).mpr hP

end SevenEighths.PerturbedMomentConstruction

end

end OAI
