import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedJointSource

namespace OAI.SevenEighths.PerturbedMomentConstruction

noncomputable section
open scoped Classical BigOperators
open HeckeFamily ProbeHighRowFamily ProbeFinalAssembly Parameters
open HighFrontierTargets PerturbedCountBridge PerturbedCountProjection
open ProbePhysical (PrimeIdeal)

/-!
Additive constructor candidate, NOT_RUN.

The data D and a finite cutoff depending on D are fixed before choosing the
common source F. The source modulus, windows, counts and height are obtained
from that single F. No analytic estimate is supplied as an assumption.
-/

/-- Choose one source, counts and moment height for an already fixed D. -/
theorem exists_fixed_data_cutoff_source_counts_chosen_height
    (hbeta : sigmaBoundary < HeckeZeroSupremum.beta)
    (D : HighDataPerturbed positiveGap)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (Ncut : ℕ) :
    let G := momentGeometryOfPerturbed D hfine
    ∃F : PerturbedSourceData G,
      (∀P : PrimeIdeal, P.val.absNorm ≤ Ncut → P.val ∈ F.S) ∧
      ∃wide : WideCountParameters F.modulus ⊤ G.t,
      ∃theta : ℝ, 0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
        4 * theta < (1 / 200 : ℝ) * G.cost ∧ theta < G.t ∧
        2 * theta ≤ G.t ∧ theta * (2 + 4 * G.eps) < G.t ∧
        ∀eta : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in Filter.atTop,
          SourceMomentBoundAt
            F.modulus ⊤ le_top F.S F.exclusions F.maximal
            G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
            positiveGap G.t wide.toCountParameters
            eta Z theta (C * Z ^ G.t) (Z ^ (2 * theta)) := by
  let G := momentGeometryOfPerturbed D hfine
  obtain ⟨F, hcut⟩ := exists_perturbed_source_data_with_norm_cutoff G Ncut
  obtain ⟨wide⟩ := source_wide_count_parameters G F
  refine ⟨F, hcut, wide, ?_⟩
  exact chosen_height_deltaGap G F wide.toCountParameters
    (high_joint_moments_deltaGap hbeta G F wide.toCountParameters)

/-- A cutoff depending on D is chosen after D and before the common source. -/
theorem exists_D_first_cutoff_source_counts_chosen_height
    (hbeta : sigmaBoundary < HeckeZeroSupremum.beta)
    (cutoff : HighDataPerturbed positiveGap → ℕ) :
    ∃D : HighDataPerturbed positiveGap,
      ∃hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200,
      let G := momentGeometryOfPerturbed D hfine
      ∃F : PerturbedSourceData G,
        (∀P : PrimeIdeal, P.val.absNorm ≤ cutoff D → P.val ∈ F.S) ∧
        ∃wide : WideCountParameters F.modulus ⊤ G.t,
        ∃theta : ℝ, 0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
          4 * theta < (1 / 200 : ℝ) * G.cost ∧ theta < G.t ∧
          2 * theta ≤ G.t ∧ theta * (2 + 4 * G.eps) < G.t ∧
          ∀eta : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in Filter.atTop,
            SourceMomentBoundAt
              F.modulus ⊤ le_top F.S F.exclusions F.maximal
              G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
              positiveGap G.t wide.toCountParameters
              eta Z theta (C * Z ^ G.t) (Z ^ (2 * theta)) := by
  have hgap : 0 < positiveGap := by
    unfold positiveGap
    linarith
  obtain ⟨D, hfine, _ht, _hN, _hell, _he⟩ :=
    exists_perturbed_data_with_moment_geometry positiveGap hgap
  exact ⟨D, hfine,
    exists_fixed_data_cutoff_source_counts_chosen_height
      hbeta D hfine (cutoff D)⟩

end
end OAI.SevenEighths.PerturbedMomentConstruction
