import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowHighSameProbeGeneric
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.QuasiPerturbationParameters
import Submissions.argonaut_20261008.HighDataMomentGeometry

/-!
Candidate for the actual PI adapter, SHA256 43595c4e...; native replay NOT_RUN.
The auxiliary HighData carrier supplies only the source/window package here.
Every slot is taken from D; every source object is taken from the same F.
-/
namespace OAI.SevenEighths.LowHighSameProbe

noncomputable section
open scoped Classical BigOperators
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeFinalAssembly PerturbedMomentConstruction
local notation "O" => HeckeFamily.O

theorem source_projections_eq {G : MomentGeometry} (F : PerturbedSourceData G) :
    F.S = F.core.S ∧ F.modulus = F.core.modulus ∧
      F.w = F.core.w ∧ F.W = F.core.W := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem geometry_slots_eq {Δ B : ℝ}
    (D : Parameters.HighDataPerturbedBudget Δ B)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200) :
    (momentGeometryOfPerturbed D hfine).N = D.N ∧
      (momentGeometryOfPerturbed D hfine).ell = D.ell ∧
      (momentGeometryOfPerturbed D hfine).e = D.e := by
  exact ⟨rfl, rfl, rfl⟩

/-- The tail certificate is at the actual perturbed e, on the same finite set. -/
theorem source_first_at_actual_e {Δ B : ℝ}
    (D : Parameters.HighDataPerturbedBudget Δ B)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine)) :
    FirstTail (4 * D.e) F.S := by
  exact F.first

/-- The high expression at G.ell equals the low expression at the very same D.ell. -/
theorem normalizedProbeAt_geometry_eq_generic {Δ B : ℝ}
    (D : Parameters.HighDataPerturbedBudget Δ B)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (Etotal lx ly : ℝ) (η : Character) :
    letI : NeZero (∏ P ∈ F.S, P) :=
      ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
    HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions F.maximal
      (momentGeometryOfPerturbed D hfine).ell 1 2 (fun _ => F.w) F.W F.W
      Etotal lx ly η =
    normalizedProbeGeneric Etotal lx ly F.modulus ⊤ F.S F.maximal D.ell
      1 2 (fun _ => F.w) F.W F.W η := by
  letI : NeZero (∏ P ∈ F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  rfl

/-- Exact public scalar definitions coincide; no numerical inequality is needed. -/
theorem frontier_quasi_parameters_eq :
    HighFrontierTargets.totalE = QuasiPerturbationParameters.E ∧
      HighFrontierTargets.lx = QuasiPerturbationParameters.lx ∧
      HighFrontierTargets.ly = QuasiPerturbationParameters.ly := by
  exact ⟨rfl, rfl, rfl⟩

/-- Ready-to-use same-probe handoff for the actual public perturbed parameters. -/
theorem normalizedProbeAt_geometry_eq_quasi {Δ B : ℝ}
    (D : Parameters.HighDataPerturbedBudget Δ B)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (η : Character) :
    letI : NeZero (∏ P ∈ F.S, P) :=
      ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
    HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions F.maximal
      (momentGeometryOfPerturbed D hfine).ell 1 2 (fun _ => F.w) F.W F.W
      HighFrontierTargets.totalE HighFrontierTargets.lx HighFrontierTargets.ly η =
    normalizedProbeGeneric QuasiPerturbationParameters.E
      QuasiPerturbationParameters.lx QuasiPerturbationParameters.ly
      F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W η := by
  letI : NeZero (∏ P ∈ F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  rfl

end
end OAI.SevenEighths.LowHighSameProbe
