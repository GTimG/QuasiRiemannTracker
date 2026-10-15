import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.PrimeRows.TotalECanonicalLargeTail
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.SameDataCanonicalSmallTail

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set MeasureTheory
namespace SevenEighths.PerturbedCanonicalLocalPrep
open HeckeFamily ProbePhysical ProbeMellinBoundary
open HeckeInverseAmplification hiding PrimeIdeal
open SevenEighths.Parameters SevenEighths.PerturbedCentral
open SevenEighths.PerturbedMomentConstruction SevenEighths.ProbeHighRowFamily
local notation "O" => HeckeFamily.O

/-- Actual D slots, F windows/source, and actual dyadic physical rows. -/
theorem same_D_canonical_large_band
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (delta saving : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃C : ℝ, 0 < C ∧ ∀(eta : Character) (Z : ℝ), 1 ≤ Z →
      ∀(T : Fin D.N → Finset PrimeIdeal)
      (hT : ∀i P, P ∈ T i → P.val ∉ F.S),
      (∀P : (∀i, T i), Function.Injective (fun i => (P i).val)) →
      Summable (fun k : ℕ => finitePhysicalRows F.S F.maximal eta
        (dyadicRows (Z ^ (physicalHeight + D.t)) k) T
        (fun _ y => (F.w y : ℂ)) (fun j => Z ^ D.ell j) F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z) ∧
      (∑'k : ℕ, ‖finitePhysicalRows F.S F.maximal eta
        (dyadicRows (Z ^ (physicalHeight + D.t)) k) T
        (fun _ y => (F.w y : ℂ)) (fun j => Z ^ D.ell j) F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z‖) ≤
        C * (eta.modulus.absNorm : ℝ) ^ delta * Z ^ (-saving) := by
  obtain ⟨C, hC, hlarge⟩ := canonical_large_original_tail_same_D_totalE D D.N
    delta 1 2 1 saving hdelta hdelta1
    (by norm_num) (by norm_num) (by norm_num)
    F.S F.exclusions F.maximal
    (F.first.mono_parameter (by
      change 4 * D.e ≤ (1 / 4 : ℝ)
      have he := D.e_small
      linarith only [he]))
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support
  refine ⟨C, hC, ?_⟩
  intro eta Z hZ T hT hdis
  have hsum := SevenEighths.PerturbedSameDataCentral.same_D_totalE D
  have hfun : (fun y => (F.w y : ℂ)) = F.W :=
    funext fun y => (F.complex_eq y).symm
  have hWS : ∀i : Fin D.N, Function.support (fun y => (F.w y : ℂ)) ⊆ Icc 1 2 := by
    intro i
    rw [hfun]
    exact F.complex_support
  have hWB : ∀(i : Fin D.N) y, ‖(F.w y : ℂ)‖ ≤ 1 := by
    intro i y
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (F.bounded y).1] using (F.bounded y).2
  exact hlarge eta Z hZ T hT hdis D.ell
    (fun j => (D.slots_bounds j).1.le) hsum (fun _ y => (F.w y : ℂ)) hWS hWB

end SevenEighths.PerturbedCanonicalLocalPrep
end
end OAI
