import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.PrimeRows.TotalECanonicalSmallTailFirst87
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.SameDataCanonicalBudgets

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set MeasureTheory
namespace SevenEighths.PerturbedCanonicalLocalPrep
open HeckeFamily ProbePhysical ProbeMellinBoundary
open HeckeInverseAmplification hiding PrimeIdeal
open SevenEighths.ProbeHighRowFamily SevenEighths.ProbeFinalAssembly
open SevenEighths.PerturbedCentral SevenEighths.PerturbedMomentConstruction
open SevenEighths.Parameters
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

/-- The actual physical small row band at D.ell and F's same windows/source. -/
theorem same_D_canonical_small_band
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hbeta : boundary < HeckeZeroSupremum.beta)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1 / 2) :
    ∃C : ℝ, 0 < C ∧ ∀(eta : Character) (Z : ℝ), 1 ≤ Z →
      ∀(T : Fin D.N → Finset PrimeIdeal)
      (hT : ∀i P, P ∈ T i → P.val ∉ F.S),
      (∀P : (∀i, T i), Function.Injective (fun i => (P i).val)) →
      ‖finitePhysicalRows F.S F.maximal eta (rowBand 1 (Z ^ (1 / 100 : ℝ))) T
        (fun _ y => (F.w y : ℂ)) (fun i => Z ^ D.ell i) F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z‖ ≤
        C * (eta.modulus.absNorm : ℝ) ^ delta *
          Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma - D.t / 8) := by
  obtain ⟨C, hC, hb⟩ := canonical_small_original_tail_totalE_first87 D.N
    D.e delta 1 2 1 D.e_pos D.e_small hdelta hdelta1
    (by norm_num) (by norm_num) (by norm_num) hbeta
    F.S F.exclusions F.maximal F.first F.W F.W 1 2 1 2
    (by norm_num) (by norm_num) F.complex_support F.complex_support
  refine ⟨C, hC, ?_⟩
  intro eta Z hZ T hT hdis
  have hell : ∀i, 0 ≤ D.ell i := fun i => (D.slots_bounds i).1.le
  have hsum : ∑i, D.ell i = totalE :=
    SevenEighths.PerturbedSameDataCentral.same_D_totalE D
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
  have hbound := hb eta Z hZ T hT hdis D.ell hell hsum
    (fun _ y => (F.w y : ℂ)) hWS hWB
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (same_D_small_power D HeckeZeroSupremum.beta Z hZ) (by positivity))

/-- Full actual normalized small-band bound; no canonical or transport input. -/
theorem same_D_normalized_canonical_small_band
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hbeta : boundary < HeckeZeroSupremum.beta)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1 / 2) :
    letI : NeZero (∏P∈F.S, P) :=
      ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
    ∀eta : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop,
      let Y : Fin D.N → ℝ := fun j => Z ^ D.ell j
      let T : Fin D.N → Finset PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
      let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
        (Probe.principalScalar Finset.univ Z totalE
          (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
      normer ≠ 0 ∧
      ‖finitePhysicalRows F.S F.maximal eta (rowBand 1 (Z ^ (1 / 100 : ℝ))) T
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z / normer‖ ≤
        C * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) := by
  letI : NeZero (∏P∈F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  obtain ⟨Cs, hCs, hsmall⟩ := same_D_canonical_small_band
    D hfine F hbeta delta hdelta hdelta1
  have hsum := SevenEighths.PerturbedSameDataCentral.same_D_totalE D
  obtain ⟨Cn, hCn, hnormer⟩ := actual_ray_normalizer_inverse_totalE F.modulus ⊤ le_top
    F.S F.exclusions 1 2 (by norm_num) (by norm_num)
    D.ell (fun j => (D.slots_bounds j).1) hsum
    (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact)
    (fun _ => F.support) (fun _ y => (F.bounded y).1) (fun _ => F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real
    F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t / 8) (by have ht := D.t_pos; positivity)
  intro eta
  let C : ℝ := Cs * (eta.modulus.absNorm : ℝ) ^ delta * Cn
  have hQ : (0 : ℝ) < eta.modulus.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr eta.modulus_ne_bot)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos hCs (Real.rpow_pos_of_pos hQ delta)) hCn
  refine ⟨C, hC, ?_⟩
  filter_upwards [hnormer,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass F.modulus ⊤) F.S
      (fun _ : Fin D.N => (1 : ℝ)) (fun _ => (2 : ℝ)) D.ell
      (fun _ => by norm_num) (fun _ => by norm_num) D.slots_injective,
    eventually_ge_atTop (1 : ℝ)] with Z hn hdis hZ
  dsimp only at hn ⊢
  let Y : Fin D.N → ℝ := fun j => Z ^ D.ell j
  let T : Fin D.N → Finset PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
  let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
    (Probe.principalScalar Finset.univ Z totalE
      (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
  have hT : ∀i P, P ∈ T i → P.val ∉ F.S := by
    intro i P hP
    exact (mem_pool _ F.S 1 2 (Y i) P).mp hP |>.2.2.2
  have hb := hsmall eta Z hZ T hT hdis
  refine ⟨hn.1, ?_⟩
  change ‖finitePhysicalRows F.S F.maximal eta (rowBand 1 (Z ^ (1 / 100 : ℝ))) T
    (fun _ y => (F.w y : ℂ)) Y F.W F.W
    (Z ^ sourceLx) (Z ^ sourceLy) Z / normer‖ ≤ _
  rw [div_eq_mul_inv, norm_mul]
  apply (mul_le_mul hb hn.2 (norm_nonneg _) (by positivity)).trans_eq
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hp : Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma - D.t / 8) *
      Z ^ (D.t / 8) = Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) := by
    rw [← Real.rpow_add hZ0]
    congr 1
    ring
  calc
    _ = C * (Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma - D.t / 8) *
        Z ^ (D.t / 8)) := by dsimp [C]; ring
    _ = _ := by rw [hp]

end SevenEighths.PerturbedCanonicalLocalPrep
end
end OAI
