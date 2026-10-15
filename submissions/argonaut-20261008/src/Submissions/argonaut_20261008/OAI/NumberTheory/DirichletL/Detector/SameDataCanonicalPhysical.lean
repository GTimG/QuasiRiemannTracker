import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.PrimeRows.SameDataCanonicalRayCube
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.SameDataCanonicalLargeTail
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.SameDataCanonicalTailNormalization

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

/-- Complete proof body for the unchanged actual canonical interface.
This additive candidate has not been elaborated or admitted. -/
theorem same_data_canonical_physical_at
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hbeta : boundary < HeckeZeroSupremum.beta)
    (theta : ℝ) (htheta : 0 < theta) :
    SevenEighths.PerturbedCanonicalFrontier.SameDataCanonicalPhysicalAt D hfine F theta := by
  letI : NeZero (∏P∈F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  obtain ⟨Ca, hCa, n, hn, hcanonical⟩ :=
    canonical_probe_exists_ray_cube_same_D F.modulus ⊤ le_top D
      D.e (1 / 2) 1 2 1 D.t theta
      D.e_pos D.e_small (by norm_num) (by norm_num) htheta
      (by norm_num) (by norm_num) (by norm_num) hbeta
      F.S F.exclusions F.maximal F.first F.W F.W
      1 2 1 2 (by norm_num) (by norm_num)
      F.complex_support F.complex_support
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
  unfold SevenEighths.PerturbedCanonicalFrontier.SameDataCanonicalPhysicalAt
  refine ⟨n, hn, ?_⟩
  intro eta
  let C : ℝ := 2 * Ca * (eta.modulus.absNorm : ℝ) ^ 2 * Cn
  have hQ : (0 : ℝ) < eta.modulus.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr eta.modulus_ne_bot)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcanonical, hnormer,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass F.modulus ⊤) F.S
      (fun _ : Fin D.N => (1 : ℝ)) (fun _ => (2 : ℝ)) D.ell
      (fun _ => by norm_num) (fun _ => by norm_num) D.slots_injective,
    eventually_ge_atTop (1 : ℝ)] with Z hcan hnorm hdis hZ
  dsimp only at hnorm ⊢
  let Y : Fin D.N → ℝ := fun j => Z ^ D.ell j
  let T : Fin D.N → Finset PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
  let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
    (Probe.principalScalar Finset.univ Z totalE
      (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
  have hT : ∀i P, P ∈ T i → P.val ∉ F.S := by
    intro i P hP
    exact (mem_pool _ F.S 1 2 (Y i) P).mp hP |>.2.2.2
  have hpool : ∀i P, P ∈ T i → (P.val.absNorm : ℝ) ≤ 2 * Z ^ D.ell i := by
    intro i P hP
    have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
    have hp := (pool_norm_bounds (RayQuotient.identityClass F.modulus ⊤) F.S
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
      (Real.rpow_pos_of_pos hZ0 _) P hP).2
    simpa only [Y, mul_comm] using hp
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
  obtain ⟨idx, grid, hlabels, hbins, hray, herr⟩ :=
    hcan eta T hT hdis hpool (fun _ y => (F.w y : ℂ)) hWS hWB
  refine ⟨hnorm.1, idx, grid, hlabels, hbins, hray, ?_⟩
  let rows := rowBand (Z ^ (1 / 100 : ℝ)) (Z ^ (physicalHeight + D.t))
  let alpha : FreeRow → ℝ := fun u => 51 / 100 + D.e * grid u
  let height : FreeRow → ℝ := fun u => (3 * idx u + 1 : ℕ) * Z ^ theta
  let A : ℂ := compensatedPhysicalProbe eta (calibrationForSet F.S F.maximal) F.W F.W
    (fun j => canonicalSlotSupport (T j)) (fun _ y => (F.w y : ℂ)) Y
    (Z ^ sourceLx) (Z ^ sourceLy) Z
  let B : ℂ := principalPhysicalPool eta F.S T (fun _ y => (F.w y : ℂ)) Y
    F.W F.W (Z ^ sourceLx) (Z ^ sourceLy) Z
  let G : ℂ := finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T hT
    (fun _ y => (F.w y : ℂ)) Y F.W F.W
    (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height
  change ‖A / normer - B / normer - G / normer‖ ≤ _
  rw [← sub_div, ← sub_div, div_eq_mul_inv, norm_mul]
  have hb : ‖A - B - G‖ ≤ Ca * (eta.modulus.absNorm : ℝ) ^ 2 *
      (Z ^ (HeckeZeroSupremum.beta - 11 / 16 - 63 / 800 +
          8 * D.e + 51 * rho0 / 100) + Z ^ (-D.t)) := herr
  apply (mul_le_mul hb hnorm.2 (norm_nonneg _) (by positivity)).trans
  calc
    _ = (Ca * (eta.modulus.absNorm : ℝ) ^ 2 * Cn) *
        ((Z ^ (HeckeZeroSupremum.beta - 11 / 16 - 63 / 800 +
            8 * D.e + 51 * rho0 / 100) + Z ^ (-D.t)) * Z ^ (D.t / 8)) := by ring
    _ ≤ (Ca * (eta.modulus.absNorm : ℝ) ^ 2 * Cn) *
        (2 * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma)) :=
      mul_le_mul_of_nonneg_left (same_D_canonical_error_power D hbeta hZ) (by positivity)
    _ = _ := by dsimp [C]; ring

/-- Choose theta from the actual datum before all eta and canonical constants. -/
theorem exists_same_data_canonical_physical_at
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hbeta : boundary < HeckeZeroSupremum.beta)
    (J : ℝ) (hJ : 0 ≤ J) :
    ∃theta : ℝ, 0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
      4 * theta < (1 / 200 : ℝ) * D.cost ∧ theta < D.t ∧
      2 * theta * (1 + J) ≤ D.t ∧ theta * (2 + 4 * D.eps) < D.t ∧
      2 * theta ≤ D.t ∧
      SevenEighths.PerturbedCanonicalFrontier.SameDataCanonicalPhysicalAt D hfine F theta := by
  obtain ⟨theta, hp, hd, hc, ht, hJc, heps, h2⟩ := exists_canonical_theta_same_D D J hJ
  exact ⟨theta, hp, hd, hc, ht, hJc, heps, h2,
    same_data_canonical_physical_at D hfine F hbeta theta hp⟩

end SevenEighths.PerturbedCanonicalLocalPrep
end
end OAI
