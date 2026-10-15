import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedFloorFrontier
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubePrimeBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorDyadic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeBinPartition
import Submissions.argonaut_20261008.PerturbedCentralAssembly

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set

namespace SevenEighths.PerturbedFloorRows

open HeckeFamily ProbePhysical ProbeMellinBoundary
open HeckeInverseAmplification hiding PrimeIdeal
open ProbeRaySlots HeckeDetectorPhysicalSelection
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open SevenEighths.ProbeHighRowFamily
open SevenEighths.PerturbedCentral
open SevenEighths.PerturbedMomentConstruction
open SevenEighths.PerturbedFloorFrontier
open SevenEighths.Parameters

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem floorPoolOutsideTotal
    (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N → ℝ) :
    ∀j P, P ∈ pool (RayQuotient.identityClass M H) S c b (Y j) → P.val ∉ S :=
  fun j P hP => (mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

/-!
## Floor arithmetic with the actual total slot mass

The only change in the old floor arithmetic is the product of slot powers.
It is evaluated by `source_slot_product_total`, so the exponent contains
`totalE * (-3/20 + mesh)` rather than `-1/40 + mesh/6`.
-/

theorem actual_floor_cube_arithmetic_totalE
    (N n : ℕ) (e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (hkappa : 0 < kappa) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hdelta : 0 < delta) (hbudget : 8 * e * R + kappa ≤ epsilon)
    (hgap : epsilon < rmin * mesh) (hmargin : 0 < margin)
    (hheight : 2 * tau < dmin * cost) (hloss : tau * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (4 * e) S) (hmax : ∀P∈S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀j, dmax * rmin ≤ ell j) (hellhi : ∀j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℂ)
    (hWs : ∀j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀j, ContDiff ℝ ∞ (W j)) (hWB : ∀j t, ‖W j t‖ ≤ A)
    (hellsum : ∑j, ell j = totalE) :
    ∃C : ℝ, 0 < C ∧ ∀eta : Character, ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ, dmin ≤ d → d ≤ dmax → ∀v : ℝ, 0 ≤ v →
      ∀rows : Finset FreeRow,
      (∀u∈rows, u.val ≠ 1 ∧ Z ^ delta ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (d - margin)) →
      (∀u∈rows, Z ^ v ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z ^ v) →
      ∀i : ℕ, i ≤ n →
      (∀u∈rows, detectorMaximum
        (sourceDetectorFamily S hS.prime eta u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ tau) < 51 / 100 + 2 * e) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,
      ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ tau ∧
          |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ tau) ∧
        |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ tau) →
      ‖cubeArithmeticSum S hS hmax eta rows T
        (floorPoolOutsideTotal M H S N c b Y) W Y (51 / 100) e t‖ ≤
        C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (v * (67 / 100 + 12 * e + eps * (N + 8)) + loss +
            totalE * (-(3 / 20) + mesh)) := by
  obtain ⟨C, hC, hbound⟩ := actual_fixed_cube_prime_bound M H hH
    N n e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin htau hepsilon hkappa hcost
    hmesh hdelta hbudget hgap hmargin hheight hloss S hS hfirst hmax
    ell hell hello hellhi W hWs hW hWB
  let alpha : ℝ := 1 / 100 + 12 * e + eps * (N + 8)
  let AA := ProbeSelectedPrimeSums.annularPower 1 2 (alpha - 17 / 50)
  have hAA : 0 ≤ AA :=
    ProbeSelectedPrimeSums.annularPower_nonneg 1 2 _ (by norm_num)
  refine ⟨256 * C * (AA + 1), by positivity, ?_⟩
  intro eta
  filter_upwards [hbound eta, eventually_ge_atTop (1 : ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hd0 : 0 < d := hdmin.trans_le hd
  let Y : Fin N → ℝ := fun j => Z ^ (ell j)
  let T : Fin N → Finset PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
  let F : FreeRow → ℝ := fun u =>
    ‖∑P : (∀j, T j), calibratedTupleValue S hS hmax eta u
      (fun j => (P j).val)
      (fun j => floorPoolOutsideTotal M H S N c b Y j _ (P j).property)
      W Y (((51 / 100 + 16 * e : ℝ) : ℂ) + t.1.1 * Complex.I)
      (((1 - 51 / 100 - 6 * e : ℝ) : ℂ) + t.2 * Complex.I) z‖
  let D : ℝ := C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) * Z ^ loss *
    Z ^ (totalE * (-(3 / 20) + mesh))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hF (u : FreeRow) (hu : u ∈ rows) : F u ≤ D * rowNorm u ^ alpha := by
    rcases hrows u hu with ⟨hu1, hulo, hcal, huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi (51 / 100) i hi le_rfl
      (by norm_num) (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N → ℝ := fun j => HeckePrimeAmplitudeBins.amplitude
      (Y j) ((51 / 100 : ℝ) - 1 / 2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hellpos (j : Fin N) : 0 ≤ ell j :=
      (mul_nonneg hdmax hrmin.le).trans (hello j)
    have hq := weightedMean_bounds Finset.univ (fun j => ell j / d) g (1 / 50)
      (fun j _ => div_nonneg (hellpos j) hd0.le)
      (by
        rw [source_slot_length_sum_total Finset.univ ell d totalE hellsum]
        exact div_pos totalE_pos hd0)
      (fun j _ => ⟨(hh.1 j).1, by
        have hhj := (hh.1 j).2.1
        dsimp [g, Y, z]
        norm_num at hhj ⊢
        exact hhj⟩)
    have hp : (∏j, (Y j) ^ (-(4 / 25 : ℝ) + g j + mesh)) ≤
        Z ^ (totalE * (-(3 / 20) + mesh)) := by
      rw [show (∏j, (Y j) ^ (-(4 / 25 : ℝ) + g j + mesh)) =
        Z ^ (totalE * (-(4 / 25 : ℝ) +
          weightedMean Finset.univ (fun j => ell j / d) g + mesh)) from
        source_slot_product_total Finset.univ ell g Z d totalE mesh
          hZp hd0.ne' totalE_ne hellsum]
      apply Real.rpow_le_rpow_of_exponent_le hZ
      have hmul := mul_le_mul_of_nonneg_left hq.2 totalE_pos.le
      nlinarith
    have hN : 0 ≤ rowNorm u := (rowNorm_ge_one u).trans' (by norm_num)
    have h := hh.2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    convert h using 1 <;> dsimp [F, D, alpha, Y, z, g] <;> norm_num <;> ring
  have hh := dyadic_weighted_rows alpha (17 / 50) D (Z ^ v) hD
    (Real.one_le_rpow hZ hv) rows hnorm F hF z (by simp [z])
  have hsum :
      ‖cubeArithmeticSum S hS hmax eta rows T
        (floorPoolOutsideTotal M H S N c b Y) W Y (51 / 100) e t‖ ≤
      ∑u∈rows, ‖frequencyWeight z ⟨u.val, u.property.1⟩‖ * F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by
      apply Finset.sum_congr rfl
      intro u hu
      rw [norm_mul])
  apply (hsum.trans hh).trans
  have hpow : Z ^ loss * Z ^ (totalE * (-(3 / 20) + mesh)) *
      (Z ^ v) ^ (1 + alpha - 17 / 50) =
      Z ^ (v * (67 / 100 + 12 * e + eps * (N + 8)) + loss +
        totalE * (-(3 / 20) + mesh)) := by
    rw [← Real.rpow_mul hZp.le, ← Real.rpow_add hZp, ← Real.rpow_add hZp]
    congr 1
    dsimp [alpha]
    ring
  calc
    _ ≤ 256 * D * (AA + 1) * (Z ^ v) ^ (1 + alpha - 17 / 50) := by
      change 256 * D * AA * _ ≤ _
      gcongr
      linarith
    _ = _ := by
      dsimp [D]
      calc
        _ = (256 * C * (AA + 1)) * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
            (Z ^ loss * Z ^ (totalE * (-(3 / 20) + mesh)) *
              (Z ^ v) ^ (1 + alpha - 17 / 50)) := by ring
        _ = _ := by rw [hpow]

/-! ## Global floor rows and the shifted physical scale -/

theorem actual_global_floor_cube_arithmetic_totalE
    (N n : ℕ) (e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (hkappa : 0 < kappa) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hdelta : 0 < delta) (hbudget : 8 * e * R + kappa ≤ epsilon)
    (hgap : epsilon < rmin * mesh) (hmargin : 0 < margin)
    (hheight : 2 * tau < dmin * cost) (hloss : tau * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (4 * e) S) (hmax : ∀P∈S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀j, dmax * rmin ≤ ell j) (hellhi : ∀j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℂ)
    (hWs : ∀j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀j, ContDiff ℝ ∞ (W j)) (hWB : ∀j t, ‖W j t‖ ≤ A)
    (hellsum : ∑j, ell j = totalE) :
    ∃C : ℝ, 0 < C ∧ ∀eta : Character, ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ, dmin ≤ d → d ≤ dmax → ∀v : ℝ, 0 ≤ v →
      ∀rows : Finset FreeRow,
      (∀u∈rows, u.val ≠ 1 ∧ Z ^ delta ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (d - margin)) →
      (∀u∈rows, rowNorm u ≤ Z ^ v) →
      ∀i : ℕ, i ≤ n →
      (∀u∈rows, detectorMaximum
        (sourceDetectorFamily S hS.prime eta u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ tau) < 51 / 100 + 2 * e) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,
      ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ tau ∧
          |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ tau) ∧
        |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ tau) →
      ‖cubeArithmeticSum S hS hmax eta rows T
        (floorPoolOutsideTotal M H S N c b Y) W Y (51 / 100) e t‖ ≤
        C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (v * (67 / 100 + 12 * e + eps * (N + 8)) + loss +
            totalE * (-(3 / 20) + mesh)) := by
  obtain ⟨C, hC, hbound⟩ := actual_floor_cube_arithmetic_totalE M H hH
    N n e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin htau hepsilon hkappa
    hcost hmesh hdelta hbudget hgap hmargin hheight hloss S hS hfirst hmax
    ell hell hello hellhi W hWs hW hWB hellsum
  let theta : ℝ := 67 / 100 + 12 * e + eps * (N + 8)
  have htheta : 0 < theta := by dsimp [theta]; positivity
  obtain ⟨Cg, hCg, hgeom⟩ := bounded_dyadic_power_sum theta htheta
  refine ⟨C * Cg, mul_pos hC hCg, ?_⟩
  intro eta
  filter_upwards [hbound eta, eventually_gt_atTop (1 : ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0 < Z := zero_lt_one.trans hZ
  let Y : Fin N → ℝ := fun j => Z ^ (ell j)
  let T : Fin N → Finset PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass M H) S c b (Y j)
  let Rn : ℕ → Finset FreeRow := fun k => rows ∩ dyadicRows 1 k
  let term : FreeRow → ℂ := fun u =>
    frequencyWeight ((17 / 50 : ℂ) + t.1.2 * Complex.I) ⟨u.val, u.property.1⟩ *
      ∑P : (∀j, T j), calibratedTupleValue S hS hmax eta u
        (fun j => (P j).val)
        (fun j => floorPoolOutsideTotal M H S N c b Y j _ (P j).property)
        W Y (((51 / 100 + 16 * e : ℝ) : ℂ) + t.1.1 * Complex.I)
        (((1 - 51 / 100 - 6 * e : ℝ) : ℂ) + t.2 * Complex.I)
        ((17 / 50 : ℂ) + t.1.2 * Complex.I)
  let D : ℝ := C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
    Z ^ (loss + totalE * (-(3 / 20) + mesh))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hdyad (k : ℕ) : ‖∑u∈Rn k, term u‖ ≤ D * ((2 : ℝ) ^ k) ^ theta := by
    let vk := Real.logb Z ((2 : ℝ) ^ k)
    have hvk : 0 ≤ vk := Real.logb_nonneg hZ (one_le_pow₀ (by norm_num))
    have heq : Z ^ vk = (2 : ℝ) ^ k := Real.rpow_logb hZp hZ.ne' (by positivity)
    have hsub : Rn k ⊆ rows := Finset.inter_subset_left
    have hn : ∀u∈Rn k, Z ^ vk ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z ^ vk := by
      intro u hu
      have h := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
      simpa only [heq, one_mul] using And.intro h.1 h.2.le
    have hh := hb d hd hd' vk hvk (Rn k) (fun u hu => hrows u (hsub hu)) hn
      i hi (fun u hu => hbin u (hsub hu)) t ht
    change ‖∑u∈Rn k, term u‖ ≤ _ at hh
    apply hh.trans_eq
    have hp : Z ^ (vk * theta + loss + totalE * (-(3 / 20) + mesh)) =
        Z ^ (loss + totalE * (-(3 / 20) + mesh)) * ((2 : ℝ) ^ k) ^ theta := by
      rw [show vk * theta + loss + totalE * (-(3 / 20) + mesh) =
        (loss + totalE * (-(3 / 20) + mesh)) + vk * theta by ring,
        Real.rpow_add hZp, Real.rpow_mul hZp.le, heq]
    change C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
      Z ^ (vk * theta + loss + totalE * (-(3 / 20) + mesh)) = _
    rw [hp]
    dsimp [D]
    ring
  have hpart := retained_dyadic_sum rows (Z ^ v)
    (fun u hu => ⟨(hrows u hu).1, hnorm u hu⟩) term
  change ‖∑u∈rows, term u‖ ≤ _
  rw [hpart]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z ^ v), ‖∑u∈Rn k, term u‖ := norm_sum_le _ _
    _ ≤ ∑k∈smallDyadicIndices (Z ^ v), D * ((2 : ℝ) ^ k) ^ theta :=
      Finset.sum_le_sum (fun k _ => hdyad k)
    _ = D * ∑k∈smallDyadicIndices (Z ^ v), ((2 : ℝ) ^ k) ^ theta :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ D * (Cg * (Z ^ v) ^ theta) := mul_le_mul_of_nonneg_left
      (hgeom (Z ^ v) (by positivity) (smallDyadicIndices (Z ^ v))
        (fun k hk => mem_smallDyadicIndices.mp hk)) hD
    _ = _ := by
      have hp : Z ^ (loss + totalE * (-(3 / 20) + mesh)) *
          (Z ^ v) ^ theta =
          Z ^ (v * theta + loss + totalE * (-(3 / 20) + mesh)) := by
        rw [← Real.rpow_mul hZp.le, ← Real.rpow_add hZp]
        congr 1
        ring
      dsimp [D]
      calc
        _ = (C * Cg) * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
          (Z ^ (loss + totalE * (-(3 / 20) + mesh)) *
            (Z ^ v) ^ theta) := by ring
        _ = _ := by rw [hp]

/-!
The physical profile lemma accepts arbitrary positive `X,Y`.  Substituting the
new powers and using the perturbed exponent identity gives the exact shifted
floor exponent.
-/

theorem actual_global_floor_cube_norm_perturbed
    (N n : ℕ) (e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (hkappa : 0 < kappa) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hdelta : 0 < delta) (hbudget : 8 * e * R + kappa ≤ epsilon)
    (hgap : epsilon < rmin * mesh) (hmargin : 0 < margin)
    (hheight : 2 * tau < dmin * cost) (hloss : tau * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (4 * e) S) (hmax : ∀P∈S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀j, dmax * rmin ≤ ell j) (hellhi : ∀j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℂ)
    (hWs : ∀j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀j, ContDiff ℝ ∞ (W j)) (hWB : ∀j t, ‖W j t‖ ≤ A)
    (hellsum : ∑j, ell j = totalE)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) :
    ∃C : ℝ, 0 < C ∧ ∀eta : Character, ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ, dmin ≤ d → d ≤ dmax → ∀v : ℝ, 0 ≤ v →
      ∀rows : Finset FreeRow,
      (∀u∈rows, u.val ≠ 1 ∧ Z ^ delta ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (d - margin)) →
      (∀u∈rows, rowNorm u ≤ Z ^ v) →
      ∀i : ℕ, i ≤ n →
      (∀u∈rows, detectorMaximum
        (sourceDetectorFamily S hS.prime eta u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ tau) < 51 / 100 + 2 * e) →
      let Yp : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Yp j)
      ‖finiteCentralCubeRows S hS hmax eta rows T
        (floorPoolOutsideTotal M H S N c b Yp) W Yp W0 W1
        (Z ^ sourceLx) (Z ^ sourceLy) Z e (fun _ => 51 / 100)
        (fun _ => (3 * i + 1 : ℕ) * Z ^ tau)‖ ≤
        C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (3 / 16 + sourceExponentTau rho0 (51 / 100) v 1 (1 / 100) +
            realLossTau rho0 N v e eps loss mesh) := by
  obtain ⟨Ca, hCa, hbound⟩ := actual_global_floor_cube_arithmetic_totalE M H hH
    N n e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin htau hepsilon hkappa
    hcost hmesh hdelta hbudget hgap hmargin hheight hloss S hS hfirst hmax
    ell hell hello hellhi W hWs hW hWB hellsum
  obtain ⟨Cp, hCp, hprofile⟩ := actual_common_cube_aggregate_norm
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cp * Ca, mul_pos hCp hCa, ?_⟩
  intro eta
  filter_upwards [hbound eta, source_cube_height_eventually tau htau] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  have hZp : 0 < Z := zero_lt_one.trans_le hZ.1
  let Yp : Fin N → ℝ := fun j => Z ^ (ell j)
  let T : Fin N → Finset PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass M H) S c b (Yp j)
  have hheight : (3 * i + 1 : ℕ) * Z ^ tau ≤ (3 * i + 2 : ℕ) * Z ^ tau := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
    exact_mod_cast (show 3 * i + 1 ≤ 3 * i + 2 by omega)
  let mass : ℝ := Ca * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
    Z ^ (v * (67 / 100 + 12 * e + eps * (N + 8)) + loss +
      totalE * (-(3 / 20) + mesh))
  have hp := hprofile e (51 / 100) (Z ^ tau) ((3 * i + 1 : ℕ) * Z ^ tau) i
    he he1 le_rfl (by norm_num) hZ.2 hheight S hS hmax hfirst eta rows
    (fun u hu => (hrows u hu).1) T (floorPoolOutsideTotal M H S N c b Yp)
    (rayCubeFamily M H hH) hbin W Yp (Z ^ sourceLx) (Z ^ sourceLy) Z
    (by positivity) (by positivity) hZp mass (by dsimp [mass]; positivity)
    (hb d hd hd' v hv rows hrows hnorm i hi hbin)
  apply hp.trans_eq
  change Cp * ((Z ^ lxTau rho0) ^ (4 / 25) *
    Z ^ (51 / 100 + 16 * e - 33 / 50) *
    (Z ^ lyTau rho0) ^ (-(51 / 100) - 6 * e)) * mass = _
  rw [shifted_physical_scale_identity Z rho0 (51 / 100) e hZp]
  have hexp :
      scaleExponentTau rho0 (51 / 100) e +
        (v * (67 / 100 + 12 * e + eps * (N + 8)) + loss +
          totalE * (-(3 / 20) + mesh)) =
      3 / 16 + sourceExponentTau rho0 (51 / 100) v 1 (1 / 100) +
        realLossTau rho0 N v e eps loss mesh := by
    unfold scaleExponentTau sourceExponentTau realLossTau
      lxTau lyTau ellTau totalE rho0 heightTau
    ring
  dsimp [mass]
  calc
    _ = (Cp * Ca) * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
      (Z ^ (scaleExponentTau rho0 (51 / 100) e) *
        Z ^ (v * (67 / 100 + 12 * e + eps * (N + 8)) + loss +
          totalE * (-(3 / 20) + mesh))) := by ring
    _ = _ := by rw [← Real.rpow_add hZp, hexp]

/-! ## Normalization and the relative floor saving -/

theorem actual_normalized_floor_cube_perturbed
    (N n : ℕ) (e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (hkappa : 0 < kappa) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hdelta : 0 < delta) (hbudget : 8 * e * R + kappa ≤ epsilon)
    (hgap : epsilon < rmin * mesh) (hmargin : 0 < margin)
    (hheight : 2 * tau < dmin * cost) (hloss : tau * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (4 * e) S) (hmax : ∀P∈S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀j, dmax * rmin ≤ ell j) (hellhi : ∀j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℝ)
    (hWs : ∀j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀j, ContDiff ℝ ∞ (W j))
    (hWB : ∀j t, 0 ≤ W j t ∧ W j t ≤ A)
    (hcompact : ∀j, HasCompactSupport (W j)) (hne : ∀j, W j ≠ 0)
    (hellsum : ∑j, ell j = totalE)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (hr0 : ∀y, (W0 y).im = 0) (hr1 : ∀y, (W1 y).im = 0)
    (hp0 : ∀y, 0 ≤ (W0 y).re) (hp1 : ∀y, 0 ≤ (W1 y).re)
    (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0) (nu : ℝ) (hnu : 0 < nu) :
    letI : NeZero (∏P∈S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ, 0 < C ∧ ∀eta : Character, ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ, dmin ≤ d → d ≤ dmax → ∀v : ℝ, 0 ≤ v →
      ∀rows : Finset FreeRow,
      (∀u∈rows, u.val ≠ 1 ∧ Z ^ delta ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (d - margin)) →
      (∀u∈rows, rowNorm u ≤ Z ^ v) →
      ∀i : ℕ, i ≤ n →
      (∀u∈rows, detectorMaximum
        (sourceDetectorFamily S hS.prime eta u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ tau) < 51 / 100 + 2 * e) →
      let Yp : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := sourceResidueConstant W0 W1 (∏P∈S, P) *
        (Probe.principalScalar Finset.univ Z totalE
          (slotMass T (residueWeights W Yp)) : ℂ)
      normer ≠ 0 ∧
      ‖finiteCentralCubeRows S hS hmax eta rows T
        (floorPoolOutsideTotal M H S N c b Yp) (fun j y => (W j y : ℂ)) Yp
        W0 W1 (Z ^ sourceLx) (Z ^ sourceLy) Z e (fun _ => 51 / 100)
        (fun _ => (3 * i + 1 : ℕ) * Z ^ tau) / normer‖ ≤
        C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (3 / 16 + sourceExponentTau rho0 (51 / 100) v 1 (1 / 100) +
            realLossTau rho0 N v e eps loss mesh + nu) := by
  let : NeZero (∏P∈S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N → ℝ → ℂ := fun j y => (W j y : ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) :=
    Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j) ⊆ Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC]; rw [hh]; simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖ ≤ A := by
    simpa only [WC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨Cg, hCg, hbound⟩ := actual_global_floor_cube_norm_perturbed M H hH
    N n e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin htau hepsilon hkappa
    hcost hmesh hdelta hbudget hgap hmargin hheight hloss S hS hfirst hmax
    ell hell hello hellhi WC hWCs hWC hWCB hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hellpos (j : Fin N) : 0 < ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn, hCn, hnormer⟩ := actual_ray_normalizer_inverse_totalE M H hH
    S hS c b hc hcb ell hellpos hellsum W hW hcompact hWs
    (fun j y => (hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨Cg * Cn, mul_pos hCg hCn, ?_⟩
  intro eta
  filter_upwards [hbound eta, hnormer, eventually_gt_atTop (0 : ℝ)] with Z hb hn hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only at hn ⊢
  refine ⟨hn.1, ?_⟩
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  rw [div_eq_mul_inv, norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ
    (3 / 16 + sourceExponentTau rho0 (51 / 100) v 1 (1 / 100) +
      realLossTau rho0 N v e eps loss mesh) nu]
  ring

/-- Floor saving at the actual boundary and actual total slot mass. -/
theorem actual_floor_cube_saving_perturbed
    (N n : ℕ) (e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (hkappa : 0 < kappa) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hdelta : 0 < delta) (hbudget : 8 * e * R + kappa ≤ epsilon)
    (hgap : epsilon < rmin * mesh) (hmargin : 0 < margin)
    (hheight : 2 * tau < dmin * cost) (hloss : tau * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (4 * e) S) (hmax : ∀P∈S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀j, dmax * rmin ≤ ell j) (hellhi : ∀j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℝ)
    (hWs : ∀j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀j, ContDiff ℝ ∞ (W j))
    (hWB : ∀j t, 0 ≤ W j t ∧ W j t ≤ A)
    (hcompact : ∀j, HasCompactSupport (W j)) (hne : ∀j, W j ≠ 0)
    (hellsum : ∑j, ell j = totalE)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (hr0 : ∀y, (W0 y).im = 0) (hr1 : ∀y, (W1 y).im = 0)
    (hp0 : ∀y, 0 ≤ (W0 y).re) (hp1 : ∀y, 0 ≤ (W1 y).re)
    (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0)
    (nu : ℝ) (hnu : 0 < nu) (zeta saving : ℝ)
    (hzeta : 0 ≤ zeta) (hzetahi : zeta ≤ 3 / 16)
    (hheightOne : physicalHeight + zeta ≤ 1) (hsaving : 0 < saving)
    (hbeta : boundary < HeckeZeroSupremum.beta)
    (htotal : 2 * zeta + 26 * e + (N + 8) * eps + loss +
      totalE * mesh + nu + saving + 32 * rho0 / 25 ≤ 7 / 1200) :
    letI : NeZero (∏P∈S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ, 0 < C ∧ ∀eta : Character, ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ, dmin ≤ d → d ≤ dmax → ∀v : ℝ, 0 ≤ v →
      v ≤ physicalHeight + zeta → ∀rows : Finset FreeRow,
      (∀u∈rows, u.val ≠ 1 ∧ Z ^ delta ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (d - margin)) →
      (∀u∈rows, rowNorm u ≤ Z ^ v) →
      ∀i : ℕ, i ≤ n →
      (∀u∈rows, detectorMaximum
        (sourceDetectorFamily S hS.prime eta u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ tau) < 51 / 100 + 2 * e) →
      let Yp : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := sourceResidueConstant W0 W1 (∏P∈S, P) *
        (Probe.principalScalar Finset.univ Z totalE
          (slotMass T (residueWeights W Yp)) : ℂ)
      normer ≠ 0 ∧
      ‖finiteCentralCubeRows S hS hmax eta rows T
        (floorPoolOutsideTotal M H S N c b Yp) (fun j y => (W j y : ℂ)) Yp
        W0 W1 (Z ^ sourceLx) (Z ^ sourceLy) Z e (fun _ => 51 / 100)
        (fun _ => (3 * i + 1 : ℕ) * Z ^ tau) / normer‖ ≤
        C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (HeckeZeroSupremum.beta - 11 / 16 - saving) := by
  let : NeZero (∏P∈S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C, hC, hbound⟩ := actual_normalized_floor_cube_perturbed M H hH
    N n e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin htau hepsilon hkappa
    hcost hmesh hdelta hbudget hgap hmargin hheight hloss S hS hfirst hmax
    ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨C, hC, ?_⟩
  intro eta
  filter_upwards [hbound eta, eventually_ge_atTop (1 : ℝ)] with Z hb hZ
  intro d hd hd' v hv hvhi rows hrows hnorm i hi hbin
  dsimp only
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hm := floor_source_margin_with_two_zeta (1 / 100)
    HeckeZeroSupremum.beta zeta v le_rfl hbeta.le hzeta hvhi
  have hl := realLossTau_bound_fixed N v e eps loss mesh
    (by linarith [hvhi, hheightOne]) he.le heps.le hmesh.le
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ ?_) (by positivity)
  nlinarith

/-- Collected floor rows with row-dependent detector index. -/
theorem actual_floor_rows_saving_perturbed
    (N n : ℕ) (e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (hkappa : 0 < kappa) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hdelta : 0 < delta) (hbudget : 8 * e * R + kappa ≤ epsilon)
    (hgap : epsilon < rmin * mesh) (hmargin : 0 < margin)
    (hheight : 2 * tau < dmin * cost) (hloss : tau * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (4 * e) S) (hmax : ∀P∈S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀j, dmax * rmin ≤ ell j) (hellhi : ∀j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℝ)
    (hWs : ∀j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀j, ContDiff ℝ ∞ (W j))
    (hWB : ∀j t, 0 ≤ W j t ∧ W j t ≤ A)
    (hcompact : ∀j, HasCompactSupport (W j)) (hne : ∀j, W j ≠ 0)
    (hellsum : ∑j, ell j = totalE)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (hr0 : ∀y, (W0 y).im = 0) (hr1 : ∀y, (W1 y).im = 0)
    (hp0 : ∀y, 0 ≤ (W0 y).re) (hp1 : ∀y, 0 ≤ (W1 y).re)
    (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0)
    (nu : ℝ) (hnu : 0 < nu) (zeta saving : ℝ)
    (hzeta : 0 ≤ zeta) (hzetahi : zeta ≤ 3 / 16)
    (hheightOne : physicalHeight + zeta ≤ 1) (hsaving : 0 < saving)
    (hbeta : boundary < HeckeZeroSupremum.beta)
    (htotal : 2 * zeta + 26 * e + (N + 8) * eps + loss +
      totalE * mesh + nu + saving + 32 * rho0 / 25 ≤ 7 / 1200) :
    letI : NeZero (∏P∈S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ, 0 < C ∧ ∀eta : Character, ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ, dmin ≤ d → d ≤ dmax → ∀v : ℝ, 0 ≤ v →
      v ≤ physicalHeight + zeta → ∀rows : Finset FreeRow,
      (∀u∈rows, u.val ≠ 1 ∧ Z ^ delta ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (d - margin)) →
      (∀u∈rows, rowNorm u ≤ Z ^ v) →
      ∀idx : FreeRow → ℕ, (∀u∈rows, idx u ≤ n) →
      (∀u∈rows, detectorMaximum
        (sourceDetectorFamily S hS.prime eta u (rayCubeFamily M H hH u))
        (3 * (idx u + 1 : ℕ) * Z ^ tau) < 51 / 100 + 2 * e) →
      let Yp : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := sourceResidueConstant W0 W1 (∏P∈S, P) *
        (Probe.principalScalar Finset.univ Z totalE
          (slotMass T (residueWeights W Yp)) : ℂ)
      normer ≠ 0 ∧
      ‖finiteCentralCubeRows S hS hmax eta rows T
        (floorPoolOutsideTotal M H S N c b Yp) (fun j y => (W j y : ℂ)) Yp
        W0 W1 (Z ^ sourceLx) (Z ^ sourceLy) Z e (fun _ => 51 / 100)
        (fun u => (3 * idx u + 1 : ℕ) * Z ^ tau) / normer‖ ≤
        C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (HeckeZeroSupremum.beta - 11 / 16 - saving) := by
  let : NeZero (∏P∈S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C, hC, hbound⟩ := actual_floor_cube_saving_perturbed M H hH
    N n e eps c b A R dmin dmax rmin tau epsilon kappa cost mesh delta margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin htau hepsilon hkappa
    hcost hmesh hdelta hbudget hgap hmargin hheight hloss S hS hfirst hmax
    ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    nu hnu zeta saving hzeta hzetahi hheightOne hsaving hbeta htotal
  refine ⟨(n + 1 : ℕ) * C, by positivity, ?_⟩
  intro eta
  filter_upwards [hbound eta] with Z hb
  intro d hd hd' v hv hvhi rows hrows hnorm idx hidx hbin
  dsimp only
  let Yp : Fin N → ℝ := fun j => Z ^ (ell j)
  let T : Fin N → Finset PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass M H) S c b (Yp j)
  let hT := floorPoolOutsideTotal M H S N c b Yp
  let WC : Fin N → ℝ → ℂ := fun j y => (W j y : ℂ)
  let normer := sourceResidueConstant W0 W1 (∏P∈S, P) *
    (Probe.principalScalar Finset.univ Z totalE (slotMass T (residueWeights W Yp)) : ℂ)
  let Ri : ℕ → Finset FreeRow := fun i => rows.filter (fun u => idx u = i)
  have hnormer := (hb d hd hd' v hv hvhi ∅ (by simp) (by simp)
    0 (Nat.zero_le n) (by simp)).1
  refine ⟨hnormer, ?_⟩
  have hpart := finiteCentralCubeRows_bin_partition S hS hmax eta rows T hT WC Yp
    W0 W1 (Z ^ sourceLx) (Z ^ sourceLy) Z e (Z ^ tau) idx (fun _ => 0)
    n 0 (fun u hu => ⟨hidx u hu, le_rfl⟩)
  have heq : finiteCentralCubeRows S hS hmax eta rows T hT WC Yp W0 W1
      (Z ^ sourceLx) (Z ^ sourceLy) Z e (fun _ => 51 / 100)
      (fun u => (3 * idx u + 1 : ℕ) * Z ^ tau) =
      ∑i∈Finset.range (n + 1), finiteCentralCubeRows S hS hmax eta (Ri i) T hT
        WC Yp W0 W1 (Z ^ sourceLx) (Z ^ sourceLy) Z e
        (fun _ => 51 / 100) (fun _ => (3 * i + 1 : ℕ) * Z ^ tau) := by
    simpa [cubeBinRows, Ri] using hpart
  change ‖finiteCentralCubeRows S hS hmax eta rows T hT WC Yp W0 W1
    (Z ^ sourceLx) (Z ^ sourceLy) Z e (fun _ => 51 / 100)
    (fun u => (3 * idx u + 1 : ℕ) * Z ^ tau) / normer‖ ≤ _
  rw [heq, Finset.sum_div]
  apply (norm_sum_le _ _).trans
  have hboundi (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ‖finiteCentralCubeRows S hS hmax eta (Ri i) T hT WC Yp W0 W1
        (Z ^ sourceLx) (Z ^ sourceLy) Z e (fun _ => 51 / 100)
        (fun _ => (3 * i + 1 : ℕ) * Z ^ tau) / normer‖ ≤
      C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
        Z ^ (HeckeZeroSupremum.beta - 11 / 16 - saving) := by
    have hsub : Ri i ⊆ rows := Finset.filter_subset _ _
    have hbi : ∀u∈Ri i, detectorMaximum
        (sourceDetectorFamily S hS.prime eta u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ tau) < 51 / 100 + 2 * e := by
      intro u hu
      have hh := hbin u (hsub hu)
      rwa [(Finset.mem_filter.mp hu).2] at hh
    exact (hb d hd hd' v hv hvhi (Ri i) (fun u hu => hrows u (hsub hu))
      (fun u hu => hnorm u (hsub hu)) i
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hbi).2
  calc
    _ ≤ ∑i∈Finset.range (n + 1),
        C * (eta.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (HeckeZeroSupremum.beta - 11 / 16 - saving) :=
      Finset.sum_le_sum hboundi
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-! ## Same-f630 specialization -/

def SameDataFloorRows
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (theta : ℝ) (n : ℕ) : Prop :=
  letI : NeZero (∏P∈F.S, P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  ∃C : ℝ, 0 < C ∧ ∀eta : Character, ∀ᶠZ : ℝ in atTop,
    ∀rows : Finset FreeRow,
    (∀u∈rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z ^ (physicalHeight + D.t)) →
    ∀idx : FreeRow → ℕ, (∀u∈rows, idx u ≤ n) →
    (∀u∈rows, detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime eta u
        (rayCubeFamily F.modulus ⊤ le_top u))
      (3 * (idx u + 1 : ℕ) * Z ^ theta) < 51 / 100 + 2 * D.e) →
    let Y : Fin D.N → ℝ := fun j => Z ^ (D.ell j)
    let T : Fin D.N → Finset PrimeIdeal := fun j =>
      pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
    let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
      (Probe.principalScalar Finset.univ Z totalE
        (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
    normer ≠ 0 ∧
    ‖finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T
      (floorPoolOutsideTotal F.modulus ⊤ F.S D.N 1 2 Y)
      (fun _ y => (F.w y : ℂ)) Y F.W F.W
      (Z ^ sourceLx) (Z ^ sourceLy) Z D.e (fun _ => 51 / 100)
      (fun u => (3 * idx u + 1 : ℕ) * Z ^ theta) / normer‖ ≤
      C * (eta.modulus.absNorm : ℝ) ^ (2 * D.eps) *
        Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma)

/-- The complete actual floor consumer from the same f630 datum. -/
theorem same_data_floor_rows
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hbeta : boundary < HeckeZeroSupremum.beta)
    {theta : ℝ} (htheta : 0 < theta)
    (hthetad : theta < (1 / 200 : ℝ) / 2)
    (hthetacost : 4 * theta < (1 / 200 : ℝ) * D.cost)
    (hthetaeps : theta * (2 + 4 * D.eps) < D.t)
    (n : ℕ) : SameDataFloorRows D hfine F theta n := by
  have hreserve := same_D_floor_rho_reserve D
  have hraw := actual_floor_rows_saving_perturbed F.modulus ⊤ le_top
    D.N n D.e D.eps 1 2 1 D.t (1 / 200) (7 / 8) D.rmin theta
    D.ε D.κ D.cost D.t (1 / 100) D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    D.t_pos.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos htheta D.epsilon_pos
    D.kappa_pos D.cost_pos.le D.t_pos (by norm_num)
    (SevenEighths.PerturbedSameDataCentral.same_D_phase_budget D)
    D.epsilon_gap D.t_pos
    (by linarith [hthetacost]) hthetaeps F.S F.exclusions F.first F.maximal
    D.ell D.slots_injective
    (SevenEighths.PerturbedSameDataCentral.same_D_slot_lower D)
    (SevenEighths.PerturbedSameDataCentral.same_D_slot_upper D)
    (fun _ => F.w) (fun _ => F.support) (fun _ => F.smooth)
    (fun _ y => F.bounded y) (fun _ => F.compact) (fun _ => F.nonzero)
    (SevenEighths.PerturbedSameDataCentral.same_D_totalE D)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero (D.t / 8)
      (div_pos D.t_pos (by norm_num))
    D.t D.sigma D.t_pos.le (by linarith [D.t_small])
    (by have hc := SevenEighths.PerturbedSameDataCentral.same_D_conductor D; linarith [D.t_pos])
    D.sigma_pos hbeta hreserve
  unfold SameDataFloorRows
  obtain ⟨C, hC, hbound⟩ := hraw
  refine ⟨C, hC, ?_⟩
  intro eta
  filter_upwards [hbound eta, eventually_ge_atTop (1 : ℝ)] with Z hb hZ
  intro rows hrows idx hidx hbin
  have hcap : physicalHeight + D.t ≤ (7 / 8 : ℝ) - D.t := by
    have hc := SevenEighths.PerturbedSameDataCentral.same_D_conductor D
    linarith [D.t_pos]
  have hrows' : ∀u∈rows,
      u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z ^ ((7 / 8 : ℝ) - D.t) := by
    intro u hu
    refine ⟨(hrows u hu).1, (hrows u hu).2.1, (hrows u hu).2.2.1, ?_⟩
    exact (hrows u hu).2.2.2.trans
      (Real.rpow_le_rpow_of_exponent_le hZ hcap)
  have hnorm : ∀u∈rows, rowNorm u ≤ Z ^ (physicalHeight + D.t) :=
    fun u hu => (hrows u hu).2.2.2
  exact hb (7 / 8) (by norm_num) le_rfl (physicalHeight + D.t)
    (add_nonneg height_nonneg D.t_pos.le) le_rfl rows hrows' hnorm idx hidx hbin

end SevenEighths.PerturbedFloorRows

end

end OAI
