import Submissions.argonaut_20261008.PerturbedCentralSlots
import Submissions.argonaut_20261008.PerturbedCountBridge
import Submissions.argonaut_20261008.PerturbedCentralExponent
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCollected
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set

namespace SevenEighths.PerturbedCentral

open SevenEighths.ProbeHighRowFamily
open SevenEighths.PerturbedCountBridge
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition HeckeDetectorBatch HeckeDetectorAdaptiveCutoff
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-! ## Central physical arithmetic with total slot mass E -/

theorem actual_class_cube_arithmetic_totalE
    (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss E : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hτ : 0 < τ) (hε : 0 < ε) (hκ : 0 < κ)
    (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hδ : 0 < δ)
    (hbudget : 8 * e * R + κ ≤ ε) (hgap : ε < rmin * mesh)
    (hmargin : 0 < margin) (hheight : 2 * τ < dmin * cost)
    (hloss : τ * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4 * e) S)
    (hmax : ∀ P ∈ S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀ j, dmax * rmin ≤ ell j) (hellhi : ∀ j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℂ)
    (hWs : ∀ j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hWB : ∀ j t, ‖W j t‖ ≤ A)
    (hellsum : ∑ j, ell j = E) (hE : 0 < E) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (v a q D Rcount : ℝ), 0 ≤ v → 51 / 100 ≤ a → a ≤ 1 → 0 ≤ D →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ δ ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (d - margin)) →
      (∀ u ∈ rows, Z ^ v ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z ^ v) →
      (rows.card : ℝ) ≤ D * (Z ^ d) ^ Rcount →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows,
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀ t : HeightSpace,
      ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) ∧
        |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) →
      (∀ u ∈ rows,
        weightedMean Finset.univ (fun j => ell j / d)
          (fun j => HeckePrimeAmplitudeBins.amplitude (Y j) (a - 1 / 2) mesh
            (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j)
              ((17 / 50 : ℂ) + t.1.2 * Complex.I))) = q) →
      ‖cubeArithmeticSum S hS hmax η rows T
          (ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y) W Y a e t‖ ≤
        C * D * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (d * Rcount +
            v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss +
            E * (-(4 / 25) + q + mesh)) := by
  obtain ⟨C, hC, hbound⟩ :=
    ProbeHighRowFamily.actual_fixed_cube_prime_bound M H hH N n e eps c b A R
      dmin dmax rmin τ ε κ cost mesh δ margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let AA : ℝ := max 1 ((2 : ℝ) ^ (4 / 25 + 12 * e + eps * (N + 8)))
  have hAA : 0 < AA := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C * AA, mul_pos hC hAA, ?_⟩
  intro η
  filter_upwards [hbound η, eventually_ge_atTop (1 : ℝ)] with Z hb hZ
  intro d hd hd' v a q D Rcount hv ha ha' hD rows hrows hnorm hcard i hi hbin
  dsimp only
  intro t ht hq
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hd0 : 0 < d := hdmin.trans_le hd
  let Y : Fin N → ℝ := fun j => Z ^ (ell j)
  let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
  let α : ℝ := a - 1 / 2 + 12 * e + eps * (N + 8)
  let F : FreeRow → ℝ := fun u =>
    ‖∑ P : (∀ j, T j), calibratedTupleValue S hS hmax η u (fun j => (P j).val)
      (fun j => ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y j _ (P j).property)
      W Y (((a + 16 * e : ℝ) : ℂ) + t.1.1 * Complex.I)
      (((1 - a - 6 * e : ℝ) : ℂ) + t.2 * Complex.I) z‖
  let Amp : ℝ := C * (η.modulus.absNorm : ℝ) ^ (2 * eps) * Z ^ loss *
    Z ^ (E * (-(4 / 25) + q + mesh))
  have hAmp : 0 ≤ Amp := by dsimp [Amp]; positivity
  have hF (u : FreeRow) (hu : u ∈ rows) : F u ≤ Amp * rowNorm u ^ α := by
    rcases hrows u hu with ⟨hu1, hulo, hcal, huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi a i hi ha ha' (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N → ℝ := fun j =>
      HeckePrimeAmplitudeBins.amplitude (Y j) (a - 1 / 2) mesh
        (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hp : (∏ j, (Y j) ^ (-(4 / 25 : ℝ) + g j + mesh)) =
        Z ^ (E * (-(4 / 25 : ℝ) + q + mesh)) := by
      rw [show (∏ j, (Y j) ^ (-(4 / 25 : ℝ) + g j + mesh)) =
        Z ^ (E * (-(4 / 25 : ℝ) +
          weightedMean Finset.univ (fun j => ell j / d) g + mesh)) from
        source_slot_product_total Finset.univ ell g Z d E mesh hZp hd0.ne' hE.ne' hellsum]
      rw [show weightedMean Finset.univ (fun j => ell j / d) g = q from hq u hu]
    have hh' := hh.2
    rw [hp] at hh'
    convert hh' using 1 <;> dsimp [F, Amp, α, Y, z, g] <;> ring
  have hh := ProbeHighRowFamily.dyadic_weighted_rows_card α (17 / 50) Amp
    (Z ^ v) (D * (Z ^ d) ^ Rcount) hAmp (Real.rpow_pos_of_pos hZp _) rows hcard hnorm
    F hF z (by simp [z])
  have hsum :
      ‖cubeArithmeticSum S hS hmax η rows T
        (ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y) W Y a e t‖ ≤
      ∑ u ∈ rows, ‖frequencyWeight z ⟨u.val, u.property.1⟩‖ * F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by
      apply Finset.sum_congr rfl
      intro u hu
      rw [norm_mul])
  have hAp : ProbeSelectedPrimeSums.annularPower 1 2 (α - 17 / 50) ≤ AA :=
    ProbeHighRowFamily.annular_power_uniform _ _ (by dsimp [α]; linarith)
  apply (hsum.trans hh).trans
  have hpow :
      (Z ^ d) ^ Rcount * Z ^ loss * Z ^ (E * (-(4 / 25) + q + mesh)) *
          (Z ^ v) ^ (α - 17 / 50) =
        Z ^ (d * Rcount +
          v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss +
          E * (-(4 / 25) + q + mesh)) := by
    simp_rw [← Real.rpow_mul hZp.le]
    rw [← Real.rpow_add hZp, ← Real.rpow_add hZp, ← Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ (D * (Z ^ d) ^ Rcount) * Amp * AA * (Z ^ v) ^ (α - 17 / 50) := by gcongr
    _ = _ := by
      dsimp [Amp]
      calc
        _ = (C * AA) * D * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
          ((Z ^ d) ^ Rcount * Z ^ loss * Z ^ (E * (-(4 / 25) + q + mesh)) *
            (Z ^ v) ^ (α - 17 / 50)) := by ring
        _ = _ := by rw [hpow]

/-! ## Source moments -> class arithmetic, retaining actual d and v -/

theorem actual_nonfloor_class_totalE_wide
    (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss E : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hτ : 0 < τ) (hε : 0 < ε) (hκ : 0 < κ)
    (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8 * e * R + κ ≤ ε) (hgap : ε < rmin * mesh)
    (hmargin : 0 < margin) (hheight : 2 * τ < dmin * cost)
    (hloss : τ * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4 * e) S)
    (hmax : ∀ P ∈ S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀ j, dmax * rmin ≤ ell j) (hellhi : ∀ j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℂ)
    (hWs : ∀ j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hWB : ∀ j t, ‖W j t‖ ≤ A)
    (hellsum : ∑ j, ell j = E) (hElo : 1 / 6 ≤ E)
    (hdtop : dmax ≤ 37 / 42) (hε1 : ε ≤ 1 / 1000) (hκ1 : κ ≤ 1)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * cost)
    (hwbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * cost ≤ ε / 2)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0 < εm) (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 9 / 40) (hν : 0 < ν)
    (hlog : 0 < logCost) (hMomentHeight : τ < heightCost)
    (counts : WideCountParameters.{0, 0, 0, 0} M H εm) :
    ∃ C : ℝ, 0 < C ∧
    ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (v a C0 : ℝ), 0 ≤ v → 51 / 100 < a → a ≤ 1 → 0 ≤ C0 →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (d - margin)) →
      (∀ u ∈ rows, Z ^ v ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z ^ v) →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows,
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * i : ℕ) * Z ^ τ)) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀ t : HeightSpace,
      ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) ∧
        |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) →
      let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
      ProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i z Δ
        (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
        (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
        (C0 * Z ^ momentCost) (Z ^ heightCost) εm →
      let Q := physical M H (fun u : FreeRow => u.val) W (fun _ => b)
        (fun j => ell j / d) (fun _ => z) (Z ^ d)
      ∀ bin : BinLabel (Finset.univ : Finset (Fin N)) ((2 * a - 1) / 2) mesh,
      let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2)
        mesh hmesh (fun j => ell j / d) Q bin
      let q := classMean Finset.univ ((2 * a - 1) / 2) mesh (fun j => ell j / d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2 * a - 1) / 2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T
        (ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y) W Y a e t‖ ≤
        C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (logCost + heightCost + momentCost +
            d * ProbeHighRowFamily.adaptiveRowExponent (2 * a - 1) q Δ ε εm R ν +
            v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss +
            E * (-(4 / 25) + q + mesh)) := by
  have hdmax0 : 0 < dmax := hdmin.trans_le hdRange
  obtain ⟨K, hK, hcount⟩ := adaptive_source_count_from_raw_moments_wide
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh
    hdmin hdmax0 hτ hlog hMomentHeight hmesh counts
  obtain ⟨C, hC, hphysical⟩ := actual_class_cube_arithmetic_totalE M H hH
    N n e eps c b A R dmin dmax rmin τ ε κ cost mesh (1 / 100) margin loss E
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    (by norm_num) hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi
    W hWs hW hWB hellsum (lt_of_lt_of_le (by norm_num) hElo)
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro η
  have hbatches := actual_source_amplitude_batches_totalE M H hH S hS hmax η
    dmin dmax τ ε e κ cost margin R mesh E n hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hElo hwbudget
  filter_upwards [hphysical η, hcount, hbatches, eventually_gt_atTop (1 : ℝ)]
    with Z hphysical hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hd0 : 0 < d := hdmin.trans_le hd
  let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
  let Q := physical M H (fun u : FreeRow => u.val) W (fun _ => b)
    (fun j => ell j / d) (fun _ => z) (Z ^ d)
  let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2)
    mesh hmesh (fun j => ell j / d) Q bin
  let q := classMean Finset.univ ((2 * a - 1) / 2) mesh (fun j => ell j / d) bin
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows ⊆ rowBand (Z ^ (1 / 100 : ℝ)) (2 * Z ^ v + 1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1, (hrows u hu).2.1, by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0 < ell j := (mul_pos hdmax0 hrmin).trans_le (hello j)
  obtain ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW', hUpper, hExternal,
      hMesh, hBin, hFam, hMean⟩ :=
    hbatch d hd hd' (2 * Z ^ v + 1) rows hrowne hband
      (fun u hu => (hrows u hu).2.2.1) (fun u hu => (hrows u hu).2.2.2)
      a i hi ha ha' hnext hcurrent N ell hellpos hellhi hellsum W (fun _ => b)
      (fun _ => z) bin hne
  have hBsub : B.rows ⊆ rows := hBr ▸ hsub
  have hBfam : ∀ u ∈ B.rows, ∀ j,
      B.family u j = sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a ε Δ ν C0 q i hi ha ha' hε.le hε1 hΔ hΔ1 hν hC0
    B (by rw [hSlots]; simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr, hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z ^ d) (2 * a - 1) mesh hmesh
    (fun j => ell j / d) Q bin (by linarith)
    (fun j _ => div_nonneg (hellpos j).le hd0.le)
    (by rw [source_slot_length_sum_total Finset.univ ell d E hellsum]; positivity) hne
  refine ⟨hqb.1, hqb.2, ?_⟩
  have hp := hphysical d hd hd' v a q (K * C0 * Z ^ (logCost + heightCost + momentCost))
    (ProbeHighRowFamily.adaptiveRowExponent (2 * a - 1) q Δ ε εm R ν)
    hv ha.le ha' (by positivity) rows'
    (fun u hu => hrows u (hsub hu)) (fun u hu => hnorm u (hsub hu)) hcard i hi
    (fun u hu => hnext u (hsub hu)) t ht
    (fun u hu => ProbeHighRowFamily.source_amplitude_class_mean M H ell W Z d b a mesh z
      hZp hd0.ne' hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost + heightCost + momentCost +
      d * ProbeHighRowFamily.adaptiveRowExponent (2 * a - 1) q Δ ε εm R ν +
      v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss +
      E * (-(4 / 25) + q + mesh) =
      (logCost + heightCost + momentCost) +
        (d * ProbeHighRowFamily.adaptiveRowExponent (2 * a - 1) q Δ ε εm R ν +
        v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss +
        E * (-(4 / 25) + q + mesh)) by ring,
      Real.rpow_add hZp (logCost + heightCost + momentCost)]
  ring

/-! ## Arithmetic saving against the actual beta -/

theorem actual_nonfloor_cube_arithmetic_perturbed
    (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hτ : 0 < τ) (hε : 0 < ε) (hκ : 0 < κ)
    (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8 * e * R + κ ≤ ε) (hgap : ε < rmin * mesh)
    (hmargin : 0 < margin) (hheight : 2 * τ < dmin * cost)
    (hloss : τ * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4 * e) S)
    (hmax : ∀ P ∈ S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀ j, dmax * rmin ≤ ell j) (hellhi : ∀ j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℂ)
    (hWs : ∀ j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hWB : ∀ j t, ‖W j t‖ ≤ A)
    (hellsum : ∑ j, ell j = totalE)
    (hdtop : dmax ≤ 37 / 42) (hε1 : ε ≤ 1 / 1000) (hκ1 : κ ≤ 1)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * cost)
    (hwbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * cost ≤ ε / 2)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm ν logCost heightCost momentCost β : ℝ)
    (hεm : 0 < εm) (hν : 0 < ν) (hlog : 0 < logCost)
    (hMomentHeight : τ < heightCost) (hβ0 : boundary < β) (hβ1 : β ≤ 1)
    (ζ μ saving : ℝ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 3 / 16) (hμ : 0 ≤ μ)
    (hcount : 159 * ε + εm + R + 7 * ν ≤ 1 / 32)
    (hfinal : physicalHeight * (159 * ε + εm + R + 7 * ν) + 2 * ζ +
      (3 / 2) * μ + (26 * e + (N + 8) * eps + loss + totalE * mesh) +
      (logCost + heightCost + momentCost) + saving + 15 * rho0 / 8 ≤ 49 / 440640)
    (counts : WideCountParameters.{0, 0, 0, 0} M H εm) :
    ∃ C : ℝ, 0 < C ∧
    ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (v a C0 : ℝ), 0 ≤ v → v ≤ physicalHeight + ζ → d - v ≤ μ →
      51 / 100 < a → a ≤ 1 → 0 ≤ C0 →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (d - margin)) →
      (∀ u ∈ rows, Z ^ v ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z ^ v) →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows,
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * i : ℕ) * Z ^ τ)) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀ t : HeightSpace,
      ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) ∧
        |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) →
      ProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17 / 50 : ℂ) + t.1.2 * Complex.I) (deltaGap β)
        (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
        (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
        (C0 * Z ^ momentCost) (Z ^ heightCost) εm →
      ‖cubeArithmeticSum S hS hmax η rows T
        (ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y) W Y a e t‖ ≤
        C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (β - 11 / 16 - saving - scaleExponentTau rho0 a e) := by
  obtain ⟨C, hC, hclass⟩ := actual_nonfloor_class_totalE_wide M H hH
    N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss totalE
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi
    W hWs hW hWB hellsum totalE_ge_sixth hdtop hε1 hκ1 hτzero hτheight hwbudget
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    εm (deltaGap β) ν logCost heightCost momentCost hεm (deltaGap_nonneg hβ0.le)
    (deltaGap_le_wide hβ1) hν hlog hMomentHeight counts
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound mesh : ℝ) ^ N
  have hcardCost : 0 ≤ cardCost := by dsimp [cardCost]; positivity
  refine ⟨(cardCost + 1) * C, by positivity, ?_⟩
  intro η
  filter_upwards [hclass η, eventually_gt_atTop (1 : ℝ)] with Z hclass hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom
  let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
  let Y : Fin N → ℝ := fun j => Z ^ (ell j)
  let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass M H) S c b (Y j)
  let Q := physical M H (fun u : FreeRow => u.val) W (fun _ => b)
    (fun j => ell j / d) (fun _ => z) (Z ^ d)
  let bound : ℝ := C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
    Z ^ (β - 11 / 16 - saving - scaleExponentTau rho0 a e)
  have hb : 0 ≤ bound := by dsimp [bound]; positivity
  have hpart := ProbeHighRowFamily.cubeArithmeticSum_class_uniform S hS hmax η rows T
    (ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y) W Y a e t Finset.univ
    (Z ^ d) ((2 * a - 1) / 2) mesh hmesh (by linarith) (fun j => ell j / d) Q bound hb (by
      intro bin hne
      have hp := hclass d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
        t ht hmom bin hne
      dsimp only at hp
      let q := classMean Finset.univ ((2 * a - 1) / 2) mesh (fun j => ell j / d) bin
      let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2)
        mesh hmesh (fun j => ell j / d) Q bin
      have hne' : rows'.Nonempty := by simpa [rows'] using hne
      have hsub : rows' ⊆ rows := Finset.filter_subset _ _
      obtain ⟨u0, hu0⟩ := hne'
      have hpow : Z ^ v ≤ Z ^ (d - margin) :=
        (hnorm u0 (hsub hu0)).1.trans (hrows u0 (hsub hu0)).2.2.2
      have hvdm : v ≤ d - margin := (Real.rpow_le_rpow_left_iff hZ).mp hpow
      have hv1 : v ≤ 1 := by linarith [hvdm, hd', hdtop, hmargin]
      have hs := adaptive_mixed_saving_gap N a q β ε εm R ν ζ μ v d e eps loss mesh
        (logCost + heightCost + momentCost) saving (by linarith) ha' hp.1 hp.2.1 hβ0 hβ1
        hε.le hεm.le hR hν.le hcount hζ hζ1 hv' hv1 hμ hdv he.le heps.le hmesh.le hfinal
      have hadapt :
          ProbeHighRowFamily.adaptiveRowExponent (2 * a - 1) q (deltaGap β) ε εm R ν =
            adaptiveRowExponentWide (2 * a - 1) q β ε εm R ν := by
        unfold ProbeHighRowFamily.adaptiveRowExponent adaptiveRowExponentWide
        rfl
      have hid := central_class_exponent_identity_total N rho0 a v d
        (adaptiveRowExponentWide (2 * a - 1) q β ε εm R ν) q e eps loss mesh
        (logCost + heightCost + momentCost)
      apply hp.2.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      rw [hadapt]
      rw [show ellTau rho0 = totalE by rfl] at hid
      unfold arithmeticExponentTotal at hid
      linarith)
  simp only [Finset.card_univ, Fintype.card_fin] at hpart
  calc
    _ ≤ cardCost * bound := hpart
    _ ≤ (cardCost + 1) * bound := mul_le_mul_of_nonneg_right (by linarith) hb
    _ = _ := by dsimp [bound]; ring

/-! ## Height integral: shifted X,Y are carried explicitly. -/

theorem actual_nonfloor_cube_norm_perturbed
    (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hτ : 0 < τ) (hε : 0 < ε) (hκ : 0 < κ)
    (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8 * e * R + κ ≤ ε) (hgap : ε < rmin * mesh)
    (hmargin : 0 < margin) (hheight : 2 * τ < dmin * cost)
    (hloss : τ * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4 * e) S)
    (hmax : ∀ P ∈ S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀ j, dmax * rmin ≤ ell j) (hellhi : ∀ j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℂ) (hWs : ∀ j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hWB : ∀ j t, ‖W j t‖ ≤ A)
    (hellsum : ∑ j, ell j = totalE)
    (hdtop : dmax ≤ 37 / 42) (hε1 : ε ≤ 1 / 1000) (hκ1 : κ ≤ 1)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * cost)
    (hwbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * cost ≤ ε / 2)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm ν logCost heightCost momentCost β : ℝ)
    (hεm : 0 < εm) (hν : 0 < ν) (hlog : 0 < logCost)
    (hMomentHeight : τ < heightCost) (hβ0 : boundary < β) (hβ1 : β ≤ 1)
    (ζ μ saving : ℝ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 3 / 16) (hμ : 0 ≤ μ)
    (hcount : 159 * ε + εm + R + 7 * ν ≤ 1 / 32)
    (hfinal : physicalHeight * (159 * ε + εm + R + 7 * ν) + 2 * ζ +
      (3 / 2) * μ + (26 * e + (N + 8) * eps + loss + totalE * mesh) +
      (logCost + heightCost + momentCost) + saving + 15 * rho0 / 8 ≤ 49 / 440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (counts : WideCountParameters.{0, 0, 0, 0} M H εm) :
    ∃ C : ℝ, 0 < C ∧
    ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (v a C0 : ℝ), 0 ≤ v → v ≤ physicalHeight + ζ → d - v ≤ μ →
      51 / 100 < a → a ≤ 1 → 0 ≤ C0 → ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z ^ (d - margin)) →
      (∀ u ∈ rows, Z ^ v ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z ^ v) →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * i : ℕ) * Z ^ τ)) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀ t : HeightSpace,
        ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) ∧
          |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) →
        ProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
          ((17 / 50 : ℂ) + t.1.2 * Complex.I) (deltaGap β)
          (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
          (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
          (C0 * Z ^ momentCost) (Z ^ heightCost) εm) →
      ‖finiteCentralCubeRows S hS hmax η rows T
        (ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y) W Y W0 W1
        (Z ^ sourceLx) (Z ^ sourceLy) Z e (fun _ => a)
        (fun _ => (3 * i + 1 : ℕ) * Z ^ τ)‖ ≤
          C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) * Z ^ (β - 11 / 16 - saving) := by
  obtain ⟨C, hC, harith⟩ := actual_nonfloor_cube_arithmetic_perturbed M H hH
    N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
    hellsum hdtop hε1 hκ1 hτzero hτheight hwbudget
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    εm ν logCost heightCost momentCost β hεm hν hlog hMomentHeight hβ0 hβ1
    ζ μ saving hζ hζ1 hμ hcount hfinal counts
  obtain ⟨D, hD, hprofile⟩ := ProbeHighRowFamily.actual_common_cube_aggregate_norm
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro η
  filter_upwards [harith η, (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with Z harith hT hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro hmom
  have hZp : 0 < Z := zero_lt_one.trans hZ
  let Y : Fin N → ℝ := fun j => Z ^ (ell j)
  let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass M H) S c b (Y j)
  let A0 : ℝ := C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
    Z ^ (β - 11 / 16 - saving - scaleExponentTau rho0 a e)
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hp := hprofile e a (Z ^ τ) ((3 * i + 1 : ℕ) * Z ^ τ) i he he1 ha.le ha' hT
    (by gcongr; omega) S hS hmax hfirst η rows (fun u hu => (hrows u hu).1)
    T (ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y) (rayCubeFamily M H hH)
    hnext W Y (Z ^ sourceLx) (Z ^ sourceLy) Z (by positivity) (by positivity) hZp A0 hA0
    (fun t ht => harith d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi
      hnext hcurrent t ht (hmom t ht))
  apply hp.trans_eq
  rw [show (Z ^ sourceLx) ^ (4 / 25 : ℝ) * Z ^ (a + 16 * e - 33 / 50) *
      (Z ^ sourceLy) ^ (-a - 6 * e) = Z ^ (scaleExponentTau rho0 a e) by
      rw [show sourceLx = lxTau rho0 by rfl, show sourceLy = lyTau rho0 by rfl]
      exact shifted_physical_scale_identity Z rho0 a e hZp]
  dsimp only [A0]
  calc
    _ = (D * C) * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
      (Z ^ (scaleExponentTau rho0 a e) *
        Z ^ (β - 11 / 16 - saving - scaleExponentTau rho0 a e)) := by ring
    _ = _ := by rw [← Real.rpow_add hZp]; congr 2; ring

/-! ## Total-E normalizer (principalScalar argument is E; residue prime powers remain unchanged). -/

include hH in
theorem actual_ray_normalizer_inverse_totalE {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0 < c) (hcb : c ≤ b)
    (ell : Fin K → ℝ) (hell : ∀ j, 0 < ell j) (hellsum : ∑ j, ell j = totalE)
    (W : Fin K → ℝ → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hcompact : ∀ j, HasCompactSupport (W j))
    (hsupp : ∀ j, Function.support (W j) ⊆ Ioo c b)
    (hp : ∀ j y, 0 ≤ W j y) (hne : ∀ j, W j ≠ 0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (hr0 : ∀ y, (W0 y).im = 0) (hr1 : ∀ y, (W1 y).im = 0)
    (hp0 : ∀ y, 0 ≤ (W0 y).re) (hp1 : ∀ y, 0 ≤ (W1 y).re)
    (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0) (nu : ℝ) (hnu : 0 < nu) :
    letI : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let T := fun j => pool (RayQuotient.identityClass M H) S c b (Z ^ (ell j))
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
        (Probe.principalScalar Finset.univ Z totalE
          (PrincipalSignalComparison.slotMass T
            (ProbePrincipalResidueActual.residueWeights W (fun j => Z ^ (ell j)))) : ℂ)
      normer ≠ 0 ∧ ‖normer⁻¹‖ ≤ C * Z ^ nu := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏ P ∈ S, P)
  refine ⟨‖cs⁻¹‖ + 1, by positivity, ?_⟩
  have hpos (j : Fin K) : tsupport (W j) ⊆ Ioi 0 := by
    apply Subset.trans (closure_minimal (Subset.trans (hsupp j) Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [ProbeRaySlots.power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW
      hcompact hpos hp hne ell hell nu hnu, eventually_gt_atTop (0 : ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏ P ∈ S, P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j => pool (RayQuotient.identityClass M H) S c b (Z ^ (ell j)))
    (ProbePrincipalResidueActual.residueWeights W (fun j => Z ^ (ell j))) Z totalE hZ
    (fun j _ => hmass.1 j), ?_⟩
  have hb0 : ‖(PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
      (Probe.principalScalar Finset.univ Z totalE
        (PrincipalSignalComparison.slotMass
          (fun j => pool (RayQuotient.identityClass M H) S c b (Z ^ (ell j)))
          (ProbePrincipalResidueActual.residueWeights W (fun j => Z ^ (ell j)))) : ℂ))⁻¹‖ ≤
      ‖cs⁻¹‖ * Z ^ nu := by
    rw [mul_inv_rev, norm_mul, ← Complex.ofReal_inv, Complex.norm_real]
    simpa only [hellsum, Real.norm_eq_abs, mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb0.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

/-! ## Normalized central rows. -/

theorem actual_normalized_nonfloor_cube_perturbed
    (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hτ : 0 < τ) (hε : 0 < ε) (hκ : 0 < κ)
    (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8 * e * R + κ ≤ ε) (hgap : ε < rmin * mesh)
    (hmargin : 0 < margin) (hheight : 2 * τ < dmin * cost)
    (hloss : τ * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4 * e) S)
    (hmax : ∀ P ∈ S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀ j, dmax * rmin ≤ ell j) (hellhi : ∀ j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℝ)
    (hWs : ∀ j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hWB : ∀ j t, 0 ≤ W j t ∧ W j t ≤ A)
    (hcompact : ∀ j, HasCompactSupport (W j)) (hne : ∀ j, W j ≠ 0)
    (hellsum : ∑ j, ell j = totalE)
    (hdtop : dmax ≤ 37 / 42) (hε1 : ε ≤ 1 / 1000) (hκ1 : κ ≤ 1)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * cost)
    (hwbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * cost ≤ ε / 2)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm ν logCost heightCost momentCost β : ℝ)
    (hεm : 0 < εm) (hν : 0 < ν) (hlog : 0 < logCost)
    (hMomentHeight : τ < heightCost) (hβ0 : boundary < β) (hβ1 : β ≤ 1)
    (ζ μ saving : ℝ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 3 / 16) (hμ : 0 ≤ μ)
    (hcount : 159 * ε + εm + R + 7 * ν ≤ 1 / 32)
    (hfinal : physicalHeight * (159 * ε + εm + R + 7 * ν) + 2 * ζ +
      (3 / 2) * μ + (26 * e + (N + 8) * eps + loss + totalE * mesh) +
      (logCost + heightCost + momentCost) + saving + 15 * rho0 / 8 ≤ 49 / 440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (hr0 : ∀ y, (W0 y).im = 0) (hr1 : ∀ y, (W1 y).im = 0)
    (hp0 : ∀ y, 0 ≤ (W0 y).re) (hp1 : ∀ y, 0 ≤ (W1 y).re)
    (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0) (normNu : ℝ) (hnormNu : 0 < normNu)
    (counts : WideCountParameters.{0, 0, 0, 0} M H εm) :
    letI : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧
    ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (v a C0 : ℝ), 0 ≤ v → v ≤ physicalHeight + ζ → d - v ≤ μ →
      51 / 100 < a → a ≤ 1 → 0 ≤ C0 → ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z ^ (d - margin)) →
      (∀ u ∈ rows, Z ^ v ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z ^ v) →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * i : ℕ) * Z ^ τ)) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀ t : HeightSpace,
        ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) ∧
          |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) →
        ProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows ell
          (fun j y => (W j y : ℂ)) Z d a ε τ dmax b R mesh i
          ((17 / 50 : ℂ) + t.1.2 * Complex.I) (deltaGap β)
          (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
          (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
          (C0 * Z ^ momentCost) (Z ^ heightCost) εm) →
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
        (Probe.principalScalar Finset.univ Z totalE
          (PrincipalSignalComparison.slotMass T
            (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer ≠ 0 ∧
      ‖finiteCentralCubeRows S hS hmax η rows T
        (ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y)
        (fun j y => (W j y : ℂ)) Y W0 W1 (Z ^ sourceLx) (Z ^ sourceLy) Z e
        (fun _ => a) (fun _ => (3 * i + 1 : ℕ) * Z ^ τ) / normer‖ ≤
        C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (β - 11 / 16 - saving + normNu) := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N → ℝ → ℂ := fun j y => (W j y : ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j) ⊆ Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC]; rw [hh]; simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖ ≤ A := by
    simpa only [WC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hWB j y).1]
      using (hWB j y).2
  obtain ⟨C, hC, hbound⟩ := actual_nonfloor_cube_norm_perturbed M H hH
    N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB
    hellsum hdtop hε1 hκ1 hτzero hτheight hwbudget
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    εm ν logCost heightCost momentCost β hεm hν hlog hMomentHeight hβ0 hβ1
    ζ μ saving hζ hζ1 hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 counts
  have hellpos (j : Fin N) : 0 < ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn, hCn, hnormer⟩ := actual_ray_normalizer_inverse_totalE M H hH S hS c b hc hcb
    ell hellpos hellsum W hW hcompact hWs (fun j y => (hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 normNu hnormNu
  refine ⟨C * Cn, mul_pos hC hCn, ?_⟩
  intro η
  filter_upwards [hbound η, hnormer, eventually_gt_atTop (0 : ℝ)] with Z hb hn hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only at hn ⊢
  intro hmom
  refine ⟨hn.1, ?_⟩
  have hh := hb d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent hmom
  rw [div_eq_mul_inv, norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (β - 11 / 16 - saving) normNu]
  ring

/-! ## Collected dyadic rows, with the perturbed height cap. -/

theorem actual_nonfloor_rows_saving_perturbed
    (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hτ : 0 < τ) (hε : 0 < ε) (hκ : 0 < κ)
    (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8 * e * R + κ ≤ ε) (hgap : ε < rmin * mesh)
    (hmargin : 0 < margin) (hheight : 2 * τ < dmin * cost)
    (hloss : τ * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4 * e) S)
    (hmax : ∀ P ∈ S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀ j, dmax * rmin ≤ ell j) (hellhi : ∀ j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℝ)
    (hWs : ∀ j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hWB : ∀ j t, 0 ≤ W j t ∧ W j t ≤ A)
    (hcompact : ∀ j, HasCompactSupport (W j)) (hne : ∀ j, W j ≠ 0)
    (hellsum : ∑ j, ell j = totalE)
    (hdtop : dmax ≤ 37 / 42) (hε1 : ε ≤ 1 / 1000) (hκ1 : κ ≤ 1)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * cost)
    (hwbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * cost ≤ ε / 2)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm ν logCost heightCost momentCost β : ℝ)
    (hεm : 0 < εm) (hν : 0 < ν) (hlog : 0 < logCost)
    (hMomentHeight : τ < heightCost) (hβ0 : boundary < β) (hβ1 : β ≤ 1)
    (ζ μ saving : ℝ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 3 / 16) (hμ : 0 ≤ μ)
    (hcount : 159 * ε + εm + R + 7 * ν ≤ 1 / 32)
    (hfinal : physicalHeight * (159 * ε + εm + R + 7 * ν) + 2 * ζ +
      (3 / 2) * μ + (26 * e + (N + 8) * eps + loss + totalE * mesh) +
      (logCost + heightCost + momentCost) + saving + 15 * rho0 / 8 ≤ 49 / 440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (hr0 : ∀ y, (W0 y).im = 0) (hr1 : ∀ y, (W1 y).im = 0)
    (hp0 : ∀ y, 0 ≤ (W0 y).re) (hp1 : ∀ y, 0 ≤ (W1 y).re)
    (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0) (normNu : ℝ) (hnormNu : 0 < normNu)
    (m : ℕ) (dyadCost : ℝ) (hdyadCost : 0 < dyadCost)
    (hdmin1 : dmin < 1 / 100)
    (hconductor : physicalHeight + ζ + 2 * margin ≤ dmax)
    (hmuMargin : 2 * margin ≤ μ) (counts : WideCountParameters.{0, 0, 0, 0} M H εm) :
    letI : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧
    ∀ η : Character, ∀ᶠ Z : ℝ in atTop, ∀ C0 : ℝ, 0 ≤ C0 →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (physicalHeight + ζ)) →
      ∀ idx grid : FreeRow → ℕ,
      (∀ u ∈ rows, idx u ≤ n ∧ grid u ≤ m ∧ grid u ≠ 0 ∧ 51 / 100 + e * grid u ≤ 1) →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (idx u + 1 : ℕ) * Z ^ τ) < 51 / 100 + e * grid u + 2 * e) →
      (∀ u ∈ rows, 51 / 100 + e * grid u ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * idx u : ℕ) * Z ^ τ)) →
      (∀ k ∈ ProbeHighRowFamily.smallDyadicIndices (Z ^ (physicalHeight + ζ)),
        ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (m + 1),
        let rows' := ProbeHighRowFamily.cubeBinRows
          (rows ∩ ProbeHighRowFamily.dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀ t : HeightSpace,
        ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) ∧
          |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) →
        ProbeHighRowFamily.SourceMomentsAt M H hH S hS.prime η rows' ell
          (fun j y => (W j y : ℂ)) Z
          (ProbeHighRowFamily.sourceDyadConductor Z margin k) (51 / 100 + e * j)
          ε τ dmax b R mesh i ((17 / 50 : ℂ) + t.1.2 * Complex.I) (deltaGap β)
          (if 2 * (51 / 100 + e * j) - 1 ≤ 5 / 6 then counts.cB else counts.cH)
          (if 2 * (51 / 100 + e * j) - 1 ≤ 5 / 6 then counts.kB else counts.kH)
          (C0 * Z ^ momentCost) (Z ^ heightCost) εm) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass M H) S c b (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
        (Probe.principalScalar Finset.univ Z totalE
          (PrincipalSignalComparison.slotMass T
            (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer ≠ 0 ∧
      ‖finiteCentralCubeRows S hS hmax η rows T
        (ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y)
        (fun j y => (W j y : ℂ)) Y W0 W1 (Z ^ sourceLx) (Z ^ sourceLy) Z e
        (fun u => 51 / 100 + e * grid u)
        (fun u => (3 * idx u + 1 : ℕ) * Z ^ τ) / normer‖ ≤
        C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (β - 11 / 16 - saving + normNu + dyadCost) := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C, hC, hbound⟩ := actual_normalized_nonfloor_cube_perturbed M H hH
    N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
    hcompact hne hellsum hdtop hε1 hκ1 hτzero hτheight hwbudget
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    εm ν logCost heightCost momentCost β hεm hν hlog hMomentHeight hβ0 hβ1
    ζ μ saving hζ hζ1 hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 normNu hnormNu counts
  have hellpos (j : Fin N) : 0 < ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn, hCn, hnormer⟩ := actual_ray_normalizer_inverse_totalE M H hH S hS c b hc hcb
    ell hellpos hellsum W hW hcompact hWs (fun j y => (hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 normNu hnormNu
  obtain ⟨Cd, hCd, hdyad⟩ := ProbeHighRowFamily.canonical_dyad_cost dyadCost hdyadCost
  refine ⟨Cd * (n + 1 : ℕ) * (m + 1 : ℕ) * C, by positivity, ?_⟩
  intro η
  filter_upwards [hbound η, hnormer,
    ProbeHighRowFamily.sourceDyad_geometry_eventually dmin dmax margin (physicalHeight + ζ)
      hdmin hdmin1 hmargin hconductor,
    eventually_gt_atTop (1 : ℝ)] with Z hb hn hg hZ
  intro C0 hC0 rows hrows idx grid hlabels hnext hcurrent hmom
  dsimp only at hn ⊢
  refine ⟨hn.1, ?_⟩
  have hZp : 0 < Z := zero_lt_one.trans hZ
  let Y : Fin N → ℝ := fun j => Z ^ (ell j)
  let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass M H) S c b (Y j)
  let hT := ProbeHighRowFamily.nonfloorPoolOutside M H S N c b Y
  let WC : Fin N → ℝ → ℂ := fun j y => (W j y : ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
    (Probe.principalScalar Finset.univ Z totalE
      (PrincipalSignalComparison.slotMass T
        (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
    Z ^ (β - 11 / 16 - saving + normNu)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let F : Finset FreeRow → (FreeRow → ℝ) → (FreeRow → ℝ) → ℂ := fun rows a Ht =>
    finiteCentralCubeRows S hS hmax η rows T hT WC Y W0 W1
      (Z ^ sourceLx) (Z ^ sourceLy) Z e a Ht
  have hcell (k : ℕ) (hk : k ∈ ProbeHighRowFamily.smallDyadicIndices (Z ^ (physicalHeight + ζ)))
      (i : ℕ) (hi : i ∈ Finset.range (n + 1))
      (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      ‖F (ProbeHighRowFamily.cubeBinRows
        (rows ∩ ProbeHighRowFamily.dyadicRows 1 k) idx grid i j)
        (fun _ => 51 / 100 + e * j) (fun _ => (3 * i + 1 : ℕ) * Z ^ τ) / normer‖ ≤ D := by
    let Rk := rows ∩ ProbeHighRowFamily.dyadicRows 1 k
    let Rij := ProbeHighRowFamily.cubeBinRows Rk idx grid i j
    have hsubk : Rij ⊆ Rk := Finset.filter_subset _ _
    have hsub : Rij ⊆ rows := hsubk.trans Finset.inter_subset_left
    by_cases hne' : Rij.Nonempty
    · have hgeo := hg rows
        (fun u hu => ⟨(hrows u hu).1, (hrows u hu).2.1, (hrows u hu).2.2.2⟩)
        k (hne'.mono hsubk)
      obtain ⟨u, hu⟩ := hne'
      have huj : grid u = j :=
        ((ProbeHighRowFamily.mem_cubeBinRows Rk idx grid i j u).mp hu).2.2
      have hju : j ≠ 0 := huj ▸ (hlabels u (hsub hu)).2.2.1
      have ha : 51 / 100 < 51 / 100 + e * j := by
        have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith
      have ha' : 51 / 100 + e * j ≤ 1 := by
        simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀ u ∈ Rij, detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (i + 1 : ℕ) * Z ^ τ) < 51 / 100 + e * j + 2 * e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (ProbeHighRowFamily.mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1, hm.2.2] at hh
      have hcurrent' : ∀ u ∈ Rij, 51 / 100 + e * j ≤ detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * i : ℕ) * Z ^ τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (ProbeHighRowFamily.mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1, hm.2.2] at hh
      have hbounded := hb (ProbeHighRowFamily.sourceDyadConductor Z margin k)
        hgeo.2.2.1 hgeo.2.2.2.1 (ProbeHighRowFamily.sourceDyadExponent Z k)
        (51 / 100 + e * j) C0 hgeo.1 hgeo.2.1
        (by unfold ProbeHighRowFamily.sourceDyadConductor; linarith) ha ha' hC0 Rij
        (fun u hu => ⟨(hrows u (hsub hu)).1, (hrows u (hsub hu)).2.1,
          (hrows u (hsub hu)).2.2.1, hgeo.2.2.2.2.2 u (hsubk hu)⟩)
        (fun u hu => hgeo.2.2.2.2.1 u (hsubk hu)) i
        (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hnext' hcurrent'
        (fun t ht => hmom k hk i hi j hj ⟨u, hu⟩ t ht)
      exact hbounded.2
    · have heq : Rij = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F, show ProbeHighRowFamily.cubeBinRows
        (rows ∩ ProbeHighRowFamily.dyadicRows 1 k) idx grid i j = ∅ from heq,
        finiteCentralCubeRows, Finset.sum_empty, zero_div, norm_zero] using hD
  have hpartition :
      F rows (fun u => 51 / 100 + e * grid u)
        (fun u => (3 * idx u + 1 : ℕ) * Z ^ τ) =
      ∑ k ∈ ProbeHighRowFamily.smallDyadicIndices (Z ^ (physicalHeight + ζ)),
        F (rows ∩ ProbeHighRowFamily.dyadicRows 1 k)
          (fun u => 51 / 100 + e * grid u)
          (fun u => (3 * idx u + 1 : ℕ) * Z ^ τ) := by
    unfold F finiteCentralCubeRows
    exact ProbeHighRowFamily.retained_dyadic_sum rows _
      (fun u hu => ⟨(hrows u hu).1, (hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u => 51 / 100 + e * grid u)
    (fun u => (3 * idx u + 1 : ℕ) * Z ^ τ) / normer‖ ≤ _
  rw [hpartition, Finset.sum_div]
  calc
    _ ≤ ∑ k ∈ ProbeHighRowFamily.smallDyadicIndices (Z ^ (physicalHeight + ζ)),
        (n + 1 : ℕ) * (m + 1 : ℕ) * D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := ProbeHighRowFamily.finiteCentralCubeRows_bin_partition S hS hmax η
        (rows ∩ ProbeHighRowFamily.dyadicRows 1 k) T hT WC Y W0 W1
        (Z ^ sourceLx) (Z ^ sourceLy) Z e (Z ^ τ) idx grid n m
        (fun u hu => ⟨(hlabels u (Finset.mem_inter.mp hu).1).1,
          (hlabels u (Finset.mem_inter.mp hu).1).2.1⟩)
      change ‖F (rows ∩ ProbeHighRowFamily.dyadicRows 1 k)
        (fun u => 51 / 100 + e * grid u)
        (fun u => (3 * idx u + 1 : ℕ) * Z ^ τ) / normer‖ ≤ _
      dsimp only [F]
      rw [hpart, Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), D := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum (fun j hj => hcell k hk i hi j hj))
        _ = _ := by simp; ring
    _ = ((ProbeHighRowFamily.smallDyadicIndices (Z ^ (physicalHeight + ζ))).card : ℝ) *
        ((n + 1 : ℕ) * (m + 1 : ℕ) * D) := by simp
    _ ≤ (Cd * Z ^ dyadCost) * ((n + 1 : ℕ) * (m + 1 : ℕ) * D) :=
      mul_le_mul_of_nonneg_right
        (hdyad Z (physicalHeight + ζ) hZ.le (by linarith)) (by positivity)
    _ = _ := by
      dsimp [D]
      rw [Real.rpow_add hZp (β - 11 / 16 - saving + normNu) dyadCost]
      ring

end SevenEighths.PerturbedCentral
end
end OAI
