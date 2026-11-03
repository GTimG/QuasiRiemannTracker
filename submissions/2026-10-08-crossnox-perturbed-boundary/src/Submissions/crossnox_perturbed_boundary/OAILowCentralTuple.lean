/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowCentralTuple.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAILowPhysicalInverseBound
import Submissions.crossnox_perturbed_boundary.OAILowSlotScales
import Submissions.crossnox_perturbed_boundary.OAILowUnselectedMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCentralTuple

namespace OAI

noncomputable section

open scoped Classical ContDiff

namespace SevenEighths.ProbePhysical

open AsymmetricGeometry

open CompletedGauss CanonicalQuadraticSieve RayFourExpansion

local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_low_central_compensated_tuple
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (t : ℝ) (ht : 0 ≤ t) (htSmall : t ≤ 1 / 30)
    (hsum : ∑ i, ell i ≤ 1 / 6 + t)
    (a b ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 M : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hab1 : a1 < b1) (hM : 0 ≤ M)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWM : ∀ x, ‖W1 x‖ ≤ M) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧
      ∀ (T : Fin K → Finset PrimeIdeal),
        (∀ i P, P ∈ T i → Supported P.val) →
        (∀ i P, P ∈ T i → P.val ∉ S) →
        Pairwise (fun i j => Disjoint (T i) (T j)) →
        (∀ i P, P ∈ T i →
          a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧
          (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
      ∀ (J : Finset (Fin K)) (X : ℝ), 0 < X →
        Z ^ (1 + lowSelectedLength ell J - ε / 2) ≤ X →
        X ≤ Z ^ (1 + lowSelectedLength ell J + ε / 2) →
      ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ θ : ℝ,
        ‖∑ p : ∀ i, canonicalSlotSupport (T i),
          compensationSubsetWeight η W (fun i => Z ^ (ell i))
            (fun i => (p i).val) J *
          compensationRowTest η (calibrationForSet S hS) W0 W1
            (fun i => (p i).val) J
            (Z ^ (xBase - t / 2))
            (Z ^ (yBase - t / 2)) X θ *
          selectedSlotFactor W (fun i => Z ^ (ell i))
            (fun i => (p i).val) J θ‖ ≤
          C * (1 + ‖θ‖) ^ degree *
            Z ^ (lowBase - t / 4 + 254 * ε) := by
  obtain ⟨Cg, hCg, hgram⟩ :=
    compensation_tuple_actual_gram ε hε hε1 W0 W1
      a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1
      hW0s hW1s hWM S hS hbad
  obtain ⟨degree, Ci, hCi, hinverse⟩ :=
    perturbed_low_physical_inverse_normalized η S hS hbad
      ell hell t ht (by linarith) hsum a b
      (a0 * a1) (max 1 (b0 * b1)) ε ha
      (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu, hCu, hmass⟩ :=
    perturbed_lowUnselectedMass_bound K a b ha ell hell
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0 < q := calibration_elementNorm_pos _
  let C0 := Cg * Ci * Real.sqrt (3 * q) * Cu
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨degree, C0, hC0, ?_⟩
  filter_upwards [hinverse,
    eventually_perturbed_original_slot_scales
      (calibrationForSet S hS) ell hell t ht
      (by linarith : t < 1 / 24) hsum
      (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1, ?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW θ
  let slots := fun i => canonicalSlotSupport (T i)
  let Yp := fun i => Z ^ (ell i)
  let d := lowUnselectedLength ell J
  let loss := max 0 ((d - 1 / 6 + 5 * t) / 4)
  let gramExponent := lowBase - t / 4 + (yBase / 2 - t / 4) * ε
  let inverseExponent := (loss + 507 * ε) / 2
  have hz : 0 < Z := lt_trans zero_lt_one hInv.1
  have hd : 0 ≤ d := Finset.sum_nonneg (fun i _ => hell i)
  have hslots : ∀ i n, n ∈ slots i → n ≠ 0 :=
    fun i => canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀ i n, n ∈ slots i →
      elementNorm n ≤ max 1 b * Z ^ (ell i) := by
    intro i n hn
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp
    (Z ^ (xBase - t / 2)) (Z ^ (yBase - t / 2)) X θ
    (by positivity) (by positivity) hX
    (fun p => (hs p).1) (fun p => (hs p).2.1)
  apply hg.trans
  let G := Z ^ gramExponent
  let V := Ci * (1 + ‖θ‖) ^ degree * Z ^ inverseExponent
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏ i : J, (p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS)
        (Z ^ (xBase - t / 2) / L)
        (Z ^ (yBase - t / 2) / L)
      ‖lowUnselectedWeight slots J W Yp p‖ *
        ((Real.sqrt Q)⁻¹ / (2 * Real.pi)) *
        lowGramFactor (calibrationForSet S hS)
          (Z ^ (xBase - t / 2) / L)
          (Z ^ (yBase - t / 2) / L) ε *
        lowInverseMass (calibrationForSet S hS)
          (a0 * a1) (max 1 (b0 * b1))
          (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z ^ (xBase - t / 2) / L)
          (Z ^ (yBase - t / 2) / L)
          (div_pos (by positivity)
            (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity)
            (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η slots J W Yp θ)
            η S hS (lowSelectedIdeal slots J) X θ) ≤
        (Ci * Real.sqrt (3 * q) * (1 + ‖θ‖) ^ degree *
          Z ^ (gramExponent + inverseExponent)) *
          (‖lowUnselectedWeight slots J W Yp p‖ *
            L ^ (-(1 / 2 : ℝ))) := by
    dsimp only
    let L := elementNorm (∏ i : J, (p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS)
      (Z ^ (xBase - t / 2) / L)
      (Z ^ (yBase - t / 2) / L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX
      hXlo hXhi W hW θ
      (div_pos (by positivity) hL)
      (div_pos (by positivity) hL)
    have hgn : 0 ≤ lowGramFactor (calibrationForSet S hS)
        (Z ^ (xBase - t / 2) / L)
        (Z ^ (yBase - t / 2) / L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb
        (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0 ≤ V by dsimp [V]; positivity)
    calc
      _ = ‖lowUnselectedWeight slots J W Yp p‖ *
        lowGramFactor (calibrationForSet S hS)
          (Z ^ (xBase - t / 2) / L)
          (Z ^ (yBase - t / 2) / L) ε *
        (Real.sqrt Q)⁻¹ / (2 * Real.pi) *
        lowInverseMass (calibrationForSet S hS)
          (a0 * a1) (max 1 (b0 * b1))
          (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z ^ (xBase - t / 2) / L)
          (Z ^ (yBase - t / 2) / L)
          (div_pos (by positivity) hL)
          (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η slots J W Yp θ)
            η S hS (lowSelectedIdeal slots J) X θ) := by ring
      _ ≤ (‖lowUnselectedWeight slots J W Yp p‖ *
        Real.sqrt (3 * q / L)) * (G * V) := by
          have hh3 := hh.trans hh2
          simp only [G, V, gramExponent, inverseExponent,
            loss, d, div_eq_mul_inv, mul_assoc] at hh3 ⊢
          convert hh3 using 1
          congr 7
      _ = (‖lowUnselectedWeight slots J W Yp p‖ *
          Real.sqrt (3 * q / L)) *
          (Ci * (1 + ‖θ‖) ^ degree *
            Z ^ (gramExponent + inverseExponent)) := by
        dsimp only [G, V]
        calc
          _ = (‖lowUnselectedWeight slots J W Yp p‖ *
              Real.sqrt (3 * q / L)) *
              (Ci * (1 + ‖θ‖) ^ degree *
                (Z ^ gramExponent * Z ^ inverseExponent)) := by ring
          _ = _ := by rw [← Real.rpow_add hz]
      _ = _ := by
        rw [low_compensated_sqrt_factor q L hq.le hL]
        ring
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun p _ => hterm p)) hCg.le
  apply hh.trans
  rw [← Finset.mul_sum]
  have hm := hmass Z hInv.1.le T hT hnorm J W Yp hW
  have hloss : loss / 2 ≤ d := by
    have hbound : max 0 ((d - 1 / 6 + 5 * t) / 4) ≤ 2 * d := by
      apply max_le
      · linarith
      · linarith
    dsimp [loss]
    linarith
  have hpower : gramExponent + inverseExponent - d ≤
      lowBase - t / 4 + 254 * ε := by
    dsimp [gramExponent, inverseExponent]
    have hte : 0 ≤ t * ε := mul_nonneg ht hε.le
    have hy : yBase / 2 ≤ (1 / 2 : ℝ) := by norm_num [yBase, skew]
    have hye := mul_le_mul_of_nonneg_right hy hε.le
    nlinarith
  calc
    _ ≤ Cg * ((Ci * Real.sqrt (3 * q) *
        (1 + ‖θ‖) ^ degree *
        Z ^ (gramExponent + inverseExponent)) *
        (Cu * Z ^ (-d))) := by gcongr
    _ = C0 * (1 + ‖θ‖) ^ degree *
        Z ^ (gramExponent + inverseExponent - d) := by
      dsimp only [C0]
      calc
        _ = (Cg * Ci * Real.sqrt (3 * q) * Cu) *
            (1 + ‖θ‖) ^ degree *
            (Z ^ (gramExponent + inverseExponent) * Z ^ (-d)) := by ring
        _ = _ := by rw [← Real.rpow_add hz]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hInv.1.le hpower)
        (by positivity)

end SevenEighths.ProbePhysical

end

end OAI
