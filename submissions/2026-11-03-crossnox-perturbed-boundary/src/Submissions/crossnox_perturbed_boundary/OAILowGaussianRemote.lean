/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowGaussianRemote.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAILowRemoteMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGaussianRemote

namespace OAI

noncomputable section

open scoped Classical ContDiff SchwartzMap

namespace SevenEighths.ProbePhysical

open AsymmetricGeometry

open CompletedGauss CanonicalQuadraticSieve

local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma eventually_perturbed_low_physical_scales
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (t : ℝ) (_ht : 0 ≤ t) (htSmall : t ≤ 1 / 30)
    (hsum : ∑ i, ell i ≤ 1 / 6 + t) (b : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧
      ∀ (slots : Fin K → Finset O),
        (∀ i x, x ∈ slots i → x ≠ 0) →
        (∀ i x, x ∈ slots i →
          elementNorm x ≤ b * Z ^ (ell i)) →
        ∀ (J : Finset (Fin K)) (p : ∀ i, slots i),
          1 ≤ Z ^ (xBase - t / 2) /
            elementNorm (slotProduct (fun i => (p i).val) J) ∧
          1 ≤ Z ^ (yBase - t / 2) /
            elementNorm (slotProduct (fun i => (p i).val) J) := by
  have hmargin : 0 < (xBase - 1 / 6 - 3 * t / 2) := by
    have hs : 0 ≤ skew := by norm_num [skew]
    dsimp only [xBase]
    linarith
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop hmargin).eventually
      (Filter.eventually_ge_atTop ((max 1 b) ^ K))]
    with Z hZ hc
  refine ⟨hZ, ?_⟩
  intro slots hn hnorm J p
  have hl : 0 < elementNorm
      (slotProduct (fun i => (p i).val) J) :=
    slotProduct_norm_pos _ (fun i => hn i _ (p i).property) J
  have hb := perturbed_lowUnselectedProduct_norm_bound
    ell hell t hsum (max 1 b) Z (le_max_left _ _) hZ.le
    slots (fun i n hm => (hnorm i n hm).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i => p i.val)
  rw [← slotProduct_subtype (fun i => (p i).val) J] at hb
  have hLX : elementNorm
      (slotProduct (fun i => (p i).val) J) ≤
      Z ^ (xBase - t / 2) := by
    apply hb.trans
    calc
      _ ≤ Z ^ (xBase - 1 / 6 - 3 * t / 2) * Z ^ (1 / 6 + t) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by
        rw [← Real.rpow_add (lt_trans zero_lt_one hZ)]
        congr 1
        ring
  constructor
  · exact (one_le_div hl).mpr hLX
  · exact (one_le_div hl).mpr
      (hLX.trans (Real.rpow_le_rpow_of_exponent_le hZ.le
        (by norm_num [xBase, yBase, skew])))

lemma perturbed_low_remote_power
    (Z ell t ε : ℝ) (N : ℕ) (hZ : 1 ≤ Z)
    (hell : ell ≤ 1 / 6 + t) (htSmall : t ≤ 1 / 30)
    (hN : 5 ≤ (ε / 2) * (N : ℝ)) :
    Z * (Z ^ (1 + ell)) ^ 2 /
      (Z ^ (ε / 2)) ^ N ≤ Z ^ (-1 : ℝ) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hsq : (Z ^ (1 + ell)) ^ 2 = Z ^ (2 * (1 + ell)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    congr 1
    push_cast
    ring
  have hn : (Z ^ (ε / 2)) ^ N =
      Z ^ ((ε / 2) * (N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
  rw [hsq, hn,
    show Z * Z ^ (2 * (1 + ell)) =
      Z ^ (1 + 2 * (1 + ell)) by
      rw [Real.rpow_add hz, Real.rpow_one],
    ← Real.rpow_sub hz]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem perturbed_low_remote_gaussian_dyads
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (t : ℝ) (ht : 0 ≤ t) (htSmall : t ≤ 1 / 30)
    (hsum : ∑ i, ell i ≤ 1 / 6 + t)
    (b ε : ℝ) (hε : 0 < ε)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V : ℝ → ℂ))
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hWB0 : ∀ x, ‖W0 x‖ ≤ B0)
    (hWB1 : ∀ x, ‖W1 x‖ ≤ B1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧
      ∀ (η : HeckeFamily.Character) (T : Fin K → Finset PrimeIdeal),
        (∀ i P, P ∈ T i → Supported P.val) →
        (∀ i P, P ∈ T i →
          (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
      ∀ (J : Finset (Fin K))
        (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
        let f := fun j : ℕ =>
          if lowRemote Z (lowSelectedLength ell J) ε ((2 : ℝ) ^ j)
          then ‖lowCommonDyad η (calibrationForSet S hS)
            W0 W1 (fun i => canonicalSlotSupport (T i))
            W (fun i => Z ^ (ell i)) J
            (Z ^ (xBase - t / 2))
            (Z ^ (yBase - t / 2)) ((2 : ℝ) ^ j)
            (Z ^ (1 + lowSelectedLength ell J)) V hV‖
          else 0
        Summable f ∧ (∑' j : ℕ, f j) ≤ C * Z ^ (-1 : ℝ) := by
  have hep : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((5 : ℝ) / (ε / 2))
  have hN' : (5 : ℝ) ≤ (ε / 2) * (N : ℝ) := by
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg, hCg, he⟩ :=
    gaussianPhysicalFamily_remote_polynomial V hV N
      a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg * (q * (128 * max 1 b) ^ K)
  have hq : 0 < q := calibration_elementNorm_pos _
  refine ⟨C0, by dsimp [C0]; positivity, ?_⟩
  filter_upwards [eventually_perturbed_low_physical_scales
    ell hell t ht htSmall hsum b] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0 < Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀ i n, n ∈ canonicalSlotSupport (T i) → n ≠ 0 :=
    fun i => canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀ i n, n ∈ canonicalSlotSupport (T i) →
      elementNorm n ≤ b * Z ^ (ell i) := by
    intro i n hn
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1
    (Finset.univ : Finset (∀ i, canonicalSlotSupport (T i)))
    (fun p => compensationSubsetWeight η W
      (fun i => Z ^ (ell i)) (fun i => (p i).val) J)
    (fun p => Ideal.span
      {slotProduct (fun i => (p i).val) (Finset.univ \ J)})
    (fun p => Z ^ (xBase - t / 2) /
      elementNorm (slotProduct (fun i => (p i).val) J))
    (fun p => Z ^ (yBase - t / 2) /
      elementNorm (slotProduct (fun i => (p i).val) J))
    (fun p _ => (hs p).1) (fun p _ => (hs p).2)
    (fun i : SelectedSlot J => W i.val)
    (fun p i => elementNorm (p i.val).val / Z ^ (ell i.val))
    (Z ^ (1 + lowSelectedLength ell J))
    (Z ^ (ε / 2)) (by positivity)
    (Real.one_le_rpow hZ.1.le hep.le)
  simp only [← lowCommonDyad_eq_family] at hh
  refine ⟨?_, ?_⟩
  · convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  · have hhFinal := hh.2.trans
      (show _ ≤ C0 * Z ^ (-1 : ℝ) from by
        have hm := perturbed_compensation_scale_mass_bound
          η (calibrationForSet S hS) ell hell t hsum
          b Z hZ.1.le T hT hnorm J W hW
        calc
          _ ≤ Cg * ((q * (128 * max 1 b) ^ K) * Z) *
              (Z ^ (1 + lowSelectedLength ell J)) ^ 2 /
              (Z ^ (ε / 2)) ^ N := by gcongr
          _ = C0 * (Z * (Z ^ (1 + lowSelectedLength ell J)) ^ 2 /
              (Z ^ (ε / 2)) ^ N) := by dsimp [C0]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (perturbed_low_remote_power Z
              (lowSelectedLength ell J) t ε N hZ.1.le
              (by
                have hd : 0 ≤ lowUnselectedLength ell J :=
                  Finset.sum_nonneg (fun i _ => hell i)
                have hl := lowLength_sum ell J
                linarith)
              htSmall hN')
            (by dsimp [C0]; positivity))
    convert hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true, ite_false]

end SevenEighths.ProbePhysical

end

end OAI
