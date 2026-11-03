/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowSelectedBound.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAILowOriginalEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSelectedBound

namespace OAI

noncomputable section

open scoped Classical ContDiff

namespace SevenEighths.ProbePhysical

open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion

local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

local instance : Fintype Oˣ :=
  @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem perturbed_low_selected_physical_energy
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    (K : ℕ) (Ck ε : ℝ) (hCk : 0 < Ck) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ degree : ℕ, ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧
    ∀ (Z t d ell0 shift : ℝ),
      Z₀ ≤ Z → 0 ≤ t → t ≤ 1 / 6 → 0 ≤ d → d ≤ 1 / 6 + t →
      0 ≤ ell0 → ell0 ≤ 1 / 6 + t - d + ε → |shift| ≤ ε →
    ∀ (R : Finset O),
      (∀ z ∈ R, z ≠ 0 ∧
        elementNorm z ≤ Ck * Z ^ (5 / 6 - t - 2 * d)) →
    ∀ (T : Fin K → Finset PrimeIdeal),
      (∀ i P, P ∈ T i → Supported P.val) →
      (∀ i P, P ∈ T i → P.val ∉ S) →
      Pairwise (fun i j => Disjoint (T i) (T j)) →
    ∀ (J : Finset (Fin K)) (H : SelectedSlot J → ℝ),
      (∀ i, 1 ≤ H i) →
      (∀ i P, P ∈ T i.val → (Ideal.absNorm P.val : ℝ) ≤ H i) →
      (∏ i, H i) ≤ Z ^ ell0 →
    ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
    ∀ (Y : Fin K → ℝ) (θ : ℝ) (σ : RayRing),
      (∑ z ∈ R,
        ‖lowSelectedInverseRow Finset.univ
          (lowSelectedWeight η (fun i => canonicalSlotSupport (T i))
            J W Y θ)
          η S hS (lowSelectedIdeal (fun i => canonicalSlotSupport (T i)) J)
          (Z ^ (1 + ell0 + shift)) θ σ z‖ ^ 2) ≤
        C * (1 + ‖θ‖) ^ degree *
          Z ^ ((5 / 6 - t - 2 * d) +
            max 0 ((d - 1 / 6 + 5 * t) / 4) + 507 * ε) := by
  obtain ⟨degree, C, Z₀, hC, hZ₀, he⟩ :=
    InverseReflectedPhase.perturbed_low_original_completed_energy
      (lowReflectionPeriod η S hS) (lowReflectionPeriod_ne_zero η S hS)
      (1 : Id) squarefree_one
      (lowReflectionMask η S hS) (lowReflectionMask_ne_zero η S hS)
      (lowReflectionMask_bad η S hS hbad).1
      (lowReflectionMask_bad η S hS hbad).2
      (lowReflectionMask_period η S hS)
      (lowReflectionMask_bad_ideals η S hS hbad)
      (1 / 2) 2 (by norm_num) gaussianFixedWindow
      gaussianFixedWindow_support gaussianFixedWindow_contDiff
      Ck ε hCk hε hε1 K
  let C0 := (lowCorrectionEnergy + 1) *
    ((Fintype.card RayCharacter : ℝ) + 1) * 6 * C
  have hC0 : 0 < C0 := by
    have hh := lowCorrectionEnergy_nonneg
    dsimp [C0]
    positivity
  refine ⟨degree, C0, Z₀, hC0, hZ₀, ?_⟩
  intro Z t d ell0 shift hZ ht htSmall hd hd1 hell hellcap hshift
    R hR T hT hout hdis J H hH1 hH hprod W hW Y θ σ
  let L := fun i : SelectedSlot J =>
    lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val))
  have hLP (i : SelectedSlot J) :
      lowPeriodPrimeList η S hS (T i.val) ⊆ T i.val :=
    Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) :
      ∀ P ∈ lowPeriodPrimeList η S hS (T i.val), Supported P.val :=
    fun P hP => hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j => Disjoint (L i) (L j)) :=
    lowPrimeIdealList_disjoint _
      (lowPeriodPrimeList_disjoint η S hS _
        (fun i j hij => hdis (fun h => hij (Subtype.ext h))))
  have hparents : ∀ I ∈ lowIdealRows R,
      I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤
        Ck * Z ^ (5 / 6 - t - 2 * d) :=
    fun I hI => ⟨lowIdealRows_nonzero R
      (fun z hz => (hR z hz).1) I hI,
      lowIdealRows_norm_bound R _ (fun z hz => (hR z hz).2) I hI⟩
  have hcard : Fintype.card (SelectedSlot J) ≤ K := by
    simpa only [Fintype.card_coe, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ \ J))
  have hrow (χ : RayCharacter) (u : Oˣ) :
      (∑ I ∈ lowIdealRows R,
        ‖lowActualIdealPolynomial L
          (fun i I => lowSingleSlotWeight η (W i.val)
            (Y i.val) θ (primaryGenerator I))
          (rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (lowReflectionMask η S hS)
            (ConcretePrimeRowBridge.idealGenerator (1 : Id))
            (u.val * ConcretePrimeRowBridge.idealGenerator I))
          (CompletedHeight.normTwistedSource gaussianFixedWindow θ)
          (Z ^ (1 + ell0 + shift))‖ ^ 2) ≤
        C * (1 + ‖θ‖) ^ degree *
          Z ^ ((5 / 6 - t - 2 * d) +
            max 0 ((d - 1 / 6 + 5 * t) / 4) + 507 * ε) := by
    convert he Z t d ell0 shift hZ ht htSmall hd hd1 hell hellcap hshift
      (lowIdealRows R) hparents hcard L H
      hlists (fun i => lowPrimeIdealList_maximal _)
      (fun i P hP => (lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i => lowPrimeIdealList_prime _)
      (fun i P hP => (lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1
      (fun i => lowPrimeIdealList_norm _ _
        (fun P hP => hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase η S hS σ χ)
      (lowReflectionPeriod_actual η S hS σ χ).2
      (lowReflectionPeriod_actual η S hS σ χ).1 u θ
      (fun i P => lowSingleSlotWeight η (W i.val)
        (Y i.val) θ (primaryGenerator P.val))
      (fun i P => low_actual_ideal_weight_bound η (W i.val)
        (hW i.val) (Y i.val) θ P.val) using 1
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy η S hS hbad T hT
    hout hdis J W Y (Z ^ (1 + ell0 + shift)) θ σ R
    (fun z hz => (hR z hz).1)).trans
  have hh := Finset.sum_le_sum
    (fun χ (_ : χ ∈ (Finset.univ : Finset RayCharacter)) =>
      Finset.sum_le_sum
        (fun u (_ : u ∈ (Finset.univ : Finset Oˣ)) => hrow χ u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, low_unit_card] at hm
  simp only [Nat.cast_ofNat, Real.norm_eq_abs] at hm ⊢
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0 ≤ (Fintype.card RayCharacter : ℝ) := Nat.cast_nonneg _
  have hzpos : 0 ≤ Z ^ ((5 / 6 - t - 2 * d) +
      max 0 ((d - 1 / 6 + 5 * t) / 4) + 507 * ε) :=
    Real.rpow_nonneg (le_trans zero_le_one (hZ₀.le.trans hZ)) _
  have htpos : 0 ≤ (1 + |θ|) ^ degree := by positivity
  calc
    _ = (lowCorrectionEnergy * (Fintype.card RayCharacter : ℝ) * 6 * C) *
        (1 + |θ|) ^ degree *
        Z ^ ((5 / 6 - t - 2 * d) +
          max 0 ((d - 1 / 6 + 5 * t) / 4) + 507 * ε) := by ring
    _ ≤ _ := by gcongr <;> linarith

end SevenEighths.ProbePhysical

end

end OAI
