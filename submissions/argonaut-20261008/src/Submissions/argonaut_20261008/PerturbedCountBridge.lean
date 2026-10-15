import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySourceCount

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter

namespace SevenEighths.PerturbedCountBridge

universe uLabel uSlot uOtherLabel uOtherSlot

open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff HeckeDetectorBranchBudget
open SevenEighths.ProbeHighRowFamily
local notation "O" => HeckeFamily.O

/-!
The old balanced count theorem assumes `Δ ≤ 1/8`.  The only genuine uses of that cap
are the plain-capacity comparison and the zero-capacity branch.  The former is valid
for every `Δ ≥ 0`; in the latter, the balanced hypothesis `δ ≤ 5/6` lets us retain the
same `+6ν` loss as long as `Δ ≤ 9/40`.
-/

theorem capacity_loss_wide {q m Δ γ : ℝ} (_hq : 0 ≤ q) (hq' : q ≤ 1 / 2)
    (hm : 1 / 3 - γ ≤ m) (hm' : m ≤ 1 / 2) (hΔ : 0 ≤ Δ) (hγ : 0 ≤ γ) :
    2 * q * (1 - 2 * m) * (2 / 9 - 1 / (9 / 2 + 12 * Δ)) ≤ Δ / 4 + 2 * γ := by
  have hd : 0 < 9 / 2 + 12 * Δ := by linarith
  have hqmul : q * (1 - 2 * m) ≤ (1 / 2) * (1 / 3 + 2 * γ) :=
    mul_le_mul hq' (by linarith) (by linarith) (by norm_num)
  have hn := mul_le_mul_of_nonneg_right hqmul (show 0 ≤ 24 * Δ by positivity)
  have he :
      2 * q * (1 - 2 * m) * (2 / 9 - 1 / (9 / 2 + 12 * Δ)) =
        24 * q * (1 - 2 * m) * Δ / ((9 / 2) * (9 / 2 + 12 * Δ)) := by
    field_simp [ne_of_gt hd]
    ring
  rw [he]
  apply (div_le_iff₀ (show 0 < (9 / 2) * (9 / 2 + 12 * Δ) by positivity)).mpr
  nlinarith [mul_nonneg hΔ hγ, sq_nonneg Δ]

theorem plain_capacity_comparison_wide {δ x Δ t r m γ : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (hΔ : 0 ≤ Δ) (hm : 1 / 3 - γ ≤ m) (hm' : m ≤ 1 / 2)
    (hγ : 0 ≤ γ) (hlength : t - r - γ ≤ m) :
    1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) / (9 / 2 + 12 * Δ) ≤
      HeckeDetectorRowCount.plainExponent δ x t r + Δ / 4 + 4 * γ := by
  have hq : 0 ≤ δ * x := mul_nonneg hδ hx
  have hq' : δ * x ≤ 1 / 2 :=
    (mul_le_mul hδ' hx' hx (by norm_num)).trans_eq (by ring)
  have hloss := capacity_loss_wide hq hq' hm hm' hΔ hγ
  have hc : 0 ≤ δ * (2 - 8 * x / 9) := mul_nonneg hδ (by linarith)
  have hc' : δ * (2 - 8 * x / 9) ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right hδ' (show 0 ≤ 2 - 8 * x / 9 by linarith)
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left (show t - r - m ≤ γ by linarith) hc
  have herror := mul_le_mul_of_nonneg_right hc' hγ
  have hid :
      (1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) * (2 / 9)) -
          HeckeDetectorRowCount.plainExponent δ x t r =
        δ * (2 - 8 * x / 9) * (t - r - m) := by
    unfold HeckeDetectorRowCount.plainExponent
    ring
  have hid' :
      1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) / (9 / 2 + 12 * Δ) =
        (1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) * (2 / 9)) +
          2 * (δ * x) * (1 - 2 * m) * (2 / 9 - 1 / (9 / 2 + 12 * Δ)) := by
    ring
  rw [hid']
  linarith

lemma plain_zero_capacity_wide {δ m Δ ν : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6) (hΔ : 0 ≤ Δ) (hΔ' : Δ ≤ 9 / 40)
    (hν : 0 ≤ ν)
    (hcap : (1 - 2 * m) / (6 * (3 / 4 + 2 * Δ)) ≤ ν) :
    1 - 2 * δ * m ≤ 1 - δ + 6 * ν := by
  have hk0 : 0 < 3 / 4 + 2 * Δ := by linarith
  have hk : 0 ≤ 3 / 4 + 2 * Δ := hk0.le
  have hk' : 3 / 4 + 2 * Δ ≤ 6 / 5 := by linarith
  have hprod : δ * (3 / 4 + 2 * Δ) ≤ 1 := by
    have hh := mul_le_mul hδ' hk' hk (by norm_num : (0 : ℝ) ≤ 5 / 6)
    nlinarith
  have hraw := (div_le_iff₀ (show 0 < 6 * (3 / 4 + 2 * Δ) by positivity)).mp hcap
  have hm : 1 - 2 * m ≤ 6 * (3 / 4 + 2 * Δ) * ν := by
    nlinarith [hraw]
  have hmul := mul_le_mul_of_nonneg_left hm hδ
  have hprodν := mul_le_mul_of_nonneg_right hprod hν
  nlinarith

/-- `count_bound_of_source_branches` with the balanced cap widened from `1/8` to `9/40`. -/
theorem count_bound_of_source_branches_wide
    (B C U δ x Δ t r m ε ν γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (hΔ : 0 ≤ Δ) (hΔ' : Δ ≤ 9 / 40)
    (ht : 1 ≤ t) (ht' : t ≤ 3 / 2) (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hleft : t - r - γ ≤ m) (hright : r ≤ t + γ)
    (hI0 : B ≤ C * U ^ (max 1 ((1 + 5 * r) / 6) - δ * r + ε))
    (hP0 : B ≤ C * U ^ (1 - 2 * δ * m + ε))
    (hI : 23 / 37 ≤ r → r < 1 → ν < (1 - r) / 2 →
      B ≤ C * U ^ (HeckeDetectorRowCount.inverseExponent δ x r + ε))
    (hP : r ≤ HeckeDetectorRowCount.crossing x t → m < 1 / 2 →
      ν < (1 - 2 * m) / (9 / 2 + 12 * Δ) →
      B ≤ C * U ^ (1 - 2 * δ * m -
        2 * (δ * x) * (1 - 2 * m) / (9 / 2 + 12 * Δ) + ε)) :
    B ≤ C * U ^ (max (HeckeDetectorRowCount.shortExponent δ x t)
      (HeckeDetectorRowCount.longExponent δ t) + Δ / 4 + ε + 6 * ν + 5 * γ) := by
  let target := max (HeckeDetectorRowCount.shortExponent δ x t)
    (HeckeDetectorRowCount.longExponent δ t) + Δ / 4 + ε + 6 * ν + 5 * γ
  have hshort : HeckeDetectorRowCount.shortExponent δ x t ≤
      max (HeckeDetectorRowCount.shortExponent δ x t)
        (HeckeDetectorRowCount.longExponent δ t) := le_max_left _ _
  have hlong : HeckeDetectorRowCount.longExponent δ t ≤
      max (HeckeDetectorRowCount.shortExponent δ x t)
        (HeckeDetectorRowCount.longExponent δ t) := le_max_right _ _
  have hbase := HeckeDetectorRowCount.short_ge_base hδ hx hx' ht'
  have hcross := HeckeDetectorRowCount.crossing_bounds hx hx' ht ht'
  have hchoose := HeckeDetectorRowCount.selected_short_bound (t := t) (r := r) hδ hx hx'
  have promote (p : ℝ) (hp : B ≤ C * U ^ p) (hpt : p ≤ target) :
      B ≤ C * U ^ target :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1 ≤ r
  · have hmax : max 1 ((1 + 5 * r) / 6) = (1 + 5 * r) / 6 :=
      max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hl := HeckeDetectorRowCount.long_count_bound hδ' hγ hright
    dsimp [target]
    have hcγ : (5 / 6 - δ) * γ ≤ γ := by nlinarith [mul_nonneg hδ hγ]
    nlinarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  have hmax : max 1 ((1 + 5 * r) / 6) = 1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : HeckeDetectorRowCount.crossing x t ≤ r
  · by_cases hcap : (1 - r) / 2 ≤ ν
    · apply promote _ hI0
      have hz := HeckeDetectorRowCount.inverse_zero_capacity hδ hcap
      have hv : 2 * δ * ν ≤ 6 * ν := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
      dsimp [target]
      linarith
    · apply promote _ (hI (hcross.1.trans hrc) hr1' (lt_of_not_ge hcap))
      have hs := hchoose.2 hrc
      dsimp [target]
      linarith
  have hrc' : r ≤ HeckeDetectorRowCount.crossing x t := (lt_of_not_ge hrc).le
  by_cases hm : 1 / 2 ≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    dsimp [target]
    linarith
  have hm' : m < 1 / 2 := lt_of_not_ge hm
  by_cases hcap : (1 - 2 * m) / (9 / 2 + 12 * Δ) ≤ ν
  · apply promote _ hP0
    have hz := plain_zero_capacity_wide hδ hδ' hΔ hΔ' hν
      (show (1 - 2 * m) / (6 * (3 / 4 + 2 * Δ)) ≤ ν by
        convert hcap using 1 <;> ring)
    dsimp [target]
    linarith
  · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
    have hmm : 1 / 3 - γ ≤ m := by linarith [hcross.2.2.1]
    have hp := plain_capacity_comparison_wide hδ (show δ ≤ 1 by linarith)
      hx hx' hΔ hmm hm'.le hγ hleft
    have hs := hchoose.1 hrc'
    dsimp [target]
    linarith

/-- Fiber count with the widened balanced `Δ` range. -/
theorem count_from_raw_moments_wide
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 →
      0 ≤ ε → ε ≤ 1 / 1000 → 1 ≤ tstar → tstar ≤ 3 / 2 →
      0 ≤ Δ → Δ ≤ 9 / 40 → 0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*}
        (F : HeckeDetectorRawFiber.Fiber M H Label Slot U a ε tstar T allowance i),
      HeckeDetectorRawFiber.Moments F Δ c κ C height εm →
      (F.rows.card : ℝ) ≤ HeckeDetectorRawFiber.fiberConstant C height K₀ *
        U ^ (max (HeckeDetectorRowCount.shortExponent (2 * a - 1) (F.q / (2 * a - 1)) tstar)
          (HeckeDetectorRowCount.longExponent (2 * a - 1) tstar) +
          Δ / 4 + 159 * ε + εm + F.mesh + 7 * ν) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hamp⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      2 εm (by norm_num) hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht'
    hΔ hΔ' hν hC hh hf Label Slot F moments
  let δ := 2 * a - 1
  let x := F.q / δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have ha' : 1 / 2 ≤ a := by linarith
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨hq0, hqδ⟩ := F.mean_bounds ha'
  have hx : 0 ≤ x := div_nonneg hq0 hδ.le
  have hx' : x ≤ 1 / 2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hqx : δ * x = F.q := by dsimp [x]; field_simp
  have hgeom := F.lengths hU
  have hr0 : 0 ≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r ≤ 2 := by linarith [hgeom.2.1]
  have hUp : 0 < U := zero_lt_one.trans hU
  obtain ⟨hconst, hconstP, hconstI, hconstI0⟩ :=
    HeckeDetectorRawFiber.fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q : ℝ) (hC' : C' ≤ HeckeDetectorRawFiber.fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ) ≤ C' * U ^ p) (hpq : p ≤ q) :
      (F.rows.card : ℝ) ≤ HeckeDetectorRawFiber.fiberConstant C height K₀ * U ^ q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
    F.fixed_right hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff
    moments.inverse_raw
  have hI0 : (F.rows.card : ℝ) ≤ HeckeDetectorRawFiber.fiberConstant C height K₀ *
      U ^ (max 1 ((1 + 5 * F.r) / 6) - δ * F.r + commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstI0 hi0
    exact HeckeDetectorBranchBudget.no_slot_inverse_loss F.r δ ε εm F.mesh ν
      hε F.mesh_nonneg hν.le
  have hp0 := F.plain_unmarked_count moments hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ) ≤ HeckeDetectorRawFiber.fiberConstant C height K₀ *
      U ^ (1 - 2 * δ * F.m + commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstP hp0
    exact HeckeDetectorBranchBudget.no_slot_plain_loss F.m δ ε εm F.mesh ν hε
      hgeom.2.2.1 F.mesh_nonneg hν.le
  have hI : 23 / 37 ≤ F.r → F.r < 1 → ν < (1 - F.r) / 2 →
      (F.rows.card : ℝ) ≤ HeckeDetectorRawFiber.fiberConstant C height K₀ *
        U ^ (HeckeDetectorRowCount.inverseExponent δ x F.r + commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz, hz', hcap1, hcap2⟩ :=
      HeckeDetectorBranchBudget.inverse_requested_capacity F.r ν hr hr1 hν hv
    have hb := F.inverse_marked_count moments hU ha' hC hh hf
      ((1 - F.r) / 2 - ν) hz hz' hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := HeckeDetectorBranchBudget.inverse_marked_loss F.r δ x ε εm F.mesh ν
      hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rwa [hqx] at hl
  have hP : F.r ≤ HeckeDetectorRowCount.crossing x tstar → F.m < 1 / 2 →
      ν < (1 - 2 * F.m) / (9 / 2 + 12 * Δ) →
      (F.rows.card : ℝ) ≤ HeckeDetectorRawFiber.fiberConstant C height K₀ *
        U ^ (1 - 2 * δ * F.m - 2 * (δ * x) * (1 - 2 * F.m) /
          (9 / 2 + 12 * Δ) + commonLoss ε εm F.mesh ν) := by
    intro hr hm hv
    obtain ⟨hz, hz', hcap⟩ := HeckeDetectorBranchBudget.plain_requested_capacity
      Δ x tstar F.r F.m ε ν hΔ hx hx' ht ht' hr hgeom.1 (by linarith) hν.le hv
    have hb := F.plain_marked_count moments hU ha' hΔ hC hh hf
      ((1 - 2 * F.m) / (9 / 2 + 12 * Δ) - ν) hz hz' hcap
    apply promote _ _ _ hconstP hb
    have hl := HeckeDetectorBranchBudget.plain_marked_loss F.m δ x Δ ε εm F.mesh ν
      hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    simpa only [hqx] using hl
  have hc' := count_bound_of_source_branches_wide
    (F.rows.card : ℝ) (HeckeDetectorRawFiber.fiberConstant C height K₀) U δ x Δ
    tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le hδcap
    hx hx' hΔ hΔ' ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
  convert hc' using 1
  congr 2
  unfold commonLoss
  ring

/-- Fixed-amplitude batch count with `Δ ≤ 9/40`. -/
theorem fixed_amplitude_count_from_raw_moments_wide
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height q : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 →
      0 ≤ ε → ε ≤ 1 / 1000 → 1 ≤ tstar → tstar ≤ 3 / 2 →
      0 ≤ Δ → Δ ≤ 9 / 40 → 0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : HeckeDetectorBatch.Batch M H Label Slot U a ε tstar T allowance i),
      (∀ u ∈ B.rows,
        HeckeDetectorAmplitudeFirst.rowMean B.slots U ((2 * a - 1) / 2)
          B.binWidth B.widths
          (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow => u.val)
            B.profile B.upper B.widths B.external U) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        HeckeDetectorRawFiber.Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        HeckeDetectorRawFiber.fiberConstant C height K₀ *
        (Fintype.card B.Bin : ℝ) *
        U ^ (max (HeckeDetectorRowCount.shortExponent (2 * a - 1) (q / (2 * a - 1)) tstar)
          (HeckeDetectorRowCount.longExponent (2 * a - 1) tstar) +
          Δ / 4 + 159 * ε + εm + B.mesh + 7 * ν) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ :=
    count_from_raw_moments_wide M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance Δ ν C height q i hU ha hd hε hε' ht ht'
    hΔ hΔ' hν hC hh hf Label Slot _ B hq moments
  have hb := B.card_bound (HeckeDetectorRawFiber.fiberConstant C height K₀)
    (fun _ => max (HeckeDetectorRowCount.shortExponent (2 * a - 1) (q / (2 * a - 1)) tstar)
      (HeckeDetectorRowCount.longExponent (2 * a - 1) tstar) +
      Δ / 4 + 159 * ε + εm + B.mesh + 7 * ν)
    (HeckeDetectorRawFiber.fiberConstant_bounds C height K₀ hC hh hK).1
    (zero_lt_one.trans hU) (by
      intro bin j J K hne
      have hc' := hcount a ε tstar T allowance Δ ν C height i hU ha hd hε hε'
        ht ht' hΔ hΔ' hν hC hh hf (B.fiber bin j J K hne) (moments bin j J K hne)
      rw [HeckeDetectorFixedAmplitudeCount.fiber_mean_eq B q hq bin j J K hne] at hc'
      exact hc')
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hb

/-- Balanced adaptive count at the source level, with the widened cap. -/
theorem balanced_adaptive_count_from_raw_moments_wide
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 →
      0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ Δ → Δ ≤ 9 / 40 →
      0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : HeckeDetectorBatch.Batch M H Label Slot U a ε
          (cutoff (2 * a - 1) q) T allowance i),
      B.rows.Nonempty →
      (∀ u ∈ B.rows,
        HeckeDetectorAmplitudeFirst.rowMean B.slots U ((2 * a - 1) / 2)
          B.binWidth B.widths
          (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow => u.val)
            B.profile B.upper B.widths B.external U) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        HeckeDetectorRawFiber.Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        HeckeDetectorRawFiber.fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (Endpoint.balancedRowCount (2 * a - 1) (1 / 2 - q / (2 * a - 1)) +
          Δ / 4 + 159 * ε + εm + B.mesh + 7 * ν) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ :=
    fixed_amplitude_count_from_raw_moments_wide M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ ν C height q i hU ha hd hε hε' hΔ hΔ' hν hC hh hf
    Label Slot _ B hne hq hmom
  have hδ : 0 < 2 * a - 1 := by linarith
  have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
  have hx : 0 ≤ q / (2 * a - 1) := div_nonneg hqb.1 hδ.le
  have hx' : q / (2 * a - 1) ≤ 1 / 2 :=
    (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := HeckeDetectorAdaptiveCutoff.cutoff_bounds (2 * a - 1) q hδ.le
  have hc' := hcount a ε (cutoff (2 * a - 1) q) T allowance Δ ν C height q i
    hU ha hd hε hε' ht.1 ht.2 hΔ hΔ' hν hC hh hf B hq hmom
  have he :
      max (HeckeDetectorRowCount.shortExponent (2 * a - 1) (q / (2 * a - 1))
        (cutoff (2 * a - 1) q))
        (HeckeDetectorRowCount.longExponent (2 * a - 1) (cutoff (2 * a - 1) q)) =
      Endpoint.balancedRowCount (2 * a - 1) (1 / 2 - q / (2 * a - 1)) := by
    rw [HeckeDetectorAdaptiveCutoff.cutoff_eq_balanced (2 * a - 1) q hδ hd hqb.1 hqb.2]
    exact HeckeDetectorRowCount.balanced_count_identity hδ.le hd hx hx'
  rw [he] at hc'
  exact hc'

/-- Count-parameter package matching `CountParameters`, but with balanced cap `9/40`. -/
structure WideCountParameters (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  cB : ℝ
  kB : ℝ
  cH : ℝ
  kH : ℝ
  cB_pos : 0 < cB
  cB_one : cB ≤ 1
  kB_pos : 0 < kB
  cH_pos : 0 < cH
  cH_one : cH ≤ 1
  kH_pos : 0 < kH
  balanced : ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 →
      0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ Δ → Δ ≤ 9 / 40 →
      0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : HeckeDetectorBatch.Batch M H Label Slot U a ε
          (cutoff (2 * a - 1) q) T allowance i),
      B.rows.Nonempty →
      (∀ u ∈ B.rows,
        HeckeDetectorAmplitudeFirst.rowMean B.slots U ((2 * a - 1) / 2)
          B.binWidth B.widths
          (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow => u.val)
            B.profile B.upper B.widths B.external U) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        HeckeDetectorRawFiber.Moments (B.fiber bin j J K hne) Δ cB kB C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        HeckeDetectorRawFiber.fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (Endpoint.balancedRowCount (2 * a - 1) (1 / 2 - q / (2 * a - 1)) +
          Δ / 4 + 159 * ε + εm + B.mesh + 7 * ν)
  high : ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1 < U → 5 / 6 < 2 * a - 1 → a ≤ 1 →
      0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : HeckeDetectorBatch.Batch M H Label Slot U a ε
          (cutoff (2 * a - 1) q) T allowance i),
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        HeckeDetectorRawFiber.Moments (B.fiber bin j J K hne) Δ cH kH C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        HeckeDetectorRawFiber.fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (1 - (2 * a - 1) + 78 * ε + εm)

theorem exists_wide_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    Nonempty (WideCountParameters M H εm) := by
  obtain ⟨cB, kB, KB, hcB, hcB1, hkB, hKB, hbalanced⟩ :=
    balanced_adaptive_count_from_raw_moments_wide M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨cH, kH, KH, hcH, hcH1, hkH, hKH, hhigh⟩ :=
    SevenEighths.ProbeHighRowFamily.high_adaptive_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨cB, kB, cH, kH, hcB, hcB1, hkB, hcH, hcH1, hkH,
    ⟨KB, hKB, hbalanced⟩, ⟨KH, hKH, hhigh⟩⟩⟩

/-- Source-level balanced count using `WideCountParameters`. -/
theorem balanced_source_count_from_raw_moments_wide
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (_hH : RayOrthogonality.globalUnits M ≤ H) (_S : Finset (Ideal O))
    (φ : ℝ → ℝ) (_hφ : ContDiff ℝ ∞ φ) (_hφc : HasCompactSupport φ)
    (_hφp : tsupport φ ⊆ Ioi 0) (_hφ0 : ∀ y, 0 ≤ φ y) (_hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (_ha₀ : 0 < a₀) (_hab₀ : a₀ ≤ b₀) (_hB₀ : 0 < B₀)
    (_hφs : Function.support φ ⊆ Ioo a₀ b₀) (_hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (_hεm : 0 < εm) (Label : Type uLabel) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth)
    (counts : WideCountParameters.{uLabel, uSlot, uOtherLabel, uOtherSlot} M H εm) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε Δ ν C q : ℝ) (i : ℕ), i ≤ n → 51 / 100 < a →
      2 * a - 1 ≤ 5 / 6 → a ≤ 1 → 0 ≤ ε → ε ≤ 1 / 1000 →
      0 ≤ Δ → Δ ≤ 9 / 40 → 0 < ν → 0 ≤ C →
      ∀ {Slot : Type uSlot}
        (B : HeckeDetectorBatch.Batch M H Label Slot (Z ^ d) a ε
          (cutoff (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth → B.rows.Nonempty →
      (∀ u ∈ B.rows,
        HeckeDetectorAmplitudeFirst.rowMean B.slots (Z ^ d) ((2 * a - 1) / 2)
          B.binWidth B.widths
          (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow => u.val)
            B.profile B.upper B.widths B.external (Z ^ d)) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        HeckeDetectorRawFiber.Moments (B.fiber bin j J K hne) Δ
          counts.cB counts.kB (C * Z ^ momentCost) (Z ^ heightCost) εm) →
      (B.rows.card : ℝ) ≤ K * C * Z ^ (logCost + heightCost + momentCost) *
        (Z ^ d) ^ (Endpoint.balancedRowCount (2 * a - 1)
          (1 / 2 - q / (2 * a - 1)) + Δ / 4 + 159 * ε + εm + B.mesh + 7 * ν) := by
  obtain ⟨K₀, hK₀, hcount⟩ := counts.balanced
  obtain ⟨K, hK, hpref⟩ := SevenEighths.ProbeHighRowFamily.source_count_prefactor_eventually
    (Label := Label) N dmin dmax logCost heightCost momentCost binWidth K₀
    hdmin hdmax hl (by linarith) hb
  refine ⟨K, hK, ?_⟩
  filter_upwards [SevenEighths.ProbeHighRowFamily.eventually_all_rpow_ge hcount dmin hdmin,
    hpref, SevenEighths.ProbeHighRowFamily.source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    SevenEighths.ProbeHighRowFamily.eventually_all_rpow_ge (eventually_gt_atTop (1 : ℝ)) dmin hdmin,
    eventually_ge_atTop (1 : ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ ν C q i hi ha haδ ha' hε hε' hΔ hΔ' hν hC Slot B
    hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) Δ ν
    (C * Z ^ momentCost) (Z ^ heightCost) q i (hU d hd) ha haδ hε hε' hΔ hΔ'
    hν (by positivity) (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2 * a - 1) q) (Z ^ τ)
      ((Z ^ d) ^ (τ / (2 * dmax))) i hC ha' B hslots hbin)
    (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

/-- Source-level high count; no `Δ` cap is needed in the high branch. -/
theorem high_source_count_from_raw_moments_wide
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (_hH : RayOrthogonality.globalUnits M ≤ H) (_S : Finset (Ideal O))
    (φ : ℝ → ℝ) (_hφ : ContDiff ℝ ∞ φ) (_hφc : HasCompactSupport φ)
    (_hφp : tsupport φ ⊆ Ioi 0) (_hφ0 : ∀ y, 0 ≤ φ y) (_hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (_ha₀ : 0 < a₀) (_hab₀ : a₀ ≤ b₀) (_hB₀ : 0 < B₀)
    (_hφs : Function.support φ ⊆ Ioo a₀ b₀) (_hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (_hεm : 0 < εm) (Label : Type uLabel) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth)
    (counts : WideCountParameters.{uOtherLabel, uOtherSlot, uLabel, uSlot} M H εm) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε Δ C q : ℝ) (i : ℕ), i ≤ n → 5 / 6 < 2 * a - 1 →
      a ≤ 1 → 0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ C →
      ∀ {Slot : Type uSlot}
        (B : HeckeDetectorBatch.Batch M H Label Slot (Z ^ d) a ε
          (cutoff (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        HeckeDetectorRawFiber.Moments (B.fiber bin j J K hne) Δ
          counts.cH counts.kH (C * Z ^ momentCost) (Z ^ heightCost) εm) →
      (B.rows.card : ℝ) ≤ K * C * Z ^ (logCost + heightCost + momentCost) *
        (Z ^ d) ^ (1 - (2 * a - 1) + 78 * ε + εm) := by
  obtain ⟨K₀, hK₀, hcount⟩ := counts.high
  obtain ⟨K, hK, hpref⟩ := SevenEighths.ProbeHighRowFamily.source_count_prefactor_eventually
    (Label := Label) N dmin dmax logCost heightCost momentCost binWidth K₀
    hdmin hdmax hl (by linarith) hb
  refine ⟨K, hK, ?_⟩
  filter_upwards [SevenEighths.ProbeHighRowFamily.eventually_all_rpow_ge hcount dmin hdmin,
    hpref, SevenEighths.ProbeHighRowFamily.source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    SevenEighths.ProbeHighRowFamily.eventually_all_rpow_ge (eventually_gt_atTop (1 : ℝ)) dmin hdmin,
    eventually_ge_atTop (1 : ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ C q i hi ha ha' hε hε' hC Slot B hslots hbin hmom
  have hcard := hcount d hd a ε (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) Δ
    (C * Z ^ momentCost) (Z ^ heightCost) q i (hU d hd) ha ha' hε hε'
    (by positivity) (by positivity) (hfreq d hd' i hi) B hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2 * a - 1) q) (Z ^ τ)
      ((Z ^ d) ^ (τ / (2 * dmax))) i hC ha' B hslots hbin)
    (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

/-- Adaptive source count with balanced `Δ ≤ 9/40` and the unchanged high branch. -/
theorem adaptive_source_count_from_raw_moments_wide
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) (Label : Type uLabel) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth)
    (counts : WideCountParameters.{uLabel, uSlot, uLabel, uSlot} M H εm) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε Δ ν C q : ℝ) (i : ℕ), i ≤ n → 51 / 100 < a → a ≤ 1 →
      0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ Δ → Δ ≤ 9 / 40 → 0 < ν → 0 ≤ C →
      ∀ {Slot : Type uSlot}
        (B : HeckeDetectorBatch.Batch M H Label Slot (Z ^ d) a ε
          (cutoff (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth → B.rows.Nonempty →
      (∀ u ∈ B.rows,
        HeckeDetectorAmplitudeFirst.rowMean B.slots (Z ^ d) ((2 * a - 1) / 2)
          B.binWidth B.widths
          (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow => u.val)
            B.profile B.upper B.widths B.external (Z ^ d)) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        HeckeDetectorRawFiber.Moments (B.fiber bin j J K hne) Δ
          (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
          (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
          (C * Z ^ momentCost) (Z ^ heightCost) εm) →
      (B.rows.card : ℝ) ≤ K * C * Z ^ (logCost + heightCost + momentCost) *
        (Z ^ d) ^ (SevenEighths.ProbeHighRowFamily.adaptiveRowExponent
          (2 * a - 1) q Δ ε εm B.mesh ν) := by
  obtain ⟨KB, hKB, hbalanced⟩ := balanced_source_count_from_raw_moments_wide
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    εm hεm Label N n dmin dmax τ logCost heightCost momentCost binWidth
    hdmin hdmax hτ hl hh hb counts
  obtain ⟨KH, hKH, hhigh⟩ := high_source_count_from_raw_moments_wide
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    εm hεm Label N n dmin dmax τ logCost heightCost momentCost binWidth
    hdmin hdmax hτ hl hh hb counts
  refine ⟨max KB KH, lt_of_lt_of_le hKB (le_max_left _ _), ?_⟩
  filter_upwards [hbalanced, hhigh, eventually_ge_atTop (1 : ℝ)] with Z hb hh hZ
  intro d hd hd' a ε Δ ν C q i hi ha ha' hε hε' hΔ hΔ' hν hC Slot B
    hslots hbin hne hq hmom
  by_cases hδ : 2 * a - 1 ≤ 5 / 6
  · simp only [if_pos hδ] at hmom
    have hc := hb d hd hd' a ε Δ ν C q i hi ha hδ ha' hε hε' hΔ hΔ' hν hC
      B hslots hbin hne hq hmom
    simp only [SevenEighths.ProbeHighRowFamily.adaptiveRowExponent, if_pos hδ]
    exact hc.trans (by gcongr; exact le_max_left _ _)
  · simp only [if_neg hδ] at hmom
    have hc := hh d hd hd' a ε Δ C q i hi (lt_of_not_ge hδ) ha' hε hε' hC
      B hslots hbin hmom
    simp only [SevenEighths.ProbeHighRowFamily.adaptiveRowExponent, if_neg hδ]
    exact hc.trans (by gcongr; exact le_max_right _ _)

end SevenEighths.PerturbedCountBridge
end
end OAI
