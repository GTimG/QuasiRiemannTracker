/-
Affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 at tracker revision 2c3df3b.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B004
import Submissions.local44_20261013.Bundles.B008
import Submissions.local44_20261013.Bundles.B009
import Submissions.affine_local_20261013.Bundles.B013
import Submissions.affine_local_20261013.Bundles.B014
import Submissions.affine_local_20261013.Bundles.B020
import Submissions.affine_local_20261013.Bundles.B021
import Submissions.affine_local_20261013.Bundles.B022
import Submissions.affine_local_20261013.Bundles.B023
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflectionError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.FirstContinuation

/- BEGIN ORIGINAL MODULE Cycle25.Energy.LiveClippingDefect ; sha256 3d277fc28423b10178632a0595ba550f5579485c2a832d48f5619cc19f168b7d -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/LiveClippingDefect.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/








namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.Cycle25CenteredMomentEnergyLiveClippingDefect
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentRetainedEnergy
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_support_witness (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X : ℝ) (h : rowTwistedSum η m A z W t X ≠ 0) :
    ∃ I : Ideal O, I ≠ 0 ∧ W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold rowTwistedSum
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · subst I
        rw [idealCoeff_zero, zero_mul, zero_mul, zero_mul]
      · rw [hn I hI, mul_zero]
    _ = 0 := tsum_zero

theorem rowTwistedSum_support_scale (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X b : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b)
    (h : rowTwistedSum η m A z W t X ≠ 0) : 1 ≤ b * X := by
  obtain ⟨I, hI, hW⟩ := rowTwistedSum_support_witness η m A z W t X h
  have hn : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hn.trans ((div_le_iff₀ hX).mp (hs hW))

variable {ι : Type*} [Fintype ι]

theorem positiveSlotRow_support_scales (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (h : positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  have hp := left_ne_zero_of_mul (right_ne_zero_of_mul h)
  exact ⟨rowTwistedSum_support_scale η m A z W₁ t X₁ b hX₁ hs₁
      (left_ne_zero_of_mul hp),
    rowTwistedSum_support_scale η m A z W₂ t X₂ b hX₂ hs₂
      (right_ne_zero_of_mul hp)⟩

theorem positiveSlotRow_profiles_scales (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (h : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  exact positiveSlotRow_support_scales η m A z _ _ S β P t X₁ X₂ b hX₁ hX₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) h

theorem length_le_raw_add_endpoint (Z X b : ℝ) (hZ : 1 < Z) (hX : 0 < X)
    (hs : 1 ≤ b * X) : length Z X ≤ Real.logb Z X + Real.logb Z (max 1 b) := by
  have hB : 0 < max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  have hc : max 1 X ≤ max 1 b * X := by
    apply max_le
    · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) b) hX.le
  have hh := Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (le_max_left (1 : ℝ) X)) hc
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  simpa [length, add_comm] using hh

theorem total_clipping_defect (Z X₁ X₂ b : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hs₁ : 1 ≤ b * X₁) (hs₂ : 1 ≤ b * X₂) :
    length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
      2 * Real.logb Z (max 1 b) := by
  have h1 := length_le_raw_add_endpoint Z X₁ b hZ hX₁ hs₁
  have h2 := length_le_raw_add_endpoint Z X₂ b hZ hX₂ hs₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  linarith

theorem endpoint_threshold (b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      2 * Real.logb Z (max 1 b) ≤ δ := by
  let Z₀ := Real.exp (1 + 2 * Real.log (max 1 b) / δ)
  have hb : 0 ≤ Real.log (max 1 b) := Real.log_nonneg (le_max_left _ _)
  have he : 0 < 1 + 2 * Real.log (max 1 b) / δ := by positivity
  have hZ₀ : 1 < Z₀ := Real.one_lt_exp_iff.mpr he
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ
  have hZ : 1 < Z := hZ₀.trans_le hZZ
  have hlog := Real.log_le_log (Real.exp_pos _) hZZ
  rw [Real.log_exp] at hlog
  have hbound : 2 * Real.log (max 1 b) ≤ δ * Real.log Z := by
    have hh : 2 * Real.log (max 1 b) / δ ≤ Real.log Z := by linarith
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  rw [Real.logb, ← mul_div_assoc]
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr hbound

theorem profiles_uniform_defect (a b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ (η : Character) (m A z : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
        positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0 →
        length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ δ := by
  obtain ⟨Z₀, hZ₀, hh⟩ := endpoint_threshold b δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  exact (total_clipping_defect Z X₁ X₂ b (hZ₀.trans_le hZZ) hX₁ hX₂ h1 h2).trans (hh Z hZZ)

theorem total_clipping_defect_nonneg (Z X₁ X₂ : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) := by
  have h1 := Real.logb_le_logb_of_le hZ hX₁ (le_max_right (1 : ℝ) X₁)
  have h2 := Real.logb_le_logb_of_le hZ hX₂ (le_max_right (1 : ℝ) X₂)
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  dsimp only [length]
  linarith

theorem positiveSlotRow_zero_or_defect (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ Z : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases hrow : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
    exact Or.inr ⟨total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂,
      total_clipping_defect Z X₁ X₂ b hZ hX₁ hX₂ h1 h2⟩

theorem energy_support_witness (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : CenteredMomentInductionEnergy.energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≠ 0) :
    ∃ z : O, keep z ∧ positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold CenteredMomentInductionEnergy.energy
  calc
    _ = ∑' _z : O, (0 : ℝ) := by
      apply tsum_congr
      intro z
      by_cases hk : keep z
      · simp only [ite_eq_left hk, hn z hk, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      · simp only [ite_eq_right hk]
    _ = 0 := tsum_zero

theorem energy_zero_or_defect (η : Character) (m A : O) (t : ℝ)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ Z : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
        S β P X₁ X₂ keep Φ K = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases h : CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
      S β P X₁ X₂ keep Φ K = 0
  · exact Or.inl h
  · obtain ⟨z, _, hz⟩ := energy_support_witness η m A t _ _ S β P X₁ X₂ keep Φ K h
    exact Or.inr ((positiveSlotRow_zero_or_defect η m A z p S β P t X₁ X₂ Z hZ hX₁ hX₂).resolve_left hz)

theorem raw_gates_of_defect (Z M X₁ X₂ ell κ e : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hdefect : length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ e)
    (hlarge : 5*M/6 ≤ length Z X₁ + length Z X₂ + ell)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*ell ≤ M) :
    5*M/6-e ≤ Real.logb Z (X₁ * X₂)+ell ∧
      Real.logb Z (X₁ * X₂)+ell+(6*κ-1)*ell ≤ M := by
  have hnonneg := total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂
  constructor <;> nlinarith

theorem robust_slot_budgets (M total ell kappa defect : ℝ)
    (hell : 0 ≤ ell) (hk : 7/10 ≤ kappa)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M) :
    ell ≤ 5*M/96+5*defect/16 ∧ (6*kappa-1)*ell ≤ M/6+defect := by
  have hkell : 16/5*ell ≤ (6*kappa-1)*ell :=
    mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem robust_defect_le_width (M xi defect : ℝ) (hM : 0 ≤ M) (hxi : 0 ≤ xi)
    (hreserve : xi+13*defect/8 ≤ M/16) : defect ≤ M := by
  linarith

theorem robust_balanced_long_nonneg (M total ell kappa xi defect : ℝ)
    (hM : 0 ≤ M) (hell : 0 ≤ ell) (hk : 7/10 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (hreserve : xi+13*defect/8 ≤ M/16) :
    17*M/32-21*defect/16 ≤ total-M/4 ∧ 0 ≤ total-M/4 := by
  obtain ⟨he, hb⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  constructor <;> linarith

theorem robust_reflected_low (M short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (_hs : 0 ≤ short) (hsM : short ≤ M/4)
    (_hell : 0 ≤ ell) (_hz : 0 ≤ z) (hze : z ≤ ell) (hk : 7/10 ≤ kappa)
    (he : ell ≤ 5*M/96+5*defect/16)
    (hbudget : (6*kappa-1)*ell ≤ M/6+defect)
    (hxi : 0 ≤ xi) (hdefect : 0 ≤ defect) (hdefectM : defect ≤ M)
    (hhigh : 5*M/6 < short+max 0 along+z)
    (href : reflected ≤ max 0 (M-along+xi)) :
    0 < along ∧ reflected+short+z ≤ 37*M/48+xi+5*defect/8 ∧
      reflected+short+6*kappa*z ≤ 15*M/16+xi+13*defect/8 := by
  have haz : 0 < along := by
    by_contra hn
    have ha : along ≤ 0 := le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget : (6*kappa-1)*z ≤ M/6+defect :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap : z ≤ 5*M/96+5*defect/16 := hze.trans he
  refine ⟨haz, ?_⟩
  by_cases hr : 0 ≤ M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem robust_reflected_low_admissible (M xi defect short reflected z kappa : ℝ)
    (hd : 0 ≤ defect) (hreserve : xi+13*defect/8 ≤ M/16)
    (ht : reflected+short+z ≤ 37*M/48+xi+5*defect/8)
    (hc : reflected+short+6*kappa*z ≤ 15*M/16+xi+13*defect/8) :
    reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*kappa*z ≤ M := by
  constructor <;> linarith

theorem robust_deleted_cases (M total short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (hs : 0 ≤ short) (hsM : short ≤ M/4)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hk : 7/10 ≤ kappa)
    (hxi : 0 ≤ xi) (hd : 0 ≤ defect)
    (hreserve : xi+13*defect/8 ≤ M/16)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (halong : max 0 along ≤ total-M/4)
    (href : reflected ≤ max 0 (M-along+xi)) :
    (short+max 0 along+z ≤ 5*M/6 ∧ short+max 0 along+6*kappa*z ≤ M) ∨
    (0 < along ∧ reflected+short+z ≤ 5*M/6 ∧
      reflected+short+6*kappa*z ≤ M) := by
  obtain ⟨he,hbudget⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  by_cases hlo : short+max 0 along+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hzcap := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*kappa)
    nlinarith
  · obtain ⟨hapos, ht, hc⟩ := robust_reflected_low M short along ell z kappa xi defect reflected
      hM hs hsM hell hz hze hk he hbudget hxi hd
      (robust_defect_le_width M xi defect hM hxi hreserve) (lt_of_not_ge hlo) href
    exact Or.inr ⟨hapos, robust_reflected_low_admissible M xi defect short reflected z kappa hd hreserve ht hc⟩

theorem robust_fixed_slack (M₀ : ℝ) (hM₀ : 0 < M₀) :
    0 < M₀/56 ∧ ∀M : ℝ, M₀ ≤ M →
      M₀/56+13*(M₀/56)/8 ≤ M/16 := by
  constructor
  · positivity
  · intro M hM
    linarith

open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDeletionBudget
open Cycle25CenteredMomentEnergyReferenceDeletionCapacity

theorem robust_deleted_reference_cases (Z M X₁ X₂ ell z κ ξ e reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 7/10 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+13*e/8 ≤ M/16)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I)
    (href : reflected ≤ max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+ξ)) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let long := length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+long+z ≤ 5*M/6 ∧ short+long+6*κ*z ≤ M) ∨
    (0 < Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ∧
      reflected+short+z ≤ 37*M/48+ξ+5*e/8 ∧
      reflected+short+6*κ*z ≤ 15*M/16+ξ+13*e/8) := by
  dsimp only
  have hb := robust_balanced_long_nonneg M (Real.logb Z (X₁*X₂)) ell κ ξ e
    hM hell hκ hξ hlarge hcap hreserve
  have hpos := comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hlog : Real.logb Z (comparisonSecond Z M X₁ X₂) = Real.logb Z (X₁*X₂)-M/4 := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hY : 1 ≤ comparisonSecond Z M X₁ X₂ := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hn₂ := product_norm_ge_one D₂ hD₂
  have hlongpos := div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort := deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0 := length_nonneg Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ)) hZ
  have hlong : length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ≤
      Real.logb Z (X₁*X₂)-M/4 := by
    rw [← hlog]
    exact Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (le_max_left 1 _)) (max_le hY (div_le_self hpos.2.le hn₂))
  by_cases hlo : length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ))+
      length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hkc := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*κ)
    nlinarith
  · apply Or.inr
    obtain ⟨hellbound, hslot⟩ := robust_slot_budgets M (Real.logb Z (X₁*X₂)) ell κ e
      hell hκ hlarge hcap
    apply robust_reflected_low M _ _ ell z κ ξ e reflected hM hshort0 hshort hell hz hze hκ
      hellbound hslot hξ he (robust_defect_le_width M ξ e hM hξ hreserve) _ href
    rw [← Cycle25CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

theorem robust_deleted_reference_window (Z M X₁ X₂ ell z κ ξ e : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 7/10 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+13*e/8 ≤ M/16)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
    (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
      length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
      length Z (Real.exp x)+short+6*κ*z ≤ M) := by
  dsimp only
  let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))
  rcases robust_deleted_reference_cases Z M X₁ X₂ ell z κ ξ e (max 0 (M-along+ξ))
    hZ hM hX₁ hX₂ hell hz hze hκ hξ he hreserve hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h.1, ?_⟩
    intro x hx
    have hh := Cycle25CenteredMomentEnergyReferenceLowWindow.reflection_window_length Z
      (max 0 (M-along+ξ)) x hZ (le_max_left _ _) hx
    have hb := robust_reflected_low_admissible M ξ e _ (max 0 (M-along+ξ)) z κ
      he hreserve h.2.1 h.2.2
    constructor <;> linarith [hh.1]

theorem live_profiles_reference_window (a b M₀ : ℝ) (hM₀ : 0 < M₀) :
    ∃ e ξ Z₀ : ℝ, 0 < e ∧ 0 < ξ ∧ 1 < Z₀ ∧
      ∀ (Z M : ℝ), Z₀ ≤ Z → M₀ ≤ M →
      ∀ (η : Character) (m A u : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ ell z κ : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ ell →
        0 ≤ z → z ≤ ell → 7/10 ≤ κ →
        5*M/6 ≤ length Z X₁+length Z X₂+ell →
        length Z X₁+length Z X₂+6*κ*ell ≤ M →
      ∀ (D₁ D₂ : Finset (Ideal O)), (∀ I ∈ D₁, Prime I) → (∀ I ∈ D₂, Prime I) →
      positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
      (let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
       let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
       (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
        short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
       (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
         length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
         length Z (Real.exp x)+short+6*κ*z ≤ M)) := by
  have he : 0 < M₀/56 := by positivity
  obtain ⟨Z₀, hZ₀, hdefect⟩ := profiles_uniform_defect (ι := ι) a b (M₀/56) he
  refine ⟨M₀/56, M₀/56, Z₀, he, he, hZ₀, ?_⟩
  intro Z M hZZ hMM η m A u p S β P t X₁ X₂ ell z κ hX₁ hX₂ hell hz hze hκ hlarge hcap D₁ D₂ hD₁ hD₂
  by_cases hrow : positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · apply Or.inr
    have hZ := hZ₀.trans_le hZZ
    obtain ⟨hl, hc⟩ := raw_gates_of_defect Z M X₁ X₂ ell κ (M₀/56) hZ hX₁ hX₂
      (hdefect Z hZZ η m A u p S β P t X₁ X₂ hX₁ hX₂ hrow) hlarge hcap
    exact robust_deleted_reference_window Z M X₁ X₂ ell z κ (M₀/56) (M₀/56)
      hZ (hM₀.le.trans hMM) hX₁ hX₂ hell hz hze hκ he.le he.le
      ((robust_fixed_slack M₀ hM₀).2 M hMM) hl hc D₁ D₂ hD₁ hD₂

end SevenEighths.Cycle25CenteredMomentEnergyLiveClippingDefect

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.LiveClippingDefect -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceLowDeletedGeometry ; sha256 8178113917e128aeec9d20f1c9ed8ddcd1c0880923c155c9d37bb1c814de35ff -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceLowDeletedGeometry.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/






namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceLowDeletedGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState Cycle25CenteredMomentEnergyReferenceDivisors
open Cycle25CenteredMomentEnergyReferenceLowWindow
local notation "O"=> HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(hB:0≤ Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤ Mcap)(hL:Mcap+Bmask+xi≤ L)
    (hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hκ:7/10≤κ)(hxi:0≤ xi)(hxiM:xi≤ s.width/16)
    (hlarge:5*s.width/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤ L ∧ along≤ L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤ L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤ s.width)):=by
  dsimp only
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hd:=balanced_divisor_range s hZ Mcap X₁ X₂ ell κ hwidth
    hX₁ hX₂ hell hκ hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hd
  have hn₁:=divisor_norm s D₁ hD₁
  have hn₂:=divisor_norm s D₂ hD₂
  have hl₁:=Real.logb_nonneg hZ hn₁.1
  have hl₂:=Real.logb_nonneg hZ hn₂.1
  have hMcap:0≤ Mcap:=s.width_nonneg.trans hwidth
  have hLc:0≤ L:=by linarith
  refine ⟨hd.2.2.2.1,hd.2.2.2.2,by linarith,by linarith [s.width_nonneg],?_,
    hd.2.2.1,?_,?_⟩
  · linarith [hg.2.2.2.2]
  · exact max_le hLc (by linarith [hd.2.1])
  · have hp₁:∀I∈D₁,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₁ hi)
    have hp₂:∀I∈D₂,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₂ hi)
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ)
    have halong:Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ))=along:=by
      rw [←hd.2.2.2.2]
      exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
    rcases Cycle25CenteredMomentEnergyReferenceLowBranchGeometry.deleted_reference_cases
      Z s.width X₁ X₂ ell z κ xi (max 0 (s.width-along+xi)) hZ s.width_nonneg
      hX₁ hX₂ hell hz hze hκ hxi hlarge hcap D₁ D₂ hp₁ hp₂
      (by rw [halong]) with hc|hc
    · apply Or.inl
      simpa only [hd.2.2.2.1,hd.2.2.2.2] using hc
    · apply Or.inr
      have hh:=Cycle25CenteredMomentEnergyReferenceLowBranchGeometry.reflected_low_admissible
        s.width xi _ (max 0 (s.width-along+xi)) z κ hxiM hc.2.1 hc.2.2
      simpa only [hd.2.2.2.1] using hh

end SevenEighths.Cycle25CenteredMomentEnergyReferenceLowDeletedGeometry

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceLowDeletedGeometry -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.FullWBound ; sha256 3ada4002305fd7ca24c61c2e426de762d6b1b5a8c6f8ea2fd48f67f58cb630ad -/
section


/-! Convert the actual w-integrated numerator estimate into a full physical cell bound. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 400000

theorem finiteFullW_uniform_norm_bound (W0 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0< a0) (hW0 : Function.support W0⊆Icc a0 b0) :
    ∃C : ℝ,0< C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι],
      ∀(e a B H : ℝ) (i : ℕ),0< e→e<1/1000→(51/100:ℝ)≤ a→a≤1→2< B→H≤(3*i+2:ℕ)*B→
      ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
      FirstTail (4*e) S→∀(η : Character) (R : Finset FreeRow),(∀u∈R,u.val≠1)→
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)< a+2*e)→
      ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ),
      0< a1→Function.support W1⊆Icc a1 b1→∀X Y Z A : ℝ,0< X→0< Y→0< Z→0≤ A→
      (∀q∈szRectangle H,‖integratedDyadValue S hS hmax η R T hT W Yp W1 Y
        (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)‖≤ A)→
      ‖finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=> a) (fun _=> H)‖≤
        C*X^(1/2-17/50:ℝ)*Z^(a+16*e+17/50-1)*A := by
  obtain ⟨C,hC,hprofile⟩ := sourceSZ_uniform_integral_bound W0 a0 b0 ha0 hW0
    (51/100) 2 (17/50) (17/50) (by norm_num) 0
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨(‖c‖+1)*C,by positivity,?_⟩
  intro K ι _ e a B H i he he' ha haTop hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp W1
    a1 b1 ha1 hW1 X Y Z A hX hY hZ hA hbound
  let G (q : ℝ×ℝ) := integratedDyadValue S hS hmax η R T hT W Yp W1 Y
    (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
  have hh := finiteFullW_reconstruction e a B H i he he' ha haTop hB hH S hS hmax hfirst
    η R hR T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  dsimp only at hh
  have hp := hprofile (a+16*e) ⟨by linarith,by linarith⟩ (17/50) ⟨le_rfl,le_rfl⟩
    X Z hX hZ H A hA G
  simp only [ofReal_div,ofReal_ofNat,pow_zero,mul_one] at hp
  have hb := hp hh.1 hbound
  rw [hh.2,norm_mul]
  change ‖c‖*‖∫q in szRectangle H,sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I)
      ((17/50:ℂ)+q.2*I)*G q ∂(volume.prod volume)‖≤_
  calc
    _ ≤ ‖c‖*(C*X^(1/2-17/50:ℝ)*Z^(a+16*e+17/50-1)*A) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ (‖c‖+1)*(C*X^(1/2-17/50:ℝ)*Z^(a+16*e+17/50-1)*A) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = _ := by ring

end Cycle25.Weighted.FullWContour
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.FullWBound -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorRamifiedProduct ; sha256 31a90bb781eb59b6e6fd3f9158b12e6566f0407478bbfc321ec67e415576c8a0 -/
section



/-! Finite coefficient expansion and subpower mass of the actual ramified product. -/
noncomputable section
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def actualRamifiedCoefficients (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) : QuadraticCoefficients :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedCorrectionCoefficients p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x z (multiplicity p u.val)

theorem actual_ramified_expansion (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z =
      (actualRamifiedCoefficients η u P hs x z).eval ((P.val.absNorm : ℂ) ^ (-w)) := by
  dsimp only [ramifiedCorrection, actualRamifiedCoefficients]
  erw [ramified_correction_expansion]
  simp only [span_primaryGenerator_of_supported P.val hs]

theorem actual_ramified_coefficient_mass (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ) ≤ P.val.absNorm) (x z : ℂ) (sigma : ℝ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + sigma) :
    (actualRamifiedCoefficients η u P hs x z).mass ((P.val.absNorm : ℝ) ^ (-sigma)) ≤ 579 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p} = P.val := span_primaryGenerator_of_supported P.val hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hh := ramified_correction_coefficient_mass p hp hg.1 hg.2
    (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x z sigma
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) (actualACube_norm_le η p)
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp))
    hx hsigma hz hxw (multiplicity p u.val) (multiplicity_lt_six u p hp)
  change (ramifiedCorrectionCoefficients p hp hg.1 (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp)))
    x z (multiplicity p u.val)).mass _ ≤ _
  simpa only [hspan] using hh

def ramifiedCoefficientVector (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (P : ramifiedPrimes S u) : Fin 3 → ℂ :=
  (actualRamifiedCoefficients η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x z).vector

def ramifiedTupleCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (j : ramifiedPrimes S u → Fin 3) : ℂ :=
  ∏ P, ramifiedCoefficientVector S hS η u x z P (j P)

def ramifiedTupleScale (S : Finset (Ideal O)) (u : FreeRow)
    (j : ramifiedPrimes S u → Fin 3) : ℝ≥0 := ∏ P, primeScale P.val ^ (j P).val

theorem ramified_product_expansion (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    ramifiedProduct S hS η u x w z =
      ∑ j : ramifiedPrimes S u → Fin 3,
        ramifiedTupleCoefficient S hS η u x z j * (ramifiedTupleScale S u j : ℂ) ^ (-w) := by
  have he (j : ramifiedPrimes S u → Fin 3) :
      (∏ P, ramifiedCoefficientVector S hS η u x z P (j P) *
        ((primeScale P.val : ℂ) ^ (-w)) ^ (j P).val) =
      ramifiedTupleCoefficient S hS η u x z j * (ramifiedTupleScale S u j : ℂ) ^ (-w) := by
    rw [Finset.prod_mul_distrib]
    unfold ramifiedTupleCoefficient ramifiedTupleScale
    congr 1
    have hh := map_prod (positiveCpowHom (-w)) (fun P : ramifiedPrimes S u =>
      primeScale P.val ^ (j P).val) Finset.univ
    simpa only [map_pow, positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] using hh.symm
  simp_rw [← he]
  rw [← Fintype.prod_sum (fun P : ramifiedPrimes S u => fun j : Fin 3 =>
    ramifiedCoefficientVector S hS η u x z P j * ((primeScale P.val : ℂ) ^ (-w)) ^ j.val)]
  unfold ramifiedProduct
  change (∏ P : ramifiedPrimes S u,
    ramifiedCorrection η u P.val
      (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z) = _
  apply Finset.prod_congr rfl
  intro P hP
  rw [ramifiedCoefficientVector, quadratic_vector_eval, actual_ramified_expansion]
  rfl

theorem ramified_product_coefficient_mass (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (sigma : ℝ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + sigma) :
    (∑ j : ramifiedPrimes S u → Fin 3,
      ‖ramifiedTupleCoefficient S hS η u x z j‖ *
        (ramifiedTupleScale S u j : ℝ) ^ (-sigma)) ≤ 579 ^ (ramifiedPrimes S u).card := by
  have he (j : ramifiedPrimes S u → Fin 3) :
      ‖ramifiedTupleCoefficient S hS η u x z j‖ * (ramifiedTupleScale S u j : ℝ) ^ (-sigma) =
      ∏ P : ramifiedPrimes S u,
        ‖ramifiedCoefficientVector S hS η u x z P (j P) *
          ((primeScale P.val : ℂ) ^ (-(sigma : ℂ))) ^ (j P).val‖ := by
    have hpos : 0 < (ramifiedTupleScale S u j : ℝ) := by
      unfold ramifiedTupleScale
      exact_mod_cast Finset.prod_pos (fun (P : ramifiedPrimes S u) _ => pow_pos (lt_of_lt_of_le
        (by norm_num : (0 : ℝ≥0) < 1) (primeScale_one_le P.val)) _)
    have hn := Complex.norm_cpow_eq_rpow_re_of_pos hpos (-(sigma : ℂ))
    simp only [Complex.neg_re, Complex.ofReal_re] at hn
    rw [← hn]
    simp only [Complex.neg_re, Complex.ofReal_re, ← norm_mul]
    unfold ramifiedTupleCoefficient ramifiedTupleScale
    have hh := map_prod (positiveCpowHom (-(sigma : ℂ))) (fun P : ramifiedPrimes S u =>
      primeScale P.val ^ (j P).val) Finset.univ
    simp only [map_pow, positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hh
    rw [hh, ← Finset.prod_mul_distrib, norm_prod]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun P : ramifiedPrimes S u => fun j : Fin 3 =>
    ‖ramifiedCoefficientVector S hS η u x z P j * ((primeScale P.val : ℂ) ^ (-(sigma : ℂ))) ^ j.val‖)]
  calc
    _ ≤ ∏ _P : ramifiedPrimes S u, (579 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro P hP
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      · intro P hP
        unfold ramifiedCoefficientVector
        rw [quadratic_vector_mass _ _ _ (by
          have := primeScale_one_le P.val
          exact lt_of_lt_of_le zero_lt_one this)]
        exact actual_ramified_coefficient_mass η u P.val _
          (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
          x z sigma hx hsigma hz hxw
    _ = _ := by simp

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorRamifiedProduct -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Scalar.Exponent ; sha256 7dcd62fb21dde74fe3a649dac105d352700809e57b3c1de7151343b4a77e2ae4 -/
section
/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/





noncomputable section
namespace Cycle25.Numerator.Scalar

theorem countingCoefficient_binding {kap p : ℝ} (hk : 7/10 ≤ kap) :
    OAI.SevenEighths.Cycle25DetectorRowCount.coefficient p kap = Arithmetic.countingCoefficient kap p := by
  rw [Arithmetic.canonical_counting_formula hk]
  unfold OAI.SevenEighths.Cycle25DetectorRowCount.coefficient
    OAI.SevenEighths.Cycle25DetectorRowCount.primeWeight
    OAI.SevenEighths.Cycle25DetectorRowCount.denominator
    OAI.SevenEighths.Cycle25DetectorRowCount.b
  ring

theorem rowCount_binding {kap p : ℝ} (hk : 7/10 ≤ kap) (delta : ℝ) :
    OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap = Arithmetic.rowExponent kap delta p := by
  unfold OAI.SevenEighths.Cycle25DetectorRowCount.rowCount Arithmetic.rowExponent Arithmetic.rowDen
  rw [countingCoefficient_binding hk]
  rfl

def numeratorExponent (kap d delta p : ℝ) : ℝ :=
  -ly/2+ell*(17/50-1/2)+delta*p*ell+
    d*((3*OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap+1)/4-17/50)-
      delta*p*(2*ly-d)/(12*kap)

def weightedSourceSZExponent (a e : ℝ) : ℝ :=
  lx*(1/2-17/50)+a+16*e+17/50-1

theorem numerator_kernel_exponent {kap : ℝ} (hk : 7/10 ≤ kap)
    (delta p e : ℝ) :
    numeratorExponent kap h delta p+weightedSourceSZExponent ((1+delta)/2) e =
      Arithmetic.fullBoundary kap delta p-(4+b)/6+16*e := by
  unfold numeratorExponent weightedSourceSZExponent Arithmetic.fullBoundary
  rw [rowCount_binding hk]
  simp only [b, lx, ly, ell, h, Arithmetic.x0, Arithmetic.y0]
  ring

theorem rowCount_bounds {kap delta p : ℝ} (hk : 7/10 ≤ kap)
    (hd : 0 ≤ delta ∧ delta ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    1-delta ≤ OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap ∧ OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap ≤ 1 := by
  rw [rowCount_binding hk]
  have hC := Arithmetic.countingCoefficient_pos hk hp
  have hDen := Arithmetic.rowDen_pos hk ⟨hd.1,by linarith [hd.2]⟩ hp
  have hV : 0 ≤ (5/6:ℝ)-delta := by linarith [hd.2]
  have hC1 : Arithmetic.countingCoefficient kap p ≤ 1 := by
    have hD : 0 < Arithmetic.countingDen kap p := by
      linarith [Arithmetic.countingDen_lower hk hp]
    apply (div_le_iff₀ hD).2
    unfold Arithmetic.countingDen
    have hm := mul_nonneg (show 0 ≤ kap by linarith) hp.1
    nlinarith [sq_nonneg p]
  have hCV : Arithmetic.countingCoefficient kap p*((5/6:ℝ)-delta) ≤
      Arithmetic.rowDen kap delta p := by
    have hm := mul_le_mul_of_nonneg_right hC1 hV
    unfold Arithmetic.rowDen
    nlinarith [mul_nonneg hd.1 hC.le]
  have hr : delta*Arithmetic.countingCoefficient kap p*((5/6:ℝ)-delta)/
      (2*Arithmetic.rowDen kap delta p) ≤ delta/2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hCV hd.1]
  unfold Arithmetic.rowExponent
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (mul_nonneg hd.1 hC.le) hV) (by positivity))
  · linarith

/-- The physical dyad extension shrinks with the contradiction gap. -/
theorem numerator_geometric_extension {kap d delta p t : ℝ} (hk : 7/10 ≤ kap)
    (_hd : 1/2 ≤ d) (_hd1 : d ≤ 1) (ht : 0 ≤ t) (htop : d ≤ h+3*t)
    (hdelta : 0 ≤ delta ∧ delta ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    numeratorExponent kap d delta p ≤ numeratorExponent kap h delta p+6*t := by
  have hr := rowCount_bounds hk hdelta hp
  have hR0 : 0 ≤ OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap := by linarith [hdelta.2]
  have hqp : 0 ≤ delta*p := mul_nonneg hdelta.1 hp.1
  have hqp1 : delta*p ≤ 3/8 := by
    have hm := mul_le_mul hdelta.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hm
    exact hm
  have hk0 : 0 < 12*kap := by linarith
  let slope := (3*OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap+1)/4-17/50+
      delta*p/(12*kap)
  have hfrac0 : 0 ≤ delta*p/(12*kap) := by positivity
  have hfrac1 : delta*p/(12*kap) ≤ 1 := by
    apply (div_le_iff₀ hk0).2
    nlinarith
  have hs0 : 0 ≤ slope := by dsimp only [slope]; linarith [hdelta.2]
  have hs1 : slope ≤ 2 := by dsimp only [slope]; linarith [hr.2]
  have hid : numeratorExponent kap d delta p-numeratorExponent kap h delta p =
      (d-h)*slope := by
    unfold numeratorExponent
    dsimp only [slope]
    field_simp [ne_of_gt (show 0 < kap by linarith)]
    ring
  have hm := mul_le_mul_of_nonneg_right (show d-h ≤ 3*t by linarith) hs0
  have hm1 := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 3*t by positivity)
  linarith

theorem numerator_supremum_improvement {beta d delta p t : ℝ}
    (hbeta : theta < beta) (hd : 1/2 ≤ d) (hd1 : d ≤ 1)
    (ht : 0 ≤ t) (htop : d ≤ h+3*t)
    (hdelta : 0 ≤ delta ∧ delta ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    numeratorExponent (2*beta-1) d delta p+
      weightedSourceSZExponent ((1+delta)/2) 0 ≤
      signal beta-(4/5)*(beta-theta)+6*t := by
  have hk : (7:ℝ)/10 ≤ 2*beta-1 := by
    have hb0 := Arithmetic.kappa0_range.1
    rw [Arithmetic.kappa0_eq] at hb0
    change Arithmetic.b0 < beta at hbeta
    linarith
  have hext := numerator_geometric_extension hk hd hd1 ht htop hdelta hp
  have hb := Arithmetic.supremum_improvement hbeta
    ⟨hdelta.1,by linarith [hdelta.2]⟩ hp
  have hid := numerator_kernel_exponent hk delta p 0
  unfold signal theta at *
  linarith

end Cycle25.Numerator.Scalar
end
/- END ORIGINAL MODULE Cycle25.Numerator.Scalar.Exponent -/

/- BEGIN ORIGINAL MODULE Endpoint.SourceFormula ; sha256 45ce109107b8936d97d04d9c2f4926373fe41511a41dcac25504bc23a63cd051 -/
section



noncomputable section
namespace Submission20261012.Endpoint
set_option maxHeartbeats 0
set_option maxRecDepth 4000

lemma source_row_formula (δ p : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    Cycle25.Arithmetic.rowExponent kappa δ p =
      1 - δ + δ * slotB p * deltaV δ / (2 * denomJ δ p) := by
  have hk : (7 : ℝ) / 10 ≤ kappa := by norm_num [kappa]
  have hd : 0 ≤ δ ∧ δ ≤ 5 / 6 := ⟨hδ0, by linarith⟩
  have hp : 0 ≤ p ∧ p ≤ 1 / 2 := ⟨hp0, hp1⟩
  have hD : Cycle25.Arithmetic.countingDen kappa p ≠ 0 :=
    ne_of_gt (by linarith [Cycle25.Arithmetic.countingDen_lower hk hp])
  have hS : Cycle25.Arithmetic.rowDen kappa δ p ≠ 0 :=
    ne_of_gt (Cycle25.Arithmetic.rowDen_pos hk hd hp)
  have hJ : denomJ δ p ≠ 0 := ne_of_gt (denomJ_pos δ p hδ0 hδ1 hp1)
  unfold Cycle25.Arithmetic.rowExponent
  field_simp [hS, hJ]
  unfold Cycle25.Arithmetic.rowDen Cycle25.Arithmetic.countingCoefficient
  field_simp [hD]
  simp only [Cycle25.Arithmetic.countingDen, denomJ, deltaV, denomD, slotB]
  norm_num [kappa]
  <;> ring

/-- Literal B0.46/B0.55 numerator ledger on the branch d >= y. -/
def sourceHighRowExponent (κ d c δ p : ℝ) : ℝ :=
  (1 + δ) / 2 + h * (13 / 75) - y / 2 - ell / 2 + ell * (δ * p)
    + d * (1 / 4 + 3 * Cycle25.Arithmetic.rowExponent κ δ p / 4 - 17 / 50)
    - δ * p * (2 * y - d) / (2 * c)

lemma sourceHighRowExponent_eq (d c δ p : ℝ) (hc : c ≠ 0)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    sourceHighRowExponent kappa d c δ p = highRowExponent d c δ p := by
  have hJ : denomJ δ p ≠ 0 := ne_of_gt (denomJ_pos δ p hδ0 hδ1 hp1)
  unfold sourceHighRowExponent
  rw [source_row_formula δ p hδ0 hδ1 hp0 hp1]
  unfold highRowExponent regular
  field_simp [hJ, hc]
  <;> ring

/-- Affine capacity retained from the local volume/defect ledger. -/
def sourceLocalRowExponent (κ d δ p : ℝ) : ℝ :=
  (1 + δ) / 2 + h * (13 / 75) - y / 2 - ell / 2 + ell * (δ * p)
    + d * (1 / 4 + 3 * Cycle25.Arithmetic.rowExponent κ δ p / 4 - 17 / 50)
    - δ * p * (2 * y - d + (37/10000)*d) / 9

lemma sourceLocalRowExponent_eq (d δ p : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    sourceLocalRowExponent kappa d δ p = localHighRowExponent d δ p := by
  have hJ : denomJ δ p ≠ 0 := ne_of_gt (denomJ_pos δ p hδ0 hδ1 hp1)
  unfold sourceLocalRowExponent
  rw [source_row_formula δ p hδ0 hδ1 hp0 hp1]
  unfold localHighRowExponent localRegular
  field_simp [hJ]
  <;> ring

theorem source_top_endpoint (δ p : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    sourceLocalRowExponent kappa h δ p ≤ theta - 1 / 2000000 := by
  rw [sourceLocalRowExponent_eq h δ p hδ0 hδ1 hp0 hp1]
  exact top_endpoint δ p hδ0 hδ1 hp0 hp1

theorem source_junction_endpoint (δ p : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    sourceHighRowExponent kappa junction (6 * kappa) δ p ≤ theta - 1 / 10000 := by
  rw [sourceHighRowExponent_eq junction (6 * kappa) δ p
    (by norm_num [kappa]) hδ0 hδ1 hp0 hp1]
  exact junction_endpoint δ p hδ0 hδ1 hp0 hp1

theorem source_half_endpoint (δ p : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    sourceHighRowExponent kappa (1 / 2) (6 * kappa) δ p ≤ theta - 1 / 100 := by
  rw [sourceHighRowExponent_eq (1 / 2) (6 * kappa) δ p
    (by norm_num [kappa]) hδ0 hδ1 hp0 hp1]
  exact half_endpoint δ p hδ0 hδ1 hp0 hp1

end Submission20261012.Endpoint
#print axioms Submission20261012.Endpoint.source_row_formula
#print axioms Submission20261012.Endpoint.source_top_endpoint
#print axioms Submission20261012.Endpoint.source_junction_endpoint
#print axioms Submission20261012.Endpoint.source_half_endpoint
end
/- END ORIGINAL MODULE Endpoint.SourceFormula -/
