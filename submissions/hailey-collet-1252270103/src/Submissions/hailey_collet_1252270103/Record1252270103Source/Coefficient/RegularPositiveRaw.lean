/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Actual buffered ordinary rows, with original profiles, raw scales and slots.
The analytic input is the existing Cycle61/OpenAI zero-free plain estimate. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularPositiveRawProfile
import Submissions.hailey_collet_1252270103.Cycle61.Moment.HighParameters

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter HeckeFamily HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentFiniteProfileExceptional CenteredMomentRetainedEnergy
open CenteredMomentRetainedProfile CenteredMomentHeckeHeight
open CenteredMomentWholeSlotDeletion
open Cycle61HighProfiles Cycle61Moment
local notation "O" => HeckeFamily.O

theorem buffered_plain_scale_power (Z d ε ν : ℝ) (X r : Fin 2 → ℝ)
    (hZ : 0 < Z) (hscale : ∀ j, clippedScale (X j) = (Z ^ d) ^ (r j)) :
    (Z ^ d) ^ (ν * (r 0 + r 1) + 2 * ε) =
      (clippedScale (X 0) * clippedScale (X 1)) ^ ν * Z ^ (2 * ε * d) := by
  have hd : 0 < Z ^ d := Real.rpow_pos_of_pos hZ _
  rw [Real.rpow_add hd]
  have h₁ : (Z ^ d) ^ (ν * (r 0 + r 1)) =
      ((Z ^ d) ^ (r 0 + r 1)) ^ ν := by
    rw [← Real.rpow_mul hd.le]
    congr 1
    ring
  rw [h₁, Real.rpow_add hd, ← hscale 0, ← hscale 1, ← Real.rpow_mul hZ.le]
  congr 2
  ring

/-- The finite profile control is chosen before the moving character family,
positive raw scales, marked type and heights. Every marked factor is retained. -/
theorem buffered_positive_raw (ap bp : ℝ) (hap : 0 < ap) :
    ∃ bound : ℕ → ℝ, (∀ k, 0 < bound k) ∧
    ∀ P : HighSourceParameters, P.profileBound = bound →
    ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ (Z : ℝ), 1 < Z → 2 < Z ^ P.τ →
    ∀ {Dict : Type*} [Fintype Dict] (χ : Dict → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (a : ℝ) (i : ℕ),
    51 / 100 ≤ a → a ≤ 1 →
    HeckeDetectorZeros.zeroMaximum χ hχ (3 * (i + 1 : ℕ) * Z ^ P.τ) < a + 2 * P.e →
    ∀ (j : Dict) (η : Character) (m z : O),
    (∀ I : Ideal O, idealCoeff η I *
      CanonicalRowCompletion.idealRowHom (m ^ 6 * (1 * z)) I = idealCoeff (χ j) I) →
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (scales : ι → ℝ),
    (∀ k, 0 < scales k) →
    ∀ (p : Profiles ap bp) (X : Fin 2 → ℝ) (t : ℝ),
    (∀ k, 0 < X k) → (∀ k, clippedScale (X k) ≤ Z ^ (P.d * P.Rplain)) →
    (χ j).modulus.absNorm ≤ Z ^ P.d →
    |t| + Z ^ P.τ / 2 ≤ (3 * i + 2 : ℕ) * Z ^ P.τ →
    (3 + (3 * i + 2 : ℕ) * Z ^ P.τ) ^ 4 ≤ (Z ^ P.d) ^ P.vplain →
    ‖positiveSlotRow η m 1 z (p.profile 0) (p.profile 1)
      pool β scales t (X 0) (X 1)‖ ^ 2 ≤
    C * (p.control T) ^ 2 * (X 0 * X 1) ^ (2 * a - 1) * Z ^ (2 * P.εplain * P.d) *
      ∏ k, max 1 (‖normalizedSlot η m 1 z (pool k) (β k) t (scales k)‖ ^ 2) := by
  obtain ⟨bound, hbound, hnorm⟩ := fixed_clipped_normalization ap bp hap
  refine ⟨bound, hbound, ?_⟩
  intro P hboundeq
  obtain ⟨n, Cp, hCp, hplain⟩ := actual_buffered_retained_plain_factors
    P.Rplain P.dmax P.τ P.εplain P.e P.κ P.vplain P.hRp P.hdmax P.hτ P.hεp
      P.he P.he' P.hκ P.hκ' P.hvp P.hplainBudget P.profileBound P.hprofile
  obtain ⟨S, T, Cm, hS, hCm, hn⟩ := hnorm n
  refine ⟨T, (max 1 bp) ^ 4 * Cm ^ 2 * Cp ^ 2, by positivity, ?_⟩
  intro Z hZ hZT Dict _ χ hχ a i ha ha' hupper j η m z hcoeff
    ι _ _ pool β scales hscales p X t hX hcap hmod hfreq hheight
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hν : 0 ≤ 2 * a - 1 := by linarith
  have hν' : 2 * a - 1 ≤ 1 := by linarith
  have hXY : 0 < X 0 * X 1 := mul_pos (hX 0) (hX 1)
  have hmax : 0 ≤ ∏ k, max 1
      (‖normalizedSlot η m 1 z (pool k) (β k) t (scales k)‖ ^ 2) :=
    Finset.prod_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
  by_cases hz : positiveSlotRow η m 1 z (p.profile 0) (p.profile 1)
      pool β scales t (X 0) (X 1) = 0
  · rw [hz, norm_zero, zero_pow (by decide)]
    exact mul_nonneg (by positivity) hmax
  have hret := positive_row_surviving_scales p η m z pool β scales t X hX hz
  have hp := hn p X hX hret
  let r : Fin 2 → ℝ := fun k => Real.logb Z (clippedScale (X k)) / P.d
  have hr (k : Fin 2) : 0 ≤ r k :=
    div_nonneg (Real.logb_nonneg hZ (clippedScale_ge_one _)) P.hd.le
  have hrbound (k : Fin 2) : r k ≤ P.Rplain := by
    apply (div_le_iff₀ P.hd).mpr
    have hh := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one (X k))) (hcap k)
    rw [Real.logb_rpow hZp hZ.ne'] at hh
    linarith
  have hclip (k : Fin 2) : clippedScale (X k) = (Z ^ P.d) ^ (r k) := by
    dsimp [r]
    rw [← Real.rpow_mul hZp.le, mul_div_cancel₀ _ P.hd.ne',
      Real.rpow_logb hZp hZ.ne' (zero_lt_one.trans_le (clippedScale_ge_one _))]
  have hb := hplain Z P.d hZ.le P.hd.le P.hdm hZT χ hχ a i ha ha' hupper
    j η m z false (by simpa using hcoeff) pool β scales hscales
    (fun k => ((normalizedPlains hap S p X hX).profile k : ℝ → ℂ)) X r
    (fun _ => ap / max 1 bp) (fun _ => bp) t hX hclip
    (fun _ => div_pos hap (zero_lt_one.trans_le (le_max_left _ _)))
    (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hp.2.2.1)
    (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hp.2.2.2.1)
    hmod hr hrbound hfreq hheight
    (by
      intro k x hx u
      simpa only [orientedProfile, Bool.false_eq_true, ite_false, hboundeq] using
        hp.2.2.2.2 k 2 (Or.inl rfl) x (high_strip_mem ha' P.he'.le hx) u)
    (by
      intro k x hx u
      simpa only [orientedProfile, Bool.false_eq_true, ite_false, hboundeq] using
        hp.2.2.2.2 k (n + 2) (Or.inr rfl) x (high_strip_mem ha' P.he'.le hx) u)
  rw [buffered_plain_scale_power Z P.d P.εplain (2 * a - 1) X r hZp hclip] at hb
  have hslots : (∏ k, ‖normalizedSlot η m 1 z (pool k) (β k) t (scales k)‖ ^ 2) ≤
      ∏ k, max 1 (‖normalizedSlot η m 1 z (pool k) (β k) t (scales k)‖ ^ 2) :=
    Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun _ _ => le_max_right _ _)
  have hclipcost := clipped_plain_product_rpow (X 0) (X 1) bp (2 * a - 1)
    (hX 0) (hX 1) (hret 0) (hret 1) hν hν'
  have hnormalized :
      ‖retainedPositiveRow η m 1 z ((normalizedPlains hap S p X hX).profile 0)
        ((normalizedPlains hap S p X hX).profile 1) pool β scales t (X 0) (X 1)‖ ^ 2 ≤
      Cp ^ 2 * ((max 1 bp) ^ 2 * (X 0 * X 1) ^ (2 * a - 1) *
        Z ^ (2 * P.εplain * P.d)) *
        ∏ k, max 1 (‖normalizedSlot η m 1 z (pool k) (β k) t (scales k)‖ ^ 2) := by
    have hfac := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hclipcost
        (Real.rpow_nonneg hZp.le (2 * P.εplain * P.d))) (sq_nonneg Cp)
    exact hb.trans (mul_le_mul hfac hslots
      (Finset.prod_nonneg (fun _ _ => sq_nonneg _)) (by positivity))
  have hcontrol :
      (clippedControl hap S p X hX 0 * clippedControl hap S p X hX 1) ^ 2 ≤
        (Cm * p.control T) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (clippedControl_nonneg hap S p X hX 0)
      (clippedControl_nonneg hap S p X hX 1)) hp.1 2
  have hretained := mul_le_mul hcontrol hnormalized (sq_nonneg _) (sq_nonneg _)
  rw [← retained_plain_normalized_norm_sq hap S hS p η m z pool β scales t X hX hret]
    at hretained
  have hraw := retained_rectangle_uniform_energy η m 1 z (p.profile 0) (p.profile 1)
    pool β scales hscales bp bp t (X 0) (X 1) (hX 0) (hX 1)
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2)
  apply hraw.trans
  apply (mul_le_mul_of_nonneg_left hretained
    (mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (zero_le_one.trans (le_max_left _ _)))).trans_eq
  ring

#print axioms buffered_plain_scale_power
#print axioms buffered_positive_raw
end
end OAI.SevenEighths.Record1252270103Source
