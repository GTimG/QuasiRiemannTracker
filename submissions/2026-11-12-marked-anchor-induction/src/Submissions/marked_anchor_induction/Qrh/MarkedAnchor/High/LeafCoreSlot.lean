/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from Hailey Collet's `actual_all_scale_high_slot` (`Cycle61/Moment/HighSlots.lean`,
Apache-2.0): the same two-case slot bound (buffered prime bound for large prime scales, bounded scale
otherwise), stated for the CORE slot of `High.LeafContract.coreSlot` (HC `wholeNaturalBatch.Q`)
through `natural_relative_slot_eq_ray`. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafContract
import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeSourceGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeHeight

/-!
# High.LeafCoreSlot

The slot envelope of the core batch. A core slot at prime scale
`P = (Z^d)^r` whose relative ray family has zero maximum `< a + 2e` at the height `3(i+1)Z^τ`, and
conductors `≤ Z^d`, satisfies

`‖coreSlot‖ ≤ C (Z^d)^((a - 1/2) r + ε)`,

for every `r ∈ [0, Rw]`, with `C` fixed before `Z` and `ε ≥ 8 e Rw + κ`. In the leaf, `d` is the
packed `d ≥ Mcap + 1` of `HighBranchMesh`, `Rw = 1/d`, and the budget is `hslotBudget`
(`8 e (1/d) + kap ≤ ε₁`). So `‖coreSlot‖ ≤ (C Z^(ε₁ d)) (Z^w)^((2a-1)/2)`, uniformly in the core
scale.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
open OAI OAI.SevenEighths
open HeckeFamily HeckePrimeRay CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot ProbePhysical
open Record12518109GainWholeGeometry Cycle61Moment HeckeInverseAmplification
local notation "O" => HeckeFamily.O

variable (rayM : Ideal O) [NeZero rayM]
local instance leafCoreSlotQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- **Core slot envelope, every prime scale.** -/
theorem core_slot_bound (W : ℝ → ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (Rw dmax τ ε e κ ηs : ℝ)
    (hRw : 0 ≤ Rw) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hηs : 0 ≤ ηs)
    (hbudget : 8*e*Rw+κ ≤ ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ →
      ∀ (ηc η₀ : Character) (u : O) (hu : u ≠ 0)
        (hn : ∀ j, (naturalRow (wholeSourceBase rayM H hH η₀ ηc j) u hu).character.residue ≠ 1)
        (θ : RayQuotient.Characters rayM H) (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 →
      HeckeDetectorZeros.zeroMaximum
          (fun j => (naturalRow (wholeSourceBase rayM H hH η₀ ηc j) u hu).character) hn
          (3*(i+1 : ℕ)*Z^τ) < a+2*e →
      ∀ r σ freq : ℝ, 0 ≤ r → r ≤ Rw → 33/50 ≤ σ → σ ≤ 33/50 →
      (∀ θ' : RayQuotient.Characters rayM H,
        (twistedFamily rayM H hH (relativeRayBase rayM H hH ηc η₀ u hu θ) θ').modulus.absNorm ≤
          Z^d) →
      |freq|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηs →
      ‖naturalSlot (naturalRow ηc u hu).character (primePool rayM H 2 ((Z^d)^r))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ θ) I *
          HeckePrimeAnnular.annularWeight W ((Z^d)^r) σ freq I) ((Z^d)^r)‖ ≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cb, hCb, hbound⟩ := ray_prime_bin_bound rayM H hH W 1 2 (by norm_num) hWs hW
    Rw dmax τ ε e κ ηs (33/50) (33/50) hRw hdmax hτ hε he he' hκ hηs hbudget
  let K := 2*(|Real.log 1|+|Real.log 2|)+1
  obtain ⟨Cs, hCs, hsmall⟩ := CenteredMomentPrimeHeight.ray_prime_bounded_scale rayM H W 1 2
    (33/50) (33/50) (Real.exp K) (by norm_num) hWs hW.continuous
    (Real.one_le_exp (by dsimp [K]; positivity))
  refine ⟨Cb + Cs + 1, by linarith, ?_⟩
  intro Z d hZ hd hdm hbase hT ηc η₀ u hu hn θ a i ha ha' hmax r σ freq hr hr' hσ hσ' hmod
    hfreq hheight
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hbasep : 0 < Z^d := Real.rpow_pos_of_pos hZp d
  have hP : 1 ≤ (Z^d)^r := Real.one_le_rpow (by linarith) hr
  have hPp : 0 < (Z^d)^r := zero_lt_one.trans_le hP
  have htarget : 1 ≤ (Z^d)^((a-1/2)*r+ε) :=
    Real.one_le_rpow (by linarith) (by nlinarith)
  rw [natural_relative_slot_eq_ray rayM H hH ηc η₀ u hu θ W 2 ((Z^d)^r) σ freq hPp]
  have hnr := relative_ray_nonprincipal rayM H hH ηc η₀ u hu hn θ
  by_cases hlarge : K ≤ Real.log ((Z^d)^r)
  · have hm := (relative_ray_maximum_le rayM H hH ηc η₀ u hu hn θ (3*(i+1 : ℕ)*Z^τ)).trans_lt hmax
    have hb := hbound Z d hZ hd hdm hbase hT (relativeRayBase rayM H hH ηc η₀ u hu θ) hnr a i ha ha'
      hm r σ freq hr hr' hσ hσ' hlarge hmod hfreq hheight
    refine hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hbasep.le _))
  · have hPD : (Z^d)^r ≤ Real.exp K := by
      have hb := Real.exp_le_exp.mpr (le_of_not_ge hlarge)
      simpa only [Real.exp_log hPp] using hb
    have hb := hsmall (relativeRayBase rayM H hH ηc η₀ u hu θ) ((Z^d)^r) σ freq hP hPD hσ hσ'
    refine hb.trans ?_
    calc Cs ≤ Cb + Cs + 1 := by linarith
      _ ≤ (Cb + Cs + 1) * (Z^d)^((a-1/2)*r+ε) := le_mul_of_one_le_right (by linarith) htarget

/-- Regular cores have a nonprincipal core family (HC `regular_nonprincipal` through the
coefficient identity of the clean bases). -/
theorem core_nonprincipal (η η₀ : Character) (u : FreeRow) (hu : RegularCore rayM H hH η η₀ u) :
    ∀ j, (coreFamily rayM H hH η η₀ u j).residue ≠ 1 := by
  intro j hp
  have hreg := (wholeRegularDictionary rayM H hH η η₀).regular_nonprincipal u hu j
  exact hreg ((HeckeFiniteDeletion.principal_iff_of_mask _ _
    (LocalMoment.coefficient_equality_mask _ _
      (fun I => LocalMoment.natural_raw_coefficients _ ⟨u.val, u.property.1⟩ I))).mp hp)

/-- Rescaling a slot product by `0 < c ≤ 1` costs `(c²)⁻¹` per slot in the `max 1` weights. -/
theorem prod_max_one_scaled {Slot : Type*} (slots : Finset Slot) (Q : Slot → ℂ) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∏ s ∈ slots, max 1 (‖Q s‖^2) ≤
      ((c^2)⁻¹)^slots.card * ∏ s ∈ slots, max 1 (‖(c : ℂ) * Q s‖^2) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => le_trans zero_le_one (le_max_left _ _)) ?_
  intro s _
  have hc2 : 0 < c^2 := by positivity
  have hinv : 1 ≤ (c^2)⁻¹ := one_le_inv₀ hc2 |>.mpr (by nlinarith)
  have hn : ‖(c : ℂ) * Q s‖^2 = c^2 * ‖Q s‖^2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]; ring
  rw [hn]
  refine max_le (le_trans hinv (le_mul_of_one_le_right (by positivity) (le_max_left _ _))) ?_
  calc ‖Q s‖^2 = (c^2)⁻¹ * (c^2 * ‖Q s‖^2) := by field_simp
    _ ≤ (c^2)⁻¹ * max 1 (c^2 * ‖Q s‖^2) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

/-- The prime scale of a slot is independent of the reference scale: `(Z^d)^(w/d) = Z^w`. -/
theorem scale_rescale {Z d w : ℝ} (hZ : 0 < Z) (hd : 0 < d) : (Z^d)^(w/d) = Z^w := by
  rw [← Real.rpow_mul hZ.le, mul_div_cancel₀ w hd.ne']

end
end Qrh.MarkedAnchor.High
