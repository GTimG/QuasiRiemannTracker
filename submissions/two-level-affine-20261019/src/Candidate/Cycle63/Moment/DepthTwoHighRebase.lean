/- A record of the HIGH part of the second step at the base `Z^c` read at the base `Z`. Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.DepthTwoHighCount

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily HeckeDetectorZeros LocalMoment ProbePhysical CanonicalQuadraticSieve IdealMobiusDivisorSum
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
variable {M : Ideal O} [NeZero M]
variable {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {Base : Type} {base : Base → Character} {η₀ : Character} {Z B B' T c : ℝ} {left : Bool} {v₁ : O}
  {unit : FirstSourceLabel → O}

/-- `c` times the logarithm to the base `Z^c` is the logarithm to the base `Z`. -/
theorem mul_logb_rpow_base {x : ℝ} (hZ : 0 < Z) (hc : c ≠ 0) : c*Real.logb (Z^c) x = Real.logb Z x := by
  unfold Real.logb
  rw [Real.log_rpow hZ, mul_div_assoc', mul_div_mul_left _ _ hc]

/-- A record of the HIGH part at the base `Z^c` read at the base `Z`: the same classes, labels, witnesses and zero
parameters, the class exponents and the row-norm and missing-radical exponents multiplied by `c`, and the caps
`(Z^c)^B` weakened to `Z^B'`. -/
def SecondStepHighCount.rebase (R : SecondStepHighCount M H hH base η₀ (Z^c) B T left v₁ unit)
    (hZ : 1 ≤ Z) (_hc : 0 < c) (hB : c*B ≤ B') : SecondStepHighCount M H hH base η₀ Z B' T left v₁ unit where
  Class := R.Class
  classFintype := R.classFintype
  labels := R.labels
  exponent := fun σ => c*R.exponent σ
  rowExp := fun σ => c*R.rowExp σ
  missExp := fun σ => c*R.missExp σ
  zeroBin := R.zeroBin
  witness := R.witness
  zero_le := R.zero_le
  row_le := fun σ ℓ hℓ => by
    have h := R.row_le σ ℓ hℓ
    rwa [← Real.rpow_mul (zero_le_one.trans hZ)] at h
  supported := R.supported
  same_support := R.same_support
  row_cap := fun σ ℓ hℓ => by
    have h := R.row_cap σ ℓ hℓ
    rw [← Real.rpow_mul (zero_le_one.trans hZ)] at h
    exact h.trans (Real.rpow_le_rpow_of_exponent_le hZ hB)
  ideal_cap := fun σ ℓ hℓ => by
    have h := R.ideal_cap σ ℓ hℓ
    have hcap : (Z^c)^B ≤ Z^B' := by
      rw [← Real.rpow_mul (zero_le_one.trans hZ)]
      exact Real.rpow_le_rpow_of_exponent_le hZ hB
    exact ⟨h.1.trans hcap, h.2.1.trans hcap, h.2.2.1.trans hcap, h.2.2.2.trans hcap⟩
  missing_le := fun σ ℓ hℓ => by
    have h := R.missing_le σ ℓ hℓ
    rwa [← Real.rpow_mul (zero_le_one.trans hZ)] at h

/-- The count form of a record does not change when the record is read at the base `Z`. -/
theorem SecondStepHighCount.rebase_value (R : SecondStepHighCount M H hH base η₀ (Z^c) B T left v₁ unit)
    (hZ : 1 ≤ Z) (hc : 0 < c) (hB : c*B ≤ B') : (R.rebase hZ hc hB).value = R.value := by
  unfold SecondStepHighCount.value
  refine Finset.sum_congr rfl fun σ _ => ?_
  change Z^(c*R.exponent σ)*((R.labels σ).card : ℝ) = (Z^c)^(R.exponent σ)*((R.labels σ).card : ℝ)
  rw [Real.rpow_mul (zero_le_one.trans hZ)]

/-- A record read at the base `Z` has the same number of classes. -/
theorem SecondStepHighCount.rebase_card (R : SecondStepHighCount M H hH base η₀ (Z^c) B T left v₁ unit)
    (hZ : 1 ≤ Z) (hc : 0 < c) (hB : c*B ≤ B') : Fintype.card (R.rebase hZ hc hB).Class = Fintype.card R.Class :=
  rfl

/-- A record that pays at the base `Z^c` with the scale, length, amplifier and loss `scale, length, amp, loss` pays at
the base `Z` with `c` times them. -/
theorem SecondStepHighCount.rebase_pays (R : SecondStepHighCount M H hH base η₀ (Z^c) B T left v₁ unit)
    (hZ : 1 ≤ Z) (hc : 0 < c) (hB : c*B ≤ B') {lo scale length amp loss : ℝ}
    (h : R.Pays lo scale length amp loss) :
    (R.rebase hZ hc hB).Pays lo (c*scale) (c*length) (c*amp) (c*loss) := by
  unfold SecondStepHighCount.Pays at h ⊢
  intro σ
  obtain ⟨h₁, h₂, h₃⟩ := h σ
  have hlog := mul_logb_rpow_base (x := ((Ideal.span {v₁}).absNorm : ℝ)) (zero_lt_one.trans_le hZ) hc.ne'
  have key := mul_le_mul_of_nonneg_left h₃ hc.le
  refine ⟨h₁, h₂, ?_⟩
  dsimp only [SecondStepHighCount.rebase]
  rw [← hlog]
  nlinarith [key]

end
end OAI.SevenEighths.Cycle63Moment
