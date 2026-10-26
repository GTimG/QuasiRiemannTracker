import Candidate.Cycle63.Density.ActualMoments

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorInverseFiberCount HeckeDetectorRawFiber

structure DensityCountingSetup where
  modulus : Ideal O
  nonzero : modulus ≠ 0
  subgroup : Subgroup (O ⧸ modulus)ˣ
  units : RayOrthogonality.globalUnits modulus ≤ subgroup
  exclusions : Finset (Ideal O)
  profile : ℝ → ℝ
  smooth : ContDiff ℝ ∞ profile
  compact : HasCompactSupport profile
  positiveSupport : tsupport profile ⊆ Ioi 0
  nonnegative : ∀ y, 0 ≤ profile y
  nontrivial : profile ≠ 0
  lower : ℝ
  upper : ℝ
  bound : ℝ
  lowerPositive : 0 < lower
  ordered : lower ≤ upper
  boundPositive : 0 < bound
  support : Function.support profile ⊆ Ioo lower upper
  bounded : ∀ y, profile y ≤ bound

/-- Actual fixed-dictionary batch count. The height exponent precedes the dictionary; the constant and the scale
threshold follow it and precede every live bin, height and finite row population. -/
theorem fixed_dictionary_actual_batch_count {Label : Type*} [Fintype Label]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm η : ℝ) (hεm : 0 < εm) (hη : 0 < η)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∀ D : FixedUnmarkedDictionary Label, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (a ε T allowance height : ℝ) (i : ℕ),
      1/2 ≤ a → 2*a-1 ≤ 5/6 → 0 ≤ ε → ε ≤ 1/1000 →
      0 ≤ height → 2*Real.pi*allowance + (3*i : ℕ)*T ≤ height →
      ∀ (B : UnmarkedBatch Label U a ε (unmarkedCutoff (2*a-1)) T allowance i),
      B.data = D.data →
        (B.rows.card : ℝ) ≤ C * (1 + height)^J *
          U^(unmarkedDensity (2*a-1) + 156*ε + εm + η) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hb⟩ := batch_count_from_unmarked_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨J, hJ⟩ := fixed_dictionary_actual_batch_moments (Label := Label) c κ εm hc hκ hεm hβ
  obtain ⟨K, hK', hd⟩ := fixed_label_dyadic_cost (Label := Label) η hη
  refine ⟨J+1, fun D => ?_⟩
  obtain ⟨A, hA, hmom⟩ := hJ D
  refine ⟨K * (192*A*max 1 K₀), by positivity, ?_⟩
  filter_upwards [hb, hmom, hd] with U hb hmom hd
  refine ⟨hmom.1, ?_⟩
  intro a ε T allowance height i ha hδ hε hε' hh hf B hdata
  have hcut := unmarkedCutoff_bounds (show 0 ≤ 2*a-1 by linarith) hδ
  have hbound := hb a ε T allowance (A*(1+height)^J) height i hmom.1 ha hδ hε hε'
    (by positivity) hh hf B
    (hmom.2 hcut.1 hcut.2 hε hε' B hdata height hh)
  apply hbound.trans
  calc
    _ ≤ (K * U^η) * fiberConstant (A*(1+height)^J) height K₀ *
        U^(unmarkedDensity (2*a-1) + 156*ε + εm) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hd
          (fiberConstant_bounds _ _ _ (by positivity) hh hK).1)
        (Real.rpow_nonneg (zero_lt_one.trans hmom.1).le _)
    _ = K*(192*A*max 1 K₀)*(1+height)^(J+1)*
        U^(unmarkedDensity (2*a-1)+156*ε+εm+η) := by
      rw [Real.rpow_add (zero_lt_one.trans hmom.1)
        (unmarkedDensity (2*a-1)+156*ε+εm) η, pow_succ]
      unfold fiberConstant
      ring

theorem DensityCountingSetup.actual_batch_count {Label : Type*} [Fintype Label]
    (S : DensityCountingSetup)
    (εm η : ℝ) (hεm : 0 < εm) (hη : 0 < η)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∀ D : FixedUnmarkedDictionary Label, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (a ε T allowance height : ℝ) (i : ℕ),
      1/2 ≤ a → 2*a-1 ≤ 5/6 → 0 ≤ ε → ε ≤ 1/1000 →
      0 ≤ height → 2*Real.pi*allowance + (3*i : ℕ)*T ≤ height →
      ∀ (B : UnmarkedBatch Label U a ε (unmarkedCutoff (2*a-1)) T allowance i),
      B.data = D.data →
        (B.rows.card : ℝ) ≤ C * (1 + height)^J *
          U^(unmarkedDensity (2*a-1) + 156*ε + εm + η) := by
  let : NeZero S.modulus := ⟨S.nonzero⟩
  exact fixed_dictionary_actual_batch_count S.modulus S.subgroup S.units S.exclusions
    S.profile S.smooth S.compact S.positiveSupport S.nonnegative S.nontrivial
    S.lower S.upper S.bound S.lowerPositive S.ordered S.boundPositive S.support S.bounded
    εm η hεm hη hβ
end SevenEighths.LocalMoment
end
end OAI
