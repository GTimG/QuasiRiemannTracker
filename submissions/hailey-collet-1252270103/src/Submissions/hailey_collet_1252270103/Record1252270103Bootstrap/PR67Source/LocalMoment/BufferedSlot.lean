import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeRay
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSlots
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! Buffered pointwise payment for the literal natural prime slots.  The
additional common puncture remains inside the actual row character. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDyadic HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance bufferedSlotFinite : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The existing buffered prime estimate pays a genuine natural relative
slot at the local bin parameter `2*a-1`.  The original puncture, zero
extensions, real norm power, and the independent two frequency parameters
are retained exactly. -/
theorem natural_relative_slot_buffered_bound
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1 / 1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8 * e * Rwidth + κ ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax →
      2 ≤ Z ^ d → 2 < Z ^ τ →
      ∀ (ηrow : Character) (z : O) (F : NaturalRow ηrow z)
        (η₀ : Character) (puncture : Ideal O), puncture ≠ 0 →
      let χ := (excluded F.character puncture).product η₀.inverse
      ∀ (hχ : ∀ θ : RayQuotient.Characters M H,
        (twistedFamily M H hH χ θ).residue ≠ 1) (a : ℝ) (i : ℕ),
        51 / 100 ≤ a → a ≤ 1 →
        HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH χ) hχ
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e →
      ∀ r σ t v : ℝ, 0 ≤ r → r ≤ Rwidth → σmin ≤ σ → σ ≤ σmax →
        2 * (|Real.log A| + |Real.log B|) + 1 ≤ Real.log ((Z ^ d) ^ r) →
        (∀ θ : RayQuotient.Characters M H,
          (twistedFamily M H hH χ θ).modulus.absNorm ≤ Z ^ d) →
        |t + v| + Z ^ τ / 2 ≤ (3 * i + 2 : ℕ) * Z ^ τ →
        (3 + (3 * i + 2 : ℕ) * Z ^ τ) ^ 2 ≤ (Z ^ d) ^ η →
        ‖normalizedSlot ηrow (fixedBadMask * idealGenerator puncture) 1 z
          (primePool M H B ((Z ^ d) ^ r))
          (fun I => idealCoeff η₀.inverse I *
            annularWeight W ((Z ^ d) ^ r) σ v I) t ((Z ^ d) ^ r)‖ ^ 2 ≤
          C ^ 2 * (Z ^ d) ^ ((2 * a - 1) * r + 2 * ε) := by
  obtain ⟨C, hC, hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax hRw hdmax hτ hε he he' hκ hη hbudget
  refine ⟨C, hC, ?_⟩
  intro Z d hZ hd hd' hbase hT ηrow z F η₀ puncture hpuncture
    χ hχ a i ha ha' hmax r σ t v hr hr' hσ hσ' hlarge hmod hfreq hheight
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hbasep : 0 < Z ^ d := Real.rpow_pos_of_pos hZp d
  have hscale : 0 < (Z ^ d) ^ r := Real.rpow_pos_of_pos hbasep r
  have hb := hbound Z d hZ hd hd' hbase hT χ hχ a i ha ha' hmax
    r σ (t + v) hr hr' hσ hσ' hlarge hmod hfreq hheight
  rw [relative_normalizedSlot_eq_ray M H ηrow (excluded F.character puncture)
    η₀.inverse (fixedBadMask * idealGenerator puncture) 1 z
    (by simpa only [one_mul] using F.masked_element puncture hpuncture)
    W B ((Z ^ d) ^ r) σ t v hscale, norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power ((Z ^ d) ^ r) t hscale, one_mul]
  apply (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq
  rw [mul_pow, pow_two ((Z ^ d) ^ ((a - 1 / 2) * r + ε)),
    ← Real.rpow_add hbasep]
  congr 2
  ring

end SevenEighths.LocalMoment
end
end OAI

end Record1252270103Bootstrap.PR67
