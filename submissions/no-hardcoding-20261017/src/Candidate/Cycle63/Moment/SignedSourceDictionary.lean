import Candidate.LocalMoment.SignedRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Mask

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

/-- The original row is retained in the literal second-transform numerator. -/
def effectiveRow (u₀ e F G V h : O) : O := u₀ * e * F * G * V * h

theorem effectiveRow_coefficient (u₀ e F G V h : O) (I : Ideal O) :
    idealRowHom u₀ I * idealRowHom e I * idealRowHom F I *
      idealRowHom G I * idealRowHom V I * idealRowHom h I =
      idealRowHom (effectiveRow u₀ e F G V h) I := by
  simp only [effectiveRow, idealRowHom_argument_mul]

/-- This is an actual natural character, with its natural conductor bound.
The fixed sixth-power factor remains an Euler puncture. -/
theorem effectiveRow_natural (η : Character) (u₀ e F G V h : O)
    (hne : effectiveRow u₀ e F G V h ≠ 0) :
    ∃ χ : Character,
      χ.modulus.absNorm ≤ η.modulus.absNorm * fixedConductorFactor *
        (Ideal.span {effectiveRow u₀ e F G V h}).absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I = idealCoeff η I *
        idealRowHom (fixedBadMask^6) I * idealRowHom u₀ I *
          idealRowHom e I * idealRowHom F I * idealRowHom G I *
          idealRowHom V I * idealRowHom h I := by
  let Frow := naturalRow η (effectiveRow u₀ e F G V h) hne
  refine ⟨Frow.character, Frow.natural_modulus_bound, ?_⟩
  intro I
  rw [Frow.ideal]
  simp only [idealRowHom_argument_mul, effectiveRow]
  ring

/-- Regroup the signed coefficient before applying a norm or a row bound. -/
theorem signed_regroup {Label Row : Type*} [DecidableEq Label] [DecidableEq Row]
    (labels : Finset Label) (row : Label → Row) (coefficient : Label → ℂ)
    (character : Row → ℂ) :
    (∑ j ∈ labels, coefficient j * character (row j)) =
      ∑ w ∈ labels.image row,
        (∑ j ∈ labels.filter (fun j => row j = w), coefficient j) * character w := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem row hj)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

/-- First labels can remain inside each signed Hilbert coordinate. There is
no cardinality factor for the first-label set in this inequality. -/
theorem joint_signed_cauchy {Label Row : Type*}
    (labels : Finset Label) (rows : Finset Row)
    (left right : Label → Row → ℂ) :
    ‖∑ w ∈ rows, (∑ j ∈ labels, left j w) *
      star (∑ j ∈ labels, right j w)‖^2 ≤
      (∑ w ∈ rows, ‖∑ j ∈ labels, left j w‖^2) *
        ∑ w ∈ rows, ‖∑ j ∈ labels, right j w‖^2 := by
  have hn := norm_sum_le rows
    (fun w => (∑ j ∈ labels, left j w) * star (∑ j ∈ labels, right j w))
  simp only [norm_mul, norm_star] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq rows
      (fun w => ‖∑ j ∈ labels, left j w‖)
      (fun w => ‖∑ j ∈ labels, right j w‖))

/-- Arbitrary valuations are allowed: every factor of an exact product is
an ideal divisor. No squarefree hypothesis occurs. -/
theorem exact_product_factor_divisor {ι : Type*} [Fintype ι]
    (f : ι → Ideal O) (N : Ideal O) (h : ∏ i, f i = N) (i : ι) : f i ∣ N := by
  rw [← h]
  exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)

theorem exact_product_fibre_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tuples : Finset (ι → Ideal O)) (N : Ideal O) (hN : N ≠ 0) :
    (tuples.filter (fun f => ∏ i, f i = N)).card ≤
      (IdealMobiusDivisorSum.idealDivisors N).card ^ Fintype.card ι := by
  have hsub : tuples.filter (fun f => ∏ i, f i = N) ⊆
      Fintype.piFinset (fun _ : ι => IdealMobiusDivisorSum.idealDivisors N) := by
    intro f hf
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (IdealMobiusDivisorSum.mem_idealDivisors hN).mpr
      (exact_product_factor_divisor f N (Finset.mem_filter.mp hf).2 i)
  apply (Finset.card_le_card hsub).trans_eq
  simp

theorem exact_product_fibre_small_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ (tuples : Finset (ι → Ideal O)) (N : Ideal O), N ≠ 0 →
        (N.absNorm : ℝ) ≤ Z^B →
        ((tuples.filter (fun f => ∏ i, f i = N)).card : ℝ) ≤ C*Z^ε := by
  let k := Fintype.card ι
  let δ := ε / (k+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hdiv⟩ := CenteredMomentMask.polynomial_mask_divisor_bound δ B hδ hB
  refine ⟨C^k, pow_pos hC _, ?_⟩
  intro Z hZ tuples N hN hNZ
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hc : ((tuples.filter (fun f => ∏ i, f i = N)).card : ℝ) ≤
      ((IdealMobiusDivisorSum.idealDivisors N).card : ℝ)^k := by
    exact_mod_cast exact_product_fibre_card tuples N hN
  have hd := pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv Z hZ N hN hNZ) k
  have hexp : δ*(k:ℝ) ≤ ε := by
    dsimp [δ]
    have hk : (0:ℝ) < k+1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hk]
    nlinarith
  apply hc.trans (hd.trans ?_)
  rw [mul_pow, ← Real.rpow_mul_natCast hZp.le]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ hexp) (pow_nonneg hC.le _)

#print axioms effectiveRow_natural
#print axioms signed_regroup
#print axioms joint_signed_cauchy
#print axioms exact_product_fibre_card
#print axioms exact_product_fibre_small_power
end
end OAI.SevenEighths.Cycle63Moment
