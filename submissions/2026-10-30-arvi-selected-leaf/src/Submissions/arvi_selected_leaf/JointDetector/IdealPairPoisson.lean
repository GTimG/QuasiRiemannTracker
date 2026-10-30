/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.PairPoisson
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.UnitNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.RowCompletion.CubicReopening

/-! Unit-compatible passage to ordinary ideal sources. The common ideal mask
is retained verbatim. These are reindexing identities, not an analytic bound. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge GaussGeneratorTransport UniqueFactorizationMonoid
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def primitivePair (A B : Ideal O) (n : O) : ℂ :=
  idealRowHom n A * star (idealRowHom n B)

/-- Full unit compatibility follows from the actual norm residue modulo 36,
not merely from the quadratic reciprocity-ray state. -/
theorem primitivePair_unit_of_norm_mod36 (A B : Ideal O) (hA : A ≠ 0) (hB : B ≠ 0)
    (hgA : ∀ P ∈ normalizedFactors A,
      P.IsMaximal ∧ lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2)
    (hgB : ∀ P ∈ normalizedFactors B,
      P.IsMaximal ∧ lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2)
    (hmod : A.absNorm % 36 = B.absNorm % 36) (u : Oˣ) :
    primitivePair A B u.val = 1 := by
  have he := CanonicalUnitEuler.idealRowHom_unit_eq_of_norm_mod_thirty_six
    u A B hA hB hgA hgB hmod
  have hn : ‖idealRowHom u.val B‖ = 1 := by
    rw [CanonicalUnitEuler.idealRowHom_unit_norm u B hB hgB, map_pow, norm_pow,
      norm_eisEmbedding_unit, one_pow]
  have hs : star (idealRowHom u.val B) = (idealRowHom u.val B)⁻¹ :=
    (Complex.inv_eq_conj hn).symm
  unfold primitivePair
  rw [he, hs, mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; norm_num))]

theorem primitivePair_unit_mul (A B : Ideal O)
    (hu : ∀ u : Oˣ, primitivePair A B u.val = 1) (u : Oˣ) (n : O) :
    primitivePair A B (u.val * n) = primitivePair A B n := by
  unfold primitivePair
  rw [idealRowHom_argument_mul, idealRowHom_argument_mul, star_mul]
  calc
    _ = primitivePair A B u.val * primitivePair A B n := by unfold primitivePair; ring
    _ = _ := by rw [hu, one_mul]; rfl

theorem primitivePair_unit_of_congruent_mod36 (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hmod : a - b ∈ (Ideal.span {(36 : O)} : Ideal O)) (u : Oˣ) :
    primitivePair (Ideal.span {a}) (Ideal.span {b}) u.val = 1 := by
  have hgood (I : Ideal O) (hI : Supported I) :
      ∀ P ∈ normalizedFactors I,
        P.IsMaximal ∧ lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 := by
    intro P hP
    have hp := prime_of_normalized_factor P hP
    exact ⟨(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero, hI.2 P hP⟩
  exact primitivePair_unit_of_norm_mod36 _ _ ha.1 hb.1
    (hgood _ ha) (hgood _ hb) (CanonicalUnitEuler.norm_residue_congruent 36 a b hmod) u

def maskedPairRadial (A B : Ideal O) (mask : Ideal O → ℂ)
    (W : ℝ → ℂ) (L : ℝ) (n : O) : ℂ :=
  mask (Ideal.span {n}) * primitivePair A B n * W (‖eisEmbedding n‖ ^ 2 / L)

theorem maskedPairRadial_summable (A B : Ideal O) (mask : Ideal O → ℂ)
    (hmask : ∀ I, ‖mask I‖ ≤ 1) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    Summable (maskedPairRadial A B mask W L) := by
  have hw : Summable (fun n : O => ‖W (‖eisEmbedding n‖ ^ 2 / L)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W L hL)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hw
  intro n
  have hp : ‖primitivePair A B n‖ ≤ 1 := by
    simpa only [primitivePair, norm_mul, norm_star, one_mul] using
      mul_le_mul (idealRowHom_norm n A) (idealRowHom_norm n B)
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  unfold maskedPairRadial
  rw [norm_mul, norm_mul]
  have hc : ‖mask (Ideal.span {n})‖ * ‖primitivePair A B n‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul (hmask (Ideal.span {n})) hp
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc
    (norm_nonneg (W (‖eisEmbedding n‖ ^ 2 / L)))

theorem maskedPairRadial_unit_mul (A B : Ideal O) (mask : Ideal O → ℂ)
    (W : ℝ → ℂ) (L : ℝ)
    (hu : ∀ u : Oˣ, primitivePair A B u.val = 1) (u : Oˣ) (n : O) :
    maskedPairRadial A B mask W L (u.val * n) = maskedPairRadial A B mask W L n := by
  unfold maskedPairRadial
  rw [Ideal.span_singleton_mul_left_unit u.isUnit,
    primitivePair_unit_mul A B hu, norm_eisEmbedding_unit_mul]

/-- The lambda mask is explicit; every further common ideal mask remains inside
both sums. The ideal source is not projected to squarefree ideals. -/
theorem masked_pair_primary_reindex (A B : Ideal O) (mask : Ideal O → ℂ)
    (W : ℝ → ℂ) (L : ℝ)
    (hu : ∀ u : Oˣ, primitivePair A B u.val = 1)
    (hs : Summable (maskedPairRadial A B mask W L)) :
    (∑' n : O, if lambda ∣ n then 0 else maskedPairRadial A B mask W L n) =
      (Nat.card Oˣ : ℂ) * ∑' I : PrimaryIdealUnitReindex.GoodIdeal,
        mask I.val * primitivePair A B (primaryGenerator I.val) *
          W ((I.val.absNorm : ℝ) / L) := by
  rw [PrimaryIdealUnitReindex.tsum_ramified_mask_unit_invariant
    (maskedPairRadial A B mask W L) hs
    (fun u I => maskedPairRadial_unit_mul A B mask W L hu u (primaryGenerator I.val))]
  congr 1
  apply tsum_congr
  intro I
  unfold maskedPairRadial
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I.val I.property).1]

/-- On the supported common mask, the primary-generator pair is exactly the
original `idealRowHom a I * conj (idealRowHom b I)` ordinary-source pair. -/
theorem masked_actual_pair_reindex (a b : O)
    (hpa : lambda ^ 2 ∣ a - 1) (hpb : lambda ^ 2 ∣ b - 1)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hray : residue a = residue b) (mask : Ideal O → ℂ)
    (hmask : ∀ I, ¬ Supported I → mask I = 0)
    (W : ℝ → ℂ) (L : ℝ)
    (hu : ∀ u : Oˣ, primitivePair (Ideal.span {a}) (Ideal.span {b}) u.val = 1)
    (hs : Summable (maskedPairRadial (Ideal.span {a}) (Ideal.span {b}) mask W L)) :
    (∑' n : O, if lambda ∣ n then 0 else
      maskedPairRadial (Ideal.span {a}) (Ideal.span {b}) mask W L n) =
      (Nat.card Oˣ : ℂ) * ∑' I : PrimaryIdealUnitReindex.GoodIdeal,
        mask I.val * (idealRowHom a I.val * star (idealRowHom b I.val)) *
          W ((I.val.absNorm : ℝ) / L) := by
  rw [masked_pair_primary_reindex _ _ mask W L hu hs]
  congr 1
  apply tsum_congr
  intro I
  by_cases hI : Supported I.val
  · have hp := primaryGenerator_spec I.val I.property
    have hn : Supported (Ideal.span {primaryGenerator I.val}) := hp.1.symm ▸ hI
    have he := same_ray_pair_orientation a b (primaryGenerator I.val)
      hpa hpb hp.2 ha hb hn hray
    rw [hp.1] at he
    unfold primitivePair
    rw [← he]
  · rw [hmask I.val hI, zero_mul, zero_mul, zero_mul, zero_mul]

theorem masked_actual_pair_all_ideals (a b : O)
    (hpa : lambda ^ 2 ∣ a - 1) (hpb : lambda ^ 2 ∣ b - 1)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hray : residue a = residue b) (mask : Ideal O → ℂ)
    (hmask : ∀ I, ¬ Supported I → mask I = 0)
    (W : ℝ → ℂ) (L : ℝ)
    (hu : ∀ u : Oˣ, primitivePair (Ideal.span {a}) (Ideal.span {b}) u.val = 1)
    (hs : Summable (maskedPairRadial (Ideal.span {a}) (Ideal.span {b}) mask W L)) :
    (∑' n : O, if lambda ∣ n then 0 else
      maskedPairRadial (Ideal.span {a}) (Ideal.span {b}) mask W L n) =
      (Nat.card Oˣ : ℂ) * ∑' I : Ideal O,
        mask I * (idealRowHom a I * star (idealRowHom b I)) * W ((I.absNorm : ℝ) / L) := by
  rw [masked_actual_pair_reindex a b hpa hpb ha hb hray mask hmask W L hu hs]
  congr 1
  apply tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | primaryGenerator I ≠ 0})
    (f := fun I : Ideal O => mask I * (idealRowHom a I * star (idealRowHom b I)) *
      W ((I.absNorm : ℝ) / L))
  intro I hI
  have hsI : Supported I := by
    by_contra hn
    exact hI (by dsimp; rw [hmask I hn, zero_mul, zero_mul])
  exact supported_primaryGenerator_ne_zero I hsI

/-- The actual modulo-36 hypothesis discharges both the unit compatibility and
the quadratic-ray cancellation; the arbitrary bounded bad-place mask survives. -/
theorem masked_actual_pair_mod36 (a b : O)
    (hpa : lambda ^ 2 ∣ a - 1) (hpb : lambda ^ 2 ∣ b - 1)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hmod : a - b ∈ (Ideal.span {(36 : O)} : Ideal O))
    (mask : Ideal O → ℂ) (hmask : ∀ I, ¬ Supported I → mask I = 0)
    (hm : ∀ I, ‖mask I‖ ≤ 1) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    (∑' n : O, if lambda ∣ n then 0 else
      maskedPairRadial (Ideal.span {a}) (Ideal.span {b}) mask W L n) =
      (6 : ℂ) * ∑' I : Ideal O,
        mask I * (idealRowHom a I * star (idealRowHom b I)) * W ((I.absNorm : ℝ) / L) := by
  have hfour : (4 : O) ∣ a - b :=
    (show (4 : O) ∣ (36 : O) from ⟨9, by norm_num⟩).trans
      (Ideal.mem_span_singleton.mp hmod)
  have hray := QuadraticGaussRay.residue_eq_of_four_dvd_sub a b hfour
  have h := masked_actual_pair_all_ideals a b hpa hpb ha hb hray mask hmask W L
    (primitivePair_unit_of_congruent_mod36 a b ha hb hmod)
    (maskedPairRadial_summable _ _ mask hm W L hL)
  simpa only [PrimaryIdealUnitReindex.card_units_eq_six, Nat.cast_ofNat] using h

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.primitivePair_unit_of_norm_mod36
#print axioms Qrh.JointDetector.masked_actual_pair_reindex
#print axioms Qrh.JointDetector.masked_actual_pair_all_ideals
#print axioms Qrh.JointDetector.masked_actual_pair_mod36
