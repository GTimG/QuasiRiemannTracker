/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.MaskedPairPoisson
import Candidate.Local.Qrh.JointDetector.RadialBilinear
import Candidate.Local.Qrh.JointDetector.PhysicalPairTail

/-! Finite selected reflection packets after fixing the source-mask divisor
and the bad-prime/unit frequency factor. This file binds actual Gauss and row
coefficients to the radial operator estimate. It does not discard bad
frequencies or assert an unproved decomposition of the infinite dual sum. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge GaussGeneratorTransport EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def frozenPairQuadCoefficient
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (sources labels : Finset (Ideal O))
    (a c : rows → ℂ) (w : sources → ℂ) (μ : labels → ℂ) (d b : O)
    (u : labels × sources × rows × rows) : ℂ :=
  let I := Ideal.span {u.2.2.1.val}
  let J := Ideal.span {u.2.2.2.val}
  if u.1.val ∣ I ∧ u.1.val ∣ J then
    μ u.1 * w u.2.1 * a u.2.2.1 * c u.2.2.2 *
      (admissibleUnaryGauss F hF I 1 * admissibleUnaryGauss F hF J 5 *
        primitivePair I J d * star (primitivePair I J (b * primaryGenerator u.2.1.val)))
  else 0

theorem frozenPairQuadCoefficient_eq
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (sources labels : Finset (Ideal O))
    (hrows : ∀ r : rows, Ideal.span {r.val} ∈ F)
    (hnonzero : ∀ r : rows, r.val ≠ 0)
    (hprimary : ∀ r : rows, lambda ^ 2 ∣ r.val - 1)
    (hmod : ∀ r s : rows, r.val - s.val ∈ (Ideal.span {(36 : O)} : Ideal O))
    (hsources : ∀ H : sources, Supported H.val)
    (a c : rows → ℂ) (w : sources → ℂ) (μ : labels → ℂ) (d b : O)
    (u : labels × sources × rows × rows) :
    frozenPairQuadCoefficient F hF rows sources labels a c w μ d b u =
      radialQuadCoefficient rows sources
        (idealDivisorMask labels (fun r : rows => Ideal.span {r.val}))
        (fun r => a r * maskedLeftDualCoefficient F hF d b (Ideal.span {r.val}))
        (fun r => c r * maskedRightDualCoefficient F hF d b (Ideal.span {r.val})) w μ u := by
  have hi := primaryGenerator_span u.2.2.1.val (hnonzero _) (hprimary _)
  have hj := primaryGenerator_span u.2.2.2.val (hnonzero _) (hprimary _)
  have he := masked_pair_actual_dual_arrays F hF (Ideal.span {u.2.2.1.val})
    (Ideal.span {u.2.2.2.val}) (hrows _) (hrows _) u.2.1.val (hsources _)
    (by simpa only [hi, hj] using hmod u.2.2.1 u.2.2.2) d b
  rw [hi, hj] at he
  rw [radialQuadCoefficient_eq_if]
  unfold frozenPairQuadCoefficient idealDivisorMask
  dsimp only
  split_ifs
  · rw [he]
    unfold selectedMatrix
    ring
  · rfl

private theorem weighted_energy_le {T : Type*} [Fintype T]
    (a q : T → ℂ) (hq : ∀ r, ‖q r‖ ≤ 1) :
    (∑ r, ‖a r * q r‖ ^ 2) ≤ ∑ r, ‖a r‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro r _
  have hh : ‖a r * q r‖ ≤ ‖a r‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hq r)
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

/-- Closed finite dyadic estimate for the ACTUAL frozen Poisson coefficient
array. The bound is uniform before the selected rows, arbitrary independent
vectors, common source mask, divisor labels, and frozen bad factor are chosen.
The row-divisor incidence loss is paid without counting the label universe. -/
theorem frozen_pair_radial_bound (W : 𝓢(ℝ, ℂ)) (decay : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (rows : Finset O) (sources labels : Finset (Ideal O))
        (_hrows : ∀ r : rows, Ideal.span {r.val} ∈ F)
        (_hnonzero : ∀ r : rows, r.val ≠ 0)
        (_hprimary : ∀ r : rows, lambda ^ 2 ∣ r.val - 1)
        (_hmod : ∀ r s : rows, r.val - s.val ∈ (Ideal.span {(36 : O)} : Ideal O))
        (_hsources : ∀ H : sources, Supported H.val)
        (a c : rows → ℂ) (w : sources → ℂ) (μ : labels → ℂ) (d b : O)
        (x : rows → ℝ) (z : sources → ℝ) (Bheight ε : ℝ)
        (_hB : 0 ≤ Bheight) (hε : 0 < ε)
        (_hnorm : ∀ r : rows, (Ideal.absNorm (Ideal.span {r.val}) : ℝ) ≤ Bheight)
        (_hw : ∀ H, ‖w H‖ ≤ 1) (_hμ : ∀ e, ‖μ e‖ ≤ 1)
        (_hx : ∀ r, x r ∈ Set.Icc (1 : ℝ) 2)
        (_hz : ∀ H, z H ∈ Set.Icc (1 : ℝ) 2),
      ‖∑ u : labels × sources × rows × rows,
        frozenPairQuadCoefficient F hF rows sources labels a c w μ d b u *
          paperRadialFourier W (R * z u.2.1 / (x u.2.2.1 * x u.2.2.2))‖ ≤
        (C / (1 + R)^decay) * selectedNorm rows sources *
          (idealDivisorConstant ε hε * Bheight^ε) *
          Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2) := by
  obtain ⟨C, hC, hbound⟩ := radial_idealDivisor_bilinear_bound W decay
  refine ⟨C, hC, ?_⟩
  intro R hR F hF rows sources labels hrows hnonzero hprimary hmod hsources
    a c w μ d b x z Bheight ε hB hε hnorm hw hμ hx hz
  simp_rw [frozenPairQuadCoefficient_eq F hF rows sources labels hrows hnonzero
    hprimary hmod hsources a c w μ d b]
  have hh := hbound R hR rows sources labels
    (fun r => a r * maskedLeftDualCoefficient F hF d b (Ideal.span {r.val}))
    (fun r => c r * maskedRightDualCoefficient F hF d b (Ideal.span {r.val}))
    w μ x z Bheight ε hB hε hnonzero hnorm hw hμ hx hz
  apply hh.trans
  have ha := weighted_energy_le a
    (fun r => maskedLeftDualCoefficient F hF d b (Ideal.span {r.val}))
    (fun r => maskedLeftDualCoefficient_norm_le F hF d b (Ideal.span {r.val}))
  have hc := weighted_energy_le c
    (fun r => maskedRightDualCoefficient F hF d b (Ideal.span {r.val}))
    (fun r => maskedRightDualCoefficient_norm_le F hF d b (Ideal.span {r.val}))
  have hK := selectedNorm_nonneg rows sources
  have hD := (idealDivisorConstant_pos ε hε).le
  gcongr

def frozenPhysicalScale (L B Y : ℝ) (d b : O) : ℝ :=
  L * ‖eisEmbedding b‖ ^ 2 * Y / (‖eisEmbedding d‖ ^ 2 * B ^ 2)

theorem frozen_frequency_norm_sq (b : O) (H : Ideal O) (hH : Supported H) :
    ‖eisEmbedding (b * primaryGenerator H)‖ ^ 2 =
      ‖eisEmbedding b‖ ^ 2 * (Ideal.absNorm H : ℝ) := by
  rw [map_mul, norm_mul, mul_pow,
    primaryGenerator_norm_sq H (supported_primaryGenerator_ne_zero H hH)]

/-- Match the genuine pair-dependent scale, including the frozen bad factor,
to the three dyadic coordinates used by the proved radial separation. -/
theorem frozen_physical_argument (L B Y : ℝ) (hB : B ≠ 0) (hY : Y ≠ 0)
    (d b : O) (I J H : Ideal O) (hH : Supported H) :
    L * ‖eisEmbedding (b * primaryGenerator H)‖ ^ 2 /
        (‖eisEmbedding d‖ ^ 2 * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ))) =
      frozenPhysicalScale L B Y d b * ((Ideal.absNorm H : ℝ) / Y) /
        (((Ideal.absNorm I : ℝ) / B) * ((Ideal.absNorm J : ℝ) / B)) := by
  rw [frozen_frequency_norm_sq b H hH]
  unfold frozenPhysicalScale
  field_simp

theorem physical_prefactor_separated (L D B n m : ℝ)
    (hB : 0 < B) (hn : 0 ≤ n) :
    L / (D * Real.sqrt (n * m)) =
      (L / (D * B)) * Real.sqrt (B / n) * Real.sqrt (B / m) := by
  have hs : Real.sqrt (B / n) * Real.sqrt (B / m) = B / Real.sqrt (n * m) := by
    rw [Real.sqrt_div hB.le, Real.sqrt_div hB.le, Real.sqrt_mul hn]
    calc
      _ = (Real.sqrt B)^2 / (Real.sqrt n * Real.sqrt m) := by ring
      _ = _ := by rw [Real.sq_sqrt hB.le]
  rw [mul_assoc, hs]
  field_simp

private theorem sqrt_row_weight_norm_le (B n : ℝ) (hB : 0 < B) (hn : B ≤ n) :
    ‖(Real.sqrt (B / n) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr ((div_le_one (hB.trans_le hn)).mpr hn)

/-- The finite physical shell bound, with the exact Poisson prefactor and
the actual frequency `b * primaryGenerator H`. The bad factor is arbitrary
and nonzero; this theorem neither deletes it nor charges its sectors for free. -/
theorem frozen_pair_physical_bound (W : 𝓢(ℝ, ℂ)) (decay : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (rows : Finset O) (sources labels : Finset (Ideal O))
        (_hrows : ∀ r : rows, Ideal.span {r.val} ∈ F)
        (_hnonzero : ∀ r : rows, r.val ≠ 0)
        (_hprimary : ∀ r : rows, lambda ^ 2 ∣ r.val - 1)
        (_hmod : ∀ r s : rows, r.val - s.val ∈ (Ideal.span {(36 : O)} : Ideal O))
        (_hsources : ∀ H : sources, Supported H.val)
        (a c : rows → ℂ) (w : sources → ℂ) (μ : labels → ℂ) (d b : O)
        (_hd : d ≠ 0) (_hb : b ≠ 0) (L B Y ε : ℝ)
        (_hL : 0 < L) (_hB : 0 < B) (_hY : 0 < Y) (hε : 0 < ε)
        (_hrowNorm : ∀ r : rows, (Ideal.absNorm (Ideal.span {r.val}) : ℝ) ∈ Set.Icc B (2 * B))
        (_hsourceNorm : ∀ H : sources, (Ideal.absNorm H.val : ℝ) ∈ Set.Icc Y (2 * Y))
        (_hw : ∀ H, ‖w H‖ ≤ 1) (_hμ : ∀ e, ‖μ e‖ ≤ 1),
      ‖∑ u : labels × sources × rows × rows,
        ((L / (‖eisEmbedding d‖ ^ 2 * Real.sqrt
          ((Ideal.absNorm (Ideal.span {u.2.2.1.val}) : ℝ) *
            (Ideal.absNorm (Ideal.span {u.2.2.2.val}) : ℝ))) : ℝ) : ℂ) *
        frozenPairQuadCoefficient F hF rows sources labels a c w μ d b u *
        paperRadialFourier W (L * ‖eisEmbedding (b * primaryGenerator u.2.1.val)‖ ^ 2 /
          (‖eisEmbedding d‖ ^ 2 * ((Ideal.absNorm (Ideal.span {u.2.2.1.val}) : ℝ) *
            (Ideal.absNorm (Ideal.span {u.2.2.2.val}) : ℝ))))‖ ≤
        (L / (‖eisEmbedding d‖ ^ 2 * B)) *
          (C / (1 + frozenPhysicalScale L B Y d b)^decay) * selectedNorm rows sources *
          (idealDivisorConstant ε hε * (2 * B)^ε) *
          Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2) := by
  obtain ⟨C, hC, hbound⟩ := frozen_pair_radial_bound W decay
  refine ⟨C, hC, ?_⟩
  intro F hF rows sources labels hrows hnonzero hprimary hmod hsources
    a c w μ d b hd hb L B Y ε hL hB hY hε hrowNorm hsourceNorm hw hμ
  let q : rows → ℂ := fun r => (Real.sqrt (B / (Ideal.absNorm (Ideal.span {r.val}) : ℝ)) : ℂ)
  let R := frozenPhysicalScale L B Y d b
  let K := L / (‖eisEmbedding d‖ ^ 2 * B)
  have hdn : 0 < ‖eisEmbedding d‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hbn : 0 < ‖eisEmbedding b‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hb))
  have hR : 0 < R := by dsimp [R, frozenPhysicalScale]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq (r : rows) : ‖q r‖ ≤ 1 := sqrt_row_weight_norm_le B _ hB (hrowNorm r).1
  have hx (r : rows) : (Ideal.absNorm (Ideal.span {r.val}) : ℝ) / B ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · exact (one_le_div hB).mpr (hrowNorm r).1
    · exact (div_le_iff₀ hB).mpr (hrowNorm r).2
  have hz (H : sources) : (Ideal.absNorm H.val : ℝ) / Y ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · exact (one_le_div hY).mpr (hsourceNorm H).1
    · exact (div_le_iff₀ hY).mpr (hsourceNorm H).2
  have ht := hbound R hR F hF rows sources labels hrows hnonzero hprimary hmod hsources
    (fun r => a r * q r) (fun r => c r * q r) w μ d b
    (fun r => (Ideal.absNorm (Ideal.span {r.val}) : ℝ) / B)
    (fun H => (Ideal.absNorm H.val : ℝ) / Y) (2 * B) ε (by positivity) hε
    (fun r => (hrowNorm r).2) hw hμ hx hz
  have he (u : labels × sources × rows × rows) :
      ((L / (‖eisEmbedding d‖ ^ 2 * Real.sqrt
          ((Ideal.absNorm (Ideal.span {u.2.2.1.val}) : ℝ) *
            (Ideal.absNorm (Ideal.span {u.2.2.2.val}) : ℝ))) : ℝ) : ℂ) *
        frozenPairQuadCoefficient F hF rows sources labels a c w μ d b u =
      (K : ℂ) * frozenPairQuadCoefficient F hF rows sources labels
        (fun r => a r * q r) (fun r => c r * q r) w μ d b u := by
    rw [physical_prefactor_separated L (‖eisEmbedding d‖ ^ 2) B _ _ hB (Nat.cast_nonneg _)]
    push_cast
    unfold frozenPairQuadCoefficient
    dsimp only
    split_ifs <;> dsimp [q, K] <;> push_cast <;> ring
  simp_rw [he, frozen_physical_argument L B Y hB.ne' hY.ne' d b _ _ _ (hsources _)]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
  have ha := weighted_energy_le a q hq
  have hc := weighted_energy_le c q hq
  have hN := selectedNorm_nonneg rows sources
  have hD := (idealDivisorConstant_pos ε hε).le
  calc
    _ ≤ K * ((C / (1 + R)^decay) * selectedNorm rows sources *
        (idealDivisorConstant ε hε * (2 * B)^ε) *
        Real.sqrt (∑ r, ‖a r * q r‖^2) * Real.sqrt (∑ r, ‖c r * q r‖^2)) :=
      mul_le_mul_of_nonneg_left ht hK
    _ ≤ K * ((C / (1 + R)^decay) * selectedNorm rows sources *
        (idealDivisorConstant ε hε * (2 * B)^ε) *
        Real.sqrt (∑ r, ‖a r‖^2) * Real.sqrt (∑ r, ‖c r‖^2)) := by gcongr
    _ = _ := by dsimp [K, R]; ring

theorem primitivePair_norm_le (I J : Ideal O) (h : O) : ‖primitivePair I J h‖ ≤ 1 := by
  rw [primitivePair, norm_mul, norm_star]
  simpa only [one_mul] using mul_le_mul (idealRowHom_norm h I)
    (idealRowHom_norm h J) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- The tail of an actual Möbius mode, at its reduced physical scale
`Ld = L / Nd`. Frequencies are arbitrary elements, including every bad-prime
and unit sector; there is no supported-source restriction on this tail. -/
theorem actual_mask_mode_tail_power (W : 𝓢(ℝ, ℂ)) (ε N P Crows : ℝ)
    (hε : 0 < ε) (hP : 0 ≤ P) (hCrows : 0 < Crows) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (Z B Ld : ℝ),
      2 ≤ Z → 1 ≤ B → B ≤ Z ^ P → Z ^ (-P) ≤ Ld → Ld ≤ Z ^ P →
      (F.card : ℝ) ≤ Crows * B →
      (∀ I : F, B ≤ (Ideal.absNorm I.val : ℝ)) →
      (∀ I : F, (Ideal.absNorm I.val : ℝ) ≤ 2 * B) →
      ∀ (frequencies : Set O),
      (∀ h ∈ frequencies, (4 * B ^ 2 / Ld) * Z ^ ε ≤ ‖eisEmbedding h‖ ^ 2) →
      ∀ (d : O) (phase : ℂ), ‖phase‖ ≤ 1 → ∀ a : F → ℂ,
      ‖∑ I : F, ∑ J : F, (a I * star (a J)) *
        ∑' h : frequencies,
          (((Ld / Real.sqrt ((Ideal.absNorm I.val : ℝ) * (Ideal.absNorm J.val : ℝ)) : ℝ) : ℂ) *
            (phase * admissibleUnaryGauss F hF I.val 1 * admissibleUnaryGauss F hF J.val 5 *
              primitivePair I.val J.val d * star (primitivePair I.val J.val h.val))) *
          paperRadialFourier W
            ((Ld / ((Ideal.absNorm I.val : ℝ) * (Ideal.absNorm J.val : ℝ))) *
              ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        Ctail * Z ^ (-N) * ∑ I : F, ‖a I‖ ^ 2 := by
  obtain ⟨Ctail, hCtail, ht⟩ := physical_pair_radial_tail_power W ε N P Crows hε hP hCrows
  refine ⟨Ctail, hCtail, ?_⟩
  intro F hF Z B Ld hZ hB hBU hLlo hLhi hcard hlo hhi frequencies hfreq d phase hphase a
  apply ht Z B Ld hZ hB hBU hLlo hLhi (by simpa only [Fintype.card_coe] using hcard)
    (fun I : F => (Ideal.absNorm I.val : ℝ)) hlo hhi frequencies hfreq
    (fun I J h => phase * admissibleUnaryGauss F hF I.val 1 * admissibleUnaryGauss F hF J.val 5 *
      primitivePair I.val J.val d * star (primitivePair I.val J.val h)) ?_ a
  intro I J h _
  simp only [norm_mul, norm_star,
    admissibleUnaryGauss_norm F hF I.val 1 (by decide) (by decide),
    admissibleUnaryGauss_norm F hF J.val 5 (by decide) (by decide), mul_one]
  have h1 := mul_le_mul hphase (primitivePair_norm_le I.val J.val d)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h2 := mul_le_mul h1 (primitivePair_norm_le I.val J.val h)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)
  simpa only [one_mul] using h2

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.frozenPairQuadCoefficient_eq
#print axioms Qrh.JointDetector.frozen_pair_radial_bound
#print axioms Qrh.JointDetector.frozen_pair_physical_bound
#print axioms Qrh.JointDetector.actual_mask_mode_tail_power
