import ZetaZeroFree.Analytic.Moments.CompactProfiles
import ZetaZeroFree.Analytic.Moments.Presentation
import ZetaZeroFree.Analytic.Moments.Unconditional
import OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState

namespace ZetaZeroFree.Analytic.Moments.D3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ZetaZeroFree.Analytic.Moments
open HeckeFamily HeckeDyadic CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorPlainFiberSource
open Filter QuadraticInitialBound
local notation "O" => HeckeFamily.O

/-- A fixed arithmetic anchor removes all auxiliary fixed-ray parameters from the moment theorem. -/
theorem unconditional_all_nonprincipal
    (a b radial B L Mcap ε : ℝ)
    (ha : 0 < a) (haUpper : a ≤ 1 / 4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hB : 0 ≤ B) (hM : 0 < Mcap) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ AllNonprincipalAt a b radial B L Mcap ε Z J S C := by
  let Q : Ideal O := Ideal.span {ConcretePrimeRowBridge.goodLambda} ⊓ Ideal.span {(72 : O)}
  have hQ0 : Q ≠ 0 := Ideal.inf_ne_bot_of_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr ConcretePrimeRowBridge.goodLambda_prime.ne_zero)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72 : O) ≠ 0))
  have hQt : Q ≠ ⊤ := by
    intro h
    have htop : Ideal.span {ConcretePrimeRowBridge.goodLambda} = ⊤ :=
      top_le_iff.mp (h ▸ (inf_le_left : Q ≤ _))
    exact ConcretePrimeRowBridge.goodLambda_prime.not_isUnit
      (Ideal.span_singleton_eq_top.mp htop)
  letI : NeZero Q := ⟨hQ0⟩
  let η₀ := HeckeRayFamily.character Q 1
  exact Unconditional.all_nonprincipal_at Q a b radial B L Mcap ε
    ha haUpper hb hrad hB hM hε η₀ Q le_rfl
    (internalQ_ne_zero Q hQ0 η₀) (internalQ_ne_top Q hQt η₀)
    (inf_le_left.trans (inf_le_right : Q ≤ Ideal.span {(72 : O)}))

/-- The unconditional sharp mixed moment, with the exact m+q+epsilon exponent.
The smooth order and constant precede every moving character, support, puncture,
row set, length and independent norm-twist height. -/
theorem mixed_plain_moment (a b B L Mcap ε Cfixed : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hM : 0 < Mcap) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ m q : ℝ, 0 ≤ m → 0 ≤ q → m + q ≤ Mcap →
      ∀ η : Character, (η.modulus.absNorm : ℝ) ≤ Cfixed * Z ^ q →
      ∀ R : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z ^ B →
      ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0) →
        (∀ z ∈ rows, (naturalPlainCharacter η z).residue ≠ 1) →
        (∀ z ∈ rows, ((Ideal.span {z}).absNorm : ℝ) ≤ Z ^ m) →
      ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
        ∑ z ∈ rows,
          ‖polynomial (excluded (naturalPlainCharacter η z) R) false W₁ X₁ 0 t₁ *
            polynomial (excluded (naturalPlainCharacter η z) R) false W₂ X₂ 0 t₂‖ ^ 2 ≤
          C * (compactNorm J W₁ * compactNorm J W₂) ^ 2 *
            (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + q + ε) := by
  let a₀ := min a (1 / 4 : ℝ)
  let b₀ := max b (1 : ℝ)
  have ha₀ : 0 < a₀ := lt_min ha (by norm_num)
  have haUpper : a₀ ≤ 1 / 4 := min_le_right _ _
  have hb₀ : 1 ≤ b₀ := le_max_right _ _
  obtain ⟨radial, hradial, hΦs⟩ :=
    CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  obtain ⟨Jh, S, C₀, hC₀, hend⟩ := unconditional_all_nonprincipal
    a₀ b₀ radial B L (Mcap + ε / 2) (ε / 2) ha₀ haUpper hb₀ hradial hB
    (by linarith) (by linarith)
  let J := max Jh (S.sup Prod.snd)
  let K := supportRadius a₀ b₀ ^ (S.sup Prod.fst)
  have hK : 0 ≤ K := pow_nonneg (zero_le_one.trans (supportRadius_ge_one a₀ b₀)) _
  let C := C₀ * diagonalControl radialMajorant * K ^ 4 + 1
  have hCbase : 0 ≤ C₀ * diagonalControl radialMajorant * K ^ 4 :=
    mul_nonneg (mul_nonneg hC₀.le (diagonalControl_nonneg _)) (pow_nonneg hK _)
  refine ⟨J, C, by dsimp [C]; linarith, ?_⟩
  filter_upwards [hend, eventually_fixed_factor Cfixed (ε / 2) (by linarith)]
    with Z hZ hfixed
  refine ⟨hZ.1, ?_⟩
  intro m q hm hq hmq η hη R hR hRnorm rows hrows hnp hnorm
    W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hL₁ hL₂
  have hsupport (W : 𝓢(ℝ, ℂ))
      (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) :
      Function.support (W : ℝ → ℂ) ⊆ Set.Icc a₀ b₀ := by
    intro x hx
    exact ⟨(min_le_left _ _).trans (hs hx).1, (hs hx).2.trans (le_max_left _ _)⟩
  have hs₁' := hsupport W₁ hs₁
  have hs₂' := hsupport W₂ hs₂
  have he := finite_mixed_from_all_nonprincipal a₀ b₀ radial B L Mcap (ε / 2)
    Z Cfixed (ε / 2) m q Jh S C₀ hZ.1.le hm hq hmq (by linarith) hfixed hZ.2
    η hη R hR hRnorm radialMajorant hΦs radialMajorant_nonneg radialMajorant_one
    rows hrows hnp hnorm W₁ W₂ (zero_le_one.trans hb₀) hs₁' hs₂' X₁ X₂ t₁ t₂ hX₁ hX₂ hL₁ hL₂
  have hp₁ : S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁ ≤ K * compactNorm J W₁ :=
    finite_schwartz_le_compactNorm_of_order a₀ b₀ S J (le_max_right _ _) W₁ hs₁'
  have hp₂ : S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂ ≤ K * compactNorm J W₂ :=
    finite_schwartz_le_compactNorm_of_order a₀ b₀ S J (le_max_right _ _) W₂ hs₂'
  have hpair :
      ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 ≤
      K ^ 4 * (compactNorm J W₁ * compactNorm J W₂) ^ 2 := by
    have hp := mul_le_mul hp₁ hp₂ (apply_nonneg _ _) (mul_nonneg hK (compactNorm_nonneg _ _))
    have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp 2
    convert hh using 1 <;> ring
  have ht₁ : (1 + ‖t₁‖) ^ Jh ≤ (1 + ‖t₁‖) ^ J :=
    pow_le_pow_right₀ (by linarith [norm_nonneg t₁]) (le_max_left _ _)
  have ht₂ : (1 + ‖t₂‖) ^ Jh ≤ (1 + ‖t₂‖) ^ J :=
    pow_le_pow_right₀ (by linarith [norm_nonneg t₂]) (le_max_left _ _)
  have hdiag := diagonalControl_nonneg radialMajorant
  have hbound := mul_le_mul_of_nonneg_left hpair
    (mul_nonneg hC₀.le hdiag)
  have hbound := mul_le_mul hbound ht₁ (by positivity)
    (mul_nonneg (mul_nonneg hC₀.le hdiag) (by positivity))
  have hbound := mul_le_mul hbound ht₂ (by positivity) (by positivity)
  have hbound := mul_le_mul_of_nonneg_right hbound
    (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le (m + q + ε / 2 + ε / 2))
  have hexp : m + q + ε / 2 + ε / 2 = m + q + ε := by ring
  rw [hexp] at he hbound
  apply he.trans (hbound.trans ?_)
  have hc : C₀ * diagonalControl radialMajorant * K ^ 4 ≤ C := by dsimp [C]; linarith
  have hnorm₁ := compactNorm_nonneg J W₁
  have hnorm₂ := compactNorm_nonneg J W₂
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  calc
    _ = (C₀ * diagonalControl radialMajorant * K ^ 4) *
      ((compactNorm J W₁ * compactNorm J W₂) ^ 2 *
       (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + q + ε)) := by ring
    _ ≤ C * ((compactNorm J W₁ * compactNorm J W₂) ^ 2 *
       (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + q + ε)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end
end ZetaZeroFree.Analytic.Moments.D3

namespace ZetaZeroFree.Analytic.Moments.D3
noncomputable section
universe u
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ZetaZeroFree.Analytic.Moments
open HeckeFamily HeckeDyadic CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CanonicalRowCompletion CanonicalQuadraticSieve
open Filter
local notation "O" => HeckeFamily.O

/-- Appendix D.3 for displayed moving residue-symbol powers.
Every support factor is charged once, independently of its positive exponent.
The constant and smooth order precede the entire moving family. -/
theorem mixed_plain_moment_radical (a b B L Mcap ε Cν : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hM : 0 < Mcap) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ m q : ℝ, 0 ≤ m → 0 ≤ q → m + q ≤ Mcap →
      ∀ ν : Character, (ν.modulus.absNorm : ℝ) ≤ Cν →
        (∀ I : Ideal O, ¬ Supported I → idealCoeff ν I = 0) →
      ∀ (ι : Type u) [Fintype ι] (p : ι → O),
        (∀ i, Supported (Ideal.span {p i})) →
      ∀ e : ι → ℕ, (∀ i, 0 < e i) →
        (∏ i, ((Ideal.span {p i}).absNorm : ℝ)) ≤ Z ^ q →
      ∃ η : Character,
        (∀ I : Ideal O, idealCoeff η I =
          idealCoeff ν I * ∏ i, (idealRowHom (p i) I) ^ e i) ∧
        (∀ k : O, k ≠ 0 → ∀ R : Ideal O, R ≠ 0 → ∀ I : Ideal O,
          idealCoeff (excluded (naturalPlainCharacter η k) R) I =
            if IsCoprime I R then
              (idealCoeff ν I * ∏ i, (idealRowHom (p i) I) ^ e i) * idealRowHom k I
            else 0) ∧
        ∀ R : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z ^ B →
        ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0) →
          (∀ z ∈ rows, (excluded (naturalPlainCharacter η z) R).residue ≠ 1) →
          (∀ z ∈ rows, ((Ideal.span {z}).absNorm : ℝ) ≤ Z ^ m) →
        ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
          Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
        ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
          ∑ z ∈ rows,
            ‖polynomial (excluded (naturalPlainCharacter η z) R) false W₁ X₁ 0 t₁ *
              polynomial (excluded (naturalPlainCharacter η z) R) false W₂ X₂ 0 t₂‖ ^ 2 ≤
            C * (compactNorm J W₁ * compactNorm J W₂) ^ 2 *
              (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + q + ε) := by
  obtain ⟨J, C, hC, hend⟩ := mixed_plain_moment a b B L Mcap ε
    (Cν * (fixedConductorFactor : ℝ)) ha hB hM hε
  refine ⟨J, C, hC, ?_⟩
  filter_upwards [hend] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro m q hm hq hmq ν hν hνfixed ι instι p hp e he hproduct
  obtain ⟨η, hηnorm, helement, hηfixed⟩ :=
    exists_moving_radical_presentation ν p hp e he
  have hηcoeff := radical_presentation_ideal ν η p e hνfixed hηfixed helement
  have hnorm : (η.modulus.absNorm : ℝ) ≤
      (Cν * (fixedConductorFactor : ℝ)) * Z ^ q := by
    have hnat : (η.modulus.absNorm : ℝ) ≤
        (ν.modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ) *
          ∏ i, ((Ideal.span {p i}).absNorm : ℝ) := by exact_mod_cast hηnorm
    apply hnat.trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hν (Nat.cast_nonneg _)) hproduct
      (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      (mul_nonneg ((Nat.cast_nonneg _).trans hν) (Nat.cast_nonneg _))
  refine ⟨η, hηcoeff, ?_, ?_⟩
  · intro k hk R hR I
    rw [excluded_naturalPlainCharacter_ideal η hηfixed k hk R hR I, hηcoeff]
  · intro R hR hRnorm rows hrows hnp hrownorm W₁ W₂ hs₁ hs₂
      X₁ X₂ t₁ t₂ hX₁ hX₂ hL₁ hL₂
    exact hZ.2 m q hm hq hmq η hnorm R hR hRnorm rows hrows
      (fun z hz => (excluded_nonprincipal_iff _ R).mp (hnp z hz)) hrownorm
      W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hL₁ hL₂

end
end ZetaZeroFree.Analytic.Moments.D3

