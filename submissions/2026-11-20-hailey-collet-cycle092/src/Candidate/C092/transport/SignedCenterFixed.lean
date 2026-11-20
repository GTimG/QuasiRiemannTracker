/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.HeckeTwist
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDegree

/-! A genuine checked stage toward H8: distinct fixed inducing characters,
their own modulus masks, and independent normalized heights in the two ordinary
factors. The coupled cube-free Euler convolution is deliberately not identified
with this factored product. Upstream OAI modules retain their original licences.
-/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation CenteredMomentHeckeTwist CenteredMomentLattice
open CenteredMomentTwist EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

/-- The outside phase must be removed before installing the reference arm.
Each profile keeps its own normalized height; there is no equality of heights. -/
theorem normalize_ordinary_height (χ : Character) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ((X : ℂ) ^ (Complex.I*t))⁻¹*twistedIdealSum χ W t X =
      idealSum χ (normPowerProfile W a b ha hs hW t) X := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX]
  have hn : (X : ℂ) ^ (Complex.I*t) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact inv_mul_cancel_left₀ hn _

/-- Different inducing characters, different original zero masks, and different
normalized profile heights are allowed. This is a factored ordinary source
estimate, proved from the actual masked Hecke lattice-volume theorem. -/
theorem distinct_fixedrow_factored_centering
    (η₁ χ₁ ψ₁ η₂ χ₂ ψ₂ : Character)
    (Q₁ Q₂ : Ideal O) (hQ₁ : Q₁ ≠ 0) (hQ₂ : Q₂ ≠ 0)
    (hQψ₁ : Q₁ ≤ ψ₁.modulus) (hQψ₂ : Q₂ ≤ ψ₂.modulus)
    (hind₁ : CenteredExceptionalProfile.InducedBy χ₁ ψ₁)
    (hind₂ : CenteredExceptionalProfile.InducedBy χ₂ ψ₂)
    (m₁ A₁ z₁ m₂ A₂ z₂ : O)
    (hml₁ : ConcretePrimeRowBridge.goodLambda ∣ m₁) (hm2₁ : (2 : O) ∣ m₁)
    (hml₂ : ConcretePrimeRowBridge.goodLambda ∣ m₂) (hm2₂ : (2 : O) ∣ m₂)
    (hrow₁ : ∀ n,elementCoeff χ₁ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η₁) m₁ 1 (A₁*z₁) n)
    (hrow₂ : ∀ n,elementCoeff χ₂ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η₂) m₂ 1 (A₂*z₂) n)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hbound₁ : ∀ y,‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y,‖W₂ y‖ ≤ M₂)
    (t₁ t₂ X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁*X₂=T) (hprodY : Y₁*Y₂=T) :
    let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t₁
    let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t₂
    let E := volumeControl Q₁ χ₁ V₁+volumeControl Q₂ χ₂ V₂
    ‖(Real.sqrt T : ℂ)⁻¹*(idealSum χ₁ V₁ X₁*idealSum χ₂ V₂ X₂-
      idealSum χ₁ V₁ Y₁*idealSum χ₂ V₂ Y₂)‖ ≤
      4*E*(128*(b₁*M₁+b₂*M₂))*(Real.sqrt T/L) := by
  let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t₁
  let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t₂
  let E := volumeControl Q₁ χ₁ V₁+volumeControl Q₂ χ₂ V₂
  let C := 128*(b₁*M₁+b₂*M₂)
  let v₁ := density (fixedPeriod Q₁) (fixedPeriod_ne_zero Q₁ hQ₁) ψ₁ χ₁.modulus*
    paperRadialFourier V₁ 0
  let v₂ := density (fixedPeriod Q₂) (fixedPeriod_ne_zero Q₂ hQ₂) ψ₂ χ₂.modulus*
    paperRadialFourier V₂ 0
  have hE₁ := volumeControl_nonneg Q₁ χ₁ V₁
  have hE₂ := volumeControl_nonneg Q₂ χ₂ V₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hC₁ : 128*b₁*M₁ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₂ hM₂]
  have hC₂ : 128*b₂*M₂ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₁ hM₁]
  have hsV₁ : Function.support (V₁ : ℝ → ℂ) ⊆ Set.Iic b₁ :=
    (normPowerProfile_support W₁ a₁ b₁ ha₁ hs₁ hW₁ t₁).trans (fun _ hx => (hs₁ hx).2)
  have hsV₂ : Function.support (V₂ : ℝ → ℂ) ⊆ Set.Iic b₂ :=
    (normPowerProfile_support W₂ a₂ b₂ ha₂ hs₂ hW₂ t₂).trans (fun _ hx => (hs₂ hx).2)
  have he₁ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ₁ V₁ X-(X : ℂ)*v₁‖ ≤ E := by
    exact (actual_induced_volume η₁ χ₁ ψ₁ Q₁ hQ₁ hQψ₁ hind₁ m₁ A₁ z₁ hml₁ hm2₁ hrow₁
      V₁ b₁ X (hL.trans_le hX) hsV₁).trans (le_add_of_nonneg_right hE₂)
  have he₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ₂ V₂ X-(X : ℂ)*v₂‖ ≤ E := by
    exact (actual_induced_volume η₂ χ₂ ψ₂ Q₂ hQ₂ hQψ₂ hind₂ m₂ A₂ z₂ hml₂ hm2₂ hrow₂
      V₂ b₂ X (hL.trans_le hX) hsV₂).trans (le_add_of_nonneg_left hE₁)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖(X : ℂ)*v₁‖ ≤ C*X := by
    have hv := (twisted_actual_volumeCoefficient_norm_le η₁ χ₁ ψ₁ Q₁ hQ₁ hQψ₁ hind₁
      m₁ A₁ z₁ hml₁ hm2₁ hrow₁ W₁ a₁ b₁ M₁ ha₁ hb₁ hM₁ hs₁ hW₁ hbound₁ t₁).trans hC₁
    change ‖v₁‖ ≤ C at hv
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hL.le.trans hX)]
    nlinarith [mul_le_mul_of_nonneg_left hv (hL.le.trans hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ₂ V₂ X‖ ≤ C*X := by
    exact (idealSum_absolute χ₂ V₂ b₂ M₂ X hb₂ hM₂ (hL.trans_le hX)
      (fun y => (normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ t₂ y).trans_le (hbound₂ y))
      hsV₂).trans (mul_le_mul_of_nonneg_right hC₂ (hL.le.trans hX))
  have hmain : ((X₁ : ℂ)*v₁)*((X₂ : ℂ)*v₂)=((Y₁ : ℂ)*v₁)*((Y₂ : ℂ)*v₂) := by
    have hp : (X₁ : ℂ)*X₂=(Y₁ : ℂ)*Y₂ := by exact_mod_cast hprodX.trans hprodY.symm
    calc
      _ = ((X₁ : ℂ)*X₂)*(v₁*v₂) := by ring
      _ = ((Y₁ : ℂ)*Y₂)*(v₁*v₂) := by rw [hp]
      _ = _ := by ring
  have hraw := CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (he₁ X₁ hX₁) (he₂ X₂ hX₂)
    (he₁ Y₁ hY₁) (he₂ Y₂ hY₂) (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁)
    (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁) hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY
  have hT : 0 < T := hprodX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  exact CenteredMoment.normalized_centered_saving _ T L C E hT hraw

/-- Uniform polynomial dependence on two independent normalized heights.
The power degree is chosen before either fixed modulus or either profile.
No character is assumed nonprincipal, and the characters need not differ. -/
theorem distinct_fixedrow_factored_uniform
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ Q₁ Q₂ : Ideal O, Q₁ ≠ 0 → Q₂ ≠ 0 →
      ∀ W₁ W₂ : ℝ → ℂ,
      ∀ hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ hW₁ : ContDiff ℝ ∞ W₁, ∀ hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ η₁ χ₁ ψ₁ η₂ χ₂ ψ₂ : Character,
      (Ideal.absNorm χ₁.modulus : ℝ) ≤ Z ^ B →
      (Ideal.absNorm χ₂.modulus : ℝ) ≤ Z ^ B →
      Q₁ ≤ ψ₁.modulus → Q₂ ≤ ψ₂.modulus →
      CenteredExceptionalProfile.InducedBy χ₁ ψ₁ →
      CenteredExceptionalProfile.InducedBy χ₂ ψ₂ →
      ∀ m₁ A₁ z₁ m₂ A₂ z₂ : O,
      ConcretePrimeRowBridge.goodLambda ∣ m₁ → (2 : O) ∣ m₁ →
      ConcretePrimeRowBridge.goodLambda ∣ m₂ → (2 : O) ∣ m₂ →
      (∀ n, elementCoeff χ₁ n = CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η₁) m₁ 1 (A₁*z₁) n) →
      (∀ n, elementCoeff χ₂ n = CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η₂) m₂ 1 (A₂*z₂) n) →
      ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t₁
      let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t₂
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (idealSum χ₁ V₁ X₁*idealSum χ₂ V₂ X₂-
          idealSum χ₁ V₁ Y₁*idealSum χ₂ V₂ Y₂)‖ ≤
        C * Z ^ ε * (1+‖t₁‖+‖t₂‖)^J * (Real.sqrt T/L) := by
  obtain ⟨n₁, hn₁⟩ := CenteredMomentNaturalFixedRaySource.volumeControl_uniform_degree
    a₁ b₁ ε B ha₁ hε hB
  obtain ⟨n₂, hn₂⟩ := CenteredMomentNaturalFixedRaySource.volumeControl_uniform_degree
    a₂ b₂ ε B ha₂ hε hB
  refine ⟨max n₁ n₂, ?_⟩
  intro Q₁ Q₂ hQ₁ hQ₂ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁, hD₁, herr₁⟩ := hn₁ Q₁ W₁ hs₁ hW₁
  obtain ⟨D₂, hD₂, herr₂⟩ := hn₂ Q₂ W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (y : ℝ) : ‖W₁ y‖ ≤ M₁ := by
    rw [← normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (y : ℝ) : ‖W₂ y‖ ≤ M₂ := by
    rw [← normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128*(b₁*M₁+b₂*M₂)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  let C := 1+4*(D₁+D₂)*V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ η₁ χ₁ ψ₁ η₂ χ₂ ψ₂ hnorm₁ hnorm₂ hQψ₁ hQψ₂ hind₁ hind₂
    m₁ A₁ z₁ m₂ A₂ z₂ hml₁ hm2₁ hml₂ hm2₂ hrow₁ hrow₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := volumeControl Q₁ χ₁ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t₁)+
    volumeControl Q₂ χ₂ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t₂)
  let H := 1+‖t₁‖+‖t₂‖
  have hH : 1 ≤ H := by dsimp only [H]; linarith [norm_nonneg t₁, norm_nonneg t₂]
  have hpow₁ : (1+‖t₁‖)^n₁ ≤ H^max n₁ n₂ := by
    calc
      _ ≤ H^n₁ := by gcongr; dsimp only [H]; linarith [norm_nonneg t₂]
      _ ≤ _ := pow_le_pow_right₀ hH (le_max_left n₁ n₂)
  have hpow₂ : (1+‖t₂‖)^n₂ ≤ H^max n₁ n₂ := by
    calc
      _ ≤ H^n₂ := by gcongr; dsimp only [H]; linarith [norm_nonneg t₁]
      _ ≤ _ := pow_le_pow_right₀ hH (le_max_right n₁ n₂)
  have hz : 0 ≤ Z^ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (D₁+D₂)*Z^ε*H^max n₁ n₂ := by
    have h₁ := (herr₁ Z hZ χ₁ hnorm₁ t₁).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hD₁.le hz))
    have h₂ := (herr₂ Z hZ χ₂ hnorm₂ t₂).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hD₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := distinct_fixedrow_factored_centering
    η₁ χ₁ ψ₁ η₂ χ₂ ψ₂ Q₁ Q₂ hQ₁ hQ₂ hQψ₁ hQψ₂ hind₁ hind₂
    m₁ A₁ z₁ m₂ A₂ z₂ hml₁ hm2₁ hml₂ hm2₂ hrow₁ hrow₂
    W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂ ha₁ ha₂ hb₁ hb₂ hM₁ hM₂
    hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂ t₁ t₂ X₁ X₂ Y₁ Y₂ T L
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hratio : 0 ≤ Real.sqrt T/L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4*E*V*(Real.sqrt T/L) := hraw
    _ ≤ 4*((D₁+D₂)*Z^ε*H^max n₁ n₂)*V*(Real.sqrt T/L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4*(D₁+D₂)*V)*Z^ε*H^max n₁ n₂*(Real.sqrt T/L) := by ring
    _ ≤ C*Z^ε*H^max n₁ n₂*(Real.sqrt T/L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

end
end QRH.Cycle092.SignedCenter
