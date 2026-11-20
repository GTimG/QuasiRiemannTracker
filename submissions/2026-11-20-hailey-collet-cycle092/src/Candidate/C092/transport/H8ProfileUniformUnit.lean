/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform unit-profile H8, retaining the original Euler-convolution source.
The source identities and source-bound suppliers retain their imported notices. -/
import Candidate.C092.transport.H8ProfileUniformControl
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O
theorem h8_unit_convolution (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b)
    (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ hS : (0,0)∈S,
    ∀ Q₁ Q₂ : Ideal O,∃ C : ℝ,0 < C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      ∀ hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ (R₁ R₂ : OrdinaryRow),R₁.Q=Q₁ → R₂.Q=Q₂ →
      ∀ (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (∀ P ∈ bad,allowed P ⊆ residualPairs true true) →
      ∀ U : ℝ,1 ≤ U → (Ideal.absNorm R₁.χ.modulus : ℝ) ≤ U^B →
      (Ideal.absNorm R₂.χ.modulus : ℝ) ≤ U^B →
      (Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ) ≤ U^B →
      ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ T L : ℝ,0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T : ℂ)⁻¹*(correctedConvolutionSource R₁ R₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) bad allowed X₁ X₂-
        correctedConvolutionSource R₁ R₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) bad allowed Y₁ Y₂)‖ ≤
      C*U^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨J,S,hS,hJ⟩ := h8_unit_pairK a b (ε/2) B ha hb (by linarith) hB
  obtain ⟨D,hD,hmask⟩ := correctedMass_capped (ε/2) B (by linarith) hB
  refine ⟨J,S,hS,?_⟩
  intro Q₁ Q₂
  obtain ⟨C,hC,hpair⟩ := hJ Q₁ Q₂
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro W₁ W₂ hs₁ hs₂ R₁ R₂ hQ₁ hQ₂ bad allowed hallowed U hU hnorm₁ hnorm₂ hrad
    t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hk := hpair W₁ W₂ hs₁ hs₂ R₁ R₂ hQ₁ hQ₂ U hU hnorm₁ hnorm₂ t₁ t₂
  have hm := hmask R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed hallowed U hU hrad
  have h := correctedConvolutionSource_signed_max R₁ R₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂)
    bad allowed X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hmass : 0 ≤ correctedMass R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed :=
    tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
  have hbound := mul_le_mul hk hm hmass (by positivity : 0 ≤ C*U^(ε/2)*(1+‖t₁‖+‖t₂‖)^J)
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg T))
    (Real.rpow_nonneg (zero_le_one.trans (le_max_left 1 L)) (-(3/5 : ℝ)))
  apply h.trans (hscaled.trans_eq ?_)
  have he : U^(ε/2)*U^(ε/2)=U^ε := by
    rw [←Real.rpow_add (zero_lt_one.trans_le hU)]
    congr 1
    ring
  calc
    _ = C*D*(U^(ε/2)*U^(ε/2))*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by ring
    _ = _ := by rw [he]


theorem h8_unit_literal (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b)
    (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ hS : (0,0)∈S,
    ∀ Q₁ Q₂ : Ideal O,∃ C : ℝ,0 < C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      ∀ hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ (R₁ R₂ : OrdinaryRow),R₁.Q=Q₁ → R₂.Q=Q₂ →
      ∀ (bad : Finset PrimeIdeal) (keep₁ keep₂ : PrimeIdeal → Bool)
        (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₁.χ.modulus) →
      (∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₂.χ.modulus) →
      (∀ P ∈ bad,allowed P ⊆ ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P) →
      ∀ U : ℝ,1 ≤ U → (Ideal.absNorm R₁.χ.modulus : ℝ) ≤ U^B →
      (Ideal.absNorm R₂.χ.modulus : ℝ) ≤ U^B →
      (Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ) ≤ U^B →
      ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ T L : ℝ,0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T : ℂ)⁻¹*(literalCubePairSource R₁ R₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) bad allowed X₁ X₂-
        literalCubePairSource R₁ R₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) bad allowed Y₁ Y₂)‖ ≤
      C*U^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨J,S,hS,hJ⟩ := h8_unit_convolution a b ε B ha hb hε hB
  refine ⟨J,S,hS,fun Q₁ Q₂ => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hJ Q₁ Q₂
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ R₁ R₂ hQ₁ hQ₂ bad keep₁ keep₂ allowed hgood₁ hgood₂ hallowed
    U hU hn₁ hn₂ hrad t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have h := hbound W₁ W₂ hs₁ hs₂ R₁ R₂ hQ₁ hQ₂ bad allowed
    (fun P hP => (hallowed P hP).trans (ordinaryResidualPairs_subset R₁ R₂ keep₁ keep₂ P))
    U hU hn₁ hn₂ hrad t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  rw [ordinaryRow_correctedConvolutionSource R₁ R₂ _ _ bad keep₁ keep₂ allowed hgood₁ hgood₂ hallowed
    X₁ X₂ (hL.trans_le hX₁) (hL.trans_le hX₂),
    ordinaryRow_correctedConvolutionSource R₁ R₂ _ _ bad keep₁ keep₂ allowed hgood₁ hgood₂ hallowed
    Y₁ Y₂ (hL.trans_le hY₁) (hL.trans_le hY₂)] at h
  exact h

#print axioms h8_unit_literal
end
end QRH.Cycle092.SignedCenter
