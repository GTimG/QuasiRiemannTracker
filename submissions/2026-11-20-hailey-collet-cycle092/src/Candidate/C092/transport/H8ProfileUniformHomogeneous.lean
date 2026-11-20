/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Restore both live Schwartz profiles, including zero-control profiles, in the
literal signed H8 source. No division by a zero profile control is assumed. -/
import Candidate.C092.transport.H8ProfileUniformRaw
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

lemma h8_raw_reconstruct (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    {a b : ℝ} (ha : 0<a) (hb : 0≤b) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Icc a b)
    (D₁ D₂ : FixedCubeDatum) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal→Finset (ℕ×ℕ)) (t₁ t₂ x y : ℝ) :
    fixedCubeRawSource D₁ D₂ ((h8Profile S hS ha hb W₁ hs₁).atHeight t₁)
      ((h8Profile S hS ha hb W₂ hs₂).atHeight t₂) bad allowed x y =
    ((sourceControl S W₁*sourceControl S W₂:ℝ):ℂ)*
      fixedCubeRawSource D₁ D₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁)
      ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) bad allowed x y := by
  have point (W : 𝓢(ℝ,ℂ)) (v : ℝ) :
      (sourceControl S W:ℂ)*normalizedProfile S W v=W v := by
    have h := congrArg (fun f : 𝓢(ℝ,ℂ) => f v) (normalizedProfile_reconstruct S hS W)
    simpa only [SchwartzMap.smul_apply, smul_eq_mul,Complex.real_smul] using h
  unfold fixedCubeRawSource
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  change _*W₁ _*W₂ _ = _*(_*normalizedProfile S W₁ _*normalizedProfile S W₂ _)
  rw [←point W₁ ((Ideal.absNorm p.1:ℝ)/x),←point W₂ ((Ideal.absNorm p.2:ℝ)/y)]
  push_cast
  simp only [OrdinaryProfile.atHeight]
  ring

theorem fixedCubeRawSource_homogeneous (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b)
    (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ hS : (0,0)∈S,
    ∀ Q₁ Q₂ : Ideal O,∃ C : ℝ,0 < C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      ∀ hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ (D₁ D₂ : FixedCubeDatum),D₁.Q=Q₁ → D₂.Q=Q₂ →
      ∀ (labels supplying holes₁ holes₂ : Finset PrimeIdeal)
        (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (supplying ∪ holes₁ ∪ holes₂ ⊆ labels) →
      (∀ P ∈ fixedCubeBad D₁ D₂ labels,
        allowed P ⊆ supplyingResidualPairs D₁.row D₂.row supplying holes₁ holes₂ P) →
      ∀ U : ℝ,1 ≤ U →
      (HeckeRowClosure.rowConductorBound D₁.η D₁.m 1 (D₁.A*D₁.z) : ℝ) ≤ U^B →
      (HeckeRowClosure.rowConductorBound D₂.η D₂.m 1 (D₂.A*D₂.z) : ℝ) ≤ U^B →
      (Ideal.absNorm (∏ P ∈ labels,P.val) : ℝ) ≤ U^B →
      ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ T L : ℝ,0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T : ℂ)⁻¹*((fixedCubeOutsidePhase ((h8Profile S hS ha hb W₁ hs₁).atHeight t₁) ((h8Profile S hS ha hb W₂ hs₂).atHeight t₂) X₁ X₂)⁻¹*
          fixedCubeRawSource D₁ D₂ ((h8Profile S hS ha hb W₁ hs₁).atHeight t₁) ((h8Profile S hS ha hb W₂ hs₂).atHeight t₂)
            (fixedCubeBad D₁ D₂ labels) allowed X₁ X₂-
        (fixedCubeOutsidePhase ((h8Profile S hS ha hb W₁ hs₁).atHeight t₁) ((h8Profile S hS ha hb W₂ hs₂).atHeight t₂) Y₁ Y₂)⁻¹*
          fixedCubeRawSource D₁ D₂ ((h8Profile S hS ha hb W₁ hs₁).atHeight t₁) ((h8Profile S hS ha hb W₂ hs₂).atHeight t₂)
            (fixedCubeBad D₁ D₂ labels) allowed Y₁ Y₂)‖ ≤
      C*(sourceControl S W₁*sourceControl S W₂)*U^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨J,S,hS,hJ⟩ := h8_unit_raw a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q₁ Q₂
  obtain ⟨C,hC,hbound⟩ := hJ Q₁ Q₂
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hcover hallowed
    U hU hcond₁ hcond₂ hlabels t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have h := hbound W₁ W₂ hs₁ hs₂ D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed
    hcover hallowed U hU hcond₁ hcond₂ hlabels t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let c : ℝ := sourceControl S W₁*sourceControl S W₂
  have hc : 0≤c := mul_nonneg (sourceControl_nonneg S W₁) (sourceControl_nonneg S W₂)
  rw [h8_raw_reconstruct S hS ha hb W₁ W₂ hs₁ hs₂,
      h8_raw_reconstruct S hS ha hb W₁ W₂ hs₁ hs₂]
  have he : ∀ x y : ℝ,
      fixedCubeOutsidePhase ((h8Profile S hS ha hb W₁ hs₁).atHeight t₁)
        ((h8Profile S hS ha hb W₂ hs₂).atHeight t₂) x y =
      fixedCubeOutsidePhase ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁)
        ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) x y := fun _ _ => rfl
  rw [he,he]
  have factor' (A B X Y : ℂ) : (Real.sqrt T:ℂ)⁻¹*(A*((c:ℂ)*X)-B*((c:ℂ)*Y)) =
      (c:ℂ)*((Real.sqrt T:ℂ)⁻¹*(A*X-B*Y)) := by ring
  change ‖(Real.sqrt T:ℂ)⁻¹*(_*((c:ℂ)*_)-_*((c:ℂ)*_))‖ ≤ _
  rw [factor',norm_mul,Complex.norm_real,Real.norm_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left h hc).trans_eq (by dsimp [c]; ring)

#print axioms fixedCubeRawSource_homogeneous
end
end QRH.Cycle092.SignedCenter
