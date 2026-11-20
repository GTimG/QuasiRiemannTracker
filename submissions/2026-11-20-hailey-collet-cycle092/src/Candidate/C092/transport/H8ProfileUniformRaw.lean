/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform normalized-unit bounds on the literal physical and raw H8 source. -/
import Candidate.C092.transport.H8ProfileUniformUnit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O
theorem h8_unit_physical (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b)
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
      ‖(Real.sqrt T : ℂ)⁻¹*(fixedCubePhysicalSource D₁ D₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂)
          (fixedCubeBad D₁ D₂ labels) allowed X₁ X₂-
        fixedCubePhysicalSource D₁ D₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂)
          (fixedCubeBad D₁ D₂ labels) allowed Y₁ Y₂)‖ ≤
      C*U^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨J,S,hS,hJ⟩ := h8_unit_literal a b ε (3*B) ha hb hε (by positivity)
  refine ⟨J,S,hS,fun Q₁ Q₂ => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hJ Q₁ Q₂
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed _hcover hallowed
    U hU hcond₁ hcond₂ hlabels t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hχ₁ : (Ideal.absNorm D₁.row.χ.modulus : ℝ) ≤ U^(3*B) := by
    apply le_trans _ (Real.rpow_le_rpow_of_exponent_le hU (show B ≤ 3*B by linarith))
    apply le_trans _ hcond₁
    exact_mod_cast D₁.row_spec.2.1
  have hχ₂ : (Ideal.absNorm D₂.row.χ.modulus : ℝ) ≤ U^(3*B) := by
    apply le_trans _ (Real.rpow_le_rpow_of_exponent_le hU (show B ≤ 3*B by linarith))
    apply le_trans _ hcond₂
    exact_mod_cast D₂.row_spec.2.1
  have hrad : (Ideal.absNorm (∏ P ∈ fixedCubeBad D₁ D₂ labels,P.val) : ℝ) ≤ U^(3*B) := by
    have he : B+B+B=3*B := by ring
    rw [←he]
    exact fixedCubeBad_polynomial_cap D₁ D₂ labels U B B B hUpos hcond₁ hcond₂ hlabels
  simp only [fixedCubePhysicalSource_eq_literal]
  exact hbound W₁ W₂ hs₁ hs₂ D₁.row D₂.row (D₁.row_spec.1.trans hQ₁) (D₂.row_spec.1.trans hQ₂)
    (fixedCubeBad D₁ D₂ labels) (supplyingPrimeKeep supplying holes₁)
    (supplyingPrimeKeep supplying holes₂) allowed
    (fun P hP => (fixedCubeBad_good D₁ D₂ labels P hP).1)
    (fun P hP => (fixedCubeBad_good D₁ D₂ labels P hP).2)
    hallowed U hU hχ₁ hχ₂ hrad t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY


theorem h8_unit_raw (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b)
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
      ‖(Real.sqrt T : ℂ)⁻¹*((fixedCubeOutsidePhase ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) X₁ X₂)⁻¹*
          fixedCubeRawSource D₁ D₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂)
            (fixedCubeBad D₁ D₂ labels) allowed X₁ X₂-
        (fixedCubeOutsidePhase ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) Y₁ Y₂)⁻¹*
          fixedCubeRawSource D₁ D₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂)
            (fixedCubeBad D₁ D₂ labels) allowed Y₁ Y₂)‖ ≤
      C*U^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨J,S,hS,hJ⟩ := h8_unit_physical a b ε B ha hb hε hB
  refine ⟨J,S,hS,fun Q₁ Q₂ => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hJ Q₁ Q₂
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hcover hallowed
    U hU hcond₁ hcond₂ hlabels t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  rw [fixedCubeRawSource_signed_normalized D₁ D₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁) ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂)
    (fixedCubeBad D₁ D₂ labels) allowed X₁ X₂ Y₁ Y₂
    (hL.trans_le hX₁) (hL.trans_le hX₂) (hL.trans_le hY₁) (hL.trans_le hY₂)]
  exact hbound W₁ W₂ hs₁ hs₂ D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hcover hallowed
    U hU hcond₁ hcond₂ hlabels t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

#print axioms h8_unit_raw
end
end QRH.Cycle092.SignedCenter
