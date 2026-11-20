/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.FixedCubeApplicationUniform
import Candidate.C092.transport.FixedCubeApplicationHeight
import Candidate.C092.transport.FixedCubeApplicationSlots

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- H8 on the original fixed-inducing signed rectangles after removing their
own outside phases. The two ordinary pitches are arbitrary independent reals.
Actual character identity, primitive masks, bad support and radical cap are
proved by the imported application modules. Residual seed submasks persist. -/
theorem fixedCubeRawSource_uniform (P₁ P₂ : OrdinaryProfile) (ε B : ℝ)
    (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ,∀ Q₁ Q₂ : Ideal O,∃ C : ℝ,0 < C ∧
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
      ‖(Real.sqrt T : ℂ)⁻¹*((fixedCubeOutsidePhase (P₁.atHeight t₁) (P₂.atHeight t₂) X₁ X₂)⁻¹*
          fixedCubeRawSource D₁ D₂ (P₁.atHeight t₁) (P₂.atHeight t₂)
            (fixedCubeBad D₁ D₂ labels) allowed X₁ X₂-
        (fixedCubeOutsidePhase (P₁.atHeight t₁) (P₂.atHeight t₂) Y₁ Y₂)⁻¹*
          fixedCubeRawSource D₁ D₂ (P₁.atHeight t₁) (P₂.atHeight t₂)
            (fixedCubeBad D₁ D₂ labels) allowed Y₁ Y₂)‖ ≤
      C*U^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨J,hJ⟩ := fixedCubePhysicalSource_uniform P₁ P₂ ε B hε hB
  refine ⟨J,fun Q₁ Q₂ => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hJ Q₁ Q₂
  refine ⟨C,hC,?_⟩
  intro D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hcover hallowed
    U hU hcond₁ hcond₂ hlabels t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  rw [fixedCubeRawSource_signed_normalized D₁ D₂ (P₁.atHeight t₁) (P₂.atHeight t₂)
    (fixedCubeBad D₁ D₂ labels) allowed X₁ X₂ Y₁ Y₂
    (hL.trans_le hX₁) (hL.trans_le hX₂) (hL.trans_le hY₁) (hL.trans_le hY₂)]
  exact hbound D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hcover hallowed
    U hU hcond₁ hcond₂ hlabels t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

#print axioms fixedCubeRawSource_uniform
end
end QRH.Cycle092.SignedCenter
