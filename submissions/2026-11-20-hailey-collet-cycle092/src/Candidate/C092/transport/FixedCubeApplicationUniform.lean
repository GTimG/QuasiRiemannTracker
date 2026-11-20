/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.FixedCubeApplicationBad

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- P.3/H.5's fixed-inducing application of H8. The source uses the original
canonical ideal-row factors, not supplied χ coefficients. Both primitive
inducing identifications, good-prime coverage and the exceptional-radical cap
are discharged from actual fixed-row data and original conductor/label caps.
All residual seed submasks are retained. Heights are independent and unbounded. -/
theorem fixedCubePhysicalSource_uniform (P₁ P₂ : OrdinaryProfile) (ε B : ℝ)
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
      ‖(Real.sqrt T : ℂ)⁻¹*(fixedCubePhysicalSource D₁ D₂ (P₁.atHeight t₁) (P₂.atHeight t₂)
          (fixedCubeBad D₁ D₂ labels) allowed X₁ X₂-
        fixedCubePhysicalSource D₁ D₂ (P₁.atHeight t₁) (P₂.atHeight t₂)
          (fixedCubeBad D₁ D₂ labels) allowed Y₁ Y₂)‖ ≤
      C*U^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨J,hJ⟩ := literalCubePairSource_uniform P₁ P₂ ε (3*B) hε (by positivity)
  refine ⟨J,fun Q₁ Q₂ => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hJ Q₁ Q₂
  refine ⟨C,hC,?_⟩
  intro D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed _hcover hallowed
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
  exact hbound D₁.row D₂.row (D₁.row_spec.1.trans hQ₁) (D₂.row_spec.1.trans hQ₂)
    (fixedCubeBad D₁ D₂ labels) (supplyingPrimeKeep supplying holes₁)
    (supplyingPrimeKeep supplying holes₂) allowed
    (fun P hP => (fixedCubeBad_good D₁ D₂ labels P hP).1)
    (fun P hP => (fixedCubeBad_good D₁ D₂ labels P hP).2)
    hallowed U hU hχ₁ hχ₂ hrad t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

/-- The constructed physical bad set really removes each frozen supplier
from both original ordinary coordinates, even after further seed restrictions. -/
theorem fixedCubePhysical_supplier_removed (D₁ D₂ : FixedCubeDatum)
    (labels supplying holes₁ holes₂ : Finset PrimeIdeal) (hsupply : supplying ⊆ labels)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hallowed : ∀ P ∈ fixedCubeBad D₁ D₂ labels,
      allowed P ⊆ supplyingResidualPairs D₁.row D₂.row supplying holes₁ holes₂ P)
    (I J : Ideal O) (hIJ : PairAllowed (fixedCubeBad D₁ D₂ labels) allowed I J)
    (P : PrimeIdeal) (hP : P ∈ supplying) :
    ProbePhysical.primeValuations I P=0 ∧ ProbePhysical.primeValuations J P=0 :=
  allowed_supplier_valuations_zero D₁.row D₂.row (fixedCubeBad D₁ D₂ labels)
    supplying holes₁ holes₂ (hsupply.trans (fixedCubeBad_contains_labels D₁ D₂ labels))
    allowed hallowed I J hIJ P hP

#print axioms fixedCubePhysicalSource_uniform
#print axioms fixedCubePhysical_supplier_removed
end
end QRH.Cycle092.SignedCenter
