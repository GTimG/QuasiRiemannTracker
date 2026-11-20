/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Independent ordinary characters and heights on actual regular core subrows.
The fourth suppliers are the original zero-slot source at the same U^V. -/
import Candidate.C092.transport.ExhaustedPairPriceUnmarked
import Candidate.C092.transport.StrongPairSmallUnmarked
import Candidate.C092.transport.TinyCoreUnmarked
import Candidate.C092.transport.TinyCoreBridgeData

namespace QRH.Cycle092.ExhaustedPairPrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ConcreteTraceCRT
open CenteredMomentCoreFloor CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore
open QRH.Cycle092.CofactorOrdinary QRH.Cycle092.StrongPair
local notation "O" => ActualEisensteinCubic.O

theorem exhausted_pair_all_radii
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (bΦ Vmax ε : ℝ) (hVmax : 0 ≤ Vmax) (hε : 0 < ε) (hbΦ : 0 < bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (hQ₁ray : Q₁ ≤ rayM) (hQ₁0 : internalQ Q₁ η₀₁ ≠ 0) (hQ₁t : internalQ Q₁ η₀₁ ≠ ⊤)
    (hQ₁72 : internalQ Q₁ η₀₁ ≤ Ideal.span {(72 : O)})
    (hQ₂ray : Q₂ ≤ rayM) (hQ₂0 : internalQ Q₂ η₀₂ ≠ 0) (hQ₂t : internalQ Q₂ η₀₂ ≠ ⊤)
    (hQ₂72 : internalQ Q₂ η₀₂ ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop,1 < U ∧
      ∀ V : ℝ, 0 ≤ V → V ≤ Vmax →
      ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
        0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U →
      ∀ (s : Finset FreeRow),
        (∀ u ∈ s, initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
        (∀ u ∈ s, initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
        (∀ u ∈ s, rowNorm u ≤ U^V) →
      (∑ u ∈ s,
        ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2*
        ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^2) ≤
        C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
          (1+|t₁|+|t₂|+height)^degree*U^(V+ε) := by
  let A : ℝ := max 1 Vmax
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hVA : Vmax ≤ A := le_max_right _ _
  let e : ℝ := min 1 (ε/A)
  have he : 0 < e := lt_min zero_lt_one (div_pos hε hA)
  have he1 : e ≤ 1 := min_le_left _ _
  have heA : A*e ≤ ε := by
    have h := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (ε/A)) hA.le
    have heq : A*(ε/A)=ε := by field_simp
    exact h.trans_eq heq
  obtain ⟨degree,controls,C,hC,hsource⟩ := exhausted_pair_unit_source hβ rayM Hr hHr
    bΦ e he he1 hbΦ hsΦ η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁t hQ₁72 hQ₂ray hQ₂0 hQ₂t hQ₂72
  refine ⟨degree,controls,C,hC,?_⟩
  have hscaled := (tendsto_rpow_atTop hA).eventually hsource
  filter_upwards [hscaled,eventually_gt_atTop (1:ℝ)] with U hsource hU
  refine ⟨hU,?_⟩
  intro V hV0 hVmax p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hX₁U hX₂U s hk₁ hk₂ hy
  have hUp : 0 < U := zero_lt_one.trans hU
  have hUA : 1 ≤ U^A := Real.one_le_rpow hU.le hA.le
  have hbase : U ≤ U^A := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le hA1
  have hdim0 : 0 ≤ V/A := div_nonneg hV0 hA.le
  have hdim1 : V/A ≤ 1 := (div_le_one hA).mpr (hVmax.trans hVA)
  have hrad : (U^A)^(V/A)=U^V := by
    rw [←Real.rpow_mul hUp.le]
    congr 1
    field_simp
  have hE := hsource hUA (V/A) hdim0 hdim1 p t₁ t₂ height X₁ X₂ hh hX₁ hX₂
    (hX₁U.trans hbase) (hX₂U.trans hbase) s hk₁ hk₂ (by simpa only [hrad] using hy)
  have hpow : (U^A)^(V/A+e) ≤ U^(V+ε) := by
    rw [←Real.rpow_mul hUp.le]
    apply Real.rpow_le_rpow_of_exponent_le hU.le
    have heq : A*(V/A+e)=V+A*e := by field_simp <;> ring
    rw [heq]
    linarith only [heA]
  exact hE.trans (mul_le_mul_of_nonneg_left hpow (by
    have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    positivity))

#print axioms exhausted_pair_all_radii
end
end QRH.Cycle092.ExhaustedPairPrice
