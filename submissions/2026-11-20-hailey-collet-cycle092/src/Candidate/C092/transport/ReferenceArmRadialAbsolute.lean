/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.3 on the literal original ray-prime pools and original annular marked
coefficients, with independent ordinary characters, profiles and pitches. -/
import Candidate.C092.transport.ReferenceShortP3Physical
import Candidate.C092.transport.ExhaustedPairPriceAllRadii
import Candidate.C092.transport.TinyCoreSlots
import Candidate.C092.transport.ReferenceArmRadialFourthJoin
import Candidate.C092.transport.ReferenceArmRadialGates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentHeckeSlots
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.TinyCore QRH.Cycle092.ExhaustedPairPrice QRH.Cycle092.ReferenceShortP3 QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
open QRH.SilDensitySplit.CubeFree.FP.MixedCanonicalSource (slotProfile)
local notation "O" => HeckeFamily.O

theorem actual_absolute_reference (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (ε bΦ : ℝ) (hε : 0 < ε) (hbΦ : 0 < bΦ)
    (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ ηshort₀ ηlong₀ : Character)
    (Q1 Q : Ideal O) (hQ1r : Q1≤ rayM)
    (hQ10 : internalQ Q1 ηshort₀≠0) (hQ1t : internalQ Q1 ηshort₀≠⊤)
    (hQ172 : internalQ Q1 ηshort₀≤ Ideal.span {(72:O)}) (hQr : Q ≤ rayM)
    (hQ0 : internalQ Q ηlong₀ ≠ 0) (hQt : internalQ Q ηlong₀ ≠ ⊤)
    (hQ72 : internalQ Q ηlong₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ V : ℝ, 0≤ V → V≤2 →
    ∀ (θ : ι → RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ),
    (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ (33/50:ℝ)) → (∑i,w i)≤ widthCap →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₁ (internalQ Q1 ηshort₀) u.val) →
    (∀ u∈s,initialKeep η₂ (internalQ Q ηlong₀) u.val) →
    (∀ u∈s,rowNorm u ≤ U^V) →
    (∀ u∈s, ∀ i, ‖mark i u‖ =
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i) t₁ (U^(w i))‖) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*(1+|t₁|+|t₂|+height)^d*U^(V+widthCap+ε) := by
  obtain ⟨B,hB,hbound⟩ := original_slot_coefficient_bound W hW hWs
  obtain ⟨d,S,C,hC,hsource⟩ := exhausted_pair_all_radii hβ rayM Hr hHr bΦ 2 ε
    (by norm_num) hε hbΦ hΦs η₁ η₂ ηshort₀ ηlong₀ Q1 Q
    hQ1r hQ10 hQ1t hQ172 hQr hQ0 hQt hQ72
  let A := ((256*B)^2)^Fintype.card ι
  have hA : 0< A := by dsimp [A];positivity
  have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  refine ⟨d,S,A*C*(QuadraticInitialBound.diagonalControl radialMajorant+1),by positivity,?_⟩
  filter_upwards [hsource] with U hU
  refine ⟨hU.1,?_⟩
  intro V hV hV2 θ w σ v hσlo hσhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hX₁U hX₂U s mark hk1 hk2 hy hm
  have hu : 0< U := zero_lt_one.trans hU.1
  have hP (i:ι) : 0< U^(w i) := Real.rpow_pos_of_pos hu _
  have hcoeff (i:ι) (I:Ideal O) : ‖originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i I‖≤ B :=
    hbound _ _ _ _ _ (hP i) (by linarith [hσlo i])
  have hcap (i:ι) (I:Ideal O) (hne:originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i I≠0) :
      (I.absNorm:ℝ)≤2*U^(w i) := original_slot_norm_cap W hWs _ _ _ _ _ (hP i) hne
  have hmarks (u:FreeRow) (hu':u∈s) : (∏i,‖mark i u‖^2)≤ A*U^widthCap := by
    have hb := slot_product_absolute η₁ (fixedBadMask*idealGenerator 1) 1 u.val t₁ B hB.le
      (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v)
      (fun i=> U^(w i)) hP (fun i I _=> hcoeff i I) (fun i I _=> hcap i I)
    have heq : (∏i,‖mark i u‖^2) =
        ∏i,‖rowSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i) t₁‖^2/(U^(w i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hm u hu' i]
      simp only [normalizedSlot,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,Real.sq_sqrt (hP i).le]
      ring
    rw [heq]
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hA.le
    rw [←Real.rpow_sum_of_pos hu]
    exact Real.rpow_le_rpow_of_exponent_le hU.1.le hsum
  have he := hU.2 V hV hV2 p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hX₁U hX₂U s hk1 hk2 hy
  calc
    _ ≤ (∑u∈s,‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2*
      ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^2)*(A*U^widthCap) := by
      unfold finiteEnergy
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun u hu'=> mul_le_mul_of_nonneg_left (hmarks u hu') (by positivity))
    _ ≤ (C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control S)^2*
        (1+|t₁|+|t₂|+height)^d*U^(V+ε))*(A*U^widthCap) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ ≤ _ := by
      rw [show V+widthCap+ε=(V+ε)+widthCap by ring,Real.rpow_add hu (V+ε) widthCap]
      have hn : 0≤(p.control S)^2*(1+|t₁|+|t₂|+height)^d*U^(V+ε)*U^widthCap := by positivity
      have hinc := mul_le_mul_of_nonneg_right (show QuadraticInitialBound.diagonalControl radialMajorant≤
        QuadraticInitialBound.diagonalControl radialMajorant+1 by linarith) (mul_nonneg (mul_nonneg hA.le hC.le) hn)
      convert hinc using 1 <;> ring

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.actual_absolute_reference
