/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual independent-character retained bridge from the native duplicated
short supplier and the original long fourth source at the same U^V. -/
import Candidate.C092.transport.CofactorIndependentMarked

namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip
local notation "O" => ActualEisensteinCubic.O

/-- This source has no assumed fourth or analytic estimate. Both arms are
supplied by the original checked sources. Only the short factor shares the
actual native mark character and height; the long factor is independent. -/
theorem independent_bridge_retained_source
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ mesh : ℝ, 0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1 : ℝ) 2 →
    ∀ bΦ : ℝ, 2 ≤ bΦ →
      Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bΦ →
    ∀ (η₁ η₂ η₀ : Character) (Q : Ideal O),
      Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, ∀ V : ℝ, bridgeMin ≤ V → V ≤ bridgeMax →
    ∀ (F : Finset Slot) (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ)
      (t₁ t₂ height : ℝ),
      (∀ j, 0 ≤ w j) → (∀ j, w j/V ≤ mesh) →
      (∀ j, (33/50 : ℝ) ≤ σ j) → (∀ j, σ j ≤ (33/50 : ℝ)) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
      2*(∑ j ∈ F, w j) ≤ V*bridgeWidth →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),
      0 < X₁ → 0 < X₂ → X₁ ≤ U → length (U^V) X₂ ≤ bridgeCap →
    ∀ (s : Finset FreeRow),
      (∀ u ∈ s, initialKeep η₁ (internalQ Q η₀) u.val) →
      (∀ u ∈ s, initialKeep η₂ (internalQ Q η₀) u.val) →
      (∀ u ∈ s, rowNorm u ≤ U^V) →
    (∑ u ∈ s,
      ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2*
      ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^2*
      (∏ j ∈ F, ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w j)
        (originalCoefficients rayM Hr hHr η₀ θ W U w σ v j) t₂ (U^(w j))‖^2)) ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V+1/1000) := by
  obtain ⟨mesh,hm,hsource⟩ := bridge_source hβ (1/10000) (by norm_num)
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hsΦ η₁ η₂ η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨ds,Ss,Cs,hCs,hshort⟩ := hsource (Fin 2×Slot) rayM Hr hHr W hW hWs
    bΦ hbΦ η₂ η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨dl,Sl,Cl,hCl,hlong⟩ := independent_fourth_source hβ rayM Hr hHr bΦ
    (by linarith) hsΦ η₁ η₀ Q hQray hQ0 hQt hQ72
  refine ⟨max dl ds,Sl∪Ss,Cl+Cs+1,by positivity,?_⟩
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hshort
  have hrad : 0 < bridgeMin := by norm_num [bridgeMin]
  have hlarge := (tendsto_rpow_atTop hrad).eventually (eventually_ge_atTop Z₀)
  filter_upwards [hlarge,hlong,eventually_gt_atTop (1 : ℝ)] with U hlarge hlong hU
  intro V hV0 hV1 F θ w σ v t₁ t₂ height hw hwm hσlo hσhi hh hv hF p X₁ X₂ hX₁ hX₂ hX₁U hX₂cap s hk₁ hk₂ hy
  have hV : 0 < V := hrad.trans_le hV0
  have hVone : V ≤ 1 := hV1.trans (by norm_num [bridgeMax])
  have hUp : 0 < U := zero_lt_one.trans hU
  have hUV : 1 < U^V := Real.one_lt_rpow hU hV
  have hsrc := hZ₀ (U^V) (hlarge.trans (Real.rpow_le_rpow_of_exponent_le hU.le hV0))
  have hbox : Box bridgeCap bridgeCap (V*bridgeWidth)
      (length (U^V) X₂) (length (U^V) X₂) (∑ j ∈ duplicated F, w j.2) := by
    refine ⟨length_nonneg _ _ hUV,length_nonneg _ _ hUV,Or.inl ⟨hX₂cap,hX₂cap⟩,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _ => hw j.2)
    · simpa only [duplicated_sum] using hF
  have hsE := labelled_retained_energy rayM Hr hHr hsrc (duplicated F)
    (fun j => θ j.2) (fun j => w j.2) (fun j => σ j.2) (fun j => v j.2) t₂ height
    (fun j => hw j.2) (fun j => hwm j.2) (fun j => hσlo j.2) (fun j => hσhi j.2)
    hh (fun j => hv j.2) radialMajorant hsΦ radialMajorant_nonneg (repeatedProfile p 1)
    X₂ X₂ hX₂ hX₂ hUp hV hbox
  have hlE := hlong hU.le V hV.le hVone p 0 t₁ height X₁ hh hX₁ hX₁U s hk₁ hy
  have hcs := finite_independent_marked_cauchy F η₁ η₂ (fixedBadMask*idealGenerator 1) 1
    (p.profile 0) (p.profile 1) (originalPools rayM Hr 2 U w)
    (originalCoefficients rayM Hr hHr η₀ θ W U w σ v) (fun j => U^(w j))
    t₁ t₂ X₁ X₂ (9/4) (U^V) (fun _ hx => (p.support 1 hx).2) hX₂
    (fun _ => Real.rpow_pos_of_pos hUp _) (Real.rpow_pos_of_pos hUp _) s
    (initialKeep η₂ (internalQ Q η₀)) hk₂ hy
  let G := (Cl+Cs+1)*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+|t₁|+|t₂|+height)^(max dl ds)*U^(V+1/1000)
  let A := sourceControl (Sl∪Ss) (p.profile 0)
  let B := sourceControl (Sl∪Ss) (p.profile 1)
  have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hA := control_mono Sl (Sl∪Ss) Finset.subset_union_left (p.profile 0)
  have hB := control_mono Ss (Sl∪Ss) Finset.subset_union_right (p.profile 1)
  have hheight : 1 ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hpL : (1+|t₁|+height)^dl ≤ (1+|t₁|+|t₂|+height)^(max dl ds) := by
    have hc : 1+|t₁|+height ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₂]
    exact (pow_le_pow_left₀ (by positivity) hc dl).trans (pow_le_pow_right₀ hheight (le_max_left _ _))
  have hpS : (1+|t₂|+height)^ds ≤ (1+|t₁|+|t₂|+height)^(max dl ds) := by
    have hc : 1+|t₂|+height ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁]
    exact (pow_le_pow_left₀ (by positivity) hc ds).trans (pow_le_pow_right₀ hheight (le_max_right _ _))
  have hrL := Real.rpow_le_rpow_of_exponent_le hU.le (show V+1/10000 ≤ V+1/1000 by norm_num)
  have hrS := Real.rpow_le_rpow_of_exponent_le hU.le
    (show V*(1+(1/10000 : ℝ)) ≤ V+1/1000 by linarith only [hVone])
  have hL : (∑ u ∈ s, ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^4) ≤ G*A^4 := by
    apply hlE.trans
    rw [show G*A^4 = (Cl+Cs+1)*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl (Sl∪Ss) (p.profile 0))^4*
      (1+|t₁|+|t₂|+height)^(max dl ds)*U^(V+1/1000) by dsimp [G,A]; ring]
    have hc : Cl ≤ Cl+Cs+1 := by linarith
    have ha0 := sourceControl_nonneg Sl (p.profile 0)
    gcongr
  have hS : subsetEnergy (duplicated F) η₂ (fixedBadMask*idealGenerator 1) 1 t₂
      (p.profile 1) (p.profile 1) (fun j => originalPools rayM Hr 2 U w j.2)
      (fun j => originalCoefficients rayM Hr hHr η₀ θ W U w σ v j.2)
      (fun j => U^(w j.2)) X₂ X₂ (initialKeep η₂ (internalQ Q η₀)) radialMajorant (U^V) ≤ G*B^4 := by
    apply hsE.trans
    rw [repeated_control,←pow_mul]
    rw [show G*B^4 = (Cl+Cs+1)*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl (Sl∪Ss) (p.profile 1))^4*
      (1+|t₁|+|t₂|+height)^(max dl ds)*U^(V+1/1000) by dsimp [G,B]; ring]
    have hc : Cs ≤ Cl+Cs+1 := by linarith
    have hb0 := sourceControl_nonneg Ss (p.profile 1)
    gcongr
  have h := hcs.trans (common_cauchy_factor hG hL hS)
  convert h using 1 <;> dsimp [G,A,B,Profiles.control] <;> ring

#print axioms independent_bridge_retained_source
end
end QRH.Cycle092.CofactorOrdinary
