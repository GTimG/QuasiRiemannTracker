/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A polynomial height factor pays the original two-ordinary energy outside
the bounded frequencies of the detector. All slot widths, lengths and row
cutoffs remain at their actual scales. -/
import Candidate.C092.transport.MeasuredBall
import Candidate.C092.transport.TinyCoreSource

namespace QRH.Cycle092.LargeHeight
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentEnergyBands QRH.Cycle090
open QRH.Cycle092.NativeStrip QRH.Cycle092.WholeSlot QRH.Cycle092.TinyCore
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_OriginalLargeHeight_e653190308b0ee9d_001 (M : Ideal O) [NeZero M] : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem height_absorbs_base (τ : ℝ) (hτ : 0 < τ) :
    ∃ d : ℕ, ∀ U B : ℝ, 1 ≤ U → U^τ ≤ B → U ≤ B^d := by
  obtain ⟨d,hd⟩ := exists_nat_ge (1/τ)
  refine ⟨d,?_⟩; intro U B hU hb
  have hd' : 1 ≤ τ*(d:ℝ) := by
    have := (div_le_iff₀ hτ).mp hd; linarith only [this]
  have h := Real.rpow_le_rpow_of_exponent_le hU hd'
  rw [Real.rpow_one,Real.rpow_mul (zero_le_one.trans hU),Real.rpow_natCast] at h
  exact h.trans (pow_le_pow_left₀ (Real.rpow_nonneg (zero_le_one.trans hU) _) hb _)

set_option maxHeartbeats 650000 in
theorem outside_original (τ : ℝ) (hτ : 0 < τ) (α : Type) [Fintype α] [DecidableEq α]
    (W : ℝ → ℂ) (hW : Continuous W) (hs : Function.support W ⊆ Set.Icc (1:ℝ) 2) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 1 < U →
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O ⧸ rayM)ˣ) (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
      (T : Finset α) (η η₀ : Character) (m A : O) (θ : T → RayQuotient.Characters rayM Hr)
      (w σ v : T → ℝ) (t height V n y X₁ X₂ : ℝ)
      (p : Profiles (1/4) (9/4)) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)),
      (∀ i, 0 ≤ σ i) → 0 ≤ height → 0 ≤ V → 0 < X₁ → 0 < X₂ →
      sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length U X₁) (length U X₂) (∑ i,w i) → U^τ ≤ 1+|t|+height →
      energy η m A t (p.profile 0) (p.profile 1) (originalPools rayM Hr 2 U w)
        (originalCoefficients rayM Hr hHr η₀ θ W U w σ v) (fun i => U^(w i)) X₁ X₂ keep Φ (U^V) ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control {(0,0)})^2*(1+|t|+height)^d*U^V := by
  obtain ⟨d,hdeg⟩ := height_absorbs_base τ hτ
  obtain ⟨B,hB,hcoeff⟩ := original_slot_coefficient_bound W hW hs
  let B' := max 1 (256*B)
  have hB' : 1 ≤ B' := le_max_left _ _
  let c := (288:ℝ)*288*B'^Fintype.card α
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨d,c^2,by positivity,?_⟩
  intro U hU rayM _ Hr hHr T η η₀ m A θ w σ v t height V n y X₁ X₂ p keep Φ hσ hh hV hX₁ hX₂ hy₀ hy₁ hn hb hbig
  have hUp := zero_lt_one.trans hU
  let S : Finset (ℕ×ℕ) := {(0,0)}
  let A₁ := sourceControl S (p.profile 0)
  let A₂ := sourceControl S (p.profile 1)
  have hprofile (i : Fin 2) (x : ℝ) : ‖p.profile i x‖ ≤ sourceControl S (p.profile i) :=
    (SchwartzMap.norm_le_seminorm ℝ (p.profile i) x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) (show (0,0) ∈ S by simp [S]))
  have hP (i : T) := Real.rpow_pos_of_pos hUp (w i)
  have hsource := energy_absolute η m A t (p.profile 0) (p.profile 1)
    (9/4) (9/4) A₁ A₂ X₁ X₂ (by norm_num) (by norm_num) (sourceControl_nonneg _ _) (sourceControl_nonneg _ _) hX₁ hX₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) (hprofile 0) (hprofile 1)
    (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
    (fun i => U^(w i)) (fun _ => 2) (fun _ => B) hP (fun _ => by norm_num) (fun _ => hB.le)
    (fun i I _ => hcoeff _ _ _ _ I (hP i) (hσ i))
    (fun i I _ hne => original_slot_norm_cap W hs _ _ _ _ _ (hP i) hne)
    keep Φ (U^V) (Real.rpow_pos_of_pos hUp _)
  have hvol := MeasuredBall.support_cap hU hX₁ hX₂ hy₀ hy₁ hn hb
  have hvol' : X₁*X₂*(∏ i,U^(w i)) ≤ (1+|t|+height)^d := by
    rw [← Real.rpow_sum_of_pos hUp]
    exact hvol.trans ((Real.rpow_le_rpow_of_exponent_le hU.le (show (9179599/10000000:ℝ) ≤ 1 by norm_num)).trans
      ((Real.rpow_one U).le.trans (hdeg U _ hU.le hbig)))
  have hcard : Fintype.card T ≤ Fintype.card α := (Fintype.card_coe T).le.trans (Finset.card_le_univ _)
  have hprod : (∏ _i : T,128*(2:ℝ)*B) ≤ B'^Fintype.card α := by
    rw [Finset.prod_const,Finset.card_univ]
    exact (pow_le_pow_left₀ (by positivity) (by norm_num; exact le_max_right _ _) _).trans (pow_le_pow_right₀ hB' hcard)
  have hcoeff' : (128*(9/4:ℝ)*A₁)*(128*(9/4)*A₂)*(∏ _i : T,128*(2:ℝ)*B) ≤ c*(A₁*A₂) := by
    calc
      _ ≤ (128*(9/4:ℝ)*A₁)*(128*(9/4)*A₂)*B'^Fintype.card α :=
        mul_le_mul_of_nonneg_left hprod (by have := sourceControl_nonneg S (p.profile 0); have := sourceControl_nonneg S (p.profile 1); dsimp [A₁,A₂]; positivity)
      _ = _ := by dsimp [c]; ring
  have hA₁ : 0 ≤ A₁ := sourceControl_nonneg _ _
  have hA₂ : 0 ≤ A₂ := sourceControl_nonneg _ _
  have hco := pow_le_pow_left₀ (by positivity) hcoeff' 2
  have hΦ := QuadraticInitialBound.diagonalControl_nonneg Φ
  rw [max_eq_right (Real.one_le_rpow hU.le hV)] at hsource
  refine hsource.trans ?_
  calc
    _ ≤ QuadraticInitialBound.diagonalControl Φ*U^V*((c*(A₁*A₂))^2*(1+|t|+height)^d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hco hvol' (by positivity) (sq_nonneg _)) (by positivity)
    _ = _ := by change _=c^2*QuadraticInitialBound.diagonalControl Φ*(A₁*A₂)^2*(1+|t|+height)^d*U^V; ring

#print axioms outside_original
end
end QRH.Cycle092.LargeHeight
