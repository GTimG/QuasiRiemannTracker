/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialSourceReduction
import Candidate.Cycle63.Physical.SecondZero.Uniform
import Candidate.Cycle63.Physical.ClippedProjectorShell

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentCommonRadialData
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentAmplificationChildSourceCaps Cycle63InitialSource Cycle63FirstGeometry
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

section Literal
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance sourceCapsFinite : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters rayM H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ} (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)
variable (Lc M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "inp" => affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha Lc t X₁ X₂ hX₁ hX₂

theorem affine_endpoints (hbslot : 0 ≤ bslot) (hb : 0 ≤ b) :
    Endpoints (max 1 bslot) b b inp := by
  exact ⟨le_max_right _ _, fun _ => hbslot, hb, le_rfl, hb, le_rfl⟩

/-- The comparison rectangle is bounded from its actual equal-product formula. -/
theorem affine_plain_caps (Mmax : ℝ) (hZ : 1 < Z) (hM : 0 ≤ M) (hmax : M ≤ Mmax)
    (hLc₀ : 0 ≤ Lc) (hLc : Lc ≤ M/4) (hvol : length Z X₁+length Z X₂ ≤ M) :
    ∀ second j, Cycle63.Physical.sourcePlainScales (inp).toData.toSource second j ≤ Z^Mmax := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hx (X : ℝ) : X ≤ Z^(length Z X) := by
    rw [length, Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have hn₁ := length_nonneg Z X₁ hZ
  have hn₂ := length_nonneg Z X₂ hZ
  have hx₁ : X₁ ≤ Z^Mmax := (hx X₁).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hx₂ : X₂ ≤ Z^Mmax := (hx X₂).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hfirst : comparisonFirstAt Z Lc ≤ Z^Mmax :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hsecond : comparisonSecondAt Z Lc X₁ X₂ ≤ Z^Mmax := by
    unfold comparisonSecondAt comparisonFirstAt
    calc
      _ ≤ Z^(length Z X₁+length Z X₂)/Z^Lc := by
        rw [Real.rpow_add hz]
        exact div_le_div_of_nonneg_right (mul_le_mul (hx X₁) (hx X₂) hX₂.le
          (Real.rpow_nonneg hz.le _)) (Real.rpow_nonneg hz.le _)
      _ = Z^(length Z X₁+length Z X₂-Lc) := (Real.rpow_sub hz _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  intro second j
  cases second <;> fin_cases j
  · exact hx₁
  · exact hx₂
  · exact hfirst
  · exact hsecond
end Literal

/-- The fixed caps precede every live slot subset and all source parameters. -/
theorem fixed_affine_source_caps {α : Type*} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi a b : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hbslot : 0 ≤ bslot) (ha : 0 < a) (hb : 1 ≤ b) :
    ∃ Cs bs bp : ℝ, 1 ≤ Cs ∧ 1 ≤ bs ∧ 1 ≤ bp ∧
    ∀ (T : Finset α) (η₀ : Character) (θ : T → RayQuotient.Characters rayM H)
      (w σ freq : T → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
      {Z Bmask bΦ : ℝ} (state : NaturalState Z Bmask bΦ) (p : Profiles a b)
      (Lc t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
    let inp := affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha Lc t X₁ X₂ hX₁ hX₂
    Fintype.card T ≤ Fintype.card α ∧ (∀ i, (inp).M i ≤ Cs) ∧ (inp).upper ≤ bs ∧
    Endpoints bs bp bp inp ∧ (inp).b₁ = bp ∧ (inp).b₂ = bp ∧
    (inp).W₁ = p.profile 0 ∧ (inp).W₂ = p.profile 1 ∧ (inp).η = state.character ∧
    CenteredMomentAllocatedRayDictionary.Matches rayM H hH inp η₀ θ w σ freq W bslot Z := by
  let Cs := CenteredMomentEnergyNaturalInputMatches.profileBound
    W hW aslot bslot lo hi haslot hWs
  refine ⟨Cs, max 1 bslot, b,
    CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one
      W hW aslot bslot lo hi haslot hWs, le_max_left _ _, hb, ?_⟩
  intro T η₀ θ w σ freq hσ Z Bmask bΦ state p Lc t X₁ X₂ hX₁ hX₂
  refine ⟨Fintype.card_le_of_injective (fun i : T => i.val) Subtype.val_injective,
    fun _ => le_rfl, le_max_right _ _, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · exact affine_endpoints rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha Lc t X₁ X₂ hX₁ hX₂ hbslot (zero_le_one.trans hb)
  · constructor <;> intros <;> rfl

end
end OAI.SevenEighths.Cycle63InitialMass
