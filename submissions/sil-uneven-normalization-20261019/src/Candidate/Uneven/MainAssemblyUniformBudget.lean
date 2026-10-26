import Candidate.Uneven.MainInitialContract
import Candidate.Uneven.MainZeroPayment
import Candidate.Uneven.MainAssemblyFinalWeight
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalWeight
import Candidate.Uneven.MainAssemblyGeometryAssembly
import Candidate.Cycle63.Physical.InitialMass.GeometryUniformControls

/- Original module: Candidate.Uneven.MainAssemblyActualBudget. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2500
namespace OAI.SevenEighths.MainAssembly
open Target830.Source.Uneven
noncomputable section
open Sil.Uneven.MainSource
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyState
open CenteredMomentEnergyBands Cycle63InitialSource CenteredMomentLogDyadic Cycle63Moment
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {plane : Sil.Uneven.MainSource.Plane}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance actualBudgetFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hray : Subgroup (O⧸rayM)ˣ) (hHray : RayOrthogonality.globalUnits rayM≤ Hray)

/-- Collect the outer weights of a proved actual-cardinality affine budget.
The premise is the remaining analytic budget, with the original Fourier
scales. This transport alone makes no unconditional endpoint claim. -/
theorem literal_affine_geometry_budget_of_actual
    (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character) (Q : Ideal O) (bΦ mesh εmass τ ξ : ℝ)
    (hactual :
      ∀Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
        (∀x,0≤(Ψ x).re) →
      ∃J K : ℕ, ∃S : Finset (ℕ×ℕ), ∃C : ℝ, 0< C ∧
      ∀ᶠ Z : ℝ in atTop, ∀hZ : 1< Z,
      ∀T : Finset α, ∀θ : T→RayQuotient.Characters rayM Hray,
      ∀w σ freq : T→ℝ, ∀t height : ℝ,
        (∀i,0≤ w i) → (∀i,w i≤ mesh) →
        ∀hσlo : (∀i,(33/50:ℝ)≤σ i), ∀hσhi : (∀i,σ i≤(33/50:ℝ)),
        0≤ height → (∀i,|freq i|≤ height) → 1+|t|+height≤ Z^τ →
      ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
      ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles (1/4) (9/4), ∀X₁ X₂ : ℝ,
      ∀hX₁ : 0< X₁, ∀hX₂ : 0< X₂,
        (81/200:ℝ)≤ length Z X₁ → length Z X₁≤(45/100:ℝ) →
        (81/200:ℝ)≤ length Z X₂ → length Z X₂≤(45/100:ℝ) →
        (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
        length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤ plane.B →
      let state := fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
      let inp := affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
        1 t X₁ X₂ hX₁ hX₂
      ∀key∈commonGeometryBins inp 1 1 Z Z ξ, ∀(reflected : Bool)(t' u : ℝ),
        unevenLiveBudget reflected inp 1 1 (Z^(1:ℝ)) Z ξ 1
          (Real.logb Z (volume inp)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
          (fun q=> normPhase (coordinateBlock inp 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
          (Fintype.card T) (9/4) (inp.t+2*Real.pi*(u-(if reflected then -t' else t'))) ≤
        C*geometryHighFactor reflected 64 key*(p.control S)^2*(1+|t|+height)^J*
          (1+‖inp.t+2*Real.pi*(u-(if reflected then -t' else t'))‖)^K*Z^εmass) :
    LiteralAffineGeometryBudget (plane:=plane) (α:=α) rayM Hray hHray W hW hWs
      η η₀ Q bΦ mesh εmass τ ξ := by
  intro Ψ hΨ hpΨ
  obtain ⟨J,K,S,C,hC,hbound⟩ := hactual Ψ hΨ hpΨ
  let Cf := (9/4:ℝ)^(Fintype.card α)*C*(1+2*(64:ℝ)^2)*(1+|2*Real.pi|)^K
  refine ⟨J+K,K,K,S,Cf,by dsimp [Cf]; positivity,?_⟩
  filter_upwards [hbound] with Z hbound
  intro hZ T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight Φ hsΦ hpΦ
    p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcell state inp E
  refine ⟨geometryDCompensator,fun _ _=> geometryDCompensator_pos _,?_⟩
  intro key hkey reflected t' u
  have h := hbound hZ T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight
    Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcell key hkey reflected t' u
  have ht : inp.t=t := rfl
  have hg := MainAssembly.geometry_affine_final_budget_weight T inp Z ξ εmass C ((p.control S)^2)
    height hZ J K Ψ reflected key t' u hC.le (sq_nonneg _) hh h
  simpa only [ht] using hg

end
end OAI.SevenEighths.MainAssembly
end

/- Original module: Candidate.Uneven.MainAssemblyUniformBudget. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.MainAssembly
open Target830.Source.Uneven
noncomputable section
open Sil.Uneven.MainSource
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyState
open CenteredMomentEnergyBands Cycle63InitialSource CenteredMomentLogDyadic Cycle63Moment
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {plane : Sil.Uneven.MainSource.Plane}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance uniformBudgetFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hray : Subgroup (O⧸rayM)ˣ) (hHray : RayOrthogonality.globalUnits rayM≤ Hray)

/-- Collect the actual subset budgets without changing a Fourier cardinality.
The finite maximum controls and the common eventual threshold follow the
detector, while the analytic cutoff remains fixed before it. -/
theorem literal_affine_geometry_budget_of_subset_budgets
    (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character) (Q : Ideal O) (bΦ mesh εmass τ ξ : ℝ)
    (hactual :
      ∀Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
        (∀x,0≤(Ψ x).re) →
      ∀T : Finset α, ∃J K : ℕ, ∃S : Finset (ℕ×ℕ), ∃C : ℝ, 0< C ∧
      ∀ᶠ Z : ℝ in atTop, ∀hZ : 1< Z,
      ∀θ : T→RayQuotient.Characters rayM Hray,
      ∀w σ freq : T→ℝ, ∀t height : ℝ,
        (∀i,0≤ w i) → (∀i,w i≤ mesh) →
        ∀hσlo : (∀i,(33/50:ℝ)≤σ i), ∀hσhi : (∀i,σ i≤(33/50:ℝ)),
        0≤ height → (∀i,|freq i|≤ height) → 1+|t|+height≤ Z^τ →
      ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
      ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles (1/4) (9/4), ∀X₁ X₂ : ℝ,
      ∀hX₁ : 0< X₁, ∀hX₂ : 0< X₂,
        (81/200:ℝ)≤ length Z X₁ → length Z X₁≤(45/100:ℝ) →
        (81/200:ℝ)≤ length Z X₂ → length Z X₂≤(45/100:ℝ) →
        (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
        length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤ plane.B →
      let state := fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
      let inp := affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
        1 t X₁ X₂ hX₁ hX₂
      ∀key∈commonGeometryBins inp 1 1 Z Z ξ, ∀(reflected : Bool)(t' u : ℝ),
        unevenLiveBudget reflected inp 1 1 (Z^(1:ℝ)) Z ξ 1
          (Real.logb Z (volume inp)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
          (fun q=> normPhase (coordinateBlock inp 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
          (Fintype.card T) (9/4) (inp.t+2*Real.pi*(u-(if reflected then -t' else t'))) ≤
        C*geometryHighFactor reflected 64 key*(p.control S)^2*(1+|t|+height)^J*
          (1+‖inp.t+2*Real.pi*(u-(if reflected then -t' else t'))‖)^K*Z^εmass) :
    LiteralAffineGeometryBudget (plane:=plane) (α:=α) rayM Hray hHray W hW hWs
      η η₀ Q bΦ mesh εmass τ ξ := by
  apply literal_affine_geometry_budget_of_actual (plane:=plane) rayM Hray hHray W hW hWs η η₀ Q bΦ mesh εmass τ ξ
  intro Ψ hΨ hpΨ
  choose J K S C hC hbound using hactual Ψ hΨ hpΨ
  obtain ⟨C₀,hC₀,S₀,J₀,K₀,L₀,hu⟩ := geometry_uniform_profile_controls C S J K
    (fun _=>0) (fun T=>(hC T).le)
  refine ⟨J₀,K₀,S₀,C₀,hC₀,?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hbound
  intro hZ T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight Φ hsΦ hpΦ
    p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcell state inp key hkey reflected t' u
  have h := hbound T hZ θ w σ freq t height hw hwm hσlo hσhi hh hv hheight
    Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcell key hkey reflected t' u
  have hc := hu T p (1+|t|+height)
    (1+‖inp.t+2*Real.pi*(u-(if reflected then -t' else t'))‖) 1
    (by linarith [abs_nonneg t]) (by linarith [norm_nonneg (inp.t+2*Real.pi*(u-(if reflected then -t' else t')))]) le_rfl
  simp only [Nat.mul_zero,pow_zero,one_pow,mul_one] at hc
  have hH := (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  have hz := Real.rpow_nonneg (zero_lt_one.trans hZ).le εmass
  have hpaid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hH) hz
  apply h.trans
  convert hpaid using 1 <;> ring

end
end OAI.SevenEighths.MainAssembly
end
