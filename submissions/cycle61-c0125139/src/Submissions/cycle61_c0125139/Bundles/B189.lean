/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B138
import Submissions.cycle61_c0125139.Bundles.B160
import Submissions.cycle61_c0125139.Bundles.B183
import Submissions.cycle61_c0125139.Bundles.B186
import Submissions.cycle61_c0125139.Bundles.B188

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineActualBudget; sha256 304daac32f151f0903b238ee38a97f3a0cf43fc11b180451ed4f1d7c9e560a31 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                          

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyState
open CenteredMomentEnergyBands Cycle61InitialSource CenteredMomentLogDyadic Cycle61Moment
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

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
      ∀T : Finset α, ∀θ : T→ RayQuotient.Characters rayM Hray,
      ∀w σ freq : T→ℝ, ∀t height : ℝ,
        (∀i,0≤ w i) → (∀i,w i≤ mesh) →
        ∀hσlo : (∀i,(33/50:ℝ)≤σ i), ∀hσhi : (∀i,σ i≤(33/50:ℝ)),
        0≤ height → (∀i,|freq i|≤ height) → 1+|t|+height≤ Z^τ →
      ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
      ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles (1/4) (9/4), ∀X₁ X₂ : ℝ,
      ∀hX₁ : 0< X₁, ∀hX₂ : 0< X₂,
        (41/100:ℝ)≤ length Z X₁ → length Z X₁≤(44/100:ℝ) →
        (41/100:ℝ)≤ length Z X₂ → length Z X₂≤(44/100:ℝ) →
        (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
        length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑i,w i)≤ Cycle61.Arithmetic.B →
      let state := fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
      let inp := affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
        1 t X₁ X₂ hX₁ hX₂
      ∀key∈commonGeometryBins inp 1 1 Z Z ξ, ∀(reflected : Bool)(t' u : ℝ),
        geometryLiveBudget reflected inp 1 1 (Z^(1:ℝ)) Z ξ 1
          (Real.logb Z (volume inp)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
          (fun q=>normPhase (coordinateBlock inp 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
          (Fintype.card T) (9/4) (inp.t+2*Real.pi*(u-(if reflected then -t' else t'))) ≤
        C*geometryHighFactor reflected 64 key*(p.control S)^2*(1+|t|+height)^J*
          (1+‖inp.t+2*Real.pi*(u-(if reflected then -t' else t'))‖)^K*Z^εmass) :
    LiteralAffineGeometryBudget (α:=α) rayM Hray hHray W hW hWs
      η η₀ Q bΦ mesh εmass τ ξ := by
  intro Ψ hΨ hpΨ
  obtain ⟨J,K,S,C,hC,hbound⟩ := hactual Ψ hΨ hpΨ
  let Cf := (9/4:ℝ)^(Fintype.card α)*C*(1+2*(64:ℝ)^2)*(1+|2*Real.pi|)^K
  refine ⟨J+K,K,K,S,Cf,by dsimp [Cf]; positivity,?_⟩
  filter_upwards [hbound] with Z hbound
  intro hZ T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight Φ hsΦ hpΦ
    p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcell state inp E
  refine ⟨geometryDCompensator,fun _ _=>geometryDCompensator_pos _,?_⟩
  intro key hkey reflected t' u
  have h := hbound hZ T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight
    Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcell key hkey reflected t' u
  have ht : inp.t=t := rfl
  have hg := geometry_affine_final_budget_weight T inp Z ξ εmass C ((p.control S)^2)
    height hZ J K Ψ reflected key t' u hC.le (sq_nonneg _) hh h
  simpa only [ht] using hg

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.literal_affine_geometry_budget_of_actual

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineActualBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineUniformBudget; sha256 267bf142194718bd38343146335f61b572473cf912d646dce097d264cc251b90 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                              
                                                           
                                                          

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyState
open CenteredMomentEnergyBands Cycle61InitialSource CenteredMomentLogDyadic Cycle61Moment
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

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
      ∀θ : T→ RayQuotient.Characters rayM Hray,
      ∀w σ freq : T→ℝ, ∀t height : ℝ,
        (∀i,0≤ w i) → (∀i,w i≤ mesh) →
        ∀hσlo : (∀i,(33/50:ℝ)≤σ i), ∀hσhi : (∀i,σ i≤(33/50:ℝ)),
        0≤ height → (∀i,|freq i|≤ height) → 1+|t|+height≤ Z^τ →
      ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
      ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles (1/4) (9/4), ∀X₁ X₂ : ℝ,
      ∀hX₁ : 0< X₁, ∀hX₂ : 0< X₂,
        (41/100:ℝ)≤ length Z X₁ → length Z X₁≤(44/100:ℝ) →
        (41/100:ℝ)≤ length Z X₂ → length Z X₂≤(44/100:ℝ) →
        (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
        length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑i,w i)≤ Cycle61.Arithmetic.B →
      let state := fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
      let inp := affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
        1 t X₁ X₂ hX₁ hX₂
      ∀key∈commonGeometryBins inp 1 1 Z Z ξ, ∀(reflected : Bool)(t' u : ℝ),
        geometryLiveBudget reflected inp 1 1 (Z^(1:ℝ)) Z ξ 1
          (Real.logb Z (volume inp)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
          (fun q=>normPhase (coordinateBlock inp 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
          (Fintype.card T) (9/4) (inp.t+2*Real.pi*(u-(if reflected then -t' else t'))) ≤
        C*geometryHighFactor reflected 64 key*(p.control S)^2*(1+|t|+height)^J*
          (1+‖inp.t+2*Real.pi*(u-(if reflected then -t' else t'))‖)^K*Z^εmass) :
    LiteralAffineGeometryBudget (α:=α) rayM Hray hHray W hW hWs
      η η₀ Q bΦ mesh εmass τ ξ := by
  apply literal_affine_geometry_budget_of_actual rayM Hray hHray W hW hWs η η₀ Q bΦ mesh εmass τ ξ
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.literal_affine_geometry_budget_of_subset_budgets

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineUniformBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePaidAssembly; sha256 abdaa4c54f1bcffe40c298375661eefbdeeedbf0833e8b295d526fb75c5c50b3 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                
                                                            
                                                               
                                                                 

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily QuadraticInitialBound CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle61InitialSource CenteredMomentLogDyadic Cycle61Moment
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyFirstAnnularAdmission ConcretePrimeRowBridge
open RayFourExpansion CenteredMomentPrimePool CenteredMomentAmplificationRadicalFamily
open CenteredMomentPrimeElements CenteredMomentChildRows CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationActiveFactor CenteredMomentAllocatedRayDictionary
open CenteredMomentAmplificationRadicalChoice CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O
local instance paidAssemblySumDecidable {ι : Type} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ geometryAffineErrorRetainedSum geometryMainRetainedSum geometryLiveBudget

/-- Separate the actual shifted first height from the original source
height. This transport changes only polynomial scalar factors. -/
theorem affine_paid_height_product (t firstHeight height : ℝ)(D : ℕ)(hh : 0≤ height) :
    (1+|firstHeight|+height)^D≤(1+|t|+height)^D*(1+‖firstHeight‖)^D := by
  rw [←mul_pow,Real.norm_eq_abs]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [abs_nonneg t,abs_nonneg firstHeight,
    mul_nonneg (abs_nonneg t) (abs_nonneg firstHeight),
    mul_nonneg hh (abs_nonneg firstHeight)]

/-- Join the two already-paid physical components with the retained
zero/tail remainder. The prime average is consumed exactly once. -/
theorem affine_paid_budget_of_components
    (p : Profiles (1/4) (9/4))(Sm Se : Finset (ℕ×ℕ))
    (budget main error average coefficient Cr Cm Ce H t firstHeight height Z εmass : ℝ)
    (Dm De : ℕ)(hCr : 0≤ Cr)(hCm : 0≤ Cm)(hCe : 0≤ Ce)(hH : 0≤ H)
    (hh : 0≤ height)(hZ : 1< Z)(hε : 0≤εmass)
    (hbudget : budget≤ Cr*(p.control {(0,0)})^2*H*Z^(-(1/20:ℝ))+
      average*(coefficient*main+error))
    (hmain : average*coefficient*main≤ Cm*(p.control Sm)^2*H*
      (1+|firstHeight|+height)^Dm*Z^(-(7/60000000:ℝ)))
    (herror : average*error≤ Ce*(p.control Se)^2*H*
      (1+|firstHeight|+height)^De*Z^(-(7/120000000:ℝ))) :
    let S:=({(0,0)}∪Sm)∪Se
    budget≤(Cr+Cm+Ce)*H*(p.control S)^2*(1+|t|+height)^(max Dm De)*
      (1+‖firstHeight‖)^(max Dm De)*Z^εmass := by
  intro S
  have hm : average*coefficient*main≤ Cm*H*(p.control Sm)^2*
      (1+|t|+height)^Dm*(1+‖firstHeight‖)^Dm*Z^(-(7/60000000:ℝ)) := by
    apply hmain.trans
    have hh:=mul_le_mul_of_nonneg_left (affine_paid_height_product t firstHeight height Dm hh)
      (by positivity : 0≤ Cm*(p.control Sm)^2*H)
    have hz:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (zero_lt_one.trans hZ).le (-(7/60000000:ℝ)))
    convert hz using 1;ring
  have he : average*error≤ Ce*H*(p.control Se)^2*
      (1+|t|+height)^De*(1+‖firstHeight‖)^De*Z^(-(7/120000000:ℝ)) := by
    apply herror.trans
    have hh:=mul_le_mul_of_nonneg_left (affine_paid_height_product t firstHeight height De hh)
      (by positivity : 0≤ Ce*(p.control Se)^2*H)
    have hz:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (zero_lt_one.trans hZ).le (-(7/120000000:ℝ)))
    convert hz using 1;ring
  apply geometry_affine_paid_branch_budget p Sm Se budget main error average coefficient
    Cr Cm Ce H (1+|t|+height) (1+‖firstHeight‖) Z (-(7/60000000)) (-(7/120000000)) εmass
    Dm De Dm De hCr hCm hCe hH (by linarith [abs_nonneg t])
    (by linarith [norm_nonneg firstHeight]) hZ (by linarith) (by linarith) hε _ hm he
  convert hbudget using 1;ring

variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance paidAssemblyFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hray : Subgroup (O⧸rayM)ˣ) (hHray : RayOrthogonality.globalUnits rayM≤ Hray)

/-- Explicit pending paid components on the literal actual subset source.
The error receipt is universal in the original retained radical witness;
the assembly therefore cannot silently replace that witness. -/
def GeometryAffinePaidSubsetComponents
    (Sbad : Finset (Ideal O))
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh μ τ : ℝ)(Ψ : 𝓢(ℝ,ℂ))(T : Finset α)
    (Sm Se : Finset (ℕ×ℕ))(Dm De : ℕ)(Cm Ce Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(θ : T→ RayQuotient.Characters rayM Hray)(w σ freq : T→ℝ)(t height : ℝ),
    (∀i,0≤ w i) → (∀i,w i≤ mesh) →
  ∀(hσlo : ∀i,(33/50:ℝ)≤σ i)(hσhi : ∀i,σ i≤(33/50:ℝ)),
    0≤ height → (∀i,|freq i|≤ height) → 1+|t|+height≤ Z^τ →
  ∀(Φ : 𝓢(ℝ,ℂ))(hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hpΦ : ∀x,0≤(Φ x).re)(p : Profiles (1/4) (9/4))(X₁ X₂ : ℝ)
    (hX₁ : 0< X₁)(hX₂ : 0< X₂),
    (41/100:ℝ)≤ length Z X₁ → length Z X₁≤(44/100:ℝ) →
    (41/100:ℝ)≤ length Z X₂ → length Z X₂≤(44/100:ℝ) →
    (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
    length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑i,w i)≤ Cycle61.Arithmetic.B →
  let state:=fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
  let s:=affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
    1 t X₁ X₂ hX₁ hX₂
  let amp:=Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑i,w i)))
  let P:=CenteredMomentPrimePool.primePool rayM Hray Sbad (1/2) 1 (Z^amp)
  ∀key∈commonGeometryBins s 1 1 Z Z (μ/64),∀(reflected : Bool)(firstHeight : ℝ),
  let side:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key
  let phase:=fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q)
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let First:=GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key
  (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
    ‖geometryMainRetainedSum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight hZ key
      1 (Real.logb Z (volume s)) phase‖≤
    Cm*(p.control Sm)^2*side*(1+|firstHeight|+height)^Dm*Z^(-(7/60000000:ℝ)) ∧
  ∀υ : First→ elementPool P→ Fin 3→ RayCharacter→ Character,
    (∀f q i ψ,(υ f q i ψ).modulus.absNorm≤
      radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key f.1.val) ψ)
        fixedBadMask q.val (errorMovingExponent (errorIndex i))) →
    (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z amp (μ/64) (μ/8)
      firstHeight hZ reflected key P υ‖≤
      Ce*(p.control Se)^2*side*(1+|firstHeight|+height)^De*Z^(-(7/120000000:ℝ))

/-- Compose the retained budget with explicit already-paid components.
The common cutoff precedes the detector; subset controls and degrees are
chosen after it and before the moving source. This is conditional on the
component receipts and makes no unconditional endpoint claim. -/
theorem literal_affine_geometry_budget_of_paid_components
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ loss mesh μ εmass τ : ℝ)
    (hloss : 0< loss)(hμ : 0<μ)(hμcap : μ≤1/128)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hεmass : 0≤εmass)
    (hcomponents :
      ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
        (∀x,0≤(Ψ x).re) →
      ∀T : Finset α,∃(Sm Se : Finset (ℕ×ℕ))(Dm De : ℕ)(Cm Ce : ℝ),0≤ Cm ∧ 0≤ Ce ∧
        ∀ᶠZ : ℝ in atTop,GeometryAffinePaidSubsetComponents rayM Hray hHray Sbad W hW hWs
          η η₀ Q bΦ mesh μ τ Ψ T Sm Se Dm De Cm Ce Z) :
    LiteralAffineGeometryBudget (α:=α) rayM Hray hHray W hW hWs
      η η₀ Q bΦ mesh εmass τ (μ/64) := by
  obtain ⟨Cr,hCr,hretained⟩:=actual_affine_geometry_retained_budget (α:=α) rayM Hray hHray
    Sbad hbad W hW hWs loss mesh μ hloss hμ hμcap hmesh
  apply literal_affine_geometry_budget_of_subset_budgets rayM Hray hHray W hW hWs
    η η₀ Q bΦ mesh εmass τ (μ/64)
  intro Ψ hΨ hpΨ T
  obtain ⟨Sm,Se,Dm,De,Cm,Ce,hCm,hCe,hpaid⟩:=hcomponents Ψ hΨ hpΨ T
  refine ⟨max Dm De,max Dm De,({(0,0)}∪Sm)∪Se,Cr+Cm+Ce,by linarith,?_⟩
  filter_upwards [hretained,hpaid] with Z hr hp
  intro hZ θ w σ freq t height hw hwm hσlo hσhi hh hv hcut Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂
    hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcone state s key hkey reflected t' u
  let firstHeight:=s.t+2*Real.pi*(u-(if reflected then -t' else t'))
  have hb:=hr.2 hZ T η₀ θ w σ freq (fun i=>⟨hσlo i,hσhi i⟩) bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone
  obtain ⟨υ,hυ,hbudget⟩:=hb.2.2 reflected key Ψ firstHeight
  have hc:=hp hZ θ w σ freq t height hw hwm hσlo hσhi hh hv hcut Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂
    hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcone key hkey reflected firstHeight
  have he:=hc.2 υ hυ
  have hside:=geometry_high_factor_pos reflected 64 key (by norm_num)
  have joined:=affine_paid_budget_of_components p Sm Se _ _ _ _ _ Cr Cm Ce
    (geometryHighFactor reflected 64 key) t firstHeight height Z εmass Dm De
    hCr.le hCm hCe hside.le hh hZ hεmass
    (by simpa only [geometry_affine_support_constant] using hbudget)
    (by simpa only [geometry_affine_support_constant] using hc.1)
    (by simpa only [geometry_affine_support_constant] using he)
  exact joined

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_paid_height_product
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_paid_budget_of_components
#print axioms OAI.SevenEighths.Cycle61InitialMass.literal_affine_geometry_budget_of_paid_components

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePaidAssembly -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePaidComponents; sha256 07d892988c67aec679ce87fed609a0e86bf6653c18d5ec1c040450c70ce36d76 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                     
                                                                      
                                                              

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonProfile
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle61InitialSource
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Both original retained terms already include their single prime payment.
Specializing the moving state does not alter the original error witness. -/
theorem affine_paid_subset_components_of_specs
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh εaffine τ : ℝ)(Ψ : 𝓢(ℝ,ℂ))(T : Finset α)
    (Sm Se : Finset (ℕ×ℕ))(Dm De : ℕ)(Cm Ce Z : ℝ)
    (hm : GeometryAffineMainPaidSpec M H hH Sbad W hW hWs η η₀ mesh
      (geometryLossUnit 1 εaffine) T Sm Dm Cm Z)
    (he : GeometryAffineErrorPaidSpec M H hH Sbad W hW hWs Ψ η η₀ mesh εaffine T Se De Ce Z) :
    GeometryAffinePaidSubsetComponents M H hH Sbad W hW hWs η η₀ Q bΦ mesh
      (geometryLossUnit 1 εaffine) τ Ψ T Sm Se Dm De Cm Ce Z := by
  intro hZ θ w σ freq t height hw hwm hσlo hσhi hh hv hcut Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂
    hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcone state s amp P key hkey reflected firstHeight
    side phase hK First
  have hη : state.character=η := rfl
  have hmain:=hm hZ θ w σ freq (fun i=>⟨hσlo i,hσhi i⟩) bΦ state hη p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone Ψ reflected key firstHeight height hh hv 1
  constructor
  · simpa only [mul_assoc] using hmain
  · intro υ hυ
    have herror:=he hZ θ w σ freq (fun i=>⟨hσlo i,hσhi i⟩) bΦ state hη p t X₁ X₂ hX₁ hX₂
      hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone reflected key firstHeight height hh hv υ hυ
    simpa only [mul_assoc] using herror

/-- Uniform paid main and error families give the literal geometry budget.
The error family remains an explicit premise until its source aggregation is joined. -/
theorem literal_affine_geometry_budget_of_main_error
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh εaffine τ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (hmain : ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃C : ℝ,0≤ C ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧ GeometryAffineMainPaidSpec M H hH Sbad W hW hWs η η₀ mesh
        (geometryLossUnit 1 εaffine) T S D C Z)
    (herror : ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃C : ℝ,0≤ C ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          GeometryAffineErrorPaidSpec M H hH Sbad W hW hWs Ψ η η₀ mesh εaffine T S D C Z) :
    LiteralAffineGeometryBudget (α:=α) M H hH W hW hWs η η₀ Q bΦ mesh εaffine τ
      (geometryLossUnit 1 εaffine/64) := by
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : geometryLossUnit 1 εaffine≤1/128 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  apply literal_affine_geometry_budget_of_paid_components M H hH Sbad hbad W hW hWs
    η η₀ Q bΦ εaffine mesh (geometryLossUnit 1 εaffine) εaffine τ
    hε hμ hμcap hmesh hε.le
  intro Ψ hΨ hpΨ T
  obtain ⟨Sm,Dm,Cm,hCm,hm⟩:=hmain T
  obtain ⟨Se,De,Ce,hCe,he⟩:=herror Ψ hΨ hpΨ T
  refine ⟨Sm,Se,Dm,De,Cm,Ce,hCm,hCe,?_⟩
  filter_upwards [hm,he] with Z hmZ heZ
  exact affine_paid_subset_components_of_specs M H hH Sbad W hW hWs η η₀ Q bΦ mesh εaffine
    τ Ψ T Sm Se Dm De Cm Ce Z hmZ.2 heZ.2

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_paid_subset_components_of_specs
#print axioms OAI.SevenEighths.Cycle61InitialMass.literal_affine_geometry_budget_of_main_error

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePaidComponents -/
