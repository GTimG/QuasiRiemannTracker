import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
import Candidate.Target830.Source.LowPhysical.AffineCaps
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryExceptionalErrorNormPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePoolCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePrimeGates
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Cycle63.Moment.InitialState
import Candidate.Cycle63.Moment.CellGeometry

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Target830.Source.LowPhysical
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CanonicalQuadraticSieve
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedRayDictionary CenteredMomentPrimeElements
open CenteredMomentCommonAllocationSum
open Cycle63InitialSource Cycle63Moment
local notation "O" => HeckeFamily.O

private theorem affine_exceptional_quarter (Z X₁ X₂ ell : ℝ)
    (hZ : 1<Z) (hX₁ : 0<X₁) (_hX₂ : 0<X₂)
    (hlo₁ : (81/200:ℝ)≤length Z X₁) (hlo₂ : (81/200:ℝ)≤length Z X₂) :
    let r:=Z^((1+ell)/4-ell/4)
    r≤X₁ ∧ r≤X₂ ∧ r≤comparisonFirst Z 1 ∧
      r≤comparisonSecond Z 1 X₁ X₂ := by
  intro r
  have hr : r=Z^(1/4:ℝ) := congrArg (fun e : ℝ=>Z^e) (by ring)
  have hq : 0<Z^(1/4:ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hx (X : ℝ) (hlo : (81/200:ℝ)≤length Z X) : Z^(1/4:ℝ)≤X := by
    rw [initial_scale_exact Z X 1 hZ (by norm_num) (by simpa only [mul_one] using hlo)]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hx₁:=hx X₁ hlo₁
  have hx₂:=hx X₂ hlo₂
  rw [hr]
  refine ⟨hx₁,hx₂,le_rfl,?_⟩
  exact (le_div_iff₀ hq).mpr (mul_le_mul hx₁ hx₂ hq.le hX₁.le)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineExceptionalFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

/-- The threshold and profile cap precede every slot subset, smooth plain
profile, fixed-parent radial function, and both heights. No energy is assumed. -/
theorem eventual_actual_affine_exceptional_source_gates
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) :
    ∃Cs : ℝ,1≤Cs ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
        (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (81/200:ℝ)≤length Z X₁ → (81/200:ℝ)≤length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) → (∑i,w i)≤(1/25:ℝ) →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      GeometryAffineExceptionalSourceGates inp p (Fintype.card α) Cs Z := by
  obtain ⟨Cs,bs,bp,hCs,hbs,hbp,hfixed⟩:=fixed_affine_source_caps (α:=α) rayM H hH W hW
    1 2 (33/50) (33/50) (1/4) (9/4) (by norm_num) hWs
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [eventual_affine_polynomial_caps (α:=α) rayM H hH W hW
      1 2 (33/50) (33/50) (1/4) (9/4) 1 (by norm_num) hWs
      (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (9/4:ℝ)] with Z hc hlarge
  refine ⟨hc.1,?_⟩
  intro T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi inp
  have hcaps:=hc.2 T η₀ θ w σ freq hσ bΦ state p 1 t X₁ X₂ hX₁ hX₂
    (by norm_num) le_rfl hw (by simpa only [mul_one] using hlo₁)
    (by simpa only [mul_one] using hlo₂) (by simpa only [mul_one] using hhi₁)
    (by simpa only [mul_one] using hhi₂) (by simpa only [one_div] using hwhi)
  have hfixed':=hfixed T η₀ θ w σ freq hσ state p 1 t X₁ X₂ hX₁ hX₂
  have he:=affine_endpoints rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    (by norm_num) (by norm_num)
  have hplain (j : Fin 2)(x : ℝ)(hne : p.profile j x≠0) : (1/4:ℝ)≤x :=
    (p.support j hne).1
  have hzero (j : Fin 2) : p.profile j 0=0 := by
    by_contra hne
    have hh:=hplain j 0 hne
    norm_num at hh
  have hpool:=affine_individual_pool_cap rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    1 hc.1 (by norm_num) le_rfl (by norm_num)
    (by norm_num; linarith) hlarge hw (by simpa using hwhi) (by simpa using hhi₁) (by simpa using hhi₂)
  have hquarter:=affine_exceptional_quarter Z X₁ X₂
    (Real.logb Z (inp.η.modulus.absNorm:ℝ)) hc.1 hX₁ hX₂ hlo₁ hlo₂
  refine ⟨hfixed'.1,hfixed'.2.1,rfl,rfl,rfl,?_,?_,rfl,rfl,hzero 0,hzero 1,
    hplain 0,hplain 1,?_,?_,?_,?_,?_,hquarter.1,hquarter.2.1,hquarter.2.2.1,hquarter.2.2.2⟩
  · exact ⟨he.1.trans (by norm_num),he.2⟩
  · intro i
    exact Real.one_le_rpow hc.1.le (hw i)
  · simpa only [show (1:ℝ)+1=2 by norm_num] using hcaps.2.2.1
  · exact hcaps.2.1.trans (by norm_num)
  · change 0<(∏i : T,(2:ℝ))*(9/4)*(9/4)*(X₁*X₂)*(∏i : T,Z^(w i))
    exact mul_pos (mul_pos (mul_pos (mul_pos (Finset.prod_pos (fun _ _=>by norm_num))
      (by norm_num)) (by norm_num)) (mul_pos hX₁ hX₂))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (zero_lt_one.trans hc.1) _))
  · simpa only [show (1:ℝ)+2=3 by norm_num] using hcaps.2.2.2.1
  · intro i I hI
    exact (hpool i I hI).trans (Real.rpow_le_rpow_of_exponent_le hc.1.le (by norm_num))


end
end OAI.SevenEighths.Target830.Source.LowPhysical
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.eventual_actual_affine_exceptional_source_gates
