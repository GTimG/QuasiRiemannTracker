/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed-radial physical reduction on canonical Natural initial inputs. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialFixedPhysical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.InitialInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState QuadraticInitialBound
open CenteredMomentEnergyOriginalProfileControl
open OAI.SevenEighths.Record1252270103Source.Collision
open QRH.Record1252270103Source.High.CoupledFirst
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)

/-- The plain control has no height loss: the canonical annular slot bound was
chosen uniformly before all slot frequencies. -/
theorem initialInput_plain_control (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal O)
    (θ : ι → RayQuotient.Characters rayM H) (w v : ι → ℝ) (t : ℝ)
    {a b : ℝ} (p : Profiles a b) (ha : 0<a)
    (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hprod : Y₁*Y₂=X₁*X₂) :
    (plainControl (initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p ha
      X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod) (p.profile 0) (p.profile 1))^2≤
      (initialSlotBound W hW hsW)^(2*Fintype.card ι)*(p.control {(0,0)})^2 := by
  simpa using plain_control_sq_le
    (initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p ha
      X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod) p ∅ (Fintype.card ι)
      (initialSlotBound W hW hsW) (initialSlotBound_ge_one W hW hsW) le_rfl (fun _=>le_rfl)

/-- Constants and the eventual threshold precede every natural character,
slot, profile, raw scale and row set. The only scale budget is the clipped sum. -/
theorem natural_marked_initial_fixed_first_physical (bΦ B ε ξ saving : ℝ)
    (hbΦ : 0<bΦ) (hB : 0≤B) (hε : 0<ε) (hξ : 0<ξ) :
    ∃Sdiag Stail : Finset (ℕ×ℕ),∃Cdiag Ctail : ℝ,0<Cdiag ∧ 0<Ctail ∧
    ∀ᶠZ : ℝ in Filter.atTop,∀hZ1 : 1<Z,
    ∀(η η₀ : Character)(Q R₀ : Ideal O)(θ : ι → RayQuotient.Characters rayM H)
      (w v : ι → ℝ)(t : ℝ)(p : Profiles (1/4) (9/4))
      (X₁ X₂ Y₁ Y₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)(hY₁ : 0<Y₁)(hY₂ : 0<Y₂)
      (hprod : Y₁*Y₂=X₁*X₂),
    length Z X₁+length Z X₂+∑i,w i≤B →
    ∀(rows : Finset O)(Φ : 𝓢(ℝ,ℂ)),(∀x,0≤(Φ x).re) →
      Function.support (Φ:ℝ → ℂ)⊆Set.Iic bΦ →
    let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ1) η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    markedFiniteEnergy s R₀ 1 (9/4) X₁ X₂ rows (initialKeep η (internalQ Q η₀)) Φ Z≤
      2*diagonalControl Φ*(
        physicalMass s (markedSourceModifier 1 1 1 1 (fun _=>1)) R₀ 1
          (fixedBadMask*idealGenerator R₀) 1 (initialRadialBump bΦ hbΦ) Z Z ξ/volume s.toData+
        Cdiag*(plainControl s (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) (initialRadialBump bΦ hbΦ)*Z*Z^ε+
        Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) (initialRadialBump bΦ hbΦ)*Z*Z^(-saving))+
      2*markedFiniteEnergy s R₀ 1 (9/4) Y₁ Y₂ rows (initialKeep η (internalQ Q η₀)) Φ Z := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,h⟩:=marked_initial_fixed_first_physical bΦ hbΦ
    (fun _ : ι=>(2:ℝ)) (1/4) (9/4) B ε ξ saving
    (fun _=>by norm_num) (by norm_num) (by norm_num) hB hε hξ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,?_⟩
  filter_upwards [h] with Z hz
  intro hZ1 η η₀ Q R₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hbudget rows Φ hΦ hsΦ
  dsimp only
  let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ1) η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  have hV : volume s.toData≤Z^B :=
    (initialInput_volume_le_clipped rayM H hH W hW hsW Z (zero_lt_one.trans hZ1)
      η η₀ R₀ θ w v t p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hZ1).trans
      (Real.rpow_le_rpow_of_exponent_le hZ1.le hbudget)
  have hKi : Z⁻¹≤Z^B :=
    (inv_le_one_of_one_le₀ hZ1.le).trans (Real.one_le_rpow hZ1.le hB)
  exact hz.2 s (p.profile 0) (p.profile 1) rfl rfl (p.support 0) (p.support 1)
    (fun _=>le_rfl) R₀ 1 (9/4) le_rfl le_rfl rows (initialKeep η (internalQ Q η₀)) Φ Z
    (zero_lt_one.trans hZ1) hΦ hsΦ hV hKi

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.initialInput_plain_control
#print axioms QRH.Record1252270103Low.natural_marked_initial_fixed_first_physical
