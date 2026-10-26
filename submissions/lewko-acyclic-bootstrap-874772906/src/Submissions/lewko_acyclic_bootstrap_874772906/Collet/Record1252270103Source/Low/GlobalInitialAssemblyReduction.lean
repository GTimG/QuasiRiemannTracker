/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed-radial physical reduction on canonical Natural initial inputs. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialNaturalPhysical
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
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)

/-- Constants and the eventual threshold precede every natural character,
slot, profile, raw scale and row set. The only scale budget is the clipped sum. -/
theorem uniform_natural_marked_reduction (bΦ B ε ξ saving : ℝ)
    (hbΦ : 0<bΦ) (hB : 0≤B) (hε : 0<ε) (hξ : 0<ξ) :
    ∃Cdiag Ctail : ℝ,0<Cdiag ∧ 0<Ctail ∧
    ∀ᶠZ : ℝ in Filter.atTop,∀hZ1 : 1<Z,∀T : Finset α,
    ∀(η η₀ : Character)(Q R₀ : Ideal O)(θ : T → RayQuotient.Characters rayM H)
      (w v : T → ℝ)(t : ℝ)(p : Profiles (1/4) (9/4))
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
        Cdiag*(p.control {(0,0)})^2*Z*Z^ε+
        Ctail*(p.control {(0,0)})^2*Z*Z^(-saving))+
      2*markedFiniteEnergy s R₀ 1 (9/4) Y₁ Y₂ rows (initialKeep η (internalQ Q η₀)) Φ Z := by
  have hall (T : Finset α):=natural_marked_initial_fixed_first_physical (ι:=T)
    rayM H hH W hW hsW bΦ B ε ξ saving hbΦ hB hε hξ
  choose Sd St Cd Ct hCd hCt ht using hall
  let L:=initialSlotBound W hW hsW
  let Ψ:=initialRadialBump bΦ hbΦ
  let ad:=fun T : Finset α=>Cd T*(Sd T).sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*L^(2*Fintype.card T)
  let aTail:=fun T : Finset α=>Ct T*(St T).sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*L^(2*Fintype.card T)
  have hL0 : 0≤L:=zero_le_one.trans (initialSlotBound_ge_one W hW hsW)
  have had (T : Finset α) : 0≤ad T :=
    mul_nonneg (mul_nonneg (hCd T).le (apply_nonneg _ _)) (pow_nonneg hL0 _)
  have hat (T : Finset α) : 0≤aTail T :=
    mul_nonneg (mul_nonneg (hCt T).le (apply_nonneg _ _)) (pow_nonneg hL0 _)
  let Dd:=1+∑T : Finset α,ad T
  let Dt:=1+∑T : Finset α,aTail T
  have hDd : 0<Dd := by
    have hs:=Finset.sum_nonneg (s:=Finset.univ) (fun T _=>had T)
    dsimp [Dd];linarith
  have hDt : 0<Dt := by
    have hs:=Finset.sum_nonneg (s:=Finset.univ) (fun T _=>hat T)
    dsimp [Dt];linarith
  have hdd (T : Finset α) : ad T≤Dd := by
    have hh:=Finset.single_le_sum (fun T _=>had T) (Finset.mem_univ T)
    dsimp [Dd];linarith
  have htt (T : Finset α) : aTail T≤Dt := by
    have hh:=Finset.single_le_sum (fun T _=>hat T) (Finset.mem_univ T)
    dsimp [Dt];linarith
  refine ⟨Dd,Dt,hDd,hDt,?_⟩
  have hevent : ∀ᶠZ : ℝ in Filter.atTop,∀T : Finset α,_:=Filter.eventually_all.mpr ht
  filter_upwards [hevent] with Z hz
  intro hZ1 T η η₀ Q R₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hbudget rows Φ hΦ hsΦ
  dsimp only
  let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ1) η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  have hred:=hz T hZ1 η η₀ Q R₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hbudget rows Φ hΦ hsΦ
  have hc:=initialInput_plain_control rayM H hH W hW hsW Z (zero_lt_one.trans hZ1)
    η η₀ R₀ θ w v t p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  change (plainControl s (p.profile 0) (p.profile 1))^2≤L^(2*Fintype.card T)*(p.control {(0,0)})^2 at hc
  have hdiag : Cd T*(plainControl s (p.profile 0) (p.profile 1))^2*
      (Sd T).sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*Z*Z^ε≤Dd*(p.control {(0,0)})^2*Z*Z^ε := by
    have h1:=mul_le_mul_of_nonneg_left hc
      (mul_nonneg (hCd T).le (apply_nonneg ((Sd T).sup (schwartzSeminormFamily ℝ ℝ ℂ)) Ψ))
    have h2:=mul_le_mul_of_nonneg_right (hdd T) (sq_nonneg (p.control {(0,0)}))
    have h3 : Cd T*(plainControl s (p.profile 0) (p.profile 1))^2*
        (Sd T).sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ≤Dd*(p.control {(0,0)})^2 := by
      dsimp [ad] at h2
      nlinarith only [h1,h2]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h3 (zero_lt_one.trans hZ1).le) (Real.rpow_nonneg (zero_lt_one.trans hZ1).le _)
  have htail : Ct T*(plainControl s (p.profile 0) (p.profile 1))^2*
      (St T).sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*Z*Z^(-saving)≤Dt*(p.control {(0,0)})^2*Z*Z^(-saving) := by
    have h1:=mul_le_mul_of_nonneg_left hc
      (mul_nonneg (hCt T).le (apply_nonneg ((St T).sup (schwartzSeminormFamily ℝ ℝ ℂ)) Ψ))
    have h2:=mul_le_mul_of_nonneg_right (htt T) (sq_nonneg (p.control {(0,0)}))
    have h3 : Ct T*(plainControl s (p.profile 0) (p.profile 1))^2*
        (St T).sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ≤Dt*(p.control {(0,0)})^2 := by
      dsimp [aTail] at h2
      nlinarith only [h1,h2]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h3 (zero_lt_one.trans hZ1).le) (Real.rpow_nonneg (zero_lt_one.trans hZ1).le _)
  exact hred.trans (add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hdiag) htail)
    (mul_nonneg (by norm_num) (diagonalControl_nonneg Φ))) le_rfl)

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.uniform_natural_marked_reduction
