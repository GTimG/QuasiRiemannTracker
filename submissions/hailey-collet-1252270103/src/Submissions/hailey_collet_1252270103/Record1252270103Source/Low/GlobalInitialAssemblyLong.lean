/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual marked first-physical leaf, analytic reference and diagonal/tail
reduction joined uniformly on the long-factor branch. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialAssemblyAlgebra
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialAssemblyContract
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialAssemblyReduction
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialAssemblyReference
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentExceptionalAmplitudePair QuadraticInitialBound CenteredMomentEnergyBandMonotonicity
open QRH.Record1252270103Source
open QRH.Record1252270103Source.High.CoupledFirst
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O

theorem uniform_initial_marked_long
    (B lam cap cross K κ mesh ξ ε : ℝ) (cell : ℝ→ℝ)
    (hB0 : 0≤B) (hB1 : B≤1) (hlam : 1≤lam) (hξ : 0<ξ) (hε : 0<ε)
    (hκlo : 7/10≤κ) (hκhi : κ≤3/4) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κ)
    (hK : 6*κ≤K) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hmesh : mesh≤Cycle61FirstActual.comparisonMesh 1 1 (ε/2))
    (hcells : ReferenceWidthCells cross cap K cell)
    (hphysical : InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell)
    (α : Type) [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2≤bΦ) (η : Character) :
    ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),
    ∀η₀ : Character,∀Q : Ideal O,Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤Ideal.span {(72:O)} →
    ∀R₀ : Ideal O,R₀≠0 → ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
    ∀hZ : 1<Z,∀T : Finset α,
    ∀(θ : T→RayQuotient.Characters rayM H)(w v : T→ℝ)(t height : ℝ),
      (∀i,0≤w i) → (∀i,w i≤mesh) → 0≤height → (∀i,|v i|≤height) →
    ∀p : Profiles (1/4) (9/4),∀X₁ X₂ : ℝ,∀hX₁ : 0<X₁,∀hX₂ : 0<X₂,
      (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1 →
      cross≤∑i,w i →
    let r:=49/100-K*cell (∑i,w i)
    Z^r≤X₁ → Z^r≤X₂ →
    let Y₂:=Z^r
    let Y₁:=X₁*X₂/Y₂
    let hY₂ : 0<Y₂:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    let hY₁ : 0<Y₁:=div_pos (mul_pos hX₁ hX₂) hY₂
    let hprod : Y₁*Y₂=X₁*X₂:=div_mul_cancel₀ _ hY₂.ne'
    let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(rows : Finset O)(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ →
      (∀x,0≤(Φ x).re) →
    markedFiniteEnergy s R₀ 1 (9/4) X₁ X₂ rows (initialKeep η (internalQ Q η₀)) Φ Z≤
      C*diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree*Z^(1+ε) := by
  obtain ⟨dp,Sp,hp⟩:=hphysical α rayM H hH W hW hsW bΦ hbΦ η
  obtain ⟨_,dr,Sr,hr⟩:=uniform_initialInput_short_reference (α:=α) rayM H hH κ K hκlo hκhi
    hκbeta hK (fun _ : Unit=>η) W hsW hW (1/4) (9/4) bΦ 1 1 2 ε
    (by norm_num) le_rfl (by norm_num) (by linarith) (by norm_num) le_rfl hε (by norm_num) hbeta
  obtain ⟨Cd,Ct,hCd,hCt,hred⟩:=uniform_natural_marked_reduction (α:=α) rayM H hH W hW hsW
    bΦ B ε ξ 0 (by linarith) hB0 hε hξ
  let S:=insert (0,0) (Sp∪Sr)
  let d:=dp+dr
  have hSp : Sp⊆S:=fun x hx=>Finset.mem_insert_of_mem (Finset.mem_union_left Sr hx)
  have hSr : Sr⊆S:=fun x hx=>Finset.mem_insert_of_mem (Finset.mem_union_right Sp hx)
  have hS0 : {(0,0)}⊆S:=by simp [S]
  refine ⟨d,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨Cp,hCp,hp⟩:=hp η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨Cr,hCr,hr⟩:=hr η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  refine ⟨2*(Cp+Cd+Ct)+2*Cr,by positivity,?_⟩
  filter_upwards [hp,hr,hred,eventually_ge_atTop (6:ℝ)] with Z hp hr hred hZ6
  intro hZ T θ w v t height hw hwm hh hv p X₁ X₂ hX₁ hX₂ hadm hcross
  dsimp only
  intro hlong₁ hlong₂ rows Φ hsΦ hΦ
  let r:=49/100-K*cell (∑i,w i)
  let Y₂:=Z^r
  let Y₁:=X₁*X₂/Y₂
  have hZ0 : 0<Z:=zero_lt_one.trans hZ
  have hY₂ : 0<Y₂:=Real.rpow_pos_of_pos hZ0 r
  have hY₁ : 0<Y₁:=div_pos (mul_pos hX₁ hX₂) hY₂
  have hprod : Y₁*Y₂=X₁*X₂:=div_mul_cancel₀ _ hY₂.ne'
  let s:=initialInput rayM H hH W hW hsW Z hZ0 η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  have hw0 : 0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hwcap : (∑i,w i)≤cap:=by simpa [globalFace] using hadm.2.2.2.2.2.1
  obtain ⟨hc,hcap,hr0⟩:=hcells _ hcross hwcap
  have hcell0 : 0≤cell (∑i,w i):=hw0.trans hc
  have hraw:=global_raw_plain_product B lam cap Z X₁ X₂ (∑i,w i) hZ hX₁ hX₂
    (by linarith) hw0 hadm
  have hsc:=reference_scales Z X₁ X₂ r B hZ hX₁ hX₂ hr0 hraw
  have hcut:=global_reference_cutoff B lam cap Z X₁ X₂ (∑i,w i) r hZ6 hX₁ hX₂
    (by linarith) hw0 hB1 hadm
  have href:=hr hZ T () 1 B r r (cell (∑i,w i)) le_rfl le_rfl hr0 hcell0 le_rfl
    (by dsimp [r];ring_nf;norm_num) Φ hsΦ hΦ p θ w v t height hw
    (fun i=>(hwm i).trans hmesh) hh hv hc Y₁ Y₂ hY₁ hY₂ hsc.2.2.2 le_rfl hcut
    X₁ X₂ hX₁ hX₂ hprod rows
  simp only [Real.rpow_one] at href
  have hphys:=hp hZ T θ w v t height hw hwm hh hv p X₁ X₂ hX₁ hX₂ hadm hcross hlong₁ hlong₂
  change physicalMass s (markedSourceModifier 1 1 1 1 (fun _=>1)) R₀ 1
    (fixedBadMask*idealGenerator R₀) 1 (initialRadialBump bΦ (by linarith)) Z Z ξ/volume s.toData≤
      Cp*(p.control Sp)^2*(1+|t|+height)^dp*Z^(1+ε) at hphys
  have hbudget : length Z X₁+length Z X₂+∑i,w i≤B := by
    have hg:=hadm.2.2.2.2.2.2
    change length Z X₁+length Z X₂+lam*(∑i,w i)≤B*1 at hg
    nlinarith
  have hreduce:=hred hZ T η η₀ Q R₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hbudget rows Φ hΦ hsΦ
  exact common_initial_bound_algebra _ _ _ (diagonalControl Φ)
    (p.control {(0,0)}) (p.control Sp) (p.control Sr) (p.control S) (1+|t|+height)
    Z ε Cp Cd Ct Cr dp dr (diagonalControl_nonneg Φ) (p.control_nonneg _)
    (p.control_nonneg _) (p.control_nonneg _) (profile_control_mono p hS0)
    (profile_control_mono p hSp) (profile_control_mono p hSr)
    (by linarith [abs_nonneg t]) hZ.le hε.le hCp.le hCd.le hCt.le hCr.le hphys href hreduce

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.uniform_initial_marked_long
