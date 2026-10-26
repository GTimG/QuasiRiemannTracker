/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Either short original factor is covered by the actual reference theorem. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyReference
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyContract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialSwap
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthOriginal
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentDetectorEnergyInitialState QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentEnergyZeroGrowthOriginal
open CenteredMomentPrimeSlot
open QRH.Record1252270103Source
local notation "O"=>HeckeFamily.O

lemma markedPositiveRow_swap_any {ι : Type*} [Fintype ι] [instD : DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) :
    markedPositiveRow η m A z W₂ W₁ b S β P t X₂ X₁=
      markedPositiveRow η m A z W₁ W₂ b S β P t X₁ X₂ := by
  have hdec : instD=Classical.decEq ι:=Subsingleton.elim _ _
  cases hdec
  exact markedPositiveRow_swap η m A z t W₁ W₂ b X₁ X₂ S β P

theorem uniform_initial_marked_short
    (B lam cap cross K κ mesh ε : ℝ) (cell : ℝ→ℝ)
    (hB1 : B≤1) (hlam : 0≤lam) (hε : 0<ε)
    (hκlo : 7/10≤κ) (hκhi : κ≤3/4) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κ)
    (hK : 6*κ≤K) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hmesh : mesh≤Cycle61FirstActual.comparisonMesh 1 1 (ε/2))
    (hcells : ReferenceWidthCells cross cap K cell)
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
      cross≤∑i,w i → min X₁ X₂≤Z^(49/100-K*cell (∑i,w i)) →
    ∀Y₁ Y₂ : ℝ,∀hY₁ : 0<Y₁,∀hY₂ : 0<Y₂,∀hprod : Y₁*Y₂=X₁*X₂,
    let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(rows : Finset O)(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ →
      (∀x,0≤(Φ x).re) →
    markedFiniteEnergy s R₀ 1 (9/4) X₁ X₂ rows (initialKeep η (internalQ Q η₀)) Φ Z≤
      C*diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree*Z^(1+ε) := by
  obtain ⟨_,d,S,hr⟩:=uniform_initialInput_short_reference (α:=α) rayM H hH κ K hκlo hκhi
    hκbeta hK (fun _ : Unit=>η) W hsW hW (1/4) (9/4) bΦ 1 1 2 ε
    (by norm_num) le_rfl (by norm_num) (by linarith) (by norm_num) le_rfl hε (by norm_num) hbeta
  refine ⟨d,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨C,hC,hr⟩:=hr η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  refine ⟨C,hC,?_⟩
  filter_upwards [hr,eventually_ge_atTop (6:ℝ)] with Z hr hZ6
  intro hZ T θ w v t height hw hwm hh hv p X₁ X₂ hX₁ hX₂ hadm hcross hshort
    Y₁ Y₂ hY₁ hY₂ hprod
  dsimp only
  intro rows Φ hsΦ hΦ
  let r:=49/100-K*cell (∑i,w i)
  have hw0 : 0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hwcap : (∑i,w i)≤cap:=by simpa [globalFace] using hadm.2.2.2.2.2.1
  obtain ⟨hc,hcap,hr0⟩:=hcells _ hcross hwcap
  have hcell0 : 0≤cell (∑i,w i):=hw0.trans hc
  have hcut : (9/4:ℝ)^2*X₁*X₂≤Z^(2:ℝ) := by
    have h:=global_reference_cutoff B lam cap Z X₁ X₂ (∑i,w i) 0 hZ6 hX₁ hX₂ hlam hw0 hB1 hadm
    simpa only [Real.rpow_zero,div_one,mul_one,mul_assoc] using h
  have hlength (X : ℝ) : X≤Z^(length Z X) := by
    rw [length,Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
      (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have ordered (p' : Profiles (1/4) (9/4)) (U₁ U₂ : ℝ) (hU₁ : 0<U₁) (hU₂ : 0<U₂)
      (hU : U₂≤Z^r) (hcut' : (9/4:ℝ)^2*U₁*U₂≤Z^(2:ℝ)) :
      markedFiniteEnergy
        (initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
          p' (by norm_num) U₁ U₂ U₁ U₂ hU₁ hU₂ hU₁ hU₂ rfl)
        R₀ 1 (9/4) U₁ U₂ rows (initialKeep η (internalQ Q η₀)) Φ Z≤
        C*diagonalControl Φ*(p'.control S)^2*(1+|t|+height)^d*Z^(1+ε) := by
    have h:=hr hZ T () 1 (length Z U₁) r r (cell (∑i,w i)) le_rfl le_rfl hr0
      hcell0 le_rfl (by dsimp [r];ring_nf;norm_num) Φ hsΦ hΦ p' θ w v t height hw
      (fun i=>(hwm i).trans hmesh) hh hv hc U₁ U₂ hU₁ hU₂ (hlength U₁) hU hcut'
      U₁ U₂ hU₁ hU₂ rfl rows
    simpa only [Real.rpow_one] using h
  rcases min_le_iff.mp hshort with hshort₁|hshort₂
  · have hswap:=ordered (swapProfiles p) X₂ X₁ hX₂ hX₁ hshort₁ (by nlinarith only [hcut])
    rw [swapProfiles_control] at hswap
    convert hswap using 1
    unfold markedFiniteEnergy
    apply Finset.sum_congr rfl
    intro z hz
    change (if initialKeep η (internalQ Q η₀) z then
      ‖markedPositiveRow η (fixedBadMask*idealGenerator R₀) 1 z (p.profile 0) (p.profile 1) (9/4)
        (fun i=>primePool rayM H 2 (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (v i) I)
        (fun i=>Z^(w i)) t X₁ X₂‖^2*(Φ (‖eisEmbedding z‖^2/Z)).re else 0)=_
    simp only [initialInput,swapProfiles,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      initialSlotProfile,HeckePrimeAnnular.annularWeight]
    rw [markedPositiveRow_swap_any]
  · exact ordered p X₁ X₂ hX₁ hX₂ hshort₂ hcut

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.uniform_initial_marked_short
