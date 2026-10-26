/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The ordinary earlier source supplies the actual masked projected subset norms. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.Parent
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialParentBridge
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentEnergyBands CenteredMomentSourceMass
open QRH.Record12518109Source QRH.Record1252270103Reference
open QRH.Record1252270103Source.Collision QRH.Record1252270103Source.Admission
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
local notation "O"=>HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

theorem canonical_projected_parent
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(B lam cap a b bΦ mesh ε Z : ℝ),
      0≤lam → 0<a → 0≤b → 1<Z →
    ∀(η η₀ : Character)(Q : Ideal O)(degree : ℕ)(SP : Finset (ℕ×ℕ))(CP : ℝ),0≤CP →
      InitialAffineAt (α:=α) rayM H hH (SourceFace.mk B lam 0 B 0 cap) W
        2 a b bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q degree SP CP →
    ∀(θ : α→RayQuotient.Characters rayM H)(w freq : α→ℝ)(t height : ℝ),
      (∀i,0≤w i) → (∀i,w i≤mesh) → 0≤height → (∀i,|freq i|≤height) →
      (∑i,w i)≤cap →
    ∀(p : Profiles a b)(X₁ X₂ : ℝ),0<X₁ → 0<X₂ →
      length Z X₁+length Z X₂+lam*(∑i,w i)≤B → b^2*X₁*X₂≤Z^(2:ℝ) →
    ∀(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀R : Ideal O,R≠0 →
    let S:=fun i=>primePool rayM H 2 (Z^(w i))
    let β:=fun i I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (freq i) I
    let atoms:=Finset.univ.biUnion S
    ∀rows : Finset O,projectedSubsetBound rows
      (fun z i (I : atoms)=>normalizedRowCoeff η (fixedBadMask*idealGenerator R) 1 z t
        (S i) (β i) (Z^(w i)) I)
      (weightedPlain η (fixedBadMask*idealGenerator R) 1 t (p.profile 0) (p.profile 1)
        b X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ Z)
      (C*(R.radical.absNorm:ℝ)^δ*(Z^δ)^2*
        (CP*QuadraticInitialBound.diagonalControl Φ*(p.control SP)^2*
          (1+|t|+height)^degree*Z^(1+ε))) := by
  obtain ⟨Cmask,hCmask,hmask⟩:=canonical_parent_shortened (α:=α) rayM H hH W hWs hW δ hδ
  obtain ⟨D,hD,hcoef⟩:=actual_annular_coefficient_bound W hW.continuous hWs (33/50) (33/50)
  let M:=holeDeletionMass*(eulerBound 5 (1/2+δ/(2+1))+eulerBound 432 (1/2+δ/(2+1)))
  let A:=collisionProjectionCost D 256 (Fintype.card α)*M^2*Cmask
  have hcost : 0≤collisionProjectionCost D 256 (Fintype.card α) := by
    unfold collisionProjectionCost
    positivity
  have hA : 0≤A:=mul_nonneg (mul_nonneg hcost (sq_nonneg _)) hCmask.le
  refine ⟨A+1,by linarith,?_⟩
  intro B lam cap a b bΦ mesh ε Z hlam ha hb hZ η η₀ Q degree SP CP hCP hsource
    θ w freq t height hw hmesh hh hv hcap p X₁ X₂ hX₁ hX₂ hbudget hcut Φ hsΦ hΦ R hR
  dsimp only
  intro rows
  let S:=fun i=>primePool rayM H 2 (Z^(w i))
  let β:=fun i I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (freq i) I
  let atoms:=Finset.univ.biUnion S
  let E:=CP*QuadraticInitialBound.diagonalControl Φ*(p.control SP)^2*
    (1+|t|+height)^degree*Z^(1+ε)
  have hZ0 : 0<Z:=zero_lt_one.trans hZ
  have hP (i : α) : 1≤Z^(w i):=Real.one_le_rpow hZ.le (hw i)
  have hE : 0≤E:=by
    have hd:=QuadraticInitialBound.diagonalControl_nonneg Φ
    dsimp [E];positivity
  have hparent := hmask B lam cap a b bΦ mesh (33/50) (33/50) 1 1 ε Z
    hlam ha hb hZ le_rfl le_rfl η η₀ Q degree SP CP hCP hsource θ w freq t height
    hw hmesh hh hv 1 le_rfl le_rfl (by simpa using hcap) p X₁ X₂ hX₁ hX₂
    (by simpa using hbudget) Φ hsΦ hΦ R hR
  simp only [Real.rpow_one] at hparent
  have hbound:=projected_subsets_of_ordinary_parent η (fixedBadMask*idealGenerator R) 1 t
    (p.profile 0) (p.profile 1) b X₁ X₂
    (fun x hx=>(p.support 0 hx).2) (fun x hx=>(p.support 1 hx).2)
    (initialKeep η (internalQ Q η₀)) Φ Z S β (fun i=>Z^(w i)) atoms
    (fun i I hI=>Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hI⟩)
    hX₁ hX₂ hP hZ0 hΦ D (Cmask*(R.radical.absNorm:ℝ)^δ*E) hD
    (by positivity)
    (fun i I _=>hcoef _ _ _ _ (Real.rpow_pos_of_pos hZ0 _) ⟨le_rfl,le_rfl⟩ I)
    (fun i I hi=>(primePool_norm_le rayM H _ (zero_le_one.trans (hP i)) I hi).1)
    (fun i I hi=>(primePool_norm_le rayM H _ (zero_le_one.trans (hP i)) I hi).2)
    δ 2 Z hδ (by norm_num) hZ.le hcut hparent rows
  intro J _ f
  have hhbound:=hbound J f
  calc
    _≤A*(R.radical.absNorm:ℝ)^δ*(Z^δ)^2*E := by
      convert hhbound using 1 <;> dsimp [A,M] <;> ring
    _≤(A+1)*(R.radical.absNorm:ℝ)^δ*(Z^δ)^2*E := by gcongr;linarith

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.canonical_projected_parent
