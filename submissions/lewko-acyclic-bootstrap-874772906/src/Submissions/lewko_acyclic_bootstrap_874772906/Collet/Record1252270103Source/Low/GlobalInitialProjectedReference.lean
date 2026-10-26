/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The proved variable short-reference supplier pays every original-slot marked projection. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialReference
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialSubsets
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState ConcretePrimeRowBridge CenteredMomentPrimeSlot
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentSecondHeightFamily
open QRH.Record1252270103Restoration QRH.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

theorem actual_projected_short_reference
    (κ Kcap : ℝ) (hκlo : 7/10≤κ) (hκhi : κ≤3/4)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κ) (hKcap : 6*κ≤Kcap)
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Wslot : ℝ → ℂ) (hsSlot : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslot : ContDiff ℝ ∞ Wslot)
    (a b bΦ Mmin Mmax Bpair ε : ℝ) (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hbΦ : 0<bΦ) (hMmin : 0<Mmin) (hMM : Mmin≤Mmax) (hε : 0<ε) (hBpair : 0≤Bpair)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    0<Cycle61FirstActual.comparisonMesh Mmin Mmax (ε/2) ∧
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∀η₀ : Character,∀Q : Ideal O,
      Q≤rayM  → internalQ Q η₀≠0  → internalQ Q η₀≠⊤  → internalQ Q η₀≤Ideal.span {(72:O)}  → 
    ∀R₀ : Ideal O,R₀≠0  → ∃C : ℝ,0<C ∧∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀j : Label,∀M along short r cap : ℝ,Mmin≤M  → M≤Mmax  → 
      0≤r  → 0≤cap  → short≤r  → r+Kcap*cap≤49*M/100  → 
    ∀Φ : 𝓢(ℝ,ℂ),Function.support (Φ:ℝ → ℂ)⊆Set.Iic bΦ  → (∀x,0≤(Φ x).re)  → 
    ∀p : Profiles a b,∀(θ : α → RayQuotient.Characters rayM H)(w freq : α → ℝ)(t height : ℝ),
      (∀i,0≤w i)  → (∀i,w i≤Cycle61FirstActual.comparisonMesh Mmin Mmax (ε/2))  → 
      0≤height  → (∀i,|freq i|≤height)  → (∑i,w i)≤cap  → 
    ∀Y₁ Y₂ : ℝ,0<Y₁  → 0<Y₂  → Y₁≤Z^along  → Y₂≤Z^short  → b^2*Y₁*Y₂≤Z^Bpair  → 
    ∀atoms : Finset (Ideal O),(∀i,primePool rayM H 2 (Z^(w i))⊆atoms)  → ∀rows : Finset O,
    projectedSubsetBound rows
      (fun z i (I : atoms)=>normalizedRowCoeff (anchors j) (fixedBadMask*idealGenerator R₀) 1 z t
        (primePool rayM H 2 (Z^(w i)))
        (fun I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (33/50) (freq i) I) (Z^(w i)) I)
      (weightedPlain (anchors j) (fixedBadMask*idealGenerator R₀) 1 t (p.profile 0) (p.profile 1)
        b Y₁ Y₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M))
      (C*diagonalControl Φ*(p.control S)^2*(1+|t|+|t|+height)^degree*Z^(M+ε)) := by
  obtain ⟨hm,d,S,href⟩:=actual_squarefree_short_reference_outer_height rayM H hH κ Kcap
    hκlo hκhi hκbeta hKcap anchors (Finset.univ : Finset α) Wslot hsSlot hWslot
    a b bΦ Mmin Mmax Bpair ε ha haUpper hb hbΦ hMmin hMM hε hBpair hbeta
  obtain ⟨B,hB,hcoeff⟩:=actual_annular_coefficient_bound Wslot hWslot.continuous hsSlot (33/50) (33/50)
  let cost:=collisionProjectionCost B 256 (Fintype.card α)
  have hcost : 0<cost := by dsimp [cost,collisionProjectionCost];positivity
  refine ⟨hm,d,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨C,hC,ht⟩:=href η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  refine ⟨cost*C,mul_pos hcost hC,?_⟩
  filter_upwards [ht] with Z hz
  refine ⟨hz.1,?_⟩
  intro j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p θ w freq t height
    hw hwmesh hheight hfreq hslots Y₁ Y₂ hY₁ hY₂ hY₁ref hY₂ref hcut atoms hatoms rows
  let pool:=fun i=>primePool rayM H 2 (Z^(w i))
  let β:=fun i I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (33/50) (freq i) I
  let P:=fun i=>Z^(w i)
  let E:=C*diagonalControl Φ*(p.control S)^2*(1+|t|+|t|+height)^d*Z^(M+ε)
  have hZ : 0<Z:=zero_lt_one.trans hz.1
  have hP (i : α) : 0<P i:=Real.rpow_pos_of_pos hZ _
  have hP1 (i : α) : 1≤P i:=Real.one_le_rpow hz.1.le (hw i)
  have hE : 0≤E := by dsimp [E];have hd:=diagonalControl_nonneg Φ;positivity
  have hsub (F : Finset α) : (∑i∈F,w i)≤cap :=
    (Finset.sum_le_univ_sum_of_nonneg (fun i=>hw i)).trans hslots
  have hfull:=fullSubsetBound_of_squarefree_subsets (anchors j) (fixedBadMask*idealGenerator R₀) 1 t
    (p.profile 0) (p.profile 1) b Y₁ Y₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M)
    pool β P atoms hatoms hY₁ hY₂ hP (Real.rpow_pos_of_pos hZ _) hpΦ E
    (fun F=>hz.2 j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p F
      (Finset.subset_univ F) θ w freq t height hw hwmesh hheight hfreq (hsub F)
      Y₁ Y₂ hY₁ hY₂ hY₁ref hY₂ref hcut) rows
  have hh:=normalized_projectedSubsetBound_of_fullSubsetBound (anchors j)
    (fixedBadMask*idealGenerator R₀) 1 t rows
    (weightedPlain (anchors j) (fixedBadMask*idealGenerator R₀) 1 t (p.profile 0) (p.profile 1)
      b Y₁ Y₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M))
    pool β P atoms B E hB hE hP1
    (fun i I _=>hcoeff _ _ _ _ (hP i) ⟨le_rfl,le_rfl⟩ I)
    (fun i I hi=>(primePool_norm_le rayM H (P i) (hP i).le I hi).1)
    (fun i I hi=>(primePool_norm_le rayM H (P i) (hP i).le I hi).2)
    (Fintype.card α) le_rfl hfull
  convert hh using 1 <;> dsimp [E,cost] <;> ring

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.actual_projected_short_reference
