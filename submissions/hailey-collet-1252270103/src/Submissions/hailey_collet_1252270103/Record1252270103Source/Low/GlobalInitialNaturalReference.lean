/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The proved variable short-reference supplier pays every original-slot marked projection. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialFiniteJoin
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

theorem actual_initialInput_short_reference
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
    ∀R₀ : Ideal O,R₀≠0  → ∃C : ℝ,0<C ∧∀ᶠZ : ℝ in atTop,∀hZ1 : 1<Z,
    ∀j : Label,∀M along short r cap : ℝ,Mmin≤M  → M≤Mmax  → 
      0≤r  → 0≤cap  → short≤r  → r+Kcap*cap≤49*M/100  → 
    ∀Φ : 𝓢(ℝ,ℂ),Function.support (Φ:ℝ → ℂ)⊆Set.Iic bΦ  → (∀x,0≤(Φ x).re)  → 
    ∀p : Profiles a b,∀(θ : α → RayQuotient.Characters rayM H)(w freq : α → ℝ)(t height : ℝ),
      (∀i,0≤w i)  → (∀i,w i≤Cycle61FirstActual.comparisonMesh Mmin Mmax (ε/2))  → 
      0≤height  → (∀i,|freq i|≤height)  → (∑i,w i)≤cap  → 
    ∀Y₁ Y₂ : ℝ,∀hY₁ : 0<Y₁,∀hY₂ : 0<Y₂, Y₁≤Z^along  → Y₂≤Z^short  → b^2*Y₁*Y₂≤Z^Bpair  → 
    ∀X₁ X₂ : ℝ,∀hX₁ : 0<X₁,∀hX₂ : 0<X₂,∀hprod : Y₁*Y₂=X₁*X₂,∀rows : Finset O,
    let s:=initialInput rayM H hH Wslot hWslot hsSlot Z (zero_lt_one.trans hZ1)
      (anchors j) η₀ R₀ θ w freq t p ha X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    markedFiniteEnergy s R₀ 1 b Y₁ Y₂ rows (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M)≤
      (C*diagonalControl Φ*(p.control S)^2*(1+|t|+|t|+height)^degree*Z^(M+ε)) := by
  obtain ⟨hm,d,S,href⟩:=actual_projected_short_reference (α:=α) rayM H hH κ Kcap
    hκlo hκhi hκbeta hKcap anchors Wslot hsSlot hWslot a b bΦ Mmin Mmax Bpair ε
    ha haUpper hb hbΦ hMmin hMM hε hBpair hbeta
  refine ⟨hm,d,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨C,hC,ht⟩:=href η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  refine ⟨C,hC,?_⟩
  filter_upwards [ht] with Z hz
  intro hZ1 j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p θ w freq t height
    hw hwmesh hheight hfreq hslots Y₁ Y₂ hY₁ hY₂ hY₁ref hY₂ref hcut X₁ X₂ hX₁ hX₂ hprod rows
  let s:=initialInput rayM H hH Wslot hWslot hsSlot Z (zero_lt_one.trans hZ1)
    (anchors j) η₀ R₀ θ w freq t p ha X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  let atoms:=Finset.univ.biUnion (fun i:α=>primePool rayM H 2 (Z^(w i)))
  have hatoms (i : α) : primePool rayM H 2 (Z^(w i))⊆atoms := by
    intro I hI
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hI⟩
  have hp (I : Ideal O) (hI : I∈atoms) : Prime I := by
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hI
    exact (Finset.mem_filter.mp hi).2.1
  have he:=hz.2 j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p θ w freq
    t height hw hwmesh hheight hfreq hslots Y₁ Y₂ hY₁ hY₂ hY₁ref hY₂ref hcut atoms hatoms rows
  exact markedFiniteEnergy_le_projected s R₀ 1 b Y₁ Y₂ hY₁ hY₂ rows
    (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M) hpΦ atoms hatoms hp _ he

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.actual_initialInput_short_reference
