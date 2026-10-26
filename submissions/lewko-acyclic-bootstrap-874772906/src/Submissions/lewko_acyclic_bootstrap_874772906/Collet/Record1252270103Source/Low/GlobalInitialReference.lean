/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual LOW short-reference estimate is applied after finite whole-column
puncture deletion. All shorter positive factors and surviving slots are retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Reference.SquarefreeReference
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialHeightEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthOriginal
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open QRH.Record1252270103Reference CenteredMomentEnergyZeroGrowthOriginal
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState ConcretePrimeRowBridge CenteredMomentPrimeSlot
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound Cycle61Moment
open QRH.Record1252270103Restoration Record1252270103KernelMass
open CenteredMomentSecondHeightFamily CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
local notation "O"=>HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

theorem actual_squarefree_short_reference_outer_height
    (κ Kcap : ℝ) (hκlo : 7/10≤κ) (hκhi : κ≤3/4)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κ) (hKcap : 6*κ≤Kcap)
    {Label : Type*} [Fintype Label] (anchors : Label→Character)
    (Fmax : Finset α) (Wslot : ℝ→ℂ)
    (hsSlot : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hWslot : ContDiff ℝ ∞ Wslot)
    (a b bΦ Mmin Mmax Bpair ε : ℝ) (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hbΦ : 0<bΦ) (hMmin : 0<Mmin) (hMM : Mmin≤Mmax) (hε : 0<ε) (hBpair : 0≤Bpair)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    0<Cycle61FirstActual.comparisonMesh Mmin Mmax (ε/2) ∧
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∀η₀ : Character,∀Q : Ideal O,
      Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤Ideal.span {(72:O)} →
    ∀R₀ : Ideal O,R₀≠0 → ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀j : Label,∀M along short r cap : ℝ,Mmin≤M → M≤Mmax →
      0≤r → 0≤cap → short≤r → r+Kcap*cap≤49*M/100 →
    ∀Φ : 𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀p : Profiles a b,∀F : Finset α,F⊆Fmax →
    ∀(θ : α→RayQuotient.Characters rayM H)(w freq : α→ℝ)(t height : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Cycle61FirstActual.comparisonMesh Mmin Mmax (ε/2)) →
      0≤height → (∀i,|freq i|≤height) → (∑i∈F,w i)≤cap →
    ∀Y₁ Y₂ : ℝ,0<Y₁ → 0<Y₂ → Y₁≤Z^along → Y₂≤Z^short →
      b^2*Y₁*Y₂≤Z^Bpair →
      QRH.Record1252270103Restoration.squarefreeEnergy (anchors j) (fixedBadMask*idealGenerator R₀) 1 t (p.profile 0) (p.profile 1) b
        (fun i:F=>primePool rayM H 2 (Z^(w i)))
        (fun (i:F) I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (33/50) (freq i) I)
        (fun i:F=>Z^(w i)) Y₁ Y₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨hm,d,S,h⟩ := actual_squarefree_short_reference_energy rayM H hH κ Kcap
    hκlo hκhi hκbeta hKcap anchors Fmax Wslot hsSlot hWslot a b bΦ Mmin Mmax Bpair ε
    ha haUpper hb hbΦ hMmin hMM hε hBpair hbeta
  refine ⟨hm,d,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨C,hC,ht⟩ := h η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  refine ⟨C,hC,?_⟩
  filter_upwards [ht] with Z hz
  refine ⟨hz.1,?_⟩
  intro j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p F hF
    θ w freq t height hw hwmesh hheight hfreq hslots Y₁ Y₂ hY₁ hY₂ hY₁ref hY₂ref hcut
  have he := squarefreeEnergy_height (anchors j) (fixedBadMask*idealGenerator R₀) 1 t
    (p.profile 0) (p.profile 1) a b ha (p.support 0) (p.support 1)
    ((p.profile 0).smooth ⊤) ((p.profile 1).smooth ⊤)
    (fun i:F=>primePool rayM H 2 (Z^(w i)))
    (fun (i:F) I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I)
    (fun _ : F=>Wslot) (fun i:F=>Z^(w i)) (fun _ : F=>(33/50:ℝ)) (fun i:F=>freq i)
    (fun i=>Real.rpow_pos_of_pos (zero_lt_one.trans hz.1) _)
    (fun i I hI=>(Finset.mem_filter.mp hI).2.1.ne_zero)
    Y₁ Y₂ hY₁ hY₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M)
  rw [he]
  have hh := hz.2 j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ
    (swapProfiles p) F hF θ w freq t t height hw hwmesh hheight hfreq hslots
    Y₁ Y₂ hY₁ hY₂ hY₁ref hY₂ref hcut
  rw [swapProfiles_control] at hh
  simpa only [independentProfiles,swapProfiles,Matrix.cons_val_zero,
    Matrix.cons_val_one,Fin.isValue,ite_true,ite_false,(by decide : (1:Fin 2)≠0)] using hh

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.actual_squarefree_short_reference_outer_height
