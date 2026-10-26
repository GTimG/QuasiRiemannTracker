/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual LOW short-reference estimate is applied after finite whole-column
puncture deletion. All shorter positive factors and surviving slots are retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Reference.MaskTransfer
import Submissions.hailey_collet_1252270103.Record1252270103Reference.SlotBounds
import Submissions.hailey_collet_1252270103.Record1252270103Reference.RawReference
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.ForwardFull
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Reference
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
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

theorem actual_squarefree_short_reference_energy
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
    ∀(θ : α→RayQuotient.Characters rayM H)(w freq : α→ℝ)(u t height : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Cycle61FirstActual.comparisonMesh Mmin Mmax (ε/2)) →
      0≤height → (∀i,|freq i|≤height) → (∑i∈F,w i)≤cap →
    ∀Y₁ Y₂ : ℝ,0<Y₁ → 0<Y₂ → Y₁≤Z^along → Y₂≤Z^short →
      b^2*Y₁*Y₂≤Z^Bpair →
      QRH.Record1252270103Restoration.squarefreeEnergy (anchors j) (fixedBadMask*idealGenerator R₀) 1 0
        ((independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t).profile 0)
        ((independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t).profile 1) b
        (fun i:F=>primePool rayM H 2 (Z^(w i)))
        (fun (i:F) I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (33/50) (t+freq i) I)
        (fun i:F=>Z^(w i)) Y₁ Y₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨hmesh,degree,S,href⟩ := actual_masked_short_reference_energy rayM H hH κ Kcap
    hκlo hκhi hκbeta hKcap anchors Fmax Wslot hsSlot hWslot a b bΦ Mmin Mmax (ε/2)
    ha haUpper hb hbΦ hMmin hMM (by linarith) hbeta
  refine ⟨hmesh,degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨Craw,hCraw,ht⟩ := href η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  let A : ℝ := holeDeletionMass*(eulerBound 5 (1/2+(ε/4)/(Bpair+1))+
    eulerBound 432 (1/2+(ε/4)/(Bpair+1)))
  let C : ℝ := (A^2+1)*Craw
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [ht] with Z hz
  refine ⟨hz.1,?_⟩
  intro j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p F hF
    θ w freq u t height hw hwmesh hheight hfreq hslots Y₁ Y₂ hY₁ hY₂ hY₁ref hY₂ref hcut
  have hZ : 0<Z := zero_lt_one.trans hz.1
  let p' := independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t
  let pool := fun i:F=>primePool rayM H 2 (Z^(w i))
  let β := fun (i:F) I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (33/50) (t+freq i) I
  let P := fun i:F=>Z^(w i)
  let E : ℝ := Craw*diagonalControl Φ*(p.control S)^2*
    (1+|u|+|t|+height)^degree*Z^(M+ε/2)
  have hdiag := diagonalControl_nonneg Φ
  have hE : 0≤E := by dsimp [E];positivity
  have hraw (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
      (hX₁Y : X₁≤Y₁) (hX₂Y : X₂≤Y₂) :
      energy (anchors j) (fixedBadMask*idealGenerator R₀) 1 0 (p'.profile 0) (p'.profile 1)
        pool β P X₁ X₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M)≤E :=
    hz.2 j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p F hF θ w freq
      u t height hw hwmesh hheight hfreq hslots X₁ X₂ hX₁ hX₂
      (hX₁Y.trans hY₁ref) (hX₂Y.trans hY₂ref)
  have he := forward_energy_transfer (anchors j) (fixedBadMask*idealGenerator R₀) 1
    (p'.profile 0) (p'.profile 1) b (fun x hx=>(p'.support 0 hx).2)
    (fun x hx=>(p'.support 1 hx).2) pool β P (fun i=>Real.rpow_pos_of_pos hZ _)
    0 Y₁ Y₂ hY₁ hY₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M)
    (Real.rpow_pos_of_pos hZ _) hpΦ E hE (ε/4) Bpair Z (by linarith) hBpair hz.1.le hcut hraw
  have he0 : squarefreeEnergy (anchors j) (fixedBadMask*idealGenerator R₀) 1 0
    (p'.profile 0) (p'.profile 1) b pool β P Y₁ Y₂
    (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M)≤(A*Z^(ε/4))^2*E := by
    simpa only [A,mul_assoc] using he
  have hpow : (Z^(ε/4))^2*Z^(M+ε/2)=Z^(M+ε) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
    congr 1
    ring
  have halg : (A*Z^(ε/4))^2*E =
      A^2*Craw*diagonalControl Φ*(p.control S)^2*
        (1+|u|+|t|+height)^degree*Z^(M+ε) := by
    dsimp only [E]
    calc
      _ = A^2*(Craw*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree)*
          ((Z^(ε/4))^2*Z^(M+ε/2)) := by ring
      _ = _ := by rw [hpow];ring
  rw [halg] at he0
  apply he0.trans
  dsimp only [C]
  gcongr
  nlinarith [sq_nonneg A]

end
end QRH.Record1252270103Reference
#print axioms QRH.Record1252270103Reference.actual_squarefree_short_reference_energy
