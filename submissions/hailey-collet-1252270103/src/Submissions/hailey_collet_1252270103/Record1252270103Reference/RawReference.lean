/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual LOW short-reference estimate is applied after finite whole-column
puncture deletion. All shorter positive factors and surviving slots are retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Reference.MaskTransfer
import Submissions.hailey_collet_1252270103.Record1252270103Reference.SlotBounds
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.ReferenceEnergy
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
open CenteredMomentSecondHeightFamily CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
local notation "O"=>HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

theorem actual_masked_short_reference_energy
    (κ Kcap : ℝ) (hκlo : 7/10≤κ) (hκhi : κ≤3/4)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κ) (hKcap : 6*κ≤Kcap)
    {Label : Type*} [Fintype Label] (anchors : Label→Character)
    (Fmax : Finset α) (Wslot : ℝ→ℂ)
    (hsSlot : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hWslot : ContDiff ℝ ∞ Wslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hbΦ : 0<bΦ) (hMmin : 0<Mmin) (hMM : Mmin≤Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    0<Cycle61FirstActual.comparisonMesh Mmin Mmax ε ∧
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∀η₀ : Character,∀Q : Ideal O,
      Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤Ideal.span {(72:O)} →
    ∀R₀ : Ideal O,R₀≠0 → ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀j : Label,∀M along short r cap : ℝ,Mmin≤M → M≤Mmax →
      0≤r → 0≤cap → short≤r → r+Kcap*cap≤49*M/100 →
    ∀Φ : 𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀p : Profiles a b,∀F : Finset α,F⊆Fmax →
    ∀(θ : α→RayQuotient.Characters rayM H)(w freq : α→ℝ)(u t height : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Cycle61FirstActual.comparisonMesh Mmin Mmax ε) →
      0≤height → (∀i,|freq i|≤height) → (∑i∈F,w i)≤cap →
    ∀Y₁ Y₂ : ℝ,0<Y₁ → 0<Y₂ → Y₁≤Z^along → Y₂≤Z^short →
      energy (anchors j) (fixedBadMask*idealGenerator R₀) 1 0
        ((independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t).profile 0)
        ((independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t).profile 1)
        (fun i:F=>primePool rayM H 2 (Z^(w i)))
        (fun (i:F) I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (33/50) (t+freq i) I)
        (fun i:F=>Z^(w i)) Y₁ Y₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨hmesh,degree,S,href⟩ := Record1252270103Low.actual_fixed_parent_short_reference_energy
    rayM H hH κ Kcap hκlo hκhi hκbeta hKcap anchors Fmax Wslot 1 2 (33/50) (33/50)
    (by norm_num) hsSlot hWslot (by norm_num) a b bΦ Mmin Mmax ε ha haUpper hb hbΦ
    hMmin hMM hε hbeta
  obtain ⟨D,hD,hDcoeff⟩ := actual_marked_coefficient_bound Wslot hsSlot hWslot
  choose Cmask hCmask hm using fun F : Finset α=>fixed_mask_energy_transfer
    F (fun _=>2) (fun _=>D) (fun _ _=>hD) 1 (by norm_num)
  let CmaskAll : ℝ := 1+∑F : Finset α,Cmask F
  have hCmaskAll : 0<CmaskAll := by
    have hh : 0≤∑F : Finset α,Cmask F := Finset.sum_nonneg (fun F _=>(hCmask F).le)
    dsimp [CmaskAll]
    linarith
  have hCmaskLe (F : Finset α) : Cmask F≤CmaskAll := by
    have hh := Finset.single_le_sum (fun G _=>(hCmask G).le) (Finset.mem_univ F)
    dsimp [CmaskAll]
    linarith
  refine ⟨hmesh,degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨Cref,hCref,ht⟩ := href η₀ Q hQM hQ0 hQt hQ72
  let C : ℝ := CmaskAll*((R₀.radical.absNorm:ℝ)+1)*Cref
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [ht] with Z hz
  refine ⟨hz.1,?_⟩
  intro j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p F hF
    θ w freq u t height hw hwmesh hheight hfreq hslots Y₁ Y₂ hY₁ hY₂ hY₁ref hY₂ref
  have hZ : 0<Z := zero_lt_one.trans hz.1
  have hM : 0≤M := hMmin.le.trans hmin
  let p' := independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t
  let pool := fun i=>primePool rayM H 2 (Z^(w i))
  let β := fun i I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (33/50) (t+freq i) I
  let P := fun i=>Z^(w i)
  let E : ℝ := Cref*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree*Z^(M+ε)
  have hdiag := diagonalControl_nonneg Φ
  have hE : 0≤E := by dsimp [E];positivity
  have hraw (G : Finset α) (hGF : G⊆F) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
      (hX₁Y : X₁≤Y₁) (hX₂Y : X₂≤Y₂) :
      energy (anchors j) (fixedBadMask*idealGenerator 1) 1 0 (p'.profile 0) (p'.profile 1)
        (fun i:G=>pool i) (fun (i:G) I=>β i I) (fun i:G=>P i) X₁ X₂
        (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M)≤E := by
    have hlog₂ : Real.logb Z X₂≤r := by
      apply (Real.logb_le_iff_le_rpow hz.1 hX₂).mpr
      exact (hX₂Y.trans hY₂ref).trans (Real.rpow_le_rpow_of_exponent_le hz.1.le hshort)
    have hslotG : (∑i∈G,w i)≤cap :=
      (Finset.sum_le_sum_of_subset_of_nonneg hGF (fun i _ _=>hw i)).trans hslots
    have he := hz.2 j M (Real.logb Z X₁) (Real.logb Z X₂) r cap hmin hmax hr hcap hlog₂
      hbudget Φ hsΦ hpΦ p G (hGF.trans hF) θ w (fun _=>33/50) freq u t height hw hwmesh
      (fun _=>le_rfl) (fun _=>le_rfl) hheight hfreq hslotG hz.1 hM
    dsimp only at he
    rw [Real.rpow_logb hZ hz.1.ne' hX₁,Real.rpow_logb hZ hz.1.ne' hX₂] at he
    exact he
  have he := hm F (anchors j) R₀ hR₀ (p'.profile 0) (p'.profile 1) a b ha (zero_le_one.trans hb)
    (p'.support 0) (p'.support 1) pool β P
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=>Real.rpow_pos_of_pos hZ _)
    (fun i _ I hI=>hDcoeff _ _ _ (Real.rpow_pos_of_pos hZ _) I (Finset.mem_filter.mp hI).2.1)
    (fun i _ I _ hn=>actual_marked_support Wslot hsSlot _ _ _ (Real.rpow_pos_of_pos hZ _) I hn)
    Y₁ Y₂ hY₁ hY₂ (initialKeep (anchors j) (internalQ Q η₀)) (fun _ hh=>hh.1)
    Φ (Z^M) E (Real.rpow_pos_of_pos hZ _) hpΦ hE hraw
  rw [Real.rpow_one] at he
  have hc : Cmask F*(R₀.radical.absNorm:ℝ)≤CmaskAll*((R₀.radical.absNorm:ℝ)+1) :=
    mul_le_mul (hCmaskLe F) (by linarith) (Nat.cast_nonneg _) hCmaskAll.le
  exact he.trans ((mul_le_mul_of_nonneg_right hc hE).trans_eq (by dsimp [E,C];ring))

end
end QRH.Record1252270103Reference
#print axioms QRH.Record1252270103Reference.actual_masked_short_reference_energy
