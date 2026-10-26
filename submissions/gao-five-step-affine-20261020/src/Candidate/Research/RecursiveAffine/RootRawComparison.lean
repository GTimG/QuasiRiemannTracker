/- Exact native raw-height bridge at the recursive root ledger. Apache-2.0. -/
import Candidate.Cycle63.Physical.FirstBranches.RawComparison
import Candidate.Research.RecursiveAffine.RootFixedComparison

noncomputable local instance recursiveRootRawLedger : Cycle63.AffineLedger := Cycle153.Root.rootLedger
namespace OAI.SevenEighths.Cycle153RootSource
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 6000
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open Filter Cycle63Moment Cycle63FirstGeometry Cycle63FirstActual
open CenteredMomentPrimeSlot
open QuadraticInitialBound
open CenteredMomentEnergyReferenceState
open CenteredMomentEnergyState CenteredMomentEnergyReferenceChild
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentInductionEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalMaskedFloor
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance rawComparisonFinite : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Literal original comparison energy at the common raw plain height. -/
theorem actual_fixed_parent_raw_comparison_fixed_mesh
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0<a) (hlo : a≤1/4) (hhi : 1≤b)
    (hbΦ : 0<bΦ) (hMmin : 0<Mmin) (hMmax : Mmin≤Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    0<comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀j : Label, ∀M Lc n₁ n₂ : ℝ, Mmin≤M → M≤Mmax →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀t height : ℝ,
      (∀i,0≤w i) → (∀i,w i≤ comparisonMesh Mmin Mmax ε) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → (∑i∈F,w i)≤Cycle63.AffineLedger.slotTop*M →
      ComparisonFits M Lc n₁ n₂ (∑i∈F,w i) →
    ∀hZ : 1<Z, ∀hM : 0≤M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:F => primePool rayM H bslot (Z^(w i)))
      (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
      (fun i:F => Z^(w i)) (comparisonFirstAt Z Lc)
      (comparisonSecondAt Z Lc (Z^n₁) (Z^n₂)) s.radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨hmesh,degree,S,hbound⟩ := actual_fixed_parent_comparison_fixed_mesh rayM H hH anchors
    Fmax Wslot aslot bslot lo hi haslot hsSlot hWslot hbslot a b bΦ Mmin Mmax ε
    ha hlo hhi hbΦ hMmin hMmax hε hbeta hκbeta
  refine ⟨hmesh,degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,ht⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C*2^degree,by positivity,?_⟩
  filter_upwards [ht] with Z hz
  refine ⟨hz.1,?_⟩
  intro j M Lc n₁ n₂ hmin hmax Φ hsΦ hpΦ p F hF θ w σ freq
    t height hw hwmesh hσlo hσhi hheight hfreq hslots hfits hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  have hh := hz.2 j M Lc n₁ n₂ hmin hmax Φ hsΦ hpΦ p F hF θ
    w σ freq t t height hw hwmesh hσlo hσhi hheight hfreq hslots hfits hZ hM
  have hX₁ : 0<comparisonFirstAt Z Lc := by unfold comparisonFirstAt; positivity
  have hX₂ : 0<comparisonSecondAt Z Lc (Z^n₁) (Z^n₂) := by
    unfold comparisonSecondAt comparisonFirstAt
    positivity
  have heq := actual_raw_radial_energy s rfl ha p
    (fun i:F => primePool rayM H bslot (Z^(w i)))
    (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i:F => Z^(w i)) (by intro i; positivity) t
    (comparisonFirstAt Z Lc) (comparisonSecondAt Z Lc (Z^n₁) (Z^n₂)) hX₁ hX₂
  have hbridge : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:F => primePool rayM H bslot (Z^(w i)))
      (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
      (fun i:F => Z^(w i)) (comparisonFirstAt Z Lc)
      (comparisonSecondAt Z Lc (Z^n₁) (Z^n₂)) s.radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*
      (1+|t|+|t|+height)^degree*Z^(M+ε) := by
    apply heq.trans_le
    convert hh using 1
    congr 1
    funext z
    rw [Finset.prod_coe_sort F (fun i => naturalSlot (naturalCharacter s.character z)
      (primePool rayM H bslot (Z^(w i)))
      (heightCoefficient (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))]
    ring
  apply hbridge.trans
  have hp : (1+|t|+|t|+height)^degree≤(2*(1+|t|+height))^degree :=
    pow_le_pow_left₀ (by positivity) (by linarith) degree
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hdom := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (show 0≤C*diagonalControl Φ*(p.control S)^2 by positivity))
    (show 0≤Z^(M+ε) by positivity)
  apply hdom.trans_eq
  rw [mul_pow]
  ring

end
end OAI.SevenEighths.Cycle153RootSource
#print axioms OAI.SevenEighths.Cycle153RootSource.actual_fixed_parent_raw_comparison_fixed_mesh
