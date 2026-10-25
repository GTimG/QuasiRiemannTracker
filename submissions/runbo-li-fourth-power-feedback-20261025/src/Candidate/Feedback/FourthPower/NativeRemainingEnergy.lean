/- Copyright (c) 2026 Sil. Apache-2.0.
Literal identification of the live polynomial in the forward expansion
with the canonical injective family, including all frozen-prime holes.
-/
import Candidate.Feedback.FourthPower.NativeInjectiveEnergy
import Candidate.Feedback.FourthPower.RestorationFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.Feedback.FourthPower.NativeRemainingEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI.SevenEighths.Record12518109GainDeletion
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowPools
open ReferencePrimeEnclosure RestorationFamily NativeFiniteHoles NativeInjectiveEnergy
open Filter CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval
open ConcreteTraceCRT CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open HeckeDyadic
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem injective_reindex {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    (e : A≃B) (a : I→B→ℂ) :
    injectiveTuplePolynomial (fun i p=>a i (e p))=injectiveTuplePolynomial a := by
  unfold injectiveTuplePolynomial
  apply Finset.sum_bij (fun s _=>fun i=>e (s i))
  · intros; exact Finset.mem_univ _
  · intro s _ t _ h
    funext i
    exact e.injective (congrFun h i)
  · intro t _
    refine ⟨fun i=>e.symm (t i),Finset.mem_univ _,?_⟩
    funext i
    exact e.apply_symm_apply _
  · intro s _
    have hi : Function.Injective (fun i=>e (s i)) ↔ Function.Injective s :=
      ⟨fun h i j hij=>h (congrArg e hij),fun h=>e.injective.comp h⟩
    simp only [hi]

def enclosureEquiv (X : ℝ) : enclosure X≃ReferencePrimeEnclosure.primePool X :=
  Equiv.ofBijective (fun q=>⟨q.val.val,by
    rw [←enclosure_values]
    exact Finset.mem_image.mpr ⟨q.val,q.property,rfl⟩⟩) (by
      constructor
      · intro p q hpq
        have h : p.val.val=q.val.val :=
          congrArg (fun r : ReferencePrimeEnclosure.primePool X=>r.val) hpq
        exact Subtype.ext (Subtype.ext h)
      · intro p
        have hp : p.val∈primeValues (enclosure X) := by
          rw [enclosure_values]
          exact p.property
        obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hp
        exact ⟨⟨q,hq⟩,Subtype.ext hqp⟩)

theorem enclosureEquiv_val (X : ℝ) (q : enclosure X) :
    (enclosureEquiv X q).val=q.val.val := rfl

variable {α : Type*} [Fintype α]

theorem enclosure_injective (X : ℝ) (χ : Character)
    (pool : α→Finset Id) (β : α→Id→ℂ) (P : α→ℝ) :
    injectiveTuplePolynomial (naturalCoefficients χ (enclosure X) pool β P)=
      injectiveTuplePolynomial (fun i=>fun p : ReferencePrimeEnclosure.primePool X=>
        slotTerm χ (pool i) (β i) (P i) p.val) := by
  have he := injective_reindex (enclosureEquiv X)
    (fun i=>fun p : ReferencePrimeEnclosure.primePool X=>
      slotTerm χ (pool i) (β i) (P i) p.val)
  apply Eq.trans ?_ he
  congr 1

def frozenHoles (T : Finset α) (S : Finset PrimeIdeal) (t : T→S) : Finset Id :=
  Finset.univ.image (fun i=>(t i).val.val)

theorem frozenHoles_card (T : Finset α) (S : Finset PrimeIdeal) (t : T→S) :
    (frozenHoles T S t).card≤T.card := by
  simpa only [frozenHoles,Finset.card_univ,Fintype.card_coe] using
    (Finset.card_image_le (s:=Finset.univ) (f:=fun i=>(t i).val.val))

theorem crossBeta_holes (T : Finset α) (S : Finset PrimeIdeal) (t : T→S)
    (β : α→Id→ℂ) :
    crossBeta T S t β=holeCoefficient (fun i : {i // i∉T}=>β i.val)
      (fun _=>frozenHoles T S t) := by
  funext i I
  have hh : I∈frozenHoles T S t ↔ ¬∀j : T,(t j).val.val≠I := by
    simp [frozenHoles]
  dsimp only [crossBeta,maskedBeta,holeCoefficient]
  simp only [hh]
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem remaining_as_injective (T : Finset α) (X : ℝ) (t : T→enclosure X)
    (χ : Character) (pool : α→Finset Id) (β : α→Id→ℂ) (P : α→ℝ) :
    remainingSum T (naturalCoefficients χ (enclosure X) pool β P) t (fun _=>1)=
      injectiveTuplePolynomial (fun i : {i // i∉T}=>fun p : ReferencePrimeEnclosure.primePool X=>
        slotTerm χ (pool i.val)
          (holeCoefficient (fun j : {j // j∉T}=>β j.val)
            (fun _=>frozenHoles T (enclosure X) t) i) (P i.val) p.val) := by
  rw [remaining_mask]
  change weightedSum (naturalCoefficients χ (enclosure X) (fun i : {i // i∉T}=>pool i.val)
    (crossBeta T (enclosure X) t β) (fun i=>P i.val)) (fun _=>1)=_
  have he (a : {i // i∉T}→enclosure X→ℂ) : weightedSum a (fun _=>1)=injectiveTuplePolynomial a := by
    unfold weightedSum injectiveTuplePolynomial
    apply Finset.sum_congr (by ext; simp)
    intro s hs
    by_cases h : Function.Injective s <;> simp only [h,ite_true,ite_false,one_mul]
  rw [he,enclosure_injective,crossBeta_holes]

theorem combined_height_holes (T : Finset α) (S : Finset PrimeIdeal) (t : T→S)
    (β : α→Id→ℂ) (R : α→Finset Id) (height : ℝ) (i : {i // i∉T}) :
    holeCoefficient (fun j : {j // j∉T}=>
      CenteredMomentCommonMaskEnergy.heightCoefficient (holeCoefficient β R j.val) height)
      (fun _=>frozenHoles T S t) i =
    CenteredMomentCommonMaskEnergy.heightCoefficient
      (holeCoefficient (fun j : {j // j∉T}=>β j.val)
        (fun j=>R j.val∪frozenHoles T S t) i) height := by
  funext I
  by_cases hi : I∈R i.val <;> by_cases hj : I∈frozenHoles T S t <;>
    simp [holeCoefficient,CenteredMomentCommonMaskEnergy.heightCoefficient,hi,hj]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The literal live sum in a fixed frozen-label term is bounded using the
canonical analytic source. Frozen primes create only marked holes; the
ordinary polynomials retain their original character and shortened lengths. -/
theorem canonical_remaining_children
    (T : Finset α) (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bmask : ℝ,∀s : NaturalState Z Bmask radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
    ∀frozen : T→enclosure (Cap*Z^Lcap),
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
        polynomial (naturalCharacter s.character z) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
        remainingSum T (naturalCoefficients (naturalCharacter s.character z)
          (enclosure (Cap*Z^Lcap)) (fun i=>supportedPool (primePool M H 2 (Z^(w i))))
          (fun i=>heightCoefficient (holeCoefficient (fun i I=>
            idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t)
          (fun i=>Z^(w i))) frozen (fun _=>1))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  classical
  obtain ⟨degree,S,hchildren⟩ := canonical_closed_children (α:={i // i∉T}) M H hH
    (Holes+T.card) W a b radial Mcap L Lslot Lcap Cap ε lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hε hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hchildren⟩ := hchildren η₀ hQη
  refine ⟨C,hC,hchildren.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bmask s hQ hwidth
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂ frozen
  have hbudget (i : {i // i∉T}) :
      (R₀ i.val∪frozenHoles T (enclosure (Cap*Z^Lcap)) frozen).card≤Holes+T.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (hR₀ i.val) (frozenHoles_card _ _ _))
  have he := hZ.2 (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
    t V (fun i=>R₀ i.val∪frozenHoles T (enclosure (Cap*Z^Lcap)) frozen)
    (fun i=>hw i.val) (fun i=>hwL i.val) (fun i=>hσ i.val) (fun i=>hσhi i.val)
    hV (fun i=>hfreq i.val) hbudget Bmask s hQ hwidth W₁ W₂ hs₁ hs₂
    t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂
  simp_rw [remaining_as_injective,combined_height_holes]
  apply he.trans
  have hκ0 : 0≤κ := by linarith
  have hsum : (∑i : {i // i∉T},w i.val)≤∑i,w i := by
    calc
      _ = ∑i∈(Finset.univ : Finset {i // i∉T}).image Subtype.val,w i := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ h=>Subtype.val_injective h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _=>hw i)
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.1.le
    (show s.width+κ*(∑i : {i // i∉T},w i.val)+ε≤s.width+κ*(∑i,w i)+ε by
      nlinarith [mul_le_mul_of_nonneg_left hsum hκ0])
  exact mul_le_mul_of_nonneg_left hpow (by
    have := diagonalControl_nonneg s.radial.profile
    positivity)

/-- One threshold, one seminorm control and one height degree work for all
frozen-label subsets. The constants are chosen before the scale and masks. -/
theorem canonical_uniform_remaining_children
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bmask : ℝ,∀s : NaturalState Z Bmask radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
    ∀T : Finset α,∀frozen : T→enclosure (Cap*Z^Lcap),
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
        polynomial (naturalCharacter s.character z) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
        remainingSum T (naturalCoefficients (naturalCharacter s.character z)
          (enclosure (Cap*Z^Lcap)) (fun i=>supportedPool (primePool M H 2 (Z^(w i))))
          (fun i=>heightCoefficient (holeCoefficient (fun i I=>
            idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t)
          (fun i=>Z^(w i))) frozen (fun _=>1))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  classical
  choose degreeT controlT hchildren using fun T : Finset α=>
    canonical_remaining_children M H hH T Holes W a b radial Mcap L Lslot Lcap Cap ε lo hi κ
      hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hε hβ hκ Q hQt hQ72 hQM
  let degree := ∑T : Finset α,degreeT T
  let S := (Finset.univ : Finset (Finset α)).biUnion controlT
  have hn (T : Finset α) : degreeT T≤degree :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hS (T : Finset α) : controlT T⊆S :=
    Finset.subset_biUnion_of_mem controlT (Finset.mem_univ T)
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  choose CT hCT hchildren using fun T=>hchildren T η₀ hQη
  let C := 1+∑T : Finset α,CT T
  have hC : 0<C := by
    have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset α)))=>(hCT T).le)
    dsimp [C]
    linarith
  have hCTC (T : Finset α) : CT T≤C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CT)
      (fun T _=>(hCT T).le) (Finset.mem_univ T)
    dsimp [C]
    linarith
  refine ⟨C,hC,(Filter.eventually_all.mpr hchildren).mono ?_⟩
  intro Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bmask s hQ hwidth
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂ T frozen
  have he := (hZ T).2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bmask s hQ hwidth
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂ frozen
  let p := independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂
  have hp : p.control (controlT T)≤p.control S := by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono (hS T)) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono (hS T)) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hh : (1+|t|+V)^(degreeT T)≤(1+|t|+V)^degree :=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) (hn T)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hbase : 0≤1+|t|+V := by positivity
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_right (hCTC T) hdiag)
    (pow_le_pow_left₀ (p.control_nonneg (controlT T)) hp 2)
    (sq_nonneg _) (mul_nonneg hC.le hdiag)
  have htotal := mul_le_mul hm hh (pow_nonneg hbase _)
    (mul_nonneg (mul_nonneg hC.le hdiag) (sq_nonneg _))
  exact he.trans (mul_le_mul_of_nonneg_right htotal
    (Real.rpow_nonneg (zero_lt_one.trans (hZ T).1).le _))

end
end Candidate.Feedback.FourthPower.NativeRemainingEnergy
