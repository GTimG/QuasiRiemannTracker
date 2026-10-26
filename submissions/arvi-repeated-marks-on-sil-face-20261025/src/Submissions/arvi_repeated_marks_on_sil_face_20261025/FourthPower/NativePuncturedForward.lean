/- Copyright (c) 2026 Sil. Apache-2.0.
Literal remaining and forward energies with both common punctures and
marked-only holes. The original conductor and uniform thresholds are retained.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.NativePuncturedInjective
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.NativeForwardEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.FourthPower.NativePuncturedForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowPools KernelRowProfiles
open ReferencePrimeEnclosure RestorationFamily NativeFiniteHoles NativeInjectiveEnergy
open NativeRemainingEnergy NativeForwardEnergy NativePuncturedInjective
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem canonical_punctured_remaining
    (T : Finset α) (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R : Finset Id,∀hR : ∀I∈R,Prime I,(Ideal.absNorm (∏I∈R,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
    ∀frozen : T→enclosure (Cap*Z^Lcap),
      radialEnergy (fun z=>polynomial ((naturalCharacter s.character z).excludePrimes R hR) false W₁
          (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
        polynomial ((naturalCharacter s.character z).excludePrimes R hR) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
        remainingSum T (naturalCoefficients ((naturalCharacter s.character z).excludePrimes R hR)
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
  obtain ⟨degree,S,hchildren⟩ := canonical_punctured_injective (α:={i // i∉T}) M H hH
    (Holes+T.card) W a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hε hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hchildren⟩ := hchildren η₀ hQη
  refine ⟨C,hC,hchildren.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R hR hRcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂ frozen
  have hbudget (i : {i // i∉T}) :
      (R₀ i.val∪frozenHoles T (enclosure (Cap*Z^Lcap)) frozen).card≤Holes+T.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (hR₀ i.val) (frozenHoles_card _ _ _))
  have he := hZ.2 (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
    t V (fun i=>R₀ i.val∪frozenHoles T (enclosure (Cap*Z^Lcap)) frozen)
    (fun i=>hw i.val) (fun i=>hwL i.val) (fun i=>hσ i.val) (fun i=>hσhi i.val)
    hV (fun i=>hfreq i.val) hbudget Bstate s hQ hwidth R hR hRcap W₁ W₂ hs₁ hs₂
    t₁ t₂ (X₁/(D₁.absNorm:ℝ)) (X₂/(D₂.absNorm:ℝ))
    (shortened_positive_le hX₁ hD₁).1 (shortened_positive_le hX₂ hD₂).1
    ((shortened_positive_le hX₁ hD₁).2.trans hc₁)
    ((shortened_positive_le hX₂ hD₂).2.trans hc₂)
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

theorem canonical_uniform_punctured_remaining
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R : Finset Id,∀hR : ∀I∈R,Prime I,(Ideal.absNorm (∏I∈R,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
    ∀T : Finset α,∀frozen : T→enclosure (Cap*Z^Lcap),
      radialEnergy (fun z=>polynomial ((naturalCharacter s.character z).excludePrimes R hR) false W₁
          (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
        polynomial ((naturalCharacter s.character z).excludePrimes R hR) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
        remainingSum T (naturalCoefficients ((naturalCharacter s.character z).excludePrimes R hR)
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
    canonical_punctured_remaining M H hH T Holes W a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ
      hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hε hβ hκ Q hQt hQ72 hQM
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
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R hR hRcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂ T frozen
  have he := (hZ T).2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R hR hRcap
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

theorem canonical_punctured_forward
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R : Finset Id,∀hR : ∀I∈R,Prime I,(Ideal.absNorm (∏I∈R,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
      radialEnergy (fun z=>row false (enclosure (Cap*Z^Lcap))
        ((naturalCharacter s.character z).excludePrimes R hR)
        (fun i=>supportedPool (primePool M H 2 (Z^(w i))))
        (fun i=>heightCoefficient (holeCoefficient (fun i I=>
          idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t)
        (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  have hLcap0 := hLslot.trans hLcap
  have hCap0 : 0<Cap := by linarith
  let δ := ε/(2*(Lcap+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨B₀,hB₀,hcoeff⟩ := slot_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW.continuous
  let B := max 1 B₀
  have hB : 1≤B := le_max_left _ _
  obtain ⟨Cf,hCf,hforward⟩ := radial_forward_energy (α:=α) B δ (zero_le_one.trans hB) hδ
  obtain ⟨degree,S,hchildren⟩ := canonical_uniform_punctured_remaining (α:=α) M H hH Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask (ε/2) lo hi κ hWs hW ha haUpper hb hrad hM
    hLslot hLcap hCap hBmask (half_pos hε) hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨Cc,hCc,hchildren⟩ := hchildren η₀ hQη
  refine ⟨Cf*Cap^δ*Cc,by positivity,hchildren.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R hR hRcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  let X := Cap*Z^Lcap
  let primes := enclosure X
  let P := fun i=>Z^(w i)
  let pool := fun i=>supportedPool (primePool M H 2 (P i))
  let β₀ := fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight W (P i) (σ i) (freq i) I
  let βc := fun i=>heightCoefficient (holeCoefficient β₀ R₀ i) t
  let E := Cc*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε/2)
  have hX : 1≤X := one_le_mul_of_one_le_of_one_le (by linarith)
    (Real.one_le_rpow hZ.1.le hLcap0)
  have hP (i : α) : 0<P i := Real.rpow_pos_of_pos hZ0 _
  have hp (i : α) (I : Id) (hI : I∈pool i) : Supported I ∧ (I.absNorm:ℝ)≤2*P i := by
    refine ⟨(Finset.mem_filter.mp hI).2,?_⟩
    exact canonical_pool_norm_le M H _ (hP i) I (Finset.mem_filter.mp hI).1
  have hβc (i : α) (I : Id) (hI : I∈pool i) : ‖βc i I‖≤B := by
    have he := ((hcoeff (relativeCharacter M H hH η₀ (θ i)) (P i) (σ i) (freq i) t
      (hP i) (hσ i) (hσhi i) I (hp i I hI).1.1).1).trans (le_max_right 1 B₀)
    by_cases hi : I∈R₀ i
    · simpa [βc,holeCoefficient,heightCoefficient,hi] using (zero_le_one.trans hB)
    · simpa only [βc,heightCoefficient,holeCoefficient,ite_eq_right hi,β₀,B] using he
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have henclose (I : Id) (hI : Supported I)
      (hlen : (I.absNorm:ℝ)≤b*X₁ ∨ (I.absNorm:ℝ)≤b*X₂) :
      primeSupport I⊆primeValues primes := by
    apply support_enclosed X I hI
    have hc (Y : ℝ) (hY : 0<Y) (hYc : Y≤Z^L) : b*Y≤X :=
      mul_le_mul hCapb (hYc.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hLordinary))
        hY.le hCap0.le
    exact hlen.elim (fun h=>h.trans (hc X₁ hX₁ hc₁)) (fun h=>h.trans (hc X₂ hX₂ hc₂))
  have he := hforward X hX primes (enclosure_bound X) (fun z=>(naturalCharacter s.character z).excludePrimes R hR)
    pool βc P hP hp hβc W₁ W₂ b X₁ X₂ t₁ t₂ E (zero_le_one.trans hb) hX₁ hX₂ hE
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2)
    (effectiveState s).radial.keep s.radial.profile s.radial.scale radial s.radial.scale_pos
    s.radial_support s.radial.nonneg
    (fun z hz=>deleted_off_supported _
      (natural_character_off_supported s.character z (s.row_ne_zero z hz.1)) R hR)
    henclose (by
      intro T frozen _ d hd
      have hn := divisor_supported hd
      exact hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R hR hRcap
        W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂) X₁ X₂ hX₁ hX₂ hc₁ hc₂
        d.1 d.2 hn.1 hn.2.1 T frozen)
  have hcost := mul_le_mul_of_nonneg_left
    (cutoff_loss Z Lcap Cap ε (s.width+κ*(∑i,w i)) hZ.1.le hLcap0 hCap0.le hε)
    (show 0≤Cf*Cc*diagonalControl s.radial.profile*
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
      (1+|t|+V)^degree by positivity)
  apply he.trans
  convert hcost using 1 <;> dsimp only [δ,X,E] <;> ring

end
end Candidate.FourthPower.NativePuncturedForward
