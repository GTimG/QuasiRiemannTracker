/- Copyright (c) 2026 Sil. Apache-2.0.
Injective canonical children after a common prime puncture. All analytic
inputs are supplied by original full subset products with bounded marked
holes; the common puncture has a separate polynomial norm budget.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.NativePuncturedChildren

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.FourthPower.NativePuncturedInjective
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT CanonicalQuadraticSieve
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor QuadraticInitialBound HeckeDyadic
open NativeFiniteHoles NativeInjectiveEnergy NativePuncturedChildren KernelNaturalSlots
open OAI.SevenEighths.Record12518109GainDeletion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

theorem deleted_off_supported (χ : Character)
    (hχ : ∀I,¬Supported I → idealCoeff χ I=0)
    (R : Finset Id) (hR : ∀I∈R,Prime I) :
    ∀I,¬Supported I → idealCoeff (χ.excludePrimes R hR) I=0 := by
  intro I hI
  by_cases hz : I=0
  · subst I
    exact map_zero _
  · have he := CenteredMomentReflectionDeletion.deleted_coefficient χ R hR ⟨I,hz⟩
    simpa only [hχ I hI,ite_self] using he

theorem punctured_supported_slots (η : Character) (R : Finset Id) (hR : ∀I∈R,Prime I)
    (D : O→ℂ) (T : Finset α) (pool : α→Finset Id) (β : α→Id→ℂ) (P : α→ℝ)
    (keep : O→Prop) (hkeep : ∀z,keep z → z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (fun z=>D z*∏i∈T,naturalSlot ((naturalCharacter η z).excludePrimes R hR)
      (supportedPool (pool i)) (β i) (P i)) keep Φ K =
    radialEnergy (fun z=>D z*∏i∈T,naturalSlot ((naturalCharacter η z).excludePrimes R hR)
      (pool i) (β i) (P i)) keep Φ K := by
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : keep z
  · simp only [ite_eq_left hk]
    have hχ := deleted_off_supported _ (natural_character_off_supported η z (hkeep z hk)) R hR
    simp_rw [supported_naturalSlot _ hχ]
  · simp only [ite_eq_right hk]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem canonical_punctured_injective (Holes : ℕ) (W : ℝ→ℂ)
    (a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ : ℝ)
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
      radialEnergy (fun z=>polynomial ((naturalCharacter s.character z).excludePrimes R hR)
          false W₁ X₁ 0 t₁ *
        polynomial ((naturalCharacter s.character z).excludePrimes R hR) false W₂ X₂ 0 t₂ *
        injectiveTuplePolynomial (fun i=>fun p : ReferencePrimeEnclosure.primePool (Cap*Z^Lcap)=>
          slotTerm ((naturalCharacter s.character z).excludePrimes R hR)
            (supportedPool (primePool M H 2 (Z^(w i))))
            (heightCoefficient (holeCoefficient (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t)
            (Z^(w i)) p.val))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  classical
  have hLcap0 := hLslot.trans hLcap
  have hCap0 : 0<Cap := by linarith
  let η := ε/(2*(Lcap+1))
  have hη : 0<η := div_pos hε (by positivity)
  obtain ⟨B₀,hB₀,hcoeff⟩ := slot_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW.continuous
  let B := max 1 B₀
  have hB : 1≤B := le_max_left _ _
  obtain ⟨Ci,hCi,hinj⟩ := natural_radial_energy (α:=α) (2*B) η (by linarith) hη
  obtain ⟨degree,S,hchildren⟩ := canonical_punctured_subsets (α:=α) M H hH
    (Holes+Fintype.card α*Fintype.card α) W a b radial Mcap L Lslot Bmask (ε/2) lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hBmask (half_pos hε) hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨Cc,hCc,hchildren⟩ := hchildren η₀ hQη
  refine ⟨Cap^η*Ci*Cc,by positivity,hchildren.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R hR hRcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  let X := Cap*Z^Lcap
  let atoms := ReferencePrimeEnclosure.primePool X
  let P := fun i=>Z^(w i)
  let pool := fun i=>supportedPool (primePool M H 2 (P i))
  let β₀ := fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight W (P i) (σ i) (freq i) I
  let βc := fun i=>heightCoefficient (holeCoefficient β₀ R₀ i) t
  let χ := fun z=>(naturalCharacter s.character z).excludePrimes R hR
  let D := fun z=>polynomial (χ z) false W₁ X₁ 0 t₁*polynomial (χ z) false W₂ X₂ 0 t₂
  let E := Cc*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε/2)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hX : 1≤X := one_le_mul_of_one_le_of_one_le (by linarith)
    (Real.one_le_rpow hZ.1.le hLcap0)
  have hatoms (I : Id) (hI : I∈atoms) : Supported I ∧ (I.absNorm:ℝ)≤X :=
    ⟨(Finset.mem_filter.mp hI).2.2,
      ((CenteredMomentSourceMass.mem_idealBall _ _).mp (Finset.mem_filter.mp hI).1).2⟩
  have hpool (i : α) : pool i⊆atoms :=
    canonical_pool_enclosed M H Z (w i) Lcap Cap hZ.1.le ((hwL i).trans hLcap) hCap
  have hP (i : α) : 0<P i := Real.rpow_pos_of_pos hZ0 _
  have hp (i : α) (I : Id) (hI : I∈pool i) : Supported I ∧ (I.absNorm:ℝ)≤2*P i :=
    ⟨(Finset.mem_filter.mp hI).2,canonical_pool_norm_le M H _ (hP i) I (Finset.mem_filter.mp hI).1⟩
  have hβc (i : α) (I : Id) (hI : I∈pool i) : ‖βc i I‖≤B := by
    have he := ((hcoeff (relativeCharacter M H hH η₀ (θ i)) (P i) (σ i) (freq i) t
      (hP i) (hσ i) (hσhi i) I (hp i I hI).1.1).1).trans (le_max_right 1 B₀)
    by_cases hi : I∈R₀ i
    · simpa [βc,holeCoefficient,heightCoefficient,hi] using (zero_le_one.trans hB)
    · simpa only [βc,heightCoefficient,holeCoefficient,ite_eq_right hi,β₀,B] using he
  have he := hinj X hX atoms hatoms D χ pool βc P E hpool hE
    (fun z i p=>slotTerm_bound _ _ _ _ B (hP i) (zero_le_one.trans hB) (hp i) (hβc i) p.val)
    (effectiveState s).radial.keep s.radial.profile s.radial.scale radial s.radial.scale_pos
    s.radial_support s.radial.nonneg (by
      intro T Rf hRf
      have hbudget (i : α) : (R₀ i∪(if i∈T then Rf i else ∅)).card≤Holes+Fintype.card α*Fintype.card α := by
        by_cases hi : i∈T
        · simpa only [hi,ite_true] using (Finset.card_union_le (R₀ i) (Rf i)).trans
            (Nat.add_le_add (hR₀ i) (hRf i hi))
        · simp only [hi,ite_false,Finset.union_empty]
          exact (hR₀ i).trans (Nat.le_add_right _ _)
      have hh := hZ.2 θ w σ freq t V (fun i=>R₀ i∪(if i∈T then Rf i else ∅))
        hw hwL hσ hσhi hV hfreq hbudget Bstate s hQ hwidth R hR hRcap T
        W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂
      have hm (i : α) (hi : i∈T) : holeCoefficient βc Rf i=
          heightCoefficient (holeCoefficient β₀ (fun i=>R₀ i∪(if i∈T then Rf i else ∅)) i) t := by
        funext I
        by_cases h₁ : I∈R₀ i <;> by_cases h₂ : I∈Rf i <;>
          simp [βc,holeCoefficient,heightCoefficient,hi,h₁,h₂]
      have hmask : (fun z=>D z*∏i∈T,naturalSlot (χ z) (pool i) (holeCoefficient βc Rf i) (P i))=
          (fun z=>D z*∏i∈T,naturalSlot (χ z) (pool i)
            (heightCoefficient (holeCoefficient β₀ (fun i=>R₀ i∪(if i∈T then Rf i else ∅)) i) t) (P i)) := by
        funext z
        congr 1
        exact Finset.prod_congr rfl (fun i hi=>by rw [hm i hi])
      rw [hmask,punctured_supported_slots s.character R hR D T
        (fun i=>primePool M H 2 (P i))
        (fun i=>heightCoefficient (holeCoefficient β₀ (fun i=>R₀ i∪(if i∈T then Rf i else ∅)) i) t) P
        (effectiveState s).radial.keep (fun z hz=>s.row_ne_zero z hz.1)]
      exact hh)
  have hcost := mul_le_mul_of_nonneg_left
    (cutoff_loss Z Lcap Cap ε (s.width+κ*(∑i,w i)) hZ.1.le hLcap0 hCap0.le hε)
    (show 0≤Ci*Cc*diagonalControl s.radial.profile*
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*(1+|t|+V)^degree by positivity)
  apply he.trans
  convert hcost using 1 <;> dsimp only [η,X,E] <;> ring

end
end Candidate.FourthPower.NativePuncturedInjective
