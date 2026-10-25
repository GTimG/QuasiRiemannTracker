/- Copyright (c) 2026 Sil. Apache-2.0.
Exact physical-source energy dictionary at every independent height.
The literal tuple restrictions and source pools remain unchanged. A
single scalar phase is extracted only after proving the row identity.
-/
import Candidate.SilPrior.FourthPower.MixedCommonHeights
import Candidate.SilPrior.FourthPower.MixedOriginalSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedHeightEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonMaskEnergy
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedLiveNormalization MixedCommonHeights MixedOriginalSource MixedRestrictedDictionary
open MixedCanonicalSource ReferencePrimeEnclosure
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

/-- The actual original finite column coefficient, before common
extraction. In particular tupleWeight stays inside its finite sum. -/
def originalColumn (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : Id→ℂ :=
  finiteColumnCoefficient (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    (fun u=>tupleWeight (punctureProduct S H) u*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed u)

/-- Exact independent-height absorption, retaining the residual phase
and both original prefix norms. Neither squarefreeness nor seed|G is
needed: those enter the analytic estimate after this identity. -/
theorem original_masked_height_row (χ : Character) (v : ℝ)
    (S H : Finset PrimeIdeal) (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R seed D : Id) (hG : G≠0)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) :
    normalization (X₁*X₂) P*
      (∑I∈residualPool G hG (finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))),
        (if IsCoprime G I ∧ D∣I then
          originalColumn S H pool d hd R seed ν Wslot P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂)
            b X₁ X₂ Y₁ Y₂ (G*I) else 0)*idealCoeff χ I*(I.absNorm:ℂ)^(Complex.I*v))=
      residualPhase (X₁*X₂) d G v*
        originalMaskedRow χ S H pool d hd G R seed D hG
          (fun i=>heightCoefficient (ν i) v) Wslot P
          (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
          b X₁ X₂ Y₁ Y₂ := by
  let Q := Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂)
  have hQ : ∀u∈Q,∀j,u j≠0 := by
    intro u hu j
    exact source_pools_nonzero pool hp d hd b X₁ X₂ Y₁ Y₂ j _ (Fintype.mem_piFinset.mp hu j)
  have hcol (I : Id) :
      originalColumn S H pool d hd R seed ν Wslot P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂)
          b X₁ X₂ Y₁ Y₂ (G*I)*(I.absNorm:ℂ)^(Complex.I*v)=
        residualPhase (X₁*X₂) d G v*
          originalColumn S H pool d hd R seed (fun i=>heightCoefficient (ν i) v) Wslot P
            (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
            b X₁ X₂ Y₁ Y₂ (G*I) := by
    simpa only [Q,originalColumn,idealHeight,MonoidHom.coe_mk,OneHom.coe_mk,heightPhase,
      Complex.ofReal_natCast] using
      residual_column_height Q hQ (tupleWeight (punctureProduct S H)) R seed G hG ν Wslot P
        W₁ W₂ t₁ t₂ v X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY d hd I
  have hterm (I : Id) :
      (if IsCoprime G I ∧ D∣I then
        originalColumn S H pool d hd R seed ν Wslot P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂)
          b X₁ X₂ Y₁ Y₂ (G*I) else 0)*idealCoeff χ I*(I.absNorm:ℂ)^(Complex.I*v)=
      residualPhase (X₁*X₂) d G v*
        ((if IsCoprime G I ∧ D∣I then
          originalColumn S H pool d hd R seed (fun i=>heightCoefficient (ν i) v) Wslot P
            (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
            b X₁ X₂ Y₁ Y₂ (G*I) else 0)*idealCoeff χ I) := by
    by_cases h : IsCoprime G I ∧ D∣I
    · simp only [if_pos h]
      calc
        _ = (originalColumn S H pool d hd R seed ν Wslot P
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (G*I)*
              (I.absNorm:ℂ)^(Complex.I*v))*idealCoeff χ I := by ring
        _ = _ := by rw [hcol I];ring
    · simp only [h,ite_false,zero_mul,mul_zero]
  simp_rw [hterm]
  rw [←Finset.mul_sum]
  change normalization (X₁*X₂) P*(residualPhase (X₁*X₂) d G v*_)=_
  unfold originalMaskedRow
  change normalization (X₁*X₂) P*(residualPhase (X₁*X₂) d G v*_)=
    residualPhase (X₁*X₂) d G v*(normalization (X₁*X₂) P*_)
  dsimp only [originalColumn]
  ring

/-- The energy identity has exactly the same keep predicate on both
sides. Its only row hypothesis is nonvanishing on kept rows. -/
theorem original_source_height_energy (η : Character) (v : ℝ)
    (S H : Finset PrimeIdeal) (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R seed D : Id) (hG : G≠0)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (keep : O→Prop) (hkeep : ∀z,keep z→z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep
      (residualPool G hG (finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))))
      (fun I=>if IsCoprime G I ∧ D∣I then
        originalColumn S H pool d hd R seed ν Wslot P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂)
          b X₁ X₂ Y₁ Y₂ (G*I) else 0) (heightCoeff η v) Φ K/
      (X₁*X₂*∏i,P i)=
    radialEnergy (fun z=>originalMaskedRow (naturalCharacter η z) S H pool d hd G R seed D hG
      (fun i=>heightCoefficient (ν i) v) Wslot P
      (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
      b X₁ X₂ Y₁ Y₂) keep Φ K := by
  rw [restricted_energy_natural_character η v _ _ keep hkeep Φ K]
  rw [←radial_normalization (X₁*X₂) (mul_pos hX₁ hX₂) P hP]
  have hrow (z : O) := original_masked_height_row (naturalCharacter η z) v S H pool hp
    d hd G R seed D hG ν Wslot P W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY
  simp_rw [hrow]
  rw [radial_mul,residual_phase_norm (X₁*X₂) (mul_pos hX₁ hX₂) d hd G hG v,one_pow,one_mul]

/-- Slot coefficients need agree only at the actual marked pool.
Ordinary ideals and inactive coefficients do not introduce a global
equality requirement at the zero ideal. -/
theorem original_masked_row_congr_slots (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R seed D : Id) (hG : G≠0)
    (ν ν' : α→Id→ℂ) (hν : ∀i,∀I∈pool i,ν i I=ν' i I)
    (Wslot : α→ℝ→ℂ) (P : α→ℝ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    originalMaskedRow χ S H pool d hd G R seed D hG ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      originalMaskedRow χ S H pool d hd G R seed D hG ν' Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  unfold originalMaskedRow
  apply congrArg (fun x : ℂ=>normalization (X₁*X₂) P*x)
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : IsCoprime G I ∧ D∣I
  · simp only [if_pos h]
    apply congrArg (fun x : ℂ=>x*idealCoeff χ I)
    unfold finiteColumnCoefficient
    apply Finset.sum_congr rfl
    intro u hu
    apply congrArg (fun x : ℂ=>tupleWeight (punctureProduct S H) u*x)
    unfold profileCoefficient
    have hm : (∏i,ν i (u (Sum.inl i))*Wslot i ((u (Sum.inl i)).absNorm/P i))=
        ∏i,ν' i (u (Sum.inl i))*Wslot i ((u (Sum.inl i)).absNorm/P i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hν i _ (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hu).1 (Sum.inl i))]
    rw [hm]
  · simp only [h,ite_false]

/-- Canonical form for the all-height envelope: the single marked height
is t+v, and each ordinary phase frequency is t_i+v/(2*pi). -/
theorem canonical_source_height_energy (η : Character) (v : ℝ)
    (S H : Finset PrimeIdeal) (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R seed D : Id) (hG : G≠0)
    (ν : α→Character) (R₀ : α→Finset Id) (t : ℝ)
    (Wslot : α→ℝ→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (keep : O→Prop) (hkeep : ∀z,keep z→z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep
      (residualPool G hG (finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))))
      (fun I=>if IsCoprime G I ∧ D∣I then
        originalColumn S H pool d hd R seed (slotCoefficient ν R₀ t) Wslot P
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (G*I) else 0)
      (heightCoeff η v) Φ K/(X₁*X₂*∏i,P i)=
    radialEnergy (fun z=>originalMaskedRow (naturalCharacter η z) S H pool d hd G R seed D hG
      (slotCoefficient ν R₀ (t+v)) Wslot P
      (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
      b X₁ X₂ Y₁ Y₂) keep Φ K := by
  apply (original_source_height_energy η v S H pool hp d hd G R seed D hG
    (slotCoefficient ν R₀ t) Wslot P hP W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hXY keep hkeep Φ K).trans
  apply congrArg (fun f : O→ℂ=>radialEnergy f keep Φ K)
  funext z
  exact original_masked_row_congr_slots (naturalCharacter η z) S H pool d hd G R seed D hG
    _ _ (fun i I hI=>slot_coefficient_height ν R₀ t v i I (hp i I hI).ne_zero)
    Wslot P (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
    b X₁ X₂ Y₁ Y₂

end
end Candidate.SilPrior.FourthPower.MixedHeightEnergy
