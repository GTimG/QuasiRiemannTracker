/- Copyright (c) 2026 Sil. Apache-2.0.
Exact dictionary from the original restricted common columns to literal
masked live tuples. Domain completion uses coefficient support. Every
coprimality, divisibility, and tuple restriction stays inside the row.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedCommonEnergy
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedDivisorMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedRestrictedDictionary
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentLiveDomain CenteredMomentFirstSectors
open MixedCommonCoefficient MixedCommonEnergy MixedLiteralAllocation MixedDivisorMask
open MixedLiveNormalization MixedCommonRestriction
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

/-- The existing supported-column physical row equals the natural
character row with the entire height factor retained. Only the retained
physical row z must be nonzero; no coefficient or pool support hypothesis
is required, because the fixed bad mask already handles those zeros. -/
theorem height_source_natural_character (η : Character) (t : ℝ)
    (Q : Finset Id) (β : Id→ℂ) (z : O) (hz : z≠0) :
    rowPolynomial Finset.univ (sourceGenerator Q)
      (fun I : supportedColumns Q=>β I*heightCoeff η t I) z=
      ∑I∈Q,β I*idealCoeff (naturalCharacter η z) I*(I.absNorm:ℂ)^(Complex.I*t) := by
  rw [height_source_row]
  apply Finset.sum_congr rfl
  intro I hI
  rw [naturalCharacter_eq η z hz,(naturalRow η z hz).ideal]
  change β I*((idealCoeff η I*CanonicalRowCompletion.idealRowHom
    (fixedBadMask^6*(1*z)) I)*(I.absNorm:ℂ)^(Complex.I*t))=_
  rw [one_mul]
  ring

/-- Coefficient-agnostic energy bridge. This is an exact equality, so
literal restrictions and window multipliers in β remain inside the
square. The height phase is explicit and is not replaced by its norm. -/
theorem restricted_energy_natural_character (η : Character) (t : ℝ)
    (Q : Finset Id) (β : Id→ℂ) (keep : O→Prop)
    (hkeep : ∀z,keep z→z≠0) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep Q β (heightCoeff η t) W K=
      radialEnergy (fun z=>∑I∈Q,β I*idealCoeff (naturalCharacter η z) I*
        (I.absNorm:ℂ)^(Complex.I*t)) keep W K := by
  unfold sourceRestrictedEnergy restrictedEnergy radialEnergy
  apply tsum_congr
  intro z
  by_cases hz : keep z
  · rw [ite_eq_left hz,ite_eq_left hz,height_source_natural_character η t Q β z (hkeep z hz)]
  · rw [ite_eq_right hz,ite_eq_right hz]

/-- Regrouping a finite tuple coefficient into columns is valid for an
arbitrary subsequent column multiplier. In particular this applies to
characters, row kernels, height phases, and column windows. -/
theorem finite_column_sum (T : Finset (Tuple α)) (β : Tuple α→ℂ) (f : Id→ℂ) :
    (∑I∈finiteColumns T,finiteColumnCoefficient T β I*f I)=
      ∑v∈T,β v*f (finiteTupleProduct v) := by
  calc
    _ = ∑I∈finiteColumns T,∑v∈T.filter (fun v=>finiteTupleProduct v=I),
        β v*f (finiteTupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [finiteColumnCoefficient,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

/-- The support statement is used before squaring: an arbitrary column
multiplier may be present, but no term with a nonzero live coefficient
is lost when the original residual column pool is replaced. -/
theorem restricted_live_column_sum (H : Id) (S : (α⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (B : Tuple α) (hB : ∀j,B j≠0) (G R : Id) (hG : G≠0)
    (hlabel : B∈allocationLabels S G) (hprod : finiteTupleProduct B=G)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) (f : Id→ℂ) :
    (∑I∈residualPool G hG (finiteColumns (Fintype.piFinset S)),
      finiteColumnCoefficient (liveBox S B hB)
        (fun v=>tupleWeight H v*liveProfile B G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v) I*f I)=
      ∑v∈liveBox S B hB,
        tupleWeight H v*liveProfile B G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v*
          f (finiteTupleProduct v) := by
  apply (sum_same_support _ (finiteColumns (liveBox S B hB)) _ f ?_ ?_).trans
    (finite_column_sum _ _ f)
  · intro I hI hn
    exact finite_column_mem _ _ I hn
  · intro I hI hn
    exact (mem_residualPool G hG _ I).mpr
      (masked_live_support S hS hp B hB G R I hlabel hprod ν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ (tupleWeight H) hn).1

/-- Exact whole-column common extraction, retaining both the literal
tuple restriction and the squarefree-divisor mask. Squarefreeness is
not needed for this identity; it enters only in the subsequent bound. -/
theorem common_masked_column_sum (H : Id) (S : (α⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (G R seed D : Id) (hG : G≠0) (hseed : seed∣G)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) (f : Id→ℂ) :
    (∑I∈residualPool G hG (finiteColumns (Fintype.piFinset S)),
      (if IsCoprime G I ∧ D∣I then finiteColumnCoefficient (Fintype.piFinset S)
        (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ B₁ B₂ seed v) (G*I) else 0)*f I)=
      ∑B : actualAllocations S G,
        (frozenWeight H B.val*frozenCoefficient B.val G R ν Wslot P)*
          ∑v∈liveBox S B.val
            (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1,
            if D∣finiteTupleProduct v then tupleWeight H v*
              liveProfile B.val G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v*
              f (finiteTupleProduct v) else 0 := by
  let Q := residualPool G hG (finiteColumns (Fintype.piFinset S))
  let c := fun B : actualAllocations S G=>frozenWeight H B.val*frozenCoefficient B.val G R ν Wslot P
  let β := fun B : actualAllocations S G=>finiteColumnCoefficient
    (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1)
    (fun v=>tupleWeight H v*liveProfile B.val G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v)
  let g := fun I : Id=>if D∣I then f I else 0
  have hne (I : Id) (hI : I∈Q) : I≠0 := by
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp ((mem_residualPool G hG _ I).mp hI)
    have hv0 : finiteTupleProduct v≠0 := by
      unfold finiteTupleProduct
      exact Finset.prod_ne_zero_iff.mpr (fun j _=>hS j _ (Fintype.mem_piFinset.mp hv j))
    rw [he] at hv0
    exact right_ne_zero_of_mul hv0
  have hrow (I : Id) (hI : I∈Q) :
      (if IsCoprime G I ∧ D∣I then finiteColumnCoefficient (Fintype.piFinset S)
        (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ B₁ B₂ seed v) (G*I) else 0)*f I=
        ∑B : actualAllocations S G,c B*(β B I*g I) := by
    have hm : (if IsCoprime G I ∧ D∣I then finiteColumnCoefficient (Fintype.piFinset S)
        (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ B₁ B₂ seed v) (G*I) else 0)*f I=
        (if IsCoprime G I then finiteColumnCoefficient (Fintype.piFinset S)
          (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
            X₁ X₂ Y₁ Y₂ B₁ B₂ seed v) (G*I) else 0)*g I := by
      by_cases hc : IsCoprime G I <;> by_cases hd : D∣I <;> simp [g,hc,hd]
    rw [hm,punctured_restricted_column H S hS hp G R seed I hG (hne I hI) hseed
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro B hB
    dsimp only [c,β]
    ring
  calc
    _ = ∑I∈Q,∑B : actualAllocations S G,c B*(β B I*g I) :=
      Finset.sum_congr rfl hrow
    _ = ∑B : actualAllocations S G,c B*(∑I∈Q,β B I*g I) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B hB
      apply congrArg (fun x : ℂ=>c B*x)
      apply (restricted_live_column_sum H S hS hp B.val
        (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1 G R hG
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ g).trans
      apply Finset.sum_congr rfl
      intro v hv
      dsimp only [g]
      split_ifs <;> simp

/-- Concrete normalized original source with the actual Hecke character.
The right side is precisely the masked common-row family whose uniform
bound is proved in MixedCommonMasked. No child-energy premise occurs. -/
theorem normalized_common_masked_identity (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R seed D : Id) (hG : G≠0) (hseed : seed∣G)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    normalization (X₁*X₂) P*
      (∑I∈residualPool G hG (finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))),
        (if IsCoprime G I ∧ D∣I then finiteColumnCoefficient
          (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
          (fun v=>tupleWeight (punctureProduct S H) v*profileCoefficient R ν Wslot P W₁ W₂
            X₁ X₂ Y₁ Y₂ d.1 d.2 seed v) (G*I) else 0)*idealCoeff χ I)=
      ∑B : actualAllocations (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) G,
        frozenWeight (punctureProduct S H) B.val*
          (normalization (X₁*X₂) P*(frozenCoefficient B.val G R ν Wslot P*
            maskedLiveSum χ S H pool d hd B.val
              (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1 G R D
              ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂)) := by
  have he := common_masked_column_sum (punctureProduct S H)
    (sourcePools pool d hd b X₁ X₂ Y₁ Y₂)
    (source_pools_nonzero pool hp d hd b X₁ X₂ Y₁ Y₂) (fun i I hI=>hp i I hI)
    G R seed D hG hseed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 (idealCoeff χ)
  apply (congrArg (fun x : ℂ=>normalization (X₁*X₂) P*x) he).trans
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  unfold maskedLiveSum
  ring

end
end Candidate.FourthPower.MixedRestrictedDictionary
