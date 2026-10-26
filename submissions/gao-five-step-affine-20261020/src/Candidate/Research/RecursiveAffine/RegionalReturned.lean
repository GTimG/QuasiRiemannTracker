import Candidate.Cycle63.Moment.DepthTwoHighCount
import Candidate.Research.RecursiveAffine.WeightedAttainer

/- Explicit-junction native returned records. These interfaces contain the
literal SecondStepHighCount records; they do not declare any source energy
bound or manufacture a length from a capacity. A regional producer must
construct them from its actual HIGH branch. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153SourceReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound Cycle63Moment

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Literal HIGH records and their actual source payment, at an explicit
junction. The numerical length is part of the payment, not a new cap. -/
structure ReturnedPartAt (junction : ℝ) {Base : Type}
    (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ) (v₁ : O) where
  unit : Bool → FirstSourceLabel → O
  record : (b : Bool) → SecondStepHighCount M H hH (base η₀) η₀ Z Bnorm T b v₁ (unit b)
  scale : ℝ
  length : ℝ
  amp : ℝ
  loss : ℝ
  pays : ∀ b, (record b).Pays junction scale length amp loss

variable {M H hH}

def ReturnedPartAt.value {junction : ℝ} {Base : Type} {base : Character → Base → Character}
    {η₀ : Character} {Z Bnorm T : ℝ} {v₁ : O}
    (P : ReturnedPartAt M H hH junction base η₀ Z Bnorm T v₁) : ℝ :=
  ∑ b, (P.record b).value

theorem ReturnedPartAt.value_nonneg {junction : ℝ} {Base : Type}
    {base : Character → Base → Character} {η₀ : Character} {Z Bnorm T : ℝ} {v₁ : O}
    (P : ReturnedPartAt M H hH junction base η₀ Z Bnorm T v₁) (hZ : 0 ≤ Z) :
    0 ≤ P.value :=
  Finset.sum_nonneg (fun b _ => (P.record b).value_nonneg hZ)

/-- Empty HIGH classes when the regional branch terminates in OLD. -/
def ReturnedPartAt.empty (junction : ℝ) {Base : Type}
    (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ) (v₁ : O)
    (scale length amp loss : ℝ) : ReturnedPartAt M H hH junction base η₀ Z Bnorm T v₁ where
  unit := fun _ _ => 0
  record := fun b => SecondStepHighCount.empty M H hH (base η₀) η₀ Z Bnorm T b v₁ (fun _ => 0)
  scale := scale
  length := length
  amp := amp
  loss := loss
  pays := fun _ σ => σ.elim

/-- The native returned-clause contract at an explicit junction. -/
def ReturnedClauseAt (junction : ℝ) (AllowRet : Prop) {Base : Type}
    (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ) (v₁ : O)
    (scale loss lengthCap ampCap Kcap factor Ret : ℝ) : Prop :=
  Ret = 0 ∨ (AllowRet ∧ ∃ P : ReturnedPartAt M H hH junction base η₀ Z Bnorm T v₁,
    P.scale = scale ∧ P.loss = loss ∧ P.length ≤ lengthCap ∧ P.amp ≤ ampCap ∧
    (∀ b, (Fintype.card (P.record b).Class : ℝ) ≤ Kcap) ∧ Ret = factor * P.value)

/-- The strengthened clause carries a literal selected source and its
retained reduction, so a caller cannot maximize F separately from records.
This definition does not assert that any source produces such a clause. -/
def SelectedReturnedClauseAt (junction : ℝ) (AllowRet : Prop) {Key : Type*}
    (valid : Key → Prop) (F : Key → ℝ) {Base : Type}
    (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ) (v₁ : O)
    (scale loss lengthCap ampCap Kcap factor Ret : ℝ) : Prop :=
  Ret = 0 ∨ (AllowRet ∧ ∃ (key : Key), valid key ∧
    ∃ P : ReturnedPartAt M H hH junction base η₀ Z Bnorm T v₁,
      P.scale = scale ∧ P.loss = loss ∧ P.length ≤ lengthCap - F key ∧ P.amp ≤ ampCap ∧
      (∀ b, (Fintype.card (P.record b).Class : ℝ) ≤ Kcap) ∧ Ret = factor * P.value)

variable (M H hH)

/-- A finite sum over terminal depths. A part at each depth has its own
junction and its own actual payment. Weights include the source-normalizing
and recursive energy factors before a daughter maximum is selected. -/
structure ReturnedFamily (n : ℕ) (junction : Fin n → ℝ) {Base : Type}
    (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ) (v₁ : O) where
  Prefix : Fin n → Type
  [prefixFintype : ∀ j, Fintype (Prefix j)]
  multiplier : (j : Fin n) → Prefix j → O
  root_divides : ∀ j p, v₁ ∣ multiplier j p
  historyMissing : (j : Fin n) → Prefix j → ℝ
  historyMissing_nonneg : ∀ j p, 0 ≤ historyMissing j p
  part : (j : Fin n) → (p : Prefix j) →
    ReturnedPartAt M H hH (junction j) base η₀ Z Bnorm T (multiplier j p)
  weight : (j : Fin n) → Prefix j → ℝ
  weight_nonneg : ∀ j p, 0 ≤ weight j p

variable {M H hH}

attribute [instance] ReturnedFamily.prefixFintype

def ReturnedFamily.value {n : ℕ} {junction : Fin n → ℝ} {Base : Type}
    {base : Character → Base → Character} {η₀ : Character} {Z Bnorm T : ℝ} {v₁ : O}
    (F : ReturnedFamily M H hH n junction base η₀ Z Bnorm T v₁) : ℝ :=
  ∑ j, ∑ p, F.weight j p * (F.part j p).value

/-- OLD or identically zero source: no terminal prefix is invented. -/
def ReturnedFamily.empty (n : ℕ) (junction : Fin n → ℝ) {Base : Type}
    (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ) (v₁ : O) :
    ReturnedFamily M H hH n junction base η₀ Z Bnorm T v₁ where
  Prefix := fun _ => Empty
  multiplier := fun _ p => p.elim
  root_divides := fun _ p => p.elim
  historyMissing := fun _ p => p.elim
  historyMissing_nonneg := fun _ p => p.elim
  part := fun _ p => p.elim
  weight := fun _ p => p.elim
  weight_nonneg := fun _ p => p.elim

theorem ReturnedFamily.empty_value (n : ℕ) (junction : Fin n → ℝ) {Base : Type}
    (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ) (v₁ : O) :
    (ReturnedFamily.empty (M:=M) (H:=H) (hH:=hH) n junction base η₀ Z Bnorm T v₁).value = 0 := by
  unfold ReturnedFamily.value
  apply Finset.sum_eq_zero
  intro j _
  exact Finset.sum_eq_zero (fun p _ => Empty.elim p)

theorem ReturnedFamily.value_nonneg {n : ℕ} {junction : Fin n → ℝ} {Base : Type}
    {base : Character → Base → Character} {η₀ : Character} {Z Bnorm T : ℝ} {v₁ : O}
    (F : ReturnedFamily M H hH n junction base η₀ Z Bnorm T v₁) (hZ : 0 ≤ Z) :
    0 ≤ F.value :=
  Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun p _ =>
    mul_nonneg (F.weight_nonneg j p) ((F.part j p).value_nonneg hZ)))

/-- A literal LOW source-contraction factor multiplies every terminal weight
and preserves the same source indices, records, multipliers and missing logs. -/
def ReturnedFamily.scaleWeights {n : ℕ} {junction : Fin n → ℝ} {Base : Type}
    {base : Character → Base → Character} {η₀ : Character} {Z Bnorm T : ℝ} {v₁ : O}
    (F : ReturnedFamily M H hH n junction base η₀ Z Bnorm T v₁)
    (c : ℝ) (hc : 0 ≤ c) : ReturnedFamily M H hH n junction base η₀ Z Bnorm T v₁ :=
  { F with weight := fun j p => c * F.weight j p
           weight_nonneg := fun j p => mul_nonneg hc (F.weight_nonneg j p) }

theorem ReturnedFamily.value_scaleWeights {n : ℕ} {junction : Fin n → ℝ} {Base : Type}
    {base : Character → Base → Character} {η₀ : Character} {Z Bnorm T : ℝ} {v₁ : O}
    (F : ReturnedFamily M H hH n junction base η₀ Z Bnorm T v₁)
    (c : ℝ) (hc : 0 ≤ c) :
    (F.scaleWeights c hc).value = c * F.value := by
  simp only [ReturnedFamily.value, ReturnedFamily.scaleWeights, Finset.mul_sum, mul_assoc]
  rfl

variable (M H hH)

/-- The source metadata and return records use the same attaining daughter.
`Meta` can retain the literal ChildPrefix, common allocations, residual ideal,
active allocation, orientation, and F. The finite selector never enumerates
these metadata a second time in the terminal density dictionary. -/
structure SelectedReturnedFamily {ι : Type*} (valid : ι → Prop) (Meta : ι → Type*)
    (n : ℕ) (junction : Fin n → ℝ) {Base : Type}
    (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ) (v₁ : O) where
  daughter : ι
  is_valid : valid daughter
  metadata : Meta daughter
  returns : ReturnedFamily M H hH n junction base η₀ Z Bnorm T v₁

variable {M H hH}

/-- The HIGH reserve keeps F without changing the record, dictionary,
missing-radical subtraction or source weight. This is a consequence of the
actual Pays field; constructing that field remains the source producer's job. -/
theorem ReturnedPartAt.pays_with_retained_F {junction : ℝ} {Base : Type}
    {base : Character → Base → Character} {η₀ : Character} {Z Bnorm T : ℝ} {v₁ : O}
    (P : ReturnedPartAt M H hH junction base η₀ Z Bnorm T v₁)
    (Acap F : ℝ) (hcap : P.length ≤ Acap - F) (b : Bool) (σ : (P.record b).Class)
    (hδ : 0 ≤ 2 * (P.record b).zeroBin σ - 1) :
    (P.record b).exponent σ - P.scale + (P.record b).missExp σ +
        LocalMoment.unmarkedDensity (2 * (P.record b).zeroBin σ - 1) *
          ((P.record b).rowExp σ - Real.logb Z ((Ideal.span {v₁}).absNorm : ℝ)) ≤
      P.loss - (P.scale * (1 - LocalMoment.unmarkedDensity (2 * (P.record b).zeroBin σ - 1)) -
        (2 * (P.record b).zeroBin σ - 1) * Acap -
        P.amp * (5 - 6 * LocalMoment.unmarkedDensity (2 * (P.record b).zeroBin σ - 1)) +
        (2 * (P.record b).zeroBin σ - 1) * F) := by
  have hp := ((P.pays b) σ).2.2
  have hm := mul_le_mul_of_nonneg_left hcap hδ
  linarith only [hp, hm]

/-- Exact native moving-state source interface with an explicit junction.
The source operator, order of uniform constants, source rows and HIGH labels
are identical to SecondStepReturnAt; a regional producer must prove it. -/
def SecondStepReturnAtJ (junction : ℝ) {α : Type*} [Fintype α] {Base : Type}
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (base : Character → Base → Character)
    (Wslot : ℝ → ℂ) (bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B : ℝ)
    (Applicable : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) :
    Prop :=
  ∀ (η₀ : Character) (Q : Ideal O), Q ≤ M →
    internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)) (Kclass : ℝ) (C : ℝ), 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (J R : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) → (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
      0 ≤ height → (∀ i, |v i| ≤ height) →
    ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
    ∀ (p : Profiles ap bp) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    ∀ (v₁ : O) (T W length amp loss : ℝ),
      Applicable η₀ Z s v₁ (CenteredMomentEnergyBands.length Z X₁) (CenteredMomentEnergyBands.length Z X₂)
        (∑ i ∈ J \ R, w i) W T length amp loss →
    ∃ (unit : Bool → FirstSourceLabel → O)
      (Hb : (b : Bool) → SecondStepHighCount M H hH (base η₀) η₀ Z B T b v₁ (unit b)),
      (∀ b, (Hb b).Pays junction s.rowWidth length amp loss) ∧
      (∀ b, (Fintype.card (Hb b).Class : ℝ) ≤ Kclass) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : ↥(J \ R) => primePool M H bslot (Z ^ (w i)))
        (fun (i : ↥(J \ R)) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
        (fun i : ↥(J \ R) => Z ^ (w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 * (1 + |t| + height) ^ degree *
        (Z ^ (s.width + ε) + ∑ b, (Hb b).value)


end
end OAI.SevenEighths.Cycle153SourceReturn

#print axioms OAI.SevenEighths.Cycle153SourceReturn.ReturnedFamily.value_scaleWeights
#print axioms OAI.SevenEighths.Cycle153SourceReturn.ReturnedPartAt.pays_with_retained_F
