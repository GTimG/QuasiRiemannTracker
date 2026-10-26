/- The bound of the second step for a character and an ideal, over a finite set of remaining slots and over a finite
cover of the states to which the step applies. Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.LowBranch.Dispatch
import Candidate.Cycle63.Moment.FiniteUniform

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional QuadraticInitialBound

variable {α : Type*} {Base : Type}
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable (base : Character → Base → Character)
variable (Wslot : ℝ → ℂ) (bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B : ℝ)

/-- The bound of `SecondStepReturnAt` for a character `η₀` and an ideal `Q` at the scale `Z`, with the constants
`Kclass`, `degree`, `S` and `C` given, for the states whose remaining slots are the finite set `U`: it is the body of
`SecondStepReturnAt` after its constants and its eventual quantifier, with the remaining slots `J \ R` replaced by a
finite set of slots `U`. -/
def SecondStepBody
    (Applicable : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (Kclass : ℝ) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) (η₀ : Character) (Q : Ideal O) (Z : ℝ) : Prop :=
  1 < Z ∧
    ∀ (U : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) → (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
      0 ≤ height → (∀ i, |v i| ≤ height) →
    ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
    ∀ (p : Profiles ap bp) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    ∀ (v₁ : O) (T W length amp loss : ℝ),
      Applicable η₀ Z s v₁ (CenteredMomentEnergyBands.length Z X₁) (CenteredMomentEnergyBands.length Z X₂)
        (∑ i ∈ U, w i) W T length amp loss →
    ∃ (unit : Bool → FirstSourceLabel → O)
      (Hb : (b : Bool) → SecondStepHighCount M H hH (base η₀) η₀ Z B T b v₁ (unit b)),
      (∀ b, (Hb b).Pays Cycle63.Optimization.secondJunction s.rowWidth length amp loss) ∧
      (∀ b, (Fintype.card (Hb b).Class : ℝ) ≤ Kclass) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : ↥U => primePool M H bslot (Z ^ (w i)))
        (fun (i : ↥U) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
        (fun i : ↥U => Z ^ (w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 * (1 + |t| + height) ^ degree *
        (Z ^ (s.width + ε) + ∑ b, (Hb b).value)

variable {M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B}
variable {Applicable : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
variable {Kclass Kclass' : ℝ} {degree degree' : ℕ} {S S' : Finset (ℕ × ℕ)} {C C' : ℝ} {η₀ : Character} {Q : Ideal O}
  {Z : ℝ}

/-- The bound of the second step with a larger count of classes, degree, source set and constant. -/
theorem SecondStepBody.mono (hK : Kclass ≤ Kclass') (hd : degree ≤ degree') (hS : S ⊆ S') (hC0 : 0 ≤ C)
    (hC : C ≤ C') (h : SecondStepBody (α := α) M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B
      Applicable Kclass degree S C η₀ Q Z) :
    SecondStepBody (α := α) M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B Applicable Kclass' degree'
      S' C' η₀ Q Z := by
  refine ⟨h.1, ?_⟩
  intro U θ w σ v t height hw0 hwL hlo hhi hh hv s hs hW p X₁ X₂ hX₁ hX₂ hL₁ hL₂ v₁ T Wd length amp loss happ
  obtain ⟨unit, Hb, hpays, hcard, henergy⟩ :=
    h.2 U θ w σ v t height hw0 hwL hlo hhi hh hv s hs hW p X₁ X₂ hX₁ hX₂ hL₁ hL₂ v₁ T Wd length amp loss happ
  refine ⟨unit, Hb, hpays, fun b => (hcard b).trans hK, henergy.trans ?_⟩
  have hZ0 : 0 ≤ Z := (zero_lt_one.trans h.1).le
  have hbase : 1 ≤ 1 + |t| + height := by linarith [abs_nonneg t]
  exact dispatch_mono h.1.le (diagonalControl_nonneg s.radial.profile) hC0 hC (p.control_nonneg S)
    (profiles_control_mono hS p) hbase hd le_rfl
    (Finset.sum_nonneg fun b _ => (Hb b).value_nonneg hZ0)

/-- The second step over a finite cover of its applicable states, for a character `η₀` and an ideal `Q`: if every state
to which it applies lies in one of finitely many parts, and on each part the bound holds with its own constants, then
it holds on all states with one count of classes, one degree, one source set and one constant. -/
theorem second_step_body_of_cover {ι : Type} [Finite ι] (η₀ : Character) (Q : Ideal O)
    (Part : ι → Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hcover : ∀ (η₀ : Character) (Z : ℝ) (s : NaturalState Z Bmask bΦ) (v₁ : O) (x₁ x₂ z W T length amp loss : ℝ),
      0 ≤ z → Applicable η₀ Z s v₁ x₁ x₂ z W T length amp loss →
      ∃ i, Part i η₀ Z s v₁ x₁ x₂ z W T length amp loss)
    (hpart : ∀ i, ∃ (Kcl : ℝ) (d : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      SecondStepBody (α := α) M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B (Part i) Kcl d S C η₀ Q Z) :
    ∃ (Kclass : ℝ) (d : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      SecondStepBody (α := α) M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B Applicable Kclass d S C
        η₀ Q Z := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose Kcl dd SS CC hCC hfam using hpart
  let Kclass : ℝ := ∑ i, |Kcl i|
  have hK : ∀ i, Kcl i ≤ Kclass := fun i =>
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |Kcl j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  let P : ι → ℕ → Finset (ℕ × ℕ) → Unit → ℝ → ℝ → Prop := fun i d S _ C Z =>
    0 < C ∧ SecondStepBody (α := α) M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B (Part i) Kclass
      d S C η₀ Q Z
  have hmono : ∀ i d d' S S' x C C' Z, d ≤ d' → S ⊆ S' → C ≤ C' → P i d S x C Z → P i d' S' x C' Z := by
    intro i d d' S S' x C C' Z hd hS hC hP
    exact ⟨hP.1.trans_le hC, hP.2.mono le_rfl hd hS hP.1.le hC⟩
  have hfamily : ∀ i, ∃ (d : ℕ) (S : Finset (ℕ × ℕ)), ∀ x, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, P i d S x C Z :=
    fun i => ⟨dd i, SS i, fun _ => ⟨CC i, hCC i, (hfam i).mono fun Z hZ =>
      ⟨hCC i, hZ.mono (hK i) le_rfl le_rfl (hCC i).le le_rfl⟩⟩⟩
  obtain ⟨d, S, hall⟩ := Cycle63.eventually_uniform_of_finite (P := P) hmono hfamily
  obtain ⟨C, hC, hev⟩ := hall ()
  refine ⟨Kclass, d, S, C, hC, ?_⟩
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with Z hZ hZ1
  refine ⟨hZ1, ?_⟩
  intro U θ w σ v t height hw0 hwL hlo hhi hh hv s hs hW p X₁ X₂ hX₁ hX₂ hL₁ hL₂ v₁ T Wd length amp loss happ
  obtain ⟨i, hi⟩ := hcover η₀ Z s v₁ _ _ _ Wd T length amp loss (Finset.sum_nonneg fun j _ => hw0 j) happ
  exact (hZ i).2.2 U θ w σ v t height hw0 hwL hlo hhi hh hv s hs hW p X₁ X₂ hX₁ hX₂ hL₁ hL₂ v₁ T Wd length amp loss hi

variable [Fintype α] in
/-- `SecondStepReturnAt` from the bound over the finite sets of slots: the remaining slots of the second step are
`J \ R`. -/
theorem second_step_return_of_body
    (h : ∀ (η₀ : Character) (Q : Ideal O), Q ≤ M → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ (Kclass : ℝ) (d : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        SecondStepBody (α := α) M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B Applicable Kclass d S C
          η₀ Q Z) :
    SecondStepReturnAt (α := α) M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B Applicable := by
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kclass, d, S, C, hC, hev⟩ := h η₀ Q hQM hQ0 hQt hQ72
  refine ⟨d, S, Kclass, C, hC, hev.mono fun Z hZ => ⟨hZ.1, ?_⟩⟩
  intro J R θ w σ v t height hw0 hwL hlo hhi hh hv s hs hW p X₁ X₂ hX₁ hX₂ hL₁ hL₂ v₁ T Wd length amp loss happ
  exact hZ.2 _ θ w σ v t height hw0 hwL hlo hhi hh hv s hs hW p X₁ X₂ hX₁ hX₂ hL₁ hL₂ v₁ T Wd length amp loss happ

end
end OAI.SevenEighths.Cycle63Moment.LowBranch
