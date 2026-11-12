/- Copyright (c) 2026 Sil. Apache-2.0.
Uses Hailey Collet's `source_root_maximum_eq_clean` (`Record12518109Gain/WholeRootMaxima.lean`,
Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafContract
import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeRootMaxima

/-!
# High.Inverse.Dictionary — inverse rows as natural rows; zero transfer to the core family

The inverse row family `data.character w`
(`elementCoeff = data.η · rowHom(m⁶ f⁴ w)`) is, coefficient by coefficient, the NATURAL row of `w`
for the fixed base `dataBase data = data.character 1` (`= data.η · rowHom(m⁶ f⁴)`):
the natural row multiplies by `rowHom(fixedBadMask⁶)`, which is the coprimality mask of
`fixedBadMask = λ₀·2`, already contained in the mask of `m` (`λ₀ ∣ m`, `2 ∣ m`).

* `data_character_natural` — `idealCoeff (data.character w) = idealCoeff (naturalRow (dataBase data) w)`.
* `inverse_root_maximum_eq_core` — for `w = c·B⁶` (`sixthFrequencyEquiv (c, B)`), the buffered zero
  maxima of the whole-source family of the inverse row (`wholeSourceFamily rayM H hH η₀
  (data.character w)`, whose `inl` member IS `data.character w`) equal those of the clean core
  family `coreFamily rayM H hH (dataBase data) η₀ c` at every height (HC
  `source_root_maximum_eq_clean`, puncture `R = 1`). So every buffered guard of an inverse HIGH row
  is a guard of the core family, the family of `MarkedCoreR1`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Inverse
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
local instance dictionaryQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The unit row. -/
def unitElement : NonzeroElement := ⟨1, one_ne_zero⟩

/-- The natural base of inverse row data: the row character of the unit row,
`data.η · rowHom(m⁶ f⁴)`. -/
def dataBase (data : RowData) : Character := data.character unitElement

theorem dataBase_coeff (data : RowData) (I : Ideal O) :
    idealCoeff (dataBase data) I =
      idealCoeff data.η I * CanonicalRowCompletion.idealRowHom (data.m^6*data.f^4*1) I :=
  HeckeRowClosure.idealCoeff_eq_row data.η _ data.m data.f 1
    (data.character_spec unitElement) I

/-- The sixth-power mask of `fixedBadMask` is absorbed by the mask of `data.m`. -/
theorem localRowValue_mask (data : RowData) (P : Ideal O) :
    CanonicalRowCompletion.localRowValue (fixedBadMask^6 * data.m^6) P =
      CanonicalRowCompletion.localRowValue (data.m^6) P := by
  rw [CanonicalRowCompletion.localRowValue_mul]
  by_cases h : P.IsMaximal ∧ ActualEisensteinCubic.lambda ∉ P
  · have : P.IsMaximal := h.1
    have e : ∀ x : O, CanonicalRowCompletion.localRowValue (x^6) P =
        if x ∈ P then 0 else 1 := by
      intro x
      have h1 := CanonicalRowCompletion.idealRowHom_prime (x^6) P h.2
      rw [← CanonicalRowCompletion.localRowValue_good] at h1
      rw [← h1, CanonicalRowCompletion.idealRowHom_prime_sixth_mask x P h.2,
        SixthPowerAverage.prime_coprime_span_iff]
      by_cases hx : x ∈ P <;> simp [hx]
    rw [e, e]
    by_cases hm : data.m ∈ P
    · simp [hm]
    · have hf : fixedBadMask ∉ P := by
        intro hf
        have hp : P.IsPrime := h.1.isPrime
        rcases hp.mem_or_mem (show ConcretePrimeRowBridge.goodLambda * 2 ∈ P from hf) with hl | h2
        · obtain ⟨k, hk⟩ := data.lambda_dvd
          exact hm (hk ▸ P.mul_mem_right k hl)
        · obtain ⟨k, hk⟩ := data.two_dvd
          exact hm (hk ▸ P.mul_mem_right k h2)
      simp [hm, hf]
  · have e0 : ∀ x : O, CanonicalRowCompletion.localRowValue x P = 0 := fun x => by
      unfold CanonicalRowCompletion.localRowValue
      simp [h]
    rw [e0, e0, mul_zero]

theorem idealRowHom_mask (data : RowData) :
    CanonicalRowCompletion.idealRowHom (fixedBadMask^6 * data.m^6) =
      CanonicalRowCompletion.idealRowHom (data.m^6) := by
  unfold CanonicalRowCompletion.idealRowHom
  congr 1
  funext P
  exact localRowValue_mask data P

/-- **The inverse row character is the natural row of the data base.** -/
theorem data_character_natural (data : RowData) (w : NonzeroElement) (I : Ideal O) :
    idealCoeff (data.character w) I =
      idealCoeff (naturalRow (dataBase data) w.val w.property).character I := by
  rw [HeckeRowClosure.idealCoeff_eq_row data.η _ data.m data.f w.val (data.character_spec w) I,
    (naturalRow _ _ _).ideal, dataBase_coeff, mul_assoc (idealCoeff data.η I)]
  congr 1
  have e1 : data.m^6*(data.f^4*w.val) = data.m^6*data.f^4*w.val := by ring
  have e2 : data.m^6*data.f^4*1*(fixedBadMask^6*w.val) =
      (fixedBadMask^6*data.m^6)*(data.f^4*w.val) := by ring
  rw [← CanonicalRowCompletion.idealRowHom_argument_mul, e2,
    CanonicalRowCompletion.idealRowHom_argument_mul (fixedBadMask^6*data.m^6), idealRowHom_mask,
    ← CanonicalRowCompletion.idealRowHom_argument_mul, e1]


/-- **Zero transfer**: the buffered zero maxima of the whole-source family of the inverse row
`w = c·B⁶` are those of the clean core family of `c` for the data base. -/
theorem inverse_root_maximum_eq_core (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (data : RowData) (η₀ : Character)
    (w : NonzeroElement) (c : FreeRow) (B : NZIdeal)
    (hw : (ProbePhysical.sixthFrequencyEquiv (c, B)).val = w.val)
    (hn : ∀ j, (Cycle61Moment.wholeSourceFamily rayM H hH η₀ (data.character w) j).residue ≠ 1)
    (hnclean : ∀ j, (coreFamily rayM H hH (dataBase data) η₀ c j).residue ≠ 1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum (Cycle61Moment.wholeSourceFamily rayM H hH η₀
        (data.character w)) hn T =
      HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH (dataBase data) η₀ c) hnclean T := by
  refine Record12518109GainWholeGeometry.source_root_maximum_eq_clean rayM H hH (dataBase data)
    η₀ (data.character w) c B 1 one_ne_zero (fun I => ?_) hn hnclean T
  rw [excluded_ideal _ _ one_ne_zero]
  simp only [isCoprime_one_right, ↓reduceIte]
  rw [data_character_natural, (naturalRow _ _ _).ideal, (naturalRow _ _ _).ideal, hw]

/-- The `inl` member of the whole-source family of the inverse row is the inverse row character. -/
theorem wholeSourceFamily_inl (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (η₀ χ : Character) :
    Cycle61Moment.wholeSourceFamily rayM H hH η₀ χ (Sum.inl ()) = χ := rfl

end
end Qrh.MarkedAnchor.High.Inverse

#print axioms Qrh.MarkedAnchor.High.Inverse.data_character_natural
#print axioms Qrh.MarkedAnchor.High.Inverse.inverse_root_maximum_eq_core
