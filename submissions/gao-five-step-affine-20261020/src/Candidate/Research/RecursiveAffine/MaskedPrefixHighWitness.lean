/- Lift the actual native local HIGH witness through the accumulated literal source prefix.
The original physical state, physical row and zero family are kept, and only the proven
fixed-dictionary presentation is composed. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.MaskedPrefixPresentation
import Candidate.Cycle63.Moment.DepthTwoHighCountRows
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153HighProvider
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment LocalMoment ProbePhysical
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Re-express a genuine local native HIGH witness in the original finite dictionary,
with the accumulated physical source multiplier. No zero or energy estimate is assumed.
The incidence of the actual local holes with the old puncture is indispensable. -/
def MaskedPrefixPresentation.liftHighWitness {Base : Type} {base : Base → Character}
    {η η₀ : Character} {P : Ideal O} {v : O}
    (p : MaskedPrefixPresentation base η P v) {w : NonzeroFrequency}
    (W : DepthTwoHighWitness M (secondFixedDictionary η) η₀ w)
    (hPW : P ∣ W.holes) :
    DepthTwoHighWitness M (extendFixedDictionary base) η₀
      ⟨v*w.val,mul_ne_zero p.multiplier_ne_zero w.property⟩ where
  scale := W.scale
  maskBound := W.maskBound
  profileEdge := W.profileEdge
  state := W.state
  fixed_le_ray := W.fixed_le_ray
  fixed_le_base := W.fixed_le_base
  row := W.row
  keep := W.keep
  natural := W.natural
  index := (p.index,W.index)
  holes := p.holes*W.holes
  holes_ne := mul_ne_zero p.holes_ne_zero W.holes_ne
  mask := fun I => (W.mask I).trans (masked_natural_row_compose (base p.index) η v p.row P p.holes
    p.puncture_ne_zero p.holes_ne_zero p.mask W.index w.val
    (naturalRow _ w.val w.property)
    (naturalRow _ (v*w.val) (mul_ne_zero p.multiplier_ne_zero w.property))
    W.holes W.holes_ne hPW I)

/-- The lift uses exactly the same physical zero family and height; no second density
loss or replacement of the physical source is introduced. -/
theorem MaskedPrefixPresentation.liftHighWitness_zeroMax {Base : Type}
    {base : Base → Character} {η η₀ : Character} {P : Ideal O} {v : O}
    (p : MaskedPrefixPresentation base η P v) {w : NonzeroFrequency}
    (W : DepthTwoHighWitness M (secondFixedDictionary η) η₀ w)
    (hPW : P ∣ W.holes) (T : ℝ) :
    (p.liftHighWitness M W hPW).zeroMax M H hH T = W.zeroMax M H hH T := rfl

/-- The same lift at the literal native multiplierLabel of a physical local joint row.
This is the label consumed by HIGH binning and by the complete history injection. -/
def MaskedPrefixPresentation.liftLabelHighWitness {Base : Type} {base : Base → Character}
    {η η₀ : Character} {P : Ideal O} {v : O}
    (p : MaskedPrefixPresentation base η P v) {left : Bool} {unit : FirstSourceLabel → O}
    (key : NonzeroJointSourceLabel left 1 unit)
    (W : DepthTwoHighWitness M (secondFixedDictionary η) η₀ (nonzeroJointSourceRow key))
    (hPW : P ∣ W.holes) :
    DepthTwoHighWitness M (extendFixedDictionary base) η₀
      (nonzeroJointSourceRow (multiplierLabel left unit p.multiplier_ne_zero key)) where
  scale := W.scale
  maskBound := W.maskBound
  profileEdge := W.profileEdge
  state := W.state
  fixed_le_ray := W.fixed_le_ray
  fixed_le_base := W.fixed_le_base
  row := W.row
  keep := W.keep
  natural := W.natural
  index := (p.index,W.index)
  holes := p.holes*W.holes
  holes_ne := mul_ne_zero p.holes_ne_zero W.holes_ne
  mask := fun I => ((W.mask I).trans (masked_natural_row_compose (base p.index) η v p.row P p.holes
    p.puncture_ne_zero p.holes_ne_zero p.mask W.index (nonzeroJointSourceRow key).val
    (naturalRow _ (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property)
    (naturalRow _ (v*(nonzeroJointSourceRow key).val)
      (mul_ne_zero p.multiplier_ne_zero (nonzeroJointSourceRow key).property))
    W.holes W.holes_ne hPW I)).trans
      (mask_at_multiplier_row _ left v unit (multiplierLabel left unit p.multiplier_ne_zero key)
        (mul_ne_zero p.multiplier_ne_zero (nonzeroJointSourceRow key).property) (p.holes*W.holes) I)

theorem MaskedPrefixPresentation.liftLabelHighWitness_zeroMax {Base : Type}
    {base : Base → Character} {η η₀ : Character} {P : Ideal O} {v : O}
    (p : MaskedPrefixPresentation base η P v) {left : Bool} {unit : FirstSourceLabel → O}
    (key : NonzeroJointSourceLabel left 1 unit)
    (W : DepthTwoHighWitness M (secondFixedDictionary η) η₀ (nonzeroJointSourceRow key))
    (hPW : P ∣ W.holes) (T : ℝ) :
    (p.liftLabelHighWitness M key W hPW).zeroMax M H hH T = W.zeroMax M H hH T := rfl

#print axioms MaskedPrefixPresentation.liftLabelHighWitness
#print axioms MaskedPrefixPresentation.liftLabelHighWitness_zeroMax
#print axioms MaskedPrefixPresentation.liftHighWitness
#print axioms MaskedPrefixPresentation.liftHighWitness_zeroMax
end
end OAI.SevenEighths.Cycle153HighProvider
