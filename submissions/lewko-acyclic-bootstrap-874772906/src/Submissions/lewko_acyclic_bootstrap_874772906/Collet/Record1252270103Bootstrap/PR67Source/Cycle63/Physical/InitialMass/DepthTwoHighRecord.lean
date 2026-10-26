import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoHighCountRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighBins
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The HIGH part of the second step in count form from a binned count of keys: one class for each piece of the labels
and each occupied exponent bin of the piece. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily HeckeDetectorZeros LocalMoment ProbePhysical CanonicalQuadraticSieve IdealMobiusDivisorSum
open CenteredMomentEnergyState CenteredMomentNaturalRowSource Cycle63Moment
variable {M : Ideal O} [NeZero M]
variable {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {Base : Type} {base : Base → Character} {η₀ : Character} {Z B T : ℝ} {left : Bool} {v₁ : O}
  {unit : FirstSourceLabel → O}

section Record
variable {κ ι : Type} [Fintype ι] (labels : Finset κ) (select : κ → ι) (x : κ → Fin 4 → ℝ) (width : ℝ)

/-- The labels of the piece `i`: those assigned to `i`. -/
def pieceLabels (i : ι) : Finset κ := labels.filter (fun l => select l = i)

/-- A class of the binned record: a piece together with an occupied exponent bin of the piece. -/
abbrev BinClass := Σ i : ι, {b // b ∈ (pieceLabels labels select i).image (fun l => exponentBin width (x l))}

/-- The labels of a class: those of its piece in its exponent bin. -/
def binClassLabels (c : BinClass labels select x width) : Finset κ :=
  (pieceLabels labels select c.1).filter (fun l => exponentBin width (x l) = c.2.val)

variable {labels select x width}

omit [Fintype ι] in
/-- A label of a class is a label of the family, of the class's piece, in the class's exponent bin. -/
theorem mem_binClassLabels {c : BinClass labels select x width} {l : κ}
    (h : l ∈ binClassLabels labels select x width c) :
    l ∈ labels ∧ select l = c.1 ∧ exponentBin width (x l) = c.2.val := by
  unfold binClassLabels pieceLabels at h
  rw [Finset.mem_filter, Finset.mem_filter] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

omit [Fintype ι] in
/-- Every class has a label. -/
theorem binClassLabels_nonempty (c : BinClass labels select x width) :
    (binClassLabels labels select x width c).Nonempty := by
  obtain ⟨l, hl, hb⟩ := Finset.mem_image.mp c.2.property
  exact ⟨l, Finset.mem_filter.mpr ⟨hl, hb⟩⟩

variable (labels select x width)
variable (lab : κ → NonzeroJointSourceLabel left v₁ unit)
  (W : ∀ l, DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow (lab l)))
  (expo : ι → (Fin 4 → ℤ) → ℝ) (zero : ι → ℝ) (rowShift : ℝ)

/-- The HIGH part of the second step from a binned count of keys. A class is a piece `i` with an occupied exponent bin
`b` of the piece; its labels are the keys `lab l` of the labels `l` of the piece in the bin, its exponent is
`expo i b`, its zero parameter `zero i`, and its row-norm and missing-radical exponents are the upper edges of `b` in
the frequency coordinate, shifted by `rowShift`, and in the missing-radical coordinate. -/
def secondStepBinRecord (hZ : 1 ≤ Z) (hw : 0 < width)
    (hzero : ∀ l ∈ labels, zero (select l) ≤ (W l).zeroMax M H hH T)
    (hrow : ∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (lab l)) ≤ Z^(x l 2 + rowShift))
    (hsupp : ∀ l ∈ labels, Supported (lab l).val.1.1.1 ∧ (lab l).val.1.1.2 ≠ 0 ∧
      Supported (lab l).val.2.1.1 ∧ (lab l).val.2.1.2 ≠ 0)
    (hsame : ∀ l ∈ labels, primeSupport (lab l).val.1.1.1 = primeSupport (lab l).val.1.1.2 ∧
      primeSupport (lab l).val.2.1.1 = primeSupport (lab l).val.2.1.2)
    (hcap : ∀ l ∈ labels,
      ((Ideal.span {jointSourceRow left v₁ unit (lab l).val}*firstSourceMissing left (lab l).val.1).absNorm : ℝ) ≤
        Z^B)
    (hideal : ∀ l ∈ labels, ((lab l).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧ ((lab l).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
      ((lab l).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((lab l).val.2.1.2.absNorm : ℝ) ≤ Z^B)
    (hmiss : ∀ l ∈ labels, ((firstSourceMissing left (lab l).val.1).absNorm : ℝ) ≤ Z^(x l 1)) :
    SecondStepHighCount M H hH base η₀ Z B T left v₁ unit :=
  SecondStepHighCount.sigma (fun c : BinClass labels select x width =>
    SecondStepHighCount.ofRows (binClassLabels labels select x width c) lab W (expo c.1 c.2.val)
      (exponentBinUpper width c.2.val 2 + rowShift) (exponentBinUpper width c.2.val 1) (zero c.1)
      (fun l hl => by
        have h := mem_binClassLabels hl
        rw [← h.2.1]
        exact hzero l h.1)
      (fun l hl => by
        have h := mem_binClassLabels hl
        have he := (exponent_bin_enclosure width hw (x l) 2).1
        rw [h.2.2] at he
        exact (hrow l h.1).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)))
      (fun l hl => hsupp l (mem_binClassLabels hl).1)
      (fun l hl => hsame l (mem_binClassLabels hl).1)
      (fun l hl => hcap l (mem_binClassLabels hl).1)
      (fun l hl => hideal l (mem_binClassLabels hl).1)
      (fun l hl => by
        have h := mem_binClassLabels hl
        have he := (exponent_bin_enclosure width hw (x l) 1).1
        rw [h.2.2] at he
        exact (hmiss l h.1).trans (Real.rpow_le_rpow_of_exponent_le hZ he)))

variable (hZ : 1 ≤ Z) (hw : 0 < width)
  (hzero : ∀ l ∈ labels, zero (select l) ≤ (W l).zeroMax M H hH T)
  (hrow : ∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (lab l)) ≤ Z^(x l 2 + rowShift))
  (hsupp : ∀ l ∈ labels, Supported (lab l).val.1.1.1 ∧ (lab l).val.1.1.2 ≠ 0 ∧
    Supported (lab l).val.2.1.1 ∧ (lab l).val.2.1.2 ≠ 0)
  (hsame : ∀ l ∈ labels, primeSupport (lab l).val.1.1.1 = primeSupport (lab l).val.1.1.2 ∧
    primeSupport (lab l).val.2.1.1 = primeSupport (lab l).val.2.1.2)
  (hcap : ∀ l ∈ labels,
    ((Ideal.span {jointSourceRow left v₁ unit (lab l).val}*firstSourceMissing left (lab l).val.1).absNorm : ℝ) ≤
      Z^B)
  (hideal : ∀ l ∈ labels, ((lab l).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧ ((lab l).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
    ((lab l).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((lab l).val.2.1.2.absNorm : ℝ) ≤ Z^B)
  (hmiss : ∀ l ∈ labels, ((firstSourceMissing left (lab l).val.1).absNorm : ℝ) ≤ Z^(x l 1))

/-- The count form of the binned record is the sum over the pieces of the binned counts of the keys of the piece, with
the weight `Z^(expo i b)` on the bin `b` of the piece `i`. -/
theorem secondStepBinRecord_value :
    (secondStepBinRecord labels select x width lab W expo zero rowShift hZ hw hzero hrow hsupp hsame hcap hideal
      hmiss).value =
      ∑ i, keyBinnedCount (pieceLabels labels select i) lab x width (fun b => Z^(expo i b)) := by
  unfold secondStepBinRecord
  rw [SecondStepHighCount.sigma_value, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold keyBinnedCount
  rw [← Finset.sum_coe_sort ((pieceLabels labels select i).image fun l => exponentBin width (x l))]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold SecondStepHighCount.ofRows
  rw [SecondStepHighCount.single_value]
  rfl

/-- The binned record has at most the number of pieces times the number of bins of a box of the coordinates
classes. -/
theorem secondStepBinRecord_card (Bbox : ℝ) (hx : ∀ l ∈ labels, ∀ j, -Bbox ≤ x l j ∧ x l j ≤ Bbox) :
    Fintype.card (secondStepBinRecord labels select x width lab W expo zero rowShift hZ hw hzero hrow hsupp hsame
      hcap hideal hmiss).Class ≤ Fintype.card ι*(Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4 := by
  change Fintype.card (Σ _c : BinClass labels select x width, Unit) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_unique, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [Fintype.card_sigma]
  calc ∑ i, Fintype.card {b // b ∈ (pieceLabels labels select i).image (fun l => exponentBin width (x l))}
      = ∑ i, ((pieceLabels labels select i).image (fun l => exponentBin width (x l))).card := by
        simp only [Fintype.card_coe]
    _ ≤ ∑ _i : ι, (Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4 :=
        Finset.sum_le_sum fun i _ => exponent_bins_card _ x width Bbox hw
          (fun l hl => hx l (Finset.mem_filter.mp hl).1)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The binned record pays the HIGH reserve of the parent when every label pays it at its own coordinates with the
loss of four bin widths: with `δ = 2 zero i - 1` of its piece in `[lo, 3/4]` and `[q0, 3/4]`, its HIGH exponent value
is at most `loss - rest + ρ scale + δ length + amp (5 - 6ρ) - 4 width`, where the class exponents are the transport
exponents `U₀ + δ U₃ + rest` at the upper edges `U` of the bins and the row shift is the log norm of `v₁`. -/
theorem secondStepBinRecord_pays (lo scale length amp loss rest : ℝ)
    (hexpo : ∀ i b, expo i b = exponentBinUpper width b 0+(2*zero i-1)*exponentBinUpper width b 3+rest)
    (hshift : rowShift = Real.logb Z ((Ideal.span {v₁}).absNorm : ℝ))
    (hδ : ∀ l ∈ labels, lo ≤ 2*zero (select l)-1 ∧ Cycle63.Arithmetic.q0 ≤ 2*zero (select l)-1 ∧
      2*zero (select l)-1 ≤ 3/4)
    (hpay : ∀ l ∈ labels, highExponentValue (2*zero (select l)-1) (x l) ≤
      loss-rest+unmarkedDensity (2*zero (select l)-1)*scale+(2*zero (select l)-1)*length+
        amp*(5-6*unmarkedDensity (2*zero (select l)-1))-4*width) :
    (secondStepBinRecord labels select x width lab W expo zero rowShift hZ hw hzero hrow hsupp hsame hcap hideal
      hmiss).Pays lo scale length amp loss := by
  rintro ⟨c, u⟩
  obtain ⟨l, hl⟩ := binClassLabels_nonempty c
  have h := mem_binClassLabels hl
  have hδl := hδ l h.1
  rw [h.2.1] at hδl
  have hpl := hpay l h.1
  rw [h.2.1] at hpl
  have ht := high_bin_reserve_transfer width (2*zero c.1-1) _ _ hw ⟨hδl.2.1, hδl.2.2⟩ (x l) hpl
  rw [h.2.2] at ht
  show lo ≤ 2*zero c.1-1 ∧ 2*zero c.1-1 ≤ 3/4 ∧
    expo c.1 c.2.val-scale+exponentBinUpper width c.2.val 1+
      unmarkedDensity (2*zero c.1-1)*(exponentBinUpper width c.2.val 2+rowShift-
        Real.logb Z ((Ideal.span {v₁}).absNorm : ℝ)) ≤
    loss-(scale*(1-unmarkedDensity (2*zero c.1-1))-(2*zero c.1-1)*length-
      amp*(5-6*unmarkedDensity (2*zero c.1-1)))
  refine ⟨hδl.1, hδl.2.2, ?_⟩
  rw [hexpo, hshift, add_sub_cancel_right]
  unfold highExponentValue at ht
  nlinarith [ht]

end Record

/-- Two maps to joint labels with the same underlying labels have images of the same size. -/
theorem card_image_eq_of_val_eq {κ : Type*} {left left' : Bool} {u u' : O} {unit unit' : FirstSourceLabel → O}
    (S : Finset κ) (f : κ → NonzeroJointSourceLabel left u unit) (g : κ → NonzeroJointSourceLabel left' u' unit')
    (h : ∀ l, (f l).val = (g l).val) : (S.image f).card = (S.image g).card := by
  have hf := Finset.card_image_of_injective (S.image f)
    (f := fun y : NonzeroJointSourceLabel left u unit => y.val) (fun _ _ hab => Subtype.ext hab)
  have hg := Finset.card_image_of_injective (S.image g)
    (f := fun y : NonzeroJointSourceLabel left' u' unit' => y.val) (fun _ _ hab => Subtype.ext hab)
  rw [← hf, ← hg, Finset.image_image, Finset.image_image]
  exact congrArg Finset.card (Finset.image_congr (fun l _ => h l))

/-- The binned counts of two maps to joint labels with the same underlying labels agree. -/
theorem keyBinnedCount_eq_of_val_eq {κ : Type*} {left left' : Bool} {u u' : O} {unit unit' : FirstSourceLabel → O}
    (S : Finset κ) (f : κ → NonzeroJointSourceLabel left u unit) (g : κ → NonzeroJointSourceLabel left' u' unit')
    (h : ∀ l, (f l).val = (g l).val) (x : κ → Fin 4 → ℝ) (width : ℝ) (weight : (Fin 4 → ℤ) → ℝ) :
    keyBinnedCount S f x width weight = keyBinnedCount S g x width weight := by
  unfold keyBinnedCount
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [card_image_eq_of_val_eq _ f g h]

/-- The joint row of a label is the fixed row times the unit of its first label times a factor of the label. -/
theorem jointSourceRow_eq_unit_mul (left : Bool) (v : O) (unit : FirstSourceLabel → O) (ℓ : JointSourceLabel) :
    jointSourceRow left v unit ℓ = v*(unit ℓ.1*jointSourceRow left 1 (fun _ => 1) ℓ) := by
  unfold jointSourceRow effectiveRow
  ring

/-- The row norm of a label at the fixed row `v` with units `unit'` is the norm of `v` times the row norm of the label
with the same underlying label at the fixed row `1` with units `unit`, when both units are units. -/
theorem rawFrequencyNorm_unit_change {left : Bool} {v : O} {unit unit' : FirstSourceLabel → O}
    (ℓ : NonzeroJointSourceLabel left 1 unit) (ℓ' : NonzeroJointSourceLabel left v unit') (h : ℓ'.val = ℓ.val)
    (hu : IsUnit (unit ℓ.val.1)) (hu' : IsUnit (unit' ℓ.val.1)) :
    rawFrequencyNorm (nonzeroJointSourceRow ℓ') =
      ((Ideal.span {v}).absNorm : ℝ)*rawFrequencyNorm (nonzeroJointSourceRow ℓ) := by
  unfold rawFrequencyNorm nonzeroJointSourceRow
  simp only []
  rw [h, jointSourceRow_eq_unit_mul left v unit', jointSourceRow_eq_unit_mul left 1 unit, one_mul,
    Ideal.span_singleton_mul_left_unit hu, ← mul_assoc, mul_comm v, mul_assoc,
    Ideal.span_singleton_mul_left_unit hu', ← Ideal.span_singleton_mul_span_singleton, map_mul]
  push_cast
  ring


end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
