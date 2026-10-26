import Candidate.Target830.Marked.Density.NaturalEndpoint
import Candidate.Cycle63.Moment.JointHighDensity
import Candidate.Cycle63.Moment.JointSourceCount
import Candidate.Cycle63.Moment.ActualRowDensity
import Candidate.Cycle63.Moment.PhysicalHighRows
import Candidate.Cycle63.Moment.SecondNaturalMask
import Candidate.Cycle63.Moment.WholeSourceFamily
import Candidate.Cycle63.Moment.HighSourceEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion

/- Original module: Candidate.Target830.High.NaturalDensity. -/
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily LocalMoment ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open HeckeDetectorZeros ConcreteTraceCRT
open HeckeInverseAmplification ProbeHighRowFamily HeckeFiniteDeletion
open Target830MarkedDensity
local notation "O" => HeckeFamily.O
theorem fixed_dictionary_actual_raw_zero_density {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ orientedActualZeroRow D.data reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hf⟩ := Target830MarkedDensity.fixed_dictionary_eventual_with_exceptions D loss hloss
  let P : Target830MarkedDensity.DensityParameter → FreeRow → Prop := fun p u =>
    rawZeroBin D.data p.val.1 (7/8) p.val.2 ⟨u.val, u.property.1⟩ ∨ D.exceptionalCore u
  let exponent : Target830MarkedDensity.DensityParameter → ℝ := fun p => unmarkedDensity (2*p.val.1-1)+loss
  let weight : Target830MarkedDensity.DensityParameter → ℝ := fun p => (1+p.val.2)^J
  have hρ (p : Target830MarkedDensity.DensityParameter) : 2/7 ≤ exponent p := by
    dsimp [exponent]
    linarith [unmarkedDensity_ge_two_sevenths (show 2*p.val.1-1 ≤ 3/4 by linarith [p.property.2.1])]
  have hw (p : Target830MarkedDensity.DensityParameter) : 1 ≤ weight p := one_le_pow₀ (by linarith [p.property.2.2])
  have hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : Target830MarkedDensity.DensityParameter, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C*weight p*Y^exponent p := by
    filter_upwards [hf] with Y hf
    intro p
    exact hf p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2
  obtain ⟨C', hC', _, hfree⟩ := uniform_free_density_weighted_of_eventually P C exponent weight
    (fun p => by linarith [hρ p]) hw hevent
  obtain ⟨D₀, hD₀, hraw⟩ := raw_core_density_uniform
  refine ⟨J, C'*D₀, mul_pos hC' hD₀, ?_⟩
  intro reverse a T ha ha' hT H hH rows hrows
  let p : Target830MarkedDensity.DensityParameter := ⟨(a,T), ha, ha', hT⟩
  have hb := hraw (P p) (C'*weight p) (exponent p) (by have := hw p; positivity) (hρ p)
    (fun Y hY F hF => hfree Y hY p F hF) H hH rows
    (fun u hu => ⟨(hrows u hu).1, Target830MarkedDensity.oriented_zero_core_predicate D reverse a T ha u (hrows u hu).2⟩)
  convert hb using 1
  dsimp [p, weight, exponent]
  ring

theorem fixed_natural_dictionary_raw_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ naturalActualZeroRow base reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_dictionary_actual_raw_zero_density
    (FixedUnmarkedDictionary.ofBases base) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro reverse a T ha ha' hT H hH rows hrows
  exact hb reverse a T ha ha' hT H hH rows (fun u hu =>
    ⟨(hrows u hu).1, Target830MarkedDensity.natural_zero_to_literal_dictionary base reverse a T ha u (hrows u hu).2⟩)

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.fixed_natural_dictionary_raw_density
end

/- Original module: Candidate.Target830.High.JointHighDensity. -/
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily LocalMoment ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily Cycle63Moment
open CenteredMomentCanonicalFirst ActualEisensteinCubic
open HeckeDetectorZeros ConcreteTraceCRT Target830MarkedDensity
local notation "O" => HeckeFamily.O
theorem actual_joint_natural_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ reverse : Dict → Bool,
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        naturalActualZeroRow base reverse a T
          (nonzeroJointSourceRow label)) →
      (∀ label ∈ labels, Supported label.val.1.1.1 ∧ label.val.1.1.2 ≠ 0 ∧
        Supported label.val.2.1.1 ∧ label.val.2.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.val.1.1.1 = primeSupport label.val.1.1.2 ∧
        primeSupport label.val.2.1.1 = primeSupport label.val.2.1.2) →
      (∀ label ∈ labels,
        ((Ideal.span {jointSourceRow left u₀ unit label.val}*
          firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, (label.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (label.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (label.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, ((firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^m) →
        (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  let δ := loss/(2*(Q+1))
  have hδ : 0 < δ := div_pos hloss (by positivity)
  obtain ⟨J,D,hD,hdensity⟩ := fixed_natural_dictionary_raw_density base δ hδ
  obtain ⟨C,hC,hcount⟩ := actual_joint_source_row_count B (loss/2) hB (by positivity)
  refine ⟨J,D*C,mul_pos hD hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels reverse hzero
    hnonzero heq hsupportnorm hnorm hmissing
  let row : NonzeroJointSourceLabel left u₀ unit → NonzeroFrequency := nonzeroJointSourceRow
  have hZ0 : 0 < Z := by linarith
  have hradius : 0 < Z^q := Real.rpow_pos_of_pos hZ0 q
  have hd := hdensity reverse a T ha ha' hT (Z^q) hradius (labels.image row) (by
    intro w hw
    obtain ⟨label,hl,rfl⟩ := Finset.mem_image.mp hw
    exact hzero label hl)
  have hfiber (w : NonzeroFrequency) (hw : w ∈ labels.image row) :
      ((labels.filter (fun label => row label = w)).card:ℝ) ≤ C*Z^(m+loss/2) := by
    let fibre := labels.filter (fun label => row label = w)
    have mem_fibre (v : NonzeroJointSourceLabel left u₀ unit) (hv : v ∈ fibre) :
        v ∈ labels ∧ row v = w := by
      simpa only [fibre, Finset.mem_filter] using hv
    have hc := hcount left u₀ unit Z hZ w.val w.property
      (by
        obtain ⟨label,hl,hrow⟩ := Finset.mem_image.mp hw
        have hn := (hzero label hl).1
        change ((Ideal.span {jointSourceRow left u₀ unit label.val}).absNorm:ℝ) ≤ Z^q at hn
        have he : jointSourceRow left u₀ unit label.val = w.val := congrArg Subtype.val hrow
        rw [he] at hn
        exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (hq.trans hQB)))
      m (fibre.image Subtype.val)
      (by
        intro label hl
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
        exact congrArg Subtype.val (mem_fibre v hv).2)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnonzero v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact heq v (mem_fibre v hv).1)
      (by
        intro label hl
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
        have he : jointSourceRow left u₀ unit v.val = w.val :=
          congrArg Subtype.val (mem_fibre v hv).2
        simpa only [he] using hsupportnorm v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnorm v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hmissing v (mem_fibre v hv).1)
    have hinj : Set.InjOn (fun v : NonzeroJointSourceLabel left u₀ unit => v.val)
        (↑fibre : Set (NonzeroJointSourceLabel left u₀ unit)) :=
      fun v _ r _ h => Subtype.ext h
    have hcard : fibre.card ≤ (fibre.image Subtype.val).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro v hv
        exact Finset.mem_image_of_mem _ hv
      · exact hinj
    change (fibre.card:ℝ) ≤ C*Z^(m+loss/2)
    exact (show (fibre.card:ℝ) ≤ ((fibre.image Subtype.val).card:ℝ) by exact_mod_cast hcard).trans hc
  have he := Finset.card_eq_sum_card_fiberwise
    (fun label (hl : label ∈ labels) => Finset.mem_image_of_mem row hl)
  have hbudget : q*δ ≤ loss/2 := by
    have hid : δ*(2*(Q+1)) = loss := by dsimp only [δ]; field_simp
    have hqδ := mul_le_mul_of_nonneg_right hq hδ.le
    nlinarith
  calc
    _ = ∑ w ∈ labels.image row, ((labels.filter (fun label => row label = w)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _w ∈ labels.image row, C*Z^(m+loss/2) := Finset.sum_le_sum hfiber
    _ = ((labels.image row).card:ℝ)*(C*Z^(m+loss/2)) := by simp
    _ ≤ (D*(1+T)^J*(Z^q)^(unmarkedDensity (2*a-1)+δ))*(C*Z^(m+loss/2)) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _ = (D*C)*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss/2+q*δ) := by
      rw [←Real.rpow_mul hZ0.le]
      calc
        _ = (D*C)*(1+T)^J*(Z^(q*(unmarkedDensity (2*a-1)+δ))*Z^(m+loss/2)) := by ring
        _ = _ := by
          rw [←Real.rpow_add hZ0]
          congr 1
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) (by positivity)

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_joint_natural_high_row_count
end

/- Original module: Candidate.Target830.High.PhysicalHighRows. -/
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily LocalMoment ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily Cycle63Moment
open CenteredMomentCanonicalFirst ActualEisensteinCubic
open HeckeDetectorZeros ConcreteTraceCRT Target830MarkedDensity
local notation "O" => HeckeFamily.O
theorem actual_joint_fixed_physical_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ character : NonzeroJointSourceLabel left u₀ unit → Character,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Dict,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Ideal O,
      ∀ reverse : NonzeroJointSourceLabel left u₀ unit → Bool,
      (∀ label ∈ labels, ∀ I : Ideal O, idealCoeff (character label) I =
        idealCoeff (excluded (naturalRow (base (dictionary label))
          (nonzeroJointSourceRow label).val (nonzeroJointSourceRow label).property).character
            (puncture label)) I) →
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        ∃ s : ℂ, LFunction (wholeOrientation (character label) (reverse label)) s = 0 ∧
          (s ≠ 1 ∨ (wholeOrientation (character label) (reverse label)).residue ≠ 1) ∧
          a ≤ s.re ∧ |s.im| ≤ T) →
      (∀ label ∈ labels, Supported label.val.1.1.1 ∧ label.val.1.1.2 ≠ 0 ∧
        Supported label.val.2.1.1 ∧ label.val.2.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.val.1.1.1 = primeSupport label.val.1.1.2 ∧
        primeSupport label.val.2.1.1 = primeSupport label.val.2.1.2) →
      (∀ label ∈ labels,
        ((Ideal.span {jointSourceRow left u₀ unit label.val}*
          firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, (label.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (label.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (label.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, ((firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^m) →
        (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hcount⟩ := actual_joint_natural_high_row_count
    (orientedFixedBase base) B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels character dictionary
    puncture reverse hcoeff hzero hnonzero heq hsupportnorm hnorm hmissing
  exact hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels Prod.snd
    (fun label hl => ⟨(hzero label hl).1,
      physical_zero_to_fixed_dictionary base (character label) (dictionary label)
        (nonzeroJointSourceRow label) (puncture label) (reverse label)
        (hcoeff label hl) a T (by linarith) (hzero label hl).2⟩)
    hnonzero heq hsupportnorm hnorm hmissing

/-- High-bin cardinality from the actual finite whole-family zero maximum,
with constants chosen before every live masked family and height. -/

theorem actual_joint_buffered_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ {Family : Type*} [Fintype Family],
      ∀ character : NonzeroJointSourceLabel left u₀ unit → Family → Character,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Family → Dict,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Family → Ideal O,
      ∀ reverse : NonzeroJointSourceLabel left u₀ unit → Family → Bool,
      ∀ hchar : ∀ label, ∀ j,
        (wholeOrientation (character label j) (reverse label j)).residue ≠ 1,
      (∀ label ∈ labels, ∀ j, ∀ I : Ideal O, idealCoeff (character label j) I =
        idealCoeff (excluded (naturalRow (base (dictionary label j))
          (nonzeroJointSourceRow label).val (nonzeroJointSourceRow label).property).character
            (puncture label j)) I) →
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (fun j => wholeOrientation (character label j) (reverse label j)) (hchar label) T) →
      (∀ label ∈ labels, Supported label.val.1.1.1 ∧ label.val.1.1.2 ≠ 0 ∧
        Supported label.val.2.1.1 ∧ label.val.2.1.2 ≠ 0) →
      (∀ label ∈ labels, primeSupport label.val.1.1.1 = primeSupport label.val.1.1.2 ∧
        primeSupport label.val.2.1.1 = primeSupport label.val.2.1.2) →
      (∀ label ∈ labels,
        ((Ideal.span {jointSourceRow left u₀ unit label.val}*
          firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, (label.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (label.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (label.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (label.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ label ∈ labels, ((firstSourceMissing left label.val.1).absNorm:ℝ) ≤ Z^m) →
        (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hcount⟩ := actual_joint_natural_high_row_count
    (orientedFixedBase base) B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels Family _ character dictionary
    puncture reverse hchar hcoeff hzero hnonzero heq hsupportnorm hnorm hmissing
  exact hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels Prod.snd
    (fun label hl => ⟨(hzero label hl).1,
      physical_family_maximum_to_fixed_dictionary base (character label) (reverse label)
        (hchar label) (dictionary label) (puncture label) (nonzeroJointSourceRow label)
        (hcoeff label hl) a T (by linarith) (hzero label hl).2⟩)
    hnonzero heq hsupportnorm hnorm hmissing

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_joint_fixed_physical_high_row_count
#print axioms OAI.SevenEighths.TargetHigh830.actual_joint_buffered_high_row_count
end

/- Original module: Candidate.Target830.High.WholeSourceFamily. -/
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily LocalMoment ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily Cycle63Moment
open CenteredMomentCanonicalFirst ActualEisensteinCubic
open CenteredMomentEnergyState CenteredMomentCommonRadialData
open HeckeDetectorZeros ConcreteTraceCRT Target830MarkedDensity
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
theorem actual_whole_joint_high_row_count {Base : Type*} [Fintype Base]
    (base : Base → Character) (η₀ : Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (Z : ℝ), 2 ≤ Z → ∀ q m a T Bmask bΦ : ℝ,
      q ≤ Q → 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z Bmask bΦ,
      ∀ hQM : ∀ l, (st l).fixedModulus ≤ M,
      ∀ hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus,
      ∀ z : NonzeroJointSourceLabel left u₀ unit → O,
      ∀ hz : ∀ l, (st l).radial.keep (z l),
      ∀ F : ∀ l, NaturalRow (st l).character (z l),
      ∀ index : NonzeroJointSourceLabel left u₀ unit → Base,
      ∀ holes : NonzeroJointSourceLabel left u₀ unit → Ideal O,
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (F l).character (st l).puncture) I =
          idealCoeff (excluded (naturalRow (base (index l))
            (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
            (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded (F l).character (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l)
            (z l) (hz l) (F l)) T) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^m) →
      (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  let bases : Base×WholeSourceIndex M H → Character :=
    fun j => wholeSourceBase M H hH η₀ (base j.1) j.2
  obtain ⟨J,C,hC,hcount⟩ := actual_joint_buffered_high_row_count bases B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T Bmask bΦ hq ha ha' hT labels st hQM hQη z hz F
    index holes hholes hmask hzero hnonzero heq hsupport hnorm hmissing
  let characters := fun l => wholeSourceFamily M H hH η₀
    (excluded (F l).character (st l).puncture)
  have hn := fun l => whole_source_family_nonprincipal M H hH (st l) η₀
    (hQM l) (hQη l) (z l) (hz l) (F l)
  apply hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels characters
    (fun l j => (index l,j)) (fun l _ => holes l) (fun _ _ => false) hn
    ?_ hzero hnonzero heq hsupport hnorm hmissing
  intro l hl j I
  exact whole_source_family_mask M H hH η₀ (base (index l))
    (excluded (F l).character (st l).puncture) (nonzeroJointSourceRow l).val
    (nonzeroJointSourceRow l).property
    (naturalRow (base (index l)) _ (nonzeroJointSourceRow l).property)
    (holes l) (hholes l hl) (hmask l hl)
    (fun j => naturalRow (wholeSourceBase M H hH η₀ (base (index l)) j)
      (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property) j I

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_whole_joint_high_row_count
end
