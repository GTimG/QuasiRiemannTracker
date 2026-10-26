import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.JointSourceCount
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.ActualRowDensity

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
local notation "O" => HeckeFamily.O

def NonzeroJointSourceLabel (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O) :=
  {label : JointSourceLabel // jointSourceRow left u₀ unit label ≠ 0}

def nonzeroJointSourceRow {left : Bool} {u₀ : O} {unit : FirstSourceLabel → O}
    (label : NonzeroJointSourceLabel left u₀ unit) : NonzeroFrequency :=
  ⟨jointSourceRow left u₀ unit label.val,label.property⟩

theorem actual_signed_zero_to_natural (η : Character)
    (puncture : (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter) →
      NonzeroFrequency → Ideal O)
    (reverse : (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter) → Bool)
    (a T : ℝ) (ha : 0 < a) (w : NonzeroFrequency)
    (hz : maskedActualZeroRow (actualMaskedRowFamily η puncture) reverse a T w) :
    naturalActualZeroRow (secondFixedDictionary η) reverse a T w := by
  apply masked_zero_to_natural (secondFixedDictionary η) (actualMaskedRowFamily η puncture)
    _ reverse a T ha w hz
  intro j u I
  exact excludePrimes_mask _ _ (support_prime (puncture j u)) I

/-- The constants precede the live source labels, Euler punctures, both heights
and the bin position. Each missing radical and literal frequency is counted once. -/
theorem actual_joint_natural_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
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

theorem actual_joint_high_row_count (η : Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit →
        (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter) → NonzeroFrequency → Ideal O,
      ∀ reverse : (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter) → Bool,
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^q ∧
        maskedActualZeroRow (actualMaskedRowFamily η (puncture label)) reverse a T
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
  obtain ⟨J,C,hC,hcount⟩ := actual_joint_natural_high_row_count
    (secondFixedDictionary η) B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels puncture reverse hzero
    hnonzero heq hsupportnorm hnorm hmissing
  exact hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels reverse
    (fun label hl => ⟨(hzero label hl).1,
      actual_signed_zero_to_natural η (puncture label) reverse a T
        (by linarith) (nonzeroJointSourceRow label) (hzero label hl).2⟩)
    hnonzero heq hsupportnorm hnorm hmissing

#print axioms actual_signed_zero_to_natural
#print axioms actual_joint_natural_high_row_count
#print axioms actual_joint_high_row_count
end
end OAI.SevenEighths.Cycle61Moment
