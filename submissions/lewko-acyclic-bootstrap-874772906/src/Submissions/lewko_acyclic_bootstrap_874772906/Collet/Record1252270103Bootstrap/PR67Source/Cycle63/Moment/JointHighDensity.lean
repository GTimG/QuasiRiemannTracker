import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointSourceCount
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.ActualRowDensity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Density.JointRows
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle63Moment
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

/-- The labels over one row: at most `C Z^(m + loss)` when the rows have norm at most `Z^B`. The constant precedes
the labels and the fixed unit. -/
theorem nonzero_joint_source_fiber_count (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ m : ℝ, ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      (∀ label ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow label) ≤ Z^B) →
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
      ∀ w : NonzeroFrequency,
        ((labels.filter (fun label => nonzeroJointSourceRow label = w)).card:ℝ) ≤ C*Z^(m+loss) := by
  obtain ⟨C,hC,hcount⟩ := actual_joint_source_row_count B loss hB hloss
  refine ⟨C,hC,?_⟩
  intro left u₀ unit Z hZ m labels hrowbound hnonzero heq hsupportnorm hnorm hmissing w
  let fibre := labels.filter (fun label => nonzeroJointSourceRow label = w)
  have mem_fibre (v : NonzeroJointSourceLabel left u₀ unit) (hv : v ∈ fibre) :
      v ∈ labels ∧ jointSourceRow left u₀ unit v.val = w.val := by
    have h := Finset.mem_filter.mp hv
    exact ⟨h.1,congrArg Subtype.val h.2⟩
  rcases fibre.eq_empty_or_nonempty with hempty | ⟨v₀,hv₀⟩
  · change ((fibre.card:ℕ):ℝ) ≤ _
    rw [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  have hc := hcount left u₀ unit Z hZ w.val w.property
    (by
      have hn := hrowbound v₀ (mem_fibre v₀ hv₀).1
      change ((Ideal.span {jointSourceRow left u₀ unit v₀.val}).absNorm:ℝ) ≤ Z^B at hn
      rwa [(mem_fibre v₀ hv₀).2] at hn)
    m (fibre.image Subtype.val)
    (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact (mem_fibre v hv).2)
    (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnonzero v (mem_fibre v hv).1)
    (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact heq v (mem_fibre v hv).1)
    (by
      intro label hl
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
      have h := hsupportnorm v (mem_fibre v hv).1
      rwa [(mem_fibre v hv).2] at h)
    (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnorm v (mem_fibre v hv).1)
    (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hmissing v (mem_fibre v hv).1)
  have hinj : Set.InjOn Subtype.val (fibre : Set (NonzeroJointSourceLabel left u₀ unit)) :=
    fun v _ r _ h => Subtype.ext h
  rw [Finset.card_image_of_injOn hinj] at hc
  exact hc

/-- The constants precede the live source labels, Euler punctures, both heights
and the bin position. Each missing radical and literal frequency is counted once. -/
theorem actual_joint_natural_high_row_count {Dict : Type*} [Fintype Dict]
    (base : Dict → Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ left : Bool, ∀ u₀ : O, ∀ unit : FirstSourceLabel → O,
      ∀ Z : ℝ, 2 ≤ Z → ∀ q m a T : ℝ, q ≤ Q → 4/5 ≤ a → a ≤ 7/8 → 0 ≤ T →
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
  obtain ⟨J,hJ⟩ := card_le_density_mul_fiber (Label := Dict) (loss/(2*(Q+1))) (div_pos hloss (by positivity))
  obtain ⟨D,hD,hdensity⟩ := hJ base
  obtain ⟨C,hC,hfiber⟩ := nonzero_joint_source_fiber_count B (loss/2) hB (by positivity)
  refine ⟨J,D*C,mul_pos hD hC,?_⟩
  intro left u₀ unit Z hZ q m a T hq ha ha' hT labels reverse hzero
    hnonzero heq hsupportnorm hnorm hmissing
  have hZ0 : 0 < Z := by linarith
  have hd := hdensity nonzeroJointSourceRow reverse a T ha ha' hT (Z^q) (Real.rpow_pos_of_pos hZ0 q) labels
    (C*Z^(m+loss/2)) hzero
    (hfiber left u₀ unit Z hZ m labels
      (fun label hl => (hzero label hl).1.trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (hq.trans hQB)))
      hnonzero heq hsupportnorm hnorm hmissing)
  have habsorb := density_loss_absorb (ρ := unmarkedDensity (2*a-1)) (by linarith : (1:ℝ) ≤ Z) hQ hq hloss
  calc (labels.card:ℝ)
      ≤ D*(1+T)^J*(Z^q)^(unmarkedDensity (2*a-1)+loss/(2*(Q+1)))*(C*Z^(m+loss/2)) := hd
    _ ≤ D*(1+T)^J*Z^(q*unmarkedDensity (2*a-1)+loss/2)*(C*Z^(m+loss/2)) := by gcongr
    _ = (D*C)*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
      have h : Z^(m+q*unmarkedDensity (2*a-1)+loss) = Z^(q*unmarkedDensity (2*a-1)+loss/2)*Z^(m+loss/2) := by
        rw [← Real.rpow_add hZ0]
        ring_nf
      rw [h]
      ring

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
